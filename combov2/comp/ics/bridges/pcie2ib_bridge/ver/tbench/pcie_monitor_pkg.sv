//
// pcie_monitor_pkg.sv: System Verilog PCI Express Monitor
// Copyright (C) 2007 CESNET
// Author(s): Tomas Malek <tomalek@liberouter.org>
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
// 3. Neither the name of the Company nor the names of its contributors
//    may be used to endorse or promote products derived from this
//    software without specific prior written permission.
//
// This software is provided ``as is'', and any express or implied
// warranties, including, but not limited to, the implied warranties of
// merchantability and fitness for a particular purpose are disclaimed.
// In no event shall the company or contributors be liable for any
// direct, indirect, incidental, special, exemplary, or consequential
// damages (including, but not limited to, procurement of substitute
// goods or services; loss of use, data, or profits; or business
// interruption) however caused and on any theory of liability, whether
// in contract, strict liability, or tort (including negligence or
// otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// $Id: pcie_monitor_pkg.sv 688 2007-10-19 16:11:56Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package pcie_monitor_pkg;

  import pcie_transaction_pkg::*; // Transaction package


  // --------------------------------------------------------------------------
  // -- PCIe Monitor Callbacks
  // --------------------------------------------------------------------------
  /* This is a abstract class for creating objects which get benefits from
   * function callback. This object can be used with PcieMonitor
   * class. Inheritence from this basic class is neaded for functionality.
   */
  class PcieMonitorCbs;
    
    // -- Class Methods --

    // ------------------------------------------------------------------------
    // Function is called before post_rx is called (modification of transaction)
    virtual task pre_rx(ref PcieTransaction transaction, integer monitorId);
      // By default, callback does nothing
    endtask
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(PcieTransaction transaction, integer monitorId);
      // By default, callback does nothing
    endtask
  
  endclass : PcieMonitorCbs

  // --------------------------------------------------------------------------
  // -- PCIe Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from 
   * PCIe interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class PcieMonitor;
    
    // -- Public Class Atributes --

    // -- Private Class Atributes --
    integer monitorId;                       // Monitor identification
    bit     enabled;                         // Monitor is enabled
    PcieMonitorCbs cbs[$];                   // Callbacks list
    virtual iPcieTx.monitor pcie;            // Pcie Interface

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( virtual iPcieTx.monitor pcie,
                   integer monitorId);
      this.enabled     = 0;           // Monitor is disabled by default   
      this.pcie        = pcie;        // Store pointer interface 
      this.monitorId   = monitorId;   // Store driver identifier
      
      // Setting default values for Internal Bus interface
      pcie.DST_RDY_N = 0;             // Ready even if disabled
      pcie.DST_DCS_N = 1;             // Never discontinue
      pcie.BUF_AV    = 3'b111;        // Full buffer availability in the core
    endfunction

    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(PcieMonitorCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks

    // -- Enable Monitor ------------------------------------------------------
    // Enable monitor and runs monitor process
    task setEnabled();
      enabled = 1; // Monitor Enabling
      fork         
        run();     // Creating monitor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Monitor -----------------------------------------------------
    // Disable monitor
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
    endtask : setDisabled    
   
    // -- Private Class Methods --

    // -- Random not ready ----------------------------------------------------
    // Disable monitor
    task randomNotReady(bit en);
      if (en) begin
        repeat ($urandom_range(2)) begin
          pcie.DST_RDY_N = 1;
          @(posedge pcie.CLK); // Wait for send
        end;
        pcie.DST_RDY_N = 0;
        end;
    endtask : randomNotReady

    // -- Run Monitor ---------------------------------------------------------
    // Receive transactions and send them for processing by call back
    task run();
      PcieTransaction transaction;     
      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        receiveTransaction(transaction); // Receive Transaction
        
        if (enabled) begin                                                           
          // Call transaction preprocesing, if is available
          foreach (cbs[i]) cbs[i].pre_rx(transaction, monitorId);

          // Call transaction postprocesing, if is available
          foreach (cbs[i]) cbs[i].post_rx(transaction, monitorId);
        end
      end
    endtask : run

    // -- Receive Transaction -------------------------------------------------
    // It receives Internal Bus transaction to tr object
    task receiveTransaction( PcieTransaction tr);
      bit enNotReady = $urandom_range(8);
      
      // Receive Header 1 + 2 (first data word) ---------------------
      do begin
        randomNotReady(enNotReady); // Generate random not ready
        // Wait if not data ready
        if (pcie.SOF_N || pcie.SRC_RDY_N)
          @(posedge pcie.CLK);
        if (!enabled) return;
      end while (pcie.SOF_N || pcie.SRC_RDY_N);
       
      receiveHdr12(tr);

      // Receive Header 3 + 4 / Header 3 + DATA / Header 3 ----------
      randomNotReady(enNotReady);
      @(posedge pcie.CLK);
      @(negedge pcie.CLK && pcie.SRC_RDY_N == 0);      

      case (tr.transType)
         RD32:
            tr.address = {32'h00000000,pcie.DATA[63:32]};
         RD64:
            tr.address = pcie.DATA;
         WR32:
            receiveData(tr);
         WR64: begin
            receiveHdr34(tr);
            receiveData(tr);
            end
         CPLD:
            receiveData(tr);
      endcase;      

      tr.barHitN   = B1111110;
      tr.supported = 1;

    endtask : receiveTransaction

    // -- Receive Header 3 + 4 ------------------------------------------------
    // Receive Header 3 + Header 4 (first DW word)
    task receiveHdr34(PcieTransaction tr); 
      bit enNotReady = $urandom_range(8); 
      tr.address = pcie.DATA;

      randomNotReady(enNotReady);
      // Wait for second header
      @(posedge pcie.CLK);
      @(negedge pcie.CLK && pcie.SRC_RDY_N == 0);             
    endtask : receiveHdr34        
    
    // -- Receive Header 1 + 2 ------------------------------------------------
    // Receive Header 1 + Header 2 (first DW word)
    task receiveHdr12(PcieTransaction tr);

      // parse Header 1 -----------------------------------
      // Get Transaction type
      case (pcie.DATA[62:56])
         CMD_RD32:
            tr.transType = RD32;
         CMD_RD64:
            tr.transType = RD64;
         CMD_WR32:
            tr.transType = WR32;
         CMD_WR64:
            tr.transType = WR64;
         CMD_CPLD:
            tr.transType = CPLD;
         default: begin
            $write("Error: received transaction of unknown type (%t)",$time);
            $stop();
         end
       endcase;      

      tr.tc     = pcie.DATA[54:52];
      tr.td     = pcie.DATA[47];
      tr.ep     = pcie.DATA[46];
      tr.attr   = pcie.DATA[45:44];
      tr.length = pcie.DATA[41:32];
                 
      // parse Header 2 -----------------------------------
      // Read/Write header
      tr.busnum_req     = pcie.DATA[31:24];
      tr.devnum_req     = pcie.DATA[23:19];
      tr.funcnum_req    = pcie.DATA[18:16];      

      tr.tag            = pcie.DATA[15: 8];
      tr.lastBE         = pcie.DATA[ 7: 4];
      tr.firstBE        = pcie.DATA[ 3: 0];      

      // Completion header
      tr.busnum_cpl     = pcie.DATA[31:24];
      tr.devnum_cpl     = pcie.DATA[23:19];
      tr.funcnum_cpl    = pcie.DATA[18:16];

      tr.bcm            = pcie.DATA[12];
      tr.byteCount      = pcie.DATA[11: 0];      

      if (tr.transType == CPLD) begin
         case (pcie.DATA[15:13])
            C_CPLSTAT_OK:
               tr.cplStatus = CPLSTAT_OK;
            default: begin
               $write("Error: received transaction with uknown CPL status (%t)",$time);
               $stop();
            end
          endcase;            
      end       
    endtask : receiveHdr12    

    // -- Receive Data --------------------------------------------------------
    // This function receives transaction data
    task receiveData( PcieTransaction tr);
      bit enNotReady = $urandom_range(8);      
      int trlen   = countLength(tr);
      int offset  = countOffset(tr);      
      int word64  = (trlen + offset + 7)/8;  
      
      int low_tr  = 0;
      int low_ib  = 0;
      int high_ib = 7;
      tr.data = new[trlen];    

      // WR32/CPLD Header 3 + DATA DW 0 -------------------
      if (tr.transType == CPLD) begin          
        tr.busnum_req     = pcie.DATA[63:56];
        tr.devnum_req     = pcie.DATA[55:51];
        tr.funcnum_req    = pcie.DATA[50:48];      
        tr.tag            = pcie.DATA[47:40];
        tr.lowerAddr      = pcie.DATA[38:32];
      end
      
      if (tr.transType == WR32)
        tr.address = {32'h00000000,pcie.DATA[63:32]};

      // DATA reception -----------------------------------
      for (int i=1; i <= word64; i++) begin

        if (i != 1) begin
          randomNotReady(enNotReady); // Generate random not ready
          @(posedge pcie.CLK && pcie.SRC_RDY_N == 0);
        end
        
        // first word
        if (i == 1) 
          low_ib = offset;              
        else
          low_ib = 0;
          
        // last word
        if (i == word64) begin        
          high_ib  = ( ((trlen + offset) - 1) % 8);
          if (pcie.EOF_N == 1) begin
            $write("Error (%t): Pcie Monitor %d receive transaction with wrong length: ", $time, monitorId);
            tr.display(1);
            $stop;
          end;
        end
               
        // One 64-bit copying
        for (low_ib = low_ib; low_ib <= high_ib ; low_ib++) begin 
          logic [7:0] wbyte = 0;
          for (int j=0; j<8; j++)
            wbyte[j] = pcie.DATA[(7-low_ib)*8 + j]; 
          tr.data[low_tr++] = wbyte;
        end          
  
      end

    endtask : receiveData  

    // -- Count Length --------------------------------------------------------
    // Count Data length in bytes
    function integer countLength(PcieTransaction tr);

      int bcount = (tr.byteCount == 0) ? 4096 : tr.byteCount;
      int len    = (tr.length    == 0) ? 1024 : tr.length;
       
      if (tr.transType == CPLD) begin
        logic [12:0] aux = (bcount + pcie.DATA[33:32] +3); //tr.lowerAddr[1:0];
        int cpl_last     = (aux[12:2] == len);

        if (cpl_last)
           countLength = bcount;
        else
           countLength = 4*len - pcie.DATA[33:32]; //tr.lowerAddr[1:0];         
      end
      else begin
         int minus = 0;
         case (tr.firstBE)
           F1111: minus += 0;
           F1110: minus += 1;
           F1100: minus += 2;
           F1000: minus += 3;           
           F0111: minus += 1; 
           F0011: minus += 2; 
           F0110: minus += 2; 
           F0100: minus += 3; 
           F0010: minus += 3; 
           F0001: minus += 3; 
         endcase 
         case (tr.lastBE)
           L1111: minus += 0;
           L0111: minus += 1;
           L0011: minus += 2;
           L0001: minus += 3;
           L0000: minus += 0;
         endcase;         
         
         countLength = 4*len - minus;
      end
          
    endfunction: countLength

    // -- Count Offset --------------------------------------------------------
    // Count initial data offset
    function integer countOffset(PcieTransaction tr);

      if (tr.transType == CPLD)
        countOffset = 4 + pcie.DATA[33:32]; //tr.lowerAddr[1:0]
      else begin
        case (tr.firstBE)
          F1111: countOffset = 0;
          F1110: countOffset = 1;
          F1100: countOffset = 2;
          F1000: countOffset = 3;
          F0111: countOffset = 0; 
          F0011: countOffset = 0; 
          F0110: countOffset = 1; 
          F0100: countOffset = 2; 
          F0010: countOffset = 1; 
          F0001: countOffset = 0;           
        endcase; 
        if (tr.transType == WR32) countOffset += 4; 
      end
          
    endfunction: countOffset   
         
  endclass : PcieMonitor

endpackage : pcie_monitor_pkg
