//
// pcie_monitor_pkg.sv: System Verilog PCI Express Monitor
// Copyright (C) 2007 CESNET
// Author(s): Tomas Malek <tomalek@liberouter.org>
//            Petr Kobierský <kobiersky@liberouter.org>
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
// $Id: pcie_monitor.sv 4234 2008-07-31 15:34:16Z xkobie00 $
//

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
    string  inst;                            // Monitor identification
    bit     enabled;                         // Monitor is enabled
    MonitorCbs cbs[$];                       // Callbacks list
    virtual iPcieTx.monitor pcie;            // Pcie Interface

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iPcieTx.monitor pcie
                 );
      this.inst        = inst;
      this.enabled     = 0;           // Monitor is disabled by default   
      this.pcie        = pcie;        // Store pointer interface 
    endfunction

    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(MonitorCbs cbs);
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

    // -- Run Monitor ---------------------------------------------------------
    // Receive transactions and send them for processing by call back
    task run();
      PcieTransaction transaction;
      Transaction tr;
      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        receiveTransaction(transaction); // Receive Transaction
        if (enabled) begin                                                           
          $cast(tr, transaction);
          // Call transaction preprocesing, if is available
          foreach (cbs[i]) cbs[i].pre_rx(tr, inst);
          // Call transaction postprocesing, if is available
          foreach (cbs[i]) cbs[i].post_rx(tr, inst);
        end
      end
    endtask : run



    // -- Wait for SOF --------------------------------------------------------
    // It waits until SOF and SRC_RDY
    task waitForSOF(); // Cekej dokud neni SOF A SRC RDY
      do begin
        if (pcie.cb_monitor.SOF_N || pcie.cb_monitor.SRC_RDY_N)
          @(pcie.cb_monitor);
      end while (pcie.cb_monitor.SOF_N || pcie.cb_monitor.SRC_RDY_N); //Detect Start of Packet
    endtask : waitForSOF
 
    // -- Wait for DST_RDY ----------------------------------------------------
    // It waits until DST_RDY and SRC_RDY
    task waitForDstRdy(); // Cekej dokud neni DST_RDY A SRC RDY
      do begin
        if (pcie.cb_monitor.DST_RDY_N || pcie.cb_monitor.SRC_RDY_N)
          @(pcie.cb_monitor);
      end while (pcie.cb_monitor.DST_RDY_N || pcie.cb_monitor.SRC_RDY_N); //Detect Destination Ready
    endtask : waitForDstRdy
   

    // -- Receive Transaction -------------------------------------------------
    // It receives Internal Bus transaction to tr object
    task receiveTransaction( PcieTransaction tr);
      // Receive first header
      waitForSOF();        // Wait for active SOF
      waitForDstRdy();     // Wait for src_dst_rd
      receiveHdr12(tr);    // Receive First Header

      if (pcie.cb_monitor.REM_N !=0) begin
        $write("Error: PCIe Monitor %s receive transaction without wrong REM_N: ", inst);
        $stop;
        end
        
      @(pcie.cb_monitor);  // Wait for next clock cycle
      // Receive second header / second header + data
      waitForDstRdy();     // Wait for src_dst_rdy

      if (tr.transType == RD32 && pcie.cb_monitor.REM_N != 8'b00001111) begin
        $write("Error: PCIe Monitor %s receive transaction with wrong REM_N: ", inst);
        $stop;
        end
      if (tr.transType != RD32 && pcie.cb_monitor.REM_N != 8'b00000000) begin
        $write("Error: PCIe Monitor %s receive transaction with wrong REM_N: ", inst);
        $stop;
        end    

      case (tr.transType)
         RD32: begin
            tr.address = {32'h00000000, pcie.cb_monitor.TD[63:32]};
            @(pcie.cb_monitor);
            end
         RD64: begin
            tr.address = pcie.cb_monitor.TD;
            @(pcie.cb_monitor);
            end
         WR32:
            receiveData(tr);
         WR64: begin
            tr.address = pcie.cb_monitor.TD;
            @(pcie.cb_monitor);
            waitForDstRdy();
            receiveData(tr);
            end
         CPLD:
            receiveData(tr);
      endcase;      
    endtask : receiveTransaction
    
    // -- Receive Header 1 + 2 ------------------------------------------------
    // Receive Header 1 + Header 2 (first DW word)
    task receiveHdr12(PcieTransaction tr);

      // parse Header 1 -----------------------------------
      // Get Transaction type
      case (pcie.cb_monitor.TD[62:56])
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

      tr.supported = 1;
      tr.error     = 0;
      tr.tc     = pcie.cb_monitor.TD[54:52];
      tr.td     = pcie.cb_monitor.TD[47];
      tr.ep     = pcie.cb_monitor.TD[46];
      tr.attr   = pcie.cb_monitor.TD[45:44];
      tr.length = pcie.cb_monitor.TD[41:32];
                 
      // parse Header 2 -----------------------------------
      // Read/Write header
      tr.requesterId    = pcie.cb_monitor.TD[31:16];
      tr.tag            = pcie.cb_monitor.TD[15: 8];
      tr.lastBE         = pcie.cb_monitor.TD[ 7: 4];
      tr.firstBE        = pcie.cb_monitor.TD[ 3: 0];      

      // Completion header
      tr.completerId    = pcie.cb_monitor.TD[31:16];
      tr.bcm            = pcie.cb_monitor.TD[12];
      tr.byteCount      = pcie.cb_monitor.TD[11: 0];      

      if (tr.transType == CPLD) begin
        case (pcie.cb_monitor.TD[15:13])
          C_CPLSTAT_OK :
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
      int trlen   = countLength(tr); // Length of valid data bytes
      int offset  = countOffset(tr); // Offset where starts first valid data in current word
      int word64  = (trlen + offset + 7)/8;  // Number of expected words
      
      int low_tr  = 0;
      int low_ib  = 0;
      int high_ib = 7;

      tr.data = new[trlen];    

      // WR32/CPLD Header 3 + DATA DW 0 -------------------
      if (tr.transType == CPLD) begin          
        tr.requesterId    = pcie.cb_monitor.TD[63:48];      
        tr.tag            = pcie.cb_monitor.TD[47:40];
        tr.lowerAddr      = pcie.cb_monitor.TD[38:32];
      end
      if (tr.transType == WR32)
        tr.address = {32'h00000000,pcie.cb_monitor.TD[63:32]};



      // DATA reception -----------------------------------
      for (int i=1; i <= word64; i++) begin // For all expected words
        waitForDstRdy();
        // first word
        if (i == 1) 
          low_ib = offset;
        else
          low_ib = 0;
          
        // last word
        if (i == word64) begin        
          high_ib  = ( ((trlen + offset) - 1) % 8);
          if (pcie.cb_monitor.EOF_N == 1) begin
            $write("Error (%t): Pcie Monitor %s receive transaction with wrong length: ", $time, inst);
            tr.display();
            $stop;
          end;
        end

        if ((pcie.cb_monitor.EOF_N == 1 && pcie.cb_monitor.REM_N != 0) ||
           (pcie.cb_monitor.EOF_N == 0 && pcie.cb_monitor.REM_N != 0  && high_ib >=4) ||
           (pcie.cb_monitor.EOF_N == 0 && pcie.cb_monitor.REM_N != 8'b00001111 && high_ib < 4)) begin
           $write("Error: PCIe Monitor %s receive transaction without wrong REM_N: ", inst);
           tr.display();
           $stop;
        end




        // One 64-bit copying
        for (low_ib=low_ib; low_ib <= high_ib;low_ib++) begin 
          logic [7:0] wbyte = 0;
          for (int j=0; j<8; j++)
            wbyte[j] = pcie.cb_monitor.TD[(7-low_ib)*8 + j]; 
          tr.data[low_tr++] = wbyte;
        end          
        @(pcie.cb_monitor);
      end
    endtask : receiveData  

    // -- Count Length --------------------------------------------------------
    // Count Data length in bytes
    function integer countLength(PcieTransaction tr);
      int bcount = (tr.byteCount == 0) ? 4096 : tr.byteCount;
      int len    = (tr.length    == 0) ? 1024 : tr.length;

      if (tr.transType == CPLD) begin
        int cpl_last = (bcount <= (len*4-pcie.cb_monitor.TD[33:32])); // tr.lowerAddr[1:0];

        if (cpl_last)
           countLength = bcount;
        else
           countLength = 4*len - pcie.cb_monitor.TD[33:32]; //tr.lowerAddr[1:0];         
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
           F0001: minus += 3; 
           F0100: minus += 3; 
           F0010: minus += 3; 
           F0110: minus += 2; 
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
        countOffset = 4 + pcie.cb_monitor.TD[33:32]; //tr.lowerAddr[1:0]
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
