//
// pcie_driver_pkg.sv: PCIe Driver
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
// $Id: pcie_driver_pkg.sv 2981 2008-06-30 09:16:01Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package pcie_driver_pkg;

  import pcie_transaction_pkg::*; // Transaction package

  // --------------------------------------------------------------------------
  // -- PCIe Driver Callbacks
  // --------------------------------------------------------------------------
  /* This is a abstract class for creating objects which get benefits from
   * function callback. This object can be used with PcieDriver
   * class. Inheritence from this basic class is neaded for functionality.
   */
  class PcieDriverCbs;
    
    // -- Class Methods --

    // ------------------------------------------------------------------------
    // Function is called before is transaction sended - usefull for
    // transaction modification
    virtual task pre_tx(ref PcieTransaction transaction, integer driverId);
      // By default, callback does nothing
    endtask: pre_tx
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended throw interface - 
    // usefull for scoreboards
    virtual task post_tx(PcieTransaction transaction, integer driverId);
      // By default, callback does nothing
    endtask: post_tx
  
  endclass : PcieDriverCbs

  // --------------------------------------------------------------------------
  // -- PCI Express Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to PCIe
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transcaction by calling "sendTransaction" function.
   */
  class PcieDriver;

    // -- Public Class Atributes --


    // -- Private Class Atributes --
    integer   driverId;                         // Driver identification
    bit       enabled;                          // Driver is enabled
    tPcieTransMbx transMbx;                     // Transaction mailbox
    PcieDriverCbs cbs[$];                       // Callbacks list
    virtual   iPcieRx.driver pcie;              // PCIe interface
    virtual   iPcieCfg.driver pcieCfg;          // PCIe configuration interface    
 
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( tPcieTransMbx           transMbx,
                   virtual iPcieRx.driver  pcie,
                   virtual iPcieCfg.driver pcieCfg,                   
                   integer                 driverId );
                   
      this.enabled     = 0;            // Driver is disabled by default
      this.pcie        = pcie;         // Store pointer interface 
      this.pcieCfg     = pcieCfg;      // Store pointer interface       
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.driverId    = driverId;     // Store driver identifier
      
      // Setting default values for PCIe interface
      this.pcie.SOF_N     = 1;
      this.pcie.EOF_N     = 1;
      this.pcie.SRC_RDY_N = 1;      
      this.pcie.REM_N     = 8'hFF;      
      this.pcie.BAR_HIT_N = 7'b1111111; // all bar spaces are accepted  
      this.pcie.DATA      = 64'h0000000000000000;
 
      // Setting default values for PCIe interface (unsupported so far)      
      this.pcie.ERR_FWD_N = 1;
      this.pcie.SRC_DSC_N = 1;
      this.pcie.FC_PH_AV  = 0;
      this.pcie.FC_PD_AV  = 0;
      this.pcie.FC_NPH_AV = 0;
      this.pcie.FC_NPD_AV = 0;     

      // Setting values for PCIe configuration interface
      this.pcieCfg.BUS_NUM          = 1;
      this.pcieCfg.DEVICE_NUM       = 2;
      this.pcieCfg.FUNC_NUM         = 3;
      this.pcieCfg.MAX_PAYLOAD_SIZE = 1; // See more p.342 of PCIe specification
      
    endfunction: new
    
    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(PcieDriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks

    // -- Set Maximal Payload Size --------------------------------------------
    // Set Max. size of packet payload, See more p.342 of PCIe specification
    function void setMaxPayloadSize(integer size);
      case (size)
        128: 
          this.pcieCfg.MAX_PAYLOAD_SIZE = 3'b000;
        256: 
          this.pcieCfg.MAX_PAYLOAD_SIZE = 3'b001;
        512: 
          this.pcieCfg.MAX_PAYLOAD_SIZE = 3'b010;
        1024: 
          this.pcieCfg.MAX_PAYLOAD_SIZE = 3'b011;
        2048: 
          this.pcieCfg.MAX_PAYLOAD_SIZE = 3'b100;
        4096: 
          this.pcieCfg.MAX_PAYLOAD_SIZE = 3'b101;          
        default
          this.pcieCfg.MAX_PAYLOAD_SIZE = 1;
      endcase;      
    endfunction : setMaxPayloadSize
    
    // -- Enable Driver -------------------------------------------------------
    // Enable driver and runs driver process
    task setEnabled();
      enabled = 1; // Driver Enabling
      fork         
        run();     // Creating driver subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Driver ------------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable driver, after sending last transaction it ends
    endtask : setDisabled
    
    // -- Send Transaction ----------------------------------------------------
    // Send transaction to Internal Bus interface
    task sendTransaction( PcieTransaction transaction );
      
      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(transaction, driverId);                 
      
      // Display transaction for debug purposes
        // transaction.display(1);

      // Wait before sending transaction
      if (pcie.CLK == 0) @(posedge pcie.CLK);
      repeat (transaction.txDelay) @(posedge pcie.CLK);
      
      // Send transaction
      case (transaction.transType)
        WR32:
          sendWR32(transaction);
        WR64:
          sendWR64(transaction);
        RD32:
          sendRD32(transaction);
        RD64:
          sendRD64(transaction);
        CPLD:
          sendCPLD(transaction);
      endcase;

      // Set not ready 
      pcie.SOF_N     = 1;
      pcie.EOF_N     = 1;
      pcie.SRC_RDY_N = 1;
      pcie.REM_N     = 8'hFF;
      pcie.BAR_HIT_N = 7'b1111111;
    
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(transaction, driverId);
    endtask : sendTransaction

    // -- Private Class Methods --
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      PcieTransaction transaction;
      @(posedge pcie.CLK);                 // Wait for clock
      while (enabled) begin                // Repeat while enabled        
        transMbx.get(transaction);         // Get transaction from mailbox
        waitForAccept();                   // Wait for destination ready (DST_RDY_N)    

        // if NP_OK_N is active, only write or completion transaction can be generated
        if ((pcie.NP_OK_N == 0) || ((transaction.transType != RD32)&&(transaction.transType != RD64))) 
          sendTransaction(transaction);                                    
        else
          @(posedge pcie.CLK);          
      end
    endtask : run
    
    // -- Wait for accept -----------------------------------------------------
    // Wait for accepting of 64 bits word of transaction
    task waitForAccept();
      logic data_writen;
      do begin
        @(negedge pcie.CLK); 
        data_writen= ! pcie.DST_RDY_N;        // Store DST_RDY status 
        @(posedge pcie.CLK);                  // Wait for Clock
      end while (! data_writen);              // Repeat until succesfull write
    endtask : waitForAccept

    // -- Wait for accept -----------------------------------------------------
    // Wait for accepting of 64 bits word of transaction
    task waitForNP_OK_N();
      logic data_writen;
      do begin
        @(negedge pcie.CLK); 
        data_writen= ! pcie.NP_OK_N;          // Store DST_RDY status 
        @(posedge pcie.CLK);                  // Wait for Clock
      end while (! data_writen);              // Repeat until succesfull write
    endtask : waitForNP_OK_N    

    // -- Random wait ---------------------------------------------------------
    // Random wait during sending transaction (Set SRC_RDY_N to 1)
    task randomWait(PcieTransaction transaction);
      repeat (transaction.getRandomWait()) begin
        pcie.SRC_RDY_N = 1;
        @(posedge pcie.CLK); // Wait for send
      end;
    endtask : randomWait

    // -- Count Offset --------------------------------------------------------
    // Count how data is aligned in first data word
    function integer countOffset(logic [3:0] firstBE);
      case (firstBE)
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
    endfunction : countOffset

    // -- Count Bar hit -------------------------------------------------------
    // Count bar hit as vector from eBarHitType in transaction
    function logic [6:0] countBarHit(eBarHitType barhit);
      case (barhit)
        B1111110: countBarHit = 7'b1111110;
        B1111101: countBarHit = 7'b1111101;
        B1111011: countBarHit = 7'b1111011;
        B1110111: countBarHit = 7'b1110111;
        B1101111: countBarHit = 7'b1101111;
        B1011111: countBarHit = 7'b1011111;
        B0111111: countBarHit = 7'b0111111;        
      endcase;
    endfunction : countBarHit    
    
    // -- Send Header 1 + 2 ---------------------------------------------------
    // Send Header 1 + Header 2 (first DW word)
    task sendHdr12(logic [63:0] hdr, eBarHitType barHitN);
      pcie.DATA      = hdr;
      pcie.SOF_N     = 0;
      pcie.EOF_N     = 1;
      pcie.SRC_RDY_N = 0;
      pcie.REM_N     = 8'h00;    
      pcie.BAR_HIT_N = countBarHit(barHitN);
      waitForAccept(); // Wait for accepting
    endtask : sendHdr12

    // -- Send Header 3 + 4 ---------------------------------------------------
    // Send Header 3 + Header 4 (second DW word) - in case of write
    task sendHdr34_wr(logic [63:0] hdr);
      pcie.DATA      = hdr;
      pcie.SOF_N     = 1;
      pcie.EOF_N     = 1;
      pcie.SRC_RDY_N = 0;
      pcie.REM_N     = 8'h00;      
      waitForAccept(); // Wait for accepting
    endtask : sendHdr34_wr    

    // -- Send Header 3 + 4 ---------------------------------------------------
    // Send Header 3 + Header 4 (second DW word) - in case of read
    task sendHdr34_rd(logic [63:0] hdr, logic [7:0] rem);
      
      if (rem == 8'h00)
        pcie.DATA    = hdr;
      else
        pcie.DATA    = {hdr[31:0],32'h00000000}; 
      
      pcie.SOF_N     = 1;
      pcie.EOF_N     = 0;
      pcie.SRC_RDY_N = 0;
      pcie.REM_N     = rem;      
      waitForAccept(); // Wait for accepting
    endtask : sendHdr34_rd        

    // -- Send transaction data -----------------------------------------------
    // Send transaction data, in case of 3-HDR data transaction -> attach header 3
    task sendData(PcieTransaction tr);
      logic data[];      // Data to write
      integer offset;    // offset for data to write

      // Count offset for data in first 64-bit word
      offset = (tr.transType == CPLD) ? tr.lowerAddr[1:0] : countOffset(tr.firstBE);
      if ((tr.transType == WR32) || (tr.transType == CPLD)) offset += 4; // hdr 3 has to be attached
      
      // Create bit array for saving write data
      data = new[(tr.data.size + offset)*8];

      // Clear part of bit array (data offset part)
      for (integer i = 0; i < offset*8; i++)
        data[i]=1'b0;
      
      // In case of 3-hdr data transaction -> header 3 is attached
      if (tr.transType == WR32) begin
        for (integer i=0; i < 4; i++) 
          for (integer j=0; j < 8; j++)             
            data[24-i*8+j] = tr.address[i*8 + j];         
      end  
      if (tr.transType == CPLD) begin
        logic [31:0] concat = {tr.busnum_req,tr.devnum_req,tr.funcnum_req,tr.tag,1'b0,tr.lowerAddr};
        for (integer i=0; i < 4; i++) 
          for (integer j=0; j < 8; j++)             
            data[24-i*8+j] = concat[i*8 + j];               
      end
                          
      // Allign data from transaction to bit array
      for (integer i=0; i < tr.data.size; i++)
        for (integer j=0; j < 8; j++)
          data[8*i+j+(offset*8)] = tr.data[i][j];
 
          
      // Send Data ----------------------------------------
      for (integer i=0; i < data.size; i=i+64) begin
        logic [63:0] write_data = 64'h0000000000000000;
        // Fill data variable
        for (integer j=0; j < 64; j++)
          if ((i+j) < data.size)
            write_data[j] = data[i+j];
        // Generate signals
        pcie.DATA      = {write_data[ 7: 0],write_data[15: 8],write_data[23:16],write_data[31:24],
                          write_data[39:32],write_data[47:40],write_data[55:48],write_data[63:56]};
        pcie.SOF_N     = 1;
        pcie.EOF_N     = 1;
        pcie.SRC_RDY_N = 0;                              
        pcie.REM_N     = 8'h00;
        
        if ((i+64) >= data.size) begin
          pcie.EOF_N   = 0;
          if ((data.size - i) <= 32) pcie.REM_N = 8'h0F;
        end
           
        waitForAccept();         // Wait for accepting
        if ((i+64) < data.size)  // If NOT EOF
          randomWait(tr);        // Random wait during transaction
       end
    endtask : sendData

    // -- Send WR32 -----------------------------------------------------------
    // Send WR32 transaction
    task sendWR32 ( PcieTransaction tr);
      logic [31:0] hdr1;  
      logic [31:0] hdr2;  
      logic [ 6:0] command = (tr.supported) ? CMD_WR32 : 7'b1111111; // supported/unsupported transaction
          
      // Assembly headers
      hdr1 = {1'b0,command,1'b0,tr.tc,4'b0000,tr.td,tr.ep,tr.attr,2'b00,tr.length};
      hdr2 = {tr.busnum_req,tr.devnum_req,tr.funcnum_req,tr.tag,tr.lastBE,tr.firstBE};
     
      sendHdr12({hdr1,hdr2},tr.barHitN); // Send header 1 + header 2 (first DW word)
      randomWait(tr);                    // Random wait during transaction
             
      sendData(tr);                      // Send header 3 + Data
    endtask : sendWR32

    // -- Send WR64 -----------------------------------------------------------
    // Send WR64 transaction
    task sendWR64 ( PcieTransaction tr);
      logic [31:0] hdr1;  
      logic [31:0] hdr2;  
      logic [ 6:0] command = (tr.supported) ? CMD_WR64 : 7'b1111111; // supported/unsupported transaction
          
      // Assembly headers
      hdr1 = {1'b0,command,1'b0,tr.tc,4'b0000,tr.td,tr.ep,tr.attr,2'b00,tr.length};
      hdr2 = {tr.busnum_req,tr.devnum_req,tr.funcnum_req,tr.tag,tr.lastBE,tr.firstBE};
     
      sendHdr12({hdr1,hdr2},tr.barHitN);   // Send header 1 + header 2 (first DW word)
      randomWait(tr);                      // Random wait during transaction

      sendHdr34_wr(tr.address);            // Send header 3 + header 4 (second DW word)
      randomWait(tr);                      // Random wait during transaction      
             
      sendData(tr);                        // Send Data
    endtask : sendWR64    

    // -- Send RD32 -----------------------------------------------------------
    // Send RD32 transaction
    task sendRD32 ( PcieTransaction tr);
      logic [31:0] hdr1;  
      logic [31:0] hdr2;
      logic [ 6:0] command = (tr.supported) ? CMD_RD32 : 7'b1111111; // supported/unsupported transaction      
          
      // Assembly headers
      hdr1 = {1'b0,command,1'b0,tr.tc,4'b0000,tr.td,tr.ep,tr.attr,2'b00,tr.length};
      hdr2 = {tr.busnum_req,tr.devnum_req,tr.funcnum_req,tr.tag,tr.lastBE,tr.firstBE};
     
      sendHdr12({hdr1,hdr2},tr.barHitN);// Send header 1 + header 2 (first DW word)
      randomWait(tr);                   // Random wait during transaction

      sendHdr34_rd(tr.address,8'h0F);   // Send header 3 + header 4 (second DW word)
    endtask : sendRD32        

    // -- Send RD64 -----------------------------------------------------------
    // Send RD64 transaction
    task sendRD64 ( PcieTransaction tr);
      logic [31:0] hdr1;  
      logic [31:0] hdr2;  
      logic [ 6:0] command = (tr.supported) ? CMD_RD64 : 7'b1111111; // supported/unsupported transaction      
          
      // Assembly headers
      hdr1 = {1'b0,command,1'b0,tr.tc,4'b0000,tr.td,tr.ep,tr.attr,2'b00,tr.length};
      hdr2 = {tr.busnum_req,tr.devnum_req,tr.funcnum_req,tr.tag,tr.lastBE,tr.firstBE};
     
      sendHdr12({hdr1,hdr2},tr.barHitN); // Send header 1 + header 2 (first DW word)
      randomWait(tr);                    // Random wait during transaction

      sendHdr34_rd(tr.address,8'h00);    // Send header 3 + header 4 (second DW word)
    endtask : sendRD64            

    // -- Send CPLD -----------------------------------------------------------
    // Send CPLD transaction
    task sendCPLD ( PcieTransaction tr);
      logic [31:0] hdr1;  // Header 1
      logic [31:0] hdr2;  // Header 2
      logic [ 6:0] command = (tr.supported) ? CMD_CPLD : 7'b1111111; // supported/unsupported transaction      
          
      // Assembly headers
      hdr1 = {1'b0,command,1'b0,tr.tc,4'b0000,tr.td,tr.ep,tr.attr,2'b00,tr.length};
      hdr2 = {tr.busnum_cpl,tr.devnum_cpl,tr.funcnum_cpl,tr.cplStatus,tr.bcm,tr.byteCount};
     
      sendHdr12({hdr1,hdr2},tr.barHitN); // Send header 1 + header 2 (first DW word)
      randomWait(tr);                    // Random wait during transaction
             
      sendData(tr);                      // Send header 3 + Data
    endtask : sendCPLD    
    
  endclass : PcieDriver

endpackage : pcie_driver_pkg



