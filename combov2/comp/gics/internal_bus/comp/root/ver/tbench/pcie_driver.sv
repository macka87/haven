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
// $Id: pcie_driver.sv 3667 2008-07-17 13:43:18Z xkobie00 $
//

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
    string    inst;                             // Driver identification
    bit       enabled;                          // Driver is enabled
    tTransMbx transMbx;                         // Transaction mailbox
    DriverCbs cbs[$];                           // Callbacks list
    virtual   iPcieRx.driver pcie;              // PCIe interface

    // ----
    rand bit enTxDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int txDelayEn_wt             = 0; 
      int txDelayDisable_wt        = 1;

    rand integer txDelay; // Delay between transactions
      // Delay between transactions limits
      int txDelayLow          = 0;
      int txDelayHigh         = 3;
    // ----

    // ----
    rand bit enInsideTxDelay;     // Enable/Disable delays inside transaction
      // Enable/Disable delays inside transaction weights
      int insideTxDelayEn_wt       = 0; 
      int insideTxDelayDisable_wt  = 1;
      // Minimal/Maximal delay between transaction words
      int insideTxDelayLow         = 0;
      int insideTxDelayHigh        = 3;
    // ----
    
    // -- Constrains --
    constraint cDelays {
      enTxDelay dist { 1'b1 := txDelayEn_wt,
                       1'b0 := txDelayDisable_wt
                     };

      txDelay inside {
                      [txDelayLow:txDelayHigh]
                     };

      enInsideTxDelay dist { 1'b1 := insideTxDelayEn_wt,
                             1'b0 := insideTxDelayDisable_wt
                     };
      }
 
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string                  inst,
                   tTransMbx               transMbx,
                   virtual iPcieRx.driver  pcie);

      this.inst        = inst;         // Store driver identifier
      this.enabled     = 0;            // Driver is disabled by default
      this.pcie        = pcie;         // Store pointer interface 
      this.transMbx    = transMbx;     // Store pointer to mailbox
      
      // Setting default values for PCIe interface
      this.pcie.cb_driver.SOF_N         <= 1;
      this.pcie.cb_driver.EOF_N         <= 1;
      this.pcie.cb_driver.SRC_RDY_N     <= 1;      
      this.pcie.cb_driver.REM_N         <= 8'hFF;      
      this.pcie.cb_driver.BAR_HIT_N     <= 7'b1111111; // all bar spaces are accepted
      this.pcie.cb_driver.DATA          <= 64'h0000000000000000;
 
      // Setting default values for PCIe interface (unsupported so far)      
      this.pcie.cb_driver.ERR_FWD_N     <= 1;
      this.pcie.cb_driver.SRC_DSC_N     <= 1;
      this.pcie.cb_driver.FC_PH_AV      <= 0;
      this.pcie.cb_driver.FC_PD_AV      <= 0;
      this.pcie.cb_driver.FC_NPH_AV     <= 0;
      this.pcie.cb_driver.FC_NPD_AV     <= 0;     
    endfunction: new
    
    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
       
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
    task sendTransaction(PcieTransaction transaction);
      Transaction tr;
      $cast(tr, transaction);

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);                 
      
      // Wait before sending transaction
      if (enTxDelay) repeat (txDelay) @(pcie.cb_driver);

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
        CPLD, CPLD_LAST:
          sendCPLD(transaction);
      endcase;

      // Set not ready 
      pcie.cb_driver.SOF_N     <= 1;
      pcie.cb_driver.EOF_N     <= 1;
      pcie.cb_driver.SRC_RDY_N <= 1;
      pcie.cb_driver.REM_N     <= 8'hFF;
      pcie.cb_driver.BAR_HIT_N <= 7'b1111111;
   
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);
    endtask : sendTransaction

    // -- Private Class Methods --
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      PcieTransaction transaction;
      Transaction to;
      @(pcie.cb_driver);           // Wait for clock
      while (enabled) begin        // Repeat while enabled        
        transMbx.get(to);          // Get transaction from mailbox
        $cast(transaction,to);
        assert(randomize());
        //if NP_OK_N is active, only write or completion transaction can be generated
        if ((pcie.cb_driver.NP_OK_N == 0) || ((transaction.transType != RD32) && (transaction.transType != RD64))) 
          sendTransaction(transaction);                                    
        else
          @(pcie.cb_driver);        
        end
    endtask : run

    // -- Wait for accept -----------------------------------------------------
    // Wait for accepting of 64 bits word of transaction
    task waitForAccept();
      while (pcie.cb_driver.DST_RDY_N) begin
        @(pcie.cb_driver); 
      end;
    endtask : waitForAccept

    //-- Random intertransaction wait -----------------------------------------
    function integer getRandomWait();
       if (enInsideTxDelay)
         return $urandom_range(insideTxDelayLow, insideTxDelayHigh);
       else
         return 0;
    endfunction : getRandomWait

    // -- Random wait ---------------------------------------------------------
    // Random wait during sending transaction (Set SRC_RDY_N to 1)
    task randomWait();
      repeat (getRandomWait()) begin
        pcie.cb_driver.SRC_RDY_N <= 1;
        @(pcie.cb_driver); // Wait for send
      end;
        pcie.cb_driver.SRC_RDY_N <= 0;
    endtask : randomWait

    // -- Send WR32 -----------------------------------------------------------
    // Send WR32 transaction
    task sendWR32 ( PcieTransaction tr);
      logic [31:0] hdr1;  
      logic [31:0] hdr2;  
      logic [ 6:0] command = (tr.supported) ? CMD_WR32 : 7'b1111111; // supported/unsupported transaction
          
      // Assembly headers
      hdr1 = {1'b0,command,1'b0,tr.tc,4'b0000,tr.td,tr.ep,tr.attr,2'b00,tr.length};
      hdr2 = {tr.requesterId,tr.tag,tr.lastBE,tr.firstBE};
     
      randomWait();                    // Random wait during transaction
      sendHdr12({hdr1,hdr2},tr.barHitN); // Send header 1 + header 2 (first DW word)
      @(pcie.cb_driver);    
      waitForAccept();                   // Wait for accept
           

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
      hdr2 = {tr.requesterId,tr.tag,tr.lastBE,tr.firstBE};
     
      randomWait();                      // Random wait during transaction
      sendHdr12({hdr1,hdr2},tr.barHitN); // Send header 1 + header 2 (first DW word)
      @(pcie.cb_driver); 
      waitForAccept();                   // Wait for accept

      randomWait();                      // Random wait during transaction
      sendHdr34_wr(tr.address);            // Send header 3 + header 4 (second DW word)
      @(pcie.cb_driver);                 // Random wait during transaction  
      waitForAccept();                   // Wait for accept
                 
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
      hdr2 = {tr.requesterId,tr.tag,tr.lastBE,tr.firstBE};
     
      randomWait();                      // Random wait during transaction
      sendHdr12({hdr1,hdr2},tr.barHitN);// Send header 1 + header 2 (first DW word)
      @(pcie.cb_driver); 
      waitForAccept();                   // Wait for accept

      randomWait();                      // Random wait during transaction
      sendHdr34_rd(tr.address,8'h0F);   // Send header 3 + header 4 (second DW word)
      @(pcie.cb_driver); 
      waitForAccept();                   // Wait for accept

    endtask : sendRD32        

    // -- Send RD64 -----------------------------------------------------------
    // Send RD64 transaction
    task sendRD64 ( PcieTransaction tr);
      logic [31:0] hdr1;  
      logic [31:0] hdr2;  
      logic [ 6:0] command = (tr.supported) ? CMD_RD64 : 7'b1111111; // supported/unsupported transaction      
          
      // Assembly headers
      hdr1 = {1'b0,command,1'b0,tr.tc,4'b0000,tr.td,tr.ep,tr.attr,2'b00,tr.length};
      hdr2 = {tr.requesterId,tr.tag,tr.lastBE,tr.firstBE};
     
      randomWait();                      // Random wait during transaction
      sendHdr12({hdr1,hdr2},tr.barHitN); // Send header 1 + header 2 (first DW word)
      @(pcie.cb_driver); 
      waitForAccept();                   // Wait for accept

      randomWait();                      // Random wait during transaction
      sendHdr34_rd(tr.address,8'h00);    // Send header 3 + header 4 (second DW word)
      @(pcie.cb_driver); 
      waitForAccept();                   // Wait for accept

    endtask : sendRD64            

    // -- Send CPLD -----------------------------------------------------------
    // Send CPLD transaction
    task sendCPLD ( PcieTransaction tr);
      logic [31:0] hdr1;  // Header 1
      logic [31:0] hdr2;  // Header 2
      logic [ 6:0] command = (tr.supported) ? CMD_CPLD : 7'b1111111; // supported/unsupported transaction      
          
      // Assembly headers
      hdr1 = {1'b0,command,1'b0,tr.tc,4'b0000,tr.td,tr.ep,tr.attr,2'b00,tr.length};
      hdr2 = {tr.completerId,tr.cplStatus,tr.bcm,tr.byteCount};
     
      randomWait();                       // Random wait during transaction
      sendHdr12({hdr1,hdr2},tr.barHitN);  // Send header 1 + header 2 (first DW word)
      @(pcie.cb_driver);                  // Random wait during transaction
      waitForAccept();                    // Wait for accept
           
      sendData(tr);                       // Send header 3 + Data
    endtask : sendCPLD    

    // -- Send Header 1 + 2 ---------------------------------------------------
    // Send Header 1 + Header 2 (first DW word)
    task sendHdr12(logic [63:0] hdr, eBarHitType barHitN);
      pcie.cb_driver.DATA      <= hdr;
      pcie.cb_driver.SOF_N     <= 0;
      pcie.cb_driver.EOF_N     <= 1;
      pcie.cb_driver.SRC_RDY_N <= 0;
      pcie.cb_driver.REM_N     <= 8'h00;    
      pcie.cb_driver.BAR_HIT_N <= countBarHit(barHitN);
    endtask : sendHdr12

    // -- Send Header 3 + 4 ---------------------------------------------------
    // Send Header 3 + Header 4 (second DW word) - in case of write
    task sendHdr34_wr(logic [63:0] hdr);
      pcie.cb_driver.DATA      <= hdr;
      pcie.cb_driver.SOF_N     <= 1;
      pcie.cb_driver.EOF_N     <= 1;
      pcie.cb_driver.SRC_RDY_N <= 0;
      pcie.cb_driver.REM_N     <= 8'h00;      
    endtask : sendHdr34_wr    

    // -- Send Header 3 + 4 ---------------------------------------------------
    // Send Header 3 + Header 4 (second DW word) - in case of read
    task sendHdr34_rd(logic [63:0] hdr, logic [7:0] rem);
      if (rem == 8'h00)
        pcie.cb_driver.DATA    <= hdr;
      else
        pcie.cb_driver.DATA    <= { hdr[31:0],32'h00000000 }; 
      pcie.cb_driver.SOF_N     <= 1;
      pcie.cb_driver.EOF_N     <= 0;
      pcie.cb_driver.SRC_RDY_N <= 0;
      pcie.cb_driver.REM_N     <= rem;      
    endtask : sendHdr34_rd        

    // -- Send transaction data -----------------------------------------------
    // Send transaction data, in case of 3-HDR data transaction -> attach header 3
    task sendData(PcieTransaction tr);
      logic data[];      // Data to write
      integer offset;    // offset for data to write

      // Count offset for data in first 64-bit word
      offset = (tr.transType == CPLD || tr.transType == CPLD_LAST) ? tr.lowerAddr[1:0] : countOffset(tr.firstBE);
      if (tr.transType == WR32 || tr.transType == CPLD || tr.transType == CPLD_LAST) offset += 4; // hdr 3 has to be attached
      
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
      if (tr.transType == CPLD || tr.transType == CPLD_LAST) begin
        logic [31:0] concat = {tr.requesterId, tr.tag, 1'b0, tr.lowerAddr};
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


        randomWait();    // Random wait during transaction
        // Generate signals
        pcie.cb_driver.DATA      <= {write_data[ 7: 0],write_data[15: 8],write_data[23:16],write_data[31:24],
                          write_data[39:32],write_data[47:40],write_data[55:48],write_data[63:56]};
        pcie.cb_driver.SOF_N     <= 1;
        pcie.cb_driver.EOF_N     <= 1;
        pcie.cb_driver.SRC_RDY_N <= 0;                              
        pcie.cb_driver.REM_N     <= 8'h00;
        if ((i+64) >= data.size) begin
          pcie.cb_driver.EOF_N   <= 0;
          if ((data.size - i) <= 32) pcie.cb_driver.REM_N <= 8'h0F;
        end
        @(pcie.cb_driver);     // Random wait during transaction
        waitForAccept();       // Wait for accept

       end
    endtask : sendData
 
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

endclass : PcieDriver

