/*!
 * \file ib_downstream.sv
 * \brief InternalBus Downstream Modul
 * \author Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 * \date 2009
 */  
 /* 
 * Copyright (C) 2009 CESNET
 *
 * LICENSE TERMS
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * 3. Neither the name of the Company nor the names of its contributors
 *    may be used to endorse or promote products derived from this
 *    software without specific prior written permission.
 *
 * This software is provided ``as is'', and any express or implied
 * warranties, including, but not limited to, the implied warranties of
 * merchantability and fitness for a particular purpose are disclaimed.
 * In no event shall the company or contributors be liable for any
 * direct, indirect, incidental, special, exemplary, or consequential
 * damages (including, but not limited to, procurement of substitute
 * goods or services; loss of use, data, or profits; or business
 * interruption) however caused and on any theory of liability, whether
 * in contract, strict liability, or tort (including negligence or
 * otherwise) arising in any way out of the use of this software, even
 * if advised of the possibility of such damage.
 *
 * $Id: ib_downstream.sv 15016 2010-08-12 12:32:34Z xsanta06 $
 *
 */
 
  import sv_dma_module_gen_pkg::*;
  import test_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- InternalBus Downstream Modul
  // --------------------------------------------------------------------------
  
  /*!
   * \brief InternalBus Downstream Modul
   * 
   * This class is responsible for modul initialization and sends transactions (pointers requests, pointers values and data) to InternalBus.down interface.
   * 
   * \param pDataWidth - data width
   * \param pFLows - count of flows
   * \param pPageSize - size of one page
   * \param pPageCount - count of size in one flow                
   */
  class IbDownstream #(int pDataWidth = 64, int pFlows = 4, 
                       int pPageSize = 4096, int pPageCount = 2);
    
    //! Modul enabling
    bit       enabled;
    //! InternalBus Transactions Queue
    InternalBusTransaction transQue[$];
    //! DMA Modul software with RAM
    DmaModuleSW #(pDataWidth,pFlows,pPageSize,pPageCount) dmaModul;
    //! Virtual interface InternalBus.down  
    virtual iInternalBusDown.ib_down_tb #(pDataWidth) ib_down; 
    
    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates modul object and sets default values of InternalBus interface signals 
     */     
    function new ( virtual iInternalBusDown.ib_down_tb #(pDataWidth) ib_down,
                   DmaModuleSW #(pDataWidth,pFlows,pPageSize,pPageCount) dmaModul
                   );
      this.enabled     = 0;         // modul is disabled by default
      this.dmaModul    = dmaModul;
      this.ib_down     = ib_down;
      // Setting default values for Internal Bus interface
      this.ib_down.ib_down_cb.DATA      <= 0;
      this.ib_down.ib_down_cb.SOP_N     <= 1;
      this.ib_down.ib_down_cb.EOP_N     <= 1;
      this.ib_down.ib_down_cb.SRC_RDY_N <= 1;
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Enable Modul 
    /*!
     * Enable Modul and runs Modul process
     */     
    task setEnabled();
      enabled = 1; // Modul Enabling
      fork         
         run();                // Creating Ib Downstream subprocess
      join_none;               // Don't wait for ending
    endtask : setEnabled
        
    // ------------------------------------------------------------------------
    //! Disable Modul 
    task setDisabled();
      enabled = 0; // Disable Modul
    endtask : setDisabled

    // ------------------------------------------------------------------------
    //! DUT (DMA Module Gen) Initialization 
    /*!
     * 1. Descriptor manager initialization
     *
     * \param ctrlNo - controller number           
     * \param pDescBaseAddr - Descriptor Manager base address           
     */     
    task initDescManagerRx(int ctrlNo, bit send = 0);
      // Descriptor Manager initialization
      initDM(2*ctrlNo, DESC_BASE_ADDR);
      if (send)
        sendTransaction(transQue.pop_front());
      
    endtask : initDescManagerRx

    // ------------
    task initDescManagerTx(int ctrlNo, bit send = 0);
      // Descriptor Manager initialization
      initDM(2*ctrlNo+1, DESC_BASE_ADDR);
      if (send) 
        sendTransaction(transQue.pop_front());
      
    endtask : initDescManagerTx

    // ------------------------------------------------------------------------
    //! InternaBusDownstream processing 
    /*!
     * Function puts InternalBus transaction into transaction queue
     * \param tr - InternalBus transacion    
     */      
    task callIbDownstream(InternalBusTransaction tr);
      transQue.push_back(tr);
    endtask : callIbDownstream
    
    // ------------------------------------------------------------------------
    //! Run InternalBus Downstream Modul
    /*!
     * Starts InternalBus Downstream processing
     */      
    task run();
      InternalBusTransaction transaction = new();
      int offset; // Data offset
      while (enabled) begin
        while (!transQue.size()) @(ib_down.ib_down_cb);  // Wait while queue is empty
        transaction=transQue.pop_front();
        // get data form RAM
        if (transaction.transType == RDC) dmaModul.getData(transaction);
        // send transaction to InternalBus.down interface 
        sendTransaction(transaction);
      end
    endtask : run
    
    // ------------------------------------------------------------------------
    //! Send Transaction 
    /*!
     * Send transaction to Internal Bus interface
     * \param tr - InternalBus transacion    
     */      
    task sendTransaction(InternalBusTransaction tr);
      logic [63:0] hdr0; // Header data0
      logic [63:0] hdr1; // Header data1

      // Assembly headers
      case (tr.transType)
        L2LW:
          begin
            hdr0 = {tr.localAddr,tr.tag, tr.length, L2LW_TYPE};
            hdr1 = tr.globalAddr;
          end  
        L2LR:
          begin
            hdr0 = {tr.localAddr,tr.tag, tr.length, L2LR_TYPE};
            hdr1 = tr.globalAddr;
          end  
        RDC:
          begin
            hdr0 = {tr.localAddr, tr.tag, tr.length, RDC_TYPE};
            hdr1 = tr.globalAddr;
          end  
      endcase
      
      sendHdr0(hdr0);    // Send header 0
      randomWait(tr);    // Random wait during transaction

      if (tr.transType == L2LR) 
        sendHdr1(hdr1, 0); // Send header 1 with eop
      else begin
        sendHdr1(hdr1, 1); // Send header 1 without eop
        randomWait(tr);    // Random wait during transaction
        sendData(tr); // Send Data
      end  
    endtask : sendTransaction
    
    // ------------------------------------------------------------------------
    //! Send Header 0 
    /*! 
     * Send Header 0
     * \param hdr - header data
     */           
    task sendHdr0(logic [63:0] hdr);
      // Send header 0
      ib_down.ib_down_cb.DATA      <= hdr;
      ib_down.ib_down_cb.SOP_N     <= 0;
      ib_down.ib_down_cb.EOP_N     <= 1;
      ib_down.ib_down_cb.SRC_RDY_N <= 0;
      waitForAccept(); // Wait for accepting
      ib_down.ib_down_cb.SOP_N     <= 1;
    endtask : sendHdr0

    // ------------------------------------------------------------------------
    //! Send Header 1 
    /*! 
     * Send Header 1
     * \param hdr - header data
     * \param eop_n - EOP signal value     
     */
    task sendHdr1(logic [63:0] hdr, bit eop_n);
      // Send header 0
      ib_down.ib_down_cb.DATA      <= hdr;
      ib_down.ib_down_cb.SOP_N     <= 1;
      ib_down.ib_down_cb.EOP_N     <= eop_n;
      ib_down.ib_down_cb.SRC_RDY_N <= 0;
      waitForAccept(); // Wait for accepting
      ib_down.ib_down_cb.EOP_N     <= 1;
      
      if (eop_n==0) begin
        // Set not ready 
        ib_down.ib_down_cb.SOP_N     <= 1;
        ib_down.ib_down_cb.EOP_N     <= 1;
        ib_down.ib_down_cb.SRC_RDY_N <= 1;  
      end
    endtask : sendHdr1
    
    // ------------------------------------------------------------------------
    //! Send transaction data 
    /*!
     * \param tr - InternalBus transacion
     */     
    task sendData(InternalBusTransaction tr);
      logic data[];      // Data to write
      int address = tr.localAddr;
      int mod = address%8; // address modulo 8
      int k = 0;
      
      if (tr.length==0) data = new[(4096+mod)*8];
      else data = new[(tr.length+mod)*8];
      
      // Allign data from transaction to bit array
      for (integer i=0; i < mod; i++)
        for (integer j=0; j < 8; j++)
          data[8*i+j] = 0;
          
      for (integer i=mod; i < data.size+mod; i++) begin
        for (integer j=0; j < 8; j++)
          data[8*i+j] = tr.data[k][j];   
        k++;   
      end
         
      for (integer i=0; i < data.size; i=i+64) begin
        logic [63:0] write_data = 64'h0000000000000000;
        // Fill data variable
        for (integer j=0; j < 64; j++)
          if ((i+j) < data.size)
            write_data[j] = data[i+j];
        // Generate signals
        ib_down.ib_down_cb.DATA      <= write_data;
        ib_down.ib_down_cb.SOP_N     <= 1;
        ib_down.ib_down_cb.SRC_RDY_N <= 0;
        if ((i+64) >= data.size)
          ib_down.ib_down_cb.EOP_N   <= 0;
        else
          ib_down.ib_down_cb.EOP_N   <= 1; 

        waitForAccept();         // Wait for accepting
        if ((i+64) < data.size)  // If NOT EOP
          randomWait(tr);        // Random wait during transaction
      end
      
      // Set not ready 
      ib_down.ib_down_cb.SOP_N     <= 1;
      ib_down.ib_down_cb.EOP_N     <= 1;
      ib_down.ib_down_cb.SRC_RDY_N <= 1;
    endtask : sendData
    
    // ------------------------------------------------------------------------
    //! Wait for accept 
    /*!
     * Wait for accepting of 64 bits word of transaction
     */      
    task waitForAccept();
      do @(ib_down.ib_down_cb);
      while (ib_down.ib_down_cb.DST_RDY_N);
    endtask : waitForAccept

    // ------------------------------------------------------------------------
    //! Random wait 
    /*!
     * Random wait during sending transaction (Set SRC_RDY_N to 1)
     */      
    task randomWait(InternalBusTransaction transaction);
/*      repeat (transaction.getRandomWait()) begin
        ib_down.ib_down_cb.SRC_RDY_N <= 1;
        @(ib_down.ib_down_cb); // Wait for send
      end;*/   
    endtask : randomWait
    
    // -- Init Descriptor Manager ---------------------------------------------
    //! Init Descriptor Manager
    /*!
     * Initiate Descriptor Manager
     * \param ctrlNo - controller number           
     * \param pDescBaseAddr - Descriptor Manager base address           
     */
    task initDM(int ctrlNo, int pDescBaseAddr); 
      InternalBusTransaction tr = new();
      logic [63:0] dataToSend = ctrlNo*pPageSize;
      logic [31:0] initOffset = pDescBaseAddr+32'h40000;       // initialization address for descriptor manager
      
      tr.localAddr = initOffset+ctrlNo*8;
      tr.globalAddr = 64'hFFFFFFFF;
      tr.tag = 0;
      tr.length = 8;
      tr.transType = L2LW;
      tr.data = new[tr.length];
      
      for (int j=0; j<tr.length; j++)
        for (int k=0; k<8; k++)
          tr.data[j][k]=dataToSend[j*8+k];
      
      transQue.push_back(tr);  // Add transaction to queue
    
    endtask : initDM 
    
  endclass : IbDownstream
