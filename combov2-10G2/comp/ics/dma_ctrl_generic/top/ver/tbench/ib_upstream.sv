/*
 * \file ib_upstream.sv
 * \brief InternalBus Upstream Modul
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
 * $$
 *
 * TODO:
 *
 */
 
  import sv_dma_module_gen_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- InternalBus Upstream Modul
  // --------------------------------------------------------------------------
 
  /*!
   * \brief InternalBus Upstream Modul
   * 
   * This class is responsible for receiving transaction objects from 
   * InternalBus.up interface signals. L2GW header is deleted from transaction 
   * and data are stored into RAM. If it is G2LR header, information is sent to 
   * IB_DOWNSTREAM component. 
   * 
   * \param pDataWidth - data width
   * \param pFLows - count of flows
   * \param pPageSize - size of one page
   * \param pPageCount - count of size in one flow                
   */
   class IbUpstream #(int pDataWidth = 64, int pFlows = 4, 
                      int pPageSize = 4096, int pPageCount = 2);
    
    // -- Private Class Atributes --
    
    //! Modul is enabled
    bit       enabled;                          
    //! DMA Modul software with RAM    
    DmaModuleSW #(pDataWidth,pFlows,pPageSize,pPageCount)  dmaModul; 
    //! InternalBus Downstream Modul
    IbDownstream #(pDataWidth,pFlows,pPageSize,pPageCount) ibDown;  
    //! Virtual interface InternalBus.up    
    virtual iInternalBusUp.ib_up_tb #(pDataWidth) ib_up;  
    
    // -- Public Class Methods --

    // -----------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates modul object and sets default values of InternalBus interface signals 
     */
    function new ( virtual iInternalBusUp.ib_up_tb #(pDataWidth) ib_up,
                   DmaModuleSW #(pDataWidth,pFlows,pPageSize,
                                                          pPageCount) dmaModul,
                   IbDownstream #(pDataWidth,pFlows,pPageSize,
                                                          pPageCount) ibDown                                            
                   );
      this.enabled     = 0;             // Modul is disabled by default
      this.dmaModul    = dmaModul;      // DMA modul
      this.ibDown      = ibDown;        // InternalBus Downstream Modul 
      this.ib_up       = ib_up;  
     
      this.ib_up.ib_up_cb.DST_RDY_N  <= 0;   // Ready even if disabled
    endfunction: new          
    
    // -----------------------------------------------------------------------
    //! Enable Modul 
    /*!
     * Enable Modul and runs Modul process
     */
    task setEnabled();
      enabled = 1; // Modul Enabling
      fork         
        run();     // Creating monitor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -----------------------------------------------------------------------
    //! Disable Modul 
    task setDisabled();
      enabled = 0; // Disable Modul
    endtask : setDisabled

    // -----------------------------------------------------------------------
    // Run InternalBus Upstream Modul
    /*!
     * Starts InternalBus Upstream processing
     */ 
    task run();
      InternalBusTransaction transaction;
      int offset; // Data offset
    
      while (enabled) begin              // Repeat while enabled        
        transaction = new;               // Create new transaction object
        // discernment of transaction type according to header, receiving of InternalBus transaction
        receiveTransaction(transaction, offset); 
        //transaction type is read completition
        if (transaction.transType == RDC) begin
          receiveData(transaction, offset); // receiving of data
        end
        //transaction type is Local to global write
        else if (transaction.transType == L2GW) begin
          receiveData(transaction, offset); // receiving of data
          dmaModul.storeData(transaction);  // data are stored into RAM
        end  
        //transaction type is global to local read 
        else begin
          transaction.transType = RDC;               // Answer to G2LR is RDC
          ibDown.callIbDownstream(transaction);      // G2LR header = calling downstream process
        end    
      end
    endtask : run
    
    // -----------------------------------------------------------------------
    //! Receive Transaction 
    /*!
     * It receives Internal Bus transaction to tr object
     * \param tr - InternalBus Transaction
     * \param offset - data offset          
     */      
    task receiveTransaction(InternalBusTransaction tr, int offset);
      bit enNotReady = $urandom_range(8);
      
      while (ib_up.ib_up_cb.SOP_N || ib_up.ib_up_cb.SRC_RDY_N) 
        @(ib_up.ib_up_cb);
      
      tr.length    = ib_up.ib_up_cb.DATA[15: 4]; // Get length
      tr.tag       = ib_up.ib_up_cb.DATA[31:16]; // Get tag

      // Get Transaction type
      case (ib_up.ib_up_cb.DATA[3:0])
         L2GW_TYPE:
            tr.transType = L2GW;
         G2LR_TYPE:
            tr.transType = G2LR;
         RDC_TYPE:
            tr.transType = RDC;
      endcase;
      
      // Store address from first header
      tr.globalAddr[31: 0] = ib_up.ib_up_cb.DATA[63:32]; 
      tr.globalAddr[63:32] = 0;

      offset = ib_up.ib_up_cb.DATA[34:32]; // Store data offset
      
      // Wait for second header
      do @(ib_up.ib_up_cb); 
      while (ib_up.ib_up_cb.SRC_RDY_N);

      // Store address from second header
      tr.globalAddr[63:32] = ib_up.ib_up_cb.DATA[63:32];  
      tr.localAddr = ib_up.ib_up_cb.DATA[31:0];
    endtask : receiveTransaction

    // -----------------------------------------------------------------------
    //! Receive Data 
    /*!
     * This function receives transaction data
     * \param tr - InternalBus Transaction 
     * \param offset - data offset          
     */      
    task receiveData(InternalBusTransaction tr, int offset);
      int word64;
      int low_tr  = 0;
      int low_ib  = 0;
      int high_tr = 7;
      int high_ib = 7;
      int tr_length = tr.length;
      
      if (tr_length == 0) tr_length = pPageSize;
      
      word64  = (tr_length + offset + 7)/8;
      tr.data = new[tr_length];

      for (int i=1; i <= word64; i++) begin
        do @(ib_up.ib_up_cb); 
        while (ib_up.ib_up_cb.SRC_RDY_N);
        // first word
        if (i == 1) 
          low_ib = offset;              
        else
          low_ib = 0;
          
        // last word
        if (i == word64) begin        
          high_tr -= (8 - ((tr_length) % 8));
          high_ib  = ( ((tr_length + offset) - 1) % 8);
          if (ib_up.ib_up_cb.EOP_N == 1) begin
            $write("Error: Received transaction with wrong length");
            $stop;
          end;
        end
               
        // One 64-bit copying
        for (low_ib = low_ib; low_ib <= high_ib ; low_ib++) begin 
          logic [7:0] wbyte = 0;
          for (int j=0; j<8; j++)
            wbyte[j] = ib_up.ib_up_cb.DATA[low_ib*8 + j]; 
          tr.data[low_tr++] = wbyte; //data
        end          
  
        high_tr += 8;     
      end
    endtask : receiveData
        
  endclass : IbUpstream
