/*
 * \file ddm_rxreq_modul.sv
 * \brief Descriptor Download Manager RX Request modul
 * \date Copyright (C) 2009 CESNET
 * \author Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: ddm_rxreq_modul.sv 10986 2009-09-03 15:41:23Z xsimko03 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  /*!
   * \brief DDM RX Request modul Class
   *
   * This class processes signals from RXREQ interface.  
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. 
   * 
   * \param pBlockSize - block size
   * \param pDataWidth - InternalBus Data Width
   * \param pDmaDataWidth - DMA request Data Width
   * \param pFlows - interface number
   * \param pDmaTag - DMA Tag
   * \param pTransType - DMA Trans Type
   * \param pRingPartSize - part size
   * \param pRingParts - parts in ring for each flow
   */
  // -------------------------------------------------------------------------- 
  class DdmRxReqModul #(int pFlows = 4, int pBlockSize = 4, int pDataWidth = 64,
                        int pDmaDataWidth = 16, int pDmaTag = 0, int pTransType = 0,
                        int pRingPartSize = 512, int pRingParts = 3, int pBlockLength = 68
                       );
  
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string    inst;                             //! Modul identification
    bit       enabled;                          //! Modul is enabled
    mailbox #(tRxRequest) rxreqMbx;             //! Parsed RX Request Mailbox
    virtual iDdm.rxreq_tb #(pFlows, pBlockSize) rxreq;

    DdmIbusModul #(pDataWidth, pDmaDataWidth, pFlows, pDmaTag, pTransType,
                   pRingPartSize, pRingParts) ib;
  
    // -------------------
    // -- Class Methods --
    // -------------------

    // ------------------------------------------------------------------------
    //! Constructor
    /*
     * Create IB modul object
     */
    function new ( string inst,
                   DdmIbusModul #(pDataWidth, pDmaDataWidth, pFlows, pDmaTag, pTransType,
                   pRingPartSize, pRingParts) ib,
                   virtual iDdm.rxreq_tb #(pFlows, pBlockSize) rxreq
                 );
      this.enabled     = 0;                //! Modul is disabled by default
      this.inst        = inst;             //! Store modul identifier
      this.ib          = ib;               //! IB Modul
      this.rxreq       = rxreq;            //! Store pointer to RXREQ interface
      this.rxreqMbx    = ib.rxreqMbx;      //! Store pointer to mailbox
      
      this.rxreq.rxreq_cb.RX_RF_FULL <= 0;
          
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Enable RXREQ Modul
    /*
     * Enable modul and runs modul process
     */
    task setEnabled();
      enabled = 1; //! Modul Enabling
      fork         
        run();     //! Creating modul subprocess
      join_none;   //! Don't wait for ending
    endtask : setEnabled
        
    // ------------------------------------------------------------------------    
    //! Disable RXREQ modul 
    /*
     * Disable generator
     */
    task setDisabled();
      enabled = 0; //! Disable modul
    endtask : setDisabled
    
    // ------------------------------------------------------------------------
    //! Run RXREQ modul
    /*
     * Take RX Request from mailbox and compare with signal values
     */
    task run();
      while (enabled) begin            //! Repeat while enabled        
        tRxRequest parsedRequest;

        //! Wait until mailbox is not empty
        while (rxreqMbx.num()==0) @(rxreq.rxreq_cb); 
        
        //! Get Request from Mailbox
        rxreqMbx.get(parsedRequest);
        
        //! Compare
        compareTransaction(parsedRequest);
      end
    endtask : run
    
    // ------------------------------------------------------------------------
    //! Compare Transaction
    /*
     * Compare parsed RX Request from mailbox with interface values
     *
     * \param parsedrequest - parsed RX request
     */
    task compareTransaction(tRxRequest parsedRequest);
      logic[pBlockLength+64-1:0] data;
      int global;
      int length;
      int desc0counter = 0;     //! Valid desc0 in one DMA transaction
     
      //! Data from RX_RF_DATA 
      waitForDataVld();
      data = rxreq.rxreq_cb.RX_RF_DATA;
      global = data[63:0];
      length = data[pBlockLength+64-1:64]; 

      //! Detection of desc type1 at global address (begin of DMA transaction)
      if ((parsedRequest.globalAddr + 16) % (pRingPartSize*16) == 0) begin
        rxreqMbx.get(parsedRequest);    //! Read new item from mailbox
      end
     
      //! Real used type0 descriptors 
      for(int i = 0; i < parsedRequest.descCount; i++) begin
          if ((parsedRequest.globalAddr + 16*(i+1)) % (pRingPartSize*16) == 0) begin
             parsedRequest.descCount  = desc0counter;
             break;
          end
          desc0counter++;
      end

      //! Check Global Address
      assert (global==parsedRequest.globalAddr)
      else $error("Incorrect global address (RX req): %0d, expected (DMA) %0d",global, parsedRequest.globalAddr);
      
      //! Check Count of Descriptors
      assert ((length)==parsedRequest.descCount) 
      else $error("Incorrect descCount: %0d  length: %d",parsedRequest.descCount,length);     
    endtask : compareTransaction
    
    // --------------------------------------------------------------------------
    //! Wait For Data Valid
    /*
     * Wait until data will be valid
     */
    task waitForDataVld();
      while (!rxreq.rxreq_cb.RX_RF_DATA_VLD)
        @(rxreq.rxreq_cb);
    endtask : waitForDataVld
        
endclass : DdmRxReqModul
