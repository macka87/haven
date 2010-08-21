/*
 * \file ddm_ib_modul.sv
 * \brief Descriptor Download Manager IB modul
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
 * $Id: ddm_ib_modul.sv 10936 2009-09-01 07:37:53Z xspinl00 $
 *
 * TODO:
 *
 */

  import test_pkg::*;
  
  // Parsed RX Request structure
  typedef struct{
    logic [63:0] globalAddr;
    logic [BLOCK_LENGTH-1:0] descCount;
  } tRxRequest;
     
  // --------------------------------------------------------------------------
  /*!
   * \brief DDM IB modul Class
   *
   * This class is responsible for generating signals to IB interface.  
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. 
   * 
   * \param pDataWidth - InternalBus Data Width
   * \param pDmaDataWidth - DMA request Data Width
   * \param pFlows - interface number
   * \param pDmaTag - DMA Tag
   * \param pTransType - DMA Trans Type
   * \param pRingPartSize - part size
   * \param pRingParts - parts in ring for each flow
   */
  // -------------------------------------------------------------------------- 
  class DdmIbusModul #(int pDataWidth = 64, int pDmaDataWidth = 16, 
                       int pFlows = 2, int pDmaTag = 0, int pTransType = 0,
                       int pRingPartSize = 512, int pRingParts = 3
                      );
  
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string    inst;                             //! Modul identification
    bit       enabled;                          //! Modul is enabled
    mailbox #(tDmaRequest) dmaMbx;              //! Parsed DMA Request Mailbox
    mailbox #(tRxRequest) rxreqMbx;             //! Parsed RX Request Mailbox
    virtual iInternalBus.ib_write_tb #(pDataWidth) ib;
    
    DmaModul #(pDmaDataWidth, pDmaTag, pTransType) dmaModul;     //! DMA modul
    DdmRingModul #(pFlows, pRingPartSize, pRingParts) ringModul; //! DDM Ring Modul
  
    const int pDataWidthByte = pDataWidth/8;
    semaphore sem;
    
    // -------------------
    // -- Class Methods --
    // -------------------

    // ------------------------------------------------------------------------
    //! Constructor
    /*
     * Create IB modul object
     */
    function new ( string inst,
                   DmaModul #(pDmaDataWidth, pDmaTag, pTransType) dmaModul,
                   DdmRingModul #(pFlows, pRingPartSize, pRingParts) ringModul,
                   virtual iInternalBus.ib_write_tb #(pDataWidth) ib
                 );
      this.enabled     = 0;            //! Modul is disabled by default
      this.inst        = inst;         //! Store modul identifier
      this.dmaModul    = dmaModul;     //! DMA modul
      this.ringModul   = ringModul;    //! DDM Ring Modul
      this.ib          = ib;           //! Store pointer to IB interface
      this.dmaMbx      = dmaModul.dmaMbx;  //! Store pointer to mailbox
      
      this.ib.ib_write_cb.WR_DATA <= 0;
      this.ib.ib_write_cb.WR_ADDR <= 0;
      this.ib.ib_write_cb.WR_REQ  <= 0;
      this.ib.ib_write_cb.WR_BE   <= 8'hFF;

      this.rxreqMbx = new(0);
      this.sem      = new(1);
         
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Enable IB Modul
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
    //! Disable IB modul 
    /*
     * Disable generator
     */
    task setDisabled();
      enabled = 0; //! Disable modul
    endtask : setDisabled
    
    // ------------------------------------------------------------------------
    //! Descriptors Initialization
    /*
     * Descriptors initialization - first address in ring is stored to HW
     */
    task initIbDdm();
      int descHwAddr;               //! HW address of descriptors for each flow
      int descRingAddr;             //! SW address of descriptors for each flow
      int descBaseAddr  = 32'h7F000;//! Base HW address for descriptors
      
      for (int i=0; i<pFlows*2; i++)begin
        //! Descriptors space Initialization
        descHwAddr = descBaseAddr+i*8; 
        descRingAddr = pRingPartSize*i*16;
        writeDesc(descHwAddr, descRingAddr);
      end
    endtask : initIbDdm
  
    // ------------------------------------------------------------------------
    //! Write Init Descriptors
    /*
     * Descriptors initialization via InternalBus
     */
    task writeDesc(int descHwAddr, int descRingAddr);
      logic[63:0] globalAddr;
      logic[31:0] localAddr;

        sem.get(1);
      
        globalAddr = descRingAddr;
        localAddr  = descHwAddr; 
        waitForWrRdy();

        //! Send data to interface
        ib.ib_write_cb.WR_DATA <= globalAddr;
        ib.ib_write_cb.WR_BE   <= 8'hFF;
        ib.ib_write_cb.WR_ADDR <= localAddr;
        ib.ib_write_cb.WR_REQ  <= 1;
        @(ib.ib_write_cb);
        ib.ib_write_cb.WR_REQ  <= 0;
        @(ib.ib_write_cb);
        //@(ib.ib_write_cb);

        sem.put(1);

    endtask : writeDesc

    // ------------------------------------------------------------------------
    //! Run IB modul
    /*
     * Take DMA Request from mailbox and put descriptors from Ring into interface
     */
    task run();
      while (enabled) begin            //! Repeat while enabled        
        tDmaRequest parsedRequest;
     
        //! Wait until mailbox is not empty
        while (dmaMbx.num()==0) @(ib.ib_write_cb); 
        
        //! Get Request from DMA Mailbox
        dmaMbx.get(parsedRequest);
        
        //! Add Request to Rx Request Mailbox  
        addRequest(parsedRequest);   

        //! Send Transaction
        sendTransaction(parsedRequest);
      end
    endtask : run
     
    // ------------------------------------------------------------------------
    //! Add RX Request
    /*
     * Add RX Request to mailbox
     */
    task addRequest(tDmaRequest parsedRequest);
      tRxRequest rxRequest;
      int low = 0;
      int high = pRingPartSize*16;
      int globalAddr = parsedRequest.globalAddr;
      int length = parsedRequest.length;
      
      for(int i=0; i<pFlows*pRingParts; i++)begin
        if((globalAddr>=low) && (globalAddr<high))begin
           rxRequest.globalAddr = globalAddr;
           rxRequest.descCount = length/16;
//           $write("IB modul:  globalAddr:  %d\n",globalAddr);
//           $write("IB modul:  length:      %d\n",length);
           rxreqMbx.put(rxRequest);
           break;
        end   
      low  += 2*pRingPartSize*16;
      high += 2*pRingPartSize*16;
      end  
    endtask : addRequest 

    // ------------------------------------------------------------------------
    //! Send Transaction
    /*
     * Get descriptor from Ring and send it to IB interface
     *
     * \param parsedrequest - parsed DMA request
     */
    task sendTransaction(tDmaRequest parsedRequest);
      byte dataByte;                           //! Part of descriptor   
      logic[pDataWidth-1:0] data = 0;
      logic[7:0] byteEnable = 0;
      int offset = parsedRequest.localAddr % pDataWidthByte; //! Offset
      int globalAddr = parsedRequest.globalAddr;             //! Global Address
      longint localAddr  = parsedRequest.localAddr - offset; //! Local Address
      
      sem.get(1);

      //! Local Address have to be aligned 
      assert (localAddr%(pDataWidth/8)==0) 
      else $error("Local Address is not aligned!\n");

      if (offset!=0) begin
        //! Wait for WR_RDY
        waitForWrRdy();
        //! Send first word
        for (int i=offset; i<pDataWidthByte; i++)
        begin
          //! Get data from Ring
          ringModul.getFromRing(dataByte,globalAddr);

          for (int j=0; j<8; j++)
            data[i*pDataWidthByte+j] = dataByte[j];
          
          byteEnable[i] = 1;  

          globalAddr++;
        end
        //! Send data to interface
        ib.ib_write_cb.WR_DATA <= data;
        ib.ib_write_cb.WR_BE   <= byteEnable;
        ib.ib_write_cb.WR_ADDR <= localAddr;
        ib.ib_write_cb.WR_REQ  <= 1;
        @(ib.ib_write_cb);
        ib.ib_write_cb.WR_REQ  <= 0;

        localAddr += pDataWidthByte;
      end

      for (int k=0; k<parsedRequest.length/pDataWidthByte; k++)
      begin
        //! Wait for WR_RDY
        waitForWrRdy();
      
        for (int i=0; i<pDataWidthByte; i++)
        begin
          //! Get data from Ring
          ringModul.getFromRing(dataByte,globalAddr);

          for (int j=0; j<8; j++)
            data[i*pDataWidthByte+j] = dataByte[j];

          globalAddr++;
        end

        //! Send data to interface
        ib.ib_write_cb.WR_DATA <= data;
        ib.ib_write_cb.WR_BE   <= 8'hFF;
        ib.ib_write_cb.WR_ADDR <= localAddr;
        ib.ib_write_cb.WR_REQ  <= 1;
        @(ib.ib_write_cb);
        ib.ib_write_cb.WR_REQ  <= 0;

        localAddr += pDataWidthByte;
        data = 0;
      end

      offset = (offset+parsedRequest.length)%pDataWidthByte;  
      byteEnable = 0;

      if (offset != 0)
      begin
        //! Wait for WR_RDY
        waitForWrRdy();
      
        for (int i=0; i<offset; i++)
        begin
           //! Get data from Ring
          ringModul.getFromRing(dataByte,globalAddr);

          for (int j=0; j<8; j++)
            data[i*pDataWidthByte+j] = dataByte[j];

          byteEnable[i] = 1;  

          globalAddr++;
        end

        //! Send data to interface
        ib.ib_write_cb.WR_DATA <= data;
        ib.ib_write_cb.WR_BE   <= byteEnable;
        ib.ib_write_cb.WR_ADDR <= localAddr;
        ib.ib_write_cb.WR_REQ  <= 1;
        @(ib.ib_write_cb);
        ib.ib_write_cb.WR_REQ  <= 0;
      end     
      
      //! Send DMA_DONE
      dmaModul.sendDmaDone(parsedRequest.tag);
      sem.put(1);
                    
    endtask : sendTransaction
   
    // ------------------------------------------------------------------------ 
    //! Wait For WR_RDY
    /*
     * Waits for WR_RDY
     */
    task waitForWrRdy();
      while (!ib.ib_write_cb.WR_RDY) @(ib.ib_write_cb);
    endtask : waitForWrRdy

endclass : DdmIbusModul
