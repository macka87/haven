/*
 * \file ddm_rx_monitor.sv
 * \brief Descriptor Download Manager RX Monitor
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
 * $Id: ddm_rx_monitor.sv 10558 2009-08-20 12:57:04Z xsimko03 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  /*!
   * \brief RX DDM Monitor Class
   *
   * This class is responsible for receiving transactions objects from
   * RX Nfifo interface signals. After is tranaction received it is sended 
   * by callback to processing units (typicaly scoreboard). Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call. 
   *
   * \param pFlows - count of flows
   * \param pBlockSize - max number of descriptors in one transfer
   */
  class RxDdmMonitor #(int pFlows = 4, int  pBlockSize = 4);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string     inst;                             //! Driver identification

    bit        enabled;                          //! Driver is enabled
    MonitorCbs cbs[$];                           //! Callbacks list
    virtual iDdm.rxnfifo_tb #(pFlows, pBlockSize) rxfifo;      

    // -------------------
    // -- Class Methods --
    // -------------------

    // ------------------------------------------------------------------------
    //! Constructor
    /*
     * Create monitor object 
     */
    function new (string inst,
                  virtual iDdm.rxnfifo_tb #(pFlows, pBlockSize) rxfifo
                 );
      this.enabled     = 0;            //! Driver is disabled by default
      this.inst        = inst;         //! Store driver identifier
      this.rxfifo      = rxfifo;       //! RX Nfifo interface

      this.rxfifo.rxnfifo_cb.RX_NFIFO_RADDR <= 0;
      this.rxfifo.rxnfifo_cb.RX_NFIFO_RD    <= 0;
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Set Callbacks 
    /*
     * Put callback object into List
     */ 
    function void setCallbacks(MonitorCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // ------------------------------------------------------------------------
    //! Enable Monitor
    /*
     * Enable monitor and runs monitor process
     */
    task setEnabled();
      enabled = 1; //! Monitor Enabling
      fork         
        run();     //! Creating monitor subprocess
      join_none;   //! Don't wait for ending
    endtask : setEnabled
        
    // ------------------------------------------------------------------------
    //! Disable Monitor
    /*
     * Disable monitor
     */
    task setDisabled();
      enabled = 0; //! Disable monitor, after sending last transaction it ends
    endtask : setDisabled

    // ---------------------------
    // -- Private Class Methods --
    // ---------------------------

    // ------------------------------------------------------------------------
    //! Run Monitor
    /*
     * Receive transactions and send them for processing by callback
     */
    task run();
      DdmTransaction transaction;
      Transaction tr;
      int flow = 0;
      string label;
      
      while(enabled) begin     //! Repeat in forever loop
        transaction = new();   //! Create new transaction object
     
        //! Call transaction preprocessing, if is available
        foreach (cbs[i]) cbs[i].pre_rx(tr,label);

        //! Wait for not Empty for some flow
        waitForNotEmpty(flow);
        
        //! Receive descriptor from interface
        receiveTransaction(transaction, flow);
             
        $swrite(label, "Monitor %0d", inst);

        if(enabled) begin
          $cast(tr,transaction);
          //tr.display(label);
          #(0);

          //! Call transaction postprocessing, if is available
          foreach (cbs[i]) cbs[i].post_rx(tr,label);
        end  
      end
    endtask : run 
    
    // -------------------------------------------------------------------------
    //! Receive trasaction
    /*
     * It receives Ddm Transaction to tr object
     *
     * \param tr - DDM transaction
     * \flow - interface number
     */ 
    task receiveTransaction(inout DdmTransaction tr, input int flow);
      rxfifo.rxnfifo_cb.RX_NFIFO_RADDR <= flow;
     
      rxfifo.rxnfifo_cb.RX_NFIFO_RD <= 1;
      @(rxfifo.rxnfifo_cb);
      rxfifo.rxnfifo_cb.RX_NFIFO_RD <= 0;
      @(rxfifo.rxnfifo_cb);

      //! First part of descriptor
      waitForDoutVld();
      tr.data[63:0] = rxfifo.rxnfifo_cb.RX_NFIFO_DOUT;
      @(rxfifo.rxnfifo_cb);

      rxfifo.rxnfifo_cb.RX_NFIFO_RD <= 1;
      @(rxfifo.rxnfifo_cb);
      rxfifo.rxnfifo_cb.RX_NFIFO_RD <= 0;
      @(rxfifo.rxnfifo_cb);

      //! Second part of descriptor
      waitForDoutVld();
      tr.data[127:64] = rxfifo.rxnfifo_cb.RX_NFIFO_DOUT;

      tr.block_addr = flow;
      tr.direction  = 1;  //! RX direction      
    endtask : receiveTransaction   

    // --------------------------------------------------------------------------
    //! Wait For Not Empty
    /*
     * Wait while ddm is ready to send descriptors
     */
    task waitForNotEmpty(inout int flow);
      while(1) begin
        if (rxfifo.rxnfifo_cb.RX_NFIFO_EMPTY[flow]==0) begin
          // $write("detekujem empty pre flow %d\n",flow);
          break;
        end
          
        flow++;

        if(flow==pFlows) begin
          flow=0;
          @(rxfifo.rxnfifo_cb);
        end  
      end
    endtask : waitForNotEmpty

    // --------------------------------------------------------------------------
    //! Wait For Data Valid
    /*
     * Wait until data will be valid
     */
    task waitForDoutVld();
      while (!rxfifo.rxnfifo_cb.RX_NFIFO_DOUT_VLD)
        @(rxfifo.rxnfifo_cb);
    endtask : waitForDoutVld
 endclass : RxDdmMonitor    

