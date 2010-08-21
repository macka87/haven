/*
 * \file ddm_tx_driver.sv
 * \brief Descriptor Download Manager TX Driver
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
 * $Id: ddm_tx_driver.sv 10605 2009-08-21 12:18:28Z xsimko03 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  /*!
   * \brief TX DDM Driver Class
   *
   * This class sends TX descriptors to simulated ring. Unit must be enabled by "setEnable()" 
   * function call. Generation can be stoped by "setDisable()" function call. 
   *
   * \param pFlows - count of flows
   */
  class TxDdmDriver #(int pFlows = 4, int pRingPartSize = 512, int pRingParts
  = 3);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string    inst;                             //! Driver identification
    bit       enabled;                          //! Driver is enabled
    tTransMbx transMbx;                         //! Transaction mailbox
    DriverCbs cbs[$];                           //! Callbacks list
    int       txTailPointerValue[];             //! Value of TX Tail Pointer  

    DdmRingModul #(pFlows, pRingPartSize, pRingParts) ringModul;  //! DDM Ring Modul
    DdmSoftwareModul                                  sw;         //! DDM SW Modul  

    // -----
    rand bit enTxDelay; //! Enable/Disable delays between transactions
      int txDelayEn_wt      = 1;
      int txDelayDisable_wt = 3;

    // -----
    rand int txDelay;   //! Delay between transactions
      int txDelayLow        = 0;
      int txDelayHigh       = 3;
      
    //! Constrains
    constraint cDelays {
      enTxDelay dist { 1'b1 := txDelayEn_wt,
                       1'b0 := txDelayDisable_wt
                     };
           
      txDelay inside {
                       [txDelayLow:txDelayHigh]
                     };               
    }

    // -------------------
    // -- Class Methods --
    // -------------------

    // ------------------------------------------------------------------------
    //! Constructor
    /*
     * Create driver object 
     */
    function new ( string inst,
                   tTransMbx transMbx,
                   DdmRingModul #(pFlows, pRingPartSize, pRingParts) ringModul,
                   DdmSoftwareModul sw
                 );
      this.enabled     = 0;            //! Driver is disabled by default
      this.transMbx    = transMbx;     //! Store pointer to mailbox
      this.inst        = inst;         //! Store driver identifier
      this.ringModul   = ringModul;    //! DDM Ring Modul
      this.sw          = sw;           //! Software Modul
    
      txTailPointerValue = new [pFlows];
      
      for(int i=0; i<pFlows; i++)
        txTailPointerValue[i]=0;
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Set Callbacks 
    /*
     * Put callback object into List
     */ 
    function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // ------------------------------------------------------------------------
    //! Enable Driver
    /*
     * Enable driver and runs driver process
     */
    task setEnabled();
      enabled = 1; //! Driver Enabling
      fork         
        run();     //! Creating driver subprocess
      join_none;   //! Don't wait for ending
    endtask : setEnabled
        
    // ------------------------------------------------------------------------
    //! Disable Driver
    /*
     * Disable generator
     */
    task setDisabled();
      enabled = 0; //! Disable driver, after sending last transaction it ends
    endtask : setDisabled

    // ---------------------------
    // -- Private Class Methods --
    // ---------------------------
  
    // ------------------------------------------------------------------------
    //! Run Driver
    /*
     * Take transactions from mailbox and generate them to interface
     */
    task run();
     DdmTransaction transaction;       //! Descriptor Download Manager transaction
     Transaction to; 
     int count;                        //! Count of needed descriptors 
     int flow;                         //! Interface number
      
     while (enabled) begin             //! Repeat while enabled
        //! descriptor number generation
        // count = $urandom_range(1,20);  //! Count of needed descriptors
        count = 1;
        flow = $urandom_range(0,pFlows-1);

        // $write("DRIVER:  count:  %d, flow:  %d\n",count,flow);
 
        for(int i=0; i<count; i++)begin   
          assert(randomize());         //! Randomize rand variables
          transMbx.get(to);            //! Get transaction from mailbox 
          $cast(transaction,to);
          transaction.block_addr = flow;  //! Interface number
              
          //! descriptors are sended to scoreboard and to TX ring 
          sendTransaction(transaction);                 
          //transaction.display(inst);
        end 
        setTailPointer(count, flow); 
      end
    endtask : run
    
    // ------------------------------------------------------------------------
    //! Send Transaction 
    /*
     * Send descriptors to tx scoreboard
     *
     * \param transaction - DDM transaction
     */
    task sendTransaction(DdmTransaction transaction);
      Transaction tr;
      $cast(tr, transaction);
      
      //! Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);       
    
      //! Wait before sending transaction
      if (enTxDelay) repeat (txDelay) @(sw.mi32.mi32_cb);           
      
      //! Store descriptor to TX ring
      ringModul.storeToRing(transaction,1); 
     
      //! Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);
    endtask : sendTransaction

    // ------------------------------------------------------------------------
    //! Set Tail Pointer
    /*
     * Set tail pointer via MI32
     */
    task setTailPointer(int count, int flow);
      int tailHwAddr;                   //! Tail Pointer Address
      int tailRegAddr = 32'h0C;         //! Tail Register Address
      int partFlows = 32'h40;           //! This constant makes from Register Address
                                        //  Reqister Addresses for flows
      
      tailHwAddr = tailRegAddr + partFlows*(flow*2+1); //! TX Tail Pointer HW Address
      txTailPointerValue[flow] += count;      //! TX Tail Pointer value
    
      //! TX Tail Pointer is set via MI32
      sw.swQueue.push_back(tailHwAddr);
      sw.swQueue.push_back(txTailPointerValue[flow]);
    endtask : setTailPointer 

  endclass : TxDdmDriver
