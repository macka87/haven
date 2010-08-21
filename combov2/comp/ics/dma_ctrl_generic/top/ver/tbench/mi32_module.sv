/*!
 * \file mi32_module.sv
 * \brief MI32 Module for DMA Module Generic 
 * \author Marek Santa <santa@liberouter.org> 
 * \date 2010
 */  
 /*   
 * Copyright (C) 2010 CESNET
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
 
  import sv_mi32_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- MI32 Module Class
  // --------------------------------------------------------------------------
  
  /*!
   * \brief MI32 Module Class
   *    
   * This class is responsible for sending and receiving transaction via MI32 
   * interface. Unit must be enabled by "setEnable()" function call. 
   * Running can be stoped by "setDisable()" function call.
   */
  class Mi32Module #(int pRxIfcCount = 4, int pTxIfcCount = 4, 
                     int pPageSize = 4096, int pPageCount = 2);
    
    // -- Private Class Atributes --
    
    //! Module identification
    string       inst;                         
    //! Module is enabled
    bit          enabled;  
    //! MI32 Driver
    Mi32Driver   miDriver;
    //! MI32 Monitor
    Mi32Monitor  miMonitor;
    //! MI32 interface
    virtual iMi32.tb mi;
    //! Transaction queue
    Mi32Transaction transQue[$];
    //! Response queue
    Mi32Transaction responseQue[$];

    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates module object and MI32 driver and monitor object.
     */
    function new (string inst,
                  virtual iMi32.tb mi
                 );
      miDriver  = new("MI32 Driver", null, mi);
      miMonitor = new("MI32 Monitor", mi);

      this.enabled = 0;
      this.inst    = inst;
      this.mi      = mi;

    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Enable Module
    /*!
     * Enable Module and runs Module process
     */     
    task setEnabled();
      enabled = 1; // Module Enabling
      fork         
         run();                // Creating module subprocess
      join_none;               // Don't wait for ending
    endtask : setEnabled
        
    // ------------------------------------------------------------------------
    //! Disable Module
    task setDisabled();
      enabled = 0; // Disable Module
    endtask : setDisabled

    // ------------------------------------------------------------------------
    //! DUT (DMA Module Gen) Initialization 
    /*!
     * 1. Buffer Size Mask register initialization     
     * 2. Control register initialization     
     */     
    task initControllers();
      
      @(miDriver.mi.cb);
      
      // Buffer Size Mask Register initialization
      for (int i=0; i<pRxIfcCount; i++) begin
        initBsmRegisterRx(i);
        miDriver.executeTransaction(transQue.pop_front());
      end
      for (int i=0; i<pTxIfcCount; i++) begin
        initBsmRegisterTx(i);
        miDriver.executeTransaction(transQue.pop_front());
      end
      
      // Control register initialization
      for (int i=0; i<pRxIfcCount; i++) begin
        setRxController(i, 1);
        miDriver.executeTransaction(transQue.pop_front());
      end
      for (int i=0; i<pTxIfcCount; i++) begin
        setTxController(i, 1);
        miDriver.executeTransaction(transQue.pop_front());
      end

    endtask : initControllers

    // -- Read Frame Counters -------------------------------------------------
    //! Read Frame Counters
    /*!
     * Function reads values in frame counter registers via MI32.          
     */
    task readFrameCounters(inout bit[63:0] droppedFrames[], 
                           inout bit[63:0] droppedLength[]);
      Mi32Transaction mi32Transaction = new();

      mi32Transaction.rw      = 0;
      mi32Transaction.be      = '1;

      for (int i=0; i<pRxIfcCount; i++) begin
        // Read Dropped Frames Counter
         // Low part
        mi32Transaction.address = 32'h2000+8*i;
        miMonitor.executeTransaction(mi32Transaction);
        droppedFrames[i][31:0]  = mi32Transaction.data;

         // High part
        mi32Transaction.address = 32'h2004+8*i;
        miMonitor.executeTransaction(mi32Transaction);
        droppedFrames[i][63:32] = mi32Transaction.data;

        // Read Length of Dropped Frames Counter
         // Low part
        mi32Transaction.address = 32'h2400+8*i;
        miMonitor.executeTransaction(mi32Transaction);
        droppedLength[i][31:0]  = mi32Transaction.data;

         // High part
        mi32Transaction.address = 32'h2404+8*i;
        miMonitor.executeTransaction(mi32Transaction);
        droppedLength[i][63:32] = mi32Transaction.data;

        // Display counters values
        $write("------------------------------------------------------------\n");
        $write("-- Channel %0d Frame Counters\n", i);
        $write("------------------------------------------------------------\n");
        $write("Dropped Frames Counter:\t\t %10d\n",droppedFrames[i]);
        $write("Length of Dropped Frames Counter:\t %10d\n",droppedLength[i]);
        $write("------------------------------------------------------------\n");
      end

    endtask : readFrameCounters

    // ------------------------------------------------------------------------
    //! Send RX End Pointer 
    /*!
     * \param flow - interface number      
     */      
    task setRxEndPtr(logic [31:0] data, int flow);
      logic [31:0] endPointerBaseAddr = 32'h0000000C;
      logic [31:0] endPointerAddr = endPointerBaseAddr+(flow*2)*(8'h40);
      
      setPtr(data, endPointerAddr);
    endtask : setRxEndPtr
    
    // ------------------------------------------------------------------------
    //! Send TX End Pointer 
    /*!
     * \param flow - interface number      
     */      
    task setTxEndPtr(logic [31:0] data, int flow);
      logic [31:0] endPointerBaseAddr = 32'h0000000C;
      logic [31:0] endPointerAddr = endPointerBaseAddr+(flow*2+1)*(8'h40);
      
      setPtr(data, endPointerAddr);
    endtask : setTxEndPtr
    
    // ------------------------------------------------------------------------
    //! Send RX Start Pointer 
    /*!
     * \param flow - interface number      
     */      
    task setRxStartPtr(logic [31:0] data, int flow);
      logic [31:0] startPointerBaseAddr = 32'h00000008;     
      logic [31:0] startPointerAddr = startPointerBaseAddr+(flow*2)*(8'h40);
      
      setPtr(data, startPointerAddr);
    endtask : setRxStartPtr
    
    // ------------------------------------------------------------------------
    //! Send TX Start Pointer 
    /*!
     * \param flow - interface number      
     */      
    task setTxStartPtr(logic [31:0] data, int flow);
      logic [31:0] startPointerBaseAddr = 32'h00000008;     
      logic [31:0] startPointerAddr = startPointerBaseAddr+(flow*2+1)*(8'h40);
      
      setPtr(data, startPointerAddr);
    endtask : setTxStartPtr

    // ------------------------------------------------------------------------
    //! Set pointer 
    /*!
     * \param data - value to set.
     * \param addr - address of register on MI32.
     */      
    task setPtr(logic [31:0] data, logic [31:0] addr);
      Mi32Transaction tr = new();
      
      tr.address = addr;
      tr.data    = data;
      tr.be      = '1;
      tr.rw      = 1;
            
      transQue.push_back(tr);  // Add transaction to queue
    endtask : setPtr
    
    // ------------------------------------------------------------------------
    //! Receive RX End Pointer 
    /*!
     * \param flow - interface number      
     */      
    task getRxEndPtr(output logic [31:0] data, input int flow);
      logic [31:0] endPointerBaseAddr = 32'h0000000C;
      logic [31:0] endPointerAddr = endPointerBaseAddr+(flow*2)*(8'h40);
      Mi32Transaction tr;
      
      tr = new();
      tr.address = endPointerAddr;
      tr.be      = '1;
      tr.rw      = 0;  
      
      transQue.push_back(tr);  // Add transaction to queue
      
      while (responseQue.size()==0 || responseQue[0].address != endPointerAddr)
        @(mi.cb); 

      tr = responseQue.pop_front();
      data = tr.data;
    endtask : getRxEndPtr
    
    // ------------------------------------------------------------------------
    //! Receive TX Start Pointer 
    /*!
     * \param flow - interface number      
     */      
    task getTxStartPtr(output logic [31:0] data, input int flow);
      logic [31:0] startPointerBaseAddr = 32'h00000008;     
      logic [31:0] startPointerAddr = startPointerBaseAddr+(flow*2+1)*(8'h40);
      Mi32Transaction tr;
      
      tr = new();
      tr.address = startPointerAddr;
      tr.be      = '1;
      tr.rw      = 0;  
      
      transQue.push_back(tr);  // Add transaction to queue
      
      while (responseQue.size()==0 || responseQue[0].address!=startPointerAddr)
        @(mi.cb); 

      tr = responseQue.pop_front();
      data = tr.data;
    endtask : getTxStartPtr
    
    // -- Set Controller ------------------------------------------------------
    //! Set controller
    /*!
     * Run, pause or stop single controller
     * \param ctrlNo - controller number   
     * \param cmd - command (1 = run, 2 = pause, 4 = stop)        
     */
    task setRxController(int ctrlNo, int cmd); 
      Mi32Transaction tr = new();
      logic [31:0] dataToSend = cmd;
      logic [31:0] ctrlRegAddr = 32'h00;  // Controll register address
      
      tr.address = ctrlRegAddr+ctrlNo*(8'h80);
      tr.data    = dataToSend;
      tr.be      = '1;
      tr.rw      = 1;

      $write("ifc:%0d addr:%0x cmd:%0x time:%0t\n",ctrlNo,tr.address,tr.data,$time);
      transQue.push_back(tr);
    endtask : setRxController 
    
    task setTxController(int ctrlNo, int cmd); 
      Mi32Transaction tr = new();
      logic [31:0] dataToSend = cmd;
      logic [31:0] ctrlRegAddr = 32'h40;  // Controll register address
      
      tr.address = ctrlRegAddr+ctrlNo*(8'h80);
      tr.data    = dataToSend;
      tr.be      = '1;
      tr.rw      = 1;
      
      $write("ifc:%0d addr:%0x cmd:%0x time:%0t\n",ctrlNo,tr.address,tr.data,$time);
      transQue.push_back(tr);
    endtask : setTxController 
    
    // -- Init BSM Register ---------------------------------------------------
    //! Init Buffer Size Mask Register
    /*!
     * Initiate Buffer Size Mask Register
     * \param ctrlNo - controller number           
     */
    task initBsmRegisterRx(int ctrlNo); 
      Mi32Transaction tr = new();
      logic [31:0] dataToSend = pPageSize*pPageCount-1;
      logic [31:0] initBSMaddr = 32'h10;  // Buffer Size Mask register
      
      tr.address = initBSMaddr+ctrlNo*(8'h80);
      tr.data    = dataToSend;
      tr.be      = '1;
      tr.rw      = 1;
      
      transQue.push_back(tr);
    endtask : initBsmRegisterRx 

    task initBsmRegisterTx(int ctrlNo); 
      Mi32Transaction tr = new();
      logic [31:0] dataToSend = pPageSize*pPageCount-1;
      logic [31:0] initBSMaddr = 32'h50;  // Buffer Size Mask register
      
      tr.address = initBSMaddr+ctrlNo*(8'h80);
      tr.data    = dataToSend;
      tr.be      = '1;
      tr.rw      = 1;
      
      transQue.push_back(tr);
    endtask : initBsmRegisterTx 

    // ------------------------------------------------------------------------
    //! Run Module 
    /*
     * Get transactions from RAM and send it to scoreboard
     */
    task run();
      Mi32Transaction transaction;

      while (enabled) begin                   // Repeat while enabled        
        // Wait while queue is empty
        while (transQue.size()==0) @(mi.cb);

        // Send transaction
        transaction = transQue.pop_front();
        if (transaction.rw == 1) miDriver.executeTransaction(transaction);
        else begin
          miMonitor.executeTransaction(transaction);
          responseQue.push_back(transaction);
        end 
//        transaction.display();
      end
    endtask : run
    
    // -- Pause RX Controller -------------------------------------------------
    //! Pause RX controller
    /*!
     * Pause single RX controller
     * \param ifcNo - RX interface number     
     */
    task pauseRxController(int ifcNo);
      setRxController(ifcNo, 2);
    endtask : pauseRxController   
    
    // -- Unpause RX Controller -----------------------------------------------
    //! Unpause RX controller
    /*!
     * Unpause single RX controller
     * \param ifcNo - RX interface number     
     */
    task unpauseRxController(int ifcNo);
      setRxController(ifcNo, 1);
    endtask : unpauseRxController   
    
    // -- Pause TX Controller -------------------------------------------------
    //! Pause TX controller
    /*!
     * Pause single TX controller
     * \param ifcNo - TX interface number     
     */
    task pauseTxController(int ifcNo);
      setTxController(ifcNo, 2);
    endtask : pauseTxController   
    
    // -- Unpause TX Controller -----------------------------------------------
    //! Unpause TX controller
    /*!
     * Unpause single TX controller
     * \param ifcNo - TX interface number     
     */
    task unpauseTxController(int ifcNo);
      setTxController(ifcNo, 1);
    endtask : unpauseTxController   
    
    // -- Stop RX Controller --------------------------------------------------
    //! Stop RX controller
    /*!
     * Stop single RX controller
     * \param ifcNo - RX interface number     
     */
    task stopRxController(int ifcNo);
      setRxController(ifcNo, 4);
    endtask : stopRxController   
    
    // -- Unstop RX Controller ------------------------------------------------
    //! Unstop RX controller
    /*!
     * Unstop single RX controller
     * \param ifcNo - RX interface number     
     */
    task unstopRxController(int ifcNo);
      initBsmRegisterRx(ifcNo);
      setRxController(ifcNo, 1);
    endtask : unstopRxController   
    
    // -- Stop TX Controller --------------------------------------------------
    //! Stop TX controller
    /*!
     * Stop single TX controller
     * \param ifcNo - TX interface number     
     */
    task stopTxController(int ifcNo);
      setTxController(ifcNo, 4);
    endtask : stopTxController   
    
    // -- Unstop TX Controller ------------------------------------------------
    //! Unstop TX controller
    /*!
     * Unstop single TX controller
     * \param ifcNo - TX interface number     
     */
    task unstopTxController(int ifcNo);
      initBsmRegisterTx(ifcNo);
      setTxController(ifcNo, 1);
    endtask : unstopTxController   
    
  endclass : Mi32Module
