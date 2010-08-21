/*
 * ext_monitor.sv: Extraction data Monitor
 * Copyright (C) 2009 CESNET
 * Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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
 * $Id: ext_monitor.sv 11120 2009-09-10 15:57:59Z xstour03 $
 *
 * TODO:
 *
 */
 
 
  // --------------------------------------------------------------------------
  // -- Extraction data Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from 
   * Frame Link interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class ExtMonitor #(int pEXT_SIZE = 4, pDataWidth = 32, pDremWidth = 2);
    
    // -- Private Class Atributes --
    string  inst;                          // Monitor identification
    bit     enabled;                       // Monitor is enabled
    bit     busy;                          // Monitor is receiving transaction
    MonitorCbs cbs[$];                     // Callbacks list
    virtual iExt_data.monitor #(pEXT_SIZE) ext_ifc;
    virtual iFrameLinkTx.monitor #(pDataWidth,pDremWidth) fl;

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iExt_data.monitor #(pEXT_SIZE) ext_ifc,
                   virtual iFrameLinkTx.monitor #(pDataWidth,pDremWidth) fl
                   );
      this.enabled     = 0;           // Monitor is disabled by default   
      this.busy        = 0;           // Monitor is not busy by default   
      this.ext_ifc     = ext_ifc;     // Store pointer interface
      this.fl          = fl;          // Store pointer interface
      this.inst        = inst;        // Store driver identifier
      
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
    
    // -- Run Monitor ---------------------------------------------------------
    // Receive transactions and send them for processing by call back
    task run();
      ExtDataTransaction transaction; 
      Transaction tr;

      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        $cast(tr, transaction);

        // Call transaction preprocesing, if is available
        foreach (cbs[i]) cbs[i].pre_rx(tr, inst);       

        // Receive Transaction
        receiveTransaction(transaction); // Receive Transaction
//        transaction.display(inst);
        
        // Necessary for not calling callback after monitor disabling
        if (!enabled) break;

        #(0); // Necessary for not calling callback before driver
        
        // Call transaction postprocesing, if is available
        foreach (cbs[i]) cbs[i].post_rx(tr, inst);

        // Monitor received transaction and is not busy
        busy = 0;
      end
    endtask : run
    

    // -- Wait for transaction ------------------------------------------------
    // It waits until EXTRACTED_DONE or EXTRACTED_ERR and both SRC_RDY_N and DST_RDY_N are set
    task waitForTrans();
      do begin
        // Wait if not data ready
        if (!ext_ifc.monitor_cb.EXTRACTED_DONE && !ext_ifc.monitor_cb.EXTRACTED_ERR || fl.monitor_cb.SRC_RDY_N || fl.monitor_cb.DST_RDY_N)
          @(ext_ifc.monitor_cb);
        if (!enabled) return;
      end while (!ext_ifc.monitor_cb.EXTRACTED_DONE && !ext_ifc.monitor_cb.EXTRACTED_ERR || fl.monitor_cb.SRC_RDY_N || fl.monitor_cb.DST_RDY_N);
    endtask : waitForTrans
 
    // -- Wait for end of frame -----------------------------------------------
    // It waits until end of frame
    task waitForEndOfFrame();
      do begin
        if (fl.monitor_cb.EOF_N || fl.monitor_cb.SRC_RDY_N || fl.monitor_cb.DST_RDY_N)
          @(fl.monitor_cb);
      end while (fl.monitor_cb.EOF_N || fl.monitor_cb.SRC_RDY_N || fl.monitor_cb.DST_RDY_N); //Detect end of frame
    endtask : waitForEndOfFrame
   
    // -- Receive Transaction -------------------------------------------------
    // It receives Extraction data transaction to tr object (ext_err or ext_done is/are set)
    task receiveTransaction(ExtDataTransaction tr);
      int byte_no;
      byte unsigned aux[];

      waitForTrans();  // Wait for extraction

      // Monitor receives transaction
      busy = 1;

      for (int i=0; i < pEXT_SIZE; i++) begin
         logic [7:0] wbyte = 0;
         for (int j=0; j<8; j++)
            wbyte[j] = ext_ifc.monitor_cb.EXTRACTED_DATA[i*8 + j];
         aux=new[byte_no+1](aux);
         aux[byte_no] = wbyte;
         byte_no++;         
       end

      // --------- Store received data into transaction -------------
      tr.ext_data = new[aux.size](aux);
      tr.ext_done = ext_ifc.monitor_cb.EXTRACTED_DONE;
      tr.ext_err  = ext_ifc.monitor_cb.EXTRACTED_ERR;

      waitForEndOfFrame(); // Wait until end of frame

      @(fl.monitor_cb);

    endtask : receiveTransaction
    
  endclass : ExtMonitor    
