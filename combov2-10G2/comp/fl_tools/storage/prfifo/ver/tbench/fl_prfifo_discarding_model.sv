/*
 * fl_fifo_discarding_model.sv: FrameLink PRFIFO Discarding Model
 * Copyright (C) 2009 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
 * $Id: fl_prfifo_discarding_model.sv 11282 2009-09-23 13:28:17Z xsanta06 $
 *
 * TODO:
 *
 */
 
  import math_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class PrfifoDriverCbs extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    Transaction tr;
    event e;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new(event e);
      this.tr = null;
      this.e  = e;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended 
    
    virtual task post_tx(Transaction transaction, string inst);
       tr = transaction;
//       tr.display("POST TX");
       -> e;
    endtask

   endclass : PrfifoDriverCbs
  
  // --------------------------------------------------------------------------
  // -- Frame Link PRFIFO Discarding Model Class
  // --------------------------------------------------------------------------
  /* This class is responsible for prediction of packet discarding. Unit must 
   * be enabled by "setEnable()" function call. Monitoring can be stoped by 
   * "setDisable()" function call.
   */
  class PrfifoDiscardingModel #(int pDataWidth=32, pDremWidth=2, pItems=16);
    
    // -- Private Class Atributes --
    string    inst;                            // Checker identification
    bit       enabled;                         // Checker is enabled
    DriverCbs cbs[$];                          // Callbacks list
    PrfifoDriverCbs prfifoCbs;
    event     e, rxEvent, txEvent;
    virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) rx;
    virtual iFrameLinkTx.tb #(pDataWidth,pDremWidth) tx;

    int items = 0;                     // Items allready stored in fifo
    int frameItems = 0;                // Item count of actual frame
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) rx,
                   virtual iFrameLinkTx.tb #(pDataWidth,pDremWidth) tx
                   );
      this.enabled     = 0;           // Monitor is disabled by default   
      this.rx          = rx;          // Store pointer RX interface 
      this.tx          = tx;          // Store pointer TX interface  
      this.inst        = inst;        // Store driver identifier
      this.prfifoCbs   = new(e);
      
    endfunction

    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // -- Enable Model --------------------------------------------------------
    // Enable model and runs model's process
    task setEnabled();
      enabled = 1; // Model Enabling
      fork         
        run();     // Creating model subprocess
        rxUpdateItems();     // Creating model subprocess
        txUpdateItems();     // Creating model subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Model -------------------------------------------------------
    // Disable checker
    task setDisabled();
      enabled = 0; // Disable model
    endtask : setDisabled 
    
    // -- Run Model -----------------------------------------------------------
    // Predict packet discarding
    task run();
      bit discardFrame = 0;              // Discarding flag
      string label;

      while (enabled) begin                   // Repeat in forever loop
        // Wait for updating actual items count
        wait (rxEvent.triggered);
        wait (txEvent.triggered);

//        $write("%0d - items:%0d\n",$time,items);
        // Decide if frame will be discarded
        if (!rx.cb.SRC_RDY_N && (items >= pItems)) begin
          discardFrame = 1;
        end 
        
        if (!rx.cb.EOF_N && !rx.cb.SRC_RDY_N && !rx.cb.DST_RDY_N) begin         
          // Wait for calling callback by driver
          wait (e.triggered);
          // Discard frame
          if (discardFrame) begin
            $swrite(label,"Discarded Frame @%0d",$time); 
//            prfifoCbs.tr.display(label);           
            items -= frameItems;
          end  
          // Send frame to scoreboard
          else begin
            foreach (cbs[i]) cbs[i].post_tx(prfifoCbs.tr, inst);
            $swrite(label,"Added Frame @%0d",$time); 
//            prfifoCbs.tr.display(label);           
          end  
          // Reset discarding flag
          discardFrame = 0;
          prfifoCbs.tr = null;
        end
        @(rx.cb);
      end
    endtask : run
    
    // -- RX Update Items -----------------------------------------------------
    // Update status (count stored items) according to Rx interface
    task rxUpdateItems();
      
      while (enabled) begin

        if (!rx.cb.SRC_RDY_N && !rx.cb.DST_RDY_N) begin
          if (!rx.cb.SOF_N) frameItems = 1;

          @(rx.cb);
          // Count items of current frame
          frameItems++;
          // Update overall items count
          items++;        
        end
        else @(rx.cb);
        -> rxEvent;
      end  
      
    endtask : rxUpdateItems    

    // -- TX Update Items -----------------------------------------------------
    // Update status (count stored items) according to Tx interfaces
    task txUpdateItems();
      
      while (enabled) begin
        if (!tx.cb.SRC_RDY_N) begin
          // Update overall items count
          items--;
          // Wait for TX DST RDY
          while(tx.cb.SRC_RDY_N || tx.cb.DST_RDY_N) begin
            @(tx.cb);
            -> txEvent;
          end  
        end
        @(tx.cb);
        -> txEvent;
      end  
      
    endtask : txUpdateItems    
        
endclass : PrfifoDiscardingModel    
