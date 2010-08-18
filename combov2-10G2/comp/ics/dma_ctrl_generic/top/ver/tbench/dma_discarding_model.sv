/*
 * dma_discarding_model.sv: Discarding Model for DMA Module Gen
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
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
 * $Id: dma_discarding_model.sv 14846 2010-08-05 08:34:48Z xsanta06 $
 *
 * TODO:
 *
 */
 
  import math_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class DiscardStatDriverCbs #(int pChannels=2) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    DriverCbs cbs[$];                          // Callbacks list
    bit discardFlag[pChannels] = '{default: 0};
    longint unsigned droppedFrames[pChannels] = '{default: 0};
    longint unsigned passedFrames[pChannels]  = '{default: 0};
    longint unsigned droppedLength[pChannels] = '{default: 0};
    longint unsigned passedLength[pChannels]  = '{default: 0};

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new();
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called before is transaction sended 
    virtual task pre_tx(ref Transaction transaction, string inst);
       cbs[0].pre_tx(transaction, inst);
    endtask

    // ------------------------------------------------------------------------
    // Function is called after is transaction sended 
    virtual task post_tx(Transaction transaction, string inst);
       // Gets number of transaction table from instance name
       int i;
       string driverLabel;
       FrameLinkTransaction tr;

       $cast(tr, transaction);
       
       for(i=0; i < pChannels; i++) begin
         $swrite(driverLabel, "Driver%0d", i);
         if (driverLabel == inst) break;
       end  

       if (discardFlag[i]) begin
         discardFlag[i] = 0;
         droppedFrames[i]++;
         droppedLength[i] += tr.data[0].size+tr.data[1].size;
       end
       else begin
         cbs[0].post_tx(transaction, inst);
         passedFrames[i]++;
         passedLength[i] += tr.data[0].size+tr.data[1].size;
       end  
    endtask

    // ------------------------------------------------------------------------
    // Function sets flag to discard actual frame 
    function void setDiscardFlag(int channel);
       discardFlag[channel] = 1;
    endfunction

    // ------------------------------------------------------------------------
    // Get frames statistics
    function void getStats(output longint unsigned df[], pf[], dl[], pl[]);
       df = droppedFrames;
       pf = passedFrames;
       dl = droppedLength;
       pl = passedLength;
    endfunction

   endclass : DiscardStatDriverCbs
  
  // --------------------------------------------------------------------------
  // -- Frame Link Discarding Model Class
  // --------------------------------------------------------------------------
  /* This class is responsible for prediction of packet discarding. Unit must 
   * be enabled by "setEnable()" function call. Monitoring can be stoped by 
   * "setDisable()" function call.
   */
  class DmaDiscardingModel #(int pDataWidth=32, pDremWidth=2, 
                                 pChannels=2, pStatusWidth=16);
    
    // -- Private Class Atributes --
    string    inst;                            // Checker identification
    bit       enabled;                         // Checker is enabled
    DiscardStatDriverCbs #(pChannels) discardStatCbs;
    virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) rx;
    virtual iDiscardStat.rx_tb #(pChannels,pStatusWidth) chan;
    virtual iDiscardStat.stat_tb #(pChannels,pStatusWidth) stat;

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) rx,
                   virtual iDiscardStat.rx_tb #(pChannels,pStatusWidth) chan,
                   virtual iDiscardStat.stat_tb #(pChannels,pStatusWidth) stat
                   );
      this.enabled     = 0;           // Model is disabled by default   
      this.rx          = rx;          // Store pointer interface 
      this.chan        = chan;        // Store pointer interface  
      this.stat        = stat;        // Store pointer interface  
      this.inst        = inst;        // Store driver identifier
      this.discardStatCbs   = new();
      
    endfunction

    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(DriverCbs cbs);
      discardStatCbs.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // -- Enable Model --------------------------------------------------------
    // Enable model and runs model's process
    task setEnabled();
      enabled = 1; // Model Enabling
      fork         
        run();     // Creating model subprocess
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
      int unsigned channel;
      logic[pStatusWidth-1:0] status;
      logic[pChannels*pStatusWidth-1:0] wholeStatus;
      logic[pStatusWidth-1:0] statusMask = '1;
      logic[15:0]             packetSize;
      int unsigned            maxStatus = 1<<(pStatusWidth+log2(pDataWidth/8)-1);

      while (enabled) begin                   // Repeat in forever loop
        // Wait for Start of Frame
        waitForSOFandGetStatus(wholeStatus);

        channel = chan.rx_cb.RX_CHAN;
        status = (wholeStatus >> (channel*pStatusWidth)) & statusMask;

        packetSize = rx.cb.DATA[15:0];
        $write("Channel: %0d Status(words): %4h Status: %4h packetSize: %4h\n",
                channel,status,status*pDataWidth/8,packetSize);

        if (status*pDataWidth/8+packetSize+pDataWidth/8 > maxStatus) begin
          // There is no space for packet
          discardStatCbs.setDiscardFlag(channel);
          $write("discarding\n");
        end 

        @(rx.cb);
      end
    endtask : run
    
    // -- Wait for SOF -------------------------------------------------------
    // Wait for Start of Frame
    task waitForSOFandGetStatus(inout logic[pChannels*pStatusWidth-1:0] 
                                                                 wholeStatus);
      while (rx.cb.SOF_N || rx.cb.SRC_RDY_N || rx.cb.DST_RDY_N) begin
        wholeStatus = stat.stat_cb.BUF_STATUS;
        @(rx.cb);
      end
    endtask : waitForSOFandGetStatus

    // -- Get Stats -----------------------------------------------------------
    // Get frames statistics
    function void getStats(output longint unsigned df[], pf[], dl[], pl[]);
      discardStatCbs.getStats(df,pf,dl,pl);
    endfunction

endclass : DmaDiscardingModel    
