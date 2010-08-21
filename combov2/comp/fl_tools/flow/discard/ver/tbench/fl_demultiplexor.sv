/*
 * fl_demultiplexor.sv: FrameLink Demultiplexor
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
 * $Id: fl_demultiplexor.sv 14277 2010-07-09 07:46:50Z xsanta06 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- Frame Link Demultiplexor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for reading signals from FrameLink
   * interface. Transactions are received from input interface and
   * demultiplexed to output interfaces.
   */
  class FrameLinkDemultiplexor #(int pDataWidth=32, int pDremWidth=2,
                                 int pChannels=2, int pStatusWidth=16);

    // -- Private Class Atransibutes --
    bit    enabled = 0;
    string inst;
    int unsigned channel;
    virtual iFrameLinkTx.tb #(pDataWidth, pDremWidth) tx;
    virtual iFrameLinkRx.tb #(pDataWidth, pDremWidth) rx[pChannels];
    virtual iDiscardStat.tx_tb #(pChannels, pStatusWidth) chan;
  
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   virtual iFrameLinkTx.tb #(pDataWidth,pDremWidth) tx,
                   virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) rx[],
                   virtual iDiscardStat.tx_tb #(pChannels, pStatusWidth) chan
                         );
      this.inst        = inst;
      this.tx          = tx;         // Store pointer interface 
      this.rx          = rx;         // Store pointer interface 
      this.chan        = chan;       // Store pointer interface 

      for (int i=0; i<pChannels; i++) begin
        this.rx[i].cb.DATA           <= 0;
        this.rx[i].cb.DREM           <= 0;
        this.rx[i].cb.SOF_N          <= 1;
        this.rx[i].cb.EOF_N          <= 1;
        this.rx[i].cb.SOP_N          <= 1;
        this.rx[i].cb.EOP_N          <= 1;
        this.rx[i].cb.SRC_RDY_N      <= 1;
      end
    endfunction: new  
    
    // -- Enable Demultiplexor -----------------------------------------------
    // Enable demultiplexor and runs demultiplexor process
    task setEnabled();
      enabled = 1; // Demultiplexor Enabling
      fork         
        run();     // Creating demultiplexor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Multipexor --------------------------------------------------
    // Disable demultiplexor
    task setDisabled();
      enabled = 0; //Disable demultiplexor
    endtask : setDisabled
    
    // -- Private Class Methods --
    
    // -- Run Demultiplexor ---------------------------------------------------
    // According to channel demultiplex signals form input interface to 
    // respective output interface
    task run();
      int unsigned channel;
      @(tx.cb);                        // Wait for clock
      
      while (enabled) begin            // Repeat while enabled
        for (int i=0; i<pChannels; i++)
          rx[i].cb.SRC_RDY_N <= 1;

        channel = chan.tx_cb.TX_CHAN;
        rx[channel].cb.DATA      <= tx.cb.DATA;
        rx[channel].cb.DREM      <= tx.cb.DREM;
        rx[channel].cb.SOF_N     <= tx.cb.SOF_N;
        rx[channel].cb.EOF_N     <= tx.cb.EOF_N;
        rx[channel].cb.SOP_N     <= tx.cb.SOP_N;
        rx[channel].cb.EOP_N     <= tx.cb.EOP_N;
        rx[channel].cb.SRC_RDY_N <= tx.cb.SRC_RDY_N;
        @(tx.cb);
      end
    endtask : run
     
  endclass : FrameLinkDemultiplexor 

