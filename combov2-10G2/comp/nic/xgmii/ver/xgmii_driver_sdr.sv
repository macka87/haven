/*!
 * \file xgmii_driver_sdr.sv
 * \brief Driver for XGMII SDR interface
 * \author Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
 * $Id: xgmii_driver_sdr.sv 14064 2010-06-16 12:38:59Z xsanta06 $
 *
 */
 
  
  // --------------------------------------------------------------------------
  // -- XGMII SDR Driver
  // --------------------------------------------------------------------------
  
  /*!
   * \brief XGMII SDR Driver
   * 
   * This class is responsible for generating signals to XGMII interface.
   * Transactions are received by 'transMbx' (Mailbox) property. Unit must be
   * enabled by "setEnable()" function call. Generation can be stoped by 
   * "setDisable()" function call. You can send your custom transaction by
   * calling "sendTransaction" function.
   */
  class XgmiiSdrDriver extends Driver;
    
    // -- Public Class Attributes --
    //! Virtual interface XGMII RX  
    virtual iXgmiiSdrRx.tb xgmii; 

    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates modul object and sets default values of InternalBus interface 
     * signals 
     */     
    function new ( string inst, 
                   tTransMbx transMbx, 
                   virtual iXgmiiSdrRx.tb xgmii
                   );
      super.new(inst, transMbx);

      this.xgmii       = xgmii;        // Store pointer interface 

      // Setting default values for Internal Bus interface
      this.xgmii.cb.RXC      <= '1;
      this.xgmii.cb.RXD      <= 64'h0707070707070707;
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Send Transaction
    /* 
     * Send transaction to XGMII interface
     * \param transaction - transaction
     */
    virtual task sendTransaction( Transaction transaction );
      XgmiiTransaction tr;
      
      // Driver is sending transaction
      busy = 1;

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(transaction, inst);       
      
      // Wait before sending transaction
      if (enDelay) repeat (delay) @(xgmii.cb);
            
      // Send transaction
      $cast(tr, transaction); 
      sendData(tr);
      
      // Set not ready 
      xgmii.cb.RXC <= '1;
      xgmii.cb.RXD <= 64'h0707070707070707;
    
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(transaction, inst);
      
      // Driver is not sending transaction
      busy = 0;
    endtask : sendTransaction
    
    // -- Private Class Methods --
    
    // ------------------------------------------------------------------------
    //! Run XGMII Driver
    /*!
     * Take transactions from mailbox and generate them to interface
     */      
    virtual task run();
      Transaction transaction;
            
      // Wait for clock
      @(xgmii.cb);
      
      while (enabled) begin            // Repeat while enabled
        // Randomize rand variables
        assert(randomize());

        // Get transaction from mailbox 
        while (transMbx.try_get(transaction)==0) begin
          if (!enabled) return;
          @(xgmii.cb);
        end

        // Send Transaction
        sendTransaction(transaction);

//        transaction.display(inst);
      end
    endtask : run

    // ------------------------------------------------------------------------
    //! Send data
    /*!
     * Send XGMII transaction data
     */
    task sendData(XgmiiTransaction tr);
      // Data with CRC
      byte dataWithCrc[] = {tr.data, tr.crc};
      logic [63:0] aux;
      logic [ 7:0] aux_ctrl;
      int i,j;
      int errorPos = 0;

      // Send Start symbol, preamble and SFD
      xgmii.cb.RXC <= 8'b00000001;
      xgmii.cb.RXD <= 64'hD5555555555555FB;
      @(xgmii.cb);

      // -- Send data (except last word) --
      for (i=0; i<dataWithCrc.size/8; i++) begin
        aux_ctrl = '0;
        for (j=0; j<8; j++) begin
          if (tr.xgmiiError && (tr.xgmiiErrorPos == errorPos)) begin
            // -- Show XGMII error in waveform
            `ifdef SHOW_XGMII_ERROR
              $info("XGMII Error");
            `endif
            // --
            // inject error
            for (int k=0; k<8; k++) begin
              logic [7:0] error = 8'hFE;
              aux[8*j+k] = error[k];
            end
            aux_ctrl[j] = 1;
          end
          else 
            for (int k=0; k<8; k++) 
              aux[8*j+k] = dataWithCrc[8*i+j][k];
          errorPos++;
        end

        // send data
        xgmii.cb.RXC <= aux_ctrl;
        xgmii.cb.RXD <= aux;
        @(xgmii.cb);
      end

      // -- Send data (last word) --
      // Prepare Idle symbols
      aux      = 64'h0707070707070707;
      aux_ctrl = '1;

      // Insert data 
      for (j=0; j<dataWithCrc.size%8; j++) begin
        if (tr.xgmiiError && (tr.xgmiiErrorPos == errorPos)) begin
          // inject error
          for (int k=0; k<8; k++) begin
            logic [7:0] error = 8'hFE;
            aux[8*j+k] = error[k];
          end
        end
        else begin 
          for (int k=0; k<8; k++)
            aux[8*j+k] = dataWithCrc[8*i+j][k];
          aux_ctrl[j] = 0;
        end  
        errorPos++;
      end  

      // Add Terminal symbol
      for (int k=0; k<8; k++) begin
        logic [7:0] terminal = 8'hFD;
        aux[8*j+k] = terminal[k];
      end  

      // -- Show packets with bad CRC in waveform
      `ifdef SHOW_CRC_ERROR
        if(tr.crcError) $info("CRC Error");
      `endif
      // --

      // Send
      xgmii.cb.RXC <= aux_ctrl;
      xgmii.cb.RXD <= aux;
      @(xgmii.cb);

      // Send obligate Idle symbols (minimally 4 bytes)
      if (j>3) begin
        xgmii.cb.RXC <= '1;
        xgmii.cb.RXD <= 64'h0707070707070707;
        @(xgmii.cb);
      end

    endtask : sendData
    
  endclass : XgmiiSdrDriver
