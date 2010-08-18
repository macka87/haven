/*!
 * \file xgmii_monitor_sdr.sv
 * \brief Monitor for XGMII SDR interface
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
 * $Id: xgmii_monitor_sdr.sv 14807 2010-08-04 08:21:35Z xsanta06 $
 *
 */
 
  
  // --------------------------------------------------------------------------
  // -- XGMII SDR Monitor
  // --------------------------------------------------------------------------
  
  /*!
   * \brief XGMII SDR Monitor
   * 
   * This class is responsible for creating transaction objects from 
   * XGMII SDR interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class XgmiiSdrMonitor extends Monitor;
    
    // -- Public Class Attributes --
    //! Virtual interface XGMII TX  
    virtual iXgmiiSdrTx.tb xgmii; 
    //! Idle Counter
    int unsigned idleCounter = 0;
    //! Deficit Idle Count
    int deficitIdleCount = 0;

    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates modul object and sets default values of InternalBus interface 
     * signals 
     */     
    function new ( string inst, 
                   virtual iXgmiiSdrTx.tb xgmii
                   );
      super.new(inst);

      this.xgmii       = xgmii;        // Store pointer interface 

    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Receive Transaction
    /* 
     * Receive transaction from XGMII interface
     * \param transaction - transaction
     */
    virtual task receiveTransaction( Transaction transaction );
      XgmiiTransaction tr;
      $cast(tr, transaction);

      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_rx(transaction, inst);       
      
      // Receive Data
      receiveData(tr);
      
      // Necessary for not calling callback after monitor disabling
      if (!enabled) return;

      #(0); // Necessary for not calling callback before driver
        
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_rx(transaction, inst);
      
      // Monitor received transaction and is not busy
      busy = 0;
    endtask : receiveTransaction
    
    // -- Private Class Methods --
    
    // ------------------------------------------------------------------------
    //! Run XGMII Monitor
    /*!
     * Receive transactions and send them for srocessing by call back
     */      
    virtual task run();
      Transaction transaction;
      XgmiiTransaction tr;
            
      // Wait for clock
      @(xgmii.cb);
      
      while (enabled) begin            // Repeat while enabled
        tr = new;
        $cast(transaction, tr);
      
        // Receive Transaction
        receiveTransaction(transaction);

        // Display transaction
        `ifdef XGMII_MONITOR_DEBUG
          transaction.display(inst);
        `endif
      end
    endtask : run

    // ------------------------------------------------------------------------
    //! Receive data
    /*!
     * Receive XGMII transaction data
     */
    task receiveData(XgmiiTransaction tr);
      // Data with CRC
      byte dataWithCrc[];
      logic [63:0] aux;
      logic [ 7:0] aux_ctrl;
      int i,j;
      int errorPos = 0;
      int offset   = 0;

      // Wait for Start symbol, preamble and SFD
      waitForStartOfFrame();

      // Return if monitor was disabled while waiting for start of frame
      if (!enabled) return;

      busy = 1;
      @(xgmii.cb);

      // -- Receive data (from word with preamble and SFD)
      if (xgmii.cb.TXD[31:0] == 32'hD5555555) begin
        idleCounter += 4;

        dataWithCrc = new[4];
        for (j=0; j<4; j++)
          for (int k=0; k<8; k++) 
            dataWithCrc[8*i+j][k] = xgmii.cb.TXD[32+8*j+k];
        offset = 4;
        @(xgmii.cb);
      end

      // Check Inter Packet Gap according to DIC
      if (idleCounter <= 15) begin
        deficitIdleCount = 12 - idleCounter + deficitIdleCount;
      end
      else deficitIdleCount = ((idleCounter%4 ? 4 - idleCounter%4 : 0) +
                                                       deficitIdleCount) % 4;
      assert (deficitIdleCount >=0 && deficitIdleCount <=3)
      else $error("Incorrect Inter Packet Gap");

      // -- Receive data (except last word) --
      while (1) begin
        if (xgmii.cb.TXC != 0)
          break;

        dataWithCrc = new[dataWithCrc.size + 8](dataWithCrc);
        for (j=0; j<8; j++)
          for (int k=0; k<8; k++) 
            dataWithCrc[8*i+j+offset][k] = xgmii.cb.TXD[8*j+k];
        i++;
        @(xgmii.cb);
      end

/*      for (i=0; i<dataWithCrc.size/8; i++) begin
        aux_ctrl = '0;
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
          errorPos++;
        end

        // send data
        xgmii.cb.RXC <= aux_ctrl;
        xgmii.cb.RXD <= aux;
      end
*/
      // -- Receive data (last word) --
      j = 0;
      idleCounter = 0;
      while(xgmii.cb.TXC[j] == 0) begin
        dataWithCrc = new[dataWithCrc.size + 1](dataWithCrc);

        for (int k=0; k<8; k++) 
          dataWithCrc[8*i+j+offset][k] = xgmii.cb.TXD[8*j+k];

        j++;
      end
      idleCounter = 8-j;

      @(xgmii.cb);

      // -- Store data into transaction -- 
      tr.data = new[dataWithCrc.size - 4](dataWithCrc);
      for (j=0; j < 4; j++)
        tr.crc[j] = dataWithCrc[dataWithCrc.size - 4 + j];

    endtask : receiveData
    
    // ------------------------------------------------------------------------
    //! Wait For Start of Frame
    /*!
     * Wait for Start symbol, preamble and SFD
     */
    task waitForStartOfFrame();
      while (enabled && (xgmii.cb.TXC != 8'b00000001 || 
             xgmii.cb.TXD != 64'hD5555555555555FB) &&
             (xgmii.cb.TXC != 8'b00011111 ||
             xgmii.cb.TXD != 64'h555555FB07070707)) begin
        idleCounter += 8;
        @(xgmii.cb);
      end
    endtask : waitForStartOfFrame

  endclass : XgmiiSdrMonitor
