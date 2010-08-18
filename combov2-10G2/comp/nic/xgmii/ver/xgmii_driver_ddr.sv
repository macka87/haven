/*!
 * \file xgmii_driver_ddr.sv
 * \brief Driver for XGMII DDR interface
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
 * $Id: xgmii_driver_ddr.sv 12328 2009-12-24 01:01:20Z xsanta06 $
 *
 */
 
  
  // --------------------------------------------------------------------------
  // -- XGMII DDR Driver
  // --------------------------------------------------------------------------
  
  /*!
   * \brief XGMII DDR Driver
   * 
   * This class is responsible for generating signals to XGMII interface.
   * Transactions are received by 'transMbx' (Mailbox) property. Unit must be
   * enabled by "setEnable()" function call. Generation can be stoped by 
   * "setDisable()" function call. You can send your custom transaction by
   * calling "sendTransaction" function.
   */
  class XgmiiDdrDriver extends Driver;
    
    // -- Public Class Attributes
    //! Virtual interface XGMII RX  
    virtual iXgmiiDdrRx.tb xgmii; 
    
    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates modul object and sets default values of InternalBus interface 
     * signals 
     */     
    function new ( string inst, 
                   tTransMbx transMbx, 
                   virtual iXgmiiDdrRx.tb xgmii
                   );
      super.new(inst, transMbx);
      this.xgmii       = xgmii;        // Store pointer interface 

      // Setting default values for Internal Bus interface
      this.xgmii.cb.RXC      <= '1;
      this.xgmii.cb.RXD      <= 32'h07070707;
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
      xgmii.cb.RXD <= 32'h07070707;
    
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
        transMbx.get(transaction);

        // Send Transaction
        sendTransaction(transaction);

        transaction.display(inst);
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
      logic [31:0] aux;
      logic [ 3:0] aux_ctrl;
      int i,j;

      // Send Start symbol, preamble and SFD
      xgmii.cb.RXC <= 4'b0001;
      xgmii.cb.RXD <= 32'h555555FB;
      @(xgmii.cb);
      xgmii.cb.RXC <= 4'b0000;
      xgmii.cb.RXD <= 32'hD5555555;
      @(xgmii.cb);

      // Send data (except last word)
      for (i=0; i<dataWithCrc.size/4; i++) begin
        for (j=0; j<4; j++) 
          for (int k=0; k<8; k++) 
            aux[8*j+k] = dataWithCrc[4*i+j][k];
        xgmii.cb.RXD <= aux;
        @(xgmii.cb);
      end

      // -- Send data (last word) --
      // Prepare Idle symbols
      aux      = 32'h07070707;
      aux_ctrl = '1;

      // Insert data
      for (j=0; j<dataWithCrc.size%4; j++) begin
        for (int k=0; k<8; k++)
          aux[8*j+k] = dataWithCrc[4*i+j][k];
        aux_ctrl[j] = 0;
      end  

      // Add Terminal symbols
      for (int k=0; k<8; k++) begin
        logic [7:0] terminal = 8'hFD;
        aux[8*j+k] = terminal[k];
      end  
      aux_ctrl[j] = 0;

      // Send
      xgmii.cb.RXC <= aux_ctrl;
      xgmii.cb.RXD <= aux;
      @(xgmii.cb);

      // Send obligate Idle symbols (minimally 4 bytes)
      if (j!=0) begin
        xgmii.cb.RXC <= '1;
        xgmii.cb.RXD <= 32'h07070707;
        @(xgmii.cb);
      end

      xgmii.cb.RXC <= '1;
      xgmii.cb.RXD <= 32'h07070707;
      @(xgmii.cb);

    endtask : sendData
    
  endclass : XgmiiDdrDriver
