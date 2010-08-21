/* \file scoreboard.sv
 * \brief XGMII IBUF Scoreboard
 * \author Marek Santa <santa@liberouter.org> 
 * \date 2009 
 */
/*  
 * Copyright (C) 2007 CESNET
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
 *
 *
 * TODO:
 *
 */

  
  // --------------------------------------------------------------------------
  // -- IBUF Model
  // --------------------------------------------------------------------------
  /*!
   * \brief IBUF Model
   * 
   * This class is responsible adding transaction into transaction table and 
   * offers possibility to modify transaction.  
   *    
   */
  
  class ScoreboardIbufModel;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Model is enabled
    bit       enabled;
    //! XGMII Transaction mailbox
    mailbox #(XgmiiTransaction) xgmiiMbx;
    //! SAU accepted queue
    bit acceptedQue[$];
    //! Transaction Table
    IbufTransactionTable xgmiiTable;
    //! Configuration settings
    tIbufConfig ibufConfig;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * \param xgmiiTable - transaction table for XGMII transactions
     */
    function new (IbufTransactionTable xgmiiTable);
      this.xgmiiTable = xgmiiTable;
      this.xgmiiMbx = new;
    endfunction
    
    // ------------------------------------------------------------------------
    //! Enable IBUF Model 
    /*!
     * Enable model and runs model process
     */     
    task setEnabled();
      enabled = 1; // Model Enabling
      fork         
        run();                // Creating model subprocess
      join_none;               // Don't wait for ending
    endtask : setEnabled

    // ------------------------------------------------------------------------
    //! Disable IBUF Model 
    task setDisabled();
      enabled = 0; // Disable model
    endtask : setDisabled
    
    // ------------------------------------------------------------------------
    //! Add XGMII Transaction 
    task addXgmiiTransation(XgmiiTransaction transaction);
      xgmiiMbx.put(transaction);
    endtask : addXgmiiTransation
    
    // ------------------------------------------------------------------------
    //! Add SAU Accepted 
    task addSauAccepted(bit accepted);
      acceptedQue.push_back(accepted);
    endtask : addSauAccepted
    
    // ------------------------------------------------------------------------
    //! Set IBUF Config 
    task setIbufConfig(tIbufConfig ibufConfig);
      this.ibufConfig = ibufConfig;
    endtask : setIbufConfig
    
    // -- Private Class Methods --
    
    // ------------------------------------------------------------------------
    //! Run IBUF Model
    /*!
     * 
     */      
    task run();
      XgmiiTransaction xgmiiTrans;
      Transaction tr;
            
      while (enabled) begin            // Repeat while enabled

        // Wait for XGMII Transaction
        xgmiiMbx.get(xgmiiTrans);

        // Check statistics

        // Check Sampling
        wait (acceptedQue.size() != 0);
        if (acceptedQue.pop_front() == 0)
          continue;

        // Check maskable errors
        if (checkMaskableErrors(xgmiiTrans))
          continue;

        // Add Transaction to Transaction table
        $cast(tr, xgmiiTrans);
        xgmiiTable.add(tr);

      end
    endtask : run

    // ------------------------------------------------------------------------
    //! Check maskable errors
    /*!
     * Checks maskable errors. 
     *
     * \param xgmiiTrans - XGMII transaction
     * \return 0 - no error occured         
     * \return 1 - error occured         
     */      
    function bit checkMaskableErrors(XgmiiTransaction xgmiiTrans);

      // XGMII error
      if (ibufConfig.pErrMaskRegXgmii && xgmiiTrans.xgmiiError)
        return 1;

      // CRC error
      if (ibufConfig.pErrMaskRegCrc && xgmiiTrans.crcError)
        return 1;

      // MIN TU error
      if (ibufConfig.pErrMaskRegMintu &&
          (xgmiiTrans.data.size + xgmiiTrans.crc.size < ibufConfig.pMintu))
        return 1;

      // MTU error
      if (ibufConfig.pErrMaskRegMtu &&
          (xgmiiTrans.data.size + xgmiiTrans.crc.size > ibufConfig.pMtu))
        return 1;

      // MAC error
      if (ibufConfig.pErrMaskRegMac && (ibufConfig.pMacCheck != 0)) begin
        bit allowedMac;

        allowedMac = 0;

        // Check available MACs
        for (int i = 0; i < ibufConfig.pMacs; i++) begin
          int matchingBytes;

          matchingBytes = 0;

          for (int j = 0; j < 6; j++) begin
            if (xgmiiTrans.data[j] == ibufConfig.pMacAddr[i][j])
              matchingBytes++;
            else break;

            if (matchingBytes == 6) allowedMac = 1;
          end

          if (allowedMac) break;
        end

        // Check broadcast
        if (!allowedMac && (ibufConfig.pMacCheck > 1)) begin
          int matchingBytes;

          matchingBytes = 0;

          for (int i = 0; i < 6; i++)
            if (xgmiiTrans.data[i] == 8'hFF)
              matchingBytes++;
            else break;

          if (matchingBytes == 6) allowedMac = 1;
        end

        // Check multicast
        if (!allowedMac && (ibufConfig.pMacCheck == 3)) begin
          if (xgmiiTrans.data[0][0] == 1) allowedMac = 1;
        end

        if (!allowedMac) return 1;
      end

      return 0;
    endfunction : checkMaskableErrors

   endclass : ScoreboardIbufModel

  // --------------------------------------------------------------------------
  // -- Sampling Unit Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief Sampling Unit Callbacks
   * 
   * This class is responsible adding transaction into transaction table and 
   * offers possibility to modify transaction.  
   *    
   */
  
  class ScoreboardSamplingCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! IBUF Model
    ScoreboardIbufModel ibufModel;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     */
    function new (ScoreboardIbufModel ibufModel);
      this.ibufModel = ibufModel;
    endfunction
    
    // -- Post_tx -------------------------------------------------------------
    //! Post_tx 
    /*!
     * Function is called after transaction is sended.
     * 
     * \param accepted - XGMII transaction was accepted by Sampling Unit 
     * \param inst - driver identifier         
     */
    virtual task post_tx(bit accepted, string inst);
      ibufModel.addSauAccepted(accepted);
    endtask

   endclass : ScoreboardSamplingCbs

  // --------------------------------------------------------------------------
  // -- XGMII Driver Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief XGMII Driver Callbacks
   * 
   * This class is responsible adding transaction into transaction table and 
   * offers possibility to modify transaction.  
   *    
   */
  
  class ScoreboardXgmiiDriverCbs extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! IBUF Model
    ScoreboardIbufModel ibufModel;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     */
    function new (ScoreboardIbufModel ibufModel);
      this.ibufModel = ibufModel;
    endfunction
    
    // -- Post_tx -------------------------------------------------------------
    //! Post_tx 
    /*!
     * Function is called after transaction is sended.
     * 
     * \param transaction - transaction 
     * \param inst - driver identifier         
     */
    virtual task post_tx(Transaction transaction, string inst);
      XgmiiTransaction to;

      $cast(to, transaction);

      ibufModel.addXgmiiTransation(to);
    endtask

   endclass : ScoreboardXgmiiDriverCbs


  // --------------------------------------------------------------------------
  // -- PACODAG Driver Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief PACODAG Driver Callbacks
   * 
   * This class is responsible adding transaction into transaction table and 
   * offers possibility to modify transaction.  
   *    
   */
  
  class ScoreboardPcdDriverCbs extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Transaction table for PACODAG data
    TransactionTable #(TR_TABLE_FIRST_ONLY) pcdTable;
    //! Control header or footer data enabled
    bit ctrlHdrFtrEn = 1;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * \param pcdTable - transaction table for PACODAG transactions
     */
    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) pcdTable);
      this.pcdTable = pcdTable;
    endfunction
    
    // ------------------------------------------------------------------------
    //! Set CTRL Header or Footer enable 
    task setCtrlHdrFtrEn(bit ctrlHdrFtrEn = 1);
      this.ctrlHdrFtrEn = ctrlHdrFtrEn;
    endtask : setCtrlHdrFtrEn
    
    // -- Post_tx -------------------------------------------------------------
    //! Post_tx 
    /*!
     * Function is called after transaction is sended.
     * 
     * \param transaction - transaction 
     * \param inst - driver identifier         
     */
    virtual task post_tx(Transaction transaction, string inst);
      if (ctrlHdrFtrEn)
        pcdTable.add(transaction);
    endtask

   endclass : ScoreboardPcdDriverCbs

  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief Frame Link Monitor Callbacks
   * 
   * This class is responsible for removing transaction from transaction table.
   *    
   * \param behav - TransactionTable behavior                
   */
  
  class ScoreboardFlMonitorCbs extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Transaction Table
    TransactionTable #(TR_TABLE_FIRST_ONLY) pcdTable;
    IbufTransactionTable xgmiiTable;
    //! Configuration settings
    tIbufConfig ibufConfig;
    
    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * \param pcdTable - transaction table for PACODAG transactions
     * \param xgmiiTable - transaction table for XGMII transactions
     */
    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) pcdTable,
                  IbufTransactionTable xgmiiTable
                        );
      this.pcdTable   = pcdTable;
      this.xgmiiTable = xgmiiTable;
    endfunction
    
    // ------------------------------------------------------------------------
    //! Set IBUF Config 
    task setIbufConfig(tIbufConfig ibufConfig);
      this.ibufConfig = ibufConfig;
    endtask : setIbufConfig
    
    // -- Post_rx -------------------------------------------------------------
    //! Post_tx 
    /*!
     * Function is called after transaction is received. It checks transaction 
     * table for the same transaction. If they match, transaction is removed, 
     * otherwise error is reporting.                         
     * 
     * \param transaction - transaction 
     * \param inst - monitor identifier         
     */
    virtual task post_rx(Transaction transaction, string inst);
      FrameLinkTransaction flTrans;
      PacodagTransaction   pcdTrans   = new();
      XgmiiTransaction     xgmiiTrans = new();
      bit pcdStatus=0, xgmiiStatus=0;

      $cast(flTrans, transaction);

      // Split FrameLink transaction into XGMII and PACODAG
      splitFlTransaction(flTrans, xgmiiTrans, pcdTrans);

      // Remove PACODAG Transaction
      if (ibufConfig.pCtrlHdrEn || ibufConfig.pCtrlFtrEn)
        pcdTable.remove(pcdTrans, pcdStatus);
      else pcdStatus = 1;

      // Remove XGMII Transaction
      xgmiiTable.remove(xgmiiTrans, xgmiiStatus, ibufConfig.pInbandfcs);

      if (xgmiiStatus==0 || pcdStatus==0)begin
        $write("Unknown transaction received from monitor %d\n", inst);
        $timeformat(-9, 3, " ns", 8);
        $write("Time: %t\n", $time);
        transaction.display(); 
        pcdTable.display(.inst("PACODAG"));
        xgmiiTable.display(.inst("XGMII"));
        $stop;
      end;
    endtask

    // ------------------------------------------------------------------------
    //! Split FrameLink Transaction
    /*!
     * It splits FrameLink transaction into XGMII and PACODAG transactions. 
     *
     * \param flTrans - FrameLink transaction
     * \param xgmiiTrans - XGMII transaction
     * \param pcdTrans - PACODAG transaction
     */      
    function void splitFlTransaction(FrameLinkTransaction flTrans,
                                     XgmiiTransaction xgmiiTrans,
                                     PacodagTransaction pcdTrans
                                          );
      int flPartNo = 0, pcdPartNo = 0;
      
      // Check correct FrameLink transaction part count
      if (flTrans.packetCount!=1+ibufConfig.pCtrlHdrEn+ibufConfig.pCtrlFtrEn)
      begin
        $write("FrameLink transaction contains incorrect part count.\n");
        flTrans.display();
        $stop;
      end

      // Set PACODAG part count
      if (ibufConfig.pCtrlHdrEn || ibufConfig.pCtrlFtrEn)
        pcdTrans.partCount = flTrans.packetCount - 1;

      pcdTrans.data   = new[pcdTrans.partCount];

      // Copy header
      if (ibufConfig.pCtrlHdrEn) 
        pcdTrans.data[pcdPartNo++] = flTrans.data[flPartNo++];

      // Copy payload with/without CRC
      if (ibufConfig.pInbandfcs) begin
        xgmiiTrans.data 
          = new[flTrans.data[flPartNo].size()-4](flTrans.data[flPartNo]);

        for (int i=0; i < 4; i++)
          xgmiiTrans.crc[i] 
            = flTrans.data[flPartNo][flTrans.data[flPartNo].size()-4+i];

        flPartNo++;
      end
      else begin
//        xgmiiTrans.data = new;
        xgmiiTrans.data = flTrans.data[flPartNo++];
      end

      // Copy footer
      if (ibufConfig.pCtrlFtrEn) 
        pcdTrans.data[pcdPartNo] = flTrans.data[flPartNo];

    endfunction : splitFlTransaction
 
  endclass : ScoreboardFlMonitorCbs


  // --------------------------------------------------------------------------
  // -- XGMII IBUF Scoreboard
  // -------------------------------------------------------------------------- 
  /*!
   * \brief XGMII IBUF Scoreboard
   * 
   * This class is responsible for creating Tranaction table and monitor and 
   * driver callback classes. It also prints Transaction table.   
   *    
   * \param behav - TransactionTable behavior                
   */
  class XgmiiIbufScoreboard #(int behav=TR_TABLE_FIRST_ONLY);
    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Scoreboard identification
    string inst;
    
    //! Transaction Table
    TransactionTable     #(TR_TABLE_FIRST_ONLY) pcdTable;
    IbufTransactionTable       xgmiiTable;
    //! IBUF Model
    ScoreboardIbufModel        ibufModel;
    //! XGMII Driver callback
    ScoreboardXgmiiDriverCbs   xgmiiDriverCbs;
    //! PACODAG Driver callback
    ScoreboardPcdDriverCbs     pcdDriverCbs;
    //! Sampling Unit callback
    ScoreboardSamplingCbs      samplingCbs;
    //! Monitor callback
    ScoreboardFlMonitorCbs     flMonitorCbs;

    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * It creates monitor and driver callbacks and Transaction Table for each 
     * flow.
     * 
     * \param inst - scoreboard identification
     */
    function new (string inst="");
      this.inst = inst;
    
      this.pcdTable   = new; 
      this.xgmiiTable = new; 
      this.ibufModel  = new(xgmiiTable); 

      this.xgmiiDriverCbs = new(ibufModel);
      this.pcdDriverCbs   = new(pcdTable);
      this.samplingCbs    = new(ibufModel);
      this.flMonitorCbs   = new(pcdTable, xgmiiTable);
    endfunction

    // ------------------------------------------------------------------------
    //! Enable IBUF Model 
    task setEnabled();
      ibufModel.setEnabled(); // Enable model
    endtask : setEnabled
    
    // ------------------------------------------------------------------------
    //! Disable IBUF Model 
    task setDisabled();
      ibufModel.setDisabled(); // Disable model
    endtask : setDisabled
    
    // ------------------------------------------------------------------------
    //! Set IBUF Config 
    task setIbufConfig(tIbufConfig ibufConfig);
      // Set config
      ibufModel.setIbufConfig(ibufConfig);
      // Set config
      flMonitorCbs.setIbufConfig(ibufConfig);
      // Set CTRL Header or Footer enable
      pcdDriverCbs.setCtrlHdrFtrEn(ibufConfig.pCtrlHdrEn || 
                                   ibufConfig.pCtrlFtrEn);
    endtask : setIbufConfig
     
    // ------------------------------------------------------------------------
    //! Set Transaction table behaviour 
    task setTrTableBehav(int firstOnly = 0);
      xgmiiTable.firstOnly = firstOnly; // Disable model
    endtask : setTrTableBehav
    
    // -- Display -------------------------------------------------------------
    //! Display 
    /*!
     * It prints Transaction Table
     */
    task display();
      pcdTable.display(.inst("PACODAG"));
      xgmiiTable.display(.inst("XGMII"));
    endtask
  
  endclass : XgmiiIbufScoreboard

