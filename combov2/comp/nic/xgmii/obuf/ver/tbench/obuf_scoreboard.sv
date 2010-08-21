/* \file obuf_scoreboard.sv
 * \brief OBUF Scoreboard
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
 *
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import math_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief Frame Link Driver Callbacks
   * 
   * This class is responsible adding transaction into transaction table and 
   * offers possibility to modify transaction.  
   *    
   * \param behav - TransactionTable behavior                
   */
  
  class ScoreboardDriverCbs #(int behav=TR_TABLE_FIRST_ONLY)
                                                   extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Transaction Table
    TransactionTable #(behav) sc_table;
    //! MAC address
    byte macAddress[6];

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * \param sc_table - transaction tables
     */
    function new (TransactionTable #(behav) sc_table);
      this.sc_table = sc_table;
    endfunction
    
    // -- Pre_tx --------------------------------------------------------------
    //! Pre_tx 
    /*!
     * Function is called before transaction is sended. It modifies transaction
     * in way first two bytes of deader sets to header size, second two bytes 
     * sets to payload size.          
     * 
     * \param transaction - transaction     
     */
    virtual task pre_tx(ref Transaction transaction, string inst);

    endtask
    
    // -- Post_tx -------------------------------------------------------------
    //! Post_tx 
    /*!
     * Function is called after transaction is sended. It adds transaction into
     * correct transaction table - depends on witch driver sends transaction               
     * 
     * \param transaction - transaction 
     * \param inst - driver identifier         
     */
    
    virtual task post_tx(Transaction transaction, string inst);
       FrameLinkTransaction flTrans;
       XgmiiTransaction     xgmiiTrans;

       $cast(flTrans, transaction);

       // If bit 0 in FrameLink footer is 0, frame is discarded
       if (flTrans.packetCount == 2 && flTrans.data[1][0][0] == 0)
         return;

       xgmiiTrans = new;
       // Copy data
       if (flTrans.data[0].size < 60)
         xgmiiTrans.data = new[60](flTrans.data[0]);
       else
         xgmiiTrans.data = new[flTrans.data[0].size](flTrans.data[0]);

       // Set MAC address
       if (flTrans.packetCount == 2 && flTrans.data[1][0][1] == 1)
         for (int i = 0; i < 6; i++)
           xgmiiTrans.data[6+i] = macAddress[i];

       // Compute CRC
       xgmiiTrans.post_randomize();

       $cast(transaction, xgmiiTrans);
       sc_table.add(transaction);
    endtask
  
    // -- Set MAC Address -----------------------------------------------------
    //! Set MAC Address
    /*!
     * Sets MAC address that is inserted into XGMII frame
     * 
     * \param macAddress - MAC address
     */
    function void setMacAddress(logic[47:0] macAddress);
      for (int i = 0; i < 6; i++)
        for (int j = 0; j < 8; j++)
          this.macAddress[i][j] = macAddress[i*8+j];
    endfunction

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- XGMII Monitor Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief XGMII Monitor Callbacks
   * 
   * This class is responsible removing transaction from transaction table.
   *    
   * \param behav - TransactionTable behavior                
   */
  
  class ScoreboardMonitorCbs #(int behav=TR_TABLE_FIRST_ONLY)
                                                   extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Scoreboard identification
    string inst;
    //! Transaction Table
    TransactionTable #(behav) sc_table;
    
    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * \param sc_table - transaction tables
     * \param inst - scoreboard identification     
     */
    function new (TransactionTable #(behav) sc_table, string inst="");
      this.sc_table = sc_table;
      this.inst     = inst;
    endfunction
    
    // -- Post_rx -------------------------------------------------------------
    //! Post_tx 
    /*!
     * Function is called after transaction is received. It checks correct
     * transaction table for the same transaction. If they match, transaction is
     * removed, otherwise error is reporting.                         
     * 
     * \param transaction - transaction 
     * \param inst - monitor identifier         
     */
     
    virtual task post_rx(Transaction transaction, string inst);
      bit status=0;

      sc_table.remove(transaction, status);
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         transaction.display(); 
         sc_table.display(.inst(this.inst));
         $stop;
      end
    endtask
 
  endclass : ScoreboardMonitorCbs


  // --------------------------------------------------------------------------
  // -- XGMII OBUF Scoreboard
  // -------------------------------------------------------------------------- 
  /*!
   * \brief XGMII OBUF Scoreboard
   * 
   * This class is responsible for creating Tranaction table and monitor and 
   * driver callback classes. It also prints Transaction table.   
   *    
   * \param behav - TransactionTable behavior                
   */
  class XgmiiObufScoreboard #(int behav = TR_TABLE_FIRST_ONLY);
    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Scoreboard identification
    string inst;
    
    //! Transaction Table
    TransactionTable     #(behav) scoreTable;
    //! Monitor callback
    ScoreboardMonitorCbs #(behav) monitorCbs;
    //! Driver callback
    ScoreboardDriverCbs  #(behav) driverCbs;

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
    
      this.scoreTable = new; 

      this.monitorCbs = new(scoreTable, inst);
      this.driverCbs  = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    //! Display 
    /*!
     * It prints Transaction Table
     * 
     */
    task display();
      scoreTable.display(.inst(inst));
    endtask
  
    // -- Set MAC Address -----------------------------------------------------
    //! Set MAC Address
    /*!
     * Sets MAC address that is inserted into XGMII frame
     * 
     */
    function void setMacAddress(logic[47:0] macAddress);
      driverCbs.setMacAddress(macAddress);
    endfunction

  endclass : XgmiiObufScoreboard

