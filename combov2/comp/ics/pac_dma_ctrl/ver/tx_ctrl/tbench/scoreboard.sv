/* \file scoreboard.sv
 * \brief Scoreboard
 * \author Marek Santa <xsanta06@stud.fit.vutbr.cz> 
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

import sv_common_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief Frame Link Driver Callbacks
   * 
   * This class is responsible adding transaction into transaction table and 
   * offers possibility to modify transaction.  
   *    
   * \param pFlows - count of flows
   * \param behav - TransactionTable behavior                
   */
  
  class ScoreboardDriverCbs #(int pFlows=2, int behav=1) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Transaction Table
    TransactionTable #(behav) sc_table[] = new [pFlows];

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * \param sc_table - transaction tables
     */
    function new (TransactionTable #(behav) sc_table[]);
      this.sc_table = sc_table;
    endfunction
    
    // -- Pre_tx --------------------------------------------------------------
    //! Pre_tx 
    /*!
     * Function is called before transaction is sended.
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
       // Gets number of transaction table from instance name
       int i;
       
       for(i=0; i< pFlows; i++) begin
         string driverLabel;
         $swrite(driverLabel, "Driver %0d", i);
         if (driverLabel == inst) break;
       end  
       
       sc_table[i].add(transaction);
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief Frame Link Monitor Callbacks
   * 
   * This class is responsible removing transaction from transaction table.
   *    
   * \param pFlows - count of flows
   * \param behav - TransactionTable behavior                
   */
  
  class ScoreboardMonitorCbs #(int pFlows=2, int behav=1) extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Scoreboard identification
    string inst;
    //! Transaction Table
    TransactionTable #(behav) sc_table[] = new[pFlows];
    
    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * \param sc_table - transaction tables
     * \param inst - scoreboard identification     
     */
    function new (TransactionTable #(behav) sc_table[], string inst="");
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
      // Gets number of transaction table from instance name
      int i;
      string tableLabel;
         
      for(i=0; i< pFlows; i++) begin
        string monitorLabel;
        $swrite(monitorLabel, "Monitor %0d", i);
        if (monitorLabel == inst) break;
      end  
      
      $swrite(tableLabel, "%s %0d", this.inst, i);

      sc_table[i].remove(transaction, status);
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         transaction.display(); 
         sc_table[i].display(.inst(tableLabel));
         $stop;
       end;
    endtask

 
  endclass : ScoreboardMonitorCbs


  // --------------------------------------------------------------------------
  // -- Scoreboard
  // -------------------------------------------------------------------------- 
  /*!
   * \brief Scoreboard
   * 
   * This class is responsible for creating Tranaction table and monitor and 
   * driver callback classes. It also prints Transaction table.   
   *    
   * \param pFLows - count of flows
   * \param behav - TransactionTable behavior                
   */
  class Scoreboard #(int pFlows=2, int behav=1);
    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Scoreboard identification
    string inst;
    
    //! Transaction Table
    TransactionTable     #(behav)         scoreTable[] = new[pFlows];
    //! Monitor callback
    ScoreboardMonitorCbs #(pFlows, behav) monitorCbs;
    //! Driver callback
    ScoreboardDriverCbs  #(pFlows, behav) driverCbs;

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
    
      for(int i=0;i<pFlows;i++) 
        this.scoreTable[i]= new; 

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
      for (int i=0; i<pFlows; i++) begin
        string tableLabel;
        $swrite(tableLabel, "%s %0d", inst, i);
        scoreTable[i].display(.inst(tableLabel));
      end  
    endtask
  
  endclass : Scoreboard

