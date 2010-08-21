/* \file scoreboard.sv
 * \brief Scoreboard
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
 *
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import test_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- Request Fifo Driver Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief Request Fifo Driver Callbacks
   * 
   * This class is responsible adding transaction into transaction table and 
   * offers possibility to modify transaction.  
   *    
   * \param pFlows - count of flows
   */
  
  class ReqFifoDriverCbs #(int pFlows=2) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Queue for descriptor addresses
    int unsigned descAddrQue[pFlows][$];

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     */
    function new ();
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
      // Parse transaction and add descriptor addresses into queue
      SumRfTransaction tr;

      $cast(tr, transaction);

      for (int i=0; i<tr.blockLength; i++) begin
        descAddrQue[tr.rfRAddr].push_back(tr.descStartAddr+16*i);
//        $write("Added descAddr: %0x\n",tr.descStartAddr+16*i);
      end  
    endtask

   endclass : ReqFifoDriverCbs

 
  // --------------------------------------------------------------------------
  // -- SUM Driver Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief Status Update Manager Driver Callbacks
   * 
   * This class is responsible adding transaction into transaction table and 
   * offers possibility to modify transaction.  
   *    
   * \param pFlows - count of flows
   * \param behav - TransactionTable behavior                
   */
  
  class ScoreboardDriverCbs #(int pFlows=2, int behav=0)extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Transaction Table
    TransactionTable #(behav) sc_table;
    ReqFifoDriverCbs #(pFlows) reqFifo;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * \param sc_table - transaction tables
     */
    function new (TransactionTable #(behav) sc_table, 
                  ReqFifoDriverCbs #(pFlows) reqFifo);
      this.sc_table = sc_table;
      this.reqFifo  = reqFifo;
    endfunction
    
    // -- Pre_tx --------------------------------------------------------------
    //! Pre_tx 
    /*!
     * Function is called before transaction is sended.
     */
    virtual task pre_tx(ref Transaction transaction, string inst);
      StatusUpdateTransaction suTrans;

      $cast(suTrans, transaction);

      // Wait for available descriptor addresses
      while(reqFifo.descAddrQue[suTrans.address].size==0)
        #(CLK_PERIOD);
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
      Transaction to;
      StatusUpdateTransaction suTrans;
      SumTransaction sumTr = new;

      $cast(suTrans, transaction);

      sumTr.descAddr = reqFifo.descAddrQue[suTrans.address].pop_front();
      sumTr.intFlag  = suTrans.intFlag;
      sumTr.lfFlag   = suTrans.lfFlag;
      sumTr.length   = suTrans.length;

      to = sumTr;

      sc_table.add(to);
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- SUM Monitor Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief Status Update Manager Monitor Callbacks
   * 
   * This class is responsible removing transaction from transaction table.
   *    
   * \param behav - TransactionTable behavior                
   */
  
  class ScoreboardMonitorCbs #(int behav=0) extends MonitorCbs;
    
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
     */
    function new (TransactionTable #(behav) sc_table);
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
         sc_table.display();
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
  class Scoreboard #(int pFlows=2, int behav=0);
    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Scoreboard identification
    string inst;
    
    //! Transaction Table
    TransactionTable     #(behav)         scoreTable;
    //! Monitor callback
    ScoreboardMonitorCbs #(behav)         monitorCbs;
    //! Driver callback
    ReqFifoDriverCbs     #(pFlows)        rfDriverCbs;
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
    
      this.scoreTable = new; 

      this.monitorCbs = new(scoreTable);
      this.rfDriverCbs  = new();
      this.driverCbs  = new(scoreTable, rfDriverCbs);
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
  
  endclass : Scoreboard

