/* *****************************************************************************
 * Project Name: FIFO Functional Verification 
 * File Name:    scoreboard.sv
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011         
 * ************************************************************************** */ 

import dpi_tr_table_pkg::*;
import test_pkg::*;

typedef TransactionTable#(1) TransactionTableType;

/*!
 * \brief FrameLink Input Callbacks 
 *
 * This class is responsible adding transaction into transaction table and 
 * offers possibility to modify transaction.  
 *    
 * \param pChannels - count of channels
 * \param behav - TransactionTable behavior                
 */
  
 class ScoreboardInputCbs extends InputCbs;

   /*
    * Public Class Atributes
    */
    
    //! Transaction Table
    TransactionTableType sc_table; 

   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates driver callback object 
    *      
    * \param sc_table - transaction tables
    */
    function new (TransactionTableType sc_table);
      this.sc_table = sc_table;
    endfunction
    
   /*! 
    * Transaction preprocessing
    *     
    * Function is called before transaction is sended to DUT.         
    * 
    * \param transaction - transaction     
    */
    virtual task pre_tr(ref Transaction transaction, byte id);
      // Transaction is not modified before sending to DUT
    endtask : pre_tr
    
   /*! 
    * Transaction postprocessing
    *
    * Function is called before transaction is sended to scoreboard. It adds
    * NetCOPE adder before the first frame of FrameLink transaction. After
    * modification stores transaction into correct transaction table. It
    * depends on which driver is sending this transaction.              
    * 
    * \param transaction - transaction 
    * \param inst        - driver identification         
    */
    
    virtual task post_tr(Transaction transaction, byte id);
      FrameLinkTransaction tr; 
      
      $cast(tr, transaction);
      
      if (FRAMEWORK == 0)
        sc_table.add(tr);
      if (FRAMEWORK == 1) 
        c_addToTable(tr.data[0]);
    endtask : post_tr
 endclass : ScoreboardInputCbs


/*!
 * \brief FrameLink Output Callbacks 
 * 
 * This class is responsible removing transaction from transaction table.
 *    
 * \param pChannels - count of channels
 * \param behav - TransactionTable behavior                
 */
  
 class ScoreboardOutputCbs extends OutputCbs;
    
   /*
    * Public Class Atributes
    */
    
    //! Scoreboard identification
    string inst;
    //! Transaction Table
    TransactionTableType sc_table;
    
   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates callback object 
    *      
    * \param sc_table - transaction tables
    * \param inst - scoreboard identification     
    */
    function new (TransactionTableType sc_table);
      this.sc_table = sc_table;
    endfunction
    
   /*! 
    * Transaction postprocessing
    *
    * Function is called after transaction is received. It checks correct
    * transaction table for the same transaction. If they match, transaction is
    * removed, otherwise error is reporting.                         
    * 
    * \param transaction - transaction 
    * \param inst - monitor identifier         
    */
    virtual task post_tr(Transaction transaction, byte id);
      FrameLinkTransaction tr;
      bit status=0;
      int res;
      
      if (FRAMEWORK == 0)begin
        sc_table.remove(transaction, status);
       
        if (status==0)begin
          $write("STATUS==0\n");
          $write("Unknown transaction received from monitor %d\n", inst);
          $timeformat(-9, 3, " ns", 8);
          $write("Time: %t\n", $time);
          transaction.display(); 
          sc_table.display("scoreboard");
          $fatal();
        end;
      end  

      if (FRAMEWORK == 1) begin 
        $cast(tr, transaction);
        res = c_removeFromTable(tr.data[0]);
        if (res==1)begin 
          $write("Unknown transaction received from output controller!\n");
          transaction.display();
          c_displayTable();
          $fatal(); 
        end   
      end
    endtask : post_tr 
 endclass : ScoreboardOutputCbs

/*!
 * \brief FIFO Scoreboard
 * 
 * This class is responsible for creating Tranaction table and monitor and 
 * driver callback classes. It also prints Transaction table.   
 *    
 * \param pChannels - count of channels
 * \param behav - TransactionTable behavior                
 */
  class FIFOScoreboard;
   /*
    * Public Class Atributes
    */
    //! Transaction Table
    TransactionTableType  scoreTable;
    //! Input callback
    ScoreboardInputCbs    inputCbs;
    //! Output callback
    ScoreboardOutputCbs   outputCbs;
    
   /*! 
    * Constructor
    * It creates monitor and driver callbacks and Transaction Table for each 
    * flow.
    * 
    * \param inst - scoreboard identification
    */
    function new ();
      this.scoreTable= new; 
      this.inputCbs  = new(scoreTable);
      this.outputCbs = new(scoreTable);
    endfunction

   /*!
    * Display
    *     
    * Prints Transaction Table
    * 
    */
    task display();
      if (FRAMEWORK == 0)
        scoreTable.display();  
      if (FRAMEWORK == 1)  
        c_displayTable(); 
    endtask

   /*!
    * Display
    *     
    * Prints Transaction Table after assertion Failure
    * 
    */
    function void displayTrans();
      scoreTable.displayState();
    endfunction
 
 endclass : FIFOScoreboard   
