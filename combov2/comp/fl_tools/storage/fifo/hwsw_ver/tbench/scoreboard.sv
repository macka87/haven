/* *****************************************************************************
 * Project Name: FIFO Functional Verification 
 * File Name:    scoreboard.sv
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011         
 * ************************************************************************** */ 

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
    TransactionTable #(0) sc_table; 

   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates driver callback object 
    *      
    * \param sc_table - transaction tables
    */
    function new (TransactionTable #(0) sc_table);
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
      sc_table.add(transaction);
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
    TransactionTable #(0) sc_table;
    
   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates callback object 
    *      
    * \param sc_table - transaction tables
    * \param inst - scoreboard identification     
    */
    function new (TransactionTable #(0) sc_table);
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
      bit status=0;
      
      // Gets number of transaction table from ID number
      sc_table.remove(transaction, status);
            
      if (status==0)begin
         $write("STATUS==0\n");
         $write("Unknown transaction received from monitor %d\n", inst);
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         transaction.display(); 
         sc_table.display("scoreboard");
         $stop;
      end;
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
    TransactionTable #(0) scoreTable;
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
      scoreTable.display();
    endtask
 endclass : FIFOScoreboard   

