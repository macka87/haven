/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
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
  
 class ScoreboardInputCbs #(int pDataWidth = 64, int pChannels=2, 
                            int behav=TR_TABLE_FIRST_ONLY)
       extends InputCbs;

   /*
    * Public Class Atributes
    */
    
    //! Transaction Table
    TransactionTable #(behav) sc_table[] = new [pChannels]; 

   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates driver callback object 
    *      
    * \param sc_table - transaction tables
    */
    function new (TransactionTable #(behav) sc_table[]);
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
      logic [31:0] size = pDataWidth/8; // Size of transaction in Bytes
      byte unsigned data_new[][];       // New data with NetCOPE header
      string driverLabel;
      int i,j; 
      
      $cast(tr, transaction);
      
      for (i=0; i<tr.frameParts; i++)
        size += tr.data[i].size;
      
      tr.frameParts += 1;               // Adds NetCOPE header as a special part
      data_new    = new[tr.frameParts];
      data_new[0] = new[4];             // NetCOPE header data
      
      for(i=0; i<4; i++)
        for(j=0; j<8; j++)
          data_new[0][i][j] = size[i*8+j];
      
      for(i=1; i<tr.frameParts; i++) begin
        data_new[i] = new[tr.data[i-1].size];
        data_new[i] = tr.data[i-1];
      end
      
      tr.data     = new[tr.frameParts]; 
      tr.data     = data_new;
       
      // Gets number of transaction table from ID number
      $cast(transaction, tr);
      sc_table[id].add(transaction);
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
  
 class ScoreboardOutputCbs #(int pChannels=2, int behav=TR_TABLE_FIRST_ONLY)
       extends OutputCbs;
    
   /*
    * Public Class Atributes
    */
    
    //! Scoreboard identification
    string inst;
    //! Transaction Table
    TransactionTable #(behav) sc_table[] = new[pChannels];
    
   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates callback object 
    *      
    * \param sc_table - transaction tables
    * \param inst - scoreboard identification     
    */
    function new (TransactionTable #(behav) sc_table[], string inst="");
      this.sc_table = sc_table;
      this.inst     = inst;
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
      string monitorLabel;
      string tableLabel;
      int i;
       
      // Gets number of transaction table from ID number
      sc_table[id].remove(transaction, status);
            
      if (status==0)begin
         $write("STATUS==0\n");
         $write("Unknown transaction received from monitor %d\n", inst);
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         transaction.display(); 
         sc_table[id].display("scoreboard");
         $stop;
      end;
    endtask : post_tr 
 endclass : ScoreboardOutputCbs

/*!
 * \brief NetCOPE Adder Scoreboard
 * 
 * This class is responsible for creating Tranaction table and monitor and 
 * driver callback classes. It also prints Transaction table.   
 *    
 * \param pChannels - count of channels
 * \param behav - TransactionTable behavior                
 */
  class NetCOPEAdderScoreboard #(int pDataWidth = 64, int pChannels=2, 
                                 int behav=TR_TABLE_FIRST_ONLY);
   /*
    * Public Class Atributes
    */
    string inst;  //! Scoreboard identification
    
    //! Transaction Table
    TransactionTable #(behav) scoreTable[] = new[pChannels];
    //! Input callback
    ScoreboardInputCbs  #(pDataWidth, pChannels, behav) inputCbs;
    //! Output callback
    ScoreboardOutputCbs #(pChannels, behav) outputCbs;
    
   /*! 
    * Constructor
    * It creates monitor and driver callbacks and Transaction Table for each 
    * flow.
    * 
    * \param inst - scoreboard identification
    */
    function new (string inst="");
      this.inst = inst;
    
      for(int i=0;i<pChannels;i++) 
        this.scoreTable[i]= new; 

      this.inputCbs  = new(scoreTable);
      this.outputCbs = new(scoreTable, inst);
    endfunction

   /*!
    * Display
    *     
    * Prints Transaction Table
    * 
    */
    task display();
      for (int i=0; i<pChannels; i++) begin
        string tableLabel;
        $swrite(tableLabel, "%s %0d", inst, i);
        scoreTable[i].display(.inst(tableLabel));
      end  
    endtask
 endclass : NetCOPEAdderScoreboard   

