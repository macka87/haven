/* *****************************************************************************
 * Project Name: ALU Functional Verification 
 * File Name:    scoreboard.sv
 * Description:  self-checking mechanism
 * Author:       Marcela Simkova <isimkova@stud.fit.vutbr.cz> 
 * Date:         26.3.2012         
 * ************************************************************************** */ 

typedef TransactionTable#(1) TransactionTableType;

/*!
 * \brief ALU Input Callbacks 
 *
 * This class is responsible adding transaction into transaction table and 
 * offers possibility to modify transaction.  
 */
  
 class ScoreboardInputCbs #(pDataWidth = 8) extends InputCbs;
   
   /*
    * Public Class Atributes
    */
    
    //! Class Identifier
    string inst;
    
    //! Transaction Table
    TransactionTableType sc_table; 
    
    //! Count of added transactions
    int transCount = 0;

   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates driver callback object 
    *      
    * \param sc_table - transaction tables
    */
    function new (TransactionTableType sc_table, string inst);
      this.inst     = inst;
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
    * Function is called before transaction is sended to scoreboard.   
    * 
    * \param transaction - transaction 
    * \param inst        - driver identification         
    */
    virtual task post_tr(Transaction transaction, byte id);
      ALUInTransaction #(pDataWidth) aluIn;
      ALUOutTransaction #(pDataWidth) aluOut;
      logic [pDataWidth-1:0] operandB;
      logic [pDataWidth*2-1:0] multResult;
      
      $cast(aluIn, transaction);
      //aluIn.display("SC: INPUT TRANSACTION");
            
      aluOut = new();
      
      // selection of operand B
      priority case (aluIn.movi)
          2'b00 : operandB = aluIn.operandB;    // register operand
          2'b01 : operandB = aluIn.operandMEM;  // memory operand
          2'b10 : operandB = aluIn.operandIMM;  // immediate operand
          2'b11 : $error("Unsupported operand type.\n");
          default : begin
                      $error("!!!SCOREBOARD: Unknown operand identifier!!!\n");
                      $finish();
                    end  
      endcase 
      
      // operation execution
      priority case (aluIn.operation)
         // ADD 
         4'b0000 : aluOut.alu_output = aluIn.operandA + operandB;
         // SUB
         4'b0001 : aluOut.alu_output = aluIn.operandA - operandB;
         // MULT
         4'b0010 : begin
                     multResult = aluIn.operandA * operandB;
                     aluOut.alu_output = multResult[pDataWidth-1:0];
                     $cast(transaction, aluOut);    
                     //$write("TRANS. NUMBER: %d\n", transCount);
                     //aluOut.display("SC: ADDED TRANSACTION:");
                     transCount++; 
                     sc_table.add(transaction);
                     // second part 
                     aluOut = new();
                     aluOut.alu_output = multResult[pDataWidth*2-1:pDataWidth];
                   end  
         // SHIFT RIGHT
         4'b0011 : aluOut.alu_output = operandB>>1;
         // SHIFT LEFT
         4'b0100 : aluOut.alu_output = operandB<<1;
         // ROTATE RIGHT
         4'b0101 : begin
                     aluOut.alu_output = operandB>>1;
                     aluOut.alu_output[pDataWidth-1] = operandB[0];
                   end  
         // ROTATE LEFT
         4'b0110 : begin
                     aluOut.alu_output = operandB<<1;
                     aluOut.alu_output[0] = operandB[pDataWidth-1];
                   end  
         // NOT
         4'b0111 : aluOut.alu_output = ~(operandB);
         // AND
         4'b1000 : aluOut.alu_output = aluIn.operandA & operandB;
         // OR
         4'b1001 : aluOut.alu_output = aluIn.operandA | operandB;
         // XOR
         4'b1010 : aluOut.alu_output = aluIn.operandA ^ operandB;
         // NAND
         4'b1011 : aluOut.alu_output = ~(aluIn.operandA & operandB);
         // NOR
         4'b1100 : aluOut.alu_output = ~(aluIn.operandA | operandB);
         // XNOR
         4'b1101 : aluOut.alu_output = aluIn.operandA ~^ operandB;
         // INC
         4'b1110 : aluOut.alu_output = ++operandB;
         // DEC
         4'b1111 : aluOut.alu_output = --operandB;
       endcase
      
      $cast(transaction, aluOut);
      //$write("TRANS. NUMBER: %d\n", transCount);
      //aluOut.display("SC: ADDED TRANSACTION:");
      transCount++; 
      sc_table.add(transaction); 
    endtask : post_tr
 endclass : ScoreboardInputCbs


/*!
 * \brief ALU Output Callbacks 
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
    
    //! Class identification
    string inst;
    //! Transaction Table
    TransactionTableType sc_table;
    //! Count of removed transactions
    int transCount = 0;
    
   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates callback object 
    *      
    * \param sc_table - transaction tables
    * \param inst - scoreboard identification     
    */
    function new (TransactionTableType sc_table, string inst);
      this.inst     = inst;
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
      bit status = 0;
      sc_table.remove(transaction, status);
      //transaction.display("SC: REMOVED TRANSACTION:");
      if (status==0)begin
         $write("Unknown transaction (number: %d) in monitor %d:\n", transCount, id);
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         transaction.display(); 
         sc_table.display(1, this.inst);
         $stop;
       end; 
       transCount++; 
    endtask : post_tr 
 endclass : ScoreboardOutputCbs

/*!
 * \brief ALU Scoreboard
 * 
 * This class is responsible for creating Tranaction table and monitor and 
 * driver callback classes. It also prints Transaction table.   
 *    
 * \param pChannels - count of channels
 * \param behav - TransactionTable behavior                
 */
  class ALUScoreboard #(pDataWidth = 8);
   
   /*
    * Private Class Atributes
    */
    string inst;
   
   /*
    * Public Class Atributes
    */
    //! Transaction Table
    TransactionTableType             scoreTable;
    //! Input callback
    ScoreboardInputCbs #(pDataWidth) inputCbs;
    //! Output callback
    ScoreboardOutputCbs              outputCbs;
    
   /*! 
    * Constructor
    * It creates monitor and driver callbacks and Transaction Table for each 
    * flow.
    * 
    * \param inst - scoreboard identification
    */
    function new (string inst);
      this.inst       = inst;
      this.scoreTable = new; 
      this.inputCbs   = new(scoreTable, inst);
      this.outputCbs  = new(scoreTable, inst);
    endfunction

   /*!
    * Display
    *     
    * Prints Transaction Table
    * 
    */
    task display();
      scoreTable.display(0, this.inst);  
    endtask
 endclass : ALUScoreboard   

