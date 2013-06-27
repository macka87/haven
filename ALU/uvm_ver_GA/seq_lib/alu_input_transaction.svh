/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_input_transaction.svh
 * Description:  UVM Input Transaction Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2013
 * ************************************************************************** */

/*!
 * \brief Input ALU Transaction
 * 
 * This class represents transaction which contains values of input signals for
 * the DUT.
 */
 
 class AluInputTransaction extends uvm_sequence_item;

   //! UVM Factory Registration Macro
   `uvm_object_utils(AluInputTransaction)
   
  /*! 
   * Data Members
   */
   
   // control signals
   logic rst;
   
   // random values of signals
   rand logic act;                       // activation signal
   rand logic [3:0] op;                  // operation
   rand logic [1:0] movi;                // selection signal of operand B
   rand logic [DATA_WIDTH-1:0] reg_a;    // operand A from register
   rand logic [DATA_WIDTH-1:0] reg_b;    // operand B from register
   rand logic [DATA_WIDTH-1:0] mem;      // operand B from memory
   rand logic [DATA_WIDTH-1:0] imm;      // immediate operand B
   rand byte btDelay;                    // between transactions delay

   //! Constraints for randomized values 
   constraint c_movi { movi >= 0; movi < 4; }  
  
  /*!
   * Methods
   */ 
  
   // Standard UVM methods
   extern function new(string name = "AluInputTransaction");
   extern function void print(string name);
      
   // Own UVM methods
   //extern function void fwrite(int fileDescr);
   //extern function void fread(int fileDescr);
  
 endclass: AluInputTransaction
