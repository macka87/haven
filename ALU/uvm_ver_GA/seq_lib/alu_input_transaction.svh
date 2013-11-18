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
   
   logic rst;  // control signals
   
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
   constraint c_movi { 
     movi inside {[0:2]};
   }    
  
  /*!
   * Methods
   */ 
  
   // Standard UVM methods
   extern function new(string name = "AluInputTransaction");
   extern function void print(string name);
   extern function void do_copy(uvm_object rhs);
   extern function void fwrite(int fileDescr);
  
 endclass: AluInputTransaction
 
 
 
/*! 
 * Constructor - creates AluInputTransaction object  
 */
 function AluInputTransaction::new(string name = "AluInputTransaction");
   super.new(name);
 endfunction: new



/*! 
 * Implementation of the do_copy() virtual function.
 */
 function void AluInputTransaction::do_copy(uvm_object rhs);
   AluInputTransaction alu_trans;
   
   if(!$cast(alu_trans, rhs)) begin
     uvm_report_error("do_copy:", "$cast failed!");
     return;
   end
   
   super.do_copy(rhs);
   
   rst     = alu_trans.rst;
   act     = alu_trans.act; 
   op      = alu_trans.op;
   movi    = alu_trans.movi;                
   reg_a   = alu_trans.reg_a;    
   reg_b   = alu_trans.reg_b;    
   mem     = alu_trans.mem;      
   imm     = alu_trans.imm;      
   btDelay = alu_trans.btDelay;                   
 endfunction: do_copy  
 


/*! 
 * Print - displays ALU Input Transaction content  
 */    
 function void AluInputTransaction::print(string name);
 
   if (name != "") begin
     $write("---------------------------------------------------------\n");
     $write("-- %s\n",name);
     $write("---------------------------------------------------------\n");
   end
      
   $write("RST: %b\n", rst);
   $write("ACT: %b\n", act);
   $write("OP: ");
   
   priority case (op) 
     4'b0000 : $write("ADD\n");
     4'b0001 : $write("SUB\n");
     4'b0010 : $write("MULT\n");
     4'b0011 : $write("SHIFT RIGHT\n");
     4'b0100 : $write("SHIFT LEFT\n");
     4'b0101 : $write("ROTATE RIGHT\n");
     4'b0110 : $write("ROTATE LEFT\n");
     4'b0111 : $write("NOT\n");
     4'b1000 : $write("AND\n");
     4'b1001 : $write("OR\n");
     4'b1010 : $write("XOR\n");
     4'b1011 : $write("NAND\n");
     4'b1100 : $write("NOR\n");
     4'b1101 : $write("XNOR\n");
     4'b1110 : $write("INC\n");
     4'b1111 : $write("DEC\n");
   endcase
   
   $write("\n");  
   
   priority case (movi) 
     2'b00 : $write("MOVI: REGISTER B\n");
     2'b01 : $write("MOVI: MEMORY OPERAND\n");
     2'b10 : $write("MOVI: IMMEDIATE OPERAND\n");
     2'b11 : $write("MOVI: UNKNOWN VALUE\n");
   endcase
   
   $write("REG_A: %b\n", reg_a);      
   $write("REG_B: %b\n", reg_b);  
   $write("MEM: %b\n", mem); 
   $write("IMM: %b\n", imm);
   $write("\n");
 endfunction: print
 
 

/*! 
 * Write to file  
 */ 
 function void AluInputTransaction::fwrite(int fileDescr);
   $fwrite(fileDescr, "%b %b %b %b %b %b %b %b\n", 1'b0, act, op, movi, reg_a, reg_b, mem, imm);
 endfunction: fwrite