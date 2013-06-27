/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_ga_input_transaction.sv
 * Description:  Definition of GA input vectors.
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2013 
 * ************************************************************************** */ 

/*! 
 * Constructor - creates AluGAInputTransaction object  
 */
 function AluGAInputTransaction::new(string name = "AluGAInputTransaction");
   super.new(name);
 endfunction: new
 
 
 
/*! 
 * Implementation of the do_copy() virtual function.
 */
 function void AluGAInputTransaction::do_copy(uvm_object rhs);
   AluGAInputTransaction alu_trans;
   
   if(!$cast(alu_trans, rhs)) begin
     uvm_report_error("do_copy:", "$cast failed!");
     return;
   end
   
   super.do_copy(rhs);
   
   reg_a = alu_trans.reg_a;
   reg_b = alu_trans.reg_b;
   mem   = alu_trans.mem;
   imm   = alu_trans.imm;
   op    = alu_trans.op;
   movi  = alu_trans.movi;
   
 endfunction: do_copy  

