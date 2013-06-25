/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_chromosome.sv
 * Description:  Genetic Algorithm ALU Chromosome Class.
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         24.6.2013 
 * ************************************************************************** */

/*! 
 * Constructor - creates the ALU Chromosome object  
 */
 function AluChromosome::new(string name = "AluChromosome");
   super.new(name);
 endfunction: new



/*! 
 * Implementation of the do_copy() virtual function.
 */
 function void AluChromosome::do_copy(uvm_object rhs);
   AluChromosome alu_chr;
   
   if(!$cast(alu_chr, rhs)) begin
     uvm_report_error("do_copy:", "$cast failed!");
     return;
   end
   
   super.do_copy(rhs);
   
   operandA_ranges      = alu_chr.operandA_ranges; 
   operandB_ranges      = alu_chr.operandB_ranges;  
   operandMEM_ranges    = alu_chr.operandMEM_ranges;  
   operandIMM_ranges    = alu_chr.operandIMM_ranges;  
   delay_ranges         = alu_chr.delay_ranges;  
   movi_values          = alu_chr.movi_values;  
   operation_values     = alu_chr.operation_values; 
    
   delay_rangesMin      = alu_chr.delay_rangesMin;           
   delay_rangesMax      = alu_chr.delay_rangesMax;  
   operandA_rangesMin   = alu_chr.operandA_rangesMin;  
   operandA_rangesMax   = alu_chr.operandA_rangesMax;  
   operandB_rangesMin   = alu_chr.operandB_rangesMin;  
   operandB_rangesMax   = alu_chr.operandB_rangesMax;  
   operandMEM_rangesMin = alu_chr.operandMEM_rangesMin;  
   operandMEM_rangesMax = alu_chr.operandMEM_rangesMax;  
   operandIMM_rangesMin = alu_chr.operandIMM_rangesMin;  
   operandIMM_rangesMax = alu_chr.operandIMM_rangesMax; 
   
   length               = alu_chr.length;
   chromosome_parts     = 7;
   fitness              = alu_chr.fitness;
   relativeFitness      = alu_chr.relativeFitness;
   chromosome           = new[length];
   for (int i=0; i<length; i++) 
     chromosome[i] = alu_chr.chromosome[i];
   
 endfunction: do_copy  
 


/*! 
 * Print - displays Chromosome content  
 */    
 function void AluChromosome::print(string name);
 
   int offset = 0;
   if (name != "") begin
     $write("---------------------------------------------------------\n");
     $write("-- %s\n", name);
     $write("---------------------------------------------------------\n");
   end
       
   $write("Structure of Chromosome:\n");
              
   $write("| MOVI w. | OP_A w. | OP_B w. | OP_MEM w. | OP_IMM w. | OP w. | DELAY w. |\n");
       
   $write("Chromosome real length: %d\n", this.length);
       
   $write("Number of MOVI values: %d\n", movi_values);
   for (int i=0; i<movi_values; i++) 
       $write("Movi value %d weight: %d\n", i, chromosome[offset++]);
         
   $write("OperandA number of ranges: %d\n", operandA_ranges);
   for (int i=0; i<8; i++) begin
     if (i < operandA_ranges) 
       $write("operandA range %d weight: %d\n", i, chromosome[offset++]);
     else offset++;
   end  
         
   $write("OperandB number of ranges: %d\n", operandB_ranges);
   for (int i=0; i<8; i++) begin
     if (i < operandB_ranges) 
       $write("operandB range %d weight: %d\n", i, chromosome[offset++]);
     else offset++;
   end 
         
   $write("OperandMEM number of ranges: %d\n", operandMEM_ranges);
   for (int i=0; i<8; i++) begin
     if (i < operandMEM_ranges)
       $write("operandMEM range %d weight: %d\n", i, chromosome[offset++]);  
     else offset++;
   end 
       
   $write("OperandIMM number of ranges: %d\n", operandIMM_ranges);
   for (int i=0; i<8; i++) begin
     if (i < operandIMM_ranges)
       $write("operandIMM range %d weight: %d\n", i, chromosome[offset++]);
     else offset++;
   end     
       
   $write("Number of operations: %d\n", operation_values);
   for (int i=0; i<operation_values; i++) 
     $write("Operation value %d weight: %d\n", i, chromosome[offset++]);   
        
   $write("Number of delay ranges: %d\n", delay_ranges);
   for (int i=0; i<8; i++) begin
     if(i<delay_ranges) 
       $write("Delay %d weight: %d\n", i, chromosome[offset++]);    
     else offset++;
   end 
       
   $write("FITNESS: %0d\n", fitness);  
   $write("Relative fitness: %0d\n", relativeFitness);  
   $write("\n");
 
 endfunction: print



/*! 
 * Evaluate - evaluate coverage of Chromosome   
 */    
 function void AluChromosome::evaluate(int coveredBins);
 endfunction: evaluate
   


