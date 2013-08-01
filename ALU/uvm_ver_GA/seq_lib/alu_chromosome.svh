/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_chromosome.svh
 * Description:  ALU Chromosome Class
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         24.6.2013 
 * ************************************************************************** */

/*!
 * \brief Chromosome
 * 
 * This class defines the structure of the chromosome and basic operations 
 * performed with chromosomes.
 */

 class AluChromosome extends Chromosome;
  
   //! UVM Factory Registration Macro
   `uvm_object_utils(AluChromosome)
   
  /*! 
   * Data Members
   */  
   
   //! Interface signals weights (every range or signal value has a weight)
   rand byte unsigned operandA_ranges;    // num. of ranges for opA
   rand byte unsigned operandB_ranges;    // num. of ranges for opB
   rand byte unsigned operandMEM_ranges;  // num. of ranges for opMEM
   rand byte unsigned operandIMM_ranges;  // num. of ranges for opIMM
   rand byte unsigned delay_ranges;       // num. of ranges for delays
   
   //! Configured items
   byte unsigned movi_values;             // num. of values for MOVI
   byte unsigned operation_values;        // num. of values for OPERATION
    
   //! Constants for generation (number of ranges for some interface signals)
   byte unsigned delay_rangesMin;         
   byte unsigned delay_rangesMax;
   byte unsigned operandA_rangesMin;
   byte unsigned operandA_rangesMax;
   byte unsigned operandB_rangesMin;
   byte unsigned operandB_rangesMax;
   byte unsigned operandMEM_rangesMin;
   byte unsigned operandMEM_rangesMax;
   byte unsigned operandIMM_rangesMin;
   byte unsigned operandIMM_rangesMax;     
   
   //! Constraints for randomized values 
   constraint chromosomeConst {
     chromosome.size == length;
   }  
    
   constraint opA_c {
     operandA_ranges inside {
                     [operandA_rangesMin:operandA_rangesMax]
                     };
   };  
    
   constraint opB_c {
     operandB_ranges inside {
                     [operandB_rangesMin:operandB_rangesMax]
                     };
   };
    
   constraint opMEM_c {
     operandMEM_ranges inside {
                     [operandMEM_rangesMin:operandMEM_rangesMax]
                     };
   };
   
   constraint opIMM_c {
     operandIMM_ranges inside {
                     [operandIMM_rangesMin:operandIMM_rangesMax]
                     };
   };
    
   constraint delay_c {
     delay_ranges inside {
                     [delay_rangesMin:delay_rangesMax]
                     };
   };              

  /*!
   * Methods
   */

   // Standard UVM methods
   extern function new(string name = "AluChromosome");
   extern function void do_copy(uvm_object rhs);
   extern function void print(int num, bit full_print);
      
   // Own UVM methods
   extern function void evaluate(int coveredBins);

 endclass: AluChromosome
 
 
 
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
 function void AluChromosome::print(int num, bit full_print);
 
   int offset = 0;
   
   if (!full_print) begin
     $write("\n\n");
     $write("--------------------------------------------------- \n");
     $write("--- ALU CHROMOSOME num: %d --- \n", num);
     $write("--------------------------------------------------- \n\n\n");
   end
   
   else begin  
     $write("\n\n");
     $write("--------------------------------------------------- \n");
     $write("--- ALU CHROMOSOME num: %d --- \n", num);
     $write("--------------------------------------------------- \n\n\n");
  
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
   end
 endfunction: print



/*! 
 * Evaluate - evaluate coverage of Chromosome   
 */    
 function void AluChromosome::evaluate(int coveredBins);
 endfunction: evaluate