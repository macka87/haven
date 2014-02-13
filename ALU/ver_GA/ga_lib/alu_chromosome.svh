/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    alu_chromosome.svh
 * Description:  ALU Chromosome Class
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         13.2.2014 
 * ************************************************************************** */

/*!
 * \brief Chromosome
 * 
 * This class defines the structure of the chromosome and basic operations 
 * performed with chromosomes.
 */

 class AluChromosome;
  
  /*! 
   * Data Members      
   */  
   
   int          length;             // length of chromosome
   int          chromosome_parts;   // uniform parts of chromosome
   int unsigned fitness;            // fitness function
   real         relativeFitness;    // relative fitness function
   real         roulette_part;      // occupied part of roulette in case of Roulette selection
   rand byte unsigned chromosome[]; // chromosome
   
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

   extern function AluChromosome clone(AluChromosome rhs = null);
   extern function void print(int num, bit full_print);
   extern function AluChromosome crossover(AluChromosome chrom = null);
   extern function AluChromosome mutate(int unsigned maxMutations); 
   extern function void setRelativeFitness(int unsigned popFitness);
 endclass: AluChromosome
 
 

/*! 
 * Implementation of the do_copy() virtual function.
 */
 function AluChromosome AluChromosome::clone(AluChromosome rhs = null);
   AluChromosome alu_chr;
   
   if (rhs == null)
     alu_chr = new();
   else 
     $cast(alu_chr, rhs);
   
   alu_chr.operandA_ranges = operandA_ranges;
   alu_chr.operandB_ranges = operandB_ranges;  
   alu_chr.operandMEM_ranges = operandMEM_ranges;
   alu_chr.operandIMM_ranges = operandIMM_ranges;  
   alu_chr.delay_ranges = delay_ranges;  
   alu_chr.movi_values = movi_values;  
   alu_chr.operation_values = operation_values;
    
   alu_chr.delay_rangesMin = delay_rangesMin;            
   alu_chr.delay_rangesMax = delay_rangesMax;   
   alu_chr.operandA_rangesMin = operandA_rangesMin;  
   alu_chr.operandA_rangesMax = operandA_rangesMax;   
   alu_chr.operandB_rangesMin = operandB_rangesMin;  
   alu_chr.operandB_rangesMax = operandB_rangesMax;  
   alu_chr.operandMEM_rangesMin = operandMEM_rangesMin;  
   alu_chr.operandMEM_rangesMax = operandMEM_rangesMax;  
   alu_chr.operandIMM_rangesMin = operandIMM_rangesMin;  
   alu_chr.operandIMM_rangesMax = operandIMM_rangesMax; 
   
   alu_chr.length = length;
   alu_chr.chromosome_parts = 7;
   alu_chr.fitness = fitness; 
   alu_chr.relativeFitness = relativeFitness;
   alu_chr.chromosome = new[length];
   for (int i=0; i<length; i++) 
     alu_chr.chromosome[i] = chromosome[i];
     
   return alu_chr;  
 endfunction: clone  
 


/*! 
 * Print - displays Chromosome content  
 */    
 function void AluChromosome::print(int num, bit full_print);
 
   int offset = 0;
   
   if (!full_print) 
     $write("\n --- ALU CHROMOSOME num: %d --- \n", num);
      
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
 * Computes relative fitness: USED
 */
 function void AluChromosome::setRelativeFitness(int unsigned popFitness);
   relativeFitness = real'(fitness)/real'(popFitness);
 endfunction: setRelativeFitness
 
 
 
/*!
 * Crossovers the current value of the object instance with the specified 
 * object instance.
 */
 function AluChromosome AluChromosome::crossover(AluChromosome chrom = null);
   // temporary chromosome
   byte unsigned tmpRange;
   
   byte unsigned tmpChrom[] = new[length];
   
   // Position of crossover
   int pos = $urandom_range(chromosome_parts-1);
   $write("pos: %d\n", pos);
   
   // | MOVI w. | OP_A w. | OP_B w. | OP_MEM w. | OP_IMM w. | OP w. | DELAY w. |
   tmpChrom = chrom.chromosome;  
            
   // compare the sizes of exchanging parts
   priority case(pos)
     // movi part = 3
     0 :  begin
            for (int i=0; i<3; i++) begin
              chrom.chromosome[i] = this.chromosome[i];
              this.chromosome[i]  = tmpChrom[i];
            end  
          end  
     // reg A part = max 8 
     1 :  begin
            tmpRange = chrom.operandA_ranges;
            chrom.operandA_ranges = this.operandA_ranges;
            this.operandA_ranges  = tmpRange;
               
            for (int i=3; i<11; i++) begin
              chrom.chromosome[i] = this.chromosome[i];
              this.chromosome[i]  = tmpChrom[i];
            end  
          end
     // reg B part 
     2 :  begin
            tmpRange = chrom.operandB_ranges;
            chrom.operandB_ranges   = this.operandB_ranges;
            this.operandB_ranges    = tmpRange;
               
            for (int i=11; i<19; i++) begin
              chrom.chromosome[i] = this.chromosome[i];
              this.chromosome[i]  = tmpChrom[i];
            end  
          end
     // MEM part 
     3 :  begin
            tmpRange = chrom.operandMEM_ranges;
            chrom.operandMEM_ranges = this.operandMEM_ranges;
            this.operandMEM_ranges  = tmpRange;
               
            for (int i=19; i<27; i++) begin
              chrom.chromosome[i] = this.chromosome[i];
              this.chromosome[i]  = tmpChrom[i];
            end
          end
     // IMM part 
     4 :  begin
            tmpRange = chrom.operandIMM_ranges;
            chrom.operandIMM_ranges = this.operandIMM_ranges;
            this.operandIMM_ranges  = tmpRange;
               
            for (int i=27; i<35; i++) begin
              chrom.chromosome[i] = this.chromosome[i];
              this.chromosome[i]  = tmpChrom[i];
            end
          end
     // OP part 
     5 :  begin
            for (int i=35; i<51; i++) begin
              chrom.chromosome[i] = this.chromosome[i];
              this.chromosome[i]  = tmpChrom[i];
            end  
          end
     // DELAY part 
     6 :  begin
            tmpRange = chrom.delay_ranges;
            chrom.delay_ranges      = this.delay_ranges;
            this.delay_ranges       = tmpRange;
               
            for (int i=51; i<55; i++) begin
              chrom.chromosome[i] = this.chromosome[i];
              this.chromosome[i]  = tmpChrom[i];
            end
          end
   endcase       
      
   return chrom;  
 endfunction: crossover
 
 
 
/*
 * Mutates the current value of the object instance.
 */
function AluChromosome AluChromosome::mutate(int unsigned maxMutations);  
   // Number of mutations
   int mutationCount = $urandom_range(maxMutations,1);
   // Positon of mutation
   int byte_pos;
   int bit_pos;
   bit old_value;
      
   for (int i=0; i < mutationCount; i++) begin
     byte_pos = $urandom_range(length - 1);
     bit_pos  = $urandom_range(7);
        
     old_value = chromosome[byte_pos][bit_pos];
     chromosome[byte_pos][bit_pos] = !old_value; // bit conversion
   end
      
   return this;
 endfunction : mutate