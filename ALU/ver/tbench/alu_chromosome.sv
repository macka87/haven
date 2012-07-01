/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    ALU Genetic Algorithm Chromosome Class
 * Description: 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         23.6.2012 
 * ************************************************************************** */

   class ALUChromosome extends Chromosome;
  
   /*
    * Public Class Atributes
    */
    
    //! Interface signals weights (every range or signal value has a weight)
    rand byte unsigned operandA_ranges;        // num. of ranges for opA
    rand byte unsigned operandB_ranges;        // num. of ranges for opB
    rand byte unsigned operandMEM_ranges;      // num. of ranges for opMEM
    rand byte unsigned operandIMM_ranges;      // num. of ranges for opIMM
    rand byte unsigned delay_ranges;           // num. of ranges for delays
    byte unsigned movi_values            = 3;  // num. of values for MOVI
    byte unsigned operation_values       = 16; // num. of values for OPERATION
    
    //! Constants for generation (number of ranges for some interface signals)
    byte unsigned delay_rangesMin        = 1;         
    byte unsigned delay_rangesMax        = 4;    
    byte unsigned operandA_rangesMin     = 1;
    byte unsigned operandA_rangesMax     = 8;
    byte unsigned operandB_rangesMin     = 1;
    byte unsigned operandB_rangesMax     = 8;
    byte unsigned operandMEM_rangesMin   = 1;
    byte unsigned operandMEM_rangesMax   = 8;
    byte unsigned operandIMM_rangesMin   = 1;
    byte unsigned operandIMM_rangesMax   = 8;
    
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

   /*
    * Public Class Methods
    */
    
   /*!
    * Constructor
    * Creates a new object and allocate memory for chromosome array according 
    * to chromosomeLength parameter.
    */
    function new(int estimatedTime = 0);
      // structure of chromozome
      this.length = operandA_rangesMax + operandB_rangesMax + 
                    operandMEM_rangesMax + operandIMM_rangesMax + 
                    delay_rangesMax + movi_values + operation_values;
    endfunction : new 
    
   /*!
    * Function displays the current value of the transaction or data described
    * by this instance in a human-readable format on the standard output.
    *
    * \param prefix - transaction type
    */
    virtual function void display(string prefix = "");
      int offset = 0;
      
      if (prefix != "")
       begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
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
    endfunction : display
 
   /*!
    * Copies the current value of the object instance to the specified object
    * instance. Returns a reference to the target instance.
    * 
    * \param to - original chromosome        
    */
    virtual function Chromosome copy(Chromosome to = null);
      ALUChromosome chrom;
      if (to == null)
        chrom = new();
      else 
        $cast(chrom, to);
      
      chrom.length           = length; 
                                                     
      chrom.chromosome_parts = 7;
      
      chrom.fitness         = fitness;
      chrom.relativeFitness = relativeFitness;
      chrom.chromosome      = new[length];
      
      for (int i=0; i<chrom.length; i++) 
        chrom.chromosome[i] = chromosome[i];
      
      chrom.operandA_ranges   = operandA_ranges;
      chrom.operandB_ranges   = operandB_ranges;
      chrom.operandMEM_ranges = operandMEM_ranges;
      chrom.operandIMM_ranges = operandIMM_ranges;
      chrom.delay_ranges      = delay_ranges;
      chrom.movi_values       = movi_values;
      chrom.operation_values  = operation_values;
      
      chrom.fitness           = fitness;
      
      return chrom;  
    endfunction: copy

   /*!
    * Saves chromosome to file
    */
    virtual function void save(string filename);
      integer file = $fopen(filename, "w");

      foreach (chromosome[i])
        $fwrite(file, "%0d ", chromosome[i]);

      $fclose(file);
    endfunction : save
    
   /*
    * Loads chromosome from file
    */
    virtual function void load(string filename);
      integer file = $fopen(filename, "r");

      foreach (chromosome[i])
        $fscanf(file, "%0d ", chromosome[i]);

      $fclose(file);
    endfunction : load
  
   /*
    * Evaluates the current value of the object instance according to the specific 
    * fitness function.
    */
    function void evaluate(int coveredBins);
      fitness = coveredBins;
      $write("FITNESS: %d\n", fitness);
    endfunction : evaluate
    
   /*
    * Mutates the current value of the object instance.
    */
    virtual function Chromosome mutate(int unsigned maxMutations);  
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
    
   /*
    * Crossovers the current value of the object instance with the specified 
    * object instance.
    */
    virtual function Chromosome crossover(Chromosome chrom = null); 
      ALUChromosome aluChr;
      
      // temporary chromosome
      byte unsigned tmpRange;
      byte unsigned tmpChrom[] = new[chrom.length];
      
      // Position of crossover
      int pos = $urandom_range(chromosome_parts-1);
      
      // | MOVI w. | OP_A w. | OP_B w. | OP_MEM w. | OP_IMM w. | OP w. | DELAY w. |
      $cast(aluChr, chrom);
      tmpChrom = aluChr.chromosome;
            
      // compare the sizes of exchanging parts
      priority case(pos)
        // movi part = 3
        0 :  begin
               for (int i=0; i<3; i++) begin
                 aluChr.chromosome[i] = this.chromosome[i];
                 this.chromosome[i]  = tmpChrom[i];
               end  
             end  
        // reg A part = max 8 
        1 :  begin
               tmpRange = aluChr.operandA_ranges;
               aluChr.operandA_ranges = this.operandA_ranges;
               this.operandA_ranges  = tmpRange;
               
               for (int i=3; i<11; i++) begin
                 aluChr.chromosome[i] = this.chromosome[i];
                 this.chromosome[i]  = tmpChrom[i];
               end  
             end
        // reg B part 
        2 :  begin
               tmpRange = aluChr.operandB_ranges;
               aluChr.operandB_ranges   = this.operandB_ranges;
               this.operandB_ranges    = tmpRange;
               
               for (int i=11; i<19; i++) begin
                 aluChr.chromosome[i] = this.chromosome[i];
                 this.chromosome[i]  = tmpChrom[i];
               end  
             end
        // MEM part 
        3 :  begin
               tmpRange = aluChr.operandMEM_ranges;
               aluChr.operandMEM_ranges = this.operandMEM_ranges;
               this.operandMEM_ranges  = tmpRange;
               
               for (int i=19; i<27; i++) begin
                 aluChr.chromosome[i] = this.chromosome[i];
                 this.chromosome[i]  = tmpChrom[i];
               end
             end
        // IMM part 
        4 :  begin
               tmpRange = aluChr.operandIMM_ranges;
               aluChr.operandIMM_ranges = this.operandIMM_ranges;
               this.operandIMM_ranges  = tmpRange;
               
               for (int i=27; i<35; i++) begin
                 aluChr.chromosome[i] = this.chromosome[i];
                 this.chromosome[i]  = tmpChrom[i];
               end
             end
        // OP part 
        5 :  begin
               for (int i=35; i<51; i++) begin
                 aluChr.chromosome[i] = this.chromosome[i];
                 this.chromosome[i]  = tmpChrom[i];
               end  
             end
        // DELAY part 
        6 :  begin
               tmpRange = aluChr.delay_ranges;
               aluChr.delay_ranges      = this.delay_ranges;
               this.delay_ranges       = tmpRange;
               
               for (int i=51; i<55; i++) begin
                 aluChr.chromosome[i] = this.chromosome[i];
                 this.chromosome[i]  = tmpChrom[i];
               end
             end
      endcase  
      
      $cast(chrom, aluChr);   
      return chrom;
    endfunction : crossover;
    
  endclass : ALUChromosome
  
