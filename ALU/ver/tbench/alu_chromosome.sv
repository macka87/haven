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
    rand byte unsigned operandIMM_ranges;      // num. of ranges for opIMM
    rand byte unsigned operandMEM_ranges;      // num. of ranges for opMEM
    rand byte unsigned delay_ranges;           // num. of ranges for delays
    byte unsigned movi_values            = 3;  // num. of values for MOVI
    byte unsigned operation_values       = 16; // num. of values for OPERATION
    
    //! Constants for generation (number of ranges for some interface signals)
    byte unsigned delay_rangesMin        = 1;         
    byte unsigned delay_rangesMax        = 3;    
    byte unsigned operandA_rangesMin     = 1;
    byte unsigned operandA_rangesMax     = 10;
    byte unsigned operandB_rangesMin     = 1;
    byte unsigned operandB_rangesMax     = 10;
    byte unsigned operandIMM_rangesMin   = 1;
    byte unsigned operandIMM_rangesMax   = 10;
    byte unsigned operandMEM_rangesMin   = 1;
    byte unsigned operandMEM_rangesMax   = 10;
    
    //! Constraint values (constraints for values of ranges)
    byte unsigned delayMin               = 0;   // minimum delay is 0
    byte unsigned delayMax               = 10;  // maximum delay is 10
    
    //! Estimated time of genetic algorithm    
    longint unsigned estimatedTime;
       
    //! Constraints for randomized values 
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
    
    constraint opIMM_c {
      operandIMM_ranges inside {
                      [operandIMM_rangesMin:operandIMM_rangesMax]
                      };
    };
    
    constraint opMEM_c {
      operandMEM_ranges inside {
                      [operandMEM_rangesMin:operandMEM_rangesMax]
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
      this.length        = operandA_ranges + operandB_ranges + 
                           operandIMM_ranges + operandMEM_ranges +
                           delay_ranges + movi_values + operation_values;
      this.estimatedTime = estimatedTime;
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
       
       $write("OperandA number of ranges: %d\n", operandA_ranges);
       //for (int i=0; i<operandA_ranges; i++) 
       //  $write("operandA range %d: %b\n", i, chromosome[offset++]);
       
       $write("OperandB number of ranges: %d\n", operandB_ranges);
       //for (int i=0; i<operandB_ranges; i++) 
       //  $write("operandB range %d: %b\n", i, chromosome[offset++]);
       
       $write("OperandIMM number of ranges: %d\n", operandIMM_ranges);
       //for (int i=0; i<operandIMM_ranges; i++) 
       //  $write("operandIMM range %d: %b\n", i, chromosome[offset++]);
       
       $write("OperandMEM number of ranges: %d\n", operandMEM_ranges);
       //for (int i=0; i<operandMEM_ranges; i++) 
       //  $write("operandMEM range %d: %b\n", i, chromosome[offset++]);
       
       $write("Number of delay ranges: %d\n", delay_ranges);
       //for (int i=0; i<delay_ranges; i++) 
       //  $write("Delay %d: %b\n", i, chromosome[offset++]); 
         
       $write("Number of MOVI values: %d\n", movi_values);
       //for (int i=0; i<movi_values; i++) 
       //  $write("Movi value %d: %b\n", i, chromosome[offset++]);
         
       $write("Number of operations: %d\n", operation_values);
       //for (int i=0; i<operation_values; i++) 
       //  $write("Operation value %d: %b\n", i, chromosome[offset++]);    
       
       //$write("Fitness: %0d\n", fitness);  
       //$write("Relative fitness: %0d\n", relativeFitness);  
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

      chrom.length          = length;
      chrom.fitness         = fitness;
      chrom.estimatedTime   = estimatedTime;
      chrom.relativeFitness = relativeFitness;
      chrom.chromosome      = new [length];
      chrom.chromosome      = chromosome;
      
      chrom.operandA_ranges = operandA_ranges;
      chrom.operandB_ranges = operandB_ranges;
      chrom.operandIMM_ranges = operandIMM_ranges;
      chrom.operandMEM_ranges = operandMEM_ranges;
      chrom.delay_ranges = delay_ranges;
      chrom.movi_values = movi_values;
      chrom.operation_values = operation_values;
      chrom.delay_rangesMin = delay_rangesMin;
      chrom.delay_rangesMax = delay_rangesMax;
      chrom.operandA_rangesMin = operandA_rangesMin;
      chrom.operandA_rangesMax = operandA_rangesMax;
      chrom.operandB_rangesMin = operandB_rangesMin;
      chrom.operandB_rangesMax = operandB_rangesMax;
      chrom.operandIMM_rangesMin = operandIMM_rangesMin;
      chrom.operandIMM_rangesMax = operandIMM_rangesMax;
      chrom.operandMEM_rangesMin = operandMEM_rangesMin;
      chrom.operandMEM_rangesMax = operandIMM_rangesMax;
      chrom.delayMin = delayMin;
      chrom.delayMax = delayMin;
      
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
    function void evaluate();
      
    endfunction : evaluate
    
   /*
    * Mutates the current value of the object instance.
    */
    virtual function Chromosome mutate(int unsigned maxMutations);  
    
    endfunction : mutate
    
   /*
    * Crossovers the current value of the object instance with the specified 
    * object instance.
    */
    virtual function Chromosome crossover(Chromosome chrom = null); 
    
    endfunction : crossover;
    
  endclass : ALUChromosome
  
