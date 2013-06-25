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
   
   AluChromosomeConfig  alu_chromosome_cfg;   // configuration object
   
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
   extern function void print(string name);
   
   // Own UVM methods
   extern function void evaluate(int coveredBins);

 endclass : AluChromosome
  
