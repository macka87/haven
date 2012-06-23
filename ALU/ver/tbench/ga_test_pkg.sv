/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    ALU Genetic Algorithm Test Package
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         23.6.2012 
 * ************************************************************************** */

 package ga_test_pkg;
 
   // GENETIC ALGORITHM PARAMETERS
   // Number of generations
   parameter GENERATIONS      = 1;
   // Size of population
   parameter POPULATION_SIZE  = 5;
   // Number of maximal mutations per individuum
   parameter MAX_MUTATIONS    = 5;
   // File for save/load population
   parameter string POPULATION_FILENAME = "pop";
   // Load or create new population on evolution start
   parameter LOAD_POPULATION  = 0; 
   // Estimated duration fifo to get full (us)
   parameter ESTIMATED_TIME   = 800;

   // CHROMOSOME PARAMETERS
   // Ranges parameters
   parameter DELAY_RANGES_MIN       = 1;
   parameter DELAY_RANGES_MAX       = 3;
   parameter OPERAND_A_RANGES_MIN   = 1;
   parameter OPERAND_A_RANGES_MAX   = 10;
   parameter OPERAND_B_RANGES_MIN   = 1;
   parameter OPERAND_B_RANGES_MAX   = 10;
   parameter OPERAND_IMM_RANGES_MIN = 1;
   parameter OPERAND_IMM_RANGES_MAX = 10;
   parameter OPERAND_MEM_RANGES_MIN = 1;
   parameter OPERAND_MEM_RANGES_MAX = 10;
   // Constraint parameters
   parameter DELAY_MIN              = 0;
   parameter DELAY_MAX              = 10;
   
   // TRANSACTION COUNT PER EACH CHROMOSOME
   parameter TRANS_COUNT_PER_CHROM  = 100;

 endpackage
