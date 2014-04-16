/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU 
 * File Name:    test_pkg.sv - test package
 * Description:  Definition of constants and parameters. 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz>
 * Date:         21.1.2014 
 * ************************************************************************** */ 

 package sv_alu_param_pkg;
   
   // VERSION
   parameter VERSION        = 1; // 0 == without GA, 1 == with GA
   
   // DUT GENERICS
   parameter DATA_WIDTH     = 8; // data width
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD     = 10ns;
   parameter RESET_TIME     = 10*CLK_PERIOD;
   
   // VE PARAMETERS
   parameter HAS_FUNCTIONAL_COVERAGE = 1;
   parameter HAS_ALU_SCOREBOARD      = 1;
   
   // GENETIC ALGORITHM PARAMETERS
   // File with parameters and chromosomes
   parameter CHROMOSOMES_FILE = "chromosomes.txt";
   
   // File with best chromosomes
   parameter BEST_CHROMOSOMES_FILE = "best_chromosomes.txt";

   // File with fitness values
   parameter FITNESS_FILE = "fitness.txt";
   
   // Number of generations
   parameter GENERATIONS      = 2;
   // Size of population
   parameter POPULATION_SIZE  = 5;
   // Elitism
   parameter ELITISM          = 1;
   // Selection
   parameter SELECTION        = 0; // 0 == proportionate
   
   // Crossover probability
   parameter CROSSOVER_PROB   = 80;
   // Mutation probability
   parameter MUTATION_PROB    = 50;

   // Number of maximal mutations per individuum
   parameter MAX_MUTATIONS    = 20;

   // File for save/load population
   parameter string POPULATION_FILENAME = "pop";
   // Load or create new population on evolution start
   parameter LOAD_POPULATION  = 0; 
   parameter ESTIMATED_TIME   = 800;

   // CHROMOSOME PARAMETERS
   // Ranges parameters
   parameter DELAY_RANGES_MIN       = 1;
   parameter DELAY_RANGES_MAX       = 4;
   parameter OPERAND_A_RANGES_MIN   = 1;
   parameter OPERAND_A_RANGES_MAX   = 8;
   parameter OPERAND_B_RANGES_MIN   = 1;
   parameter OPERAND_B_RANGES_MAX   = 8;
   parameter OPERAND_MEM_RANGES_MIN = 1;
   parameter OPERAND_MEM_RANGES_MAX = 8;
   parameter OPERAND_IMM_RANGES_MIN = 1;
   parameter OPERAND_IMM_RANGES_MAX = 8;
   
   // TRANSACTION COUNT FOR CLASSICAL RUN
   parameter TRANS_COUNT            = 10;
   parameter SEED                   = 0;
 endpackage
