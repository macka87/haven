/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    chromosome_sequence.svh
 * Description:  Chromosome Sequence Class
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         24.6.2013 
 * ************************************************************************** */

/*!
 * \brief ChromosomeSequence
 * 
 * This class represents UVM sequence of chromosomes for ALU.
 */
 
 class ChromosomeSequence extends uvm_sequence #(AluChromosome);

   //! UVM Factory Registration Macro
   `uvm_object_utils(ChromosomeSequence)
  
  /*! 
   * Data Members
   */
   
   local int          populationSize;  // Size of a population
   local selection_t  selection;       // Selection type 
   local bit          elitism;         // Elitism
   local int unsigned maxMutations;    // Maximum number of mutations
   local int unsigned crossoverProb;   // Crossover probability
   local real         allsums[];
   
   ChromosomeArray            old_chr_array;  // Chromosomes stored into an array
   ChromosomeArray            new_chr_array;  // Chromosomes stored into an array
   ChromosomeSequenceConfig   chrom_seq_cfg;  // configuration object
   
   // Configuration object for the coverage storage
   AluCoverageInfo cov_info;   
   
  /*! 
   * Component Members   
   */                
   
   Population pop_sequencer;   
     
  /*!
   * Methods
   */

   // Standard UVM methods
   extern function new(string name = "ChromosomeSequence");
   extern task body();  
      
   // Own UVM methods
   extern task configurePopulation(ChromosomeSequenceConfig chrom_seq_cfg);
   extern task evaluateFitness(AluChromosome alu_chromosome); 
   extern function void getBestChromosome(inout AluChromosome best_chromosome);
   extern function void selectAndReplace();
 endclass: ChromosomeSequence
 
 
 
/*! 
 * Constructor - creates ChromosomeSequence object  
 */
 function ChromosomeSequence::new(string name = "ChromosomeSequence");
   super.new(name);
   
   // create array of chromosomes
   new_chr_array = ChromosomeArray::type_id::create("new_chr_array");
 endfunction: new              



/*! 
 * Body - implements behavior of the transaction
 */ 
 task ChromosomeSequence::body;
   AluChromosome best_chromosome;
   TransactionSequence trans_sequence;     // Transaction Sequence
   string ucdb_file, num;
   int idx;
   int chr_count = 0;
   
   
   // check configuration for Chromosome Sequence
   if (!uvm_config_db #(ChromosomeSequenceConfig)::get(null, get_full_name(), "ChromosomeSequenceConfig", chrom_seq_cfg)) 
     `uvm_error("BODY", "ChromosomeSequenceConfig doesn't exist!"); 
   
   // configure Population of Chromosomes (Chromosome Sequence)
   configurePopulation(chrom_seq_cfg);  
   
   // get population of Chromosomes from the configuration database TREBA VOBEC? NEODPAMATA SI TO TA TRIEDA SAMA NEJAK?
   if (!uvm_config_db #(ChromosomeArray)::get(null, get_full_name(), "ChromosomeArray", old_chr_array))
     `uvm_error("BODY", "Population of chromosomes doesn't exist!"); 
  
   //$set_coverage_db_name("alu.ucdb");
   $write("EVALUATION OF ONE POPULATION: \n");
   
   //$load_coverage_db("alu_empty.ucdb");
   //$set_coverage_db_name("alu_empty.ucdb");
  
   // SEND CHROMOSOMES FROM POPULATION TO DRIVER
   while (chr_count < populationSize) begin
     
     // >>>>> RESET SIMULATION >>>>>
     //$load_coverage_db("alu_empty.ucdb");
     //$set_coverage_db_name ("alu_two.ucdb");
     
     // >>>>> SEND CHROMOSOME TO THE TRANSACTION SEQUENCE >>>>>
     start_item(old_chr_array.alu_chromosome[chr_count]);
     finish_item(old_chr_array.alu_chromosome[chr_count]);
       
     // >>>>> GET COVERAGE >>>>>
     evaluateFitness(old_chr_array.alu_chromosome[chr_count]); 
     
     chr_count++; 
   end
   
   //$load_coverage_db("alu_empty.ucdb");
   
   // FIND THE BEST CHROMOSOME
   getBestChromosome(best_chromosome);
   //$write("BEST CHROMOSOME: index 0: \n");
   //best_chromosome.print(0, 1);
   
   // SIMULATE THE BEST CHROMOSOME ONES MORE AND STORE COVERAGE INTO THE UCDB
   /*$write(">>>>> BEST CHROMOSOME EVALUATION: <<<<<\n");
   $load_coverage_db("alu_empty.ucdb");
   start_item(best_chromosome);
   finish_item(best_chromosome);
   evaluateFitness(cov_info, best_chromosome);*/ 
   
   // CREATE NEW POPULATION
   new_chr_array.alu_chromosome = new[populationSize];
     
   // CHECK ELITISM
   if (elitism) new_chr_array.alu_chromosome[0] = best_chromosome;
   
   // SELECT AND REPLACE
   selectAndReplace();
   
   // SET NEW POPULATION OF CHROMOSOMES TO THE DATABASE
   uvm_config_db #(ChromosomeArray)::set(null, "*", "ChromosomeArray", new_chr_array); 
       
 endtask: body
 
 
 
/*! 
 * configurePopulation - configure Population with data from the configuration object
 */ 
 task ChromosomeSequence::configurePopulation(ChromosomeSequenceConfig chrom_seq_cfg);
   populationSize = chrom_seq_cfg.populationSize;  // Size of a population
   elitism        = chrom_seq_cfg.elitism;         // Elitism 
   selection      = chrom_seq_cfg.selection;       // Selection type 
   maxMutations   = chrom_seq_cfg.maxMutations;    // Maximum number of mutations
   crossoverProb  = chrom_seq_cfg.crossoverProb;   // Maximum number of mutations
 endtask: configurePopulation                      // Crossover probability
 
 
 
/*! 
 * evaluateFitness - counts fitness value for every chromosome
 */ 
 task ChromosomeSequence::evaluateFitness(AluChromosome alu_chromosome); 
   
   // get configuration object from database
   if (!uvm_config_db #(AluCoverageInfo)::get(null, get_full_name(), "AluCoverageInfo", cov_info)) 
     `uvm_error("MYERR", "AluCoverageInfo doesn't exist!"); 
   
   $write("CHROMOSOME: ALU_IN_COVERAGE: %f%%\n", cov_info.alu_in_coverage);  
   $write("CHROMOSOME: ALU_OUT_COVERAGE: %f%%\n", cov_info.alu_out_coverage);
   
   alu_chromosome.fitness = cov_info.alu_in_coverage + cov_info.alu_out_coverage; 
 endtask: evaluateFitness 
 
 
 
/*!
 * Returns the chromosome with the best fitness.
 */
 function void ChromosomeSequence::getBestChromosome(inout AluChromosome best_chromosome);
   int idx;
   int unsigned bestFitness = 0;
      
   for (int i=0; i<old_chr_array.alu_chromosome.size; i++) begin
     if (old_chr_array.alu_chromosome[i].fitness > bestFitness) begin
       bestFitness = old_chr_array.alu_chromosome[i].fitness;
       idx = i;
     end
   end
        
   best_chromosome = old_chr_array.alu_chromosome[idx];  
   
   $write("best chromosome index: %d\n", idx);
   $write("bestFitness: %d\n", bestFitness);
 endfunction: getBestChromosome 
 
 

/*!
 * Selects parents for next generation, creates offsprings using crossover and 
 * mutation. 
 */
 function void ChromosomeSequence::selectAndReplace();
   real tmp;         // random number
   int index;
   real portion = 0; // portion of roulette occupied by chromosomes 
   int unsigned populationFitness = 0;
   
   // different selection mechanisms
   if (selection == PROPORTIONATE) begin
     // compute population fitness = a sum of fitness functions of all chromosomes
     foreach (old_chr_array.alu_chromosome[i]) 
       populationFitness += old_chr_array.alu_chromosome[i].fitness;
     
     // compute relative fitness and portion of roulette for every chromosome
     foreach (old_chr_array.alu_chromosome[i]) begin 
       // set relative fitness
       old_chr_array.alu_chromosome[i].setRelativeFitness(populationFitness);
       // compute and set occupied roulette part 
       portion += old_chr_array.alu_chromosome[i].relativeFitness;
       old_chr_array.alu_chromosome[i].roulette_part = portion;
       //$write("portion %f%%\n", old_chr_array.alu_chromosome[i].roulette_part);
     end  
     
     // Preserve 25% of origin population for next generation
     //numOfParents = populationSize / 6;
     //if (numOfParents < 1)
     //   numOfParents = 1;
     
     // select parents using roulette selection
     for (int i=1; i < populationSize; i++) begin
       tmp = real'($urandom() & 16'hFFFF)/16'hFFFF;
       //$write("tmp = %f\n",tmp);
       
       for (int j=0; j < populationSize; j++) begin
         if (old_chr_array.alu_chromosome[j].roulette_part > tmp) begin
           index = j;
           break;
         end  
       end  
       
       //$write("SELECTED CHROMOSOME: index: %d\n", index);
       new_chr_array.alu_chromosome[i] = old_chr_array.alu_chromosome[index];
       //new_chr_array.alu_chromosome[i].print(i, 1);       
     end
     
     // crossover neighbour chromosomes
     for (int i=1; i < populationSize; i+=2) begin
       if ((i+1 < populationSize) && ($urandom_range(100) < crossoverProb)) 
         new_chr_array.alu_chromosome[i+1] = new_chr_array.alu_chromosome[i].crossover(new_chr_array.alu_chromosome[i+1]);  
     end   
     
     //$write("POPULATION AFTER CROSSOVER:\n");
     //for (int i=0; i < populationSize; i++) begin 
     //   new_chr_array.alu_chromosome[i].print(i, 1);     
     //end
     
     // mutate chromosomes
     for (int i=1; i < populationSize; i++)
       void'(new_chr_array.alu_chromosome[i].mutate(maxMutations)); 
   end
 endfunction: selectAndReplace