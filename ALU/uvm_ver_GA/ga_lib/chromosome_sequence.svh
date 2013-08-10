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
   local real         allsums[];
   
   ChromosomeArray            old_chr_array;      // Chromosomes stored into an array
   ChromosomeArray            new_chr_array;      // Chromosomes stored into an array
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
   extern task evaluateFitness(AluCoverageInfo cov_info, AluChromosome alu_chromosome); 
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
   int chr_count = 0;
   
   
   // check configuration for Chromosome Sequence
   if (!uvm_config_db #(ChromosomeSequenceConfig)::get(null, get_full_name(), "ChromosomeSequenceConfig", chrom_seq_cfg)) 
     `uvm_error("BODY", "ChromosomeSequenceConfig doesn't exist!"); 
   
   // configure Population of Chromosomes (Chromosome Sequence)
   configurePopulation(chrom_seq_cfg);  
   
   // get population of Chromosomes from the configuration database TREBA VOBEC? NEODPAMATA SI TO TA TRIEDA SAMA NEJAK?
   if (!uvm_config_db #(ChromosomeArray)::get(null, get_full_name(), "ChromosomeArray", old_chr_array))
     `uvm_error("BODY", "Population of chromosomes doesn't exist!"); 
  
   // create configuration object for coverage info
   cov_info = AluCoverageInfo::type_id::create("cov_info");
   
   // store new coverage info into the configuration object
   uvm_config_db #(AluCoverageInfo)::set(null, "*", "AluCoverageInfo", cov_info);
      
  
   // SEND CHROMOSOMES FROM POPULATION TO DRIVER
   while (chr_count < populationSize) begin
     
     // >>>>> RESET SIMULATION >>>>>
     //$load_coverage_db("alu_coverage_report.ucdb");
     
     // >>>>> SEND CHROMOSOME TO THE TRANSACTION SEQUENCE >>>>>
     start_item(old_chr_array.alu_chromosome[chr_count]);
     finish_item(old_chr_array.alu_chromosome[chr_count]);
       
     // >>>>> GET COVERAGE AND RESET VALUES >>>>>
     evaluateFitness(cov_info, old_chr_array.alu_chromosome[chr_count]); 
         
     //num.itoa(chr_count);
     //ucdb_file = {"coverage_report_", num, ".ucdb"};
     //$write("%s\n", ucdb_file);
     //$set_coverage_db_name(ucdb_file);
     //$system("./coverage_save.sh");
     
     chr_count++; 
   end
   
   // !!! prerobit old_chr_array dostupne v celej triede !! netreba predavat ako parametre 
   
   // FIND THE BEST CHROMOSOME
   getBestChromosome(best_chromosome);
   best_chromosome.print(0, 1);
   
   // CREATE NEW POPULATION
   new_chr_array.alu_chromosome = new[populationSize];
   
   // CHECK ELITISM
   if (elitism) new_chr_array.alu_chromosome[0] = best_chromosome;
   
   // SELECT AND REPLACE
   selectAndReplace();
    
 endtask: body
 
 
 
/*! 
 * configurePopulation - configure Population with data from the configuration object
 */ 
 task ChromosomeSequence::configurePopulation(ChromosomeSequenceConfig chrom_seq_cfg);
   populationSize = chrom_seq_cfg.populationSize;  // Size of a population
   elitism        = chrom_seq_cfg.elitism;         // Elitism 
   selection      = chrom_seq_cfg.selection;       // Selection type 
   maxMutations   = chrom_seq_cfg.maxMutations;    // Maximum number of mutations
 endtask: configurePopulation
 
 
 
/*! 
 * evaluateFitness - counts fitness value for every chromosome
 */ 
 task ChromosomeSequence::evaluateFitness(AluCoverageInfo cov_info, AluChromosome alu_chromosome); 
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
 endfunction: getBestChromosome 
 
 

/*!
 * Selects parents for next generation, creates offsprings using crossover and 
 * mutation. 
 */
 function void ChromosomeSequence::selectAndReplace();
   real tmp;         // random number
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
       $write("portion %f%%\n", portion);
     end  
     
     // Preserve 25% of origin population for next generation
     //numOfParents = populationSize / 6;
     //if (numOfParents < 1)
     //   numOfParents = 1;
     
     // select parents using roulette selection
      for (int i=1; i < populationSize; i++) begin
        tmp = real'($urandom() & 16'hFFFF)/16'hFFFF;
        $write("tmp = %f\n",tmp);
        index = allsums.find_first_index(s) with (s >= tmp);
        $write("index: %0d\n",index[0]);
        nextPopulation[i].copy(population[index[0]]);
      end
     
     
   end
 endfunction: selectAndReplace