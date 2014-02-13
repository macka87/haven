/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    chromosome_sequencer.svh
 * Description:  Chromosome Sequencer Class
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         13.2.2014 
 * ************************************************************************** */

/*!
 * \brief ChromosomeSequencer
 * 
 * This class represents sequencer of chromosomes for ALU.
 */
 
 class ChromosomeSequencer;
  
  /*! 
   * Data Members
   */ 
   
   AluCoverageInfo cov_info;
  
  /*! 
   * Channels
   */   
   mailbox #(AluChromosome)   chromosomeMbx; 
   mailbox #(AluCoverageInfo) coverageMbx;   
   
  /*!
   * Component Members
   */ 
   AluChromosomeArray old_chromosome_array; 
   AluChromosomeArray new_chromosome_array;
    
  /*!
   * Methods
   */
   extern function new(AluChromosomeArray chromosome_array);
   extern task run();
   extern task evaluateFitness(AluChromosome alu_chromosome); 
   extern function void getBestChromosome(inout AluChromosome best_chromosome);
   extern function void selectAndReplace();
 endclass: ChromosomeSequencer
 


/*! 
 *  Constructor
 */
 function ChromosomeSequencer::new(AluChromosomeArray chromosome_array);
   this.old_chromosome_array = chromosome_array;    
 endfunction: new  
 

 
/*! 
 * The main run task
 */ 
 task ChromosomeSequencer::run();
   AluChromosome best_chromosome;
   int chr_count = 0;
   
   $write("EVALUATION OF ONE POPULATION: \n");
   
   // send chromosomes to transaction sequencer
   while (chr_count < POPULATION_SIZE) begin
     
     // put chromosome to mailbox
     chromosomeMbx.put(old_chromosome_array.alu_chromosome[chr_count]);
       
     // get coverage information (the mailbox should be blocking until the coverage is available)  
     coverageMbx.get(cov_info);
           
     // get coverage
     evaluateFitness(old_chromosome_array.alu_chromosome[chr_count]); 
     
     chr_count++; 
   end
   
   // find the best chromosome
   getBestChromosome(best_chromosome);
   
   // create new population
   new_chromosome_array = new();
   new_chromosome_array.alu_chromosome = new[POPULATION_SIZE];
     
   // check elitism
   if (ELITISM) new_chromosome_array.alu_chromosome[0] = best_chromosome;
   
   // select and replace
   selectAndReplace();
   
 endtask: run
 


/*! 
 * evaluateFitness - counts fitness value for every chromosome
 */ 
 task ChromosomeSequencer::evaluateFitness(AluChromosome alu_chromosome); 
   
   $write("CHROMOSOME: ALU_IN_COVERAGE: %f%%\n", cov_info.alu_in_coverage);  
   $write("CHROMOSOME: ALU_OUT_COVERAGE: %f%%\n", cov_info.alu_out_coverage);
   
   alu_chromosome.fitness = cov_info.alu_in_coverage + cov_info.alu_out_coverage; 
 endtask: evaluateFitness 
 
 
 
/*!
 * Returns the chromosome with the best fitness.
 */
 function void ChromosomeSequencer::getBestChromosome(inout AluChromosome best_chromosome);
   int idx;
   int unsigned bestFitness = 0;
      
   for (int i=0; i<old_chromosome_array.alu_chromosome.size; i++) begin
     if (old_chromosome_array.alu_chromosome[i].fitness > bestFitness) begin
       bestFitness = old_chromosome_array.alu_chromosome[i].fitness;
       idx = i;
     end
   end
        
   best_chromosome = old_chromosome_array.alu_chromosome[idx];  
   
   $write("best chromosome index: %d\n", idx);
   $write("bestFitness: %d\n", bestFitness);
 endfunction: getBestChromosome 
 
 

/*!
 * Selects parents for next generation, creates offsprings using crossover and 
 * mutation. 
 */
 function void ChromosomeSequencer::selectAndReplace();
   real tmp;         // random number
   int index;
   real portion = 0; // portion of roulette occupied by chromosomes 
   int unsigned populationFitness = 0;
   
   // different selection mechanisms
   // proportionate selection
   if (SELECTION == 0) begin
     // compute population fitness = a sum of fitness functions of all chromosomes
     foreach (old_chromosome_array.alu_chromosome[i]) 
       populationFitness += old_chromosome_array.alu_chromosome[i].fitness;
     
     // compute relative fitness and portion of roulette for every chromosome
     foreach (old_chromosome_array.alu_chromosome[i]) begin 
       // set relative fitness
       old_chromosome_array.alu_chromosome[i].setRelativeFitness(populationFitness);
       // compute and set occupied roulette part 
       portion += old_chromosome_array.alu_chromosome[i].relativeFitness;
       old_chromosome_array.alu_chromosome[i].roulette_part = portion;
       //$write("portion %f%%\n", old_chromosome_array.alu_chromosome[i].roulette_part);
     end  
     
     // Preserve 25% of origin population for next generation
     //numOfParents = populationSize / 6;
     //if (numOfParents < 1)
     //   numOfParents = 1;
     
     // select parents using roulette selection
     for (int i=1; i < POPULATION_SIZE; i++) begin
       tmp = real'($urandom() & 16'hFFFF)/16'hFFFF;
       //$write("tmp = %f\n",tmp);
       
       for (int j=0; j < POPULATION_SIZE; j++) begin
         if (old_chromosome_array.alu_chromosome[j].roulette_part > tmp) begin
           index = j;
           break;
         end  
       end  
       
       //$write("SELECTED CHROMOSOME: index: %d\n", index);
       new_chromosome_array.alu_chromosome[i] = old_chromosome_array.alu_chromosome[index];
       //new_chr_array.alu_chromosome[i].print(i, 1);       
     end
     
     // crossover neighbour chromosomes
     for (int i=1; i < POPULATION_SIZE; i+=2) begin
       if ((i+1 < POPULATION_SIZE) && ($urandom_range(100) < CROSSOVER_PROB)) 
         new_chromosome_array.alu_chromosome[i+1] = new_chromosome_array.alu_chromosome[i].crossover(new_chromosome_array.alu_chromosome[i+1]);  
     end   
     
     //$write("POPULATION AFTER CROSSOVER:\n");
     //for (int i=0; i < populationSize; i++) begin 
     //   new_chromosome_array.alu_chromosome[i].print(i, 1);     
     //end
     
     // mutate chromosomes
     for (int i=1; i < POPULATION_SIZE; i++)
       void'(new_chromosome_array.alu_chromosome[i].mutate(MAX_MUTATIONS)); 
   end
 endfunction: selectAndReplace