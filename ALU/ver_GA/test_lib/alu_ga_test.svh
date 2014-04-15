/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    alu_ga_test.svh
 * Description:  GA Test for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014
 * ************************************************************************** */

/*!
 * \brief AluGATest
 * 
 * This class represents GA test for ALU.
 */
 class AluGATest;  
  
  /*!
   * Component Members
   */
   
   AluGAAgent           alu_ga_agent;          // The agent class
     
  /*
   * Virtual interfaces
   */    
   virtual iAluIn  dut_alu_in_if;  // ALU input interface
   virtual iAluOut dut_alu_out_if; // ALU output interface 
   
  /*! 
   * Channels
   */  
   mailbox #(AluChromosome) chromosomeMbx;  
   mailbox #(AluCoverageInfo) coverageMbx;
  
  /*! 
   * Data Members
   */
   AluChromosomeArray chromosome_array; 
   AluChromosomeArray new_chromosome_array;
   AluCoverageInfo cov_info;
        
   /*!
   * Methods
   */
   extern function new(virtual iAluIn dut_alu_in_if, virtual iAluOut dut_alu_out_if);
   extern function void create_structure();
   extern task run();
   extern task createOrLoadInitialPopulation(int file_id);
   extern task configureAluChromosome(AluChromosome alu_chromosome);
   extern task evaluateFitness(AluChromosome alu_chromosome); 
   extern function void readChromosomeArrayFromFile(int file_id);
   extern function void getBestChromosome(inout AluChromosome best_chromosome);
   extern function void selectAndReplace();
 endclass: AluGATest
 


/*! 
 *  Constructor
 */
 function AluGATest::new(virtual iAluIn  dut_alu_in_if,
                         virtual iAluOut dut_alu_out_if
                         );
   this.dut_alu_in_if = dut_alu_in_if;    //! Store pointer interface 
   this.dut_alu_out_if = dut_alu_out_if;  //! Store pointer interface  
   
   chromosome_array = new();
 endfunction: new   


 
/*! 
 *  Constructor - create and configure environment
 */ 
 function void AluGATest::create_structure();
   // >>>>> CREATE COMPONENTS >>>>>
   chromosomeMbx  = new(1);
   coverageMbx    = new(1);
 
   //chromosome_sequencer  = new(chr_array);
   alu_ga_agent = new(dut_alu_in_if, dut_alu_out_if);
   
   //chromosome_sequencer.chromosomeMbx = chromosomeMbx;
   alu_ga_agent.chromosomeMbx = chromosomeMbx;
   
   //chromosome_sequencer.coverageMbx = coverageMbx;
   alu_ga_agent.coverageMbx = coverageMbx;
   
 endfunction: create_structure
 


/*! 
 * Main run
 */     
 task AluGATest::run();
   int file_id, res, file_id2;
   int population_number;
   int chromosome_number;
   AluChromosome best_chromosome;
  
   // ------------------------------------------------------------------------
   $write("\n\n########## GENETIC ALGORITHM ##########\n\n");
   
   // initialize the extern file
   /*file_id = $fopen(CHROMOSOMES_FILE, "w+");
   $fwrite(file_id, "%x\n", 0);
   $fwrite(file_id, "%x\n", 0);
   $fclose(file_id);*/
   
   // read parameters that determine the number of generation and the number of chromosome in this generation of chromosomes
   file_id = $fopen(CHROMOSOMES_FILE, "r+");
   res = $fscanf(file_id, "%x\n", population_number);
   $write("POPULATION NUMBER: %d\n", population_number);
   
   res = $fscanf(file_id, "%x\n", chromosome_number);
   $write("CHROMOSOME NUMBER: %d\n", chromosome_number);
   
   // create mailboxes and agent
   create_structure();
   
   // ak sa jedna o nultu generaciu a nulty chromozom, vygeneruj init populaciu chromozomov, zapis ich do suboru a nulty chromozom ohodnot a uloz fitness 
   if (population_number == 0 && chromosome_number == 0) begin
     createOrLoadInitialPopulation(file_id);
     
     // evaluate first chromosome of initial population
     chromosomeMbx.put(chromosome_array.alu_chromosome[0]);
     $fclose(file_id);
     
     // run agent
     alu_ga_agent.run();
       
     // get coverage information
     coverageMbx.get(cov_info);
       
     // see coverage
     evaluateFitness(chromosome_array.alu_chromosome[0]);
     
     // rewrite number of generation and chromosome for the next run
     file_id = $fopen(CHROMOSOMES_FILE, "r+");
     $fwrite(file_id, "%x\n", 0);
     $fwrite(file_id, "%x\n", 1);
     $fclose(file_id);
   end  
   
   // ak sa jedna o nultu generaciu ale chromozom >0, nacitaj chromozom zo suboru a ohodnot a zapis fitness
   else if (population_number == 0 && chromosome_number > 0) begin
     // read chromosomes into an array
     readChromosomeArrayFromFile(file_id);
     $fclose(file_id);
     
     // evaluate x-th chromosome of initial population
     chromosomeMbx.put(chromosome_array.alu_chromosome[chromosome_number]);
     
     // run agent
     alu_ga_agent.run();
       
     // get coverage information
     coverageMbx.get(cov_info);
       
     // see coverage
     evaluateFitness(chromosome_array.alu_chromosome[chromosome_number]);
     
     // rewrite number of generation and chromosome for the next run
     file_id = $fopen(CHROMOSOMES_FILE, "r+");
     
     if (chromosome_number == POPULATION_SIZE-1) begin 
       $fwrite(file_id, "%x\n", (population_number+1));
       $fwrite(file_id, "%x\n", 0);

       // find the best chromosome
       getBestChromosome(best_chromosome);
       $write("best chromosome fitness %d\n", best_chromosome.fitness);
   
       // create new population
       new_chromosome_array = new();
       new_chromosome_array.alu_chromosome = new[POPULATION_SIZE];
     
       // check elitism
       if (ELITISM) new_chromosome_array.alu_chromosome[0] = best_chromosome;
   
       // select and replace
       selectAndReplace();



       // write new chromosomes into the file - najskor test, potom priamo do suboru CHROMOSOMES_FILE
       /*file_id2 = $fopen("test.txt", "a+");
       for (int i=0; i<POPULATION_SIZE; i++) begin
         new_chromosome_array.alu_chromosome[i].writeToFile(file_id2);   
       end
       $fclose(file_id2);*/


     end  
     else begin
       $fwrite(file_id, "%x\n", 0);
       $fwrite(file_id, "%x\n", (chromosome_number+1));
     end  
     $fclose(file_id);
   end
   
   
   // ak sa jedna o nultu generaciu a chromozom = POPULATION_SIZE-1, tak ohodnot posledny chromozom, aplikuj selekciu a vytvorenie novej generacie, uloz best chromozom do separatneho suboru a nove chromozomy, uloz nove cislo generacie
   
   // ak sa jedna o generaciu >0, nacitaj chromozom zodpovedajuceho cisla, pocet best chromozomes posla cisla generacie. Vyhodnot simulaciou best chromozomes a hned za nimi ohodnot novy chromozom + uloz fitness
   
 endtask: run  



/*
 *  Create or load initial population.  
 */  
 task AluGATest::createOrLoadInitialPopulation(int file_id);
   
   $write("******************************************************************** \n");
   $write("******************     INITIAL POPULATION      ********************* \n");
   $write("******************************************************************** \n");
   
   // create random initial population
   chromosome_array.alu_chromosome = new[POPULATION_SIZE];
   for (int i=0; i<POPULATION_SIZE; i++) begin
     // create chromosome 
     chromosome_array.alu_chromosome[i] = new();
     // configure chromosome
     configureAluChromosome(chromosome_array.alu_chromosome[i]);
     // randomize chromosome
     assert(chromosome_array.alu_chromosome[i].randomize()); 
     // print chromosome
     chromosome_array.alu_chromosome[i].print(i, 0); 
     // store chromosomes into the chromosomes.txt file
     chromosome_array.alu_chromosome[i].writeToFile(file_id);    
   end 
 endtask: createOrLoadInitialPopulation
 


/*
 *  Read chromosomes from an external file.
 */
 function void AluGATest::readChromosomeArrayFromFile(int file_id);
   chromosome_array.alu_chromosome = new[POPULATION_SIZE];
   for (int i=0; i<POPULATION_SIZE; i++) begin
      // create chromosome 
      chromosome_array.alu_chromosome[i] = new();
      // read the content of chromosome
      chromosome_array.alu_chromosome[i].readFromFile(file_id);
      // set all constants
      chromosome_array.alu_chromosome[i].chromosome_parts = 7;
   end    
 endfunction: readChromosomeArrayFromFile



/*! 
 * configureAluChromosome - configure ALU Chromosome with data from the configuration object
 */ 
 task AluGATest::configureAluChromosome(AluChromosome alu_chromosome);
   alu_chromosome.movi_values           = 3;   // num. of values for MOVI
   alu_chromosome.operation_values      = 16;  // num. of values for OPERATION
   alu_chromosome.delay_rangesMin       = DELAY_RANGES_MIN;         
   alu_chromosome.delay_rangesMax       = DELAY_RANGES_MAX;
   alu_chromosome.operandA_rangesMin    = OPERAND_A_RANGES_MIN;
   alu_chromosome.operandA_rangesMax    = OPERAND_A_RANGES_MAX;
   alu_chromosome.operandB_rangesMin    = OPERAND_B_RANGES_MIN;
   alu_chromosome.operandB_rangesMax    = OPERAND_B_RANGES_MAX;  
   alu_chromosome.operandMEM_rangesMin  = OPERAND_MEM_RANGES_MIN;
   alu_chromosome.operandMEM_rangesMax  = OPERAND_MEM_RANGES_MAX;  
   alu_chromosome.operandIMM_rangesMin  = OPERAND_IMM_RANGES_MIN;
   alu_chromosome.operandIMM_rangesMax  = OPERAND_IMM_RANGES_MAX;
   
   // !!! maximal length
   alu_chromosome.length = alu_chromosome.operandA_rangesMax + alu_chromosome.operandB_rangesMax + 
                           alu_chromosome.operandMEM_rangesMax + alu_chromosome.operandIMM_rangesMax + 
                           alu_chromosome.delay_rangesMax + alu_chromosome.movi_values + 
                           alu_chromosome.operation_values;
                           
   alu_chromosome.chromosome_parts     = 7;                        
 endtask: configureAluChromosome 
 
 
 
 /*! 
 * evaluateFitness - counts fitness value for every chromosome
 */ 
 task AluGATest::evaluateFitness(AluChromosome alu_chromosome); 
   int file_id;   

   $write("CHROMOSOME: ALU_IN_COVERAGE: %f%%\n", cov_info.alu_in_coverage);  
   $write("CHROMOSOME: ALU_OUT_COVERAGE: %f%%\n", cov_info.alu_out_coverage);
   
   alu_chromosome.fitness = cov_info.alu_in_coverage + cov_info.alu_out_coverage; 
   
   // store fitness value into the external file - cez append?
   file_id = $fopen(FITNESS_FILE, "a+");
   $fwrite(file_id, "%x\n", alu_chromosome.fitness);
   $fclose(file_id);  
 endtask: evaluateFitness 
 
 
 
/*!
 * Returns the chromosome with the best fitness.
 */
 function void AluGATest::getBestChromosome(inout AluChromosome best_chromosome);
   int file_id, res; 
   int idx;
   int unsigned bestFitness = 0;

   // read fitness values of all chromosomes in array (they are already read in readChromosomeArrayFromFile function)
   file_id = $fopen(FITNESS_FILE, "a+");

   for (int i=0; i<POPULATION_SIZE; i++) begin
      // read fitness and store it into the chromosome array field 
      res = $fscanf(file_id, "%x\n", chromosome_array.alu_chromosome[i].fitness);
   end 

   $fclose(file_id);
   
   // find chromosome with best fitness value
   for (int i=0; i<chromosome_array.alu_chromosome.size; i++) begin
     if (chromosome_array.alu_chromosome[i].fitness > bestFitness) begin
       bestFitness = chromosome_array.alu_chromosome[i].fitness;
       idx = i;
     end
   end

   best_chromosome = chromosome_array.alu_chromosome[idx];
   $write("best chromosome index: %d\n", idx);   

   // store best fitness chromosome into the special file: BEST_CHROMOSOMES_FILE     
   file_id = $fopen(BEST_CHROMOSOMES_FILE, "a+");  
   chromosome_array.alu_chromosome[idx].writeToFile(file_id);   
   $fclose(file_id);
 endfunction: getBestChromosome 
 
 

/*!
 * Selects parents for next generation, creates offsprings using crossover and 
 * mutation. 
 */
 function void AluGATest::selectAndReplace();
   real tmp;         // random number
   int tmp2;
   int index;
   real portion = 0; // portion of roulette occupied by chromosomes 
   int unsigned populationFitness = 0;
   int file_id_select, file_id_cross, file_id_mutate;
   int h = 1;
   
   // different selection mechanisms
   // proportionate selection
   if (SELECTION == 0) begin
     // compute population fitness = a sum of fitness functions of all chromosomes
     foreach (chromosome_array.alu_chromosome[i]) 
       populationFitness += chromosome_array.alu_chromosome[i].fitness;
     
     // compute relative fitness and portion of roulette for every chromosome
     foreach (chromosome_array.alu_chromosome[i]) begin 
       // set relative fitness
       chromosome_array.alu_chromosome[i].setRelativeFitness(populationFitness);
       // compute and set occupied roulette part 
       portion += chromosome_array.alu_chromosome[i].relativeFitness;
       chromosome_array.alu_chromosome[i].roulette_part = portion;
       $write("portion %f%%\n", chromosome_array.alu_chromosome[i].roulette_part);
     end  
     
     // Preserve 25% of origin population for next generation
     //numOfParents = populationSize / 6;
     //if (numOfParents < 1)
     //   numOfParents = 1;
     
     // select parents using roulette selection
     for (int i=1; i < POPULATION_SIZE; i++) begin  // i=1 because of elitism
       tmp = real'($urandom() & 16'hFFFF)/16'hFFFF;
       $write("tmp = %f\n",tmp);

       tmp2 = $urandom_range(100);
       $write("tmp2 = %d\n",tmp2);
       
       for (int j=0; j < POPULATION_SIZE; j++) begin
         if (chromosome_array.alu_chromosome[j].roulette_part > tmp) begin
           index = j;
           break;
         end  
       end  
       
       $write("SELECTED CHROMOSOME: index: %d\n", index);
       new_chromosome_array.alu_chromosome[i] = chromosome_array.alu_chromosome[index].clone();  //clone - to bol ten zasadny problem koli ktoremu to nefungovalo
       //new_chr_array.alu_chromosome[i].print(i, 1);       
     end

     // print selected population
     $write("NEW POPULATION AFTER SELECTION\n");
     /*for (int i=0; i < POPULATION_SIZE; i++) begin
       $write("%x %x %x %x %x %x %x %x\n", new_chromosome_array.alu_chromosome[i].length, new_chromosome_array.alu_chromosome[i].movi_values, new_chromosome_array.alu_chromosome[i].operandA_ranges, new_chromosome_array.alu_chromosome[i].operandB_ranges, new_chromosome_array.alu_chromosome[i].operandMEM_ranges, new_chromosome_array.alu_chromosome[i].operandIMM_ranges, new_chromosome_array.alu_chromosome[i].operation_values, new_chromosome_array.alu_chromosome[i].delay_ranges);
     end */
     
     file_id_select = $fopen("test_selection.txt", "a+");
          
     for (int i=0; i < POPULATION_SIZE; i++) begin
       new_chromosome_array.alu_chromosome[i].writeToFile(file_id_select); 
     end
     
     $fclose(file_id_select);
     
     // crossover neighbour chromosomes
     //for (int i=1; i < POPULATION_SIZE; i+=2) begin
     while (h<POPULATION_SIZE)  begin
       if ((h+1 < POPULATION_SIZE) && ($urandom_range(100) < CROSSOVER_PROB)) begin
         $write("crossover of chromosomes: %d and %d\n", (h+1), h);
         
         /*new_chromosome_array.alu_chromosome[0].print(0, 1);
         new_chromosome_array.alu_chromosome[1].print(1, 1);
         new_chromosome_array.alu_chromosome[2].print(2, 1);   
         new_chromosome_array.alu_chromosome[3].print(3, 1);   
         new_chromosome_array.alu_chromosome[4].print(4, 1);*/
         
         //$write("%d, %d\n", h, h+1);
         //new_chromosome_array.alu_chromosome[h+1] = new_chromosome_array.alu_chromosome[h].crossover(new_chromosome_array.alu_chromosome[h+1]); 
         
         new_chromosome_array.alu_chromosome[h].crossover(new_chromosome_array.alu_chromosome[h+1]); 
         
         /*new_chromosome_array.alu_chromosome[0].print(0, 1);
         new_chromosome_array.alu_chromosome[1].print(1, 1);
         new_chromosome_array.alu_chromosome[2].print(2, 1);   
         new_chromosome_array.alu_chromosome[3].print(3, 1);   
         new_chromosome_array.alu_chromosome[4].print(4, 1); */  
         // ! uz tu je chyba!!!!!!
       end   
       h=h+2;
     end   
     
     // print selected population
     $write("NEW POPULATION AFTER CROSSOVER\n");
     /*for (int i=0; i < POPULATION_SIZE; i++) begin
       $write("%x %x %x %x %x %x %x %x\n", new_chromosome_array.alu_chromosome[i].length, new_chromosome_array.alu_chromosome[i].movi_values, new_chromosome_array.alu_chromosome[i].operandA_ranges, new_chromosome_array.alu_chromosome[i].operandB_ranges, new_chromosome_array.alu_chromosome[i].operandMEM_ranges, new_chromosome_array.alu_chromosome[i].operandIMM_ranges, new_chromosome_array.alu_chromosome[i].operation_values, new_chromosome_array.alu_chromosome[i].delay_ranges);
     end*/
     
     
     
     
     file_id_cross = $fopen("test_crossover.txt", "a+");
          
     for (int i=0; i < POPULATION_SIZE; i++) begin
       //new_chromosome_array.alu_chromosome[i].print(i, 1);
       
       new_chromosome_array.alu_chromosome[i].writeToFile(file_id_cross); 
     end
     
     $fclose(file_id_cross);
     
     // mutate chromosomes
     for (int i=1; i < POPULATION_SIZE; i++) begin
	if ($urandom_range(100) < MUTATION_PROB)   begin    
		$write("Mutation for chromosome %d\n", i);		
		void'(new_chromosome_array.alu_chromosome[i].mutate(MAX_MUTATIONS)); 
	end
     end
       
     $write("NEW POPULATION AFTER MUTATION\n");  
     
     file_id_mutate = $fopen("test_mutation.txt", "a+");
          
     for (int i=0; i < POPULATION_SIZE; i++) begin
       new_chromosome_array.alu_chromosome[i].writeToFile(file_id_mutate); 
     end
     
     $fclose(file_id_mutate);
   end
 endfunction: selectAndReplace
