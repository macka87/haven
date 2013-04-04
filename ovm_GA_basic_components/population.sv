/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    population.sv
 * Description:  Genetic Algorithm Population Class
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         3.4.2013 
 * ************************************************************************** */

/*!
 * \brief Population
 * 
 * This class defines population and basic operations performed with population.
 */

 class Population extends ovm_component;
 
    // registration of component tools
    `ovm_component_utils(Population)
  
   /*
    * Local Class Atributes
    */
    local int          populationSize;  // Size of a population
    local Chromosome   population[];    // An array of chromosomes
    local int unsigned fitness;         // Fitness function
    local selection_t  selection;       // Selection type 
    local int unsigned maxMutations;    // Maximum number of mutations
    local real         allsums[];
    
   /*
    * Public Class Methods
    */
  
   /*!
    * Creates a new instance of the population class.
    */
    function new(string name, ovm_component parent);
      super.new(name, parent);  
    endfunction : new
    
   /*! 
    * Build - initialisation and configuration: setting the size of population
    * and maximal number of generations. The memory is allocated for a new 
    * population and fill it with random chromosomes. 
    */
    function void build;
      string msg;
      int sel;
     
      super.build();
     
      // get configuration items
      if (!get_config_int("populationSize", populationSize)) begin
        $sformat(msg, "\"populationSize\" is not in the configuration database, using default value of %0d",populationSize);
        ovm_report_warning("BUILD PHASE", msg);
      end  
     
      if (!get_config_int("maxMutations", maxMutations)) begin
        $sformat(msg, "\"maxMutations\" is not in the configuration database, using default value of %0d",populationSize);
        ovm_report_warning("BUILD PHASE", msg);
      end 
     
      if (!get_config_int("maxMutations", maxMutations)) begin
        $sformat(msg, "\"maxMutations\" is not in the configuration database, using default value of %0d",populationSize);
        ovm_report_warning("BUILD PHASE", msg);
      end 
     
      if (!get_config_int("selection", sel)) begin
        $cast(selection, sel);
        $sformat(msg, "\"selection\" is not in the configuration database, using default value of %0d",populationSize);
        ovm_report_warning("BUILD PHASE", msg);
      end
     
      // instanciation
      population = new[populationSize];
      allsums    = new[populationSize];
     
      // initialisation
      fitness    = 0;  
      //selection = PROPORTIONATE;  
     
      // CO TOTO ROBI???
      /*if (selection == RANK) begin
        real sum       = 0;
        int sumOfRanks = 0;

        for(int i=1; i<=populationSize; i++)
          sumOfRanks += i;
        foreach (population[i]) begin
          sum += real'(i+1)/sumOfRanks;
          allsums[i] = sum;
        end
      end*/
    endfunction: build 

   /*
    * Local Class Methods
    */
   
   /*!
    * Displays the current value of the population or data described by this
    * instance in a human-readable format on the standard output. Each line of
    * the output will be prefixed with the specified prefix. 
    */
    virtual function void display(string prefix = "");
      if (prefix != "")
      begin
        $write("---------------------------------------------------------\n");
        $write("-- %s\n",prefix);
        $write("---------------------------------------------------------\n");
      end
      
      $write("Population size: %0d\n", populationSize);
      $write("Population fitness: %0d\n", fitness);
      $write("\n");  
    endfunction : display
  
   /*!
    * Fills up population with chromosomes randomly generated with respect to
    * chromosome blueprint parameter.
    */
    virtual function void create_chromosome(Chromosome chromBlueprint);
      // Randomize chromosome and insert it in population
      foreach (population[i]) begin  
        assert(chromBlueprint.randomize);
        //population[i] = chromBlueprint.copy();
        population[i].do_copy(chromBlueprint);
        //population[i].display("CHROMOSOME");
      end

    endfunction : create_chromosome

   /*!
    * Saves each chromosome in population to file
    */
    virtual function void save(string fname);
      string filename;

      // Save each chromosome to file
      foreach (population[i]) begin
        $swrite(filename, "%s.%0d.chr", fname, i);
        population[i].save(filename);
      end

    endfunction : save

   /*!
    * Loads each chromosome in population from file
    */
    virtual function void load(string fname, Chromosome chromBlueprint);
      string filename;

      // Load each chromosome from file
      foreach (population[i]) begin
        $swrite(filename, "%s.%0d.chr", fname, i);
        population[i].load(filename);
      end

    endfunction : load

   /*!
    * Sums fitness values of chromosomes in current population.
    */
    virtual function int unsigned evaluate();
      int unsigned sum = 0;

      // Compute population fitness
      foreach (population[i])
        sum += population[i].getFitness();

      fitness = sum;
      
      $write("\n");
      $write("POPULATION FITNESS: %0d\n\n",fitness);

      // Set relative fitness of each chromosome
      foreach (population[i])
        population[i].setRelativeFitness(fitness);

      //foreach (population[i])
        //$write("Relative Fitness: %0f\n",population[i].getRelativeFitness());  
        
      return fitness;
    endfunction : evaluate

   /*!
    * Returns queue of chromosomes with best fitness.
    */
    virtual function void getBestChromosomes(int count = 1,
                                             ref Chromosome chrom[]);
      int unsigned bestFitness;
      int idx;
      bit flag[] = new[populationSize];

      for (int j=0; j < count; j++) begin
        bestFitness = 0;

        foreach (population[i]) begin
          if ((bestFitness < population[i].getFitness()) && (flag[i]!=1)) begin
            bestFitness = population[i].getFitness();
            idx         = i;
          end
        end
        flag[idx] = 1;
        chrom[j]  = population[idx];
      end
    endfunction : getBestChromosomes

   /*!
    * Selects parents for next generation using Roulette Wheel selection,
    * creates offsprings using crossover and mutation. Old population is
    * replaced with these offsprings.
    */
    virtual function void selectAndReplace(ref Chromosome best_chrom);
      Chromosome nextPopulation[] = new[populationSize];  // new population
      int index[$];
      real tmp;
      int numOfParents;                                   // number of parents
      Chromosome bestParentsQue[];                        // parents
      real sum = 0; 

      // Preserve 25% of origin population for next generation
      numOfParents = populationSize / 6;
      if (numOfParents < 1)
        numOfParents = 1;

      bestParentsQue = new[numOfParents];
      getBestChromosomes(numOfParents, bestParentsQue);
      
      // select best chromosome
      best_chrom = bestParentsQue[0];
      
      for (int i=0; i < numOfParents; i++)
        nextPopulation[i].copy(bestParentsQue[i]);

      // Compute relative fitness for each chromosome and all prefix sums for
      // Roulette Wheel selection
      if (selection == PROPORTIONATE) begin
        foreach (population[i]) begin
          sum += population[i].getRelativeFitness();
          allsums[i] = sum;
        end
      end
      else begin
        // Sort individuals according to fitness and set all prefix sums for
        // Rank selection
        population.sort with (item.getFitness());
      end

//      foreach (allsums[i])
//        $write("allsums: %0f\n",allsums[i]);

      // Select parents using Roulette Wheel selection
      for (int i=numOfParents; i < populationSize; i++) begin
        tmp = real'($urandom() & 16'hFFFF)/16'hFFFF;
//        $write("tmp = %f\n",tmp);
        index = allsums.find_first_index(s) with (s >= tmp);
//        $write("index: %0d\n",index[0]);
        nextPopulation[i].copy(population[index[0]]);
      end
        
      // Crossover neighbour chromosomes
      // If populationSize is odd number, last member does not have neighbour
      // to crossover, therefore round populationSize down to even number
      for (int i=numOfParents; i < populationSize; i+=2)
        if (i+1 < populationSize && $urandom_range(100) < 80) 
          nextPopulation[i+1] = nextPopulation[i].crossover(nextPopulation[i+1]);

      // Mutate chromosomes
      for (int i=numOfParents; i < populationSize; i++)
        void'(nextPopulation[i].mutate(maxMutations));

      population = nextPopulation;
    endfunction : selectAndReplace

  endclass : Population
  
