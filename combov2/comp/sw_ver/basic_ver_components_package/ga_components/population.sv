/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Genetic Algorithm Population Class
 * Description: 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         14.6.2012 
 * ************************************************************************** */

 class Population;
  
   /*
    * Public Class Atributes
    */
    string       inst;
    int          populationSize;
    Chromosome   population[];
    int unsigned fitness;
    selection_t  selection;
    int unsigned maxMutations;

   /*
    * Private Class Atributes
    */
    real allsums[];
    
   /*
    * Public Class Methods
    */
  
   /*!
    * Creates a new instance of the population class with the specified
    * instance name, size of population and maximal number of generations.
    * Function allocates memory for new population and fill it with random
    * chromosomes.
    */
    function new(string inst, int popSize, int unsigned maxMutations, 
                 selection_t selection = PROPORTIONATE);
      this.inst         = inst;
      populationSize    = popSize;
      this.selection    = selection;
      this.maxMutations = maxMutations;
      fitness           = 0;

      population = new[populationSize];
      allsums    = new[populationSize];

      if (selection == RANK) begin
        real sum       = 0;
        int sumOfRanks = 0;

        for(int i=1; i<=populationSize; i++)
          sumOfRanks += i;
        foreach (population[i]) begin
          sum += real'(i+1)/sumOfRanks;
          allsums[i] = sum;
        end
      end
    endfunction : new
    
   /*!
    * Displays the current value of the population or data described by this
    * instance in a human-readable format on the standard output. Each line of
    * the output will be prefixed with the specified prefix. This method prints
    * the value returned by the psdisplay() method.
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
    virtual function void create(Chromosome chromBlueprint);
      $write("population: VYTVARANIE POPULACIE:\n");

      // Randomize chromosome and insert it in population
      foreach (population[i]) begin  
        assert(chromBlueprint.randomize);
        population[i] = chromBlueprint.copy();
        //population[i].display("CHROMOSOME");
      end

    endfunction : create

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
      $write("Population fitness: %0d\n",fitness);

      // Set relative fitness of each chromosome
      foreach (population[i])
        population[i].setRelativeFitness(fitness);

      foreach (population[i])
        $write("Relative Fitness: %0f\n",population[i].getRelativeFitness());  
        
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
    virtual function void selectAndReplace();
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
      for (int i=0; i < numOfParents; i++)
        nextPopulation[i] = bestParentsQue[i].copy();

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
        nextPopulation[i] = population[index[0]].copy();
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
  
