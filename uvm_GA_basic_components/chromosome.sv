/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    chromosome.sv
 * Description:  Genetic Algorithm Chromosome Class.
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         10.5.2013 
 * ************************************************************************** */

 
/*! 
 * Constructor - creates the Chromosome object  
 */
 function Chromosome::new(string name = "Chromosome");
   super.new(name);
 endfunction: new  
  

/*
 * It is recommended to use the following methods:
 * copy();
 * clone(); 
 * print();
 * compare();
 */   
    
/*!
 * Saves chromosome to file
 */
 function void Chromosome::save(string filename);
 endfunction : save



/*!
 * Loads chromosome from file
 */
 function void Chromosome::load(string filename);
 endfunction : load


    
/*!
 * Read chromosome
 */
 function void Chromosome::getChromosomes(byte unsigned chromosome[]);
   this.chromosome = chromosome;
 endfunction : getChromosomes 



/*!
 * Returns fitness value of the object instance. 
 */
 function unsigned int Chromosome::getFitness();
   return fitness;
 endfunction : getFitness



/*!
 * Mutates the current value of the object instance.
 */
 function Chromosome Chromosome::mutate(int unsigned maxMutations);
   return this;
 endfunction : mutate



/*!
 * Crossovers the current value of the object instance with the specified 
 * object instance.
 */
 function Chromosome Chromosome::crossover(Chromosome chrom = null);
   return null;
 endfunction : crossover



/*!
 * Computes relative fitness.
 */
 function void Chromosome::setRelativeFitness(int unsigned popFitness);
   relativeFitness = real'(fitness)/real'(popFitness);
 endfunction : setRelativeFitness



/*!
 * Get relative fitness.
 */
 function real Chromosome::getRelativeFitness();
   return relativeFitness;
 endfunction : getRelativeFitness

