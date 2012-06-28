/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Genetic Algorithm Chromosome Class
 * Description: 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         14.6.2012 
 * ************************************************************************** */

 class Chromosome;
  
   /*
    * Public Class Atributes
    */
    int          length;                 // length of chromosome
    int          chromosome_parts;       // uniform parts of chromosome
    rand byte unsigned chromosome[];     // chromosome
    int unsigned fitness         = 0;    // fitness function
    real         relativeFitness = 0;    // relative fitness function

   /*
    * Public Class Methods
    */
  
   /*
    * Displays the current value of the chromosome or data described by this
    * instance in a human-readable format on the standard output. Each line of
    * the output will be prefixed with the specified prefix. This method prints
    * the value returned by the psdisplay() method.
    */
    virtual function void display(string prefix = "");
    endfunction : display
  
   /*!
    * Copies the current value of the object instance to the specified object
    * instance. If no target object instance is specified, a new instance is
    * allocated. Returns a reference to the target instance.
    */
    virtual function Chromosome copy(Chromosome to = null);
      return null;
    endfunction : copy

   /*!
    * Saves chromosome to file
    */
    virtual function void save(string filename);
    endfunction : save

   /*!
    * Loads chromosome from file
    */
    virtual function void load(string filename);
    endfunction : load

   /*!
    * Returns fitness value of the object instance. 
    */
    function unsigned int getFitness();
      return fitness;
    endfunction : getFitness

   /*!
    * Mutates the current value of the object instance.
    */
    virtual function Chromosome mutate(int unsigned maxMutations);
      return this;
    endfunction : mutate

   /*!
    * Crossovers the current value of the object instance with the specified 
    * object instance.
    */
    virtual function Chromosome crossover(Chromosome chrom = null);
      return null;
    endfunction : crossover

   /*!
    * Computes relative fitness.
    */
    function void setRelativeFitness(int unsigned popFitness);
      relativeFitness = real'(fitness)/real'(popFitness);
    endfunction : setRelativeFitness

   /*!
    * Get relative fitness.
    */
    function real getRelativeFitness();
      return relativeFitness;
    endfunction : getRelativeFitness

  endclass : Chromosome
  
