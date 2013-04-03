/* *****************************************************************************
 * Project Name: HAVEN - GA
 * File Name:    chromosome.sv
 * Description:  Genetic Algorithm Chromosome Class
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         2.4.2013 
 * ************************************************************************** */

/*!
 * \brief Chromosome
 * 
 * This class defines the structure of the chromosome and basic operations 
 * performed with chromosomes.
 */

 class Chromosome extends ovm_sequence_item;
  
    // registration of component 
    `ovm_object_utils(Chromosome)
  
   /*
    * Local Class Atributes
    */
    local int          length;                 // length of chromosome
    local int          chromosome_parts;       // uniform parts of chromosome
    local int unsigned fitness         = 0;    // fitness function
    local real         relativeFitness = 0;    // relative fitness function
    
    local rand byte unsigned chromosome[];     // chromosome

   /*! 
    * Constructor
    *
    * \param name - transaction instance name
    */
    function new (string name = "");
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
    * Prints chromosome
    */
    virtual function void print();
    endfunction : print  
  
   /*
    * Local Class Methods
    *
   
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
    * Read chromosome
    */
    function void getChromosomes(byte unsigned chromosome[]);
      chromosome[] = this.chromosome[];
    endfunction : getChromosomes 

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
  
