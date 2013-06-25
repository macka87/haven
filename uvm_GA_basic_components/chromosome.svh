/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    chromosome.svh
 * Description:  Genetic Algorithm Chromosome Class
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         10.5.2013 
 * ************************************************************************** */

/*!
 * \brief Chromosome
 * 
 * This class defines the structure of the chromosome and basic operations 
 * performed with chromosomes.
 */

 class Chromosome extends uvm_sequence_item;
  
   //! UVM Factory Registration Macro
   `uvm_object_utils(Chromosome)
   
  /*! 
   * Data Members
   */  
   
   int          length;             // length of chromosome
   int          chromosome_parts;   // uniform parts of chromosome
   int unsigned fitness;            // fitness function
   real         relativeFitness;    // relative fitness function
   rand byte unsigned chromosome[]; // chromosome
   
   ChromosomeConfig  chromosome_cfg;          // configuration object

  /*!
   * Methods
   */

   // Standard UVM methods
   extern function new(string name = "Chromosome");
   
   // Own UVM methods
   extern function void save(string filename);
   extern function void load(string filename);
   extern function void getChromosomes(byte unsigned chromosome[]);
   extern function unsigned int getFitness();
   extern function Chromosome mutate(int unsigned maxMutations);
   extern function Chromosome crossover(Chromosome chrom = null); 
   extern function void setRelativeFitness(int unsigned popFitness);
   extern function real getRelativeFitness();

 endclass : Chromosome
  
