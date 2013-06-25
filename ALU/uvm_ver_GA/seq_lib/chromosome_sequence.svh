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
   local Chromosome   population[];    // An array of chromosomes
   local int unsigned fitness;         // Fitness function
   local selection_t  selection;       // Selection type 
   local int unsigned maxMutations;    // Maximum number of mutations
   local real         allsums[];
   
   ChromosomeSequenceConfig   chrom_seq_cfg;  // configuration object
     
  /*!
   * Methods
   */

   // Standard UVM methods
   extern function new(string name = "ChromosomeSequence");
   extern task body();  
   extern task post_body();   
   
   // Own UVM methods
   extern task configurePopulation(ChromosomeSequenceConfig chrom_seq_cfg);
   extern task configureAluChromosome(AluChromosome alu_chromosome, ChromosomeSequenceConfig chrom_seq_cfg);
   
   
   /*extern function void print(string prefix = "");
   extern function void create_chromosome(Chromosome chromBlueprint);
   extern function void save(string fname);
   extern function void load(string fname, Chromosome chromBlueprint);
   extern function int unsigned evaluate();
   extern function void getBestChromosomes(int count = 1, ref Chromosome chrom[]);
   extern function void selectAndReplace(ref Chromosome best_chrom); */ 
 
 endclass: ChromosomeSequence