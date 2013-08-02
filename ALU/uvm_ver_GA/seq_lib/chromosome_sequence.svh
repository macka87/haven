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
   
   ChromosomeArray            chr_array;      // Chromosomes stored into an array
   ChromosomeSequenceConfig   chrom_seq_cfg;  // configuration object
   
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
   
 endclass: ChromosomeSequence
 
 
 
/*! 
 * Constructor - creates ChromosomeSequence object  
 */
 function ChromosomeSequence::new(string name = "ChromosomeSequence");
   super.new(name);
 endfunction: new              



/*! 
 * Body - implements behavior of the transaction
 */ 
 task ChromosomeSequence::body;
   TransactionSequence trans_sequence;     // Transaction Sequence
   int chr_count = 0;
   
   // check configuration for Chromosome Sequence
   if (!uvm_config_db #(ChromosomeSequenceConfig)::get(null, get_full_name(), "ChromosomeSequenceConfig", chrom_seq_cfg)) 
     `uvm_error("BODY", "ChromosomeSequenceConfig doesn't exist!"); 
   
   // configure Population of Chromosomes (Chromosome Sequence)
   configurePopulation(chrom_seq_cfg);  
   
   // get population of Chromosomes from the configuration database
   if (!uvm_config_db #(ChromosomeArray)::get(null, get_full_name(), "ChromosomeArray", chr_array))
     `uvm_error("BODY", "Population of chromosomes doesn't exist!"); 
  
   // send Chromosomes from Population to Driver
   while (chr_count < populationSize) begin
     
     // >>>>> SEND CHROMOSOME TO THE TRANSACTION SEQUENCE >>>>>
     start_item(chr_array.alu_chromosome[chr_count]);
     finish_item(chr_array.alu_chromosome[chr_count]);
       
     // >>>>> GET COVERAGE >>>>>
     
     chr_count++; 
   end
 endtask: body
 
 
 
/*! 
 * configurePopulation - configure Population with data from the configuration object
 */ 
 task ChromosomeSequence::configurePopulation(ChromosomeSequenceConfig chrom_seq_cfg);
   populationSize = chrom_seq_cfg.populationSize;  // Size of a population
   selection      = chrom_seq_cfg.selection;       // Selection type 
   maxMutations   = chrom_seq_cfg.maxMutations;    // Maximum number of mutations
 endtask: configurePopulation