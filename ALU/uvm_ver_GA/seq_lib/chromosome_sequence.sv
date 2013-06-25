/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    chromosome_sequence.sv
 * Description:  Chromosome Sequence Class
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         24.6.2013 
 * ************************************************************************** */

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
   AluChromosome alu_chromosome;
   AluChromosome alu_chromosome_c;
   int trans_count = 0;
   
   
   // check configuration for Chromosome Sequence
   if (!uvm_config_db #(ChromosomeSequenceConfig)::get(null, get_full_name(), "ChromosomeSequenceConfig", chrom_seq_cfg)) 
     `uvm_error("BODY", "ChromosomeSequenceConfig doesn't exist!"); 
   
   // configure Population of Chromosomes (Chromosome Sequence)
   configurePopulation(chrom_seq_cfg);  
   
   // create ALU Chromosome
   alu_chromosome = AluChromosome::type_id::create("alu_chromosome");
   
   // configure ALU Chromosome
   configureAluChromosome(alu_chromosome, chrom_seq_cfg);
     
   // generate Chromosomes in Population
   while (trans_count < populationSize) begin
         
     assert($cast(alu_chromosome_c, alu_chromosome.clone));
     
     // start_item(alu_chromosome_c);
     // finish_item(alu_chromosome_c);
     
     uvm_report_info("BODY PHASE", alu_chromosome_c.convert2string());
     
     // RANDOM GENERATION OF CHROMOSOME
     assert(alu_chromosome_c.randomize());     
     
     // PRINT CHROMOSOME
     alu_chromosome_c.print("ALU Chromosome");    
     
     // TU BY SOM ICH MALA ULOZIT DO POLA ABY SA S NIMI DALO PRACOVAT
     
     // NEZAVISLE BY SA MALI POSIELAT DO DALSIEHO SEQUENCERA
        
     trans_count++; 
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
 
 
 
/*! 
 * configureAluChromosome - configure ALU Chromosome with data from the configuration object
 */ 
 task ChromosomeSequence::configureAluChromosome(AluChromosome alu_chromosome, ChromosomeSequenceConfig chrom_seq_cfg);
   alu_chromosome.movi_values           = chrom_seq_cfg.movi_values;
   alu_chromosome.operation_values      = chrom_seq_cfg.operation_values;
   alu_chromosome.delay_rangesMin       = chrom_seq_cfg.delay_rangesMin;         
   alu_chromosome.delay_rangesMax       = chrom_seq_cfg.delay_rangesMax;
   alu_chromosome.operandA_rangesMin    = chrom_seq_cfg.operandA_rangesMin;
   alu_chromosome.operandA_rangesMax    = chrom_seq_cfg.operandA_rangesMax;
   alu_chromosome.operandB_rangesMin    = chrom_seq_cfg.operandB_rangesMin;
   alu_chromosome.operandB_rangesMax    = chrom_seq_cfg.operandB_rangesMax;  
   alu_chromosome.operandMEM_rangesMin  = chrom_seq_cfg.operandMEM_rangesMin;
   alu_chromosome.operandMEM_rangesMax  = chrom_seq_cfg.operandMEM_rangesMax;  
   alu_chromosome.operandIMM_rangesMin  = chrom_seq_cfg.operandIMM_rangesMin;
   alu_chromosome.operandIMM_rangesMax  = chrom_seq_cfg.operandIMM_rangesMax;
   
   alu_chromosome.length = alu_chromosome.operandA_rangesMax + alu_chromosome.operandB_rangesMax + 
                           alu_chromosome.operandMEM_rangesMax + alu_chromosome.operandIMM_rangesMax + 
                           alu_chromosome.delay_rangesMax + alu_chromosome.movi_values + 
                           alu_chromosome.operation_values;
 endtask: configureAluChromosome 
 
 
   
/*! 
 * Post-body - implements closing of output file with transactions
 */ 
 task ChromosomeSequence::post_body;
   uvm_report_info("SCOREBOARD", ":\n\nVERIFICATION ENDED CORRECTLY :)\n\n");
   $stop();
 endtask : post_body
