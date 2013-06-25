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
     
   populationSize = chrom_seq_cfg.populationSize;  // Size of a population
   selection      = chrom_seq_cfg.selection;       // Selection type 
   maxMutations   = chrom_seq_cfg.maxMutations;    // Maximum number of mutations
   
   alu_chromosome = AluChromosome::type_id::create("alu_chromosome");
     
   while (trans_count < populationSize) begin
     assert($cast(alu_chromosome_c, alu_chromosome.clone));
     // start_item(alu_chromosome_c);
     // alu_chromosome_c.randomize();
     // finish_item(alu_chromosome_c);
     
     // VYPIS CHROMOZOMOV
     uvm_report_info("BODY PHASE", alu_chromosome_c.convert2string());    
     
     // TU BY SOM ICH MALA ULOZIT DO POLA ABY SA S NIMI DALO PRACOVAT
     
     // NEZAVISLE BY SA MALI POSIELAT DO DALSIEHO SEQUENCERA
        
     trans_count++; 
   end
 endtask: body
 
 
 
   
/*! 
 * Post-body - implements closing of output file with transactions
 */ 
 task ChromosomeSequence::post_body;
   uvm_report_info("SCOREBOARD", ":\n\nVERIFICATION ENDED CORRECTLY :)\n\n");
   $stop();
 endtask : post_body
