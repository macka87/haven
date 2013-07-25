/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    transaction_sequence.svh
 * Description:  UVM Sequence for ALU Transactions 
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2013
 * ************************************************************************** */

/*!
 * \brief TransactionSequence
 * 
 * This class represents UVM sequence of random input transactions for ALU.
 */
 
 class TransactionSequence extends uvm_sequence #(AluInputTransaction);

   //! UVM Factory Registration Macro
   `uvm_object_utils(TransactionSequence)
  
  /*! 
   * Data Members
   */ 
   
   int trans_count;
   int populationSize;
   TransactionSequenceConfig transaction_sequence_cfg; 
   
  /*! 
   * Component Members
   */ 
   
   Population pop_sequencer;
   
  /*!
   * Methods
   */
  
   // Standard UVM methods
   extern function new(string name = "TransactionSequence");
   extern task body();  
   
   // Own UVM methods
   extern task configureSequence(TransactionSequenceConfig transaction_sequence_cfg);
   extern task configureTrans(AluChromosome alu_chr, AluGAInputTransaction alu_in_trans);
      
 endclass: TransactionSequence
 
 
 
/*! 
 * Constructor - creates TransactionSequence object  
 */
 function TransactionSequence::new(string name = "TransactionSequence");
   super.new(name);
 endfunction: new   



/*! 
 * Body - implements behavior of the transaction
 */ 
 task TransactionSequence::body;
   Chromosome            chr;
   AluChromosome         alu_chr;
   AluGAInputTransaction alu_ga_in_trans, alu_ga_in_trans_c;
   AluInputTransaction   alu_in_trans, alu_in_trans_c;
   int                   cnt = 0;
   int                   chr_cnt = 0;
   
   // check configuration for Transaction Sequence
   if (!uvm_config_db #(TransactionSequenceConfig)::get(null, get_full_name(), "TransactionSequenceConfig", transaction_sequence_cfg)) 
     `uvm_error("BODY", "TransactionSequenceConfig doesn't exist!"); 
   
   // configure Sequence of Transactions 
   configureSequence(transaction_sequence_cfg); 
     
   // receives Chromosomes in Population
   while (chr_cnt < populationSize) begin
     
     // get Chromosome from Population Sequencer
     pop_sequencer.seq_item_export.get_next_item(chr);
     assert($cast(alu_chr, chr));
     
     alu_ga_in_trans = AluGAInputTransaction::type_id::create();
     
     cnt = 0;
     
     // generate transactions for every chromosome 
     while (cnt < trans_count) begin
       assert($cast(alu_ga_in_trans_c, alu_ga_in_trans.clone)); 
      
       start_item(alu_ga_in_trans_c);
       configureTrans(alu_chr, alu_ga_in_trans_c);
       assert(alu_ga_in_trans_c.randomize());
       //alu_ga_in_trans_c.print("TRANS_SEQUENCE: ALU TRANSACTION");
       finish_item(alu_ga_in_trans_c);
       
       cnt++; 
     end 
     
     // let Population Sequencer know about the chromosome processing 
     pop_sequencer.item_done();
     chr_cnt++;
   end
 endtask: body



 /*! 
 * configureSequence - configure Sequence with data from the configuration object
 */ 
 task TransactionSequence::configureSequence(TransactionSequenceConfig transaction_sequence_cfg);
   trans_count = transaction_sequence_cfg.trans_count;
   populationSize = transaction_sequence_cfg.populationSize;  // Size of a population
 endtask: configureSequence
 


/*! 
 * Configure ALU input transactions according to the settings from Chromosome
 */ 
 task TransactionSequence::configureTrans(AluChromosome alu_chr,
                                          AluGAInputTransaction alu_in_trans
                                          );
   int offset = 0;
   
   // MOVI
   alu_in_trans.movi_values = alu_chr.movi_values;
   alu_in_trans.movi_wt = new[alu_chr.movi_values];
   for (int j=0; j<alu_chr.movi_values; j++) 
     alu_in_trans.movi_wt[j] = alu_chr.chromosome[offset++];
   
   // OPERAND A  
   alu_in_trans.operandA_ranges = alu_chr.operandA_ranges;
   alu_in_trans.opA_range_wt = new[alu_chr.operandA_ranges];
   for (int j=0; j<8; j++) begin
     if (j < alu_in_trans.operandA_ranges) 
       alu_in_trans.opA_range_wt[j] = alu_chr.chromosome[offset++]; 
     else offset++;
   end 
   
   // OPERAND B  
   alu_in_trans.operandB_ranges = alu_chr.operandB_ranges;
   alu_in_trans.opB_range_wt = new[alu_chr.operandB_ranges];
   for (int j=0; j<8; j++) begin
     if (j < alu_in_trans.operandB_ranges) 
       alu_in_trans.opB_range_wt[j] = alu_chr.chromosome[offset++]; 
     else offset++;
   end
   
   // OPERAND MEM  
   alu_in_trans.operandMEM_ranges = alu_chr.operandMEM_ranges;
   alu_in_trans.opMEM_range_wt = new[alu_chr.operandMEM_ranges];
   for (int j=0; j<8; j++) begin
     if (j < alu_in_trans.operandA_ranges) 
       alu_in_trans.opMEM_range_wt[j] = alu_chr.chromosome[offset++]; 
     else offset++;
   end
   
   // OPERAND IMM  
   alu_in_trans.operandIMM_ranges = alu_chr.operandIMM_ranges;
   alu_in_trans.opIMM_range_wt = new[alu_chr.operandIMM_ranges];
   for (int j=0; j<8; j++) begin
     if (j < alu_in_trans.operandIMM_ranges) 
       alu_in_trans.opIMM_range_wt[j] = alu_chr.chromosome[offset++]; 
     else offset++;
   end   
        
   // OPERATION  
   alu_in_trans.operation_values = 16;
   alu_in_trans.op_range_wt = new[16];
   for (int j=0; j<16; j++) 
     alu_in_trans.op_range_wt[j] = alu_chr.chromosome[offset++];  
    
   // DELAY         
   alu_in_trans.delay_ranges = alu_chr.delay_ranges;
   alu_in_trans.delay_range_wt = new[alu_in_trans.delay_ranges];
   for (int j=0; j<8; j++) begin
     if (j < alu_in_trans.delay_ranges) 
       alu_in_trans.delay_range_wt[j] = alu_chr.chromosome[offset++];
     else offset++;
   end    
 endtask: configureTrans