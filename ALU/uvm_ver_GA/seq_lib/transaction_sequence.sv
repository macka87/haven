/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    transaction_sequence.sv
 * Description:  uVM Sequence for ALU Transactions 
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2013
 * ************************************************************************** */

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
   AluGAInputTransaction alu_in_trans;
   int                   cnt = 0;
   
    $write("TransactionSequence::body\n");
   
   // check configuration for Transaction Sequence
   if (!uvm_config_db #(TransactionSequenceConfig)::get(null, get_full_name(), "TransactionSequenceConfig", transaction_sequence_cfg)) 
     `uvm_error("BODY", "TransactionSequenceConfig doesn't exist!"); 
   
   // configure Sequence of Transactions 
   configureSequence(transaction_sequence_cfg); 
     
   forever begin
     // get Chromosome from Population Sequencer
     pop_sequencer.get_next_item(chr);
     assert($cast(alu_chr, chr));
     alu_chr.print("TransactionSequence: ALU Chromosome");
     
     // generate transactions for every chromosome 
     while (cnt < trans_count) begin
       $write("cnt: %d\n", cnt);
       $write("trans_count: %d\n", trans_count);
       alu_in_trans = AluGAInputTransaction::type_id::create();
       //start_item(alu_in_trans);
       configureTrans(alu_chr, alu_in_trans);
       assert(alu_in_trans.randomize());
       alu_in_trans.print("ALU TRANSACTION");
       //finish_item(alu_in_trans);
       cnt++; 
     end 
     
     // let Population Sequencer know about the chromosome processing 
     pop_sequencer.item_done();
   end
 endtask: body



 /*! 
 * configureSequence - configure Sequence with data from the configuration object
 */ 
 task TransactionSequence::configureSequence(TransactionSequenceConfig transaction_sequence_cfg);
   trans_count = transaction_sequence_cfg.trans_count;
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
 endtask : configureTrans


   
/*! 
 * Post-body - implements closing of output file with transactions
 */ 
 task TransactionSequence::post_body;
   uvm_report_info("SCOREBOARD", ":\n\nVERIFICATION ENDED CORRECTLY :)\n\n");
   $stop();
 endtask : post_body

