/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    transaction_ga_sequencer.svh
 * Description:  Sequencer Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         13.2.2014
 * ************************************************************************** */

/*!
 * \brief TransactionGASequencer
 * 
 * This class manages random inputs for DUT and sends them to driver.
 */

 class TransactionGASequencer;
    
  /*! 
   * Data Members
   */ 
  
  /*! 
   * Channels
   */   
   mailbox #(AluChromosome)       chromosomeMbx;  
   mailbox #(AluInputTransaction) inputMbx; 
   
  /*!
   * Methods
   */
  
   // User-defined methods
   extern task run();
   extern task configureGATrans(AluChromosome alu_chr, AluGAInputTransaction alu_in_trans);

 endclass: TransactionGASequencer


 
/*! 
 * Generate transactions
 */ 
 task TransactionGASequencer::run();
   AluChromosome alu_chromosome;
   AluGAInputTransaction alu_ga_in_trans, alu_ga_in_trans_c;
   AluInputTransaction alu_in_trans, alu_in_trans_c;
   int cnt = 0;
   int chr_cnt = 0;
   
   //$write("\n\n########## TRANSACTION GA SEQUENCER ##########\n\n");
   
   forever begin
   
     // get chromosome from Population Sequencer
     chromosomeMbx.get(alu_chromosome);   
   
     // create AluGAInputTransaction and AluTransaction
     alu_ga_in_trans = new();
     alu_in_trans = new();
     
     // generate TRANS_COUNT transactions for every chromosome 
     while (cnt < TRANS_COUNT) begin
       
       // clone
       alu_ga_in_trans_c = alu_ga_in_trans.clone();
       alu_in_trans_c = alu_in_trans.clone();    
   
       // configure AluGaInputTransaction using the settings from chromosome
       configureGATrans(alu_chromosome, alu_ga_in_trans_c);
   
       // generate fields in AluGAInputTransaction
       assert(alu_ga_in_trans_c.randomize());
       
       // cast AluGAInputTransaction to AluInputTransaction
       assert($cast(alu_in_trans_c, alu_ga_in_trans_c));
   
       // sent AluInputTransaction using mailbox to driver
       inputMbx.put(alu_in_trans_c);
       
       cnt++;
     end
     
     chr_cnt++;
     cnt = 0;
   end  
   write("TRANSATION SEQUENCER TERMINATING\n"); 
 endtask: run 
 
 
 
/*! 
 * Configure ALU input transactions according to the settings from Chromosome
 */ 
 task TransactionGASequencer::configureGATrans(AluChromosome alu_chr,
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
 endtask: configureGATrans  