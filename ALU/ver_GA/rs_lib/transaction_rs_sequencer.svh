/* *****************************************************************************
 * Project Name: Random Search for ALU
 * File Name:    transaction_rs_sequencer.svh
 * Description:  Sequencer Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         17.6.2014
 * ************************************************************************** */

/*!
 * \brief TransactionRSSequencer
 * 
 * This class manages random inputs for DUT and sends them to driver.
 */

 class TransactionRSSequencer;
    
  /*! 
   * Data Members
   */ 
   bit enabled;
     
  /*! 
   * Channels
   */   
   mailbox #(AluInputTransaction) inputMbx; 
   
  /*!
   * Methods
   */
  
   // User-defined methods
   extern function new();
   extern task run();
   extern task createConfiguration(AluChromosome random_config);
   extern task configureRSTrans(AluChromosome alu_chr, AluRSInputTransaction alu_in_trans);

 endclass: TransactionRSSequencer



/*! 
 *  Constructor
 */
 function TransactionRSSequencer::new();
   enabled = 1;
 endfunction: new 
 
 
 
/*! 
 * Generate transactions
 */ 
 task TransactionRSSequencer::run();
   AluRSInputTransaction alu_rs_in_trans, alu_rs_in_trans_c;
   AluInputTransaction alu_in_trans, alu_in_trans_c;
   AluChromosome random_config, random_config_c;
   int cnt = 0;
      
   //$write("\n\n########## TRANSACTION RS SEQUENCER ##########\n\n");
   
   random_config = new();
   createConfiguration(random_config);   
   
   alu_rs_in_trans = new();
   alu_in_trans = new();
   
   forever begin
     
     // clone
     alu_rs_in_trans_c = alu_rs_in_trans.clone();
     alu_in_trans_c = alu_in_trans.clone(); 
     
     // create new configuration for random search 
     if (cnt % TRANS_RS == 0) begin
       
       random_config_c =  random_config.clone();
       
       // randomize chromosome
       assert(random_config_c.randomize()); 
       
       //random_config_c.print(0, 1); 
     end  
     
     // configure AluRSInputTransaction using the settings from configuration
     configureRSTrans(random_config_c, alu_rs_in_trans_c);   
   
     // generate fields in AluRSnputTransaction
     assert(alu_rs_in_trans_c.randomize());
       
     // cast AluRSInputTransaction to AluInputTransaction
     assert($cast(alu_in_trans_c, alu_rs_in_trans_c));
   
     // sent AluInputTransaction using mailbox to driver
     inputMbx.put(alu_in_trans_c);
             
     cnt++;
   end
     
   cnt = 0;
     
   wait(!enabled);
   
   $write("RS TRANSATION SEQUENCER TERMINATING\n"); 
 endtask: run 
 

/*
 *  Create new configuration for random search
 */ 
 task TransactionRSSequencer::createConfiguration(AluChromosome random_config);
   random_config.movi_values           = 3;   // num. of values for MOVI
   random_config.operation_values      = 16;  // num. of values for OPERATION
   random_config.delay_rangesMin       = DELAY_RANGES_MIN;         
   random_config.delay_rangesMax       = DELAY_RANGES_MAX;
   random_config.operandA_rangesMin    = OPERAND_A_RANGES_MIN;
   random_config.operandA_rangesMax    = OPERAND_A_RANGES_MAX;
   random_config.operandB_rangesMin    = OPERAND_B_RANGES_MIN;
   random_config.operandB_rangesMax    = OPERAND_B_RANGES_MAX;  
   random_config.operandMEM_rangesMin  = OPERAND_MEM_RANGES_MIN;
   random_config.operandMEM_rangesMax  = OPERAND_MEM_RANGES_MAX;  
   random_config.operandIMM_rangesMin  = OPERAND_IMM_RANGES_MIN;
   random_config.operandIMM_rangesMax  = OPERAND_IMM_RANGES_MAX;
   
   // !!! maximal length
   random_config.length = random_config.operandA_rangesMax + random_config.operandB_rangesMax + 
                          random_config.operandMEM_rangesMax + random_config.operandIMM_rangesMax + 
                          random_config.delay_rangesMax + random_config.movi_values + 
                          random_config.operation_values;
                           
   random_config.chromosome_parts     = 7;          
  
 endtask: createConfiguration

/*! 
 * Configure ALU input transactions according to the settings from configuration
 */ 
 task TransactionRSSequencer::configureRSTrans(AluChromosome alu_chr,
                                               AluRSInputTransaction alu_in_trans
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
 endtask: configureRSTrans  