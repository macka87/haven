/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_ga_input_transaction.svh
 * Description:  Definition of GA input vectors.
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2013 
 * ************************************************************************** */ 

/*!
 * \brief GA Input ALU Transaction
 * 
 * This class represents transaction which contains values of input signals for
 * the DUT.
 */

 class AluGAInputTransaction extends AluInputTransaction;
      
   //! UVM Factory Registration Macro
   `uvm_object_utils(AluGAInputTransaction)
   
  /*! 
   * Data Members
   */
   
   // transactions parameters
   
   // weights of input signals
   byte unsigned movi_values       = 3;   // num. of values for MOVI
   byte unsigned movi_wt[];       
          
   byte unsigned operandA_ranges   = 1;   // num. of ranges for opA
   byte unsigned opA_range_wt[];  
       
   byte unsigned operandB_ranges   = 1;   // num. of ranges for opB
   byte unsigned opB_range_wt[];
   
   byte unsigned operandMEM_ranges = 1;   // num. of ranges for opMEM
   byte unsigned opMEM_range_wt[];
       
   byte unsigned operandIMM_ranges = 1;   // num. of ranges for opIMM
   byte unsigned opIMM_range_wt[];
       
   byte unsigned operation_values  = 16;  // num. of values for OPERATION
   byte unsigned op_range_wt[];  
       
   //! Constraints for randomized values
   
   //! MOVI constraint
   constraint c_movi {
      movi dist { 0 := movi_wt[0],
                  1 := movi_wt[1],
                  2 := movi_wt[2]
                };
   }; 
   
   // !!!!!!!!!!!!! NIE JE GENERICKE, PREROBIT !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
   
   //! REG_A constraint (if range == 1, without constraint)
   constraint c_operandA {
      (operandA_ranges == 2) -> reg_a dist { 
                                  [128:255] := opA_range_wt[0],
                                  [0:127]   := opA_range_wt[1]
                                };
      (operandA_ranges == 3) -> reg_a dist { 
                                  [170:255] := opA_range_wt[0],
                                  [85:169]  := opA_range_wt[1],
                                  [0:84]    := opA_range_wt[2]
                                };                          
      (operandA_ranges == 4) -> reg_a dist { 
                                  [192:255] := opA_range_wt[0],
                                  [128:191] := opA_range_wt[1],
                                  [64:127]  := opA_range_wt[2],
                                  [0:63]    := opA_range_wt[3]
                                }; 
      (operandA_ranges == 5) -> reg_a dist { 
                                  [204:255] := opA_range_wt[0],
                                  [153:203] := opA_range_wt[1],
                                  [102:152] := opA_range_wt[2],
                                  [51:101]  := opA_range_wt[3],
                                  [0:50]    := opA_range_wt[4]
                                }; 
      (operandA_ranges == 6) -> reg_a dist { 
                                  [215:255] := opA_range_wt[0],
                                  [172:214] := opA_range_wt[1],
                                  [129:171] := opA_range_wt[2],
                                  [86:128]  := opA_range_wt[3],
                                  [43:85]   := opA_range_wt[4],
                                  [0:42]    := opA_range_wt[5]
                                };                          
      (operandA_ranges == 7) -> reg_a dist { 
                                  [222:255] := opA_range_wt[0],
                                  [185:221] := opA_range_wt[1],
                                  [148:184] := opA_range_wt[2],
                                  [111:147] := opA_range_wt[3],
                                  [74:110]  := opA_range_wt[4],
                                  [37:73]   := opA_range_wt[5],
                                  [0:36]    := opA_range_wt[6]
                                };                                                    
      (operandA_ranges == 8) -> reg_a dist { 
                                  [224:255] := opA_range_wt[0],
                                  [192:223] := opA_range_wt[1],
                                  [160:191] := opA_range_wt[2],
                                  [128:159] := opA_range_wt[3],
                                  [96:127]  := opA_range_wt[4],
                                  [64:95]   := opA_range_wt[5],
                                  [32:63]   := opA_range_wt[6],
                                  [0:31]    := opA_range_wt[7]
                                };                                                     
   }; 
   
   //! REG_B constraint (if range == 1, without constraint)
   constraint c_operandB {
      (operandB_ranges == 2) -> reg_b dist { 
                                  [128:255] := opB_range_wt[0],
                                  [0:127]   := opB_range_wt[1]
                                };
      (operandB_ranges == 3) -> reg_b dist { 
                                  [170:255] := opB_range_wt[0],
                                  [85:169]  := opB_range_wt[1],
                                  [0:84]    := opB_range_wt[2]
                                };                          
      (operandB_ranges == 4) -> reg_b dist { 
                                  [192:255] := opB_range_wt[0],
                                  [128:191] := opB_range_wt[1],
                                  [64:127]  := opB_range_wt[2],
                                  [0:63]    := opB_range_wt[3]
                                }; 
      (operandB_ranges == 5) -> reg_b dist { 
                                  [204:255] := opB_range_wt[0],
                                  [153:203] := opB_range_wt[1],
                                  [102:152] := opB_range_wt[2],
                                  [51:101]  := opB_range_wt[3],
                                  [0:50]    := opB_range_wt[4]
                                }; 
      (operandB_ranges == 6) -> reg_b dist { 
                                  [215:255] := opB_range_wt[0],
                                  [172:214] := opB_range_wt[1],
                                  [129:171] := opB_range_wt[2],
                                  [86:128]  := opB_range_wt[3],
                                  [43:85]   := opB_range_wt[4],
                                  [0:42]    := opB_range_wt[5]
                                };                          
      (operandB_ranges == 7) -> reg_b dist { 
                                  [222:255] := opB_range_wt[0],
                                  [185:221] := opB_range_wt[1],
                                  [148:184] := opB_range_wt[2],
                                  [111:147] := opB_range_wt[3],
                                  [74:110]  := opB_range_wt[4],
                                  [37:73]   := opB_range_wt[5],
                                  [0:36]    := opB_range_wt[6]
                                };                                                    
      (operandB_ranges == 8) -> reg_b dist { 
                                  [224:255] := opB_range_wt[0],
                                  [192:223] := opB_range_wt[1],
                                  [160:191] := opB_range_wt[2],
                                  [128:159] := opB_range_wt[3],
                                  [96:127]  := opB_range_wt[4],
                                  [64:95]   := opB_range_wt[5],
                                  [32:63]   := opB_range_wt[6],
                                  [0:31]    := opB_range_wt[7]
                                };                                                     
   }; 
   
   //! MEM constraint (if range == 1, without constraint)
   constraint c_operandMEM {
      (operandMEM_ranges == 2) -> mem dist { 
                                  [128:255] := opMEM_range_wt[0],
                                  [0:127]   := opMEM_range_wt[1]
                                };
      (operandMEM_ranges == 3) -> mem dist { 
                                  [170:255] := opMEM_range_wt[0],
                                  [85:169]  := opMEM_range_wt[1],
                                  [0:84]    := opMEM_range_wt[2]
                                };                          
      (operandMEM_ranges == 4) -> mem dist { 
                                  [192:255] := opMEM_range_wt[0],
                                  [128:191] := opMEM_range_wt[1],
                                  [64:127]  := opMEM_range_wt[2],
                                  [0:63]    := opMEM_range_wt[3]
                                }; 
      (operandMEM_ranges == 5) -> mem dist { 
                                  [204:255] := opMEM_range_wt[0],
                                  [153:203] := opMEM_range_wt[1],
                                  [102:152] := opMEM_range_wt[2],
                                  [51:101]  := opMEM_range_wt[3],
                                  [0:50]    := opMEM_range_wt[4]
                                }; 
      (operandMEM_ranges == 6) -> mem dist { 
                                  [215:255] := opMEM_range_wt[0],
                                  [172:214] := opMEM_range_wt[1],
                                  [129:171] := opMEM_range_wt[2],
                                  [86:128]  := opMEM_range_wt[3],
                                  [43:85]   := opMEM_range_wt[4],
                                  [0:42]    := opMEM_range_wt[5]
                                };                          
      (operandMEM_ranges == 7) -> mem dist { 
                                  [222:255] := opMEM_range_wt[0],
                                  [185:221] := opMEM_range_wt[1],
                                  [148:184] := opMEM_range_wt[2],
                                  [111:147] := opMEM_range_wt[3],
                                  [74:110]  := opMEM_range_wt[4],
                                  [37:73]   := opMEM_range_wt[5],
                                  [0:36]    := opMEM_range_wt[6]
                                };                                                    
      (operandMEM_ranges == 8) -> mem dist { 
                                  [224:255] := opMEM_range_wt[0],
                                  [192:223] := opMEM_range_wt[1],
                                  [160:191] := opMEM_range_wt[2],
                                  [128:159] := opMEM_range_wt[3],
                                  [96:127]  := opMEM_range_wt[4],
                                  [64:95]   := opMEM_range_wt[5],
                                  [32:63]   := opMEM_range_wt[6],
                                  [0:31]    := opMEM_range_wt[7]
                                };                                                     
   };
   
   //! IMM constraint (if range == 1, without constraint)
   constraint c_operandIMM {
      (operandIMM_ranges == 2) -> imm dist { 
                                  [128:255] := opIMM_range_wt[0],
                                  [0:127]   := opIMM_range_wt[1]
                                };
      (operandIMM_ranges == 3) -> imm dist { 
                                  [170:255] := opIMM_range_wt[0],
                                  [85:169]  := opIMM_range_wt[1],
                                  [0:84]    := opIMM_range_wt[2]
                                };                          
      (operandIMM_ranges == 4) -> imm dist { 
                                  [192:255] := opIMM_range_wt[0],
                                  [128:191] := opIMM_range_wt[1],
                                  [64:127]  := opIMM_range_wt[2],
                                  [0:63]    := opIMM_range_wt[3]
                                }; 
      (operandIMM_ranges == 5) -> imm dist { 
                                  [204:255] := opIMM_range_wt[0],
                                  [153:203] := opIMM_range_wt[1],
                                  [102:152] := opIMM_range_wt[2],
                                  [51:101]  := opIMM_range_wt[3],
                                  [0:50]    := opIMM_range_wt[4]
                                }; 
      (operandIMM_ranges == 6) -> imm dist { 
                                  [215:255] := opIMM_range_wt[0],
                                  [172:214] := opIMM_range_wt[1],
                                  [129:171] := opIMM_range_wt[2],
                                  [86:128]  := opIMM_range_wt[3],
                                  [43:85]   := opIMM_range_wt[4],
                                  [0:42]    := opIMM_range_wt[5]
                                };                          
      (operandIMM_ranges == 7) -> imm dist { 
                                  [222:255] := opIMM_range_wt[0],
                                  [185:221] := opIMM_range_wt[1],
                                  [148:184] := opIMM_range_wt[2],
                                  [111:147] := opIMM_range_wt[3],
                                  [74:110]  := opIMM_range_wt[4],
                                  [37:73]   := opIMM_range_wt[5],
                                  [0:36]    := opIMM_range_wt[6]
                                };                                                    
      (operandIMM_ranges == 8) -> imm dist { 
                                  [224:255] := opIMM_range_wt[0],
                                  [192:223] := opIMM_range_wt[1],
                                  [160:191] := opIMM_range_wt[2],
                                  [128:159] := opIMM_range_wt[3],
                                  [96:127]  := opIMM_range_wt[4],
                                  [64:95]   := opIMM_range_wt[5],
                                  [32:63]   := opIMM_range_wt[6],
                                  [0:31]    := opIMM_range_wt[7]
                                };                                                     
   };
    
   //! OPERATION constraint
   constraint c_op {
             op dist { 0 := op_range_wt[0],
                       1 := op_range_wt[1],
                       2 := op_range_wt[2],
                       3 := op_range_wt[3],
                       4 := op_range_wt[4],
                       5 := op_range_wt[5],
                       6 := op_range_wt[6],
                       7 := op_range_wt[7],
                       8 := op_range_wt[8],
                       9 := op_range_wt[9],
                       10 := op_range_wt[10],
                       11 := op_range_wt[11],
                       12 := op_range_wt[12],
                       13 := op_range_wt[13],
                       14 := op_range_wt[14],
                       15 := op_range_wt[15]
                     };
   }; 
   
   //! --- RANDOMIZATION OF DELAY PARAMETERS ---
   byte unsigned delay_ranges;        // num. of delay ranges
   byte unsigned delay_range_wt[];     
   
   //! --- CONSTRAINTS OF DELAY PARAMETERS ---
   
   //! DELAY constraint (if range == 1, without constraint)
   constraint c_delay {
      (delay_ranges == 2) -> btDelay dist { 
                               [8:15]  := delay_range_wt[0],
                               [0:7]   := delay_range_wt[1]
                             };
      (delay_ranges == 3) -> btDelay dist { 
                               [10:15] := delay_range_wt[0],
                               [5:9]   := delay_range_wt[1],
                               [0:4]   := delay_range_wt[2]
                             };                              
      (delay_ranges == 4) -> btDelay dist { 
                               [12:15] := delay_range_wt[0],
                               [8:11]  := delay_range_wt[1],
                               [4:7]   := delay_range_wt[2],
                               [0:3]   := delay_range_wt[3]
                             }; 
   };   
  
  
  /*!
   * Methods
   */ 
    
   // Standard UVM methods
   extern function new(string name = "AluGAInputTransaction");
   extern function void do_copy(uvm_object rhs); 
   
 endclass: AluGAInputTransaction
 
 
 
/*! 
 * Constructor - creates AluGAInputTransaction object  
 */
 function AluGAInputTransaction::new(string name = "AluGAInputTransaction");
   super.new(name);
 endfunction: new
 
 
 
/*! 
 * Implementation of the do_copy() virtual function.
 */
 function void AluGAInputTransaction::do_copy(uvm_object rhs);
   AluGAInputTransaction alu_trans;
   
   if(!$cast(alu_trans, rhs)) begin
     uvm_report_error("do_copy:", "$cast failed!");
     return;
   end
   
   super.do_copy(rhs);
   
   reg_a = alu_trans.reg_a;
   reg_b = alu_trans.reg_b;
   mem   = alu_trans.mem;
   imm   = alu_trans.imm;
   op    = alu_trans.op;
   movi  = alu_trans.movi;
   
 endfunction: do_copy  