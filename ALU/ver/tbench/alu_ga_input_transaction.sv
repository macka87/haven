/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    alu_ga_input_transaction.sv
 * Description:  Definition of input vectors (transactions)
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2012 
 * ************************************************************************** */ 

class ALUInGATransaction #(pDataWidth = 8) extends ALUInTransaction #(pDataWidth);
      
   /*
    * Public Class Atributes
    */
   
   //! --- RANDOMIZATION OF TRANSACTION PARAMETERS ---
   
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
       
   //! --- CONSTRAINTS OF SIGNAL VALUES ---
   
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
      (operandA_ranges == 2) -> operandA dist { 
                                  [128:255] := opA_range_wt[0],
                                  [0:127]   := opA_range_wt[1]
                                };
      (operandA_ranges == 3) -> operandA dist { 
                                  [170:255] := opA_range_wt[0],
                                  [85:169]  := opA_range_wt[1],
                                  [0:84]    := opA_range_wt[2]
                                };                          
      (operandA_ranges == 4) -> operandA dist { 
                                  [192:255] := opA_range_wt[0],
                                  [128:191] := opA_range_wt[1],
                                  [64:127]  := opA_range_wt[2],
                                  [0:63]    := opA_range_wt[3]
                                }; 
      (operandA_ranges == 5) -> operandA dist { 
                                  [204:255] := opA_range_wt[0],
                                  [153:203] := opA_range_wt[1],
                                  [102:152] := opA_range_wt[2],
                                  [51:101]  := opA_range_wt[3],
                                  [0:50]    := opA_range_wt[4]
                                }; 
      (operandA_ranges == 6) -> operandA dist { 
                                  [215:255] := opA_range_wt[0],
                                  [172:214] := opA_range_wt[1],
                                  [129:171] := opA_range_wt[2],
                                  [86:128]  := opA_range_wt[3],
                                  [43:85]   := opA_range_wt[4],
                                  [0:42]    := opA_range_wt[5]
                                };                          
      (operandA_ranges == 7) -> operandA dist { 
                                  [222:255] := opA_range_wt[0],
                                  [185:221] := opA_range_wt[1],
                                  [148:184] := opA_range_wt[2],
                                  [111:147] := opA_range_wt[3],
                                  [74:110]  := opA_range_wt[4],
                                  [37:73]   := opA_range_wt[5],
                                  [0:36]    := opA_range_wt[6]
                                };                                                    
      (operandA_ranges == 8) -> operandA dist { 
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
      (operandB_ranges == 2) -> operandB dist { 
                                  [128:255] := opB_range_wt[0],
                                  [0:127]   := opB_range_wt[1]
                                };
      (operandB_ranges == 3) -> operandB dist { 
                                  [170:255] := opB_range_wt[0],
                                  [85:169]  := opB_range_wt[1],
                                  [0:84]    := opB_range_wt[2]
                                };                          
      (operandB_ranges == 4) -> operandB dist { 
                                  [192:255] := opB_range_wt[0],
                                  [128:191] := opB_range_wt[1],
                                  [64:127]  := opB_range_wt[2],
                                  [0:63]    := opB_range_wt[3]
                                }; 
      (operandB_ranges == 5) -> operandB dist { 
                                  [204:255] := opB_range_wt[0],
                                  [153:203] := opB_range_wt[1],
                                  [102:152] := opB_range_wt[2],
                                  [51:101]  := opB_range_wt[3],
                                  [0:50]    := opB_range_wt[4]
                                }; 
      (operandB_ranges == 6) -> operandB dist { 
                                  [215:255] := opB_range_wt[0],
                                  [172:214] := opB_range_wt[1],
                                  [129:171] := opB_range_wt[2],
                                  [86:128]  := opB_range_wt[3],
                                  [43:85]   := opB_range_wt[4],
                                  [0:42]    := opB_range_wt[5]
                                };                          
      (operandB_ranges == 7) -> operandB dist { 
                                  [222:255] := opB_range_wt[0],
                                  [185:221] := opB_range_wt[1],
                                  [148:184] := opB_range_wt[2],
                                  [111:147] := opB_range_wt[3],
                                  [74:110]  := opB_range_wt[4],
                                  [37:73]   := opB_range_wt[5],
                                  [0:36]    := opB_range_wt[6]
                                };                                                    
      (operandB_ranges == 8) -> operandB dist { 
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
      (operandMEM_ranges == 2) -> operandMEM dist { 
                                  [128:255] := opMEM_range_wt[0],
                                  [0:127]   := opMEM_range_wt[1]
                                };
      (operandMEM_ranges == 3) -> operandMEM dist { 
                                  [170:255] := opMEM_range_wt[0],
                                  [85:169]  := opMEM_range_wt[1],
                                  [0:84]    := opMEM_range_wt[2]
                                };                          
      (operandMEM_ranges == 4) -> operandMEM dist { 
                                  [192:255] := opMEM_range_wt[0],
                                  [128:191] := opMEM_range_wt[1],
                                  [64:127]  := opMEM_range_wt[2],
                                  [0:63]    := opMEM_range_wt[3]
                                }; 
      (operandMEM_ranges == 5) -> operandMEM dist { 
                                  [204:255] := opMEM_range_wt[0],
                                  [153:203] := opMEM_range_wt[1],
                                  [102:152] := opMEM_range_wt[2],
                                  [51:101]  := opMEM_range_wt[3],
                                  [0:50]    := opMEM_range_wt[4]
                                }; 
      (operandMEM_ranges == 6) -> operandMEM dist { 
                                  [215:255] := opMEM_range_wt[0],
                                  [172:214] := opMEM_range_wt[1],
                                  [129:171] := opMEM_range_wt[2],
                                  [86:128]  := opMEM_range_wt[3],
                                  [43:85]   := opMEM_range_wt[4],
                                  [0:42]    := opMEM_range_wt[5]
                                };                          
      (operandMEM_ranges == 7) -> operandMEM dist { 
                                  [222:255] := opMEM_range_wt[0],
                                  [185:221] := opMEM_range_wt[1],
                                  [148:184] := opMEM_range_wt[2],
                                  [111:147] := opMEM_range_wt[3],
                                  [74:110]  := opMEM_range_wt[4],
                                  [37:73]   := opMEM_range_wt[5],
                                  [0:36]    := opMEM_range_wt[6]
                                };                                                    
      (operandMEM_ranges == 8) -> operandMEM dist { 
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
      (operandIMM_ranges == 2) -> operandIMM dist { 
                                  [128:255] := opIMM_range_wt[0],
                                  [0:127]   := opIMM_range_wt[1]
                                };
      (operandIMM_ranges == 3) -> operandIMM dist { 
                                  [170:255] := opIMM_range_wt[0],
                                  [85:169]  := opIMM_range_wt[1],
                                  [0:84]    := opIMM_range_wt[2]
                                };                          
      (operandIMM_ranges == 4) -> operandIMM dist { 
                                  [192:255] := opIMM_range_wt[0],
                                  [128:191] := opIMM_range_wt[1],
                                  [64:127]  := opIMM_range_wt[2],
                                  [0:63]    := opIMM_range_wt[3]
                                }; 
      (operandIMM_ranges == 5) -> operandIMM dist { 
                                  [204:255] := opIMM_range_wt[0],
                                  [153:203] := opIMM_range_wt[1],
                                  [102:152] := opIMM_range_wt[2],
                                  [51:101]  := opIMM_range_wt[3],
                                  [0:50]    := opIMM_range_wt[4]
                                }; 
      (operandIMM_ranges == 6) -> operandIMM dist { 
                                  [215:255] := opIMM_range_wt[0],
                                  [172:214] := opIMM_range_wt[1],
                                  [129:171] := opIMM_range_wt[2],
                                  [86:128]  := opIMM_range_wt[3],
                                  [43:85]   := opIMM_range_wt[4],
                                  [0:42]    := opIMM_range_wt[5]
                                };                          
      (operandIMM_ranges == 7) -> operandIMM dist { 
                                  [222:255] := opIMM_range_wt[0],
                                  [185:221] := opIMM_range_wt[1],
                                  [148:184] := opIMM_range_wt[2],
                                  [111:147] := opIMM_range_wt[3],
                                  [74:110]  := opIMM_range_wt[4],
                                  [37:73]   := opIMM_range_wt[5],
                                  [0:36]    := opIMM_range_wt[6]
                                };                                                    
      (operandIMM_ranges == 8) -> operandIMM dist { 
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
      operation dist { 0 := op_range_wt[0],
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
    * Function displays the current value of the transaction or data described
    * by this instance in a human-readable format on the standard output.
    *
    * \param prefix - transaction type
    */
    virtual function void display(string prefix = "");
      if (prefix != "")
       begin
         $write("---------------------------------------------------------\n");
         $write("-- %s\n",prefix);
         $write("---------------------------------------------------------\n");
       end
       
       $write("GA transaction\n");  
       
       $write("operandA: %d\n", operandA);  
       $write("operandB: %d\n", operandB); 
       $write("operandMEM: %d\n", operandMEM); 
       $write("operandIMM: %d\n", operandIMM); 
       
       priority case (movi) 
         2'b00 : $write("MOVI: REGISTER B\n");
         2'b01 : $write("MOVI: MEMORY OPERAND\n");
         2'b10 : $write("MOVI: IMMEDIATE OPERAND\n");
         2'b11 : $write("UNSUPPORTED!!!!!\n");
       endcase
       
       $write("operation: ");
       priority case (operation) 
         4'b0000 : $write("ADD\n");
         4'b0001 : $write("SUB\n");
         4'b0010 : $write("MULT\n");
         4'b0011 : $write("SHIFT RIGHT\n");
         4'b0100 : $write("SHIFT LEFT\n");
         4'b0101 : $write("ROTATE RIGHT\n");
         4'b0110 : $write("ROTATE LEFT\n");
         4'b0111 : $write("NOT\n");
         4'b1000 : $write("AND\n");
         4'b1001 : $write("OR\n");
         4'b1010 : $write("XOR\n");
         4'b1011 : $write("NAND\n");
         4'b1100 : $write("NOR\n");
         4'b1101 : $write("XNOR\n");
         4'b1110 : $write("INC\n");
         4'b1111 : $write("DEC\n");
       endcase
              
       $write("\n");
    endfunction : display
    
   /*!
    * Copies the current value of the object instance to the specified object
    * instance. Returns a reference to the target instance.
    * 
    * \param to - original transaction        
    */
    virtual function Transaction copy(Transaction to = null);
      ALUInGATransaction #(pDataWidth) tr;
      if (to == null)
        tr = new();
      else 
        $cast(tr, to);

      tr.operandA   = operandA;
      tr.operandB   = operandB;
      tr.operandMEM = operandMEM;
      tr.operandIMM = operandIMM;
      tr.operation  = operation;
      tr.movi       = movi;
      
      tr.movi_values = movi_values;
      tr.movi_wt = new[movi_values];
      for (int i=0; i < movi_values; i++) 
        tr.movi_wt[i] = movi_wt[i];
         
      tr.operandA_ranges = operandA_ranges;
      tr.opA_range_wt = new[operandA_ranges];
      for (int i=0; i < operandA_ranges; i++)
        tr.opA_range_wt[i] = opA_range_wt[i];
        
      tr.operandB_ranges = operandB_ranges;
      tr.opB_range_wt = new[operandB_ranges];
      for (int i=0; i < movi_values; i++)
        tr.opB_range_wt[i] = opB_range_wt[i];
      
      tr.operandMEM_ranges = operandMEM_ranges;
      tr.opMEM_range_wt = new[operandMEM_ranges];
      for (int i=0; i < movi_values; i++)
        tr.opMEM_range_wt[i] = opMEM_range_wt[i];
      
      tr.operandIMM_ranges = operandIMM_ranges;
      tr.opIMM_range_wt = new[operandIMM_ranges];
      for (int i=0; i < movi_values; i++)
        tr.opIMM_range_wt[i] = opIMM_range_wt[i];
      
      tr.operation_values = operation_values;
      tr.op_range_wt = new[operation_values];
      for (int i=0; i < movi_values; i++)
       tr.op_range_wt[i] = op_range_wt[i];
      
      tr.delay_ranges = delay_ranges;
      tr.delay_range_wt = new[delay_ranges];
      for (int i=0; i < movi_values; i++)
        tr.delay_range_wt[i] = delay_range_wt[i]; 
      
      copy = tr;  
    endfunction: copy
   
  endclass: ALUInGATransaction
