/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    alu_ga_input_transaction.sv
 * Description:  Definition of input vectors (transactions)
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2012 
 * ************************************************************************** */ 

class ALUInGATransaction #(pDataWidth = 8) extends Transaction;
      
   /*
    * Public Class Atributes
    */
   
   //! --- RANDOMIZATION OF TRANSACTION PARAMETERS ---
   
   // input signals with weights
   rand logic [1:0] movi;                   // type of B operand
       byte unsigned movi_values = 3;       // num. of values for MOVI
       byte unsigned movi_wt[];  
          
   rand logic [pDataWidth-1:0] operandA;    // register operand A
       byte unsigned operandA_ranges = 1;   // num. of ranges for opA
       byte unsigned opA_range_wt[];
       
   rand logic [pDataWidth-1:0] operandB;    // register operand B
       byte unsigned operandB_ranges = 1;   // num. of ranges for opB
       byte unsigned opB_range_wt[];
       
   rand logic [pDataWidth-1:0] operandIMM;  // immediate operand B
       byte unsigned operandIMM_ranges = 1; // num. of ranges for opIMM
       byte unsigned opIMM_range_wt[];
       
   rand logic [pDataWidth-1:0] operandMEM;  // memory operand B
       byte unsigned operandMEM_ranges = 1; // num. of ranges for opMEM
       byte unsigned opMEM_range_wt[];   
       
   rand logic [3:0] operation;              // type of operation  
       byte unsigned operation_values = 16; // num. of values for OPERATION
       byte unsigned op_range_wt[];  
       
   //! --- CONSTRAINTS OF SIGNAL VALUES ---
   
   //! MOVI constraint
   constraint c_movi {
      movi dist { 2'b00 := movi_wt[0],
                  2'b01 := movi_wt[1],
                  2'b10 := movi_wt[2],
                };
   }; 
   
   
   // !!!!!!!!!!!!! NIE JE GENERICKE, PREROBIT !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
   
   //! REG_A constraint (if range == 1, without constraint)
   constraint c_operandA {
      (operandA_ranges == 2) -> operandA dist { 
                                  [255:128] := opA_range_wt[0],
                                  [127:0]   := opA_range_wt[1]
                                };
      (operandA_ranges == 4) -> operandA dist { 
                                  [255:192] := opA_range_wt[0],
                                  [191:128] := opA_range_wt[1],
                                  [127:64]  := opA_range_wt[2],
                                  [63:0]    := opA_range_wt[3]
                                }; 
      (operandA_ranges == 8) -> operandA dist { 
                                  [255:224] := opA_range_wt[0],
                                  [223:192] := opA_range_wt[1],
                                  [191:160] := opA_range_wt[2],
                                  [159:128] := opA_range_wt[3],
                                  [127:96]  := opA_range_wt[4],
                                  [65:64]   := opA_range_wt[5],
                                  [63:32]   := opA_range_wt[6],
                                  [31:0]    := opA_range_wt[7]
                                };                                                     
   }; 
   
   //! REG_B constraint (if range == 1, without constraint)
   constraint c_operandB {
      (operandB_ranges == 2) -> operandB dist { 
                                  [255:128] := opB_range_wt[0],
                                  [127:0]   := opB_range_wt[1]
                                };
      (operandB_ranges == 4) -> operandB dist { 
                                  [255:192] := opB_range_wt[0],
                                  [191:128] := opB_range_wt[1],
                                  [127:64]  := opB_range_wt[2],
                                  [63:0]    := opB_range_wt[3]
                                }; 
      (operandB_ranges == 8) -> operandB dist { 
                                  [255:224] := opB_range_wt[0],
                                  [223:192] := opB_range_wt[1],
                                  [191:160] := opB_range_wt[2],
                                  [159:128] := opB_range_wt[3],
                                  [127:96]  := opB_range_wt[4],
                                  [65:64]   := opB_range_wt[5],
                                  [63:32]   := opB_range_wt[6],
                                  [31:0]    := opB_range_wt[7]
                                };                                                     
   }; 
   
   //! REG_IMM constraint (if range == 1, without constraint)
   constraint c_operandIMM {
      (operandIMM_ranges == 2) -> operandIMM dist { 
                                  [255:128] := opIMM_range_wt[0],
                                  [127:0]   := opIMM_range_wt[1]
                                };
      (operandIMM_ranges == 4) -> operandIMM dist { 
                                  [255:192] := opIMM_range_wt[0],
                                  [191:128] := opIMM_range_wt[1],
                                  [127:64]  := opIMM_range_wt[2],
                                  [63:0]    := opIMM_range_wt[3]
                                }; 
      (operandIMM_ranges == 8) -> operandIMM dist { 
                                  [255:224] := opIMM_range_wt[0],
                                  [223:192] := opIMM_range_wt[1],
                                  [191:160] := opIMM_range_wt[2],
                                  [159:128] := opIMM_range_wt[3],
                                  [127:96]  := opIMM_range_wt[4],
                                  [65:64]   := opIMM_range_wt[5],
                                  [63:32]   := opIMM_range_wt[6],
                                  [31:0]    := opIMM_range_wt[7]
                                };                                                     
   }; 
    
   //! REG_MEM constraint (if range == 1, without constraint)
   constraint c_operandMEM {
      (operandMEM_ranges == 2) -> operandMEM dist { 
                                  [255:128] := opMEM_range_wt[0],
                                  [127:0]   := opMEM_range_wt[1]
                                };
      (operandMEM_ranges == 4) -> operandMEM dist { 
                                  [255:192] := opMEM_range_wt[0],
                                  [191:128] := opMEM_range_wt[1],
                                  [127:64]  := opMEM_range_wt[2],
                                  [63:0]    := opMEM_range_wt[3]
                                }; 
      (operandMEM_ranges == 8) -> operandMEM dist { 
                                  [255:224] := opMEM_range_wt[0],
                                  [223:192] := opMEM_range_wt[1],
                                  [191:160] := opMEM_range_wt[2],
                                  [159:128] := opMEM_range_wt[3],
                                  [127:96]  := opMEM_range_wt[4],
                                  [65:64]   := opMEM_range_wt[5],
                                  [63:32]   := opMEM_range_wt[6],
                                  [31:0]    := opMEM_range_wt[7]
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
                       15 := op_range_wt[15],
                     };
   };
   
  
   //! --- RANDOMIZATION OF DELAY PARAMETERS ---
   rand byte btDelay; 
       byte unsigned delay_ranges;        // num. of delay ranges
       byte unsigned delay_range_wt[];     
   
   //! --- CONSTRAINTS OF DELAY PARAMETERS ---
   
   //! DELAY constraint (if range == 1, without constraint)
   constraint c_delay {
      (delay_ranges == 2) -> btDelay dist { 
                               [15:8] := delay_range_wt[0],
                               [7:0]  := delay_range_wt[1]
                             };
      (delay_ranges == 4) -> btDelay dist { 
                               [15:12] := delay_range_wt[0],
                               [11:8]  := delay_range_wt[1],
                               [7:4]   := delay_range_wt[2],
                               [3:0]   := delay_range_wt[3]
                             }; 
   }; 
   
   /*
    * Public Class Methods
    */
    
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
       
       $write("operandA: %d\n", operandA);  
       $write("operandB: %d\n", operandB); 
       $write("operandIMM: %d\n", operandIMM); 
       $write("operandMEM: %d\n", operandMEM); 
       
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
      ALUInTransaction #(pDataWidth) tr;
      if (to == null)
        tr = new();
      else 
        $cast(tr, to);

      tr.operandA   = operandA;
      tr.operandB   = operandB;
      tr.operandIMM = operandIMM;
      tr.operandMEM = operandMEM;
      tr.operation  = operation;
      tr.movi       = movi;
      
      //tr.btDelayEn_wt  = btDelayEn_wt;
      //tr.btDelayDi_wt  = btDelayDi_wt;
      //tr.btDelayLow    = btDelayLow;
      //tr.btDelayHigh   = btDelayHigh;
      
      copy = tr;  
    endfunction: copy

   /*!
    * Function for writing transaction into an external file. 
    */
    function void fwrite(int fileDescr);
      $fwrite(fileDescr, "%b %b %b %b %b %b\n", operandA, operandB, operandIMM, operandMEM, operation, movi);
    endfunction : fwrite
    
   /*!
    * Function for reading transaction from an external file. 
    */
    function void fread(int fileDescr);
      int r;
            
      r = $fscanf(fileDescr,"%b %b %b %b %b %b\n", operandA, operandB, operandIMM, operandMEM, operation, movi);
      
      if (r==0) begin
        $write("File corrupted!!!");
        $stop;
      end  
    endfunction : fread
  endclass: ALUInGATransaction
