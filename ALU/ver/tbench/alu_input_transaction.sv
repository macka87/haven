/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    alu_input_transaction.sv
 * Description:  Definition of input vectors (transactions)
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         22.3.2012 
 * ************************************************************************** */ 

class ALUInTransaction #(pDataWidth = 8) extends Transaction;
      
   /*
    * Public Class Atributes
    */
   
   //! --- RANDOMIZATION OF TRANSACTION PARAMETERS ---
   
   // operands
   rand logic [1:0]            movi;           // type of B operand
   rand logic [pDataWidth-1:0] operandA;       // register operand A
   rand logic [pDataWidth-1:0] operandB;       // register operand B
   rand logic [pDataWidth-1:0] operandMEM;     // memory operand B
   rand logic [pDataWidth-1:0] operandIMM;     // immediate operand B
   
   // operation
   rand logic [3:0] operation;                 // type of operation
   
   //constraint values_range
   //{
   //  movi inside       {[0 : 2]};
     //operandA inside   {[0 : 5]};
     //operandB inside   {[0 : 5]};
     //operandMEM inside {[0 : 5]};
     //operandIMM inside {[0 : 5]};
  // }
   
   //! --- RANDOMIZATION OF DELAY PARAMETERS ---
   
   //! Enable/Disable delays "between transactions" according to weights
   // rand bit enBtDelay;   
   //      byte btDelayEn_wt  = 1; 
   //      byte btDelayDi_wt  = 3;

    //! Value of delay "between transactions" randomized inside boundaries
   rand byte btDelay; 
   //      byte btDelayLow    = 0;
   //      byte btDelayHigh   = 3;
   
    //! Constraints for randomized values 
   // constraint cDelay1 {
   //   enBtDelay dist { 1'b1 := btDelayEn_wt,
   //                    1'b0 := btDelayDi_wt
   //                  };
   // };                 

   // constraint cDelay2 {
   //   btDelay inside {
   //                   [btDelayLow:btDelayHigh]
   //                  };
   // };                 

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
      ALUInTransaction #(pDataWidth) tr;
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
      $fwrite(fileDescr, "%b %b %b %b %b %b\n", operandA, operandB, operandMEM, operandIMM, operation, movi);
    endfunction : fwrite
    
   /*!
    * Function for reading transaction from an external file. 
    */
    function void fread(int fileDescr);
      int r;
            
      r = $fscanf(fileDescr,"%b %b %b %b %b %b\n", operandA, operandB, operandMEM, operandIMM, operation, movi);
      
      if (r==0) begin
        $write("File corrupted!!!");
        $stop;
      end  
    endfunction : fread
  endclass: ALUInTransaction
