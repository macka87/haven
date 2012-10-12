/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_input_transaction.sv
 * Description:  OVM Input Transaction Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         27.9.2012
 * ************************************************************************** */

/*!
 * \brief Input ALU Transaction
 * 
 * This class represents transaction which contains values of input signals for
 * the DUT.
 */
 
 class AluInputTransaction extends HavenInputTransaction;

   // registration of component tools
   `ovm_object_utils(AluInputTransaction)
   
   // basic signals
   logic rst;
   
   // random values of signals
   rand logic act;                       // activation signal
   rand logic [3:0] op;                  // operation
   rand logic [1:0] movi;                // selection signal of operand B
   rand logic [DATA_WIDTH-1:0] reg_a;    // operand A from register
   rand logic [DATA_WIDTH-1:0] reg_b;    // operand B from register
   rand logic [DATA_WIDTH-1:0] mem;      // operand B from memory
   rand logic [DATA_WIDTH-1:0] imm;      // immediate operand B

   // constraints for values of input signals
   
   // *** Upravte nasledujici podminku ***
   
   constraint c_movi { movi >= 0; }
   
   // constraint for values of operation signal
   
   // *** Upravte nasledujici podminku ***
   
   constraint c_op { op >= 0; op <= 13; }

  /*! 
   * Constructor - creates AluInputTransaction object  
   *
   * \param name - transaction instance name
   */
   function new (string name = "");
     super.new(name);
   endfunction: new

  /*!
   * Function displays the current value of the transaction or data described
   * by this instance in a human-readable format on the standard output.
   *
   * \param prefix - transaction type
   */
   function void display(string prefix = "");
      if (prefix != "")
      begin
        $write("---------------------------------------------------------\n");
        $write("-- %s\n",prefix);
        $write("---------------------------------------------------------\n");
      end
      $write("RST: %b\n", rst);
      $write("ACT: %b\n", act);
      $write("OP: ");
      priority case (op) 
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
        /*
        *** zde doplnte kod pro nove operace ***
        4'b1110 : $write("INC\n");
        4'b1111 : $write("DEC\n");
        
        */
      endcase
      $write("\n");  
      priority case (movi) 
        2'b00 : $write("MOVI: REGISTER B\n");
        2'b01 : $write("MOVI: MEMORY OPERAND\n");
        2'b10 : $write("MOVI: IMMEDIATE OPERAND\n");
        2'b11 : $write("MOVI: UNKNOWN VALUE\n");
      endcase
      $write("REG_A: %b\n", reg_a);      
      $write("REG_B: %b\n", reg_b);  
      $write("MEM: %b\n", mem); 
      $write("IMM: %b\n", imm);
      $write("\n");
   endfunction: display

  /*!
   * Function for writing transaction into an external file. 
   */
   function void fwrite(int fileDescr);
     $fwrite(fileDescr, "%b %b %b %b %b %b\n", op, movi, reg_a, reg_b, mem, imm);
   endfunction : fwrite
    
  /*!
   * Function for reading transaction from an external file. 
   */
   function void fread(int fileDescr);
     int r;
           
     r = $fscanf(fileDescr, "%b %b %b %b %b %b\n", op, movi, reg_a, reg_b, mem, imm);
      
     if (r==0) begin
       $write("AluInputTransaction: File corrupted!!!");
       $stop;
     end  
   endfunction : fread
   
 endclass: AluInputTransaction
