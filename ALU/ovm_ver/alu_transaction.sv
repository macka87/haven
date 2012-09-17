/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_transaction.sv
 * Description:  OVM Transaction Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         7.9.2012
 * ************************************************************************** */

`include "ovm_macros.svh"
package alu_transaction_pkg;
 import ovm_pkg::*;
 import sv_basic_comp_pkg::*; 
  
/*!
 * \brief BasicTransaction
 * 
 * This class is transaction which contains input values for DUT.
 */
 
 class AluTransaction #(pDataWidth = 8) extends BasicTransaction;

   //registration of component tools
   `ovm_object_utils(BasicTransaction)
   
   //included data
   rand bit RST;
   bit ACT;
   rand logic [3:0] OP;
   rand logic [1:0] MOVI;
   rand logic [pDataWidth-1:0] REGA;
   rand logic [pDataWidth-1:0] REGB;
   rand logic [pDataWidth-1:0] MEM;
   rand logic [pDataWidth-1:0] IMM;

   //obmedzenia na nahodne generovane hodnoty vyssie uvedenych premennych
   constraint c_MOVI { MOVI >= 0; MOVI < 3; }

  /*! 
   * Constructor - creates AluTransaction object  
   *
   * \param name     - transaction instance name
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
      $write("RST: %d\n", RST);      
      //$write("ACT: %d\n", ACT);  
      $write("OP:);
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
      priority case (MOVI) 
        2'b00 : $write("MOVI: REGISTER B\n");
        2'b01 : $write("MOVI: MEMORY OPERAND\n");
        2'b10 : $write("MOVI: IMMEDIATE OPERAND\n");
        2'b11 : $write("UNSUPPORTED!!!!!\n");
      endcase
      $write("REGA: %d\n", REGA);      
      $write("REGB: %d\n", REGB);  
      $write("MEM: %d\n", MEM); 
      $write("IMM: %d\n", IMM);
      $write("\n");
   endfunction: display

  /*!
   * Copies the current value of the object instance to the specified object
   * instance. Returns a reference to the target instance.
   * 
   * \param to - original transaction        
   */
   virtual function AluTransaction copy(AluTransaction to = null);
   
     AluTransaction  #(pDataWidth) tr;
     if (to == null)
       tr = new();
     else 
       $cast(tr, to);

     tr.RST  = RST;
     //tr.ACT  = ACT;
     tr.OP   = OP;
     tr.MOVI = MOVI;
     tr.REGA = REGA;
     tr.REGB = REGB;
     tr.MEM  = MEM;
     tr.IMM  = IMM;
             
     copy = tr;
   endfunction : copy
   
  /*!
   * Compares the current value of the object instance with the current value
   * of the specified object instance, according to the specified kind. 
   * Returns TRUE (i.e., non-zero) if the value is identical. If the value is
   * different, FALSE is returned and a descriptive text of the first 
   * difference found is returned in the specified string variable. The kind 
   * argument may be used to implement different comparison functions (e.g., 
   * full compare, comparison of rand properties only, comparison of all 
   * properties physically implemented in a protocol and so on.)
   * 
   * \param to - transaction instance
   * \param diff - first difference
   * \param kind - comparation function                 
   */
   virtual function bit compare(input AluTransaction to, 
                                output string diff, input int kind = -1);
     bit same = 1; // Suppose that are same
     AluTransaction tr;
     $cast(tr, to);
       
     if (RST != tr.RST) 
     begin
       same = 0;
       $write(diff, "RST does not match!\n");
     end
       
     /*if (ACT != tr.ACT) 
     begin
       same = 0;
       $write(diff, "ACT does not match!\n");
     end*/
     
     if (OP != tr.OP) 
     begin
       same = 0;
       $write(diff, "OP does not match!\n");
     end
       
     if (MOVI != tr.MOVI) 
     begin
       same = 0;
       $write(diff, "MOVI does not match!\n");
     end
     
     if (REGA != tr.REGA) 
     begin
       same = 0;
       $write(diff, "REGA does not match!\n");
     end
       
     if (REGB != tr.REGB) 
     begin
       same = 0;
       $write(diff, "REGB does not match!\n");
     end
     
     if (MEM != tr.MEM) 
     begin
       same = 0;
       $write(diff, "MEM does not match!\n");
     end
       
     if (IMM != tr.IMM) 
     begin
       same = 0;
       $write(diff, "IMM does not match!\n");
     end
           
     compare = same; 
   endfunction : compare 

  /*!
   * Function for writing transaction into an external file. 
   */
   function void fwrite(int fileDescr);
     $fwrite(fileDescr, "%b %b %b %b %b %b\n", OP, MOVI, REGA, REGB, MEM, IMM);
   endfunction : fwrite
    
  /*!
   * Function for reading transaction from an external file. 
   */
   function void fread(int fileDescr);
     int r;
           
     r = $fscanf(fileDescr, "%b %b %b %b %b %b\n", OP, MOVI, REGA, REGB, MEM, IMM);
      
     if (r==0) begin
       $write("File corrupted!!!");
       $stop;
     end  
   endfunction : fread
   
 endclass: AluTransaction
 
endpackage: alu_transaction_pkg