/* *****************************************************************************
 * Project Name: ALU Functional Verification 
 * File Name:    alu_ifc.sv
 * Description:  ALU interfaces
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         22.3.2012         
 * ************************************************************************** */

/*
 *  ALU Input Interface Declaration
 */ 
 interface iAluIn #(int pDataWidth = 8) (input logic CLK, RESET);  
   logic       ACT                 ;   // Activity signal
   logic       ALU_RDY             ;   // ALU is ready to process instructions
   logic [3:0] OP                  ;   // ALU Operation
   logic [1:0] MOVI                ;   // Type of second operand
   logic [pDataWidth-1:0] REG_A    ;   // Operand in register A
   logic [pDataWidth-1:0] REG_B    ;   // Operand in register B
   logic [pDataWidth-1:0] IMM      ;   // Immediate operand
   logic [pDataWidth-1:0] MEM      ;   // Memory operand
   
   // Clocking block  
   clocking cb @(posedge CLK);
     input ALU_RDY;
     output ACT, OP, MOVI, REG_A, REG_B, IMM, MEM;  
   endclocking: cb;
   
   // Clocking block for coverage
   clocking cover_cb @(posedge CLK);
     input ACT, ALU_RDY, OP, MOVI, REG_A, REG_B, IMM, MEM;  
   endclocking: cover_cb;

   // DUT Modport
   modport aluin (input  ACT, 
                  output ALU_RDY,
                  input  OP,
                  input  MOVI,
                  input  REG_A,
                  input  REG_B,
                  input  IMM,
                  input  MEM
                 );
  
   modport aluin_tb (clocking cb);
   modport cover_tb (clocking cover_cb);
 endinterface : iAluIn
 
 /*
 *  ALU Output Interface Declaration
 */ 
 interface iAluOut #(int pDataWidth = 8) (input logic CLK, RESET);  
   logic [pDataWidth-1:0] EX_ALU   ;   // Result of ALU
   logic EX_ALU_VLD                ;   // Validity of ALU result
   
   // Clocking blocks  
   clocking cb @(posedge CLK);
     input EX_ALU, EX_ALU_VLD;   
   endclocking: cb;

   // DUT Modport
   modport aluout (output  EX_ALU,
                   output  EX_ALU_VLD
                  );
  
   modport aluout_tb (clocking cb);
 endinterface : iAluOut
