/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU 
 * File Name:    alu_dut_if.sv
 * Description:  ALU interfaces.
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014        
 * ************************************************************************** */

 import sv_alu_param_pkg::*;

/*
 * ALU Input Interface Declaration
 */ 
 interface iAluIn (input logic CLK, input logic RST);  
   logic       ACT                 ;   // Activity signal
   logic       ALU_RDY             ;   // ALU is ready to process instructions
   logic [3:0] OP                  ;   // ALU Operation
   logic [1:0] MOVI                ;   // Type of second operand
   logic [DATA_WIDTH-1:0] REG_A    ;   // Operand in register A
   logic [DATA_WIDTH-1:0] REG_B    ;   // Operand in register B
   logic [DATA_WIDTH-1:0] IMM      ;   // Immediate operand
   logic [DATA_WIDTH-1:0] MEM      ;   // Memory operand
   
   // Clocking block  
   clocking cb @(posedge CLK);
     input ALU_RDY;
     output RST, ACT, OP, MOVI, REG_A, REG_B, IMM, MEM;  
   endclocking: cb;
   
   // Clocking block for coverage
   clocking cover_cb @(posedge CLK);
     input RST, ACT, ALU_RDY, OP, MOVI, REG_A, REG_B, IMM, MEM;  
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
  
 endinterface : iAluIn
 
/*
 * ALU Output Interface Declaration
 */ 
 interface iAluOut (input logic CLK, input logic RST);  
   logic [DATA_WIDTH-1:0] EX_ALU   ;   // Result of ALU
   logic EX_ALU_VLD                ;   // Validity of ALU result
   
   // Clocking blocks  
   clocking cb @(posedge CLK);
     input EX_ALU, EX_ALU_VLD;   
   endclocking: cb;
   
   // DUT Modport
   modport aluout (output  EX_ALU,
                   output  EX_ALU_VLD
                  );
  
 endinterface : iAluOut
