/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_dut.sv
 * Description:  OVM Module for ALU Encapsulation
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         10.9.2012
 * ************************************************************************** */

/*!
 * \brief AluDut
 * 
 * This module encapsulates DUT
 */

module AluDut(AluDutIf _if);

 ALU_ENT #(
     .DATA_WIDTH    (DATA_WIDTH)       
   )

   VHDL_DUT_U (
     .CLK         (_if.CLK),     
     .RST         (_if.RST),
     .ACT         (_if.ACT),
     .OP          (_if.OP),
     .MOVI        (_if.MOVI),
     .REGA        (_if.REGA),
     .REGB        (_if.REGB),
     .MEM         (_if.MEM),
     .IMM         (_if.IMM),
     .EX_ALU      (_if.EX_ALU),
     .EX_ALU_VLD  (_if.EX_ALU_VLD),
     .ALU_RDY     (_if.ALU_RDY));
  

endmodule: AluDut