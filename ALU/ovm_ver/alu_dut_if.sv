/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_dut_if.sv
 * Description:  OVM ALU Interface
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         10.9.2012
 * ************************************************************************** */

interface AluDutIf(pDataWidth = 8);
  
  logic CLK;
  logic RST;
  logic ACT;
  logic[3:0] OP;
  logic[1:0] MOVI;
  logic[pDataWidth-1:0] REGA;
  logic[pDataWidth-1:0] REGB;
  logic[pDataWidth-1:0] MEM;
  logic[pDataWidth-1:0] IMM;
  logic[pDataWidth-1:0] EX_ALU;
  logic[pDataWidth-1:0] EX_ALU_VLD;
  logic[pDataWidth-1:0] ALU_RDY;

endinterface: AluDutIf