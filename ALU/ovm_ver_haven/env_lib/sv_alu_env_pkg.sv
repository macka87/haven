/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    sv_alu_env_pkg.sv
 * Description:  OVM ALU Verification Environment Package
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.9.2012
 * ************************************************************************** */

package sv_alu_env_pkg;

 import ovm_pkg::*;
 import sv_alu_param_pkg::*;
 import sv_alu_seq_pkg::*;

`include "ovm_macros.svh"
`include "alu_dut_if_wrapper.sv"
`include "alu_driver.sv"
`include "alu_monitor.sv"
`include "alu_scoreboard.sv"
`include "alu_env.sv"

endpackage