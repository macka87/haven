/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    sv_alu_test_pkg.sv
 * Description:  OVM ALU Test Package
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.9.2012
 * ************************************************************************** */

package sv_alu_test_pkg;
  import ovm_pkg::*;
  import sv_alu_param_pkg::*;
  import sv_alu_seq_pkg::*;
  import sv_alu_env_pkg::*;
  
  `include "ovm_macros.svh"
  `include "alu_test.sv"
endpackage