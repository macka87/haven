/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    sv_alu_seq_pkg.sv
 * Description:  OVM ALU Sequence Package
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.9.2012
 * ************************************************************************** */

package sv_alu_seq_pkg;

  import ovm_pkg::*;
  import sv_alu_param_pkg::*;
  import sv_basic_ga_pkg::*;
  
  `include "ovm_macros.svh"
  `include "alu_chromosome.sv"
  
 /* `include "haven_sequence_item.sv"
  `include "haven_input_transaction.sv"
  `include "haven_output_transaction.sv"
  `include "alu_input_transaction.sv"
  `include "alu_output_transaction.sv"
  `include "alu_sequence.sv"
  `include "alu_sequencer.sv" */
  
endpackage