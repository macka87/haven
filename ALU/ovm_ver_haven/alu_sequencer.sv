/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_sequencer.sv
 * Description:  OVM Sequencer Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.9.2012
 * ************************************************************************** */

`include "ovm_macros.svh"

package sv_alu_pkg;
 
 import ovm_pkg::*;
 
/*!
 * \brief AluSequencer
 * 
 * This class creates random inputs for DUT and sends them to driver
 */

 class AluSequencer extends ovm_squencer #(AluTransactionDUTInput);
    
   //registration of component tools
   `ovm_component_utils(AluSequencer)

  /*! 
   * Constructor - creates AluSequencer object  
   *
   * \param name     - sequencer instance name
   * \param parent   - parent class identification
   */ 
   function new(string name, ovm_component parent);
     super.new(name, parent);
   endfunction: new

 endclass: AluSequencer
 
endpackage