/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_sender.sv
 * Description:  OVM Sender for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         12.9.2012
 * ************************************************************************** */

`include "ovm_macros.svh"

package sv_alu_pkg;
 
 import ovm_pkg::*;
  
/*!
 * \brief AluSender
 * 
 * This class writes received transactions on the screen or to the file.
 */
 
 class AluSender extends ovm_component;
    
   //registration of component tools
   `ovm_component_utils(AluSender)

   //pre pripojenie na driver a monitor
   ovm_analysis_export #(AluTransactionDUTInput) aport_dut_input;
    
   //fronty prijatych tranzakcii
   local tlm_analysis_fifo #(AluTransactionDUTInput) fifo_dut_input;

  /*! 
   * Constructor - creates AluSender object  
   *
   * \param name     - instance name
   * \param parent   - parent class identification
   */
   function new(string name, ovm_component parent);
     super.new(name, parent);
   endfunction: new

  /*! 
   * Build - instanciates child components
   */ 
   function void build;
     super.build();
     aport_dut_input = new("aport_dut_input",this);
     fifo_dut_input = new("fifo_dut_input",this);
   endfunction: build

  /*! 
   * Connect - connects ports of the child components, afterwards they can
   * communicate
   */    
   virtual function void connect();
     aport_dut_input.connect(fifo_dut_input.analysis_export);
   endfunction: connect

  /*! 
   * Run - runs the sequence of transactions
   */     
   task run;
     AluTransactionDUTInput tx;
     forever begin
       fifo_dut_input.get(tx);
       tx.display("SENDER:");
       //tx.fwrite("input_transactions.txt");
     end
   endtask: run
  
 endclass: AluSender

endpackage