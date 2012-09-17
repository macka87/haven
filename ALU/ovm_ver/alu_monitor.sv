/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_monitor.sv
 * Description:  OVM Monitor Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         16.8.2012
 * ************************************************************************** */

`include "ovm_macros.svh"
package alu_monitor_pkg;
 import ovm_pkg::*;
 import sv_basic_comp_pkg::*;
 import alu_transaction_result_pkg::*;
 import alu_dut_if_wrapper_pkg::*;  

/*!
 * \brief AluMonitor
 * 
 * This class reads signals on ALU interface and sends their values transformed
 * into transactions to other components.
 */

 class AluMonitor #(int pDataWidth = 8) extends BasicMonitor #(AluTransactionResults);

   //registration of component tools
   `ovm_component_utils(AluMonitor)

   //referencia na virtual interface
   virtual AluDutIf #(pDataWidth) dut_if1;
    
  /*! 
   * Constructor - creates AluMonitor object  
   *
   * \param name     - monitor instance name
   * \param parent   - parent class identification
   */ 
   function new (string name, ovm_component parent);
     super.new(name, parent);
   endfunction: new

  /*! 
   * Build - instanciates child components
   */ 
   function void build;
     super.build();
     begin
       ovm_object obj;
       AluDutIfWrapper #(pDataWidth) if_wrapper;
       //reads object from configuration table
       get_config_object("AluDutIfWrapper", obj, 0);
       //transforms obtained object to wrapper for virtual interface
       assert( $cast(if_wrapper, obj) );
       //takes virtual interface from the wrapper
       dut_if1 = if_wrapper.dut_if1;
     end
   endfunction: build
    
   task run;

     //delay, so the actual and predicted restults would be at the same time
     #10;
      
     forever
     begin
       AluTransactionResults #(pDataWidth) tx_results;
       //synchronisation with DUT
       @(posedge dut_if1.CLK);
       tx_results = AluTransactionResults::type_id::create("tx_results");
       tx_results.EX_ALU     = dut_if1.EX_ALU;
       tx_results.EX_ALU_VLD = dut_if1.EX_ALU_VLD;
       tx_results.ALU_RDY    = dut_if1.ALU_RDY;
       tx_results.display("MONITOR:"); 
       //sends transaction through analytic port
       aport.write(tx_results);
     end
   endtask: run
      
 endclass: AluMonitor
 
endpackage: alu_monitor_pkg 