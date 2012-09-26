/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_monitor.sv
 * Description:  OVM Monitor Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         20.9.2012
 * ************************************************************************** */

`include "ovm_macros.svh"

package sv_alu_pkg;
 
 import ovm_pkg::*; 

/*!
 * \brief AluMonitor
 * 
 * This class reads signals on ALU interface and sends their values transformed
 * into transactions to other components.
 */

 class AluMonitor #(int pDataWidth = 8) extends ovm_monitor #(AluTransactionDUTOutput);

   //registration of component tools
   `ovm_component_utils(AluMonitor)

   //reference to a virtual interface
   virtual iAluOut #(pDataWidth) dut_if1;
   
   //analysis port, sends data received from the DUT output interface
   //used to connect monitor with scoreboards or subscribers
   ovm_analysis_port #(AluTransactionDUTOutput) aport_dut_output;
    
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
     aport_dut_output = new("aport_dut_output", this);
     begin
       ovm_object obj;
       AluDutIfWrapper #(pDataWidth) if_wrapper;
       //reads object from configuration table
       get_config_object("AluDutIfWrapper", obj, 0);
       //transforms obtained object to wrapper for virtual interface
       assert( $cast(if_wrapper, obj) );
       //takes output virtual interface from the wrapper
       dut_if1 = if_wrapper.dut_alu_out_if;
     end
   endfunction: build
    
   task run;

     //delay, so the actual and predicted restults would be at the same time
     #10;
      
     forever
     begin
       AluTransactionDUTOutput #(pDataWidth) tx_results;
       //synchronisation with DUT
       @(posedge dut_if1.CLK);
       tx_results = AluTransactionDUTOutput::type_id::create("tx_results");
       tx_results.EX_ALU     = dut_if1.EX_ALU;
       tx_results.EX_ALU_VLD = dut_if1.EX_ALU_VLD;
       tx_results.display("MONITOR:"); 
       //sends transaction through analysis port
       aport.write(tx_results);
     end
   endtask: run
      
 endclass: AluMonitor
 
endpackage