/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_driver.sv
 * Description:  OVM Driver Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         16.8.2012
 * ************************************************************************** */

`include "ovm_macros.svh"
package alu_driver_pkg;
 import ovm_pkg::*;
 import sv_basic_comp_pkg::*;
 import alu_transaction_pkg::*;
 import alu_dut_if_wrapper_pkg::*; 

/*!
 * \brief AluDriver
 * 
 * This class puts transactions from sequencer on ALU interface.
 */

 class AluDriver #(int pDataWidth = 8) extends BasicDriver #(AluTransaction);

   //registration of component tools
   `ovm_component_utils(AluDriver)
    
   //reference on the vitrtual interface
   virtual AluDutIf #(pDataWidth) dut_if1;

  /*! 
   * Constructor - creates AluDriver object  
   *
   * \param name     - driver instance name
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
     begin
       ovm_object obj;
       AluDutIfWrapper  #(pDataWidth) if_wrapper;
       //reads object from configuration table
       get_config_object("AluDutIfWrapper", obj, 0);
       //transforms obtained object to wrapper for virtual interface
       assert( $cast(if_wrapper, obj) );
       //takes virtual interface from the wrapper
       dut_if1 = if_wrapper.dut_if1;
     end
   endfunction: build   
   
   task run;

     forever begin

       AluTransaction #(pDataWidth) tx;

       //$write("Driver waits for CLK\n");

       //synchronization with DUT
       @(posedge dut_if1.CLK);
       seq_item_port.get(tx);
  
       tx.display("DRIVER:");

       //sends values from transaction on the virtual interface
       dut_if1.RST  = tx.RST;
       //dut_if1.ACT  = tx.ACT;
       dut_if1.OP   = tx.OP;
       dut_if1.MOVI = tx.MOVI;
       dut_if1.REGA = tx.REGA;
       dut_if1.REGB = tx.REGB;
       dut_if1.MEM  = tx.MEM;
       dut_if1.IMM  = tx.IMM;
        
       //poslanie vygenerovanej sekvencie do scoreboardu
       aport.write(tx);
             
     end
     
     //wait for CLK and then end, program will never reach this command
     //it would reach it, if repeat(n) was used instead of forever 
     @(posedge dut_if1.CLK) ovm_top.stop_request();
   
   endtask: run

 endclass: AluDriver
 
endpackage: alu_driver_pkg 