/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_driver.sv
 * Description:  OVM Driver Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         20.9.2012
 * ************************************************************************** */

`include "ovm_macros.svh"

package sv_alu_pkg;
 
 import ovm_pkg::*; 

/*!
 * \brief AluDriver
 * 
 * This class puts transactions from sequencer on ALU interface.
 */

 class AluDriver #(int pDataWidth = 8, int GEN_OUTPUT=0) 
   extends ovm_driver #(AluTransactionDUTInput);

   //registration of component tools
   `ovm_component_utils(AluDriver)
    
   //reference on the vitrtual interface
   virtual iAluIn #(pDataWidth) dut_if1;
   
   //analysis port, sends data received from sequencer
   //used to connect driver with scoreboards or subscribers
   ovm_analysis_port #(AluTransactionDUTInput) aport_dut_input;

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
     aport_dut_input = new("aport_dut_input", this);
     begin
       ovm_object obj;
       AluDutIfWrapper  #(pDataWidth) if_wrapper;
       //reads object from configuration table
       get_config_object("AluDutIfWrapper", obj, 0);
       //transforms obtained object to wrapper for virtual interface
       assert( $cast(if_wrapper, obj) );
       //takes input virtual interface from the wrapper
       dut_if1 = if_wrapper.dut_alu_in_if;
     end
   endfunction: build   
   
   task run;

     forever begin

       AluTransactionDUTInput #(pDataWidth) tx;

       //$write("Driver waits for CLK\n");

       //synchronization with DUT
       @(posedge dut_if1.CLK);
       seq_item_port.get(tx);
  
       tx.display("DRIVER:");

       if(GEN_OUTPUT==0 || GEN_OUTPUT==2)
         begin
           //sends values from transaction on the virtual interface
           dut_if1.RST  = tx.RST;
           dut_if1.ACT  = tx.ACT;
           dut_if1.OP   = tx.OP;
           dut_if1.MOVI = tx.MOVI;
           dut_if1.REGA = tx.REG_A;
           dut_if1.REGB = tx.REG_B;
           dut_if1.MEM  = tx.MEM;
           dut_if1.IMM  = tx.IMM;
         end
        
       //sends generated transaction to the scoreboards, subscribers etc.
       aport.write(tx);
             
     end
     
     //wait for CLK and then end, program will never reach this command
     //it would reach it, if repeat(n) was used instead of forever 
     @(posedge dut_if1.CLK) ovm_top.stop_request();
   
   endtask: run

 endclass: AluDriver
 
endpackage 