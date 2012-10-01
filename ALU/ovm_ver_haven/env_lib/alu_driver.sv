/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_driver.sv
 * Description:  OVM Driver Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         1.10.2012
 * ************************************************************************** */

/*!
 * \brief AluDriver
 * 
 * This class drives the input interface of ALU and supplies transactions from 
 * sequencer to this interface.
 */

 class AluDriver extends ovm_driver #(AluInputTransaction);

   // registration of component tools
   `ovm_component_utils(AluDriver)
    
   // reference to the input virtual interface
   virtual iAluIn dut_alu_in_if;
   
   // analysis port for sending data received from sequencer to the connected 
   // scoreboard and subscriber 
   ovm_analysis_port #(AluInputTransaction) aport_alu_in_if;

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
     aport_alu_in_if = new("Analysis Port for ALU Input Interface", this);
     begin
       ovm_object obj;
       AluDutIfWrapper dut_if_wrapper;
       
       // read object from the configuration table
       get_config_object("AluDutIfWrapper", obj, 0);
       
       // cast obtained object into the ALU Wrapper
       assert( $cast(dut_if_wrapper, obj) );
       
       // receive input virtual interface from the ALU wrapper
       dut_alu_in_if = dut_if_wrapper.dut_alu_in_if;
     end
   endfunction: build   
  
  /*! 
   * Run - starts the processing in driver
   */ 
   task run;
   
     forever begin

       AluInputTransaction tr;

       // synchronization with the DUT
       @(posedge dut_alu_in_if.CLK);
       
       // receive transaction from sequencer
       seq_item_port.get(tr);
  
       tr.display("DRIVER:");

       if (GEN_OUTPUT==0 || GEN_OUTPUT==2)
         begin
           // sends values from transaction on the virtual interface
           dut_alu_in_if.RST  = tr.rst;
           dut_alu_in_if.ACT  = 1;         // change later !!!
           dut_alu_in_if.OP   = tr.op;
           dut_alu_in_if.MOVI = tr.movi;
           dut_alu_in_if.REG_A = tr.reg_a;
           dut_alu_in_if.REG_B = tr.reg_b;
           dut_alu_in_if.MEM  = tr.mem;
           dut_alu_in_if.IMM  = tr.imm;
         end
        
       // sends generated transaction to the scoreboard, subscriber etc.
       aport_alu_in_if.write(tr);
       
       // synchronise with CLK 
       @(posedge dut_alu_in_if.CLK);
             
     end
     
   endtask: run

 endclass: AluDriver
