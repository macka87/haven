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
     string msg;
   
     super.build();
     aport_alu_in_if = new("Analysis Port for ALU Input Interface", this);
     begin
       ovm_object obj;
       AluDutIfWrapper dut_if_wrapper;
       
       // read object from the configuration table
       if (!get_config_object("AluDutIfWrapper", obj, 0)) begin
         $sformat(msg, "It is not possible to obtain AluDutIfWrapper from the configuration table!\n");
         ovm_report_error("DRIVER", msg, OVM_NONE);
       end
       
       // cast obtained object into the ALU Wrapper
       assert($cast(dut_if_wrapper, obj));
       
       // receive input virtual interface from the ALU wrapper
       dut_alu_in_if = dut_if_wrapper.dut_alu_in_if;
     end
   endfunction: build   
  
  /*! 
   * Run - starts the processing in driver
   */ 
   task run;
     AluInputTransaction tr;
          
     dut_alu_in_if.cb.ACT <= 0;  
     
     // synchronization with the DUT
     @(dut_alu_in_if.cb);
   
     forever
     begin
     
       // receive transaction from sequencer
       seq_item_port.get(tr);
  
       // display the content of transaction 
       //tr.display("DRIVER:");
       
       // wait for readiness of ALU to process data
       waitForAluRdy();
       
       tr.rst = dut_alu_in_if.RST;
       
       // set input signals of DUT
       // sends values from transaction on the virtual interface
       dut_alu_in_if.cb.ACT   <= tr.act;        
       dut_alu_in_if.cb.OP    <= tr.op;
       dut_alu_in_if.cb.MOVI  <= tr.movi;
       dut_alu_in_if.cb.REG_A <= tr.reg_a;
       dut_alu_in_if.cb.REG_B <= tr.reg_b;
       dut_alu_in_if.cb.MEM   <= tr.mem;
       dut_alu_in_if.cb.IMM   <= tr.imm;
                
       // synchronise with CLK 
       @(dut_alu_in_if.cb);  
        
       // sends generated transaction to the scoreboard, subscriber etc.
       if (tr.act) 
         aport_alu_in_if.write(tr);
     end
   endtask: run
  
  /*!
   * Wait for ALU_RDY
   */
   task waitForAluRdy();
     while (!dut_alu_in_if.cb.ALU_RDY || dut_alu_in_if.RST) 
       @(dut_alu_in_if.cb);
   endtask : waitForAluRdy     
 endclass: AluDriver
