/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_driver.sv
 * Description:  UVM Driver Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2013
 * ************************************************************************** */

/*! 
 * Constructor - creates the AluDriver object  
 */
 function AluDriver::new(string name = "AluDriver", uvm_component parent = null);
   super.new(name, parent);
 endfunction: new
   
 

/*! 
 * Build - instanciates child components
 */ 
 function void AluDriver::build_phase(uvm_phase phase);
   if (!uvm_config_db #(AluAgentConfig)::get(this, "", "AluAgentConfig", alu_agent_cfg)) 
     `uvm_error("MYERR", "AluAgentConfig doesn't exist!");
 endfunction: build_phase   



  
/*! 
 * Connect - interconnection of AluDriver components.
 */  
 function void AluDriver::connect_phase(uvm_phase phase);
   super.connect_phase(phase);
   dut_alu_in_if = alu_agent_cfg.dut_alu_in_if;
 endfunction: connect_phase
 
 
 
/*! 
 * Run - starts driver processing.
 */  
 task AluDriver::run_phase(uvm_phase phase); 
   AluInputTransaction alu_in_trans;
   
   // synchronise with CLK 
   @(dut_alu_in_if.cb); 
   
   forever begin
     seq_item_port.get_next_item(alu_in_trans);
     
     // display the content of transaction 
     alu_in_trans.print("DRIVER: ALU_TRANSACTION");
       
     // wait for readiness of ALU to process data
     waitForAluRdy();
            
     alu_in_trans.rst = dut_alu_in_if.RST;
       
     // set input signals of DUT
     // sends values from transaction on the virtual interface
     dut_alu_in_if.cb.ACT   <= alu_in_trans.act;        
     dut_alu_in_if.cb.OP    <= alu_in_trans.op;
     dut_alu_in_if.cb.MOVI  <= alu_in_trans.movi;
     dut_alu_in_if.cb.REG_A <= alu_in_trans.reg_a;
     dut_alu_in_if.cb.REG_B <= alu_in_trans.reg_b;
     dut_alu_in_if.cb.MEM   <= alu_in_trans.mem;
     dut_alu_in_if.cb.IMM   <= alu_in_trans.imm;
     
     // synchronise with CLK 
     @(dut_alu_in_if.cb); 
     
     seq_item_port.item_done();
   end   
 endtask: run_phase
 
 
 
/*!
 * Wait for ALU_RDY
 */
 task AluDriver::waitForAluRdy();
   while (!dut_alu_in_if.cb.ALU_RDY || dut_alu_in_if.RST) 
     @(dut_alu_in_if.cb);
 endtask : waitForAluRdy     