/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_monitor.sv
 * Description:  UVM Monitor Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         8.7.2013
 * ************************************************************************** */

/*!
 * \brief AluMonitor
 * 
 * This class monitors signals on ALU output interface and sends their values 
 * in the form of transactions to other components.
 */

 class AluMonitor extends uvm_monitor;

   //! UVM Factory Registration Macro
   `uvm_component_utils(AluMonitor)

  /*! 
   * Virtual interfaces for DUT
   */ 
  
   virtual iAluOut dut_alu_out_if;
   
  /*! 
   * Ports/Exports
   */ 
   
   uvm_analysis_port #(AluOutputTransaction) aport_alu_out_if;
  
  /*! 
   * Data Members
   */
  
   AluAgentConfig alu_agent_cfg; // agent configuration
   
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluMonitor", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern function void connect_phase(uvm_phase phase); 
   extern task run_phase(uvm_phase phase); 
   
   // OWN UVM methods
   extern task waitForVld();
   
 endclass: AluMonitor
 
 
 
/*! 
 * Constructor - creates the AluMonitor object  
 */
 function AluMonitor::new(string name = "AluMonitor", uvm_component parent = null);
   super.new(name, parent);
 endfunction: new



/*! 
 * Build - instanciates child components
 */ 
 function void AluMonitor::build_phase(uvm_phase phase);
   super.build_phase(phase);
   
   // get configuration
   if (!uvm_config_db #(AluAgentConfig)::get(this, "", "AluAgentConfig", alu_agent_cfg)) 
     `uvm_error("MYERR", "AluAgentConfig doesn't exist!");
     
   // create analysis port
   aport_alu_out_if = new("aport_alu_out_if", this);  
 endfunction: build_phase   
 
 
 
/*! 
 * Connect - interconnection of AluMonitor components.
 */  
 function void AluMonitor::connect_phase(uvm_phase phase);
   super.connect_phase(phase);
   dut_alu_out_if = alu_agent_cfg.dut_alu_out_if;
 endfunction: connect_phase
 
 

/*! 
 * Run - starts monitor processing.
 */  
 task AluMonitor::run_phase(uvm_phase phase); 
   AluOutputTransaction alu_out_trans, alu_out_trans_c;    
   
   // check RESET
   while (dut_alu_out_if.RST) 
     @(dut_alu_out_if.cb); 
   
   // create output transaction  
   alu_out_trans = AluOutputTransaction::type_id::create();  
   
   forever
     begin
       // wait for EX_ALU_VLD = 1
       waitForVld();
       
       // clone output transaction
       assert($cast(alu_out_trans_c, alu_out_trans.clone));
       
       // receive the value of output
       alu_out_trans.ex_alu = dut_alu_out_if.cb.EX_ALU;
       
       // display the content of transaction 
       alu_out_trans.print("MONITOR:"); 
       
       // sends generated transaction to the scoreboard, subscriber etc.
       aport_alu_out_if.write(alu_out_trans);
       
       // synchronisation with the DUT
       @(dut_alu_out_if.cb);
     end
 endtask: run_phase 
 


/*! 
 * Wait for validity of output EX_ALU and not RESET.
 */ 
 task AluMonitor::waitForVld();
   while (!(dut_alu_out_if.cb.EX_ALU_VLD === 1))  
     @(dut_alu_out_if.cb);
 endtask: waitForVld