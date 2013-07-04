/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_driver.sv
 * Description:  UVM Driver Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2013
 * ************************************************************************** */

/*!
 * \brief AluDriver
 * 
 * This class drives the input interface of ALU and supplies transactions from 
 * sequencer to this interface.
 */

 class AluDriver extends uvm_driver #(AluInputTransaction);

   //! UVM Factory Registration Macro
   `uvm_component_utils(AluDriver)
  
  /*!
   * Component Members
   */ 
  
   // reference to the input virtual interface
   virtual iAluIn dut_alu_in_if;
   
   // agent configuration
   AluAgentConfig alu_agent_cfg;
   
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluDriver", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern function void connect_phase(uvm_phase phase); 
   extern task run_phase(uvm_phase phase); 
   
   // Own UVM methods
   extern task waitForAluRdy();
   
 endclass: AluDriver
