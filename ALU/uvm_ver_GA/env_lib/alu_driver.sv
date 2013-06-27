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
   
 endfunction: build_phase   
  
/*! 
 * Connect - interconnection of AluDriver components.
 */  
 function void AluDriver::connect_phase(uvm_phase phase);
 
 endfunction: connect_phase