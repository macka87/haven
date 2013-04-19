/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_env.svh
 * Description:  ALU environment.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*! 
 * Constructor - creates the AluEnv object  
 */
 function AluEnv::new(string name = "AluEnv", uvm_component parent = null);
   super.new(name, parent);
 endfunction: new
 

 
 /*! 
 * Build - environment configuration
 */ 
 function void AluEnv::build_phase(uvm_phase phase);
 endfunction: build_phase
 
 
 
 /*! 
 * Connect - interconnection of environment components
 */ 
 function void AluEnv::connect_phase(uvm_phase phase);
 endfunction: connect_phase