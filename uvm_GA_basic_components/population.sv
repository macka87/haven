/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    population.sv
 * Description:  Genetic Algorithm Population Class
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         10.5.2013  
 * ************************************************************************** */

/*! 
 * Constructor - creates the Population object  
 */
 function Population::new(string name = "Population", uvm_component parent = null);
   super.new(name, parent);
 endfunction: new

    
