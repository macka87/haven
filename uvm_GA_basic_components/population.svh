/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    population.svh
 * Description:  Genetic Algorithm Population Class
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         10.5.2013  
 * ************************************************************************** */

/*!
 * \brief Population
 * 
 * This class defines population and basic operations performed with population.
 */

 class Population extends uvm_sequencer #(Chromosome);
 
   //! UVM Factory Registration Macro
   `uvm_component_utils(Population)
  
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "Population", uvm_component parent = null);
   
 endclass : Population
  
