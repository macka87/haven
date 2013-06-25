/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    sv_basic_ga_pkg.sv
 * Description:  UVM Genetic Algorithm Components Package.
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         10.5.2013
 * ************************************************************************** */

 package sv_basic_ga_pkg; 
  
   // Standard UVM import & include
   import uvm_pkg::*;
   `include "uvm_macros.svh"
  
   typedef enum {PROPORTIONATE, RANK} selection_t;

   // Includes
   `include "chromosome.svh"
   `include "chromosome.sv"
   `include "population.svh"
   `include "population.sv"
   
 endpackage : sv_basic_ga_pkg
