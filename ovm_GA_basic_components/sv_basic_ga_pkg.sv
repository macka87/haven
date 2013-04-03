/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    sv_basic_ga_pkg.sv
 * Description:  Genetic Algorithm Components Package
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         2.4.2013 
 * ************************************************************************** */

package sv_basic_ga_pkg; 
  import ovm_pkg::*;
  
  typedef enum {PROPORTIONATE, RANK} selection_t;

  `include "ovm_macros.svh"
  `include "chromosome.sv"
  `include "population.sv"
endpackage : sv_basic_ga_pkg
