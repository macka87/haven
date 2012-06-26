/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Genetic Algorithm Components Package
 * Description: 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         14.6.2012 
 * ************************************************************************** */

package ga_pkg; 
  typedef enum {PROPORTIONATE, RANK} selection_t;

  `include "chromosome.sv"
  `include "population.sv"
endpackage : ga_pkg
