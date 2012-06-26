/* *****************************************************************************
 * Project Name: Hardware - Software Framework for Functional Verification 
 * File Name:    C Wrapper for MI32 initialization 
 * Description: 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2012 
 * ************************************************************************** */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <combosix.h>
#include "mi32_wrapper_pkg.h"

//-----------------------------------------------------------------------------
//- GLOBAL VARIABLES
//-----------------------------------------------------------------------------
char        *file     = CS_PATH_DEV(0); // Set device file path
cs_target_t space 		= CS_SPACE_FPGA;  // Select space, 'fpga' is default

cs_device_t *d;        // Combo6 device structure 
cs_space_t 	*s;        // Mallocated space structure 
cs_size_t 	mapsize;   // Region size in bytes 
cs_addr_t  	offs;      // Absolute region offset in bytes 

//-----------------------------------------------------------------------------
//- USER Functions  
//- combosix.h library functions:
//- http://www.liberouter.org/~perex/libcombo/html/combosix_8h.html#a29
//-----------------------------------------------------------------------------

/*
 * Starts the MI32 transfer. 
 */ 
int c_start_mi32_transfer(cs_addr_t hw_addr) {
  
  if (cs_attach(&d, file) != 0) 
    return EXIT_FAILURE; // cs_attach failed
  
  mapsize = 4;
  
  if (cs_space_map(d, &s, space, mapsize, hw_addr, 0) != 0)
		return EXIT_FAILURE; // cs_space_map failed

  return EXIT_SUCCESS;
} 
 
/*
 *  Write value to register through MI32 interface. 
 *  
 *  cs_addr_t addr - relative offset into space structure in bytes
 *  u_int32_t data - input data     
 */
void c_writeToRegister(cs_addr_t addr, u_int32_t data){
  cs_space_write_4(d, s, addr, data);
}  

/*
 *  Read value from register through MI32 interface. 
 *  
 *  cs_addr_t addr - relative offset into space structure in bytes
 *  u_int32_t data - input data     
 */
void c_readFromRegister(cs_addr_t addr, u_int32_t data){
  data = cs_space_read_4(d, s, addr);
}

/*
 * Ends the MI32 transfer. 
 */ 
void c_end_mi32_transfer() {
  
  cs_space_unmap(d, &s);
	cs_detach(&d);
} 
