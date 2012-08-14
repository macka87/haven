/* *****************************************************************************
 * Project Name: Hardware - Software Framework for Functional Verification 
 * File Name:    C Wrapper for MI32 initialization 
 * Description: 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2012 
 * ************************************************************************** */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <combosix.h>
#include "dpi_mi32_wrapper_pkg.h"

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
int c_start_mi32_transfer(cs_addr_t addr) {
    
  if (cs_attach(&d, file) != 0) { 
    printf("CS ATTACH FAILED!\n");
    return EXIT_FAILURE; // cs_attach failed
  }
  mapsize = 4;
  
  if (cs_space_map(d, &s, space, mapsize, addr, 0) != 0) {
		printf("CS SPACE MAP FAILED!\n");
    return EXIT_FAILURE; // cs_space_map failed        
  } 
  return EXIT_SUCCESS;
} 

/*
 * Ends the MI32 transfer. 
 */ 
void c_end_mi32_transfer() {
  
  cs_space_unmap(d, &s);
	cs_detach(&d);
}
 
/*
 *  Write value to register through MI32 interface. 
 *  
 *  cs_addr_t addr - relative offset into space structure in bytes
 *  u_int32_t data - input data     
 */
void c_writeToRegister(const svBitVecVal* hw_addr, const svBitVecVal* hw_data){
  cs_addr_t addr = hw_addr[0];
  u_int32_t data = hw_data[0];
  
  if (c_start_mi32_transfer(addr)) 
    printf("It is not possible to configure hardware registers with MI32!!!");
  
  assert(NULL != d);
  assert(NULL != s);
  
  cs_space_write_4(d, s, 0, data);
  
  c_end_mi32_transfer();
} 

/*
 *  Read value from register through MI32 interface. 
 *  
 *  cs_addr_t addr - relative offset into space structure in bytes
 *  u_int32_t data - input data     
 */
void c_readFromRegister(const svBitVecVal* hw_addr, svBitVecVal* hw_data){
  u_int32_t data;
  cs_addr_t addr = hw_addr[0];
  
  if (c_start_mi32_transfer(addr)) 
    printf("It is not possible to configure hardware registers with MI32!!!");
  
  assert(NULL != d);
  assert(NULL != s);
  
  data = cs_space_read_4(d, s, 0);
  
  hw_data[0] = data; 
  
  c_end_mi32_transfer();
}

 
