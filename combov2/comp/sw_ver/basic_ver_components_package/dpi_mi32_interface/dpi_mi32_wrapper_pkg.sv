/* *****************************************************************************
 * Project Name: Hardware - Software Framework for Functional Verification 
 * File Name:    SV Wrapper for MI32 initialization 
 * Description: 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.6.2012 
 * ************************************************************************** */

/*!
 * This package calls functions written in C language. Their purpose is 
 * communication with HW and setting of registers in HW.  
 */

package dpi_mi32_wrapper_pkg;

  /*
   * Starts the MI32 transfer. 
   */ 
   //import "DPI-C" context function int c_start_mi32_transfer(input bit [31:0] hw_addr);
  
  /*
   *  Write value to register through MI32 interface. 
   *  
   *  cs_addr_t addr - relative offset into space structure in bytes
   *  u_int32_t data - input data     
   */
   import "DPI-C" context function void c_writeToRegister(input bit [31:0] hw_addr, input bit [31:0] hw_data);

  /*
   *  Read value from register through MI32 interface. 
   *  
   *  cs_addr_t addr - relative offset into space structure in bytes
   *  u_int32_t data - input data     
   */
   import "DPI-C" context function void c_readFromRegister(input bit [31:0] hw_addr, inout bit [31:0] hw_data);
 
  /*
   * Ends the MI32 transfer. 
   */ 
   //import "DPI-C" pure function void c_end_mi32_transfer();
  
endpackage : dpi_mi32_wrapper_pkg
