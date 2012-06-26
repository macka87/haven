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

package mi32_wrapper_pkg;

  /*
   * Starts the MI32 transfer. 
   */ 
   import "DPI-C" context function int c_start_mi32_transfer(input logic [31:0] hw_addr);
  
  /*
   *  Write value to register through MI32 interface. 
   *  
   *  cs_addr_t addr - relative offset into space structure in bytes
   *  u_int32_t data - input data     
   */
   import "DPI-C" context function void c_writeToRegister(input logic [31:0] addr, input logic [31:0] data);

  /*
   *  Read value from register through MI32 interface. 
   *  
   *  cs_addr_t addr - relative offset into space structure in bytes
   *  u_int32_t data - input data     
   */
   import "DPI-C" context function void c_readFromRegister(input logic [31:0] addr, inout logic [31:0] data);
 
  /*
   * Ends the MI32 transfer. 
   */ 
   import "DPI_C" pure function void c_end_mi32_transfer();
  
endpackage : mi32_wrapper_pkg
