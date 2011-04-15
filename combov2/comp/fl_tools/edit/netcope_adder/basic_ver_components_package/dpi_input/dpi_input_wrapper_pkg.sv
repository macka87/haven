/* *****************************************************************************
 * Project Name: Hardware - Software Framework for Functional Verification 
 * File Name:    Input DPI layer
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

/*!
 * This package calls functions written in C language. Their purpose is 
 * communication with HW and data transfer to HW.  
 */

package dpi_input_wrapper_pkg;
  
  // C function for sending data to hardware
  import "DPI-C" context function int c_sendData(input byte unsigned hwpacket[]);

endpackage : dpi_input_wrapper_pkg
