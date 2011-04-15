/* *****************************************************************************
 * Project Name: Hardware - Software Framework for Functional Verification 
 * File Name:    Ouput DPI layer
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

/*!
 * This package calls functions written in C language. Their purpose is 
 * communication with HW and data transfer from HW.  
 */

package dpi_output_wrapper_pkg;
  
  // C function for receiving data from hardware
  import "DPI-C" context function int c_receiveData(output byte unsigned hwpacket[]);

endpackage : dpi_output_wrapper_pkg
