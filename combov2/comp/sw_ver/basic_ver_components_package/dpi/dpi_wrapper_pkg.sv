/* *****************************************************************************
 * Project Name: Hardware - Software Framework for Functional Verification 
 * File Name:    SystemVerilog DPI layer package
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         3.5.2011 
 * ************************************************************************** */

/*!
 * This package calls functions written in C language. Their purpose is 
 * communication with HW and data transfer to HW.  
 */

package dpi_wrapper_pkg;
  
  /*
   *  Open DMA Channel for data transport. 
   */
  import "DPI-C" pure function int c_openDMAChannel();
  
  /*
   *  Close DMA Channel after data transport. 
   */
  import "DPI-C" pure function int c_closeDMAChannel(); 
  
  /*
   *  Data transport through DMA Channel to HW. 
   */
  import "DPI-C" context function int c_sendData(input byte unsigned inhwpkt[]);
  
  /*
   *  Data transport through DMA Channel from HW and comparison in scoreboard 
   *  table. 
   */
  import "DPI-C" context function int c_receiveData(output int unsigned size, inout byte unsigned outhwpkt[]);
  
endpackage : dpi_wrapper_pkg
