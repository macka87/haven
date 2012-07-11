/* *****************************************************************************
 * Project Name: Hardware - Software Framework for Functional Verification 
 * File Name:    SystemVerilog DPI Transaction Table package
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         5.3.2011 
 * ************************************************************************** */

/*!
 * This package calls functions written in C language. Their purpose is to 
 * add and remove transactions from scoreboard table after comparison.  
 */

package dpi_tr_table_pkg;
  
  /*
   *  Add transaction to scoreboard table. 
   */
  import "DPI-C" context function void c_addToTable(input byte unsigned inTrans[]);
  
  /*
   *  Check emptiness of transaction table.
   */
  import "DPI-C" context function int c_tableEmpty();
   
  /*
   *  Remove transaction from scoreboard table.
   */
  import "DPI-C" context function int c_removeFromTable(inout byte unsigned outTrans[]);
  
  /*
   *  Display final state of transaction table. 
   */ 
  import "DPI-C" context function void c_displayTable();
  
endpackage : dpi_tr_table_pkg
