/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    test_pkg.sv - test package
 * Description:  Definition of constants and parameters. 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */ 

package test_pkg;
   
   import math_pkg::*;       
      
   // DUT GENERICS
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT 
        
   // TEST PARAMETERS
   parameter TRANSACTION_COUT = 1; // Count of transactions

endpackage
