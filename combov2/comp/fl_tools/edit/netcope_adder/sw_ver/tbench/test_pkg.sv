/* *****************************************************************************
 * Project Name: NetCOPE Adder Functional Verification
 * File Name:    test_pkg.sv - test package
 * Description:  Definition of constants and parameters 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */ 

package test_pkg;
   
   import math_pkg::*;       
      
   // DUT GENERICS
   parameter DATA_WIDTH = 128;            // FrameLink data width
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT 
   int GENERATOR_FL_FRAME_COUNT     = 1;              // frame parts
   int GENERATOR_FL_PART_SIZE_MAX[] = '{650,650,650}; // maximal size of part
   int GENERATOR_FL_PART_SIZE_MIN[] = '{1,1,1};       // minimal size of part     

   // TEST PARAMETERS
   parameter TRANSACTION_COUT = 10;        // Count of transactions

endpackage
