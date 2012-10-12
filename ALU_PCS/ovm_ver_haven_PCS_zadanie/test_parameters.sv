/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    test_pkg.sv - test package
 * Description:  Definition of constants and parameters 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz>,
 *               Michaela Belesova <xbeles00@stud.fit.vutbr.cz>   
 * Date:         18.9.2012 
 * ************************************************************************** */ 

 package sv_alu_param_pkg;
   
   // DUT GENERICS
   parameter DATA_WIDTH     = 8; // data width
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD     = 10ns;
   parameter RESET_TIME     = 10*CLK_PERIOD;
     
   // TEST PARAMETERS
   parameter TRANSACTION_COUT = 100; // Count of transactions
   parameter SEED1            = 0;     // Seed for PRNG
   
 endpackage
