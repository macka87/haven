/* *****************************************************************************
 * Project Name: NetCOPE Adder Functional Verification
 * File Name:    test_pkg.sv - test package
 * Description:  Definition of constants and parameters 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */ 

package test_pkg;
   
   import math_pkg::*;       
   
   // VERIFICATION FRAMEWORK
   int FRAMEWORK  = 0;                         // 0 = software framework
                                               // 1 = sw/hw framework      
   // DUT GENERICS
   parameter DATA_WIDTH   = 64;                // FrameLink data width
   parameter DREM_WIDTH   = log2(DATA_WIDTH/8);// drem width
   parameter USE_BRAMS    = 1;                 // Use BlockBAMs/SelectRAMs 
   parameter ITEMS        = 1024;              // Number of items in the FIFO
   parameter BLOCK_SIZE   = 16;                // Size of block (for LSTBLK signal)
   parameter STATUS_WIDTH = 7;                 // Width of STATUS signal available
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD   = 10ns;
   parameter RESET_TIME   = 10*CLK_PERIOD;
   parameter SIM_DELAY    = 100;

   // TRANSACTION FORMAT 
   int GENERATOR_FL_FRAME_COUNT     = 1;       // frame parts
   int GENERATOR_FL_PART_SIZE_MAX[] = '{36};   // maximal size of part
   int GENERATOR_FL_PART_SIZE_MIN[] = '{1};    // minimal size of part     
   
   // SOFTWARE DRIVER PARAMETERS 
   // Enable/Disable weights of "delay between transactions" 
   parameter byte DRIVER_BT_DELAY_EN_WT  = 0;       
   parameter byte DRIVER_BT_DELAY_DI_WT  = 10;
   // Low/High limit of "delay between transactions" value
   parameter byte DRIVER_BT_DELAY_LOW    = 0;
   parameter byte DRIVER_BT_DELAY_HIGH   = 10;
   // Enable/Disable weights of "delays inside transaction"
   parameter byte DRIVER_IT_DELAY_EN_WT  = 0;
   parameter byte DRIVER_IT_DELAY_DI_WT  = 10;
   // Low/High limit of "delay inside transaction" values
   parameter byte DRIVER_IT_DELAY_LOW    = 0;
   parameter byte DRIVER_IT_DELAY_HIGH   = 10;
   
   // SOFTWARE RESPONDER PARAMETERS 
   // Low/High limit of "delay between transactions" value
   parameter byte RESPONDER_BT_DELAY_LOW    = 0;
   parameter byte RESPONDER_BT_DELAY_HIGH   = 10;
   // Low/High limit of "delay inside transaction" values
   parameter byte RESPONDER_IT_DELAY_LOW    = 0;
   parameter byte RESPONDER_IT_DELAY_HIGH   = 10;

   // TEST PARAMETERS
   parameter TRANSACTION_COUT = 300;  // Count of transactions
   parameter SEED1            = 1;  // Seed for PRNG
   parameter SEED2            = 2;  // Seed for PRNG
endpackage
