/* *****************************************************************************
 * Project Name: HGEN Functional Verification
 * File Name:    test_pkg.sv - test package
 * Description:  Definition of constants and parameters 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         24.4.2011 
 * ************************************************************************** */

package test_pkg;

   // VERIFICATION FRAMEWORK
   int FRAMEWORK  = 1;                      // 0 = software framework
                                            // 1 = sw/hw framework      
   // DUT GENERICS
   parameter DATA_WIDTH = 128;           // datova sirka RX
   parameter DREM_WIDTH = 4;             // drem  sirka RX
      
   // size of UH header (bytes 16 - 64)
   parameter UH_SIZE      = 64;
   // width of flow id (bits 32 - 128)
   parameter FLOWID_WIDTH = 128;
   // inicialisation vector of HGEN unit
   bit[31:0] HGEN_INIT = 32'b10100101101001000101110111010111;
   // mask for masking bytes in UH header
   bit[UH_SIZE-1:0] HGEN_MASK = 64'hFFFFFFFFFFFFFFFF;
   // items in FL fifo
   parameter ITEMS = 64;
   
   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;
   parameter SIM_DELAY  = 100;
   
   // TRANSACTION FORMAT 
   parameter GENERATOR_FL_FRAME_COUNT       = 1;                // frame parts
   int       GENERATOR_FL_PART_SIZE_MAX[]   = '{UH_SIZE};       // maximal size of part
   int       GENERATOR_FL_PART_SIZE_MIN[]   = '{UH_SIZE};       // minimal size of part 
   bit[63:0] DATA_IN                        = 'd6418;

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
   parameter TRANSACTION_COUT = 50000;  // Count of transactions
   parameter SEED1            = 1;    // Seed for PRNG
   parameter SEED2            = 2;    // Seed for PRNG
endpackage
