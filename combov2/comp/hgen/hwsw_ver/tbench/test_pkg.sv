/* *****************************************************************************
 * Project Name: HGEN Functional Verification
 * File Name:    test_pkg.sv - test package
 * Description:  Definition of constants and parameters 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         24.4.2011 
 * ************************************************************************** */

package test_pkg;

   import math_pkg::*;
   import sv_types_pkg::*; 
   
   // VERIFICATION FRAMEWORK
  /*
   * Enumeration type for Framework definition
   * SW = software
   * HW = hardware
   * G  = generator included
   * E  = enumaration part included
   * S  = scoreboard included
   * D  = design (DUT) included
   * 
   * Supported options: 
   * SW_FULL           
   * HW_FULL           
   * SW_GES_HW_D       
   * SW_ES_HW_GD        
   * SW_GE_HW_DS - unsopported     
   * SW_E_HW_GDS - unsupported 
   * SW_DES_HW_G
   */ 
   parameter tFramework FRAMEWORK = SW_FULL;  
     
   // DUT GENERICS
   parameter BRANCH_COUNT = 4;                  // number of HGEN units
   parameter USE_BRAMS_FOR_HGEN_FIFO = 0;
   parameter DATA_WIDTH   = 128;                // datova sirka RX
   parameter DREM_WIDTH   = log2(DATA_WIDTH/8); // drem  sirka RX
      
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
   
   // GENERATOR PARAMETERS
 
  /*
   * Enumeration type for inputs of Generator
   * SV_GEN      = SystemVerilog generator of transactions
   * EXT_FILE_IN = reading transactions from external file  
   * OTHER_GEN   = other generator of transactions
   * HW_GEN      = hardware generator of transactions 
   */ 
   parameter tGenInput GEN_INPUT = SV_GEN;  
   
  /*
   * Enumeration type for storage outputs of Generator
   * SV_SIM          = SystemVerilog simulation
   * EXT_FILE_OUT    = storing transactions into external file
   * SV_SIM_EXT_FILE = SystemVerilog simulation and storing to ext. file
   */ 
   parameter tGenOutput GEN_OUTPUT = SV_SIM; 
   
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
   parameter TRANSACTION_COUNT = 100000;  // Count of transactions
   parameter SEED1             = 1;      // Seed for PRNG
   parameter SEED2             = 2;      // Seed for PRNG
endpackage
