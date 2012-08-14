/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    sv_types_pkg.sv
 * Description:  SystemVerilog User Defined Types 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         3.7.2011 
 * ************************************************************************** */

package sv_types_pkg; 

  /*
   * Enumeration type for Framework type
   * SW = software
   * HW = hardware
   * G  = generator included
   * E  = enumaration part included
   * S  = scoreboard included
   * D  = design (DUT) included
   */    
   typedef enum {SW_FULL,           
                 HW_FULL,           
                 SW_GES_HW_D,       
                 SW_ES_HW_GD,        
                 SW_GE_HW_DS,       
                 SW_E_HW_GDS,
                 SW_DES_HW_G
                 } tFramework; 
                 
  /*
   * Enumeration type for inputs of Generator
   * SV_GEN      = SystemVerilog generator of transactions
   * EXT_FILE_IN = reading transactions from external file  
   * OTHER_GEN   = other generator of transactions
   * HW_GEN      = hardware generator of transactions 
   */ 
   typedef enum {SV_GEN, EXT_FILE_IN, OTHER_GEN, HW_GEN} tGenInput;   
   
  /*
   * Enumeration type for storage outputs of Generator
   * SV_SIM          = SystemVerilog simulation
   * EXT_FILE_OUT    = storing transactions into external file
   * SV_SIM_EXT_FILE = SystemVerilog simulation and storing to ext. file
   */ 
   typedef enum {SV_SIM, EXT_FILE_OUT, SV_SIM_EXT_FILE} tGenOutput;
                                                 
endpackage : sv_types_pkg
