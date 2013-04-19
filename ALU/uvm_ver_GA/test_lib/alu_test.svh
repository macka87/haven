/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_test.svh
 * Description:  UVM Test for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*!
 * \brief AluTest
 * 
 * This class represents UVM test for ALU.
 */
 
 class AluTest extends AluTestBase;
    
   //! UVM Factory Registration Macro
   `uvm_component_utils(AluTest)

   /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluTest", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   // Other methods
   extern task main_phase(uvm_phase phase);

 endclass: AluTest