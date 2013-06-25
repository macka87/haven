/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_ga_test.svh
 * Description:  UVM GA Test for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         19.4.2013
 * ************************************************************************** */

/*!
 * \brief AluGATest
 * 
 * This class represents UVM test for ALU.
 */
 
 class AluGATest extends AluTestBase;
    
   //! UVM Factory Registration Macro
   `uvm_component_utils(AluGATest)
   
  /*! 
   * Data Members
   */
   // Configuration objects
   ChromosomeConfig         chromosome_cfg;
   AluChromosomeConfig      alu_chromosome_cfg;
   ChromosomeSequenceConfig chromosome_sequence_cfg;
   
  /*! 
   * Component Members
   */ 
   Population population_sequencer; 

   /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluGATest", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   
   // Other methods
   extern task main_phase(uvm_phase phase);
   extern function void configure_chromosome(ChromosomeConfig chromosome_cfg);
   extern function void configure_alu_chromosome(AluChromosomeConfig alu_chromosome_cfg);
   extern function void configure_chromosome_sequence(ChromosomeSequenceConfig chromosome_sequence_cfg);
   extern task createOrLoadInitialPopulation();
   
 endclass: AluGATest