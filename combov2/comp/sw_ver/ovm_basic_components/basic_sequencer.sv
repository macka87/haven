/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    basic_sequencer.sv
 * Description:  OVM Basic Sequencer Class
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         16.8.2012
 * ************************************************************************** */

 `include "ovm_macros.svh"

 package BasicSequencer_pkg;
  
   //include official ovm package
   import ovm_pkg::*;

  /*!
   * \brief BasicSequencer
   * 
   * This class is parent class for any sequencer.
   */
   class BasicSequencer extends ovm_sequencer #(BasicTransaction);
    
     //registracia komponenty
     `ovm_component_utils(BasicSequencer)

    /*
     * Public Class Atributes
     */

     int input_file;        // input file with transactions
     int output_file;       // output file with transactions
    
    /*
     * GENERATOR INPUT.
     *
     * Enumeration type for inputs of Generator:
     * SV_GEN      = SystemVerilog generator of transactions
     * EXT_FILE_IN = reading transactions from external file  
     * OTHER_GEN   = other generator of transactions
     * HW_GEN      = hardware generator of transactions 
     */
     tGenInput gen_input = SV_GEN;
    
    /*
     * GENERATOR OUTPUT.
     *
     * Enumeration type for storage outputs of Generator
     * SV_SIM          = SystemVerilog simulation
     * EXT_FILE_OUT    = storing transactions into external file
     * SV_SIM_EXT_FILE = SystemVerilog simulation and storing to ext. file
     */
     tGenOutput gen_output = SV_SIM;

    /*!
     * The generator will stop after the specified number of object
     * instances has been generated and consumed by the output channel.
     * The generator must be reset before it can be restarted. If the
     * value of this property is 0, the generator will not stop on
     * its own.
     */
     int unsigned stop_after_n_insts = 0;
  
    /*! 
     * Constructor - creates BasicSequencer object  
     *
     * \param name       - sequencer instance name
     * \param parent     - parent class identification
     * \param gen_input  - source of transactions' flow
     * \param gen_output - destination of transactions' flow   
     */  
     function new (string name,
                   ovm_component parent, 
                   tGenInput gen_input = SV_GEN,
                   tGenOutput gen_output = SV_SIM);
       super.new(name, parent);
       this.gen_input  = gen_input;
       this.gen_output = gen_output;
     endfunction: new

    /*! 
     * Build - instanciates child components
     */     
     function void build;
       super.build();
     endfunction: build
   
    /*
     * Iniciate generator in full HW version of framework.  
     */     
     task initiateHW(int unsigned nInst=32'hFFFFFFFF);
       stop_after_n_insts = nInst;
     endtask : initiateHW
   
   endclass: BasicSequencer
 
 endpackage: BasicSequencer_pkg