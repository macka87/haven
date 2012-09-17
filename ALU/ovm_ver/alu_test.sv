/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_test.sv
 * Description:  OVM Test for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         12.9.2012
 * ************************************************************************** */

`include "ovm_macros.svh"
package alu_test_pkg;
 import ovm_pkg::*;
 import alu_env_pkg::*;
 import alu_sequence_pkg::*; 
  
/*!
 * \brief AluTest
 * 
 * This class is OVM test for ALU.
 */
 
 class AluTest #(int pDataWidth = 8) extends ovm_test;
    
   //registration of component tools
   `ovm_component_utils(AluTest)

   //reference na instanciu verifikacneho prostredia
   //testovacie prostredie zabaluje verifikacne prostredie
   AluEnv #(pDataWidth) AluEnv_h;

  /*! 
   * Constructor - creates AluTest object  
   *
   * \param name     - instance name
   * \param parent   - parent class identification
   */
   function new(string name, ovm_component parent);
     super.new(name, parent);
   endfunction: new

  /*! 
   * Build - instanciates child components
   */ 
   function void build;
     super.build();
     AluEnv_h = AluEnv::type_id::create("AluEnv_h", this);
   endfunction: build

  /*! 
   * Run - runs the sequence of transactions
   */     
   task run;
     AluSequence #(pDataWidth) seq;
     seq = AluSequence::type_id::create("seq");
     seq.start( AluEnv_h.AluAgent_h.AluSequencer_h);
   endtask: run
  
 endclass: AluTest

endpackage: alu_test_pkg