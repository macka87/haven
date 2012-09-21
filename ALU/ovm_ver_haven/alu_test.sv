/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_test.sv
 * Description:  OVM Test for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         12.9.2012
 * ************************************************************************** */

`include "ovm_macros.svh"

package sv_alu_pkg;
 
 import ovm_pkg::*;
 import test_pkg::*;
  
/*!
 * \brief AluTest
 * 
 * This class is OVM test for ALU.
 */
 
 class AluTest extends ovm_test;
    
   //registration of component tools
   `ovm_component_utils(AluTest)

   //reference to the verification enviroment
   //test enviroment encapsulates verification enviroment
   AluEnv #(DATA_WIDTH, GEN_OUTPUT) AluEnv_h;

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
        
     if(GEN_INPUT==0) // 0 = SV generator of transactions
       begin
         SwSequence #(DATA_WIDTH) seq;
         seq = AluSequence::type_id::create("seq");
         seq.start( AluEnv_h.AluSequencer_h);
       end
       
     else if(GEN_INPUT==1) // 1 = reading transactions from external file
       begin
         FileSequence #(DATA_WIDTH) seq;
         seq = AluSequence::type_id::create("seq");
         seq.start( AluEnv_h.AluSequencer_h);
       end
       
     else if(GEN_INPUT==2) // 2 = other generator
       begin
       end
       
     else if(GEN_INPUT==3) // 3 = hardware generator 
       begin
       end
       
     else $fatal("AluTest: Parameter GEN_INPUT must be from {0,1,2,3}");
       
   endtask: run
  
 endclass: AluTest

endpackage