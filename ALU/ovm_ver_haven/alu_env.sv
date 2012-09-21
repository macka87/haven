/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_env.sv
 * Description:  OVM Basic Enviroment Class
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         20.9.2012
 * ************************************************************************** */

`include "ovm_macros.svh"

package sv_alu_pkg;
 
 import ovm_pkg::*;
 
/*!
 * \brief AluEnv
 * 
 * This class is verification enviroment which contains agents, subscribers and
 * scoreboards.
 * 
 * \param pDataWidth - data width of the verified ALU  
 * \param GEN_OUTPUT - destination for generated data   
 */
 class AluEnv #(int pDataWidth = 8, int GEN_OUTPUT=0) 
   extends ovm_env;
  
   //registration of component tools
   `ovm_component_utils(my_env)
   
   //handles to the contained objects
   AluDriver #(pDataWidth,GEN_OUTPUT) AluDriver_h;
   AluMonitor #(pDataWidth) AluMonitor_h;
   AluSequencer #(pDataWidth) AluSequencer_h;
   AluSender #(pDataWidth) AluSender_h;
   //AluScoreboard #(pDataWidth) AluScoreboard_h;
   //AluSubscriber #(pDataWidth) AluSubscriber_h;

  /*! 
   * Constructor - creates AluEnv object  
   *
   * \param name       - instance name
   * \param parent     - parent class identification
   */ 
   function new(string name, ovm_component parent);
     super.new(name, parent);
   endfunction: new

  /*! 
   * Build - instanciates child components
   */
   function void build;
     super.build();
     
     AluDriver_h = AluDriver::type_id::create("AluDriver_h", this);
     AluSequencer_h = AluSequencer::type_id::create("AluSequencer_h", this);
     
     if(GEN_OUTPUT==0 || GEN_OUTPUT==2)
       begin
         AluMonitor_h = AluMonitor::type_id::create("AluMonitor_h", this);
              
         /*AluScoreboard_h = AluScoreboard::type_id::create("AluScoreboard_h", this);
         AluSubscriber_h = AluSubscriber::type_id::create("AluSubscriber_h", this);*/
       end
       
     if(GEN_OUTPUT==1 || GEN_OUTPUT==2)
       AluSender_h = AluSender::type_id::create("AluSender_h", this);
        
   endfunction: build

  /*! 
   * Connect - connects ports of the child components so they can communicate
   */    
   function void connect;
     
     AluDriver_h.seq_item_port.connect(AluSequencer_h.seq_item_export);
     
     if(GEN_OUTPUT==0 || GEN_OUTPUT==2)
       begin
         /*AluMonitor_h.aport_dut_output.connect(AluScoreboard_h.aport_dut_output);
         AluDriver_h.aport_dut_input.connect(AluScoreboard_h.aport_dut_input);
         AluDriver_h.aport_dut_input.connect(AluSubscriber_h.analysis_export);*/
       end
     
     if(GEN_OUTPUT==1 || GEN_OUTPUT==2)
       AluDriver_h.aport_dut_input.connect(AluSender_h.aport_dut_input);
   
   endfunction: connect

  /*! 
   * Run - runs the simulation
   */ 
   task run;
     
     if(GEN_OUTPUT<0 || GEN_OUTPUT>2) 
       $fatal("AluEnv: Parameter GEN_OUTPUT must be from {0,1,2,3}");
              
     //after 50 time units stop the simulation
     //the driver stops the simulation now because of the small number of loops
     #50 ovm_top.stop_request();
   
   endtask: run
  
  endclass: AluEnv

endpackage