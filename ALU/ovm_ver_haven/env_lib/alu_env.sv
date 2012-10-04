/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_env.sv
 * Description:  OVM Basic Enviroment Class
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         20.9.2012
 * ************************************************************************** */

/*!
 * \brief AluEnv
 * 
 * This class represents the main parts of the verification enviroment.
 */
 class AluEnv extends ovm_env;
  
   // registration of component tools
   `ovm_component_utils(AluEnv)
   
   // handles to the main objects
   AluSequencer  AluSequencer_h;
   AluDriver     AluDriver_h;
   AluMonitor    AluMonitor_h;
   AluScoreboard AluScoreboard_h;
   
   //AluSender #(pDataWidth) AluSender_h;
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
     
     AluSequencer_h  = new("AluSequencer_h", this);
     AluDriver_h     = new("AluDriver_h", this);
     AluMonitor_h    = new("AluMonitor_h", this);
     AluScoreboard_h = new("AluScoreboard_h", this);
    
    /*
     if(GEN_OUTPUT==0 || GEN_OUTPUT==2)
       begin
         AluMonitor_h = AluMonitor::type_id::create("AluMonitor_h", this);
              
         AluScoreboard_h = AluScoreboard::type_id::create("AluScoreboard_h", this);
         AluSubscriber_h = AluSubscriber::type_id::create("AluSubscriber_h", this);
       end
       
     if(GEN_OUTPUT==1 || GEN_OUTPUT==2)
       AluSender_h = AluSender::type_id::create("AluSender_h", this); */
        
   endfunction: build

  /*! 
   * Connect - connects ports of the child components so they can communicate
   */    
   function void connect;
     
     super.connect();
     
     // SEQUENCER <= DRIVER 
     AluDriver_h.seq_item_port.connect(AluSequencer_h.seq_item_export);
     
     // DRIVER => SCOREBOARD
     AluDriver_h.aport_alu_in_if.connect(AluScoreboard_h.export_alu_in_if);     
     
     // MONITOR => SCOREBOARD
     AluMonitor_h.aport_alu_out_if.connect(AluScoreboard_h.export_alu_out_if);
 
     
     
     /*
     $write("AluSequencer: %d\n", AluSequencer_h.seq_item_export.size());    
     $write("AluDriver: %d\n", AluDriver_h.aport_alu_in_if.size());
     $write("AluScoreboard: %d\n", AluScoreboard_h.export_alu_in_if.size());
     $write("AluScoreboard name: %s\n", AluScoreboard_h.export_alu_in_if.get_name());
     */
     
          
     /*if(GEN_OUTPUT==0 || GEN_OUTPUT==2)
       begin
         AluMonitor_h.aport_dut_output.connect(AluScoreboard_h.aport_dut_output);
         AluDriver_h.aport_dut_input.connect(AluScoreboard_h.aport_dut_input);
         AluDriver_h.aport_dut_input.connect(AluSubscriber_h.analysis_export);
       end
     
     if(GEN_OUTPUT==1 || GEN_OUTPUT==2)
       AluDriver_h.aport_dut_input.connect(AluSender_h.aport_dut_input);*/
   
   endfunction: connect

   /*function void end_of_elaboration();
     AluScoreboard_h.export_alu_in_if.debug_connected_to();
     AluDriver_h.aport_alu_in_if.debug_connected_to();
   endfunction*/

  /*! 
   * Run - runs the simulation
   */ 
   task run;
     string msg;
     
     if(GEN_OUTPUT<0 || GEN_OUTPUT>2) begin
       $sformat(msg, "Parameter GEN_OUTPUT must be from {0,1,2,3}!\n");
       ovm_report_fatal("ALU_ENV", msg, OVM_NONE);
     end

     // end of the simulation
     //#20us ovm_top.stop_request();
   
   endtask: run
  
 endclass: AluEnv

