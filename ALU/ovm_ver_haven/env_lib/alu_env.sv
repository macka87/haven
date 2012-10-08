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
   AluSequencer        AluSequencer_h;
   AluDriver           AluDriver_h;
   AluMonitor          AluMonitor_h;
   AluScoreboard       AluScoreboard_h;
   AluInputSubscriber  AluInputSubscriber_h;
   AluOutputSubscriber AluOutputSubscriber_h;

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
     AluInputSubscriber_h  = new("AluInputSubscriber_h", this);
     AluOutputSubscriber_h = new("AluOutputSubscriber_h", this);
    
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
     
     // DRIVER => SUBSCRIBER   
     AluDriver_h.aport_alu_in_if.connect(AluInputSubscriber_h.analysis_export);
     
     // MONITOR => SCOREBOARD
     AluMonitor_h.aport_alu_out_if.connect(AluScoreboard_h.export_alu_out_if);
 
     // MONITOR => SUBSCRIBER   
     AluMonitor_h.aport_alu_out_if.connect(AluOutputSubscriber_h.analysis_export);
     
   endfunction: connect

  /*! 
   * Run - runs the simulation
   */ 
   task run;
     string msg;
     
     if(GEN_OUTPUT<0 || GEN_OUTPUT>2) begin
       $sformat(msg, "Parameter GEN_OUTPUT must be from {0,1,2,3}!\n");
       ovm_report_fatal("ALU_ENV", msg, OVM_NONE);
     end
  
   endtask: run
  
 endclass: AluEnv

