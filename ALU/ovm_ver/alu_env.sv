/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_env.sv
 * Description:  OVM Basic Enviroment Class
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         10.9.2012
 * ************************************************************************** */

/*!
 * \brief AluEnv
 * 
 * This class is verification enviroment which contains agents, subscribers and
 * scoreboards.
 */
 class AluEnv #(int pDataWidth = 8) extends ovm_env;
  
   //registration of component tools
   `ovm_component_utils(my_env)
    
   //handles to the contained objects
   AluAgent #(pDataWidth) AluAgent_h;
   AluSubscriber #(pDataWidth) AluSubscriber_h;
   AluScoreboard #(pDataWidth) AluScoreboard_h;

  /*! 
   * Constructor - creates AluEnv object  
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
     AluAgent_h = my_agent ::type_id::create("AluAgent_h" , this);
     AluSubscriber_h = my_subscriber::type_id::create("AluSubscriber_h" , this);
     AluScoreboard_h = my_scoreboard::type_id::create("AluScoreboard_h", this); 
   endfunction: build

  /*! 
   * Connect - connects ports of the child components so they can communicate
   */    
   function void connect;
     AluAgent_h.aport_zadanie.connect(AluSubscriber_h.analysis_export);
     AluAgent_h.aport_zadanie.connect(AluScoreboard_h.driver_export);
     AluAgent_h.aport_vysledok.connect(AluScoreboard_h.monitor_export);
   endfunction: connect

  /*! 
   * Run - runs the simulation
   */ 
   task run;
      
     //after 50 time units stop the simulation
     //the driver stops the simulation now because of the small number of loops
     #50 ovm_top.stop_request();
   
   endtask: run
  
  endclass: my_env 