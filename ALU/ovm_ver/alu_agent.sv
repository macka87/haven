/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_agent.sv
 * Description:  OVM Agent for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         12.9.2012
 * ************************************************************************** */

 /*!
 * \brief AluAgent
 * 
 * This class contains OVM sequencer, driver and monitor
 */
 
 class AluAgent #(int pDataWidth = 8) extends ovm_agent;

   //registration of component tools
   `ovm_component_utils(my_agent)

   ovm_analysis_port #(AluTransaction) aport_dut_input;
   ovm_analysis_port #(AluTransactionResult) aport_dut_output;

   //handles to the contained objects
   AluSequencer AluSequencer_h;
   AluDriver #(pDataWidth) AluDriver_h;
   AluMonitor #(pDataWidth) AluMonitor_h;

  /*! 
   * Constructor - creates AluAgent object  
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
     
     //factory methods: allow changing the type and behavior of object
     //from elsewhere without rewriting the existing code
     AluSequencer_h = AluSequencer::type_id::create("AluSequencer_h", this);
     AluDriver_h = AluDriver ::type_id::create("AluDriver_h" , this);
     AluMonitor_h = AluMonitor ::type_id::create("AluMonitor_h" , this);
     
     aport_dut_input = new("aport_dut_input", this);
     aport_dut_output = new("aport_dut_output", this);
   endfunction: build

  /*! 
   * Connect - connects ports of the child components so they can communicate
   */    
   function void connect;
     AluDriver_h.seq_item_port.connect(AluSequencer_h.seq_item_export);
     AluDriver_h.aport.connect(aport_dut_input);
     AluMonitor_h.aport.connect(aport_dut_output);
   endfunction: connect
  
 endclass: AluAgent
 