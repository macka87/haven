                                                                                                                                    /* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_output_subscriber.sv
 * Description:  OVM subscriber for ALU Output Interface 
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         5.10.2012
 * ************************************************************************** */

/*!
 * \brief AluOutSubscriber
 * 
 * Functional Coverage for ALU Output Interface
 * 
 * This class measures exercised combinations of interface signals.
 */

 class AluOutputSubscriber extends ovm_subscriber #(AluOutputTransaction);
  
   //registration of component tools
   `ovm_component_utils(AluOutputSubscriber)

   // Sampled values of interface signals
   byte unsigned alu_output;
         
  /*
   * Definition of covergroups
   */
   covergroup AluOutCovergroup;
     alu_output_00_FF: coverpoint alu_output {
       bins zeros = {0};
       bins ones  = {8'hFF}; 
     } 
   endgroup
   
  /*! 
   * Constructor - creates Subscriber object  
   *
   * \param name     - instance name
   * \param parent   - parent class identification
   */
   function new(string name, ovm_component parent);
     super.new(name, parent);
     AluOutCovergroup = new();
   endfunction: new

  /*! 
   * Build - instanciates child components
   */ 
   function void build;
     super.build();
   endfunction: build
        
  /*
   * Display coverage statistics.  
   */
   task display();
     $write("Functional coverage ALU Output Subscriber: %d percent\n",
             AluOutCovergroup.get_inst_coverage());
   endtask : display

  /*
   * Write - obligatory function, samples values on the interface.  
   */
   function void write(AluOutputTransaction t);
     real coverage;
     
     alu_output  = t.ex_alu;
     
     AluOutCovergroup.sample();
     
     coverage = AluOutCovergroup.get_inst_coverage();
   endfunction: write
    
 endclass: AluOutputSubscriber
