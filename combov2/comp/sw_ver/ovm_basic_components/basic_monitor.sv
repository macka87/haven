/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    basic_monitor.sv
 * Description:  OVM Basic Monitor Class
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         16.8.2012
 * ************************************************************************** */

 `include "ovm_macros.svh"

 package BasicMonitor_pkg;
  
   //include official ovm package
   import ovm_pkg::*;
 
  /*!
   * \brief BasicMonitor
   * 
   * This class is parent class for any monitor.
   */
 
   class BasicMonitor #(type TypeOfTransaction=ovm_sequence_item) extends ovm_monitor;

     //registration of component tools
     `ovm_component_utils(BasicMonitor)

     //analysis port, sends data to scoreboards, subscribers, etc
     ovm_analysis_port #(TypeOfTransaction) aport;

    /*! 
     * Constructor - creates BasicMonitor object  
     *
     * \param name     - monitor instance name
     * \param parent   - parent class identification
     */  
     function new (string name, ovm_component parent);
       super.new(name, parent);
     endfunction: new

    /*! 
     * Build - instanciates child components
     */ 
     function void build;
       super.build();
       aport = new("aport", this);
     endfunction: build

    /*! 
     * Run - runs monitor processes
     */     
     virtual task run;
       assert (0) 
         $fatal("Monitor: Task run must be implemented in derived class"); 
     endtask: run
      
   endclass: BasicMonitor
 
 endpackage: BasicMonitor_pkg 