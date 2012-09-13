/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    basic_driver.sv
 * Description:  OVM Basic Driver Class
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         14.8.2012
 * ************************************************************************** */

 `include "ovm_macros.svh"

 package BasicDriver_pkg;
  
   //include official ovm package
   import ovm_pkg::*;
 
  /*!
   * \brief BasicDriver
   * 
   * This class is parent class for any driver.
   */
   //class BasicDriver extends ovm_driver #(BasicTransaction);
   class BasicDriver#(type TypeOfTransaction=ovm_sequence_item) extends ovm_driver
                                                           #(TypeOfTransaction);

     //registration of component tools
     `ovm_component_utils(BasicDriver)

     //analysis port, sends data to scoreboards, subscribers, etc
     ovm_analysis_port #(TypeOfTransaction) aport;

    /*! 
     * Constructor - creates BasicDriver object  
     *
     * \param name     - driver instance name
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
       aport = new("aport", this);
     endfunction: build

    /*! 
     * Run - runs driver processes
     */   
     virtual task run;
        assert (0) 
          $fatal("Driver: Task run must be implemented in derived class"); 
     endtask: run

   endclass: BasicDriver

 endpackage: BasicDriver_pkg