/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    basic_output_controller.sv
 * Description:  OVM Basic Output Controller Class
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         16.8.2012
 * ************************************************************************** */

 `include "ovm_macros.svh"

 package BasicOutputController_pkg;
  
   //include official ovm package
   import ovm_pkg::*;
 
  /*!
   * \brief BasicOutputController
   * 
   * This class is parent class for any output controller.
   */ 
   class BasicOutputController extends ovm_component;
     
     //registration of component tools
     `ovm_component_utils(BasicOutputController)
  
    /*! 
     * Constructor - creates BasicOutputController object  
     *
     * \param name     - instance name
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
     endfunction: build
   
    /*! 
     * Run - runs output controller processes
     */      
     virtual task run();
       assert (0) 
         $fatal("Output Controller: Task run must be implemented in derived class"); 
     endtask : run 
   
   endclass : BasicOutputController
 
 endpackage: BasicOutputController_pkg