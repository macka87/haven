/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    basic_input_controller.sv
 * Description:  OVM Basic Input Controller Class
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         16.8.2012
 * ************************************************************************** */

 `include "ovm_macros.svh"

 package BasicInputController_pkg;
  
   //include official ovm package
   import ovm_pkg::*;
 
  /*!
   * \brief BasicInputController
   * 
   * This class is parent class for any input controller.
   */
   class BasicInputController extends ovm_monitor;
     
     //registration of component tools
     `ovm_component_utils(BasicInputController)
  
    /*! 
     * Constructor - creates BasicInputController object  
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
     * Start controller's activity
     */     
     virtual task start();
     endtask : start
   
    /*!
     * Stop controller's activity
     */     
     virtual task stop();
     endtask : stop  
   
    /*!
     * Wait for written number of clocks 
     */     
     virtual task waitFor(input int clocks);
     endtask : waitFor  
   
    /*! 
     * Wait forever
     */     
     virtual task waitForever();
     endtask : waitForever    
   
    /*! 
     * Send transaction
     */      
     virtual task send(input Transaction trans);
     endtask : send 
   
   endclass : BasicInputController
 
 endpackage: BasicInputController_pkg