/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    Input Controller Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
 class InputController;
   
   /*
    * Public Class Atributes
    */ 
    string     inst;       //! Controller identification
    tTransMbx  transMbx;   //! Transaction Mailbox
    tTransMbx  inputMbx;   //! Input Transaction Mailbox
    int        framework;
    InputCbs   cbs[$];     //! Input callback list 
    
   /*
    * Public Class Methods
    */ 
   
   /*! 
    * Constructor 
    */    
    function new(string inst,
                 int framework,
                 tTransMbx inputMbx); 
      this.inst      = inst; 
      this.transMbx  = new(1);     // blocking mailbox
      this.inputMbx  = inputMbx;
      this.framework = framework;
    endfunction: new 
   
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
   
 endclass : InputController  
