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
   int        framework;  //! Verification Framework  
   tTransMbx  transMbx;   //! Transaction Mailbox
       
   /*
    * Public Class Methods
    */ 
   
   /*! 
    * Constructor 
    */    
    function new (int framework); 
      // Identify framework
      this.framework = framework; //???? bude treba tu tato informacia ????
      // Create mailbox
      this.transMbx  = new(0);
    endfunction: new 
    
   /*!
    * Wait for written number of clocks 
    */     
    virtual task waitFor(input int clocks);
    endtask : waitFor 
   
   /*!
    * Stop driver's activity
    */     
    virtual task stop();
    endtask : stop  
   
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