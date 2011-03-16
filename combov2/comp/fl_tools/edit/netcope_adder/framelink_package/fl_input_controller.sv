/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    FrameLink Input Controller Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
 class FrameLinkInputController extends InputController;
   
   /*
    * Public Class Atributes
    */ 
    
   /*
    * Public Class Methods
    */ 
    
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
   
 endclass : FrameLinkInputController  