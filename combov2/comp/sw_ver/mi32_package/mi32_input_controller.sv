/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    MI32 Input Controller Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         5.5.2011 
 * ************************************************************************** */
 
 class MI32InputController extends InputController;
   
   /*
    * Public Class Atributes
    */ 
    //! Software driver   
    MI32Driver       swMI32Driver;   
    //! Hardware sender                        
    //MI32Sender       hwMI32Sender; 
    
    //! FrameLink interface
    virtual iMi32.tb mi;
    
   /*
    * Public Class Methods
    */ 
   
   /*! 
    * Constructor 
    */    
    function new (string inst, int framework, tTransMbx inputMbx,
                  virtual iMi32.tb mi
                 ); 
      
      super.new(inst, framework, inputMbx);
      
      this.mi       = mi;
      
      //! Create software driver
      swMI32Driver  = new("Software MI32 Driver", 0, transMbx, mi); 
           
      //! Create hardware sender
      //hwMI32Sender  = new("Hardware MI32 Sender", 0, transMbx, inputMbx); 
    endfunction: new
    
   /*! 
    * Set Callback - callback object into List 
    */
    virtual function void setCallbacks(InputCbs cbs);
      if (framework == 0)      swMI32Driver.setCallbacks(cbs); 
      //else if (framework == 1) hwMI32Sender.setCallbacks(cbs); 
    endfunction : setCallbacks 
   
   /*!
    * Start controller's activity
    */
    task start();
      // software framework
      if (framework == 0) begin 
        swMI32Driver.setEnabled();
      end  
      
      // hardware framework
      //else if (framework == 1) 
      //  hwMI32Sender.sendStart();
    endtask : start
   
   /*!
    * Stop controller's activity
    */     
    task stop();
      int i=0; 
     
      // software framework
      if (framework == 0) begin
        swMI32Driver.setDisabled();
      end
    
      // hardware framework
      //else if (framework == 1) 
      //  hwMI32Sender.sendStop();
    endtask : stop
   
   /*!
    * Wait for written number of clocks 
    */     
    task waitFor(input int clocks);
      // software framework  
      if (framework == 0) begin  
        swMI32Driver.sendWait(clocks);
      end   
      
      // hardware framework
      //else if (framework == 1) 
      //  hwMI32Sender.sendWait(clocks);
    endtask : waitFor 
   
   /*! 
    * Wait forever
    */     
    task waitForever();
      // software framework
      if (framework == 0) 
        swMI32Driver.setDisabled();     
      
      // hardware framework
      //else if (framework == 1) 
      //  hwMI32Sender.sendWaitForever();
    endtask : waitForever    
   
   /*!
    * Send created transaction 
    */
    task sendTransaction(MI32Transaction trans);
      // software framework
      if (framework == 0) 
        swMI32Driver.sendTransaction(trans);  
              
      // hardware framework
      //if (framework == 1) 
      //  hwMI32Sender.sendTransaction(trans); 
    endtask : sendTransaction 
   
 endclass : MI32InputController  
