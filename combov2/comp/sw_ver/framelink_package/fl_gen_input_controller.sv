/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    fl_gen_input_controller
 * Description:  Input Controller of Generated FrameLink Class
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
 class FrameLinkGenInputController #(int pDataWidth=32, int pDremWidth=2)
       extends GenInputController;
   
   /*
    * Public Class Atributes
    */ 
    
    //! Transaction format
    FrameLinkTransaction                       flBlueprint; 
    //! Software driver   
    FrameLinkDriver #(pDataWidth, pDremWidth)  swFlDriver;   
    //! Hardware sender                        
    FrameLinkSender #(pDataWidth)              hwFlSender; 
    
    //! FrameLink interface
    virtual iFrameLinkRx #(pDataWidth,pDremWidth) fl;
    
   /*
    * Public Class Methods
    */ 
    
   /*! 
    * Constructor 
    * 
    * \param frameParts  - count of FrameLink frame parts
    * \param partSizeMax - maximal size of FrameLink frame part        
    * \param partSizeMin - minimal size of FrameLink frame part    
    */    
    function new (string inst, int framework, tTransMbx inputMbx,
                  int frameParts, int partSizeMax[], int partSizeMin[],
                  byte btDelayEn_wt, byte btDelayDi_wt, 
                  byte btDelayLow, byte btDelayHigh,
                  byte itDelayEn_wt, byte itDelayDi_wt, 
                  byte itDelayLow, byte itDelayHigh,
                  virtual iFrameLinkRx #(pDataWidth,pDremWidth) fl
                 ); 
      
      super.new(inst, framework, inputMbx);
      
      this.fl       = fl;
      
      //! Create generator
      generator     = new("FrameLink Generator", 2, -1, transMbx);
      
      //! Create blueprint transaction
      flBlueprint   = new();
      
      flBlueprint.dataWidth     = pDataWidth/8;
      
      flBlueprint.frameParts    = frameParts;
      flBlueprint.partSizeMax   = partSizeMax;
      flBlueprint.partSizeMin   = partSizeMin;
      
      flBlueprint.btDelayEn_wt  = btDelayEn_wt;
      flBlueprint.btDelayDi_wt  = btDelayDi_wt;
      flBlueprint.btDelayLow    = btDelayLow;
      flBlueprint.btDelayHigh   = btDelayHigh;
            
      flBlueprint.itDelayEn_wt  = itDelayEn_wt;
      flBlueprint.itDelayDi_wt  = itDelayDi_wt;
      flBlueprint.itDelayLow    = itDelayLow;
      flBlueprint.itDelayHigh   = itDelayHigh;
            
      generator.blueprint       = flBlueprint;
      
      //! Create software driver
      swFlDriver   = new("Software FrameLink Driver", 0, transMbx, fl); 
           
      //! Create hardware sender
      hwFlSender   = new("Hardware FrameLink Sender", 0, transMbx, inputMbx); 
    endfunction: new  
    
   /*! 
    * Set Callback - callback object into List 
    */
    virtual function void setCallbacks(InputCbs cbs);
      if (framework == 0)      swFlDriver.setCallbacks(cbs); 
      else if (framework == 1) hwFlSender.setCallbacks(cbs); 
    endfunction : setCallbacks 
    
   /*!
    * Start controller's activity
    */
    task start();
      // software framework
      if (framework == 0) begin 
        swFlDriver.setEnabled();
      end  
      
      // hardware framework
      else if (framework == 1) 
        hwFlSender.sendStart();
    endtask : start
    
   /*!
    * Stop controller's activity
    */     
    task stop();
      int i=0; 
     
      // software framework
      if (framework == 0) begin
        swFlDriver.setDisabled();
      end
    
      // hardware framework
      else if (framework == 1) 
        hwFlSender.sendStop();
    endtask : stop   
   
   /*!
    * Wait for written number of clocks 
    */     
    task waitFor(input int clocks);
      // software framework  
      if (framework == 0) begin  
        swFlDriver.sendWait(clocks);
      end   
      
      // hardware framework
      else if (framework == 1) 
        hwFlSender.sendWait(clocks);
    endtask : waitFor
    
   /*! 
    * Wait forever
    */     
    task waitForever();
      // software framework
      if (framework == 0) 
        swFlDriver.setDisabled();     
      
      // hardware framework
      else if (framework == 1) 
        hwFlSender.sendWaitForever();
    endtask : waitForever    
   
   /*!
    * Send generated transaction 
    */
    task sendGenerated(int unsigned transCount);
      //! run generator
      generator.setEnabled(transCount);
      
      // software framework
      if (framework == 0) 
        swFlDriver.sendTransactions(transCount);  
              
      // hardware framework
      if (framework == 1) 
        hwFlSender.sendTransactions(transCount); 
    endtask : sendGenerated 
    
 endclass : FrameLinkGenInputController
  
  
 

  