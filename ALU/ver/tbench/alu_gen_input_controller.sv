/* *****************************************************************************
 * Project Name: ALU Functional Verification 
 * File Name:    alu_gen_input_controller.sv
 * Description:  Input Controller of Generated ALU instructions
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         23.3.2012 
 * ************************************************************************** */
 
 class ALUGenInputController #(pDataWidth = 8) extends GenInputController;
   
   /*
    * Public Class Atributes
    */ 
    
    //! Transaction format
    ALUInTransaction #(pDataWidth) aluBlueprint; 
    //! Software driver   
    ALUDriver #(pDataWidth)        swAluDriver;   
    //! Hardware sender                        
    ALUSender #(pDataWidth)        hwAluSender; 
    
    //! Input ALU interface
    virtual iAluIn #(pDataWidth) aluIn;      //!! bolo predtym iAluIn.tb
    
   /*
    * Public Class Methods
    */ 
    
   /*! 
    * Constructor 
    */    
    function new (string inst, int framework, tTransMbx inputMbx,
                  byte btDelayEn_wt, byte btDelayDi_wt, 
                  byte btDelayLow, byte btDelayHigh,
                  virtual iAluIn #(pDataWidth) aluIn  //!! bolo predtym iAluIn.tb
                 ); 
      
      super.new(inst, framework, inputMbx);
      
      this.aluIn    = aluIn;
      
      //! Create generator
      generator     = new("ALU Generator", transMbx);
      
      //! Create blueprint transaction
      aluBlueprint  = new();
      
      aluBlueprint.btDelayEn_wt  = btDelayEn_wt;
      aluBlueprint.btDelayDi_wt  = btDelayDi_wt;
      aluBlueprint.btDelayLow    = btDelayLow;
      aluBlueprint.btDelayHigh   = btDelayHigh;
            
      generator.blueprint        = aluBlueprint;
      
      //! Create software driver
      swAluDriver   = new("Software ALU Driver", 0, transMbx, aluIn); 
           
      //! Create hardware sender
      hwAluSender   = new("Hardware ALU Sender", 0, transMbx, inputMbx); 
    endfunction: new  
    
   /*! 
    * Set Callback - callback object into List 
    */
    virtual function void setCallbacks(InputCbs cbs);
      if (framework == 0)      swAluDriver.setCallbacks(cbs); 
      else if (framework == 1) hwAluSender.setCallbacks(cbs); 
    endfunction : setCallbacks 
    
   /*!
    * Start controller's activity
    */
    task start();
      // software framework
      if (framework == 0) begin 
        swAluDriver.setEnabled();
      end  
      
      // hardware framework
      else if (framework == 1) 
        hwAluSender.sendStart();
    endtask : start
    
   /*!
    * Stop controller's activity
    */     
    task stop();
      int i=0; 
     
      // software framework
      if (framework == 0) begin
        swAluDriver.setDisabled();
      end
    
      // hardware framework
      else if (framework == 1) 
        hwAluSender.sendStop();
    endtask : stop   
   
   /*!
    * Wait for written number of clocks 
    */     
    task waitFor(input int clocks);
      // software framework  
      if (framework == 0) begin  
        swAluDriver.sendWait(clocks);
      end   
      
      // hardware framework
      else if (framework == 1) 
        hwAluSender.sendWait(clocks);
    endtask : waitFor
    
   /*! 
    * Wait forever
    */     
    task waitForever();
      // software framework
      if (framework == 0) 
        swAluDriver.setDisabled();     
      
      // hardware framework
      else if (framework == 1) 
        hwAluSender.sendWaitForever();
    endtask : waitForever    
   
   /*!
    * Send generated transaction 
    */
    task sendGenerated(int unsigned transCount);
      //! run generator
      generator.setEnabled(transCount);
      
      // software framework
      if (framework == 0)
        swAluDriver.sendTransactions(transCount);  
                    
      // hardware framework
      if (framework == 1) 
        hwAluSender.sendTransactions(transCount); 
    endtask : sendGenerated 
    
 endclass : ALUGenInputController
  
  
 

  