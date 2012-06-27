/* *****************************************************************************
 * Project Name: ALU Functional Verification 
 * File Name:    alu_ga_input_controller.sv
 * Description:  Input Controller of Genetic Algorithm
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         23.6.2012 
 * ************************************************************************** */
 
 class ALUGAInputController #(int pDataWidth = 8, 
                              int genInput = 0,
                              int genOutput = 0
                              ) extends GenInputController;
       
   /*
    * Public Class Atributes
    */ 
    
    //! Transaction format
    ALUInGATransaction #(pDataWidth) aluBlueprint;
    //! Software driver   
    ALUDriver #(pDataWidth)          swAluDriver;   
    //! Hardware sender                        
    ALUSender #(pDataWidth)          hwAluSender; 
    
    //! Input ALU interface
    virtual iAluIn #(pDataWidth)     aluIn;  
    
   /*
    * Public Class Methods
    */ 
    
   /*! 
    * Constructor 
    */    
    function new (string inst, int framework, tTransMbx inputMbx,
                  virtual iAluIn #(pDataWidth) aluIn  
                 ); 
      
      super.new(inst, framework, inputMbx);
      
      this.aluIn    = aluIn;
      
      //! Create generator
      generator     = new("ALU Generator", genInput, genOutput, -1, transMbx);
            
      //! Create software driver
      swAluDriver   = new("Software ALU Driver", 0, transMbx, aluIn); 
           
      //! Create hardware sender
      hwAluSender   = new("Hardware ALU Sender", 0, transMbx, inputMbx); 
    endfunction: new  
   
   /*!
    * Set ALU transaction parameters
    */
    task setParameters(ALUChromosome chr);
      int offset = 0;
    
      aluBlueprint  = new();
        
      // ALU Blueprint transaction parameters from chromosome
      aluBlueprint.movi_values = 3;
      aluBlueprint.movi_wt = new[3];
      for (int j=0; j<3; j++) 
        aluBlueprint.movi_wt[j] = chr.chromosome[offset++];
         
      aluBlueprint.operandA_ranges = chr.operandA_ranges;
      aluBlueprint.opA_range_wt = new[aluBlueprint.operandA_ranges];
      for (int j=0; j<aluBlueprint.operandA_ranges; j++) 
        aluBlueprint.opA_range_wt[j] = chr.chromosome[offset++];  
        
      aluBlueprint.operandB_ranges = chr.operandB_ranges;
      aluBlueprint.opB_range_wt = new[aluBlueprint.operandB_ranges];
      for (int j=0; j<aluBlueprint.operandB_ranges; j++) 
        aluBlueprint.opB_range_wt[j] = chr.chromosome[offset++];
      
      aluBlueprint.operandMEM_ranges = chr.operandMEM_ranges;
      aluBlueprint.opMEM_range_wt = new[aluBlueprint.operandMEM_ranges];
      for (int j=0; j<aluBlueprint.operandMEM_ranges; j++) 
        aluBlueprint.opMEM_range_wt[j] = chr.chromosome[offset++];
          
      aluBlueprint.operandIMM_ranges = chr.operandIMM_ranges;
      aluBlueprint.opIMM_range_wt = new[aluBlueprint.operandIMM_ranges];
      for (int j=0; j<aluBlueprint.operandIMM_ranges; j++) 
        aluBlueprint.opIMM_range_wt[j] = chr.chromosome[offset++];
            
      aluBlueprint.operation_values = 16;
      aluBlueprint.op_range_wt = new[16];
      for (int j=0; j<16; j++) 
        aluBlueprint.op_range_wt[j] = chr.chromosome[offset++];  
            
      aluBlueprint.delay_ranges = chr.delay_ranges;
      aluBlueprint.delay_range_wt = new[aluBlueprint.delay_ranges];
      for (int j=0; j<aluBlueprint.delay_ranges; j++) 
        aluBlueprint.delay_range_wt[j] = chr.chromosome[offset++];
      
      // blueprint transaction for generator
      generator.blueprint = aluBlueprint;
    endtask : setParameters
   
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
    * Send generated transaction 
    */
    task sendGenerated(int unsigned transCount);
      //! run generator
      generator.setEnabled(transCount);
      
      if (genOutput != 1) begin 
        // software framework
        if (framework == 0)
          swAluDriver.sendTransactions(transCount);  
                    
        // hardware framework
        if (framework == 1) 
          hwAluSender.sendTransactions(transCount);
      end    
    endtask : sendGenerated     
   
 endclass : ALUGAInputController
  
  
 

  
