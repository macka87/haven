/* *****************************************************************************
 * Project Name: ALU Functional Verification 
 * File Name:    alu_ga_input_controller.sv
 * Description:  Input Controller of Genetic Algorithm
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         23.6.2012 
 * ************************************************************************** */
 
 class ALUGAInputController #(int pDataWidth = 8, int genTrans = 0) extends GenInputController;
       
   /*
    * Public Class Atributes
    */ 
    
    //! Chromosome format
    ALUChromosome                  aluBlueprint; 
    //! Population
    Population                     population;
    //! Software driver   
    ALUDriver #(pDataWidth)        swAluDriver;   
    //! Hardware sender                        
    ALUSender #(pDataWidth)        hwAluSender; 
    
    //! Input ALU interface
    virtual iAluIn #(pDataWidth) aluIn;  
    
   /*
    * Public Class Methods
    */ 
    
   /*! 
    * Constructor 
    */    
    function new (string inst, int framework, tTransMbx inputMbx,
                  byte unsigned delay_rangesMin, byte unsigned delay_rangesMax, 
                  byte unsigned operandA_rangesMin, byte unsigned operandA_rangesMax,
                  byte unsigned operandB_rangesMin, byte unsigned operandB_rangesMax,
                  byte unsigned operandIMM_rangesMin, byte unsigned operandIMM_rangesMax,
                  byte unsigned operandMEM_rangesMin, byte unsigned operandMEM_rangesMax, 
                  byte unsigned delayMin, byte unsigned delayMax,
                  virtual iAluIn #(pDataWidth) aluIn  
                 ); 
      
      super.new(inst, framework, inputMbx);
      
      this.aluIn    = aluIn;
      
      //! Create generator
      generator     = new("ALU Generator", genTrans, -1, transMbx);
      //lfsrGenerator  = new("LFSR Generator", genTrans, -1, transMbx);
      
      //! Create blueprint transaction
      aluBlueprint  = new();
      
      aluBlueprint.delay_rangesMin       = delay_rangesMin;
      aluBlueprint.delay_rangesMax       = delay_rangesMax;
      aluBlueprint.operandA_rangesMin    = operandA_rangesMin;
      aluBlueprint.operandA_rangesMax    = operandA_rangesMax;
      aluBlueprint.operandB_rangesMin    = operandB_rangesMin;
      aluBlueprint.operandB_rangesMax    = operandB_rangesMax;
      aluBlueprint.operandIMM_rangesMin  = operandIMM_rangesMin;
      aluBlueprint.operandIMM_rangesMax  = operandIMM_rangesMax;
      aluBlueprint.operandMEM_rangesMin  = operandMEM_rangesMin;
      aluBlueprint.operandMEM_rangesMax  = operandMEM_rangesMax;
      aluBlueprint.delayMin              = delayMin;
      aluBlueprint.delayMax              = delayMax;
      
      //lfsrGenerator.blueprint    = aluBlueprint;      
      //generator.blueprint        = aluBlueprint;
      
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
    * Create or load initial population.
    */
    task createOrLoadInitialPopulation(string filename, bit load, int populationSize, int maxMutations);
      // Create population
      population = new("Population", populationSize, maxMutations);
      population.create(aluBlueprint);
    
      // Load population from file
      if (load) begin
        $write("Population loaded from file %s\n",filename);
        population.load(filename,aluBlueprint);
      end
    endtask : createOrLoadInitialPopulation
    
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
   
 endclass : ALUGAInputController
  
  
 

  
