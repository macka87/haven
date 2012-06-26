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
    
    //! Chromosome format
    ALUChromosome                  aluChromosome;
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
                  byte unsigned delay_rangesMin, 
                  byte unsigned delay_rangesMax, 
                  byte unsigned operandA_rangesMin, 
                  byte unsigned operandA_rangesMax,
                  byte unsigned operandB_rangesMin, 
                  byte unsigned operandB_rangesMax,
                  byte unsigned operandIMM_rangesMin, 
                  byte unsigned operandIMM_rangesMax,
                  byte unsigned operandMEM_rangesMin, 
                  byte unsigned operandMEM_rangesMax, 
                  byte unsigned delayMin, byte unsigned delayMax,
                  virtual iAluIn #(pDataWidth) aluIn  
                 ); 
      
      super.new(inst, framework, inputMbx);
      
      this.aluIn    = aluIn;
      
      //! Create generator
      //generator     = new("ALU Generator", genInput, genOutput, -1, transMbx);
            
      //! Create blueprint transaction
      aluChromosome  = new();
      
      aluChromosome.delay_rangesMin       = delay_rangesMin;
      aluChromosome.delay_rangesMax       = delay_rangesMax;
      aluChromosome.operandA_rangesMin    = operandA_rangesMin;
      aluChromosome.operandA_rangesMax    = operandA_rangesMax;
      aluChromosome.operandB_rangesMin    = operandB_rangesMin;
      aluChromosome.operandB_rangesMax    = operandB_rangesMax;
      aluChromosome.operandIMM_rangesMin  = operandIMM_rangesMin;
      aluChromosome.operandIMM_rangesMax  = operandIMM_rangesMax;
      aluChromosome.operandMEM_rangesMin  = operandMEM_rangesMin;
      aluChromosome.operandMEM_rangesMax  = operandMEM_rangesMax;
      aluChromosome.delayMin              = delayMin;
      aluChromosome.delayMax              = delayMax;
      
      //generator.blueprint = aluChromosome;
      
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
    task createOrLoadInitialPopulation(string filename, 
                                       bit load, 
                                       int populationSize,
                                       int maxMutations
                                       );
    
      //! ALU transaction format
      //ALUInTransaction #(pDataWidth) aluBlueprint;
    
      //! Create blueprint transaction
      //aluBlueprint  = new();
    
    
      // Create population
      population = new("Population", populationSize, maxMutations);
      population.create(aluChromosome);
    
      // Load population from file
      if (load) begin
        $write("Population loaded from file %s\n",filename);
        population.load(filename,aluChromosome);
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
  
  
 

  
