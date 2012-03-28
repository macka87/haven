/* *****************************************************************************
 * Project Name: ALU Functional Verification 
 * File Name:    Coverage Class
 * Description:  Measures coverage information during verification.
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         22.3.2012 
 * ************************************************************************** */

/*!
 * Command Coverage for ALU Input Interface
 * 
 * This class measures exercised combinations of interface signals.
 */ 
 class CoverageIn;
  
   // Interface on which is coverage measured.
   virtual iAluIn.cover_tb aluIn;
   string  inst;

   // Enabling of data sampling.
   bit enabled;

   // Sampled values of interface signals
   logic [1:0] movi;
   logic [1:0] operation;
   byte unsigned operandA;
   byte unsigned operandB;
   byte unsigned operandIMM;
   byte unsigned operandMEM;
       
  /*
   * Definition of covergroups
   */
   covergroup CommandsCovergroup;
     coverpoint movi;
     coverpoint operation;
     
     operandA_00_FF: coverpoint operandA {
       bins zeros = {0};
       bins ones  = {8'hFF}; 
     } 
     
     operandB_00_FF: coverpoint operandB {
       bins zeros = {0};
       bins ones  = {8'hFF}; 
     }
     
     operandIMM_00_FF: coverpoint operandIMM {
       bins zeros = {0};
       bins ones  = {8'hFF}; 
     }
     
     operandMEM_00_FF: coverpoint operandMEM {
       bins zeros = {0};
       bins ones  = {8'hFF}; 
     }
   endgroup

  /*
   * Constructor.
   */
   function new (virtual iAluIn.cover_tb aluIn,
                 string inst);
     this.aluIn = aluIn;         // Store interface
     CommandsCovergroup = new;   // Create covergroup
     enabled = 0;                // Disable interface sampling
     this.inst = inst;
   endfunction

  /*
   * Enable command coverage measures.
   */
   task setEnabled();
     enabled = 1;  // Coverage Enabling
     fork         
       run();      // Creating coverage subprocess
     join_none;    // Don't wait for ending
   endtask : setEnabled
  
  /*
   * Disable command coverage measures.
   */        
   task setDisabled();
     enabled = 0;  // Disable measures
   endtask : setDisabled
  
  /*
   * Run command coverage measures.  
   */ 
   task run();
     while (enabled) begin  // repeat while enabled
       @(aluIn.cover_cb);   // Wait for clock
       // Sample signals values
       movi       = aluIn.cover_cb.MOVI;
       operation  = aluIn.cover_cb.OP;
       operandA   = aluIn.cover_cb.REG_A;
       operandB   = aluIn.cover_cb.REG_B;
       operandIMM = aluIn.cover_cb.IMM;
       operandMEM = aluIn.cover_cb.MEM;
       CommandsCovergroup.sample();
     end
   endtask : run
  
  /*
   * Display coverage statistics.  
   */
   task display();
     $write("Commands coverage for %s: %d percent\n",
             inst, CommandsCovergroup.get_inst_coverage());
   endtask : display
 endclass: CoverageIn

/*!
 * Command Coverage for Output ALU Interface
 * 
 * This class measures exercised combinations of interface signals.
 */ 
 class CoverageOut;
  
   // Interface on which is coverage measured.
   virtual iAluOut.aluout_tb aluOut;
   string  inst;

   // Enabling of data sampling.
   bit enabled;

   // Sampled values of interface signals
   byte unsigned alu_output;
   byte unsigned port_output;
       
  /*
   * Definition of covergroups
   */
   covergroup CommandsCovergroup;
     alu_output_00_FF: coverpoint alu_output {
       bins zeros = {0};
       bins ones  = {8'hFF}; 
     } 
     
     port_output_00_FF: coverpoint port_output {
       bins zeros = {0};
       bins ones  = {8'hFF}; 
     }
   endgroup

  /*
   * Constructor.
   */
   function new (virtual iAluOut.aluout_tb aluOut,
                 string inst);
     this.aluOut = aluOut;       // Store interface
     CommandsCovergroup = new;   // Create covergroup
     enabled = 0;                // Disable interface sampling
     this.inst = inst;
   endfunction

  /*
   * Enable command coverage measures.
   */
   task setEnabled();
     enabled = 1;  // Coverage Enabling
     fork         
       run();      // Creating coverage subprocess
     join_none;    // Don't wait for ending
   endtask : setEnabled
  
  /*
   * Disable command coverage measures.
   */        
   task setDisabled();
     enabled = 0;  // Disable measures
   endtask : setDisabled
  
  /*
   * Run command coverage measures.  
   */ 
   task run();
     while (enabled) begin  // repeat while enabled
       @(aluOut.cb);        // Wait for clock
       // Sample signals values
       alu_output  = aluOut.cb.EX_ALU;
       CommandsCovergroup.sample();
     end
   endtask : run
  
  /*
   * Display coverage statistics.  
   */
   task display();
     $write("Commands coverage for %s: %d percent\n",
             inst, CommandsCovergroup.get_inst_coverage());
   endtask : display
 endclass: CoverageOut

/*! 
 * ALU Coverage
 * This class measures coverage of commands.
 */    
 class ALUCoverage;
   string inst;
   
   CoverageIn    cmdListIn[$];   // Commands coverage list
   CoverageOut   cmdListOut[$];  // Commands coverage list
  
  /*! 
    * Constructor
    * 
    * \param inst - coverage identification
    */
    function new (string inst);
      this.inst       = inst;
    endfunction
        
  /*
   * Add interfaces to coverage measurement.
   */
     
   // Add input interface of ALU to command coverage 
   task addInALUInterface (virtual iAluIn.cover_tb aluIn,
                           string inst
                           );
     // Create commands coverage class
     CoverageIn cmdCoverageIn = new(aluIn, inst);  
       
     // Insert class into list
     cmdListIn.push_back(cmdCoverageIn);
   endtask : addInALUInterface
    
   // Add output interface of ALU to command coverage 
   task addOutALUInterface (virtual iAluOut.aluout_tb aluOut,
                           string inst
                           );
     // Create commands coverage class
     CoverageOut cmdCoverageOut = new(aluOut, inst);  
      
     // Insert class into list
     cmdListOut.push_back(cmdCoverageOut);
   endtask : addOutALUInterface

  /*
   * Enable coverage measures.
   */ 
   task setEnabled();
     foreach (cmdListIn[i])   cmdListIn[i].setEnabled();   
     foreach (cmdListOut[i])  cmdListOut[i].setEnabled();
   endtask : setEnabled
         
  /*
   * Disable coverage measures.
   */
   task setDisabled();
     foreach (cmdListIn[i])   cmdListIn[i].setDisabled();   
     foreach (cmdListOut[i])  cmdListOut[i].setDisabled();    
   endtask : setDisabled

  /*
   * Display coverage statistic
   */
   virtual task display();
     $write("------------------------------------------------------------\n");
     $write("-- COVERAGE STATISTICS:\n");
     $write("------------------------------------------------------------\n");
     foreach (cmdListIn[i])  cmdListIn[i].display();
     foreach (cmdListOut[i]) cmdListOut[i].display();
     $write("------------------------------------------------------------\n");
   endtask
 endclass : ALUCoverage


