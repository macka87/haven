/* *****************************************************************************
 * Project Name: ALU Functional Verification 
 * File Name:    Coverage Class
 * Description:  Measures coverage information during verification.
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         3.5.2012 
 * ************************************************************************** */

 import math_pkg::*;  

/*!
 * Functional Coverage for ALU Input Interface
 * 
 * This class measures exercised combinations of interface signals.
 */ 
 class CoverageIn #(int pDataWidth = 8);
  
   // Interface on which is coverage measured.
   virtual iAluIn #(pDataWidth) aluIn;
   string  inst;

   // Enabling of data sampling.
   bit enabled;
   
   // Enumeration for operation
   enum logic [3:0] {ADD, SUB, MULT, SHIFT_RIGHT, SHIFT_LEFT, ROTATE_RIGHT, ROTATE_LEFT, NOT, AND, OR, XOR, NAND, NOR, XNOR, INC, DEC} operation;

   // Sampled values of interface signals
   logic rst;
   logic act;
   logic [1:0] movi;
   logic [3:0] operation_s;
   byte unsigned operandA;
   byte unsigned operandB;
   byte unsigned operandIMM;
   byte unsigned operandMEM;
   
   // max value 
   logic [pDataWidth-1:0] max_value = pow (2, pDataWidth) - 1; 
         
  /*
   * Definition of covergroups
   */
   covergroup FunctionalCovergroup;
     resetB : coverpoint rst {
       bins rst0 = {0};        
       bins rst1 = {1};
     }
     
     actH : coverpoint act {
       bins act1          = {1};    
       ignore_bins act_ig = {0};
     } 
     
     moviH : coverpoint movi {
       bins movi_opB          = {0};        
       bins movi_opMEM        = {1};
       bins movi_opIMM        = {2};
       ignore_bins movi_ig_op = {3};
     } 
     
     operationH: coverpoint operation;
     
     // sequences of operations
     op_after_op: coverpoint operation {
       bins op_after_op[] = ([0:$] => [0:$]); 
     }
     
     opA: coverpoint operandA {
       bins zeros        = {0};
       bins ones         = {max_value};
       bins small_values = {[1:15]};
       bins big_values   = {[(max_value-15):(max_value-1)]};
       bins other_values = default;
     }
     
     opB: coverpoint operandB {
       bins zeros        = {0};
       bins ones         = {max_value};
       bins small_values = {[1:15]};
       bins big_values   = {[(max_value-15):(max_value-1)]};
       bins other_values = default;
     }
     
     opIMM: coverpoint operandIMM {
       bins zeros        = {0};
       bins ones         = {max_value};
       bins small_values = {[1:15]};
       bins big_values   = {[(max_value-15):(max_value-1)]};
       bins other_values = default;
     }
     
     opMEM: coverpoint operandMEM {
       bins zeros        = {0};
       bins ones         = {max_value};
       bins small_values = {[1:15]};
       bins big_values   = {[(max_value-15):(max_value-1)]};
       bins other_values = default;
     }
     
     // all operations with ACT
     op_act_cross : cross operationH, actH;
     
     // all movi variations with ACT
     movi_act_cross : cross moviH, actH;
     
     // all operations x movi x ACT
     op_movi_act_cross : cross operationH, moviH, actH;
     
     // all operations x movi x act => operations x movi x act
     trans_movi_act_cross : cross op_after_op, actH, moviH;
     
     // all corner values x movi x act
     opA_movi_act_cross : cross opA, moviH, actH;
     opB_movi_act_cross : cross opB, moviH, actH;
     opIMM_movi_act_cross : cross opIMM, moviH, actH;
     opMEM_movi_act_cross : cross opMEM, moviH, actH;
     
     // delayed act with operations
     
     // sequences of act
     delayed_act: coverpoint act {
       bins delayed1_act = (1 => 0 => 1);
       bins delayed2_act = (1 => 0 [* 2] => 1);
       bins delayed3_act = (1 => 0 [* 3] => 1);
       bins delayed4_act = (1 => 0 [* 4] => 1);
       bins delayed5_act = (1 => 0 [* 5] => 1);
     }
     
     // operation x delayed_act
     delayed_act_operation_cross : cross delayed_act, operationH;
     
     // reset at least two times
    /* reset_after_reset: coverpoint rst {
       bins reset_down = (1 => 0); 
       bins reset_up   = (0 => 1);
     } */
     
     option.per_instance=1;                   // Also per instance statistics
   endgroup
   
  /*
   * Constructor.
   */
   function new (virtual iAluIn #(pDataWidth) aluIn,
                 string inst);
     this.aluIn = aluIn;         // Store interface
     FunctionalCovergroup = new; // Create covergroup
     enabled = 0;                // Disable interface sampling
     this.inst = inst;
   endfunction

  /*
   * Enable functional coverage measures.
   */
   task setEnabled();
     enabled = 1;  // Coverage Enabling
     fork         
       run();      // Creating coverage subprocess
     join_none;    // Don't wait for ending
   endtask : setEnabled
  
  /*
   * Disable functional coverage measures.
   */        
   task setDisabled();
     enabled = 0;  // Disable measures
   endtask : setDisabled
  
  /*
   * Run functional coverage measures.  
   */ 
   task run();
     while (enabled) begin   // repeat while enabled
       
       while (aluIn.cover_cb.RST) begin
         rst = aluIn.cover_cb.RST;
         @(aluIn.cover_cb);  // Wait for clock
         FunctionalCovergroup.sample();
       end
       
       // Sample signals values
       rst         = aluIn.cover_cb.RST;
       act         = aluIn.cover_cb.ACT;
       movi        = aluIn.cover_cb.MOVI;
       operation_s = aluIn.cover_cb.OP;
       operandA    = aluIn.cover_cb.REG_A;
       operandB    = aluIn.cover_cb.REG_B;
       operandIMM  = aluIn.cover_cb.IMM;
       operandMEM  = aluIn.cover_cb.MEM;
       
       $cast(operation, operation_s);
       
       FunctionalCovergroup.sample();
       @(aluIn.cover_cb);   // Wait for clock
     end
   endtask : run
  
  /*
   * Display coverage statistics.  
   */
   task display();
     $write("Functional coverage for %s: %d percent\n",
             inst, FunctionalCovergroup.get_inst_coverage());
   endtask : display
 endclass: CoverageIn

/*!
 * Functional Coverage for Output ALU Interface
 * 
 * This class measures exercised combinations of interface signals.
 */ 
 class CoverageOut #(int pDataWidth = 8);
  
   // Interface on which is coverage measured.
   virtual iAluOut #(pDataWidth) aluOut;
   string  inst;

   // Enabling of data sampling.
   bit enabled;

   // Sampled values of interface signals
   byte unsigned alu_output;
   byte unsigned port_output;
       
  /*
   * Definition of covergroups
   */
   covergroup FunctionalCovergroup;
     alu_output_00_FF: coverpoint alu_output {
       bins zeros = {0};
       bins ones  = {8'hFF}; 
     } 
   endgroup

  /*
   * Constructor.
   */
   function new (virtual iAluOut #(pDataWidth) aluOut,
                 string inst);
     this.aluOut = aluOut;       // Store interface
     FunctionalCovergroup = new; // Create covergroup
     enabled = 0;                // Disable interface sampling
     this.inst = inst;
   endfunction

  /*
   * Enable functional coverage measures.
   */
   task setEnabled();
     enabled = 1;  // Coverage Enabling
     fork         
       run();      // Creating coverage subprocess
     join_none;    // Don't wait for ending
   endtask : setEnabled
  
  /*
   * Disable functional coverage measures.
   */        
   task setDisabled();
     enabled = 0;  // Disable measures
   endtask : setDisabled
  
  /*
   * Run functional coverage measures.  
   */ 
   task run();
     while (enabled) begin  // repeat while enabled
       @(aluOut.cb);        // Wait for clock
       // Sample signals values
       alu_output  = aluOut.cb.EX_ALU;
       FunctionalCovergroup.sample();
     end
   endtask : run
  
  /*
   * Display coverage statistics.  
   */
   task display();
     $write("Functional coverage for %s: %d percent\n",
             inst, FunctionalCovergroup.get_inst_coverage());
   endtask : display
 endclass: CoverageOut

/*! 
 * ALU Coverage
 * This class measures functional coverage.
 */    
 class ALUCoverage #(int pDataWidth = 8);
   string inst;
   
   CoverageIn  #(pDataWidth)  cmdListIn[$];   // Functional coverage list
   CoverageOut #(pDataWidth)  cmdListOut[$];  // Functional coverage list
  
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
     
   // Add input interface of ALU to functional coverage 
   task addInALUInterface (virtual iAluIn #(pDataWidth) aluIn,
                           string inst
                           );
     // Create functional coverage class
     CoverageIn #(pDataWidth) cmdCoverageIn = new(aluIn, inst);  
       
     // Insert class into list
     cmdListIn.push_back(cmdCoverageIn);
   endtask : addInALUInterface
    
   // Add output interface of ALU to functional coverage 
   task addOutALUInterface (virtual iAluOut #(pDataWidth) aluOut,
                           string inst
                           );
     // Create functional coverage class
     CoverageOut #(pDataWidth) cmdCoverageOut = new(aluOut, inst);  
      
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


