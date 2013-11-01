/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_in_coverage_monitor.sv
 * Description:  UVM subscriber for ALU Input Interface 
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         26.7.2013
 * ************************************************************************** */

/*!
 * \brief AluInCoverageMonitor
 * 
 * Functional Coverage for ALU Input Interface
 * This class measures exercised combinations of interface signals.
 */

 class AluInCoverageMonitor extends uvm_subscriber #(AluInputTransaction);
  
   //! UVM Factory Registration Macro
   `uvm_component_utils(AluInCoverageMonitor)

  /*!
   * Data Members
   */  
   
   // Enumeration for operation
   typedef enum logic [3:0] {ADD, SUB, MULT, SHIFT_RIGHT, SHIFT_LEFT, ROTATE_RIGHT, ROTATE_LEFT, NOT, AND, OR, XOR, NAND, NOR, XNOR, INC, DEC} t_operation;

   // Sampled transaction
   AluInputTransaction alu_in_trans;
   
   t_operation operation;
   int pkt_cnt;
  
   // max value 
   logic [DATA_WIDTH-1:0] max_value = pow (2, DATA_WIDTH) - 1; 
   
   // Configuration object for the coverage storage
   AluCoverageInfo cov_info;   
   
  /*
   * Definitions of covergroups
   */          
   
   covergroup alu_in_covergroup;
     
     // activity coverpoint
     actH : coverpoint alu_in_trans.act {
       bins act1          = {1};    
       ignore_bins act_ig = {0};
     } 
     
     // movi coverpoint
     moviH : coverpoint alu_in_trans.movi {
       bins movi_opB          = {0};        
       bins movi_opMEM        = {1};
       bins movi_opIMM        = {2};  
       illegal_bins movi_ill_op = {3};
     } 
     
     // operation coverpoint
     //operationH: coverpoint alu_in_trans.op;
     //operationH: coverpoint operation;
     operationH: coverpoint operation {
       bins o_add = {ADD};
       bins o_sub = {SUB};
       bins o_mult = {MULT};
       bins o_shift_right = {SHIFT_RIGHT};
       bins o_shift_left = {SHIFT_LEFT};
       bins o_rotate_right = {ROTATE_RIGHT};
       bins o_rotate_left = {ROTATE_LEFT};
       bins o_not = {NOT};
       bins o_and = {AND};
       bins o_or = {OR};
       bins o_xor = {XOR};
       bins o_nand = {NAND};
       bins o_nor = {NOR};
       bins o_xnor = {XNOR};
       bins o_inc = {INC};
       bins o_dec = {DEC};
     }
     
     // combinations of operations
     op_after_op: coverpoint operation {
       bins op_after_op[] = ([0:$] => [0:$]); 
     }
     
     // operand A coverpoint          
     opA: coverpoint alu_in_trans.reg_a {
       bins zeros        = {0};
       bins ones         = {max_value};
       bins small_values = {[1:15]};
       bins big_values   = {[(max_value-15):(max_value-1)]};
       bins other_values = default;
     }
     
     // operand B coverpoint
     opB: coverpoint alu_in_trans.reg_b {
       bins zeros        = {0};
       bins ones         = {max_value};
       bins small_values = {[1:15]};
       bins big_values   = {[(max_value-15):(max_value-1)]};
       bins other_values = default;
     }
     
     // operand IMM coverpoint
     opIMM: coverpoint alu_in_trans.imm {
       bins zeros        = {0};
       bins ones         = {max_value};
       bins small_values = {[1:15]};
       bins big_values   = {[(max_value-15):(max_value-1)]};
       bins other_values = default;
     }
     
     // operand MEM coverpoint
     opMEM: coverpoint alu_in_trans.mem {
       bins zeros        = {0};
       bins ones         = {max_value};
       bins small_values = {[1:15]};
       bins big_values   = {[(max_value-15):(max_value-1)]};
       bins other_values = default;
     }
     
     // all operations with ACT
     //op_act_cross : cross operationH, actH;
     
     // all movi variations with ACT
     //movi_act_cross : cross moviH, actH;
     
     // all operations x movi x ACT
     //op_movi_act_cross : cross operationH, moviH, actH;
     
     // all corner values x movi x act
     //opA_movi_act_cross : cross opA, moviH, actH;
     //opB_movi_act_cross : cross opB, moviH, actH;
     //opIMM_movi_act_cross : cross opIMM, moviH, actH;
     //opMEM_movi_act_cross : cross opMEM, moviH, actH; 
                                                        
     option.per_instance=1; // Also per instance statistics
     option.name = "alu_in_covergroup";
     option.cross_num_print_missing = 1000;
   
   endgroup 
   
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluInCoverageMonitor", uvm_component parent = null);
   extern function void write(AluInputTransaction t);
   
 endclass: AluInCoverageMonitor   
   
   
   
/*! 
 * Constructor - creates the AluInCoverageMonitor object  
 */
 function AluInCoverageMonitor::new(string name = "AluInCoverageMonitor", uvm_component parent = null);
   super.new(name, parent);
   alu_in_covergroup = new();
   pkt_cnt = 0;
 endfunction: new 
 


/*
 * Write - samples values on the interface.  
 */
 function void AluInCoverageMonitor::write(AluInputTransaction t);
   
   // get configuration object from database
   if (!uvm_config_db #(AluCoverageInfo)::get(this, "", "AluCoverageInfo", cov_info)) 
     `uvm_error("MYERR", "AluCoverageInfo doesn't exist!"); 
     
   alu_in_trans = t;
   
   $cast(operation, t.op);
   
   pkt_cnt++;
     
   // sample coverage
   alu_in_covergroup.sample();
     
   cov_info.alu_in_coverage = alu_in_covergroup.get_inst_coverage();
        
   // print statistics
   uvm_report_info("ALU INPUT COVERAGE", $psprintf("%0d Packets sampled, Coverage = %f%% ", pkt_cnt, cov_info.alu_in_coverage));
   
   // store new coverage info into the configuration object
   uvm_config_db #(AluCoverageInfo)::set(this, "*", "AluCoverageInfo", cov_info);
     
 endfunction: write