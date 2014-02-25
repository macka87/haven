/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    alu_driver.svh
 * Description:  Driver Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014
 * ************************************************************************** */

/*!
 * \brief AluDriver
 * 
 * This class drives the input interface of ALU and supplies transactions from 
 * sequencer to this interface.
 */

 class AluDriver;

  /*! 
   * Virtual interfaces for DUT
   */ 
   virtual iAluIn dut_alu_in_if;
  
  /*! 
   * Channels
   */ 
   mailbox #(AluInputTransaction) inputMbx; 
   mailbox #(AluInputTransaction) sbInMbx; 
   mailbox #(AluCoverageInfo) coverageMbx; 
   
  /*!
   * Data Members
   */ 
   AluCoverageInfo cov_info;
   
   // Enumeration for operation
   typedef enum logic [3:0] {ADD, SUB, MULT, SHIFT_RIGHT, SHIFT_LEFT, ROTATE_RIGHT, ROTATE_LEFT, NOT, AND, OR, XOR, NAND, NOR, XNOR, INC, DEC} t_operation;
   
   AluInputTransaction alu_in_trans;
   t_operation operation;
   
   // max value 
   logic [DATA_WIDTH-1:0] max_value = pow (2, DATA_WIDTH) - 1; 
   
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
     op_act_cross : cross operationH, actH;
     
     // all movi variations with ACT
     movi_act_cross : cross moviH, actH;
     
     // all operations x movi x ACT
     op_movi_act_cross : cross operationH, moviH, actH;
     
     // all corner values x movi x act
     opA_movi_act_cross : cross opA, moviH, actH;
     opB_movi_act_cross : cross opB, moviH, actH;
     opIMM_movi_act_cross : cross opIMM, moviH, actH;
     opMEM_movi_act_cross : cross opMEM, moviH, actH; 
                                                        
     option.per_instance=1; // Also per instance statistics
     option.name = "alu_in_covergroup";
     option.cross_num_print_missing = 1000;
   
   endgroup 
   
   
  /*!
   * Methods
   */
   
   // User-defined methods
   extern function new(virtual iAluIn dut_alu_in_if);
   extern task run();
   extern task waitForAluRdy();
 endclass: AluDriver



/*! 
 *  Constructor
 */
 function AluDriver::new(virtual iAluIn dut_alu_in_if);
   this.dut_alu_in_if = dut_alu_in_if;  //! Store pointer interface 
   alu_in_covergroup = new();
   cov_info = new();                    // coverage information
 endfunction: new 



/*! 
 * Run - starts driver processing.
 */  
 task AluDriver::run();
   int cnt = 0;
   
   //$write("\n\n########## DRIVER ##########\n\n");
   
   // synchronise with CLK 
   @(dut_alu_in_if.cb); 
   
   forever begin
     inputMbx.get(alu_in_trans);
     
     // wait for readiness of ALU to process data
     waitForAluRdy();
            
     alu_in_trans.rst = dut_alu_in_if.RST;
     
     // display the content of transaction 
     alu_in_trans.print("DRIVER: ALU_TRANSACTION");
       
     // set input signals of DUT
     // sends values from transaction on the virtual interface
     
     dut_alu_in_if.cb.ACT   <= 1;   
     dut_alu_in_if.cb.OP    <= alu_in_trans.op;
     dut_alu_in_if.cb.MOVI  <= alu_in_trans.movi;
     dut_alu_in_if.cb.REG_A <= alu_in_trans.reg_a;
     dut_alu_in_if.cb.REG_B <= alu_in_trans.reg_b;
     dut_alu_in_if.cb.MEM   <= alu_in_trans.mem;
     dut_alu_in_if.cb.IMM   <= alu_in_trans.imm;
     
     $cast(operation, alu_in_trans.op);
     alu_in_covergroup.sample();
     
     // print statistics
     $write("ALU INPUT COVERAGE: %0d Packets sampled, Coverage = %f%%\n", cnt, alu_in_covergroup.get_inst_coverage());
     
     // store coverage info 
     if ((cnt+1)%TRANS_COUNT == 0) begin
       cov_info.alu_in_coverage = alu_in_covergroup.get_inst_coverage();
       coverageMbx.put(cov_info);
     end
     
     // sends generated transaction to the scoreboard, subscriber etc.
     //if (alu_in_trans.act) aport_alu_in_if.write(alu_in_trans);
     sbInMbx.put(alu_in_trans);
              
     // synchronise with CLK 
     @(dut_alu_in_if.cb); 
     
     cnt++;
   end 
 endtask: run
 
 
 
/*!
 * Wait for ALU_RDY
 */
 task AluDriver::waitForAluRdy();
   while (!dut_alu_in_if.cb.ALU_RDY || dut_alu_in_if.RST) begin
     @(dut_alu_in_if.cb);
   end 
 endtask: waitForAluRdy
