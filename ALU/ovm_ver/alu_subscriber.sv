/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_subscriber.sv
 * Description:  OVM subscriber ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         13.9.2012
 * ************************************************************************** */

/*!
 * \brief AluSubscriber
 * 
 * Functional Coverage for ALU Input Interface
 * 
 * This class measures exercised combinations of interface signals.
 */

  class AluSubscriber#(int pDataWidth = 8) extends ovm_subscriber#(AluTransaction);
  
   //registration of component tools
   `ovm_component_utils(my_subscriber)

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
    
  /*! 
   * Constructor - creates AluTest object  
   *
   * \param name     - instance name
   * \param parent   - parent class identification
   */
   function new(string name, ovm_component parent);
     super.new(name, parent);
     FunctionalCovergroup = new();
   endfunction: new

  /*! 
   * Build - instanciates child components
   */ 
   function void build;
     super.build();
   endfunction: build
        
  /*
   * Display coverage statistics.  
   */
   task display();
     $write("Functional coverage AluSunscriber: %d percent\n",
             FunctionalCovergroup.get_inst_coverage());
   endtask : display

  /*
   * Write - obligatory function; samples values on the interface.  
   */
   function void write(AluTransaction t);
     rst = t.rst;
     act = t.act;
     operation_s = t.operation_s;
     movi = t.movi;
     operandA = t.operandA;
     operandB = t.operandB;
     operandMEM = t.operandMEM;
     operandIMM = t.operandIMM;
     cover_bus.sample();
   endfunction: write
    
 endclass: AluSubscriber 