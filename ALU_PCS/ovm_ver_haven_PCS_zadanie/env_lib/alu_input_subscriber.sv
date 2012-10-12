/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_input_subscriber.sv
 * Description:  OVM subscriber for ALU Input Interface 
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         5.10.2012
 * ************************************************************************** */

/*!
 * \brief AluInSubscriber
 * 
 * Functional Coverage for ALU Input Interface
 * 
 * This class measures exercised combinations of interface signals.
 */

 class AluInputSubscriber extends ovm_subscriber #(AluInputTransaction);
  
   //registration of component tools
   `ovm_component_utils(AluInputSubscriber)

   // Enumeration for operation
   
   // *** Doplnte nasledujici ENUM ***
   
   typedef enum logic [3:0] {ADD, SUB, MULT, SHIFT_RIGHT, SHIFT_LEFT, ROTATE_RIGHT, ROTATE_LEFT, NOT, AND, OR, XOR, NAND, NOR, XNOR} t_operation;

   // Sampled values of interface signals
   logic rst;
   logic act;
   logic [1:0] movi;
   t_operation operation;
   byte unsigned operandA;
   byte unsigned operandB;
   byte unsigned operandIMM;
   byte unsigned operandMEM;
   
   // max value 
   logic [DATA_WIDTH-1:0] max_value = pow (2, DATA_WIDTH) - 1; 
         
  /*
   * Definition of covergroups
   */
   covergroup AluInCovergroup;
     
     // activity coverpoint
     actH : coverpoint act {
       bins act1          = {1};    
       ignore_bins act_ig = {0};
     } 
     
     // movi coverpoint
     moviH : coverpoint movi {
       bins movi_opB          = {0};        
       bins movi_opMEM        = {1};
       bins movi_opIMM        = {2};  
       illegal_bins movi_ill_op = {3};
     } 
     
     // operation coverpoint
     operationH: coverpoint operation;
     
     // *** Zde doplnte bod pokryti: op_after_op ***
          
     // operand A coverpoint          
     opA: coverpoint operandA {
       bins zeros        = {0};
       bins ones         = {max_value};
       bins small_values = {[1:15]};
       bins big_values   = {[(max_value-15):(max_value-1)]};
       bins other_values = default;
     }
     
     // operand B coverpoint
     opB: coverpoint operandB {
       bins zeros        = {0};
       bins ones         = {max_value};
       bins small_values = {[1:15]};
       bins big_values   = {[(max_value-15):(max_value-1)]};
       bins other_values = default;
     }
     
     // operand IMM coverpoint
     opIMM: coverpoint operandIMM {
       bins zeros        = {0};
       bins ones         = {max_value};
       bins small_values = {[1:15]};
       bins big_values   = {[(max_value-15):(max_value-1)]};
       bins other_values = default;
     }
     
     // operand MEM coverpoint
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
     
     // all corner values x movi x act
     opA_movi_act_cross : cross opA, moviH, actH;
     opB_movi_act_cross : cross opB, moviH, actH;
     opIMM_movi_act_cross : cross opIMM, moviH, actH;
     opMEM_movi_act_cross : cross opMEM, moviH, actH;
     
     option.per_instance=1; // Also per instance statistics
   endgroup
    
  /*! 
   * Constructor - creates Subscriber object  
   *
   * \param name     - instance name
   * \param parent   - parent class identification
   */
   function new(string name, ovm_component parent);
     super.new(name, parent);
     AluInCovergroup = new();
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
     $write("Functional coverage ALU Input Subscriber: %d percent\n",
             AluInCovergroup.get_inst_coverage());
   endtask : display

  /*
   * Write - obligatory function, samples values on the interface.  
   */
   function void write(AluInputTransaction t);
     real coverage;
     
     rst         = t.rst;
     act         = t.act;
     $cast(operation, t.op);
     movi        = t.movi;
     operandA    = t.reg_a;
     operandB    = t.reg_b;
     operandMEM  = t.mem;
     operandIMM  = t.imm;
     
     AluInCovergroup.sample();
     
     coverage = AluInCovergroup.get_inst_coverage();
   endfunction: write
    
 endclass: AluInputSubscriber
