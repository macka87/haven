/* *****************************************************************************
 * Project Name: HAVEN - Genetic Algorithm
 * File Name:    alu_scoreboard.sv
 * Description:  UVM Scoreboard Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         25.7.2013
 * ************************************************************************** */

/*!
 * \brief AluScoreboard
 * 
 * This class receives transactions from Driver and performs transformation of 
 * these transactions into the form of expected responses according to the 
 * specification. Afterwards, it receives transactions from Monitor and
 * automatically compares these real responses with the expected ones. 
 */

 class AluScoreboard extends uvm_scoreboard;

   //! UVM Factory Registration Macro
   `uvm_component_utils(AluScoreboard)
   
  /*! 
   * Ports/Exports
   */ 
   
   uvm_analysis_export #(AluInputTransaction)  export_alu_in_if;
   uvm_analysis_export #(AluOutputTransaction) export_alu_out_if;
   
   uvm_tlm_analysis_fifo #(AluInputTransaction)  driver_fifo;
   uvm_tlm_analysis_fifo #(AluOutputTransaction) monitor_fifo;
   
  /*!
   * Data Members
   */  
   
   int m_matches, m_mismatches;
   
  /*!
   * Methods
   */
   
   // Standard UVM methods
   extern function new(string name = "AluScoreboard", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern function void connect_phase(uvm_phase phase); 
   extern task run_phase(uvm_phase phase); 
   extern function void report_phase(uvm_phase phase);
   
 endclass: AluScoreboard   
   
/*! 
 * Constructor - creates the AluScoreboard object  
 */
 function AluScoreboard::new(string name = "AluScoreboard", uvm_component parent = null);
   super.new(name, parent);
   m_matches    = 0;
   m_mismatches = 0;
 endfunction: new
 
 
    
/*! 
 * Build - instanciates child components
 */ 
 function void AluScoreboard::build_phase(uvm_phase phase);
   export_alu_in_if  = new("export_alu_in_if",this);
   export_alu_out_if = new("export_alu_out_if",this);
     
   driver_fifo  = new("driver_fifo",this);
   monitor_fifo = new("monitor_fifo",this);
 endfunction: build_phase   
   


/*! 
 * Connect - interconnection of AluScoreboard components.
 */  
 function void AluScoreboard::connect_phase(uvm_phase phase);
   export_alu_in_if.connect(driver_fifo.analysis_export);
   export_alu_out_if.connect(monitor_fifo.analysis_export);
 endfunction: connect_phase
 
 
  
/*! 
 * Run - starts scoreboard processing.
 */  
 task AluScoreboard::run_phase(uvm_phase phase); 
   string msg;
   AluInputTransaction      alu_in_tr;
   AluOutputTransaction     alu_out_tr_exp, alu_out_tr_exp_c;  // expected transaction 
   AluOutputTransaction     alu_out_tr_real;                   // real transaction
   logic [DATA_WIDTH-1:0]   operandB;
   logic [DATA_WIDTH*2-1:0] multResult;
     
   // create expected output transaction
   alu_out_tr_exp = AluOutputTransaction::type_id::create();
     
   forever begin
    
     // receive input transaction from Driver
     driver_fifo.get(alu_in_tr);
      
     // display received transaction
     //alu_in_tr.print("SCOREBOARD INPUT:");
       
     // selection of operand B
     priority case (alu_in_tr.movi)
       2'b00 : operandB = alu_in_tr.reg_b;  // register operand
       2'b01 : operandB = alu_in_tr.mem;    // memory operand
       2'b10 : operandB = alu_in_tr.imm;    // immediate operand
       default : begin
                   uvm_report_error("SCOREBOARD: Unknown operand identifier!!!", msg);
                   $stop;
                 end  
     endcase
       
     // >>>>> PREDICTOR >>>>>
       
     // clone expected output transaction
     assert($cast(alu_out_tr_exp_c, alu_out_tr_exp.clone));
       
     // operation execution
     priority case (alu_in_tr.op)
       // ADD 
       4'b0000 : alu_out_tr_exp_c.ex_alu = alu_in_tr.reg_a + operandB;
       // SUB
       4'b0001 : alu_out_tr_exp_c.ex_alu = alu_in_tr.reg_a - operandB;
       // MULT
       4'b0010 : begin
                   // first part
                   multResult = alu_in_tr.reg_a * operandB;
                   alu_out_tr_exp_c.ex_alu = multResult[DATA_WIDTH-1:0]; 
                   
                   // receive output trasanction from Monitor
                   monitor_fifo.get(alu_out_tr_real);
      
                   // display expected transaction
                   //alu_out_tr_exp_c.print("1:SCOREBOARD EXPECTED OUTPUT:");
      
                   // display received transaction
                   //alu_out_tr_real.print("1:SCOREBOARD REAL OUTPUT:");
       
                   // compare expected and real output transaction
                   if (!alu_out_tr_real.compare(alu_out_tr_exp_c)) begin
                     $sformat(msg, "Expected and real output transaction do not match!!!\n");
                     uvm_report_fatal("SCOREBOARD", msg);
                     m_mismatches++;
                   end 
                   else m_matches++;
                                        
                   // second part 
                   assert($cast(alu_out_tr_exp_c, alu_out_tr_exp.clone));
                   alu_out_tr_exp_c.ex_alu = multResult[DATA_WIDTH*2-1:DATA_WIDTH];
                 end  
       // SHIFT RIGHT
       4'b0011 : alu_out_tr_exp_c.ex_alu = operandB>>1;
       // SHIFT LEFT
       4'b0100 : alu_out_tr_exp_c.ex_alu = operandB<<1;
       // ROTATE RIGHT
       4'b0101 : begin
                   alu_out_tr_exp_c.ex_alu = operandB>>1;
                   alu_out_tr_exp_c.ex_alu[DATA_WIDTH-1] = operandB[0];
                 end  
       // ROTATE LEFT
       4'b0110 : begin
                   alu_out_tr_exp_c.ex_alu = operandB<<1;
                   alu_out_tr_exp_c.ex_alu[0] = operandB[DATA_WIDTH-1];
                 end  
       // NOT
       4'b0111 : alu_out_tr_exp_c.ex_alu = ~(operandB);
       // AND
       4'b1000 : alu_out_tr_exp_c.ex_alu = alu_in_tr.reg_a & operandB;
       // OR
       4'b1001 : alu_out_tr_exp_c.ex_alu = alu_in_tr.reg_a | operandB;
       // XOR
       4'b1010 : alu_out_tr_exp_c.ex_alu = alu_in_tr.reg_a ^ operandB;
       // NAND
       4'b1011 : alu_out_tr_exp_c.ex_alu = ~(alu_in_tr.reg_a & operandB);
       // NOR
       4'b1100 : alu_out_tr_exp_c.ex_alu = ~(alu_in_tr.reg_a | operandB);
       // XNOR
       4'b1101 : alu_out_tr_exp_c.ex_alu = alu_in_tr.reg_a ~^ operandB;
       // INC
       4'b1110 : alu_out_tr_exp_c.ex_alu = operandB + 1;
       // DEC
       4'b1111 : alu_out_tr_exp_c.ex_alu = operandB - 1;
       default : begin
                   $sformat(msg, "Unsupported operation!!!\n");
                   uvm_report_error("SCOREBOARD", msg);
                   $stop;
                 end
     endcase 
       
     // receive output trasanction from Monitor
     monitor_fifo.get(alu_out_tr_real);
       
     // display expected transaction
     //alu_out_tr_exp_c.print("SCOREBOARD EXPECTED OUTPUT:");
       
     // display received transaction
     //alu_out_tr_real.print("SCOREBOARD REAL OUTPUT:");
       
     // compare expected and real output transaction
     if (!alu_out_tr_real.compare(alu_out_tr_exp_c)) begin
       $sformat(msg, "Expected and real output transaction do not match!!!\n");
       uvm_report_error("SCOREBOARD", msg);
       m_mismatches++;
       //$stop;
     end 
     else m_matches++;
   end  // of forever
 endtask: run_phase 
 
 
 
/*! 
 * Post-body - implements closing of output file with transactions
 */ 
 function void AluScoreboard::report_phase(uvm_phase phase);
   $write("\n\n");
   $write("-------------------------------------------------------------------- \n");
   $write("------------------          SCOREBOARD         --------------------- \n");
   $write("-------------------------------------------------------------------- \n");
   
   if (m_mismatches == 0) begin
     $write("\n MATCHES: %d\n\n MISMATCHES: %d\n", m_matches, m_mismatches);
     //$write("\n VERIFICATION ENDED CORRECTLY :)\n\n");
   end
   
   else begin
     $write("\n MATCHES: %d\n\n MISMATCHES: %d\n", m_matches, m_mismatches);
     $write("\n SCOREBOARD MISMATCHES OCCURED IN VERIFICATION. \n\n");
   end
   
   $stop();
 endfunction: report_phase