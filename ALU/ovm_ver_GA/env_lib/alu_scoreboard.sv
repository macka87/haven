/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_scoreboard.sv
 * Description:  OVM Scoreboard Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         2.10.2012
 * ************************************************************************** */

/*!
 * \brief AluScoreboard
 * 
 * This class receives transactions from Driver and performs transformation of 
 * these transactions into the form of expected responses according to the 
 * specification. Afterwards, it receives transactions from Monitor and
 * automatically compares these real responses with the expected ones. 
 */

 class AluScoreboard extends ovm_scoreboard;

   // registration of component tools
   `ovm_component_utils(AluScoreboard)
   
   // definition of two analysis ports for Driver and Monitor
   ovm_analysis_export #(AluInputTransaction)  export_alu_in_if;
   ovm_analysis_export #(AluOutputTransaction) export_alu_out_if;
   
   // queues for Driver and Monitor transactions
   local tlm_analysis_fifo #(AluInputTransaction)  driver_fifo;
   local tlm_analysis_fifo #(AluOutputTransaction) monitor_fifo;
   
  /*! 
   * Constructor - creates AluScoreboard object  
   *
   * \param name     - scoreboard instance name
   * \param parent   - parent class identification
   */
   function new(string name, ovm_component parent);
     super.new(name, parent);
   endfunction: new
   
  /*! 
   * Build - instanciates child components
   */
   function void build();
     export_alu_in_if  = new("Input IFC Analysis Export",this);
     export_alu_out_if = new("Output IFC Analysis Export",this);
     
     driver_fifo  = new("FIFO for Driver's Transactions",this);
     monitor_fifo = new("FIFO for Monitor's Transactions",this);
   endfunction: build
  
  /*! 
   * Connect - connection between Transaction FIFOs and analysis ports in
   * Scoreboard
   */
   function void connect();
     export_alu_in_if.connect(driver_fifo.analysis_export);
     export_alu_out_if.connect(monitor_fifo.analysis_export);
   endfunction: connect
   
  /*! 
   * Run - starts the processing in scoreboard
   */
   task run();
     string msg;
     AluInputTransaction      alu_in_tr;
     AluOutputTransaction     alu_out_tr_exp;   // expected transaction 
     AluOutputTransaction     alu_out_tr_real;  // real transaction
     logic [DATA_WIDTH-1:0]   operandB;
     logic [DATA_WIDTH*2-1:0] multResult;
     
     forever
     begin
    
       // receive input transaction from Driver
       driver_fifo.get(alu_in_tr);
           
       // display received transaction
       alu_in_tr.display("SCOREBOARD INPUT:");
       
       alu_out_tr_exp = new();
       
       // selection of operand B
       priority case (alu_in_tr.movi)
         2'b00 : operandB = alu_in_tr.reg_b;  // register operand
         2'b01 : operandB = alu_in_tr.mem;    // memory operand
         2'b10 : operandB = alu_in_tr.imm;    // immediate operand
         default : begin
                     $sformat(msg, "Unknown operand identifier!!!\n");
                     ovm_report_error("SCOREBOARD", msg, OVM_NONE);
                     $stop;
                   end  
       endcase
       
       // operation execution
       priority case (alu_in_tr.op)
         // ADD 
         4'b0000 : alu_out_tr_exp.ex_alu = alu_in_tr.reg_a + operandB;
         // SUB
         4'b0001 : alu_out_tr_exp.ex_alu = alu_in_tr.reg_a - operandB;
         // MULT
         4'b0010 : begin
                     // first part
                     multResult = alu_in_tr.reg_a * operandB;
                     alu_out_tr_exp.ex_alu = multResult[DATA_WIDTH-1:0]; 
                     
                     // receive output trasanction from Monitor
                     monitor_fifo.get(alu_out_tr_real);
       
                     // display expected transaction
                     alu_out_tr_exp.display("1:SCOREBOARD EXPECTED OUTPUT:");
       
                     // display received transaction
                     alu_out_tr_real.display("1:SCOREBOARD REAL OUTPUT:");
       
                     // compare expected and real output transaction
                     if (!alu_out_tr_real.compare(alu_out_tr_exp)) begin
                       $sformat(msg, "Expected and real output transaction do not match!!!\n");
                       ovm_report_fatal("SCOREBOARD", msg, OVM_NONE);
                     end 
                     
                     // second part 
                     alu_out_tr_exp = new();
                     alu_out_tr_exp.ex_alu = multResult[DATA_WIDTH*2-1:DATA_WIDTH];
                   end  
         // SHIFT RIGHT
         4'b0011 : alu_out_tr_exp.ex_alu = operandB>>1;
         // SHIFT LEFT
         4'b0100 : alu_out_tr_exp.ex_alu = operandB<<1;
         // ROTATE RIGHT
         4'b0101 : begin
                     alu_out_tr_exp.ex_alu = operandB>>1;
                     alu_out_tr_exp.ex_alu[DATA_WIDTH-1] = operandB[0];
                   end  
         // ROTATE LEFT
         4'b0110 : begin
                     alu_out_tr_exp.ex_alu = operandB<<1;
                     alu_out_tr_exp.ex_alu[0] = operandB[DATA_WIDTH-1];
                   end  
         // NOT
         4'b0111 : alu_out_tr_exp.ex_alu = ~(operandB);
         // AND
         4'b1000 : alu_out_tr_exp.ex_alu = alu_in_tr.reg_a & operandB;
         // OR
         4'b1001 : alu_out_tr_exp.ex_alu = alu_in_tr.reg_a | operandB;
         // XOR
         4'b1010 : alu_out_tr_exp.ex_alu = alu_in_tr.reg_a ^ operandB;
         // NAND
         4'b1011 : alu_out_tr_exp.ex_alu = ~(alu_in_tr.reg_a & operandB);
         // NOR
         4'b1100 : alu_out_tr_exp.ex_alu = ~(alu_in_tr.reg_a | operandB);
         // XNOR
         4'b1101 : alu_out_tr_exp.ex_alu = alu_in_tr.reg_a ~^ operandB;
         // INC
         // *** Zde doplnte svuj kod pro INCREMENT ***
         // DEC
         // *** Zde doplnte svuj kod pro DECREMENT ***
         default : begin
                     $sformat(msg, "Unsupported operation!!!\n");
                     ovm_report_error("SCOREBOARD", msg, OVM_NONE);
                     $stop;
                   end
       endcase 
       
       // receive output trasanction from Monitor
       monitor_fifo.get(alu_out_tr_real);
       
       // display expected transaction
       alu_out_tr_exp.display("SCOREBOARD EXPECTED OUTPUT:");
       
       // display received transaction
       alu_out_tr_real.display("SCOREBOARD REAL OUTPUT:");
       
       // compare expected and real output transaction
       if (!alu_out_tr_real.compare(alu_out_tr_exp)) begin
         $sformat(msg, "Expected and real output transaction do not match!!!\n");
         ovm_report_error("SCOREBOARD", msg, OVM_NONE);
         $stop;
       end 
     end  // of forever
   endtask : run    

 endclass : AluScoreboard   
