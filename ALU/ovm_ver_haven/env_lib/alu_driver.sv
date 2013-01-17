/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_driver.sv
 * Description:  OVM Driver Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         1.10.2012
 * ************************************************************************** */

/*!
 * \brief AluDriver
 * 
 * This class drives the input interface of ALU and supplies transactions from 
 * sequencer to this interface.
 */

 class AluDriver extends ovm_driver #(AluInputTransaction);

   // registration of component tools
   `ovm_component_utils(AluDriver)
   
   int output_file;   
    
   // reference to the input virtual interface
   virtual iAluIn dut_alu_in_if;
   
   // analysis port for sending data received from sequencer to the connected 
   // scoreboard and subscriber 
   ovm_analysis_port #(AluInputTransaction) aport_alu_in_if;
   
   // inbuild covergroup
   logic act, rst;
   
   // Enumeration for operation
   enum logic [3:0] {ADD, SUB, MULT, SHIFT_RIGHT, SHIFT_LEFT, ROTATE_RIGHT, ROTATE_LEFT, NOT, AND, OR, XOR, NAND, NOR, XNOR, INC, DEC} operation;
   
   logic [3:0] operation_s;
   
   covergroup ActCovergroup;
     // reset
     resetB : coverpoint rst {
       bins rst0 = {0};        
       bins rst1 = {1};
     }
     
     // reset at least two times
     reset_after_reset: coverpoint rst {
       bins reset_down = (1 => 0); 
       bins reset_up   = (0 => 1);
     } 
     
     // delayed setting of activity signal
     delayed_act: coverpoint act { 
       bins delayed1_act = (1 => 0 => 1);
       bins delayed2_act = (1 => 0 [* 2] => 1);
       bins delayed3_act = (1 => 0 [* 3] => 1);
       bins delayed4_act = (1 => 0 [* 4] => 1);
       bins delayed5_act = (1 => 0 [* 5] => 1);
     }
     
     // operation 
     operationH: coverpoint operation;
     
     // operation x delayed_act
     delayed_act_operation_cross : cross delayed_act, operationH;
     
     option.per_instance=1; // Also per instance statistics
   endgroup    

  /*! 
   * Constructor - creates AluDriver object  
   *
   * \param name     - driver instance name
   * \param parent   - parent class identification
   */ 
   function new(string name, ovm_component parent);
     super.new(name, parent);
     ActCovergroup = new();
   endfunction: new

  /*! 
   * Build - instanciates child components
   */ 
   function void build;
     string msg;
   
     super.build();
     aport_alu_in_if = new("Analysis Port for ALU Input Interface", this);
     begin
       ovm_object obj;
       AluDutIfWrapper dut_if_wrapper;
       
       // read object from the configuration table
       if (!get_config_object("AluDutIfWrapper", obj, 0)) begin
         $sformat(msg, "It is not possible to obtain AluDutIfWrapper from the configuration table!\n");
         ovm_report_error("DRIVER", msg, OVM_NONE);
       end
       
       // cast obtained object into the ALU Wrapper
       assert($cast(dut_if_wrapper, obj));
       
       // receive input virtual interface from the ALU wrapper
       dut_alu_in_if = dut_if_wrapper.dut_alu_in_if;
     end
   endfunction: build   
  
  /*! 
   * Run - starts the processing in driver
   */ 
   task run;
     AluInputTransaction tr;
     string msg;
     
     output_file = $fopen("inputs_from_fv.txt", "w");
     if (output_file == 0) begin
       $sformat(msg, "Output file where ALU transactions should be stored is corrupted!!!\n");
       ovm_report_fatal("ALU_SEQUENCE", msg, OVM_NONE);
     end
          
     dut_alu_in_if.cb.ACT <= 0;  
     
     // synchronization with the DUT
     @(dut_alu_in_if.cb);
   
     forever
     begin
     
       // wait for readiness of ALU to process data
       waitForAluRdy(tr);
     
       // receive transaction from sequencer
       seq_item_port.get(tr);
       
       // display the content of transaction 
       //tr.display("DRIVER:");
       
       
       
       // sample coverage
       rst = dut_alu_in_if.RST;
       act = tr.act;
       operation_s = tr.op;
       $cast(operation, operation_s);
       ActCovergroup.sample();

       // set input signals of DUT
       if (GEN_OUTPUT==0 || GEN_OUTPUT==2)
         begin
           // sends values from transaction on the virtual interface
           dut_alu_in_if.cb.ACT   <= tr.act;        
           dut_alu_in_if.cb.OP    <= tr.op;
           dut_alu_in_if.cb.MOVI  <= tr.movi;
           dut_alu_in_if.cb.REG_A <= tr.reg_a;
           dut_alu_in_if.cb.REG_B <= tr.reg_b;
           dut_alu_in_if.cb.MEM   <= tr.mem;
           dut_alu_in_if.cb.IMM   <= tr.imm;
         end
       
       // write transaction to output file
       tr.fwrite(output_file, 0, rst);
         
       // synchronise with CLK 
       @(dut_alu_in_if.cb);  
        
       // sends generated transaction to the scoreboard, subscriber etc.
       if (tr.act)
         aport_alu_in_if.write(tr);
     end
   endtask: run
  
  /*!
   * Wait for ALU_RDY
   */
   task waitForAluRdy(AluInputTransaction tr);
     while (!dut_alu_in_if.cb.ALU_RDY || dut_alu_in_if.RST) begin
       rst = dut_alu_in_if.RST;
       ActCovergroup.sample(); 
       
       if (tr!=null) 
       
       // write transaction to output file
       tr.fwrite(output_file, 0, rst);
       
       @(dut_alu_in_if.cb);
     end  
   endtask : waitForAluRdy     
 endclass: AluDriver
