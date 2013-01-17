/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_monitor.sv
 * Description:  OVM Monitor Class for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         2.10.2012
 * ************************************************************************** */

/*!
 * \brief AluMonitor
 * 
 * This class monitors signals on ALU output interface and sends their values 
 * in the form of transactions to other components.
 */

 class AluMonitor extends ovm_monitor;

   // registration of component tools
   `ovm_component_utils(AluMonitor)
   
   int output_file;        

   // reference to virtual output interface
   virtual iAluOut dut_alu_out_if;
   
   // reference to the input virtual interface
   virtual iAluIn dut_alu_in_if;
   
   // analysis port for sending data received from the DUT output interface
   // to the connected scoreboard or subscriber
   ovm_analysis_port #(AluOutputTransaction) aport_alu_out_if;
    
  /*! 
   * Constructor - creates AluMonitor object  
   *
   * \param name     - monitor instance name
   * \param parent   - parent class identification
   */ 
   function new (string name, ovm_component parent);
     super.new(name, parent);
   endfunction: new

  /*! 
   * Build - instanciates child components
   */ 
   function void build;
     string msg;
          
     output_file = $fopen("outputs_from_fv.txt", "w");
     if (output_file == 0) begin
       $sformat(msg, "Output file where ALU transactions should be stored is corrupted!!!\n");
       ovm_report_fatal("ALU_SEQUENCE", msg, OVM_NONE);
     end
   
     super.build();
     aport_alu_out_if = new("Analysis Port for ALU Output Interface", this);
     begin
       ovm_object obj;
       AluDutIfWrapper dut_if_wrapper;
       
       // reads object from configuration table
       if (!get_config_object("AluDutIfWrapper", obj, 0)) begin
         $sformat(msg, "It is not possible to obtain AluDutIfWrapper from the configuration table!\n");
         ovm_report_error("MONITOR", msg, OVM_NONE);
       end  
       
       // cast obtained object into the ALU Wrapper
       assert($cast(dut_if_wrapper, obj));
       
       // receive output virtual interface from the ALU wrapper
       dut_alu_out_if = dut_if_wrapper.dut_alu_out_if;
       
       // receive input virtual interface from the ALU wrapper
       dut_alu_in_if = dut_if_wrapper.dut_alu_in_if;
     end
   endfunction: build
  
  /*! 
   * Run - starts the processing in monitor
   */   
   task run;
     // check RESET
     while (dut_alu_out_if.RST) 
       @(dut_alu_out_if.cb); 
     
     forever
     begin
       AluOutputTransaction tr;      
       tr = new("Output Transaction");

       // wait for EX_ALU_VLD = 1
       waitForVld(tr);
       
       // receive the value of output
       tr.ex_alu = dut_alu_out_if.cb.EX_ALU;
       
       // write transaction to output file
       tr.fwrite(output_file, dut_alu_in_if.cb.ALU_RDY, 1);
       
       // display the content of transaction 
       //tr.display("MONITOR:"); 
       
       // sends generated transaction to the scoreboard, subscriber etc.
       aport_alu_out_if.write(tr);
       
       // synchronisation with the DUT
       @(dut_alu_out_if.cb);
     end
   endtask: run
   
  /*! 
   * Wait for validity of output EX_ALU and not RESET.
   */ 
   task waitForVld(AluOutputTransaction tr);
     while (!dut_alu_out_if.cb.EX_ALU_VLD) begin
       tr.ex_alu = dut_alu_out_if.cb.EX_ALU;
       tr.fwrite(output_file, dut_alu_in_if.cb.ALU_RDY, 0);
       @(dut_alu_out_if.cb);
     end  
   endtask : waitForVld
      
 endclass: AluMonitor
