/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    alu_monitor.sv
 * Description:  Monitor Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         23.1.2014
 * ************************************************************************** */

/*!
 * \brief AluMonitor
 * 
 * This class monitors signals on ALU output interface and sends their values 
 * in the form of transactions to other components.
 */

 class AluMonitor;

  /*! 
   * Virtual interfaces for DUT
   */ 
  
   virtual iAluOut dut_alu_out_if;
   
  /*! 
   * Channels
   */ 
   mailbox #(AluOutputTransaction) outputMbx;
   
  /*! 
   * Data Members
   */
   
  AluOutputTransaction alu_out_trans_c;
  
  /*
   * Definition of covergroups
   */
   
   covergroup alu_out_covergroup;
    
     alu_output_00_FF: coverpoint alu_out_trans_c.ex_alu {
       bins zeros = {0};
       bins ones  = {8'hFF}; 
     } 
     
   endgroup 
  
  /*!
   * Methods
   */
   
   // User-defined methods
   extern function new(virtual iAluOut dut_alu_out_if);
   extern task run();
   extern task waitForVld();
   
 endclass: AluMonitor



/*! 
 *  Constructor
 */
 function AluMonitor::new(virtual iAluOut dut_alu_out_if);
   this.dut_alu_out_if = dut_alu_out_if;  //! Store pointer interface 
   alu_out_covergroup = new();
 endfunction: new 



/*! 
 * Run - starts monitor processing.
 */  
 task AluMonitor::run(); 
   AluOutputTransaction alu_out_trans;  
   int cnt = 0;  
   
   $write("\n\n########## MONITOR ##########\n\n");
   
   // check RESET
   while (dut_alu_out_if.RST) 
     @(dut_alu_out_if.cb); 
   
   // create output transaction  
   alu_out_trans = new();  
   
   //while (cnt < TRANS_COUNT) begin
   forever begin
     
     // wait for EX_ALU_VLD = 1
     waitForVld();
       
     // clone output transaction
     alu_out_trans_c = alu_out_trans.clone(); 
       
     // receive the value of output
     alu_out_trans_c.ex_alu = dut_alu_out_if.cb.EX_ALU;
     
     // display the content of transaction 
     alu_out_trans_c.print("MONITOR:"); 
       
     outputMbx.put(alu_out_trans_c);
     
     // sample coverage
     alu_out_covergroup.sample();
     
     // print statistics
     $write("ALU OUTPUT COVERAGE: %0d Packets sampled, Coverage = %f%%\n", cnt, alu_out_covergroup.get_inst_coverage());
       
     cnt++;
       
     // sends generated transaction to the scoreboard, subscriber etc.
     //aport_alu_out_if.write(alu_out_trans);
      
     // synchronisation with the DUT
     @(dut_alu_out_if.cb);
   end
 endtask: run 
 


/*! 
 * Wait for validity of output EX_ALU and not RESET.
 */ 
 task AluMonitor::waitForVld();
   while (!(dut_alu_out_if.cb.EX_ALU_VLD === 1))  
     @(dut_alu_out_if.cb);
 endtask: waitForVld