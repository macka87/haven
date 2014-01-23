/* *****************************************************************************
 * Project Name: Genetic Algorithm for ALU
 * File Name:    alu_monitor.sv
 * Description:  Monitor Class for ALU
 * Authors:      Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         21.1.2014
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
   * Ports/Exports
   */ 
   
  /*! 
   * Data Members
   */
  
  /*!
   * Methods
   */
   
   // User-defined methods
   extern task run();
   extern task waitForVld();
   
 endclass: AluMonitor

 

/*! 
 * Run - starts monitor processing.
 */  
 task AluMonitor::run(); 
   /*AluOutputTransaction alu_out_trans, alu_out_trans_c;    
   
   // check RESET
   while (dut_alu_out_if.RST) 
     @(dut_alu_out_if.cb); 
   
   // create output transaction  
   alu_out_trans = AluOutputTransaction::type_id::create();  
   
   forever
     begin
       // wait for EX_ALU_VLD = 1
       waitForVld();
       
       // clone output transaction
       assert($cast(alu_out_trans_c, alu_out_trans.clone));
       
       // receive the value of output
       alu_out_trans.ex_alu = dut_alu_out_if.cb.EX_ALU;
       
       // display the content of transaction 
       //alu_out_trans.print("MONITOR:"); 
       
       // sends generated transaction to the scoreboard, subscriber etc.
       aport_alu_out_if.write(alu_out_trans);
       
       // synchronisation with the DUT
       @(dut_alu_out_if.cb);
     end*/
 endtask: run 
 


/*! 
 * Wait for validity of output EX_ALU and not RESET.
 */ 
 task AluMonitor::waitForVld();
   /*while (!(dut_alu_out_if.cb.EX_ALU_VLD === 1))  
     @(dut_alu_out_if.cb);*/
 endtask: waitForVld