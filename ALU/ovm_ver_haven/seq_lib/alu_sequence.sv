/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    alu_sequence.sv
 * Description:  OVM Sequence of Transactions for ALU
 * Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
 *               Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         27.9.2012
 * ************************************************************************** */

/*!
 * \brief AluSequence
 * 
 * This class represents OVM sequence of random input transactions for ALU.
 */
 
 class AluSequence extends ovm_sequence #(AluInputTransaction);

   // registration of component tools
   `ovm_object_utils(AluSequence)
   
   // output file where transactions are stored
   int output_file;      

  /*! 
   * Constructor - creates AluSequence object  
   *
   * \param name     - instance name
   */
   function new (string name = "");
     super.new(name);
   endfunction: new

  /*! 
   * Pre-body - implements opening of output file with transactions
   */ 
   task pre_body;
     string msg;
   
     /*output_file = $fopen("alu_trans_file.txt", "w");
     if (output_file == 0) begin
       $sformat(msg, "Output file where ALU transactions should be stored is corrupted!!!\n");
       ovm_report_fatal("ALU_SEQUENCE", msg, OVM_NONE);
     end*/  
     
     $write("START TIME: ");
     $system("date");
   endtask : pre_body

  /*! 
   * Body - implements behavior of the transaction
   */ 
   task body;
     int trans_count = 0;
     
     while (trans_count < TRANSACTION_COUNT) begin
      
       assert($cast(req, create_item(AluInputTransaction::get_type(), m_sequencer, "req")));
 
       start_item(req);
       
       assert(req.randomize());
       
       // store transactions into external file
       //req.fwrite(output_file);
       
       //req.display();
       finish_item(req);
       
       trans_count++; 
     end
   endtask: body
   
  /*! 
   * Post-body - implements closing of output file with transactions
   */ 
   task post_body;
     //$fclose(output_file); 
     
     ovm_report_info("SCOREBOARD", ":\n\nVERIFICATION ENDED CORRECTLY :)\n\n");
     
     $write("END TIME: ");
     $system("date");
     
     $stop();
   endtask : post_body

 endclass: AluSequence
