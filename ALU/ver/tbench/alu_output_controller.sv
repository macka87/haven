/* *****************************************************************************
 * Project Name: ALU Functional Verification
 * File Name:    ALU Output Controller Class
 * Description:  Controller of the output software side of testbench.
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         23.3.2012 
 * ************************************************************************** */
 
 class ALUOutputController #(int pDataWidth = 8) extends OutputController;
   
   /*
    * Public Class Atributes
    */
    
   /*
    * Public Class Methods
    */ 
    
   /*! 
    * Constructor 
    */    
    function new(string inst,
                 byte id,
                 tTransMbx outputMbx 
                 ); 
       super.new(inst, id, outputMbx);
    endfunction: new
    
   /*! 
    * Run Controller - receives transactions and sends them for processing by 
    * callback.
    */ 
    task run();
      NetCOPETransaction ntr;
      ALUOutTransaction #(pDataWidth) alutr;
      Transaction tr;

      // create new ALU output transaction
      alutr = new();
      
      // fill ALU Transaction with received data        
      while (enabled) begin 
        // receive data from mailbox
        busy = 0;
        outputMbx.get(tr);
        busy = 1;
          
        $cast(ntr, tr);
        
        for (int i=0; i<ntr.size; i++)      
          for (int j=0; j<pDataWidth; j++)
            alutr.alu_output[i*pDataWidth+j] = ntr.data[i][j];
            
        //alutr.display("CREATED OUTPUT ALU TRANSACTION");
          
        $cast(tr, alutr);
          
        //! Call transaction postprocesing in scoreboard  
        foreach (cbs[i])          
          cbs[i].post_tr(tr, id); 
      end
    endtask : run
 endclass : ALUOutputController  
