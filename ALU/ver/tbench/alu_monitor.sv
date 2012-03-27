/* *****************************************************************************
 * Project Name: ALU Functional Verification 
 * File Name:    Software Monitor Class
 * Description:  Drives the output interfaces of DUT and builds 
 *               output transactions.
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         22.3.2012 
 * ************************************************************************** */
 
/*!
 * This class is responsible for creating transaction objects from 
 * output interface signals of ALU. After is transaction received it is sended
 * by callback to scoreboard. Unit must be enabled by "setEnable()" function
 * call. Monitoring can be stoped by "setDisable()" function call.
 */
 class ALUMonitor #(int pDataWidth = 8) extends Monitor;
    
   /*
    * Public Class Atributes
    */
    //! ALU interface
    virtual iAluOut.aluout_tb aluOut;
    
   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates monitor object  
    *
    * \param inst     - monitor instance name
    * \param id       - identification number     
    */
    function new (string inst,
                  byte id,
                  virtual iAluOut.aluout_tb aluOut
                  );
                  
      super.new(inst, id);
      this.aluOut = aluOut;  //! Store pointer interface 
    endfunction

   /*
    * Private Class Methods
    */
   
   /*! 
    * Run Monitor - receives transactions and sends them for processing by 
    * callback.
    */
    task run();
      ALUOutTransaction #(pDataWidth) transaction; 
      Transaction tr;

      while (enabled) begin              
        transaction = new();             
        $cast(tr, transaction);

        foreach (cbs[i])                 //! Call transaction preprocesing
          cbs[i].pre_tr(tr, id);       

        receiveTransaction(transaction); //! Receive Transaction
        //transaction.display(inst);
        
        // Necessary for not calling callback after monitor disabling
        if (!enabled) break;

        #(0); // Necessary for not calling callback before driver
        
        foreach (cbs[i])                 //! Call transaction postprocesing
          cbs[i].post_tr(tr, id);

        busy = 0;                        //! Monitor is not busy now
      end
    endtask : run
    
   /*!
    * Receives ALU Transaction from interface
    *     
    * \param tr - transaction
    */
    task receiveTransaction(ALUOutTransaction #(pDataWidth) tr);
      waitForExAluVLD();
      busy = 1;
      tr.alu_output  = aluOut.cb.EX_ALU;
      @(aluOut.cb);
    endtask : receiveTransaction
    
   /*!
    * Wait for EX_ALU_VLD
    */
    task waitForExAluVLD();
      do begin
        // Wait if EX_ALU_VLD
        if (!aluOut.cb.EX_ALU_VLD)
          @(aluOut.cb);
        if (!enabled) return;
      end while (!aluOut.cb.EX_ALU_VLD); 
    endtask : waitForExAluVLD
  
 endclass : ALUMonitor    
