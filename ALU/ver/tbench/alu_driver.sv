/* *****************************************************************************
 * Project Name: ALU Functional Verification 
 * File Name:    Software Driver Class
 * Description:  Passes transactions on the input interfaces of DUT
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         29.3.2012 
 * ************************************************************************** */

/*!
 * This class is responsible for generating signals to input interface
 * of ALU. Transactions are received by 'transMbx'(Mailbox) property.
 * Unit must be enabled by "setEnable()" function call. Unit can be
 * stoped by "setDisable()" function call. You can send your custom
 * transaction by calling "sendTransaction" function.
 */
 class ALUDriver #(int pDataWidth = 8) extends Driver;  

   /*
    * Public Class Atributes
    */
    //! ALU input interface
    virtual iAluIn #(pDataWidth) aluIn; 
        
   /*
    * Public Class Methods
    */

   /*!
    * Constructor - creates driver object 
    *
    * \param inst     - driver instance name
    * \param transMbx - transaction mailbox   
    * \param fl       - input FrameLink interface
    */           
    function new (string inst, 
                  byte id,
                  tTransMbx transMbx, 
                  virtual iAluIn #(pDataWidth) aluIn
                  ); 
      super.new(inst, id, transMbx);
      this.aluIn = aluIn;  //! Store pointer interface 
 
      this.aluIn.cb.ACT       <= 0;
      this.aluIn.cb.OP        <= 0;
      this.aluIn.cb.MOVI      <= 0;
      this.aluIn.cb.REG_A     <= 0;
      this.aluIn.cb.REG_B     <= 0;
      this.aluIn.cb.MEM       <= 0;
      this.aluIn.cb.IMM       <= 0;
      
    endfunction: new  
    
   /*! 
    * Enable Driver - eable driver and runs driver process
    */
    task setEnabled();
      enabled = 1;  //! Driver Enabling
      @(aluIn.cb);  
    endtask : setEnabled
        
   /*! 
    * Disable Driver
    */
    task setDisabled();
      enabled = 0;  
    endtask : setDisabled 
    
   /*
    * Private Class Methods
    */
   
   /*! 
    * Send wait - waits for defined count of clock.    
    */ 
    task sendWait(int clocks);
       repeat (clocks) @(aluIn.cb);
    endtask : sendWait
    
   /*! 
    * Send transactions - takes transactions from mailbox and sends it 
    * to interface.
    */  
    task sendTransactions(input int transCount);
      ALUInTransaction #(pDataWidth) transaction;
      Transaction to;
      int i=0;
      
      /*int cnt_movi0 = 0;
      int cnt_movi1 = 0;
      int cnt_movi2 = 0;
      int cnt_opa0 = 0;
      int cnt_opa1 = 0;
      int cnt_opa2 = 0;
      int cnt_opb0 = 0;
      int cnt_opb1 = 0;
      int cnt_opb2 = 0;
      int cnt_opb3 = 0;
      int cnt_opb4 = 0;
      int cnt_opb5 = 0;
      int cnt_mem = 0;  */
      
      while (enabled && (i < transCount)) begin 
        transMbx.get(to);              //! Get transaction from mailbox 
        
        foreach (cbs[i])               //! Call transaction preprocessing
          cbs[i].pre_tr(to, id);
        
        $cast(transaction,to);
        
        /* if (transaction.movi == 0) cnt_movi0++;
        else if (transaction.movi == 1) cnt_movi1++;
        else if (transaction.movi == 2) cnt_movi2++;
      
        if (transaction.operandA <= 255 && transaction.operandA >= 170) cnt_opa0++;
        else if (transaction.operandA <= 169 && transaction.operandA >= 85) cnt_opa1++;
        else if (transaction.operandA <= 84 && transaction.operandA >= 0) cnt_opa2++;
      
        if (transaction.operandB <= 255 && transaction.operandB >= 215) cnt_opb0++;
        else if (transaction.operandB <= 214 && transaction.operandB >= 172) cnt_opb1++;
        else if (transaction.operandB <= 171 && transaction.operandB >= 129) cnt_opb2++;
        else if (transaction.operandB <= 128 && transaction.operandB >= 86) cnt_opb3++;
        else if (transaction.operandB <= 85 && transaction.operandB >= 43) cnt_opb4++;
        else if (transaction.operandB <= 42 && transaction.operandB >= 0) cnt_opb5++;
     
        if (transaction.operandMEM <= 255 && transaction.operandMEM >= 0) cnt_mem++;
      
        $write("cnt_movi0: %d\n", cnt_movi0);    
        $write("cnt_movi1: %d\n", cnt_movi1);
        $write("cnt_movi2: %d\n", cnt_movi2);
      
        $write("cnt_opa0: %d\n", cnt_opa0);    
        $write("cnt_opa1: %d\n", cnt_opa1);
        $write("cnt_opa2: %d\n", cnt_opa2);
      
        $write("cnt_opb0: %d\n", cnt_opb0);    
        $write("cnt_opb1: %d\n", cnt_opb1);
        $write("cnt_opb2: %d\n", cnt_opb2);
        $write("cnt_opb3: %d\n", cnt_opb3);    
        $write("cnt_opb4: %d\n", cnt_opb4);
        $write("cnt_opb5: %d\n", cnt_opb5);
   
        $write("cnt_mem: %d\n", cnt_mem);   */

        waitForAluRdy();
        
        //$write("enBtDelay: %d\n",transaction.enBtDelay);
        //$write("btDelay: %d\n",transaction.btDelay);
        
        // Set ACT signal and wait before sending next transaction
        //if (!transaction.enBtDelay) aluIn.cb.ACT <= 1;
        
        //else begin
          aluIn.cb.ACT <= 0;
          repeat (transaction.btDelay) @(aluIn.cb);
          aluIn.cb.ACT <= 1;
        //end
        
        sendData(transaction);
        
        foreach (cbs[i])               //! Call transaction postprocessing
          cbs[i].post_tr(to, id);
      
        //transaction.display(inst);   //! Display transaction
        i++;
      end
      waitForAluRdy();
      aluIn.cb.ACT <= 0;
    endtask : sendTransactions
    
   /*!
    * Send transaction data 
    * 
    * \param tr - ALU transaction
    */                 
    task sendData(ALUInTransaction #(pDataWidth) tr);
      aluIn.cb.OP     <= tr.operation;
      aluIn.cb.MOVI   <= tr.movi;    
      aluIn.cb.REG_A  <= tr.operandA;      
      aluIn.cb.REG_B  <= tr.operandB; 
      aluIn.cb.MEM    <= tr.operandMEM;  
      aluIn.cb.IMM    <= tr.operandIMM;       
      @(aluIn.cb);
      aluIn.cb.ACT    <= 1;
    endtask : sendData  
    
  /*!
    * Wait for ALU_RDY
    */
    task waitForAluRdy();
      while (!aluIn.cb.ALU_RDY) begin
        if (!enabled) return;
        @(aluIn.cb);
      end;
    endtask : waitForAluRdy     
        
 endclass : ALUDriver 

