/* *****************************************************************************
 * Project Name: ALU Functional Verification 
 * File Name:    Software Driver Class
 * Description:  Passes transactions on the input interfaces of DUT
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         22.3.2012 
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
    virtual iAluIn #(pDataWidth) aluIn; //virtual iAluIn.aluin_tb aluIn;
    
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
 
      this.aluIn.cb.ACT     <= 0;
      this.aluIn.cb.OP      <= 0;
      this.aluIn.cb.MOVI    <= 0;
      this.aluIn.cb.REG_A   <= 0;
      this.aluIn.cb.REG_B   <= 0;
      this.aluIn.cb.IMM     <= 0;
      this.aluIn.cb.MEM     <= 0;
     
    endfunction: new  
    
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
      
      while (enabled && (i < transCount)) begin 
        transMbx.get(to);              //! Get transaction from mailbox 
        
        foreach (cbs[i])               //! Call transaction preprocessing
          cbs[i].pre_tr(to, id);
        
        $cast(transaction,to);
          
        // Set ACT signal and wait before sending next transaction
        // $write("enBtDelay: %d\n",enBtDelay);
        // $write("btDelay: %d\n",btDelay);
        if (!transaction.enBtDelay) aluIn.cb.ACT <= 1;
        else begin
          repeat (transaction.btDelay) @(aluIn.cb);
          aluIn.cb.ACT <= 1;
        end 
      
        waitForAluRdy(); 
      
        sendData(transaction);         //! Send transaction
        
        foreach (cbs[i])               //! Call transaction postprocessing
          cbs[i].post_tr(to, id);
      
        //transaction.display(inst);   //! Display transaction
        i++;
      end
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
      aluIn.cb.IMM    <= tr.operandIMM;       
      aluIn.cb.MEM    <= tr.operandMEM;      
      @(aluIn.cb);
      aluIn.cb.ACT    <= 0;
    endtask : sendData  
    
  /*!
    * Wait for ALU_RDY
    */
    task waitForAluRdy();
      do begin
        // Wait if ALU_RDY
        if (!aluIn.cb.ALU_RDY)
          @(aluIn.cb);
        if (!enabled) return;
      end while (!aluIn.cb.ALU_RDY); 
    endtask : waitForAluRdy     
        
 endclass : ALUDriver 

