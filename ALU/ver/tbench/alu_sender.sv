/* *****************************************************************************
 * Project Name: ALU Functional Verification 
 * File Name:    Hardware ALU Sender Class
 * Description:  Prepares hardware representation of transactions.
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         23.3.2012 
 * ************************************************************************** *
  
/*!
 * This class is responsible for dividing ALU transactions to parts
 * and attaching NetCOPE protocol header to each part. Also creates control 
 * transactions (src_rdy information) with NetCOPE protocol header. Transactions
 * are received by 'transMbx'(Mailbox) property.
 *
 */
 class ALUSender #(int pDataWidth = 8) extends Sender;  
   /*
    * Public Class Methods
    */

   /*!
    * Constructor - creates sender object 
    *
    * \param inst     - driver instance name
    * \param transMbx - transaction mailbox   
    */           
    function new (string inst, 
                  byte id,
                  tTransMbx transMbx,
                  tTransMbx inputMbx 
                  ); 
      super.new(inst, id, transMbx, inputMbx);
    endfunction: new 
    
   /*
    * Private Class Methods
    */
 
   /*! 
    * Sends transactions - takes transaction from mailbox, divides it to parts
    * and adds NetCOPE protocol header to each part.     
    */  
    task sendTransactions(input int transCount);
      ALUInTransaction #(pDataWidth) transaction;
      Transaction to;
      int i=0;
      
      while (i < transCount) begin  
        transMbx.get(to);                 //! Get transaction from mailbox 
        
        foreach (cbs[i])                  //! Call transaction postprocessing
          cbs[i].post_tr(to, id);  
          
        $cast(transaction,to);   
        //transaction.display(inst);        //! Display transaction
        createNetCOPETrans(transaction);  //! Create NetCOPE transactions
        i++;
      end  
    endtask : sendTransactions
    
   /*! 
    * Create data and control NetCOPE transactions from ALU transaction.      
    *
    * \param tr - input ALU transaction
    */  
    task createNetCOPETrans(input ALUInTransaction #(pDataWidth) tr);
      createDataTransaction(tr);
      createControlTransaction(tr);
    endtask : createNetCOPETrans
    
   /*! 
    * Create NetCOPE data transaction from ALU input transaction.      
    *
    * \param tr - input FrameLink transaction
    */  
    task createDataTransaction(input ALUInTransaction #(pDataWidth) tr);
      int partSize, size;
      int counter = 0;
      NetCOPETransaction dataTrans = new();
            
      // NetCOPE transaction settings      
      dataTrans.endpointID  = id;
      dataTrans.transType   = 0;  // data transaction
      dataTrans.ifcProtocol = 0;  // no protocol
      
      // Size of Data part
      if (pDataWidth%8 == 0) partSize = pDataWidth/8;
      else partSize = pDataWidth/8+1;
      
      size = 2 + 4*partSize; // operation[1 B] + movi[1B] + 4*operand[partSize]
            
      // NetCOPE transaction transported data  
      dataTrans.data = new[size + 8];
      
      // NetCOPE header
      dataTrans.data[counter++] = id;             // endpointID
      dataTrans.data[counter++] = 0;              // endpointProtocol
      dataTrans.data[counter++] = 0; 
      dataTrans.data[counter++] = 0;
      dataTrans.data[counter++] = 0;              // transType
      dataTrans.data[counter++] = 0;
      dataTrans.data[counter++] = 0;              // ifcProtocol
      dataTrans.data[counter++] = 0;              // ifcInfo
      
      // data 
      dataTrans.data[counter++] = tr.operation;   // operation
      dataTrans.data[counter++] = tr.movi;        // movi
      
      for (int i=0; i<partSize; i++)
        for (int j=0; j<pDataWidth; j++)      
          dataTrans.data[counter++][j] = 
            tr.operandA[i*pDataWidth+j];          // operand A
          
      for (int i=0; i<partSize; i++)      
        for (int j=0; j<pDataWidth; j++)
          dataTrans.data[counter++][j] = 
            tr.operandB[i*pDataWidth+j];          // operand B
            
      for (int i=0; i<partSize; i++)      
        for (int j=0; j<pDataWidth; j++)
          dataTrans.data[counter++][j] = 
            tr.operandMEM[i*pDataWidth+j];        // memory operand
                        
      for (int i=0; i<partSize; i++)      
        for (int j=0; j<pDataWidth; j++)
          dataTrans.data[counter++][j] = 
            tr.operandIMM[i*pDataWidth+j];        // immediate operand            
           
      dataTrans.display("DATA");
      inputMbx.put(dataTrans);    // put transaction to mailbox
    endtask : createDataTransaction 
    
   /*! 
    * Create NetCOPE control transaction from ALU input transaction.      
    *
    * \param tr - input ALU transaction
    */  
    task createControlTransaction(input ALUInTransaction #(pDataWidth) tr);
      NetCOPETransaction controlTrans = new();
      int size    = 1; // btDelay takes 1 Byte
            
      controlTrans.endpointID  = id;
      controlTrans.transType   = 5;  // control src_rdy transaction
      controlTrans.ifcProtocol = 0;  // no protocol
      controlTrans.ifcInfo     = 0;  // no info
      
      controlTrans.data    = new[size + 8];
      
      // NetCOPE header
      controlTrans.data[0] = id;  // endpointID
      controlTrans.data[1] = 0;   // endpointProtocol
      controlTrans.data[2] = 0; 
      controlTrans.data[3] = 0;
      controlTrans.data[4] = 5;   // transType
      controlTrans.data[5] = 0;
      controlTrans.data[6] = 0;   // ifcProtocol
      controlTrans.data[7] = 0;   // ifcInfo
      
      // data
      if (tr.enBtDelay) controlTrans.data[8] = tr.btDelay;
      else controlTrans.data[8] = 0;
      
      controlTrans.display("CONTROL");
      inputMbx.put(controlTrans);   // put transaction to mailbox
    endtask : createControlTransaction  
     
 endclass : ALUSender
