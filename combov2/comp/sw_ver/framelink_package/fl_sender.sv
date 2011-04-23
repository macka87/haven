/* *****************************************************************************
 * Project Name: Hardware-Software Framework for Functional Verification 
 * File Name:    Hardware FrameLink Sender Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** *
  
/*!
 * This class is responsible for dividing FrameLink transactions to parts
 * and attaching NetCOPE protocol header to each part. Also creates control 
 * transactions (src_rdy information) with NetCOPE protocol header. Transactions
 * are received by 'transMbx'(Mailbox) property.
 *
 */
 class FrameLinkSender extends Sender;  
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
      FrameLinkTransaction transaction;
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
    * Create data and control NetCOPE transactions from FrameLink transaction.      
    *
    * \param tr - input FrameLink transaction
    */  
    //! dorobit potom pre viac slovne pakety !!!!!!!!
    task createNetCOPETrans(input FrameLinkTransaction tr);
      for (int i=0; i<tr.frameParts; i++)
        if (i == (tr.frameParts-1)) createDataTransaction(tr, 1, 1, i);
        else createDataTransaction(tr, 0, 1, i);
      createControlTransaction(tr);
    endtask : createNetCOPETrans
    
   /*! 
    * Create NetCOPE data transaction from one part of FrameLink transaction.      
    *
    * \param tr - input FrameLink transaction
    */  
    task createDataTransaction(input FrameLinkTransaction tr, 
                               input bit lastPart,
                               input bit allData,
                               input int part);
      NetCOPETransaction dataTrans = new();
      
      dataTrans.endpointID  = id;
      //dataTrans.endpointID  = 0;  // identifies driver protocol
      dataTrans.transType   = 0;  // data transaction
      dataTrans.ifcProtocol = 1;  // identifies FrameLink protocol
      dataTrans.ifcInfo     = 2*allData + lastPart;  
      
      dataTrans.data        = new[tr.data[part].size];
      dataTrans.data        = tr.data[part];
      
      //dataTrans.display("DATA");
      inputMbx.put(dataTrans);    // put transaction to mailbox
    endtask : createDataTransaction 
    
   /*! 
    * Create NetCOPE control transaction from FrameLink transaction.      
    *
    * \param tr - input FrameLink transaction
    */  
    task createControlTransaction(input FrameLinkTransaction tr);
      NetCOPETransaction controlTrans = new();
      int size    = 1; // btDelay takes 1 Byte
      int counter = 0;
      
      controlTrans.endpointID  = id;
      //controlTrans.endpointID  = 0;  // identifies driver protocol
      controlTrans.transType   = 5;  // control src_rdy transaction
      controlTrans.ifcProtocol = 1;  // no protocol
      controlTrans.ifcInfo     = 0;  // no info
      
      // size = total count if words in framelink packet
      for (int i=0; i<tr.frameParts; i++) begin
        $write("data size: %d\n", tr.data[i].size);
        size += (tr.data[i].size-1);
      end  
            
      controlTrans.data    = new[size];
      
      if (tr.enBtDelay) controlTrans.data[counter] = tr.btDelay;
      else controlTrans.data[counter] = 0;
      
      counter++;
      
      for (int i=0; i<tr.frameParts; i++) begin
        for (int j=0; j<tr.data[i].size-1; j++) begin
          if (tr.enItDelay) 
            controlTrans.data[counter] = tr.itDelay[i][j];
          else 
            controlTrans.data[counter] = 0;  
          counter++;
        end  
      end
         
      //controlTrans.display("CONTROL");
      inputMbx.put(controlTrans);   // put transaction to mailbox
    endtask : createControlTransaction  
     
 endclass : FrameLinkSender