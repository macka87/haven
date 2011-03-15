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
 class FrameLinkSender #();  
 
   /*
    * Public Class Atributes
    */
    string    inst;      //! Sender identification
    byte      id;        //! Sender ID number
    bit       enabled;   //! Sender is enabled
    bit       busy;      //! Sender is sending transaction
    tTransMbx transMbx;  //! Transaction mailbox
    tTransMbx inputMbx;  //! Input controller's mailbox 
    
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
      this.id          = id;        //! Sender ID number
      this.enabled     = 0;         //! Sender is disabled by default
      this.busy        = 0;         //! Sender is not busy by default
      this.transMbx    = transMbx;  //! Store pointer to mailbox
      this.inputMbx    = inputMbx;  //! Store pointer to mailbox 
      this.inst        = inst;      //! Store sender identifier
    endfunction: new 
    
   /*! 
    * Enable Sender - eable sender and runs sender process
    */
    task setEnabled();
      enabled = 1;  //! Sender Enabling
      fork         
        run();      //! Creating sender subprocess
      join_none;    //! Don't wait for ending
    endtask : setEnabled
        
   /*! 
    * Disable Sender
    */
    task setDisabled();
      enabled = 0;  //! Disable Sender, after sending last transaction it ends
    endtask : setDisabled
    
   /*
    * Private Class Methods
    */
    
   /*! 
    * Run Sender - takes transaction from mailbox, divides it to parts and adds 
    * NetCOPE protocol header to each part.     
    */  
    task run();
      FrameLinkTransaction transaction;
      Transaction to;
      
      while (enabled) begin               //! Repeat while enabled
        transMbx.get(to);                 //! Get transaction from mailbox 
        $cast(transaction,to);   
        transaction.display(inst);        //! Display transaction
        createNetCOPETrans(transaction);  //! Create NetCOPE transactions
      end
    endtask : run
    
   /*! 
    * Create data and control NetCOPE transactions from FrameLink transaction.      
    *
    * \param tr - input FrameLink transaction
    */  
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
      dataTrans.endpointID  = 0;  // identifies driver protocol
      dataTrans.transType   = 0;  // data transaction
      dataTrans.ifcProtocol = 1;  // identifies FrameLink protocol
      dataTrans.ifcInfo     = 2*allData + lastPart;  
      
      dataTrans.data        = new[tr.data[part].size];
      dataTrans.data        = tr.data[part];
      
      dataTrans.display("DATA");
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
      controlTrans.endpointID  = 0;  // identifies driver protocol
      controlTrans.transType   = 3;  // control src_rdy transaction
      controlTrans.ifcProtocol = 0;  // no protocol
      controlTrans.ifcInfo     = 0;  // no info
      
      if (tr.enItDelay) begin
        for (int i=0; i<tr.frameParts; i++)
          size += tr.itDelay[i].size; 
      end
      else size += 1;
      
      $write("size: %d\n",size);    
        
      controlTrans.data    = new[size];
      
      if (tr.enBtDelay) controlTrans.data[counter] = tr.btDelay;
      else controlTrans.data[counter] = 0;
      
      counter++;
      
      if (tr.enItDelay) begin
        for (int i=0; i<tr.frameParts; i++)
          for (int j=0; j<tr.itDelay[i].size; j++) begin
            controlTrans.data[counter] = tr.itDelay[i][j];
            counter++;
          end  
      end
      else controlTrans.data[counter] = 0;    
          
      controlTrans.display("CONTROL");
      inputMbx.put(controlTrans);   // put transaction to mailbox
    endtask : createControlTransaction  
     
 endclass : FrameLinkSender