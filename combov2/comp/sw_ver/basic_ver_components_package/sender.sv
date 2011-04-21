/* *****************************************************************************
 * Project Name: Hardware-Software Framework for Functional Verification 
 * File Name:    Hardware Sender Class
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
 class Sender;  
 
   /*
    * Public Class Atributes
    */
    string    inst;      //! Sender identification
    byte      id;        //! Sender ID number
    tTransMbx transMbx;  //! Transaction mailbox
    tTransMbx inputMbx;  //! Input controller's mailbox
    InputCbs  cbs[$];    //! Sender callback list  
    
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
      this.inst        = inst;      //! Store sender identifier
      this.id          = id;        //! Sender ID number
      this.transMbx    = transMbx;  //! Store pointer to mailbox
      this.inputMbx    = inputMbx;  //! Store pointer to mailbox 
    endfunction: new 
    
   /*! 
    * Set Sender Callback - callback object into List 
    */
    virtual function void setCallbacks(InputCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks 
    
   /*
    * Private Class Methods
    */
    
   /*! 
    * Sends start control transaction to HW.    
    */ 
    virtual task sendStart();
      NetCOPETransaction controlTrans = new();
      
      controlTrans.endpointID  = id;
     //controlTrans.endpointID  = 0;  // identifies driver protocol
      controlTrans.transType   = 1;  // control start transaction
      controlTrans.ifcProtocol = 0;  // no protocol
      controlTrans.ifcInfo     = 0;  // no info
      
      //controlTrans.display("START CONTROL");
      inputMbx.put(controlTrans);    // put transaction to mailbox  
    endtask : sendStart
    
   /*! 
    * Sends stop control transaction to HW.    
    */ 
    task sendStop();
      NetCOPETransaction controlTrans = new();
      
      controlTrans.endpointID  = id;
      //controlTrans.endpointID  = 0;  // identifies driver protocol
      controlTrans.transType   = 4;  // control stop transaction
      controlTrans.ifcProtocol = 0;  // no protocol
      controlTrans.ifcInfo     = 0;  // no info
      
      //controlTrans.display("STOP CONTROL");
      inputMbx.put(controlTrans);    // put transaction to mailbox  
    endtask : sendStop
    
   /*! 
    * Sends waitfor control transaction to HW.    
    */ 
    task sendWait(int clocks);
      NetCOPETransaction controlTrans = new();
      logic [63:0] data = clocks;
      
      controlTrans.endpointID  = id;
      //controlTrans.endpointID  = 0;  // identifies driver protocol
      controlTrans.transType   = 2;  // control wait transaction
      controlTrans.ifcProtocol = 0;  // no protocol
      controlTrans.ifcInfo     = 0;  // no info
      
      controlTrans.data        = new[8];
      for(int i=0; i<8; i++)
        for(int j=0; j<8; j++)
          controlTrans.data[i][j] = data[i*8+j];
      
      //controlTrans.display("WAIT FOR CONTROL");
      inputMbx.put(controlTrans);    // put transaction to mailbox  
    endtask : sendWait
    
   /*! 
    * Sends waitforever control transaction to HW.    
    */
    task sendWaitForever();
      NetCOPETransaction controlTrans = new();
      
      controlTrans.endpointID  = id;
      //controlTrans.endpointID  = 0;  // identifies driver protocol
      controlTrans.transType   = 3;  // control wait transaction
      controlTrans.ifcProtocol = 0;  // no protocol
      controlTrans.ifcInfo     = 0;  // no info
      
      //controlTrans.display("WAIT FOREVER CONTROL");
      inputMbx.put(controlTrans);    // put transaction to mailbox
    endtask : sendWaitForever
    
   /*! 
    * Sends transactions - takes transaction from mailbox, divides it to parts
    * and adds NetCOPE protocol header to each part.     
    */  
    virtual task sendTransactions(input int transCount);
    endtask : sendTransactions
 endclass : Sender  