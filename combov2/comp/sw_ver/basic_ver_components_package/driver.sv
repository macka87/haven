/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Driver Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */  
 
/*!
 * \brief Driver
 * 
 * This class is parent class for any driver. Transactions are received by 
 * 'transMbx' (Mailbox) property. Unit must be enabled by "setEnable()" 
 * function call. Unit can be stoped by "setDisable()" function call. 
 * You can send your custom transaction by calling "sendTransaction" function.
 */
 class Driver;
    
   /*
    * Public Class Atributes
    */
    string    inst;      //! Driver identification
    byte      id;        //! Driver ID number
    bit       enabled;   //! Driver enabling
    tTransMbx transMbx;  //! Transaction mailbox
    InputCbs  cbs[$];    //! Driver callback list 
    
   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates driver object  
    *
    * \param inst     - driver instance name
    * \param id       - identification number     
    * \param transMbx - transaction mailbox     
    */     
    function new (string inst, 
                  byte id,
                  tTransMbx transMbx);
      this.inst        = inst;      //! Store driver identifier
      this.id          = id;        //! Driver ID number
      this.enabled     = 0;         //! Driver is disabled by default
      this.transMbx    = transMbx;  //! Store pointer to mailbox
    endfunction: new          
   
   /*! 
    * Set Driver Callback - put callback object into List 
    */
    virtual function void setCallbacks(InputCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
   /*! 
    * Enable Driver - eable driver and runs driver process
    */     
    virtual task setEnabled();
    endtask : setEnabled
        
   /*! 
    * Disable Driver
    */      
    virtual task setDisabled();
    endtask : setDisabled

   /*
    * Private Class Methods
    */

   /*! 
    * Send wait - waits for defined count of clock.    
    */ 
    virtual task sendWait(int clocks);
    endtask : sendWait
   
   /*! 
    * Send transactions - takes transactions from mailbox and sends it 
    * to interface.
    */
    virtual task sendTransactions(input int transCount);
    endtask : sendTransactions
 endclass : Driver
