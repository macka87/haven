/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Driver Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** *  
 
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
    bit       enabled;   //! Driver enabling
    bit       busy;      //! Driver is sending transaction
    tTransMbx transMbx;  //! Transaction mailbox
    
   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates driver object  
    *
    * \param inst     - driver instance name
    * \param transMbx - transaction mailbox     
    */     
    function new (string inst, tTransMbx transMbx);
      this.enabled     = 0;         //! Driver is disabled by default
      this.busy        = 0;         //! Driver is not busy by default   
      this.transMbx    = transMbx;  //! Store pointer to mailbox
      this.inst        = inst;      //! Store driver identifier
    endfunction: new          
    
   /*! 
    * Enable Driver - eable driver and runs driver process
    */     
    virtual task setEnabled();
      enabled = 1;  //! Driver Enabling
      fork         
         run();     //! Creating driver subprocess
      join_none;    //! Don't wait for ending
    endtask : setEnabled
        
   /*! 
    * Disable Driver
    */      
    virtual task setDisabled();
      enabled = 0;  //! Disable Driver
    endtask : setDisabled

   /*! 
    * Send Transaction - sends transaction to input interface
    *
    * \param transaction - transaction from generator or direct transaction
    */
    task sendTransaction(Transaction transaction);
    endtask : sendTransaction
    
   /*
    * Private Class Methods
    */
    
   /*! 
    * Run Driver - takes transactions from mailbox and sends it to interface
    */      
    virtual task run();
    endtask : run
 endclass : Driver
