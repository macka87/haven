/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    Output Controller Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
 class OutputController;
   
   /*
    * Public Class Atributes
    */ 
    string     inst;       //! Controller identification
    byte       id;         //! Controller ID number
    bit        enabled;    //! Controller enabling
    bit        busy;       //! Controller is receiving transaction
    tTransMbx  outputMbx;  //! Mailbox for transactions received from Sorter
    OutputCbs  cbs[$];     //! Output callback list 
    
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
      this.inst      = inst;      //! Store controller identifier
      this.id        = id;
      this.enabled   = 0;         //! Controller is disabled by default
      this.busy      = 0;         //! Controller is not busy by default 
      this.outputMbx = outputMbx; //! Mailbox
    endfunction: new 
   
   /*! 
    * Set Controller Callback - put callback object into List 
    */
    virtual function void setCallbacks(OutputCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks 
    
   /*! 
    * Enable Controller - enable controller and runs controller process
    */    
    virtual task setEnabled();
      enabled = 1;  //! Controller Enabling
      fork         
         run();     //! Creating controller subprocess
      join_none;    //! Don't wait for ending
    endtask : setEnabled
        
   /*! 
    * Disable Controller
    */
    virtual task setDisabled();
      enabled = 0;  //! Disable controller, after receiving last transaction
    endtask : setDisabled

   /*
    * Private Class Methods
    */
   
   /*! 
    * Run Controller - receives transactions and sends them for processing by 
    * callback.
    */      
    virtual task run();
      assert (0) 
        $fatal("Controller: Task run must be implemented in derived class"); 
    endtask : run
 endclass : OutputController  
