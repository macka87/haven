/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Monitor Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

/*!
 * \brief Monitor
 * 
 * This class is parent class for any Monitor. It is responsible for
 * creating transaction objects. Unit must be enabled by "setEnable()" 
 * function call. Monitoring can be stoped by "setDisable()" function call. 
 */
 class Monitor;
  
   /*
    * Public Class Atributes
    */  
    string    inst;     //! Monitor identification
    byte      id;       //! Monitor ID number
    bit       enabled;  //! Monitor enabling
    bit       busy;     //! Monitor is sending transaction
    OutputCbs cbs[$];   //! Callback list

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
                  byte id);
      this.inst        = inst;      //! Store monitor identifier
      this.id          = id;        //! Monitor ID number
      this.enabled     = 0;         //! Monitor is disabled by default
      this.busy        = 0;         //! Monitor is not busy by default  
    endfunction: new 
    
   /*! 
    * Set Monitor Callback - put callback object into List 
    */
    virtual function void setCallbacks(OutputCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
       
   /*! 
    * Enable Monitor - enable monitor and runs monitor process
    */    
    virtual task setEnabled();
      enabled = 1;  //! Monitor Enabling
      fork         
         run();     //! Creating monitor subprocess
      join_none;    //! Don't wait for ending
    endtask : setEnabled
        
   /*! 
    * Disable Monitor
    */
    virtual task setDisabled();
      enabled = 0;  //! Disable monitor, after receiving last transaction
    endtask : setDisabled

   /*
    * Private Class Methods
    */
   
   /*! 
    * Run Monitor - receives transactions and sends them for processing by 
    * callback.
    */      
    virtual task run();
      assert (0) 
        $fatal("Monitor: Task run must be implemented in derived class"); 
    endtask : run
 endclass : Monitor
