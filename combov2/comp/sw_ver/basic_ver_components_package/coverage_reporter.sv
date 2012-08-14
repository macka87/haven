/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    Coverage Reporter Class
 * Description: 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         14.7.2012 
 * ************************************************************************** */
 
 class CoverageReporter;
   
   /*
    * Public Class Atributes
    */ 
    tTransMbx mbx;    //! Mailbox for transactions received from Sorter
    string    inst;   //! Reporter identification
    byte      id;     //! Reporter ID number
    bit enabled;      //! Reporter enabling
    bit busy;         //! Reporter is receiving transaction

   /*
    * Public Class Methods
    */ 
    
   /*! 
    * Constructor 
    */    
    function new(string inst,
                 byte id,
                 tTransMbx mbx
                 ); 
       this.inst      = inst;      //! Store reporter identifier
       this.id        = id;        //! Store reporter ID
       this.mbx       = mbx;       //! Store pointer to mailbox
       this.enabled   = 0;         //! Reporter is disabled by default
       this.busy      = 0;         //! Reporter is not busy by default 
    endfunction: new
    
   /*! 
    * Enable Reporter - enable reporter and runs reporter process
    */    
    virtual task setEnabled();
      enabled = 1;  //! Reporter Enabling
      fork         
         run();     //! Creating reporter subprocess
      join_none;    //! Don't wait for ending
    endtask : setEnabled
        
   /*! 
    * Disable Reporter
    */
    virtual task setDisabled();
      enabled = 0;  //! Disable reporter, after receiving last transaction
    endtask : setDisabled

   /*
    * Private Class Methods
    */

   /*! 
    * Run Reporter - receives messages from hardware assertion checker and
    * prints corresponding reports .
    */ 
    virtual task run();
      assert (0) 
        $fatal("Controller: Task run must be implemented in derived class"); 
    endtask : run
 endclass : CoverageReporter  
