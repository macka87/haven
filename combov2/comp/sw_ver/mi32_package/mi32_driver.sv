/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Software MI32 Driver Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         5.5.2011 
 * ************************************************************************** */
 
/*!
 * This class is responsible for generating signals to MI32
 * interface. Transactions are received by 'transMbx'(Mailbox) property.
 * Unit must be enabled by "setEnable()" function call. Unit can be
 * stoped by "setDisable()" function call. You can send your custom
 * transaction by calling "sendTransaction" function.
 */
 class MI32Driver extends Driver;

   /*
    * Public Class Atributes
    */
    //! FrameLink interface
    virtual iMi32.tb    mi;
    
   /*
    * Public Class Methods
    */

   /*!
    * Constructor - creates driver object 
    *
    * \param inst     - driver instance name
    * \param transMbx - transaction mailbox   
    * \param mi       - input MI32 interface
    */
    function new ( string inst,
                   byte id, 
                   tTransMbx transMbx, 
                   virtual iMi32.tb mi 
                         );
      super.new(inst, id, transMbx);
      this.enabled     = 0;            // Driver is disabled by default
      this.mi          = mi;           // Store pointer interface 
      
      this.mi.cb.ADDR      <= 0;
      this.mi.cb.DRD       <= 0;
      this.mi.cb.DWR       <= 0;
      this.mi.cb.BE        <= 0;
      this.mi.cb.RD        <= 0;
      this.mi.cb.WR        <= 0;
      this.mi.cb.ARDY      <= 0;
      this.mi.cb.DRDY      <= 0;
    endfunction: new  
    
   /*! 
    * Enable Driver - eable driver and runs driver process
    */
    task setEnabled();
      enabled = 1;  //! Driver Enabling
      @(mi.cb); 
    endtask : setEnabled
        
   /*! 
    * Disable Driver
    */
    task setDisabled();
      enabled = 0;  
    endtask : setDisabled
    
   /*
    * Private Class Methods
    */
   
   /*! 
    * Send wait - waits for defined count of clock.    
    */ 
    task sendWait(int clocks);
       repeat (clocks) @(mi.cb);
    endtask : sendWait 
    
   /*! 
    * Send transactions - takes transactions from mailbox and sends it 
    * to interface.
    */  
    task sendTransaction(MI32Transaction transaction);
      if (enabled) begin 
        if (transaction.enBtDelay)     //! Delay between transactions
          repeat (transaction.btDelay) 
            @(mi.cb);

        sendData(transaction);         //! Send transaction
        
        // Set no request 
        mi.cb.RD     <= 0;
        mi.cb.WR     <= 0;
        
        //transaction.display("MI trans");     //! Display transaction
      end
    endtask : sendTransaction 

   /*!
    * Send transaction data 
    * 
    * \param tr - MI32 transaction
    */
    task sendData(MI32Transaction tr);
      mi.cb.ADDR      <= tr.address;
      mi.cb.DWR       <= tr.data;    
      mi.cb.BE        <= tr.be;     
      mi.cb.WR        <= tr.rw;  // wr == 1 => write request 
      mi.cb.RD        <= !tr.rw; // wr == 0 => read request 
      
      @(mi.cb);
      waitForARDY();  // Wait until oposit side set ready

      // clear pending request signals
      mi.cb.WR        <= 0;
      mi.cb.RD        <= 0;
    endtask : sendData
    
   /*!
    * Wait for ARDY
    */      
    task waitForARDY();
      while (mi.cb.ARDY == 0) begin
        @(mi.cb);
      end;
    endtask : waitForARDY
     
  endclass : MI32Driver 

