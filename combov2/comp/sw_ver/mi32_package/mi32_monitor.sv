/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Software MI32 Monitor Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         24.4.2011 
 * ************************************************************************** */
 
/*!
 * This class is responsible for creating transaction objects from 
 * MI32 interface signals. After is transaction received it is sended
 * by callback to scoreboard. Unit must be enabled by "setEnable()" function
 * call. Monitoring can be stoped by "setDisable()" function call.
 */
 class Mi32Monitor extends Monitor;

   /*
    * Public Class Atributes
    */
    virtual iMi32.tb    mi;
  
    rand bit enTxDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int txDelayEn_wt             = 1; 
      int txDelayDisable_wt        = 3;

    rand integer txDelay; // Delay between transactions
      // Delay between transactions limits
      int txDelayLow          = 0;
      int txDelayHigh         = 3;
    // ----

    // -- Constrains --
    constraint cDelays {
      enTxDelay dist { 1'b1 := txDelayEn_wt,
                       1'b0 := txDelayDisable_wt
                     };

      txDelay inside {
                      [txDelayLow:txDelayHigh]
                     };
      }

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
                  byte id,
                  virtual iMi32.tb mi 
                  );
      super.new(inst, id);

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
    
    // -- Wait for ARDY -----------------------------------------------------
    // Wait for address ready signal
    task waitForARDY();
      while (mi.cb.ARDY == 0) begin
        @(mi.cb);
      end;
    endtask : waitForARDY

    // -- Wait for DRDY -----------------------------------------------------
    // Wait for data ready signal
   task waitForDRDY();
      while (mi.cb.DRDY == 0) begin
        @(mi.cb);
      end;
    endtask : waitForDRDY

    // -- Execute transaction -----------------------------------------------
    // Send transaction command and receive data
    task executeTransaction(Mi32Transaction tr);
    
      // Allign data from transaction to fl.DATA
      mi.cb.ADDR      <= tr.address;
      mi.cb.BE        <= tr.be;     
      mi.cb.WR        <= tr.rw;  // wr == 1 => write request 
      mi.cb.RD        <= !tr.rw; // wr == 0 => read request 
      
      @(mi.cb);
      waitForARDY();  // Wait until oposit side set ready

      // clear pending request signals
      mi.cb.WR        <= 0;
      mi.cb.RD        <= 0;

      waitForDRDY();  // Wait until oposit side set data ready

      tr.data = mi.cb.DRD;   // Store received data
      
    endtask : executeTransaction
     
  endclass : Mi32Monitor 

