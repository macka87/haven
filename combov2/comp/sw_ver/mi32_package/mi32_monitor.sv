/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Software MI32 Monitor Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         5.5.2011 
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
  
   /*
    * Public Class Methods
    */

   /*! 
    * Constructor - creates monitor object  
    *
    * \param inst - monitor instance name
    * \param id   - identification number     
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
    
   /*!
    * Wait for ARDY 
    */
    task waitForARDY();
      while (mi.cb.ARDY == 0) begin
        @(mi.cb);
      end;
    endtask : waitForARDY

   /*!
    * Wait for DRDY 
    */
    task waitForDRDY();
      while (mi.cb.DRDY == 0) begin
        @(mi.cb);
      end;
    endtask : waitForDRDY

   /*!
    * Send transaction command and receive data
    */     
    task receiveTransaction(MI32Transaction tr);
    
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
    endtask : receiveTransaction
  endclass : Mi32Monitor 

