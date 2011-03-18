/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Software FrameLink Responder Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

/*!
 * This class is responsible for random intra- and intertransaction's dealys. 
 * Unit must be enabled by "setEnable()" function call. Random delaying can be
 * stoped by "setDisable()" function call.
 * 
 * \param pDataWidth - width of transaction data
 * \param pDremWidth - drem width  
 */
 class FrameLinkResponder #(int pDataWidth=32, int pDremWidth=2);
    
   /*
    * Public Class Atributes
    */
    string  inst;     //! Responder identification
    byte    id;       //! Responder identification number
    bit     enabled;  //! Responder is enabled
    virtual iFrameLinkTx.tb #(pDataWidth,pDremWidth) fl;
    
    //! --- RANDOMIZATION OF DELAY PARAMETERS ---
    
    //! Enable/Disable delays "between transactions" according to weights
    rand bit enBtDelay;   
         byte btDelayEn_wt  = 1; 
         byte btDelayDi_wt  = 3;

    //! Value of delay "between transactions" randomized inside boundaries
    rand byte btDelay; 
         byte btDelayLow    = 0;
         byte btDelayHigh   = 3;
    
    //! Enable/Disable delays "inside transaction" according to weights 
    rand bit enItDelay;     
         byte itDelayEn_wt  = 1; 
         byte itDelayDi_wt  = 3;
    
    //! Value of delay "inside transaction" randomized inside boundaries  
    rand byte itDelay;  
         byte itDelayLow    = 0;
         byte itDelayHigh   = 3;
    
    //! Constraints for randomized values 
    constraint cDelay1 {
      enBtDelay dist { 1'b1 := btDelayEn_wt,
                       1'b0 := btDelayDi_wt
                     };
    };                 

    constraint cDelay2 {
      btDelay inside {
                      [btDelayLow:btDelayHigh]
                     };
    };                 

    constraint cDelay3 {
      enItDelay dist { 1'b1 := itDelayEn_wt,
                       1'b0 := itDelayDi_wt
                     };
    };                 
     
    constraint cDelay4 {    
      itDelay inside {
                      [itDelayLow:itDelayHigh]
                     };               
    }; 

   /*
    * Public Class Methods
    */

   /*!
    * Constructor - creates responder object 
    *
    * \param inst     - responder instance name
    * \param fl       - output FrameLink interface
    */
    function new ( string inst,
                   byte id,
                   virtual iFrameLinkTx.tb #(pDataWidth,pDremWidth) fl
                   );
      this.enabled     = 0;     //! Responder is disabled by default   
      this.fl          = fl;    //! Store pointer interface 
      this.inst        = inst;  //! Store responder identifier
      this.id          = id;    //! Store responder identification number  
      
      fl.cb.DST_RDY_N <= 1;     //! Ready ONLY IF enabled
    endfunction
    
   /*! 
    * Enable Responder - eable responder and runs responder process
    */
    task setEnabled();
      enabled = 1;  //! Responder Enabling
      fork         
        run();      //! Creating responder subprocess
      join_none;    //! Don't wait for ending
    endtask : setEnabled
        
   /*! 
    * Disable Driver
    */
    task setDisabled();
      $write("DISABLING RESPONDER\n");
      enabled = 0;  //! Disable responder, after receiving last transaction
    endtask : setDisabled 
    
   /*
    * Private Class Methods
    */
    
   /*!
    * Run Responder 
    */
    task run();
      
      while (enabled) begin
        fl.cb.DST_RDY_N <= 0;  //! destination ready active for one cycle
        @(fl.cb);
        assert(randomize());   //! randomize delays

        if (fl.cb.EOF_N == 0 && fl.cb.SRC_RDY_N == 0)   
          waitBtDelay();       //! between transaction delay
        else                                           
          waitItDelay();       //! inside transaction delay
      end
      fl.cb.DST_RDY_N <= 1;
    endtask : run
   
   /*!
    * Random wait between sending transactions (Set DST_RDY_N to 1)
    */ 
    task waitBtDelay();
      if (enBtDelay)
        repeat (btDelay) begin
          fl.cb.DST_RDY_N <= 1;
          @(fl.cb);
        end
    endtask : waitBtDelay
   
   /*!
    * Random wait during sending transaction (Set DST_RDY_N to 1)
    */     
    task waitItDelay();
      if (enItDelay)
        repeat (itDelay) begin
          fl.cb.DST_RDY_N <= 1;
          @(fl.cb);
        end
    endtask : waitItDelay
 endclass: FrameLinkResponder
