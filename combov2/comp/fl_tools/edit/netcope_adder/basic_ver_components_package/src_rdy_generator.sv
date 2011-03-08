/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Source Ready Generator Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
 class SrcRdyGenerator; 
 
   /*
    * Public Class Atributes
    */
    
    //! FrameLink interface
    virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) fl;
    
    //! Enable/Disable delays "between transactions" according to weights
    rand bit enBtDelay;   
         int btDelayEn_wt  = 1; 
         int btDelayDi_wt  = 3;

    //! Value of delay "between transactions" randomized inside boundaries
    rand int btDelay; 
         int btDelayLow    = 0;
         int btDelayHigh   = 3;
    
    //! Enable/Disable delays "inside transaction" according to weights 
    rand bit enItDelay;     
         int itDelayEn_wt  = 1; 
         int itDelayDi_wt  = 3;
    
    //! Value of delay "inside transaction" randomized inside boundaries  
    rand int itDelay;  
         int itDelayLow    = 0;
         int itDelayHigh   = 3;
    
    //! Constraints for randomized values 
    constraint cDelays {
      enBtDelay dist { 1'b1 := btDelayEn_wt,
                       1'b0 := btDelayDi_wt
                     };

      btDelay inside {
                      [btDelayLow:btDelayHigh]
                     };

      enItDelay dist { 1'b1 := itDelayEn_wt,
                       1'b0 := itDelayDi_wt
                     };
                     
      itDelay inside {
                       [itDelayLow:itDelayHigh]
                     };               
    }
    
   /*
    * Public Class Methods
    */
    
   /*!
    * Constructor - creates generator object 
    *
    * \param fl  - input FrameLink interface
    */           
    function new (virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) fl);
      this.fl = fl; //! Store pointer interface 
    endfunction: new 
   
   /*!
    * Randomize rand variables
    */
   task randomizeVar();
     assert(randomize());  
   endtask : randomizeVar 
    
   /*!
    * Random wait between transactions.
    */
    task randomWaitBt();
      if (enBtDelay)
        repeat (btDelay) @(fl.cb);
    endtask : randomWaitBt
    
   /*!
    * Random wait inside transaction (Sets SRC_RDY_N to 1)
    */    
    task randomWaitIt();
      if (enItDelay)
        repeat (itDelay) begin
          fl.cb.SRC_RDY_N <= 1;
          @(fl.cb); 
        end
      fl.cb.SRC_RDY_N <= 0;
    endtask : randomWait