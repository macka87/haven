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
    string  inst;         //! Responder identification
    byte    id;           //! Responder identification number
    bit     enabled;      //! Responder is enabled
    bit     busy;         //! Responder is running
    mailbox #(logic [8:0]) btDelayMbx;  //! Mailbox for generated values
    mailbox #(logic [8:0]) itDelayMbx;  //! Mailbox for generated values
    
    virtual iFrameLinkTx.tb #(pDataWidth,pDremWidth) fl;
    
    LFSR #(9) btDelayGenerator;  //! LFSR generator for bt delays 
    LFSR #(9) itDelayGenerator;  //! LFSR generator for it delays 
    
    //! delay constraints 
    
    //! Delay between transactions limits
    logic [8:0] btDelayLow  = 0;
    logic [8:0] btDelayHigh = 3;
    
    //! Delay inside transactions limits
    logic [8:0] itDelayLow  = 0;
    logic [8:0] itDelayHigh = 3;
     
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
      
      logic [8:0][8:0] btseed;
      logic [8:0][8:0] itseed;
            
      this.enabled     = 0;     //! Responder is disabled by default  
      this.busy        = 0;     //! Responder is not busy by default  
      this.fl          = fl;    //! Store pointer interface 
      this.inst        = inst;  //! Store responder identifier
      this.id          = id;    //! Store responder identification number  
      
      fl.cb.DST_RDY_N <= 1;     //! Ready ONLY IF enabled
      
      btDelayMbx = new(1);
      itDelayMbx = new(1);
      
      btseed = {9'h1ff, 9'h1fe, 9'h1fc, 9'h1f8, 
                9'h1f0, 9'h1e0, 9'h1c0, 9'h180,
                9'h100}; 
      //!!! zatial rovnake potom treba zmenit !!!!           
      itseed = {9'h100, 9'h180, 9'h1c0, 9'h1e0, 
                9'h1f0, 9'h1f8, 9'h1fc, 9'h1fe,
                9'h1ff};    
                
      //! Create btDelay generator
      btDelayGenerator = new("BtDelay Generator", btDelayMbx, btseed, 9'h12c);
      itDelayGenerator = new("ItDelay Generator", itDelayMbx, itseed, 9'h12c);
    endfunction
    
   /*! 
    * Enable Responder - eable responder and runs responder process
    */
    task setEnabled();
      enabled = 1;  //! Responder Enabling    
      fork  
        btDelayGenerator.setEnabled();  
        itDelayGenerator.setEnabled();     
        run();      //! Creating responder subprocess
      join_none;    //! Don't wait for ending
    endtask : setEnabled
        
   /*! 
    * Disable Driver
    */
    task setDisabled();
      enabled = 0;  //! Disable responder, after receiving last transaction
      btDelayGenerator.setDisabled(); 
      itDelayGenerator.setDisabled(); 
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
        
        if (fl.cb.EOF_N == 0 && fl.cb.SRC_RDY_N == 0)   
          waitBtDelay();       //! between transaction delay
        if (fl.cb.EOF_N != 0 && fl.cb.EOP_N == 0 && fl.cb.SRC_RDY_N == 0)                                            
          waitItDelay();       //! inside transaction delay
        
        busy = 0;
      end
      fl.cb.DST_RDY_N <= 1;
    endtask : run
   
   /*!
    * Random wait between sending transactions (Set DST_RDY_N to 1)
    */ 
    task waitBtDelay();
      // between transaction delay from LFSR
      logic [8:0] btDelayFull; 
      logic enBtDelay;     
      logic [7:0] btDelay; 
      
      busy = 1;
      
      do begin
        btDelayMbx.get(btDelayFull);
        //$write("btDelayFull: %b\n", btDelayFull);
        enBtDelay = btDelayFull[8];    // 9. bit is enable bit
        btDelay   = btDelayFull[7:0];  // 8. - 7. bits represent delay 
        if (enBtDelay == 0) break;
      end while((btDelay>btDelayHigh) || (btDelay<btDelayLow));
      
      //$write("enBtDelay: %b\n", enBtDelay);
      //$write("btDelay: %b\n", btDelay);
      
      if (enBtDelay) begin
        repeat (btDelay) begin
          fl.cb.DST_RDY_N <= 1;
          @(fl.cb);
        end
      end  
    endtask : waitBtDelay
   
   /*!
    * Random wait during sending transaction (Set DST_RDY_N to 1)
    */     
    task waitItDelay();
      // inside transaction delay from LFSR
      logic [8:0] itDelayFull; 
      logic enItDelay;     
      logic [7:0] itDelay; 
      
      busy = 1;
      
      do begin
        itDelayMbx.get(itDelayFull);
        enItDelay = itDelayFull[8];    // 9. bit is enable bit
        itDelay   = itDelayFull[7:0];  // 8. - 7. bits represent delay 
        if (enItDelay == 0) break;
      end while((itDelay>itDelayHigh) || (itDelay<itDelayLow));
       
      //$write("enItDelay: %b\n", enItDelay);
      //$write("itDelay: %b\n", itDelay);
      
      if (enItDelay)
        repeat (itDelay) begin
          fl.cb.DST_RDY_N <= 1;
          @(fl.cb);
        end
    endtask : waitItDelay
 endclass: FrameLinkResponder
