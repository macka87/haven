/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Software Simple FrameLink Responder Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         12.5.2011 
 * ************************************************************************** */

/*!
 * This class is responsible for random intra- and intertransaction's dealys. 
 * Unit must be enabled by "setEnable()" function call. Random delaying can be
 * stoped by "setDisable()" function call.
 * 
 * \param pDataWidth - width of transaction data
 * \param pDremWidth - drem width  
 */
 class FrameLinkResponderSimple #(int pDataWidth=32, int pDremWidth=2);
    
   /*
    * Public Class Atributes
    */
    string  inst;             //! Responder identification
    byte    id;               //! Responder identification number
    bit     enabled;          //! Responder is enabled
    bit     busy;             //! Responder is running
    mailbox #(logic) dstMbx;  //! Mailbox for generated values
       
    virtual iFrameLinkTx.tb #(pDataWidth,pDremWidth) fl;
    
    LFSR_1 #(8) dstGenerator;
        
    //! delay constraints 
    
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
      
      logic [7:0] seed;
      logic [7:0] polynomial;
     
      this.enabled     = 0;     //! Responder is disabled by default  
      this.busy        = 0;     //! Responder is not busy by default  
      this.fl          = fl;    //! Store pointer interface 
      this.inst        = inst;  //! Store responder identifier
      this.id          = id;    //! Store responder identification number  
      
      fl.cb.DST_RDY_N <= 1;     //! Ready ONLY IF enabled
      
      dstMbx     = new(1);
      seed       = 8'hff;
      polynomial = 8'h8e;
            
      //! Create generator
      dstGenerator = new("Destination Ready Generator", dstMbx, seed, polynomial);
    endfunction
    
   /*! 
    * Enable Responder - eable responder and runs responder process
    */
    task setEnabled();
      enabled = 1;  //! Responder Enabling    
      fork  
        dstGenerator.setEnabled();  
        run();      //! Creating responder subprocess
      join_none;    //! Don't wait for ending
    endtask : setEnabled
        
   /*! 
    * Disable Driver
    */
    task setDisabled();
      enabled = 0;  //! Disable responder, after receiving last transaction
      dstGenerator.setDisabled(); 
    endtask : setDisabled 
    
   /*
    * Private Class Methods
    */
    
   /*!
    * Run Responder 
    */
    task run();
      logic dst;
    
      while (enabled) begin
        dstMbx.get(dst);
        fl.cb.DST_RDY_N <= dst;  //! destination ready active for one cycle
        @(fl.cb);
      end
      fl.cb.DST_RDY_N <= 1;
    endtask : run
 endclass: FrameLinkResponderSimple
