/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    FrameLink Driver Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** * 

/*!
 * This class is responsible for generating signals to FrameLink
 * interface. Transactions are received by 'transMbx'(Mailbox) property.
 * Unit must be enabled by "setEnable()" function call. Unit can be
 * stoped by "setDisable()" function call. You can send your custom
 * transaction by calling "sendTransaction" function.
 *
 * \param pDataWidth - width of transaction data
 * \param pDremWidth - drem width   
 */
 class FrameLinkDriver #(int pDataWidth=32, int pDremWidth=2);

   /*
    * Public Class Atributes
    */
    string    inst;      //! Driver identification
    bit       enabled;   //! Driver is enabled
    bit       busy;      //! Driver is sending transaction
    tTransMbx transMbx;  //! Transaction mailbox
    
    //! FrameLink interface
    virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) fl;
    
   /*
    * Public Class Methods
    */

   /*!
    * Constructor - creates driver object 
    *
    * \param inst     - driver instance name
    * \param transMbx - transaction mailbox   
    * \param fl       - inoput FrameLink interface
    */           
    function new (string inst, 
                  tTransMbx transMbx, 
                  virtual iFrameLinkRx.tb #(pDataWidth,pDremWidth) fl
                  ); 
      this.enabled     = 0;         //! Driver is disabled by default
      this.busy        = 0;         //! Driver is not busy by default   
      this.fl          = fl;        //! Store pointer interface 
      this.transMbx    = transMbx;  //! Store pointer to mailbox
      this.inst        = inst;      //! Store driver identifier
      
      this.fl.cb.DATA      <= 0;
      this.fl.cb.DREM      <= 0;
      this.fl.cb.SOF_N     <= 1;
      this.fl.cb.EOF_N     <= 1;
      this.fl.cb.SOP_N     <= 1;
      this.fl.cb.EOP_N     <= 1;
      this.fl.cb.SRC_RDY_N <= 1;
    endfunction: new  
    
   /*! 
    * Enable Driver - eable driver and runs driver process
    */
    task setEnabled();
      enabled = 1;  //! Driver Enabling
      fork         
        run();      //! Creating driver subprocess
      join_none;    //! Don't wait for ending
    endtask : setEnabled
        
   /*! 
    * Disable Driver
    */
    task setDisabled();
      enabled = 0;  //! Disable driver, after sending last transaction it ends
    endtask : setDisabled
    
   /*! 
    * Send Transaction - sends transaction to input FrameLink interface
    *
    * \param transaction - transaction from generator or direct transaction
    */
    task sendTransaction(FrameLinkTransaction transaction);
      
      //! Driver is sending transaction
      busy = 1;
      
      //! Delay between transactions
      if (transaction.enBtDelay) repeat (transaction.btDelay) @(fl.cb);

      //! Send transaction
      sendData(transaction);
      
      //! Set not ready 
      fl.cb.SRC_RDY_N <= 1;
    
      //! Driver is not sending transaction
      busy = 0;
    endtask : sendTransaction
    
   /*
    * Private Class Methods
    */
    
   /*! 
    * Run Driver - takes transactions from mailbox and sends it to interface
    */  
    task run();
      FrameLinkTransaction transaction;
      Transaction to;
      int wordsNum = 0;
            
      @(fl.cb);                        //! Wait for clock
      
      while (enabled) begin            //! Repeat while enabled
        $write("som v driveri\n");
        transMbx.get(to);              //! Get transaction from mailbox 
        $cast(transaction,to);   
        sendTransaction(transaction);  //! Send transaction
        transaction.display(inst);   //! Display transaction
      end
    endtask : run
    
   /*!
    * Wait for accept - waits for accepting of general bits word of transaction
    */      
    task waitForAccept();
      while (fl.cb.DST_RDY_N) begin
        @(fl.cb);
      end;
    endtask : waitForAccept
    
   /*!
    * Random wait after every transaction word (Sets SRC_RDY_N to 1)
    */    
    task randomWait(FrameLinkTransaction tr, int part, int counter);
      if (tr.enItDelay)
        repeat (tr.itDelay[part][counter]) begin
          fl.cb.SRC_RDY_N <= 1;
          @(fl.cb); 
        end
      fl.cb.SRC_RDY_N <= 0;
    endtask : randomWait 
        
   /*!
    * Send transaction data 
    * 
    * \param tr - FrameLink transaction
    */                 
    task sendData(FrameLinkTransaction tr);
      int m = 0;
      int counter = 0;
      logic[pDataWidth-1:0] dataToSend = 0;
      
      //! for all frame parts 
      for (int i=0; i < tr.frameParts; i++) begin              
        //! for all bytes in frame part
        for (int j=0; j < tr.data[i].size; j++) begin 
          //! set SOP a SOF
          if (j<pDataWidth/8) begin
            fl.cb.SOP_N <= 0;           //! set Start of Part
            if (i==0) fl.cb.SOF_N <=0;  //! set Start of Frame
          end

          //! set one data byte
          for (int k=0; k < 8; k++) 
            dataToSend[m++] = tr.data[i][j][k];
                  
          //! last byte in frame part
          if (j==tr.data[i].size-1) begin  //! last byte of frame part
            fl.cb.EOP_N<=0;                //! set End Of Part
            if (i==tr.frameParts-1)        //! last byte of frame
              fl.cb.EOF_N<=0;              //! set End of Frame

            //! set REM signal
            if (tr.data[i].size%(pDataWidth/8) == 0)
              fl.cb.DREM <= (pDataWidth/8)-1;
            else
              fl.cb.DREM <= (tr.data[i].size%(pDataWidth/8))-1;

            m=pDataWidth;
          end

          //! when data word is ready to send
          if (m==pDataWidth) begin
            fl.cb.DATA <= dataToSend;
            randomWait(tr, i, counter);  //! create not ready
            counter++;
            @(fl.cb);                    //! send data
            waitForAccept();             //! wait until oposite side set ready

            //! init for sending next data word
            fl.cb.SOF_N<=1;       
            fl.cb.SOP_N<=1;
            fl.cb.EOP_N<=1;
            fl.cb.EOF_N<=1;
            dataToSend = 0;
            m=0;
          end
        end
      end
    endtask : sendData
 endclass : FrameLinkDriver 

