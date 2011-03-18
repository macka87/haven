/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Software FrameLink Monitor Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
/*!
 * This class is responsible for creating transaction objects from 
 * FrameLink interface signals. After is transaction received it is sended
 * by callback to scoreboard. Unit must be enabled by "setEnable()" function
 * call. Monitoring can be stoped by "setDisable()" function call.
 *
 * \param pDataWidth - width of transaction data
 * \param pDremWidth - drem width   
 */
 class FrameLinkMonitor #(int pDataWidth=32, int pDremWidth=2)
       extends Monitor;
    
   /*
    * Public Class Atributes
    */
    //! FrameLink interface
    virtual iFrameLinkTx.monitor #(pDataWidth,pDremWidth) fl;
    
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
                  virtual iFrameLinkTx.monitor #(pDataWidth,pDremWidth) fl
                  );
                  
      super.new(inst, id);
      this.fl = fl;  //! Store pointer interface 
    endfunction

   /*
    * Private Class Methods
    */
    
   /*! 
    * Run Monitor - receives transactions and sends them for processing by 
    * callback.
    */
    task run();
      FrameLinkTransaction transaction; 
      Transaction tr;

      while (enabled) begin              
        transaction = new();             
        $cast(tr, transaction);

        foreach (cbs[i])                 //! Call transaction preprocesing
          cbs[i].pre_tr(tr, id);       

        receiveTransaction(transaction); //! Receive Transaction
        transaction.display(inst);
        
        // Necessary for not calling callback after monitor disabling
        if (!enabled) break;

        #(0); // Necessary for not calling callback before driver
        
        foreach (cbs[i])                 //! Call transaction postprocesing
          cbs[i].post_tr(tr, id);

        busy = 0;                        //! Monitor is not busy now
      end
    endtask : run
    
   /*!
    * Receives FrameLink Transaction from interface
    *     
    * \param tr - FrameLink transaction
    */
    task receiveTransaction(FrameLinkTransaction tr);
      int packet_no=0;
      int byte_no, inLastWord;
      byte unsigned aux[];
      
      waitForSOF();  //! Wait for Start of Frame (SOF) 
      busy = 1;      //! Monitor is receiving transaction
                                                
      //! processes all frame parts 
      do begin 
        byte_no=0;     //! Byte offset in packet
        waitForSOP();  //! Wait for Start of Part (SOP)
    
        //! processes all bytes in frame part until detects End of Packet (EOP)
        do begin
          if (fl.monitor_cb.EOP_N || fl.monitor_cb.SRC_RDY_N) begin              
            if (fl.monitor_cb.SRC_RDY_N == 0 && 
                fl.monitor_cb.DST_RDY_N == 0) begin
              for (int i=0; i<pDataWidth/8; i++) begin
                logic [7:0] wbyte = 0;
                for (int j=0; j<8; j++)
                  wbyte[j] = fl.monitor_cb.DATA[i*8 + j];
                aux=new[byte_no+1](aux);    
                aux[byte_no] = wbyte;
                byte_no++;          
              end
            end              
            @(fl.monitor_cb);
          end
        end while (fl.monitor_cb.EOP_N || fl.monitor_cb.SRC_RDY_N); 
        
        //! last word in frame part 
        waitForDstRdy();

        if (pDremWidth!=0) inLastWord = fl.monitor_cb.DREM;
        else inLastWord = 0;

        for (int i=0; i<=inLastWord; i++) begin
          logic [7:0] wbyte = 0;
          for (int j=0; j<8; j++)
            wbyte[j] = fl.monitor_cb.DATA[i*8 + j]; 
          aux=new[byte_no+1](aux);  
          aux[byte_no] = wbyte;
          byte_no++;    
        end

        //! stores received data into FrameLink transaction 
        tr.frameParts = packet_no+1;       
        tr.data = new[tr.frameParts](tr.data);
        tr.data[tr.data.size-1] = new[aux.size];
        tr.data[tr.frameParts-1] = aux;
        
        //! detects End of Frame (EOF)
        if (fl.monitor_cb.EOF_N || fl.monitor_cb.SRC_RDY_N) begin
          @(fl.monitor_cb);
          packet_no++;
        end
        else break;                                 
      end while (1);
      
      @(fl.monitor_cb);
    endtask : receiveTransaction
    
   /*!
    * Wait for Start of Frame (SOF)
    */
    task waitForSOF();
      do begin
        if (fl.monitor_cb.SOF_N || fl.monitor_cb.SRC_RDY_N || 
            fl.monitor_cb.DST_RDY_N)
          @(fl.monitor_cb);
        if (!enabled) return;
      end while (fl.monitor_cb.SOF_N || fl.monitor_cb.SRC_RDY_N || 
                 fl.monitor_cb.DST_RDY_N); 
    endtask : waitForSOF
  
   /*!
    * Wait for Start of Part (SOP)
    */  
    task waitForSOP();
      do begin
        if (fl.monitor_cb.SOP_N || fl.monitor_cb.SRC_RDY_N || 
            fl.monitor_cb.DST_RDY_N)
          @(fl.monitor_cb);
      end while (fl.monitor_cb.SOP_N || fl.monitor_cb.SRC_RDY_N || 
                 fl.monitor_cb.DST_RDY_N);
    endtask : waitForSOP
    
   /*!
    * Wait for destination ready (DST_RDY_N)
    */
    task waitForDstRdy();
      do begin
        if (fl.monitor_cb.DST_RDY_N || fl.monitor_cb.SRC_RDY_N)
          @(fl.monitor_cb);
      end while (fl.monitor_cb.DST_RDY_N || fl.monitor_cb.SRC_RDY_N); 
    endtask : waitForDstRdy
 endclass : FrameLinkMonitor    
