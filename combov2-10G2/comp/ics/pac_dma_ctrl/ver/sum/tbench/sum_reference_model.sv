/*
 * sum_reference_model.sv: Reference Model for Status Update Manager
 * Copyright (C) 2009 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * 3. Neither the name of the Company nor the names of its contributors
 *    may be used to endorse or promote products derived from this
 *    software without specific prior written permission.
 *
 * This software is provided ``as is'', and any express or implied
 * warranties, including, but not limited to, the implied warranties of
 * merchantability and fitness for a particular purpose are disclaimed.
 * In no event shall the company or contributors be liable for any
 * direct, indirect, incidental, special, exemplary, or consequential
 * damages (including, but not limited to, procurement of substitute
 * goods or services; loss of use, data, or profits; or business
 * interruption) however caused and on any theory of liability, whether
 * in contract, strict liability, or tort (including negligence or
 * otherwise) arising in any way out of the use of this software, even
 * if advised of the possibility of such damage.
 *
 * $Id: sum_reference_model.sv 11736 2009-10-25 11:01:35Z xsanta06 $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- Status Update Manager Reference Model
  // --------------------------------------------------------------------------
  /* This class is responsible for checking Status Update Manager signals.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call.
   */
  class SumReferenceModel #(int pFlows = 2, int pBlockSize = 4, 
                            int pIbDataSize = 64, int pRxDataSize = 24, 
                            int pTxDataSize = 8, int pCtrlDmaDataWidth = 32);
    
    // -----------------------------
    // -- Private Class Atributes --
    // -----------------------------
    string    inst;                          // Model identification
    bit       enabled;                       // Model is enabled
    virtual iSu.su_tb #(pFlows, pRxDataSize)       rxSu;
    virtual iSu.su_tb #(pFlows, pTxDataSize)       txSu;
    virtual iSum.misc_tb #(pFlows, pBlockSize)     misc;
    virtual iInternalBus.ib_read_tb #(pIbDataSize) ib;
    virtual iMi32.tb                               mi; 
    virtual iDmaCtrl.dma_tb #(pCtrlDmaDataWidth)   dma;

    SumTimeoutModule #(pFlows) timeoutModule;   // Timeout Module

    bit txInt[pFlows];
    int rxUpdateCounter[pFlows];
    int rxReqQue[$];
    int rxHwCounter[pFlows];
    int rxSwCounter[pFlows];
    int timeoutReg[2*pFlows];
    int timeoutCounter[2*pFlows];
    bit timeoutSet[2*pFlows];
    bit timeoutExpired[2*pFlows];
    bit suUpdate[2*pFlows];
    bit dmaReqAllowed[2*pFlows];
    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create Status Update Driver object 
    function new ( string inst, 
                   SumTimeoutModule #(pFlows)            timeoutModule,
                   virtual iSu.su_tb #(pFlows, pRxDataSize)       rxSu,
                   virtual iSu.su_tb #(pFlows, pTxDataSize)       txSu,
                   virtual iSum.misc_tb #(pFlows, pBlockSize)     misc,
                   virtual iInternalBus.ib_read_tb #(pIbDataSize) ib,
                   virtual iMi32.tb                               mi, 
                   virtual iDmaCtrl.dma_tb #(pCtrlDmaDataWidth)   dma
                   );      
      this.enabled     = 0;            // Driver is disabled by default
      this.timeoutModule = timeoutModule; // Store pointer to timeout module
      this.inst        = inst;         // Store driver identifier
      this.rxSu        = rxSu;         // Store pointer interface 
      this.txSu        = txSu;         // Store pointer interface 
      this.misc        = misc;         // Store pointer interface 
      this.ib          = ib;           // Store pointer interface 
      this.mi          = mi;           // Store pointer interface 
      this.dma         = dma;          // Store pointer interface 
      
      foreach(txInt[i]) begin
        txInt[i]           = 0;
        rxUpdateCounter[i] = 0;
        rxHwCounter[i]     = 0;
        rxSwCounter[i]     = 0;
      end  

      foreach(timeoutReg[i]) begin
        timeoutReg[i]     = 0;
        timeoutCounter[i] = 0;
        timeoutSet[i]     = 0;
        timeoutExpired[i] = 0;
        suUpdate[i]       = 0;
        dmaReqAllowed[i]  = 0;
      end  
            
    endfunction: new          
    
    // -- Enable Modul --------------------------------------------------------
    // Enable Modul and run Modul process
    task setEnabled();
      enabled = 1; // Modul Enabling
      fork         
        checkInterrupt();        // Creating modul subprocess
        checkRxIdle();           // Creating modul subprocess
        checkDma();              // Creating modul subprocess
        checkInterruptWithDone();// Creating modul subprocess
      join_none;    // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Modul -------------------------------------------------------
    // Disable Modul
    task setDisabled();
      enabled = 0; // Modul Disabling
    endtask : setDisabled
  
    // -- Check Interrupt -----------------------------------------------------
    // Check if INTERRUPT is properly set when not IB RD_SRC_RDY
    task checkInterrupt();
      bit timeoutReset[2*pFlows];
      bit txIntFlag = 0;
      int flow;

      while (enabled) begin            // Repeat while enabled
        txIntFlag = 0;
        foreach(timeoutReset[i])
          timeoutReset[i] = 0;

        // Check TX interrupt flag
        // Set internal int flag to set interrupt next clock cycle 
        if (txSu.su_cb.SU_DVLD && txSu.su_cb.SU_DATA[0]==1)begin
          txIntFlag = 1;
          flow = txSu.su_cb.SU_ADDR;
        end  

        // Check appropriate interrupt signal
        if (ib.ib_read_cb.RD_REQ)
          for(int i=0; i<pFlows; i++) begin
            if (ib.ib_read_cb.RD_ADDR==(32'h1000+(i/2)*8)) begin
              fork
                automatic int j=i;
                checkTxInt(j);
              join_none;
            end  
            else if (ib.ib_read_cb.RD_ADDR[31:12]==2*i) begin
              fork
                automatic int j=i;
                checkRxInt(j);
              join_none;
            end  
          end    

        // If not IB RD_SRC_RDY, Interrupt is 0
        if(ib.ib_read_cb.RD_SRC_RDY==0 && dma.dma_cb.DMA_DONE==0)
          for(int i=0; i<2*pFlows; i++)
            // If timeout expired for RX flow there will be interrupt
            if(i%2!=0 || timeoutExpired[i]==0) begin
              assert(misc.misc_cb.INTERRUPT[i]==0)
              else $error("INTERRUPT[%0d] is active without RD_SRC_RDY or DMA_DONE",i);
          end  

        // Reset timeout expired if interrupt at next clock cycle
        foreach(timeoutExpired[i])
          if(timeoutExpired[i] && misc.misc_cb.INTERRUPT[i]==1) begin
            timeoutReset[i]=1;
            timeoutModule.setNewTimeout(i);
          end  

        @(txSu.su_cb);      

        // TX INTF occured, interrupt is valid next clock cycle
        if (txIntFlag) 
          txInt[flow] = 1;

        // Reset timeout expired if at next clock cycle
        foreach(timeoutExpired[i])
          if(timeoutReset[i])
            timeoutExpired[i]=0;

      end
    endtask : checkInterrupt
        
    // -- Check TX Int --------------------------------------------------------
    // Check if TX interrupt is properly set when IB RD_SRC_RDY
    task checkTxInt(int flow);
      @(ib.ib_read_cb);

      // Wait for RD_SRC_RDY
      while (ib.ib_read_cb.RD_SRC_RDY==0) @(ib.ib_read_cb);

      // There was TX update with interrupt flag
      if(txInt[flow]==1) begin
        assert(misc.misc_cb.INTERRUPT[2*flow+1])
        else $error("INTERRUPT[%0d] is not active when exporting counter status",2*flow+1);
        txInt[flow] = 0;
      end  
      // There wasn't TX update with interrupt flag
      else if(dma.dma_cb.DMA_DONE==0) begin
        assert(misc.misc_cb.INTERRUPT[2*flow+1]==0)
        else $error("INTERRUPT[%0d] is active when exporting counter status",2*flow+1);
      end  
    endtask : checkTxInt

    // -- Check RX Int --------------------------------------------------------
    // Check if RX interrupt is properly set when IB RD_SRC_RDY
    task checkRxInt(int flow);
      logic[2*pFlows-1:0] interrupt = 0;
      bit rxTimeoutExpired = 0;

      @(ib.ib_read_cb);

      // Wait for RD_SRC_RDY
      while (ib.ib_read_cb.RD_SRC_RDY==0) @(ib.ib_read_cb);

      for(int i=0; i<2*pFlows; i+=2)
        if (timeoutExpired[i])
          rxTimeoutExpired = 1;

      // There is RX update with interrupt flag
      if(ib.ib_read_cb.RD_DATA[32]==1) begin
        assert(misc.misc_cb.INTERRUPT[2*flow])
        else $error("INTERRUPT[%0d] is not active when exporting RX update with INTF",2*flow);
      end  
      // There isn't RX update with interrupt flag
      // Do not check if DMA DONE or expired timeout for any RX flow
      else if((dma.dma_cb.DMA_DONE==0) && (rxTimeoutExpired==0)) begin
        assert(misc.misc_cb.INTERRUPT==interrupt)
        else $error("INTERRUPT is active when exporting RX update without INTF");
      end  
    endtask : checkRxInt


    // -- Check RX Idle -------------------------------------------------------
    // Check for incomming RX updates
    task checkRxIdle();

      // Run Idle check subprocesses
      fork
        checkRxSu();
        checkRxIbReq();
        checkRxIbSrcRdy();
      join_none

      while (enabled) begin
        // Check correct RX IDLE setting
        for(int i=0; i<pFlows; i++)
          if(rxUpdateCounter[i]==0) begin
            assert(misc.misc_cb.IDLE[2*i]==1)
            else $error("IDLE[%0d] is not active after exporting all RX updates",2*i);
          end  

        @(rxSu.su_cb);
      end  
    endtask : checkRxIdle

    // -- Check RX IB SRC RDY -------------------------------------------------
    // Check for outcomming RX updates
    task checkRxIbSrcRdy();
      int req=0;
      int flow;

      while(enabled) begin
        while(rxReqQue.size()==0) @(ib.ib_read_cb);

        // Wait for RD_SRC_RDY
        while (ib.ib_read_cb.RD_SRC_RDY==0) @(ib.ib_read_cb);

        // Decrement RX Update counter
        flow = rxReqQue.pop_front();
        rxUpdateCounter[flow]--;

        @(ib.ib_read_cb);

        // Wait for RD_SRC_RDY
        while (ib.ib_read_cb.RD_SRC_RDY==0) @(ib.ib_read_cb);

        flow = rxReqQue.pop_front();
        rxHwCounter[flow]++;

        @(ib.ib_read_cb);
      end  

    endtask : checkRxIbSrcRdy
    
    // -- Check RX SU ---------------------------------------------------------
    // Check for incomming RX updates
    task checkRxSu();
      while (enabled) begin
        // Increment RX Update counter
        if (rxSu.su_cb.SU_DVLD)
          rxUpdateCounter[rxSu.su_cb.SU_ADDR]++;

        @(rxSu.su_cb);
      end  
    endtask : checkRxSu

    // -- Check RX IB REQ -----------------------------------------------------
    // Parse addresses of IB read requests
    task checkRxIbReq();
      while (enabled) begin
        // Add flow number into queue
        if(ib.ib_read_cb.RD_REQ)
          if(ib.ib_read_cb.RD_ADDR[31:12]!=1)
            rxReqQue.push_back(ib.ib_read_cb.RD_ADDR[31:12]/2);

        @(ib.ib_read_cb);
      end  
    endtask : checkRxIbReq

    // -- Check DMA Requests -----------------------------------------------
    // Check setting timeouts, incomming SU updates and DMA requests
    task checkDma();
      bit dmaReq = 0;
      bit txSuUpdate = 0;
      bit timeoutExpiredFlag[2*pFlows];

      while (enabled) begin
        // Set timeout
        if (mi.cb.WR && mi.cb.ADDR[5:0]=='h10) begin
          timeoutReg[mi.cb.ADDR[31:6]] = mi.cb.DWR;
          timeoutCounter[mi.cb.ADDR[31:6]] = 0;
          timeoutSet[mi.cb.ADDR[31:6]] = 1;
//          $write("TIMEOUT SETTED @%0t for flow %0d\n",$time,mi.cb.ADDR[31:6]);
        end  

        // Set SW counter
        if (mi.cb.WR && mi.cb.ADDR[5:0]=='h14) begin
          rxSwCounter[mi.cb.ADDR[31:6]/2] = mi.cb.DWR;
        end  

        // Reset counter if TX update occured
        if(txSu.su_cb.SU_DVLD) begin
          timeoutCounter[2*txSu.su_cb.SU_ADDR+1] = 0;
          suUpdate[2*txSu.su_cb.SU_ADDR+1]=1;
          // Update includes interrupt flag
          if (txSu.su_cb.SU_DATA[0]==1)
            dmaReqAllowed[2*txSu.su_cb.SU_ADDR+1] = 1;
        end    

        // Reset counter if RX update occured
        if(rxSu.su_cb.SU_DVLD) begin
          timeoutCounter[2*rxSu.su_cb.SU_ADDR] = 0;
          suUpdate[2*rxSu.su_cb.SU_ADDR] = 1;
        end    

        // Check if timeout expired
        foreach(timeoutSet[i])
          if(timeoutSet[i] && (timeoutCounter[i]==timeoutReg[i])) begin
            // Allow TX DMA Request if there was update for any TX ifc
            if(i%2 == 1) begin
              for(int j=1; j<2*pFlows; j+=2)
                if (suUpdate[j]) txSuUpdate = 1;
            end
            if (suUpdate[i] || txSuUpdate) begin
              dmaReqAllowed[i]=1;
              timeoutSet[i]=0;
              suUpdate[i]=0;
              timeoutExpiredFlag[i]=1;
            end
            // RX HW and SW Counter does not match
            if((i%2 == 0) && (rxHwCounter[i/2]!=rxSwCounter[i/2])) begin
              timeoutSet[i]=0;
              timeoutExpiredFlag[i]=1;
//              $write("HW counter[%0d]=%0d\n",i,rxHwCounter[i/2]);
//              $write("SW counter[%0d]=%0d\n",i,rxSwCounter[i/2]);
            end
//            $info("TIMEOUT EXPIRED for flow %0d, %0b\n",i,timeoutExpired[i]);
            txSuUpdate = 0;
          end

        // Check FLUSH
        foreach(suUpdate[i])
          if(misc.misc_cb.FLUSH[i] && suUpdate[i]) begin
            dmaReqAllowed[i]=1;
            suUpdate[i]=0;
          end
        
        // Check if DMA request is legal
        if(dma.dma_cb.DMA_REQ) begin
          @(rxSu.su_cb);
          if(dma.dma_cb.DMA_DOUT[27:18]==1) begin
            dmaReq = 0;
            for(int i=1; i<2*pFlows;i+=2) begin
              if(dmaReqAllowed[i]) dmaReq=1;
              dmaReqAllowed[i]=0;
            end
            assert(dmaReq)
            else $error("Illegal TX DMA Request");
          end
        end
        else @(rxSu.su_cb);
        
        // Set timeout expired at next clock cycle
        foreach(timeoutExpiredFlag[i])begin
          if(timeoutExpiredFlag[i])
            timeoutExpired[i] = 1;
          timeoutExpiredFlag[i] = 0;
        end  

        // Increment timeout counters
        foreach(timeoutCounter[i])
          if(timeoutSet[i]) timeoutCounter[i]++;
      end  
    endtask : checkDma

    // -- Check INTERRUPT with DMA DONE ---------------------------------------
    // Check setting INTERRUPT signal when timeout expire
    task checkInterruptWithDone();
      bit expired;
      bit expiredFlag;

      while (enabled) begin
        expired = 0;
        expiredFlag = 0;

        // Check if timeout expired
        foreach(timeoutExpired[i])
          if (timeoutExpired[i]) expiredFlag = 1;

        if(expired) begin
          // Wait for DMA DONE
          while(dma.dma_cb.DMA_DONE==0) @(dma.dma_cb);

          // Check setting INTERRUPT signal
          if(dma.dma_cb.DMA_TAG[15:2]==1)
            for(int i=1; i<2*pFlows; i+=2) begin
              if(timeoutExpired[i] && misc.misc_cb.FLUSH[i]==0) begin
//                $write("Timeout expired for flow:%0d\n",i);
                assert(misc.misc_cb.INTERRUPT[i]==1)
                else $error("INTERRUPT[%0d] is not active with DMA_DONE when timeout expired",i);
                timeoutExpired[i]=0;
              end
            end  
        end

        @(dma.dma_cb);

        // Set expired at next clock cycle
        if(expiredFlag)
          expired = 1;
      end  
    endtask : checkInterruptWithDone
endclass : SumReferenceModel 
