/*
 * rx_dma_ctrl_monitor.sv: RX DMA Controller Monitor
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: rx_dma_ctrl_monitor.sv 12979 2010-02-26 16:13:08Z kastovsky $
 *
 * TODO:
 *
 */
 
  import sv_rx_dma_ctrl_pkg::*;
 
  // --------------------------------------------------------------------------
  // -- RX DMA Controller Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for receiving transaction objects from 
   * Frame Link interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class RxDmaCtrlMonitor #(int pDataWidth=64, int pCtrlDmaDataWidth = 16, 
                           int pFlows = 2, int pPageSize = 4096, int pPageCount = 3);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string  inst;                            // Monitor identification
    bit     enabled;                         // Monitor is enabled
    MonitorCbs cbs[$];                       // Callbacks list
    tTransInfoMbx transInfoMbx;              // Store info about header and body length from driver        
    tTransInfo  transInfoQue[$]; 
    
    RxSoftwareModul #(pFlows,pPageSize,pPageCount) swModul;                             // MI32 interface Modul
    RxIbusModul #(pDataWidth,pCtrlDmaDataWidth,pFlows,pPageSize,pPageCount) ibus;       // Internal Bus interface Modul

    virtual iMi32.tb mi32; 
  
    int startPtr[]     = new [pFlows];          // Start pointers for each flow
    int endPtr[]       = new [pFlows];          // End pointers for each flows 
    logic[63:0] base_for_pointer[]; 		// Base for Pointer - is used when data continues on another page
    logic[63:0] bound[];				// Boundary for each page
    logic[63:0] descriptor[];                   // Boundary for each flow  
    int pom;
    
    // -------------------
    // -- Class Methods --
    // -------------------
    
    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   RxIbusModul #(pDataWidth,pCtrlDmaDataWidth,pFlows,pPageSize,pPageCount) ibus,
                   virtual iMi32.tb mi32,
                   tTransInfoMbx transInfoMbx
                   );
      int pageSizeCounter = 0;
      
      this.enabled      = 0;           // Monitor is disabled by default   
      this.inst         = inst;        // Store driver identifier
      this.transInfoMbx = transInfoMbx;
      this.mi32         = mi32;
      this.ibus         = ibus;
     
      swModul = new("SwModul", mi32);
      
      // Base for Pointer Initialization
      base_for_pointer = new[pFlows];

      for(int i=0;i<pFlows;i++)
        base_for_pointer[i]=i*pPageSize;

      // Bond Initialization
      bound = new[pFlows];

      for(int i=0;i<pFlows;i++)
        bound[i]=i*pPageSize;

      // Descriptor Initialization
      descriptor = new[pFlows];
      pom=pFlows-1;
        
      for(int j=0; j<pFlows; j++)begin
        descriptor[j]=(pPageCount*pFlows-pom)*pPageSize;
        pom--;
      end
                
      // Initiate start and end pointer for each flow
      for(int i=0; i<pFlows; i++)begin
        startPtr[i] = 0;
        endPtr[i]   = 0;
      end
      
    endfunction : new

    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(MonitorCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks

    // -- Enable Monitor ------------------------------------------------------
    // Enable monitor and runs monitor process
    task setEnabled();
      enabled = 1; // Monitor Enabling
      fork         
        run();     // Creating monitor subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Monitor -----------------------------------------------------
    // Disable monitor
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
    endtask : setDisabled 
    
    // -- Run Monitor ---------------------------------------------------------
    // Receive transactions and send them for processing by call back
    task run();
      FrameLinkTransaction transaction; 
      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        detectEndPointerChange ();       // Receive Transaction
        #(0); // Necessary for not calling callback before driver
      end
    endtask : run
    
    // -- Detect change of SW End Pointer ------------------------------------- 
    task detectEndPointerChange();
      int start_data;
      int end_data;
      int i;
      int detect=0;
      int size;
      int count;

      // detect change of EndPointer 
      do begin
        for (i=0;i<pFlows;i++) begin
          swModul.getEndPtr(i, end_data);
          if (end_data!=endPtr[i]) begin
            //$write("Detekovaná zmena SWEndPointera!\n");
	    detect=1;
            break;
	  end
        end 
        if (detect==0) @(mi32.cb);
      end while(detect==0);
      
      // StartPointer is old EndPointer now       
      start_data=endPtr[i]; 
      
      swModul.setStrPtr(i, start_data);   // Send new StartPointer 
      endPtr[i]=end_data;                 // Set EndPointer 
      
      // count is number of Bytes that we need from RAM
      if(start_data>end_data) count = ((pPageCount*pPageSize)-start_data+end_data)/(pDataWidth/8);  
      else count =(end_data-start_data)/(pDataWidth/8);
      
      start_data=(start_data/(pDataWidth/8))+(base_for_pointer[i]/(pDataWidth/8));
      //$write("SWStartPointer: %d,  velkost citanych dat:  %d\n",start_data,count);    
      receiveTransaction(start_data,count,i);
        
    endtask : detectEndPointerChange
    
    // -- Receive Transaction -------------------------------------------------
    // It receives SW RX Buffer transaction to tr object
    task receiveTransaction(int start_data, int count, int ifcNo);
      tTransInfo transInfo;		// Informations about Size of FrameLink Transactions
      byte unsigned ram_data[];		// Data from address in RAM (pDataWidth size)
      byte unsigned ram_transaction[];  // Data from RAM (EndPointer-Startpointer size)
      FrameLinkTransaction tr;		// FrameLink Transaction
      Transaction trans;		// Transaction
      int address=0;			// Address in RAM
      int suma=0;
      int diff;
      int m=0;
      ram_data = new[pDataWidth/8];
      ram_transaction = new[count*pDataWidth/8];

      address=start_data;		// Address is StartPointer
      for(int i=0;i<count;i++) begin
        // Jump to another Page
        if (address+1==(descriptor[ifcNo]/(pDataWidth/8)))begin
	  base_for_pointer[ifcNo]=ifcNo*pPageSize;
          bound[ifcNo]=ifcNo*pPageSize;
        end
       
        // End of Flow, Address is in another Page
        else if (address==(descriptor[ifcNo]/(pDataWidth/8)))
          address=(bound[ifcNo]/(pDataWidth/8));
      
        // End of Page, Address is in another Page
        else if (address==((bound[ifcNo]+pPageSize)/(pDataWidth/8))) begin
          base_for_pointer[ifcNo]+=(pFlows-1)*pPageSize;
          bound[ifcNo]+=(pFlows*pPageSize);
          address=(bound[ifcNo]/(pDataWidth/8));
        end
       
        // get Data from RAM  
        //$write("Adresa pri citani z RAM:  %d\n",address);
        ibus.getData(address++,ram_data);
        //$write("Citane data z RAM:  %x\n",ram_data);
        
        // RAM transaction
        for(int j=0; j<(pDataWidth/8);j++) 
          ram_transaction[i*(pDataWidth/8)+j]=ram_data[j];
      end  

      // Copy info from mailbox to queue for easier manipulation
      while (transInfoMbx.num()!=0) begin
        transInfoMbx.get(transInfo);
        transInfoQue.push_back(transInfo);
      end
     
      do begin
        for (int j=0; j<transInfoQue.size; j++) begin
          if (transInfoQue[j].ifcNo == ifcNo) begin
            transInfo = transInfoQue[j];
            transInfoQue.delete(j);
            break;
          end 
        end

        suma=suma+transInfo.headerLen+transInfo.bodyLen;
        diff=suma%8;
        if (diff!=0) suma+=(8-diff);
      
        // Prepare transaction for data store
        tr             = new();
        tr.ifcNo       = ifcNo;
        tr.packetCount = 2;
        tr.data        = new[tr.packetCount];
        
        // --- Parse header -------------
        tr.data[0]     = new[transInfo.headerLen];
        
        for (int j=0; j<transInfo.headerLen; j++)
          tr.data[0][j] = ram_transaction[m++];
          
        // --- Parse body ---------------
        tr.data[1]     = new[transInfo.bodyLen];
        
        for (int j=0; j<transInfo.bodyLen; j++)
          tr.data[1][j] = ram_transaction[m++]; 
          
        //tr.display("MONITOR");
  
        if (enabled) begin 
          $cast(trans,tr);
          foreach (cbs[i]) cbs[i].pre_rx(trans,inst);
          foreach (cbs[i]) cbs[i].post_rx(trans,inst);
        end
   
        m=suma; 
      end while(count*(pDataWidth/8)>suma);
         
    endtask : receiveTransaction
    
  endclass : RxDmaCtrlMonitor 
