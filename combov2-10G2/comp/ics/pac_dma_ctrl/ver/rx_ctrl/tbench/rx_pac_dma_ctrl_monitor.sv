/*
 * rx_pac_dma_ctrl_monitor.sv: RX DMA Controller Monitor
 * Copyright (C) 2009 CESNET
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
 * $Id: rx_pac_dma_ctrl_monitor.sv 9322 2009-07-10 13:27:44Z xsimko03 $
 *
 * TODO:
 *
 */
 
  import sv_rx_pac_dma_ctrl_pkg::*;
  import sv_fl_pkg::*;
 
  // --------------------------------------------------------------------------
  // -- RX DMA Controller Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for receiving transaction objects from 
   * Frame Link interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class RxDmaCtrlMonitor #(int pNumFlags=8, pDataWidth=64, int pCtrlDmaDataWidth = 16, 
                           int pFlows = 2, int pRamSize = 1024, int pDmaTag = 0, 
                           int pTransType = 0);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string  inst;                            // Monitor identification
    bit     enabled;                         // Monitor is enabled
    MonitorCbs cbs[$];                       // Callbacks list
            
    RxDescManager #(pFlows,pRamSize) desc;                            // Descriptor Manager  
    RxIbusModul #(pDataWidth,pCtrlDmaDataWidth,pFlows,pRamSize,
                  pDmaTag,pTransType) ibus;                           // Internal Bus interface Modul
    RxStatusManager #(pFlows,pNumFlags) stat;                         // Status Manager  
    
    // -------------------
    // -- Class Methods --
    // -------------------
    
    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   RxDescManager #(pFlows,pRamSize) desc,
                   RxStatusManager #(pFlows,pNumFlags) stat,
                   RxIbusModul #(pDataWidth,pCtrlDmaDataWidth,pFlows,pRamSize,pDmaTag,pTransType) ibus
                  );
            
      this.enabled      = 0;           // Monitor is disabled by default   
      this.inst         = inst;        // Store driver identifier
      this.desc         = desc;        // Descriptor Doenload Manager 
      this.stat         = stat;        // Status Update Manager 
      this.ibus         = ibus;        // IB modul 
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
      Transaction trans;
      int flow = 0;
      string label;
      
      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        
        // Call transaction preprocesing, if is available
        foreach (cbs[i]) cbs[i].pre_rx(trans,label);

        // Detect non-empty status queue
        detectQueues(flow);
        
        // Pop information from statusQueue and receive transaction
        receiveTransaction(transaction,flow,stat.statusQueue[flow].pop_front());
         
        $swrite(label, "Monitor %0d", flow);  
               
        if (enabled) begin         
          $cast(trans,transaction);
          //trans.display(label);  
          #(0); // Necessary for not calling callback before driver
          
          // Call transaction postprocesing, if is available
          foreach (cbs[i]) cbs[i].post_rx(trans,label);
        end
      end
    endtask : run
    
    // -- Detect Queues --------------------------------------------------------
    // Detect if statusQueue[flow] is empty, else takes an entry from queue 
    task detectQueues(inout int flow);    
      while (!stat.detectState(flow)) begin
        @(stat.stat.statrx_cb);
        flow++;
        if (flow>pFlows) flow=0;
      end
    endtask : detectQueues
    
    // -- Receive Transaction --------------------------------------------------
    // It receives SW RX Buffer transaction to tr object
    task receiveTransaction(inout FrameLinkTransaction tr, input int ifcNo, 
                            logic[pNumFlags+16-1:0] flags_length);
      byte unsigned ram_data[];		// Data from address in RAM (pDataWidth size)
      byte unsigned ram_transaction[];  // Data from RAM (size from Status Update Manager)
      int address=0;			// Address in RAM
      int desc_flag=0;                  // Flag from descriptor manager
      int stat_flag=0;                  // Flag from status manager
      int length;                       // Real size of transaction
      int count;                        // Number of (pDataWidth/8) words in transaction
      logic[127:0] descriptor;          // descriptor
      
      ram_data = new[pDataWidth/8];     // One word of received data
      
      // Size of transaction from Status Update Manager in Bytes
      length = flags_length[15:0];
      // Flags from Status Update Manager
      stat_flag = flags_length[pNumFlags+16-1:16];
      
      ram_transaction = new[length];
      count=length/(pDataWidth/8);
      if((length%(pDataWidth/8))>0) count++;
            
      // Transaction address in RAM from MonitorQueue 
      desc.readMonitorQueue(descriptor,ifcNo);
      // Flags from Descriptor Manager
      desc_flag=descriptor[63:32];
      
      //Check Flags from Descriptor Manager and from Status Manager
      assert (desc_flag==stat_flag) 
      else $error("Error in flags!  desc_flag :  %d, stat_flag :  %d\n",desc_flag,stat_flag);
      
      // Address of transaction in RAM from Descriptor Manager
      address=descriptor[127:64]/(pDataWidth/8);
      //$write("MONITOR: ADDRESS RAM:  %d\n",address);
      
      for(int i=0;i<count;i++) begin
        // get Data from RAM  
        ibus.getData(address++,ram_data);
        //$write("MONITOR: Citane data z RAM:  %x  adresa:  %d\n",ram_data, address);
        
        // RAM transaction
        for(int j=0; j<(pDataWidth/8);j++) 
          ram_transaction[i*(pDataWidth/8)+j]=ram_data[j];
      end  
      
      // Prepare transaction for data store
        tr             = new();
        tr.packetCount = 1;
        tr.data        = new[tr.packetCount];
        tr.data[0]     = new[length];
        
        //$write("MONITOR: ram_transaction:  %x\n",ram_transaction);
        for (int j=0; j<length; j++)
          tr.data[0][j] = ram_transaction[j];
   
    endtask : receiveTransaction
    
  endclass : RxDmaCtrlMonitor 
