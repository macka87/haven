/*
 * au_monitor.sv: Align Unit Monitor
 * Copyright (C) 2008 CESNET
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
 * $Id: au_monitor.sv 3590 2008-07-16 09:05:59Z xsanta06 $
 *
 * TODO:
 *
 */
   
   import sv_au_pkg::*;
 
  // --------------------------------------------------------------------------
  // -- Align Unit Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from 
   * Frame Link interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class AlignUnitMonitor;
    
    // -- Private Class Atributes --
    string  inst;                            // Monitor identification
    bit     enabled;                         // Monitor is enabled
    MonitorCbs cbs[$];                       // Callbacks list
    virtual iAlignUnit.monitor monitor;
    tInfoQue tr_info;                   // List with transaction info
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iAlignUnit.monitor monitor,
                   tInfoQue tr_info
                   );
      this.enabled     = 0;           // Monitor is disabled by default   
      this.monitor     = monitor;          // Store pointer interface 
      this.inst        = inst;        // Store driver identifier
      this.tr_info     = tr_info;
      
    endfunction

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
      AlignUnitTransaction transaction; 
      Transaction tr;
      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        receiveTransaction(transaction); // Receive Transaction
//        transaction.display("MONITOR");
        #(0); // Necessary for not calling callback before driver
        if (enabled) begin
          $cast(tr, transaction);
          // Call transaction preprocesing, if is available
          foreach (cbs[i]) cbs[i].pre_rx(tr, inst);
          // Call transaction postprocesing, if is available
          foreach (cbs[i]) cbs[i].post_rx(tr, inst);
        end
      end
    endtask : run
    
    // -- Get Info ------------------------------------------------------------
    // Get info about transaction
    task getInfo(AlignUnitTransaction tr, output int dst_addr, data_len);
      tTransInfo info;
      
      tr_info.get(info);
      dst_addr = info.dstAddr;
      data_len = info.dataLen;
    endtask : getInfo
    
    // -- Wait for SOF --------------------------------------------------------
    // It waits until SOF and SRC_RDY
    task waitForSOF();  // Cekej dokud neni SOF A SRC RDY
      do begin
        if (!monitor.monitor_cb.OUT_SOF || !monitor.monitor_cb.OUT_SRC_RDY || !monitor.monitor_cb.OUT_DST_RDY)
          @(monitor.monitor_cb);
        if (!enabled) return;
      end while (!monitor.monitor_cb.OUT_SOF || !monitor.monitor_cb.OUT_SRC_RDY || !monitor.monitor_cb.OUT_DST_RDY); //Detect Start of Frame
    endtask : waitForSOF
    
    // -- Wait for DST_RDY ----------------------------------------------------
    // It waits until DST_RDY and SRC_RDY
    task waitForDstRdy(); // Cekej dokud neni DST_RDY A SRC RDY
      do begin
        if (!monitor.monitor_cb.OUT_SRC_RDY || !monitor.monitor_cb.OUT_DST_RDY)
          @(monitor.monitor_cb);
      end while (!monitor.monitor_cb.OUT_SRC_RDY || !monitor.monitor_cb.OUT_DST_RDY); //Detect Destination Ready
    endtask : waitForDstRdy
    
    // -- Receive Transaction -------------------------------------------------
    // It receives Frame Link transaction to tr object
    task receiveTransaction(AlignUnitTransaction tr);
      int byte_no=0, dst_addr, data_len, offset;
      byte unsigned aux[];
      byte unsigned dataToReceive[];
      
      // -------- Process Frame ----------- 
      waitForSOF(); // Wait for SOF
      getInfo(tr, dst_addr, data_len);  // Get info about expected transaction

      offset = (dst_addr+data_len)%8;
      
      // -------- Process data in packet (no last word)-----------
      do begin
        if (!monitor.monitor_cb.OUT_EOF || !monitor.monitor_cb.OUT_SRC_RDY) begin              
          if (monitor.monitor_cb.OUT_SRC_RDY && monitor.monitor_cb.OUT_DST_RDY) begin
            for (int i=dst_addr; i<8; i++) begin                   // Process one word from input
              logic [7:0] wbyte = 0;
              for (int j=0; j<8; j++)
                wbyte[j] = monitor.monitor_cb.OUT_DATA[i*8 + j];   // Process one byte
              aux=new[byte_no+1](aux);    
              aux[byte_no] = wbyte;
              byte_no++;
              dst_addr=0;          
            end
          end              
          @(monitor.monitor_cb);
        end
      end while (!monitor.monitor_cb.OUT_EOF || !monitor.monitor_cb.OUT_SRC_RDY); // Detect End of Frame
      
      
      // -------- Process data in packet (only last word)-----------
      waitForDstRdy();

      for (int i=0; i<offset; i++) begin
        logic [7:0] wbyte = 0;
        for (int j=0; j<8; j++)
          wbyte[j] = monitor.monitor_cb.OUT_DATA[i*8 + j];      // Process one byte
        aux=new[byte_no+1](aux);  
        aux[byte_no] = wbyte;
        byte_no++;    
      end
      
      // --------- Store received data into transaction -------------
      tr.data = new [aux.size];
      tr.data = aux;

    endtask : receiveTransaction
    
  endclass : AlignUnitMonitor    
