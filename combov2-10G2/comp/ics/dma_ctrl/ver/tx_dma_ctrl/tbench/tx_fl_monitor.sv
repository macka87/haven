/*
 * tx_fl_monitor.sv: FrameLink Monitor
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
 * $Id: tx_fl_monitor.sv 8584 2009-06-01 14:39:20Z xsimko03 $
 *
 * TODO:
 *
 */
 // ----------------------------------------------------------------------------
 //                        Package declaration
 // ----------------------------------------------------------------------------

   
  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from 
   * Frame Link interface signals. After is transaction received it is sended
   * by callback to processing units (typicaly scoreboard) Unit must be enabled
   * by "setEnable()" function call. Monitoring can be stoped by "setDisable()"
   * function call.
   */
  class FrameLinkMonitor #(int pDataWidth=64, int pDremWidth = 3, int pFlows = 4);
    
    // -- Private Class Atributes --
    string  inst;                            // Monitor identification
    int     ifcNo;                           // Actual interface number   
    bit     enabled;                         // Monitor is enabled
    MonitorCbs cbs[$];                       // Callbacks list
    virtual iFrameLinkTx.monitor #(pDataWidth,pDremWidth) fl;
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   int ifcNo,
                   virtual iFrameLinkTx.monitor #(pDataWidth,pDremWidth) fl
                   );
      this.enabled     = 0;           // Monitor is disabled by default 
      this.ifcNo       = ifcNo;  
      this.fl          = fl;          // Store pointer interface 
      this.inst        = inst;        // Store driver identifier
      
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
      FrameLinkTransaction transaction; 
      Transaction tr;
      while (enabled) begin              // Repeat in forewer loop
        transaction = new;               // Create new transaction object
        receiveTransaction(transaction); // Receive Transaction
        //transaction.display("MONITOR");
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
    
    // -- Wait for SOF --------------------------------------------------------
    // It waits until SOF and SRC_RDY
    task waitForSOF();  // Cekej dokud neni SOF A SRC RDY
      do begin
        // Wait if not data ready
        if (fl.monitor_cb.SOF_N ==1 || fl.monitor_cb.SRC_RDY_N==1 || fl.monitor_cb.DST_RDY_N==1)
          @(fl.monitor_cb);
        if (!enabled) return;
      end while (fl.monitor_cb.SOF_N ==1 || fl.monitor_cb.SRC_RDY_N==1 || fl.monitor_cb.DST_RDY_N==1); //Detect Start of Frame
    endtask : waitForSOF
    
    // -- Wait for SOP --------------------------------------------------------
    // It waits until SOP and SRC_RDY
    task waitForSOP(); // Cekej dokud neni SOP A SRC RDY
      do begin
        if (fl.monitor_cb.SOP_N || fl.monitor_cb.SRC_RDY_N)
          @(fl.monitor_cb);
      end while (fl.monitor_cb.SOP_N || fl.monitor_cb.SRC_RDY_N); //Detect Start of Packet
    endtask : waitForSOP
    
    // -- Wait for DST_RDY ----------------------------------------------------
    // It waits until DST_RDY and SRC_RDY
    task waitForDstRdy(); // Cekej dokud neni DST_RDY A SRC RDY
      do begin
        if (fl.monitor_cb.DST_RDY_N || fl.monitor_cb.SRC_RDY_N)
          @(fl.monitor_cb);
      end while (fl.monitor_cb.DST_RDY_N || fl.monitor_cb.SRC_RDY_N); //Detect Destination Ready
    endtask : waitForDstRdy
    
    // -- Receive Transaction -------------------------------------------------
    // It receives Frame Link transaction to tr object
    task receiveTransaction(FrameLinkTransaction tr);
      int packet_no=0;
      int byte_no;
      byte unsigned aux[];
 
      waitForSOF(); // Wait for SOF

      // -------- Process Packets -----------
      do begin 
        byte_no=0;                  // Byte offset in packet
        if (fl.monitor_cb.SRC_RDY_N == 0 && fl.monitor_cb.DST_RDY_N == 0)    
          waitForSOP();               // Wait for SOP
    
          // -------- Process data in packet (no last word)-----------
        do begin
          if (fl.monitor_cb.EOP_N || fl.monitor_cb.SRC_RDY_N) begin              
            if (fl.monitor_cb.SRC_RDY_N == 0 && fl.monitor_cb.DST_RDY_N == 0) begin
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
        end while (fl.monitor_cb.EOP_N || fl.monitor_cb.SRC_RDY_N); // Detect End of Packet
        
        // -------- Process data in packet (only last word)-----------
        waitForDstRdy();

        // when FLOWS>=8 DREM is undefinied value
        if(pFlows>=8) begin
          logic [7:0] wbyte = 0;
          for (int j=0; j<8; j++)
            wbyte[j] = fl.monitor_cb.DATA[j]; 
          aux=new[byte_no+1](aux);  
          aux[byte_no] = wbyte;
          byte_no++;
        end
        
        else begin   
          for (int i=0; i<=fl.monitor_cb.DREM; i++) begin
            logic [7:0] wbyte = 0;
            for (int j=0; j<8; j++)
              wbyte[j] = fl.monitor_cb.DATA[i*8 + j]; 
            aux=new[byte_no+1](aux);  
            aux[byte_no] = wbyte;
            byte_no++;    
          end
        end

                
        // --------- Store received data into transaction -------------
        waitForDstRdy();
        
        tr.ifcNo       = ifcNo; 
        tr.packetCount = packet_no+1;       
        tr.data        = new [tr.packetCount](tr.data);
        tr.data[tr.data.size-1]   = new [aux.size];
        tr.data[tr.packetCount-1] = aux;
        
        
        if (fl.monitor_cb.EOF_N || fl.monitor_cb.SRC_RDY_N) begin
          @(fl.monitor_cb);
          packet_no++;
        end
        else begin
          if (packet_no == 0) begin              // Frame has no header, only payload
            tr.ifcNo = ifcNo; 
            tr.packetCount = packet_no+1;       
            tr.data = new [tr.packetCount];
            tr.data[tr.data.size-1] = new [0];
            packet_no++;
            tr.packetCount = packet_no+1;       
            tr.data = new [tr.packetCount](tr.data);
            tr.data[tr.data.size-1] = new [aux.size];
            tr.data[tr.packetCount-1] = aux;
          end
          break;                                 // Detect End of Frame
        end
      
      end while (1);
      
      @(fl.monitor_cb);

    endtask : receiveTransaction
    
  endclass : FrameLinkMonitor    
