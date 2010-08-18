/*
 * ib_driver8_pkg.sv: Internal Bus Driver
 * Copyright (C) 2008 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
 *            Tomas Malek <tomalek@liberouter.org> 
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
 * $Id: ib_driver8_pkg.sv 1366 2008-02-18 15:26:54Z tomalek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------

package ib_driver_pkg;

  import ib_transaction_pkg::*; // Transaction package

  // --------------------------------------------------------------------------
  // -- Internal Bus Driver Callbacks
  // --------------------------------------------------------------------------
  /* This is a abstract class for creating objects which get benefits from
   * function callback. This object can be used with InternalBusDriver
   * class. Inheritence from this basic class is neaded for functionality.
   */
  class DriverCbs;
    
    // -- Class Methods --

    // ------------------------------------------------------------------------
    // Function is called before is transaction sended - usefull for
    // transaction modification
    virtual task pre_tx(ref InternalBusTransaction transaction, integer driverId);
      // By default, callback does nothing
    endtask: pre_tx
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended throw interface - 
    // usefull for scoreboards
    virtual task post_tx(InternalBusTransaction transaction, integer driverId);
      // By default, callback does nothing
    endtask: post_tx
  
  endclass : DriverCbs

  // --------------------------------------------------------------------------
  // -- Internal Bus Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to Internal Bus
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transcaction by calling "sendTransaction" function.
   */
  class InternalBusDriver;

    // -- Public Class Atributes --


    // -- Private Class Atributes --
    integer   driverId;                         // Driver identification
    bit       enabled;                          // Driver is enabled
    tTransMbx transMbx;                         // Transaction mailbox
    DriverCbs cbs[$];                           // Callbacks list
    virtual   iIB.tx internalBus;  // Internal Bus interface
 
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( tTransMbx                    transMbx,
                   virtual iIB.tx  internalBus,
                   integer                      driverId );
      this.enabled     = 0;            // Driver is disabled by default
      this.internalBus = internalBus;  // Store pointer interface 
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.driverId    = driverId;     // Store driver identifier
      // Setting default values for Internal Bus interface
      this.internalBus.DATA      = 0;
      this.internalBus.SOF_N     = 1;
      this.internalBus.EOF_N     = 1;
      this.internalBus.SRC_RDY_N = 1;
    endfunction: new
    
    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(DriverCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // -- Enable Driver -------------------------------------------------------
    // Enable driver and runs driver process
    task setEnabled();
      enabled = 1; // Driver Enabling
      fork         
        run();     // Creating driver subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Driver ------------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable driver, after sending last transaction it ends
    endtask : setDisabled
    
    // -- Send Transaction ----------------------------------------------------
    // Send transaction to Internal Bus interface
    task sendTransaction( InternalBusTransaction transaction );
      
      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(transaction, driverId);

      // Wait before sending transaction
      repeat (transaction.txDelay) @(posedge internalBus.CLK);
      
      // Send transaction
      case (transaction.transType)
        L2LW:
          sendL2LW(transaction);
        L2LR:
          sendL2LR(transaction);
        L2GW:
          sendL2GW(transaction);
        G2LR:
          sendG2LR(transaction);
        RDC:
          sendRDC(transaction);
        RDCL:
          sendRDCL(transaction);
      endcase;

      // Set not ready 
      internalBus.SOF_N     = 1;
      internalBus.EOF_N     = 1;
      internalBus.SRC_RDY_N = 1;
    
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(transaction, driverId);
    endtask : sendTransaction

    // -- Private Class Methods --
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      InternalBusTransaction transaction;
      @(posedge internalBus.CLK);      // Wait for clock
      while (enabled) begin            // Repeat while enabled
        transMbx.get(transaction);     // Get transaction from mailbox
        $write("D%0x: ",driverId);
        transaction.display(1);        // Display transaction
        sendTransaction(transaction);  // Send Transaction
      end
    endtask : run
    
    // -- Wait for accept -----------------------------------------------------
    // Wait for accepting of 64 bits word of transaction
    task waitForAccept();
      logic data_writen;
      do begin
        @(negedge internalBus.CLK);  
        data_writen= ! internalBus.DST_RDY_N; // Store DST_RDY status 
        @(posedge internalBus.CLK);           // Wait for Clock
      end while (! data_writen);              // Repeat until succesfull write
    endtask : waitForAccept

    // -- Random wait ---------------------------------------------------------
    // Random wait during sending transaction (Set SRC_RDY_N to 1)
    task randomWait(InternalBusTransaction transaction);
      repeat (transaction.getRandomWait()) begin
        internalBus.SRC_RDY_N = 1;
        @(posedge internalBus.CLK); // Wait for send
      end;
    endtask : randomWait

    // -- Send Header 0 -------------------------------------------------------
    // Send Header 0
    task sendHdr0(logic [7:0] hdr);
      // Send header 0
      internalBus.DATA      = hdr;
      internalBus.SOF_N     = 0;
      internalBus.EOF_N     = 1;
      internalBus.SRC_RDY_N = 0;
      waitForAccept(); // Wait for accepting
      internalBus.SOF_N     = 1;
    endtask : sendHdr0

    // -- Send Header X -------------------------------------------------------
    // Send Header X
    task sendHdrX(logic [7:0] hdr);
      // Send header X
      internalBus.DATA      = hdr;
      internalBus.SOF_N     = 1;
      internalBus.EOF_N     = 1;
      internalBus.SRC_RDY_N = 0;
      waitForAccept(); // Wait for accepting
      internalBus.SOF_N     = 1;
    endtask : sendHdrX    

    // -- Send Header 1 -------------------------------------------------------
    // Send Header 1
    task sendHdr1(logic [7:0] hdr, bit eop_n);
      // Send header 0
      internalBus.DATA      = hdr;
      internalBus.SOF_N     = 1;
      internalBus.EOF_N     = eop_n;
      internalBus.SRC_RDY_N = 0;
      waitForAccept(); // Wait for accepting
      internalBus.EOF_N     = 1;
    endtask : sendHdr1

    // -- Send transaction data -----------------------------------------------
    // Send transaction data
    task sendData(InternalBusTransaction tr, integer offset);
 
      // Send Data
      for (integer i=0; i < tr.data.size; i=i+1) begin

        //logic [7:0] write_data = 8'h00; 
        //for (integer j=0; j < 8; j++)
        //  write_data[j] = tr.data[i][j]; 
         
        internalBus.DATA      = tr.data[i];
        internalBus.SOF_N     = 1;
        internalBus.SRC_RDY_N = 0;
        if ((i+1) >= tr.data.size)
          internalBus.EOF_N   = 0;
        else
          internalBus.EOF_N   = 1; 

        waitForAccept();         // Wait for accepting
        if ((i+1) < tr.data.size)  // If NOT EOF
          randomWait(tr);        // Random wait during transaction
       end
    endtask : sendData

    // -- Send L2LW -----------------------------------------------------------
    // Send L2LW transaction, data is aligned to destination adress
    task sendL2LW ( InternalBusTransaction tr);
     
      // 7:0 ----------------------------------------------
      sendHdr0({tr.length[3:0],L2LW_TYPE});   
      randomWait(tr);   
      // 15:8 ---------------------------------------------
      sendHdrX(tr.length[11:4]);   
      randomWait(tr);         
      // 23:16 --------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);               
      // 31:24 --------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);
      // 39:32 --------------------------------------------
      sendHdrX(tr.localAddr[7:0]);   
      randomWait(tr);                        
      // 47:40 --------------------------------------------
      sendHdrX(tr.localAddr[15:8]);   
      randomWait(tr);                           
      // 55:48 --------------------------------------------
      sendHdrX(tr.localAddr[23:16]);   
      randomWait(tr);                                    
      // 63:56 --------------------------------------------
      sendHdrX(tr.localAddr[31:24]);   
      randomWait(tr);                                          
      // 71:64 --------------------------------------------
      sendHdrX(tr.globalAddr[7:0]);   
      randomWait(tr);                                             
      // 79:72 --------------------------------------------
      sendHdrX(tr.globalAddr[15:8]);   
      randomWait(tr);                                          
      // 87:80 --------------------------------------------
      sendHdrX(tr.globalAddr[23:16]);   
      randomWait(tr);                                                   
      // 95:88 --------------------------------------------
      sendHdrX(tr.globalAddr[31:24]);   
      randomWait(tr);                                                         
      // 103:96 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                             
      // 111:104 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                                  
      // 119:112 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                                  
      // 127:120 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                                  
       
      sendData(tr, tr.localAddr[2:0]); // Send Data
    endtask : sendL2LW

    // -- Send L2LR -----------------------------------------------------------
    // Send L2LR transaction, Read data from source address
    task sendL2LR( InternalBusTransaction tr );
      logic [63:0] hdr0; // Header data0
      logic [63:0] hdr1; // Header data1
      
      // Assembly headers
      hdr0 = {tr.localAddr,8'h00, tr.tag,tr.length,L2LR_TYPE};
      hdr1 = {32'h00000000, tr.globalAddr[31:0]};

      // 7:0 ----------------------------------------------
      sendHdr0({tr.length[3:0],L2LR_TYPE});   
      randomWait(tr);   
      // 15:8 ---------------------------------------------
      sendHdrX(tr.length[11:4]);   
      randomWait(tr);         
      // 23:16 --------------------------------------------
      sendHdrX(tr.tag);   
      randomWait(tr);               
      // 31:24 --------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);
      // 39:32 --------------------------------------------
      sendHdrX(tr.localAddr[7:0]);   
      randomWait(tr);                        
      // 47:40 --------------------------------------------
      sendHdrX(tr.localAddr[15:8]);   
      randomWait(tr);                           
      // 55:48 --------------------------------------------
      sendHdrX(tr.localAddr[23:16]);   
      randomWait(tr);                                    
      // 63:56 --------------------------------------------
      sendHdrX(tr.localAddr[31:24]);   
      randomWait(tr);                                          
      // 71:64 --------------------------------------------
      sendHdrX(tr.globalAddr[7:0]);   
      randomWait(tr);                                             
      // 79:72 --------------------------------------------
      sendHdrX(tr.globalAddr[15:8]);   
      randomWait(tr);                                          
      // 87:80 --------------------------------------------
      sendHdrX(tr.globalAddr[23:16]);   
      randomWait(tr);                                                   
      // 95:88 --------------------------------------------
      sendHdrX(tr.globalAddr[31:24]);   
      randomWait(tr);                                                         
      // 103:96 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                             
      // 111:104 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                                  
      // 119:112 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                                  
      // 127:120 -------------------------------------------
      sendHdr1(8'h00,0);   
      
    endtask : sendL2LR

    // -- Send L2GW -----------------------------------------------------------
    // Send L2GW transaction, Write data to global address space
    task sendL2GW( InternalBusTransaction tr );
      logic [63:0] hdr0; // Header data0
      logic [63:0] hdr1; // Header data1

      // Assembly headers
      hdr0 = {tr.globalAddr[31:0],16'h0000,tr.length,L2GW_TYPE};
      hdr1 = {tr.globalAddr[63:32], tr.localAddr};
 
      // 7:0 ----------------------------------------------
      sendHdr0({tr.length[3:0],L2GW_TYPE});   
      randomWait(tr);   
      // 15:8 ---------------------------------------------
      sendHdrX(tr.length[11:4]);   
      randomWait(tr);         
      // 23:16 --------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);               
      // 31:24 --------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);
      // 39:32 --------------------------------------------
      sendHdrX(tr.globalAddr[7:0]);   
      randomWait(tr);                        
      // 47:40 --------------------------------------------
      sendHdrX(tr.globalAddr[15:8]);   
      randomWait(tr);                           
      // 55:48 --------------------------------------------
      sendHdrX(tr.globalAddr[23:16]);   
      randomWait(tr);                                    
      // 63:56 --------------------------------------------
      sendHdrX(tr.globalAddr[31:24]);   
      randomWait(tr);                                          
      // 71:64 --------------------------------------------
      sendHdrX(tr.localAddr[7:0]);   
      randomWait(tr);                                             
      // 79:72 --------------------------------------------
      sendHdrX(tr.localAddr[15:8]);   
      randomWait(tr);                                          
      // 87:80 --------------------------------------------
      sendHdrX(tr.localAddr[23:16]);   
      randomWait(tr);                                                   
      // 95:88 --------------------------------------------
      sendHdrX(tr.localAddr[31:24]);   
      randomWait(tr);                                                         
      // 103:96 -------------------------------------------
      sendHdrX(tr.globalAddr[39:32]);   
      randomWait(tr);                                                             
      // 111:104 -------------------------------------------
      sendHdrX(tr.globalAddr[47:40]);   
      randomWait(tr);                                                                  
      // 119:112 -------------------------------------------
      sendHdrX(tr.globalAddr[55:48]);   
      randomWait(tr);                                                                  
      // 127:120 -------------------------------------------
      sendHdrX(tr.globalAddr[63:56]);   
      randomWait(tr);                                                                      

      sendData(tr, tr.globalAddr[2:0]); // Send Data
    endtask : sendL2GW

    // -- Send G2LR -----------------------------------------------------------
    // Send G2LR transaction, Read data from global address space
    task sendG2LR( InternalBusTransaction tr );
      logic [63:0] hdr0; // Header data0
      logic [63:0] hdr1; // Header data1

      // Assembly headers
      hdr0 = {tr.globalAddr[31:0],8'h00,tr.tag, tr.length, G2LR_TYPE};
      hdr1 = {tr.globalAddr[63:32], tr.localAddr};

      // 7:0 ----------------------------------------------
      sendHdr0({tr.length[3:0],G2LR_TYPE});   
      randomWait(tr);   
      // 15:8 ---------------------------------------------
      sendHdrX(tr.length[11:4]);   
      randomWait(tr);         
      // 23:16 --------------------------------------------
      sendHdrX(tr.tag);   
      randomWait(tr);               
      // 31:24 --------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);
      // 39:32 --------------------------------------------
      sendHdrX(tr.globalAddr[7:0]);   
      randomWait(tr);                        
      // 47:40 --------------------------------------------
      sendHdrX(tr.globalAddr[15:8]);   
      randomWait(tr);                           
      // 55:48 --------------------------------------------
      sendHdrX(tr.globalAddr[23:16]);   
      randomWait(tr);                                    
      // 63:56 --------------------------------------------
      sendHdrX(tr.globalAddr[31:24]);   
      randomWait(tr);                                          
      // 71:64 --------------------------------------------
      sendHdrX(tr.localAddr[7:0]);   
      randomWait(tr);                                             
      // 79:72 --------------------------------------------
      sendHdrX(tr.localAddr[15:8]);   
      randomWait(tr);                                          
      // 87:80 --------------------------------------------
      sendHdrX(tr.localAddr[23:16]);   
      randomWait(tr);                                                   
      // 95:88 --------------------------------------------
      sendHdrX(tr.localAddr[31:24]);   
      randomWait(tr);                                                         
      // 103:96 -------------------------------------------
      sendHdrX(tr.globalAddr[39:32]);   
      randomWait(tr);                                                             
      // 111:104 -------------------------------------------
      sendHdrX(tr.globalAddr[47:40]);   
      randomWait(tr);                                                                  
      // 119:112 -------------------------------------------
      sendHdrX(tr.globalAddr[55:48]);   
      randomWait(tr);                                                                  
      // 127:120 -------------------------------------------
      sendHdr1(tr.globalAddr[63:56],0);   
      
    endtask : sendG2LR

    // -- Send RDC ------------------------------------------------------------
    // Send RDC transaction, Read completition transaction, data is alligned to
    // destination address (without last flag)
    task sendRDC( InternalBusTransaction tr );
      logic [63:0] hdr0; // Header data0
      logic [63:0] hdr1; // Header data1
       
      // Assembly headers
      hdr0 = {tr.globalAddr[31:0],8'h00,tr.tag, tr.length, RDC_TYPE};
      hdr1 = {32'h00000000, tr.localAddr};
      
      // 7:0 ----------------------------------------------
      sendHdr0({tr.length[3:0],RDC_TYPE});   
      randomWait(tr);   
      // 15:8 ---------------------------------------------
      sendHdrX(tr.length[11:4]);   
      randomWait(tr);         
      // 23:16 --------------------------------------------
      sendHdrX(tr.tag);   
      randomWait(tr);               
      // 31:24 --------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);
      // 39:32 --------------------------------------------
      sendHdrX(tr.globalAddr[7:0]);   
      randomWait(tr);                        
      // 47:40 --------------------------------------------
      sendHdrX(tr.globalAddr[15:8]);   
      randomWait(tr);                           
      // 55:48 --------------------------------------------
      sendHdrX(tr.globalAddr[23:16]);   
      randomWait(tr);                                    
      // 63:56 --------------------------------------------
      sendHdrX(tr.globalAddr[31:24]);   
      randomWait(tr);                                          
      // 71:64 --------------------------------------------
      sendHdrX(tr.localAddr[7:0]);   
      randomWait(tr);                                             
      // 79:72 --------------------------------------------
      sendHdrX(tr.localAddr[15:8]);   
      randomWait(tr);                                          
      // 87:80 --------------------------------------------
      sendHdrX(tr.localAddr[23:16]);   
      randomWait(tr);                                                   
      // 95:88 --------------------------------------------
      sendHdrX(tr.localAddr[31:24]);   
      randomWait(tr);                                                         
      // 103:96 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                             
      // 111:104 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                                  
      // 119:112 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                                  
      // 127:120 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                                 
      
      sendData(tr, tr.globalAddr[2:0]); // Send Data
    endtask : sendRDC

    // -- Send RDCL -----------------------------------------------------------
    // Send RDCL transaction, Read completition transakce, data is aligned to
    // destination addres (with last flag)
    task sendRDCL( InternalBusTransaction tr );
      logic [63:0] hdr0; // Header data0
      logic [63:0] hdr1; // Header data1

      // Assembly headers
      hdr0 = {tr.globalAddr[31:0],8'h00,tr.tag, tr.length, RDCL_TYPE};
      hdr1 = {32'h00000000, tr.localAddr};

      // 7:0 ----------------------------------------------
      sendHdr0({tr.length[3:0],RDCL_TYPE});   
      randomWait(tr);   
      // 15:8 ---------------------------------------------
      sendHdrX(tr.length[11:4]);   
      randomWait(tr);         
      // 23:16 --------------------------------------------
      sendHdrX(tr.tag);   
      randomWait(tr);               
      // 31:24 --------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);
      // 39:32 --------------------------------------------
      sendHdrX(tr.globalAddr[7:0]);   
      randomWait(tr);                        
      // 47:40 --------------------------------------------
      sendHdrX(tr.globalAddr[15:8]);   
      randomWait(tr);                           
      // 55:48 --------------------------------------------
      sendHdrX(tr.globalAddr[23:16]);   
      randomWait(tr);                                    
      // 63:56 --------------------------------------------
      sendHdrX(tr.globalAddr[31:24]);   
      randomWait(tr);                                          
      // 71:64 --------------------------------------------
      sendHdrX(tr.localAddr[7:0]);   
      randomWait(tr);                                             
      // 79:72 --------------------------------------------
      sendHdrX(tr.localAddr[15:8]);   
      randomWait(tr);                                          
      // 87:80 --------------------------------------------
      sendHdrX(tr.localAddr[23:16]);   
      randomWait(tr);                                                   
      // 95:88 --------------------------------------------
      sendHdrX(tr.localAddr[31:24]);   
      randomWait(tr);                                                         
      // 103:96 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                             
      // 111:104 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                                  
      // 119:112 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                                  
      // 127:120 -------------------------------------------
      sendHdrX(8'h00);   
      randomWait(tr);                                                                      

      sendData(tr, tr.globalAddr[2:0]); // Send Data
    endtask : sendRDCL

  endclass : InternalBusDriver

endpackage : ib_driver_pkg










