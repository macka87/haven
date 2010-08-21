/*
 * ib_memory.sv: Internal Bus Memory
 * Copyright (C) 2009 CESNET
 * Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz> 
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
 * $Id: ib_memory.sv 11501 2009-10-06 12:13:46Z washek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_memory_pkg;
  
  import ib_params_pkg::*;
  import ib_memory_transaction_pkg::*;
   
  // --------------------------------------------------------------------------
  // -- Internal Bus Memory Callbacks
  // --------------------------------------------------------------------------
  /* This is an abstract class for creating objects which get benefits from
   * function callback. This object can be used with InternalBusMemory
   * class. Inheritence from this basic class is needed for functionality.
   */
  class MemoryCbs;

    // ------------------------------------------------------------------------
    // Function is called after a write transaction is received
    virtual task writeTransReceived(MemoryTransaction tr, int memoryId);
         // By default, callback does nothing
    endtask
    
    // Function is called after a read request is received
    virtual task readReqReceived(MemoryTransaction tr, int memoryId);
         // By default, callback does nothing
    endtask
    
    // Function is called after a read data is sent
    virtual task readDataSent(MemoryTransaction tr, int memoryId);
         // By default, callback does nothing
    endtask

  endclass : MemoryCbs


  // --------------------------------------------------------------------------
  // -- Internal Bus Memory
  // --------------------------------------------------------------------------
  /* This class has memory behaviour with random delays. It is intended for
   * connection with ib_endpoint.
   */
  class InternalBusMemory #(pIbEndpointGenerics G = dIbEndpointGenerics);
    
    parameter int DW = G.DATA_WIDTH;
    parameter int AW = G.ADDR_WIDTH;
    
    virtual iIbEndpointWrite.tb #(DW, AW) wr; // Write ifc
    virtual iIbEndpointRead.tb  #(DW, AW) rd; // Read ifc
    bit enabled;                     // Enable
    bit [1:0] busy;                  // Memory is receiving transaction [R,W]
    string memoryId;                 // ID
    logic [7:0] assoc_mem[int];      // Associative memory
    MemoryCbs cbs[$];                // Callbacks list
    
    logic src_rdy;
    
    // Mailboxes for replies (for packet and continual read_type)
    tMemoryTransMbx                    replyMbx_p;
    mailbox #(logic[G.DATA_WIDTH-1:0]) replyMbx_c;
    
    // -- dealys --------------------------------------------------------------
    rand bit delayRDY;           // Do not assert RDY to delay WRITE operation
    rand bit delayARDY;          // Do not assert ARDY to delay READ operation
    rand bit delayDATA;          // Put some delay in returning read data
    rand int delayLengthDATA;    // Delay length for read data

    pIbMemoryDelays D;
    
    constraint cDelays {
       delayRDY  dist { 1'b1 := D.rdyEnWt,
                        1'b0 := D.rdyDisWt };
       delayARDY dist { 1'b1 := D.ardyEnWt,
                        1'b0 := D.ardyDisWt };
       delayDATA dist { 1'b1 := D.dataEnWt,
                        1'b0 := D.dataDisWt };
       delayLengthDATA inside {[D.dataLow : D.dataHigh]};
    }
    
    int latency = 0; // Latency of memory
    
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new(string id,
                 virtual iIbEndpointWrite.tb #(DW, AW) wr,
                 virtual iIbEndpointRead.tb  #(DW, AW) rd,
                 pIbMemoryDelays delays = dIbMemoryDelays );
      this.wr       = wr;
      this.rd       = rd;
      this.memoryId = id;
      this.enabled  = 0;
      this.D        = delays;
      
      if (G.READ_TYPE == PACKET)
        replyMbx_p = new();
      else
        replyMbx_c = new();
    endfunction : new

    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setCallbacks(MemoryCbs cbs);
      this.cbs.push_back(cbs);
    endfunction : setCallbacks
    
    // -- Enable Memory -------------------------------------------------------
    // Enable memory and runs driver process
    task setEnabled();
      enabled = 1; // Driver Enabling
      wr.cb.RDY         <= 0;
      rd.cb.ARDY_ACCEPT <= 0;
      rd.cb.SRC_RDY     <= 0; // Default state
      rd.cb.DATA        <= 0;
      fork         
        run();     // Creating driver subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Memory ------------------------------------------------------
    // Disable memory
    task setDisabled();
      enabled = 0; // Disable driver, after sending last transaction it ends
    endtask : setDisabled

    // -- Private Class Methods --
    
    // -- Run Memory ----------------------------------------------------------
    // Run memory monitoring
    task run();
      fork
        waitForRead();
        replyForRead();
        waitForWrite();
        randomNotArdy();
        randomNotRdy();
        randomDelays();
      join
    endtask : run

    // -- Wait for read -------------------------------------------------------
    // Recieve Read Requests
    task waitForRead();
      MemoryTransaction transaction, newTransaction;
      logic [G.DATA_WIDTH/8-1:0] be;
      logic [G.DATA_WIDTH-1:0]   data;
      int i, offset, byte_count;
      
      while (enabled) begin
        
        busy[1] = 0;
        
        //wait for SOF  
        while (rd.cb.SOF != 1 || rd.cb.REQ != 1)
          @(rd.cb);
        
        busy[1] = 1;
        
        while (rd.cb.SOF != 1 || rd.cb.REQ != 1 || rd.cb.ARDY_ACCEPT != 1)
          @(rd.cb);
        
        // Create Read request
        transaction           = new;
        transaction.transType = READ_REQ;
        
        //-- READ_TYPE == PACKET --
        if (G.READ_TYPE == PACKET) begin
          transaction.addr         = rd.cb.ADDR;
          transaction.length[11:0] = rd.cb.LENGTH;
          transaction.length[12]   = (rd.cb.LENGTH == 0) ? 1 : 0;
          
          // Send transaction to callbacks
          foreach (cbs[i]) cbs[i].readReqReceived(transaction, memoryId);
        
          // Store transaction to mailbox - kind of reply buffer
          addReplyToMbx_p(transaction);
          
          @(rd.cb);
        end
        
        //-- READ_TYPE == CONTINUAL --
        else begin
          
          //resolve byte enables in the first word
          be = rd.cb.BE;
          offset = 0;
          while (be[offset] == 0)
            offset++;
          
          transaction.addr   = rd.cb.ADDR + offset;
          transaction.length = -offset;
          
          newTransaction           = new;
          newTransaction.transType = READ_DATA;
          newTransaction.addr      = transaction.addr;
          
          //add bytes to length and put data to reply mailbox until EOF
          i = 0;
          byte_count = 0;
          do begin
            
            while (rd.cb.REQ != 1 || rd.cb.ARDY_ACCEPT != 1)
              @(rd.cb);
            
            if (rd.cb.ADDR != transaction.addr - offset + i*G.DATA_WIDTH/8) begin
              $display($time,"Error: Invalid address incrementing in READ transaction");
              break;
            end
                        
            //read data from memory
            for (int j = 0; j < G.DATA_WIDTH/8; j++) begin
              if (assoc_mem.exists(rd.cb.ADDR+j) && rd.cb.BE[j] == 1)
                for (int k = 0; k < 8; k++)
                  data[j*8+k] = assoc_mem[rd.cb.ADDR+j][k];
              else
                for (int k = 0; k < 8; k++)
                  data[j*8+k] = 0;
            end
            
            transaction.length += G.DATA_WIDTH/8;
            
            //copy data to newTransaction
            if (i == 0) begin
              newTransaction.data = new[transaction.length];
              for (int j = offset; j < G.DATA_WIDTH/8; j++) begin
                for (int k = 0; k < 8; k++)
                  newTransaction.data[byte_count][k] = data[j*8+k];
                byte_count++;
              end
            end else begin
              newTransaction.data = new[transaction.length](newTransaction.data);
              for (int j = 0; j < G.DATA_WIDTH/8; j++) begin
                for (int k = 0; k < 8; k++)
                  newTransaction.data[byte_count][k] = data[j*8+k];
                byte_count++;
              end
            end
            
            i++;
            
            //put data to mailbox
            addReplyToMbx_c(data);
            
            if (rd.cb.EOF)
              break;
            
            @(rd.cb);
            
          end while (1);
          
          //resolve byte enables in the last word
          be = rd.cb.BE;
          i = 0;
          while (be[G.DATA_WIDTH/8-i-1] == 0)
            i++;
          
          transaction.length -= i;
          newTransaction.length = transaction.length;
          
          // Send transaction to callbacks
          foreach (cbs[i]) cbs[i].readReqReceived(transaction, memoryId);
          
          // Send newTransaction to callbacks
          foreach (cbs[i]) cbs[i].readDataSent(newTransaction, memoryId);
          
          @(rd.cb);
          
        end //read_type == continual
        
      end // while enabled
    endtask : waitForRead
    
    // -- Add Reply To Mailbox -----------------------------------------------
    //Wait latency-time and than put transaction to mailbox (packet readtype)
    task addReplyToMbx_p(MemoryTransaction tr);
      fork
        begin
          repeat(latency) @(rd.cb);
          replyMbx_p.put(tr);
        end
      join_none;
    endtask : addReplyToMbx_p;
    
    //Wait latency-time and than put data to mailbox (continual readtype)
    task addReplyToMbx_c(logic [G.DATA_WIDTH-1:0] data);
      fork
        begin
          repeat(latency) @(rd.cb);
          replyMbx_c.put(data);
        end
      join_none;
    endtask : addReplyToMbx_c;
    
    // -- Reply for readed data ----------------------------------------------
    // Send read data (with delays)
    task replyForRead();
      MemoryTransaction transaction, newTransaction;
      logic [G.DATA_WIDTH-1:0] data;
      int cur_byte;
      bit seed = 10;
      
      @(rd.cb);
      
      while (enabled) begin
        
        //-- READ_TYPE == PACKET --
        if (G.READ_TYPE == PACKET) begin
          // Get transaction to reply to (blocking)
          replyMbx_p.get(transaction);
  
          // Create reply        
          newTransaction           = new;
          newTransaction.transType = READ_DATA;
          newTransaction.addr      = transaction.addr;
          newTransaction.length    = transaction.length;
          newTransaction.data      = new[transaction.length]; 
          
          for (int i = 0; i < transaction.length; i++) begin
            if (assoc_mem.exists(transaction.addr+i))
              newTransaction.data[i] = assoc_mem[transaction.addr+i];
            else
              // Return zeros when reading from empty location
              newTransaction.data[i] = 0;
          end
          
          // Send reply
          cur_byte = 0;
          while (cur_byte < newTransaction.length) begin
            
            //get one word of data
            for (int i = 0; i < G.DATA_WIDTH/8; i++) begin
              if (cur_byte+i < newTransaction.length)
                for (int j = 0; j < 8; j++)
                  data[i*8+j] = newTransaction.data[cur_byte+i][j];
              else
                for (int j = 0; j < 8; j++)
                  data[i*8+j] = 0;
            end
            
            cur_byte += G.DATA_WIDTH/8;
            
            //send word of data
            rd.cb.DATA    <= data;
            rd.cb.SRC_RDY <= 1;
            
            do begin
              if (delayDATA) begin
                rd.cb.SRC_RDY <= 0;
                repeat (delayLengthDATA) @(rd.cb);
                rd.cb.SRC_RDY <= 1;
              end 
              @(rd.cb);
            end while (rd.cb.DST_RDY != 1);
              
          end
          
          rd.cb.SRC_RDY <= 0;
          rd.cb.DATA    <= 0;
          
          // Send transaction to callbacks
          foreach (cbs[i]) cbs[i].readDataSent(newTransaction, memoryId);
        
        end
        
        //-- READ_TYPE == CONTINUAL --
        else begin
          
          // Get data to send (blocking)
          replyMbx_c.get(data);
          
          //send data
          rd.cb.DATA    <= data;
          rd.cb.SRC_RDY <= 1;
          
          do begin
            if (delayDATA) begin
              rd.cb.SRC_RDY <= 0;
              repeat (delayLengthDATA) @(rd.cb);
              rd.cb.SRC_RDY <= 1;
            end 
            @(rd.cb);
          end while (rd.cb.DST_RDY != 1);
          
          rd.cb.SRC_RDY <= 0;
          rd.cb.DATA    <= 0;
          
        end
        
      end // while enabled
    endtask : replyForRead

    // -- Receive write request -----------------------------------------------
    task waitForWrite();
      MemoryTransaction tr;
      int cur_byte,i,offset;
      logic [G.DATA_WIDTH/8-1:0] be;
      bit endloop = 0;
      
      while (enabled) begin
        
        busy[0] = 0;
        
        //wait for SOF  
        while (wr.cb.SOF != 1 || wr.cb.REQ != 1)
          @(wr.cb);
        
        busy[0] = 1;
        
        while (wr.cb.SOF != 1 || wr.cb.REQ != 1 || wr.cb.RDY != 1)
          @(wr.cb);
        
        //resolve byte enables in the first word
        be = wr.cb.BE;
        offset = 0;
        while (be[offset] == 0)
          offset++;
        
        // Recieve and store WRITE memory Transaction
        tr              = new; 
        tr.transType    = WRITE; 
        tr.addr         = wr.cb.ADDR + offset;
        tr.length[11:0] = wr.cb.LENGTH;
        tr.length[12]   = (wr.cb.LENGTH == 0) ? 1 : 0;
        tr.data      = new[int'(tr.length)];
        cur_byte = 0;
        endloop = 0;
        i = 0;
        
        do begin
          
          if (wr.cb.ADDR != tr.addr - offset + i*G.DATA_WIDTH/8) begin
            $display($time,"Error: Invalid address incrementing in WRITE transaction");
            endloop = 1;
          end
          
          i++;
          
          //copy word of data to transaction and store it into memory
          for (int j = 0; j < G.DATA_WIDTH/8; j++) begin
            if (wr.cb.BE[j] == 1) begin
              tr.data[cur_byte] = wr.cb.DATA >> j*8;
              assoc_mem[tr.addr+cur_byte] = wr.cb.DATA >> j*8;
              cur_byte++;
            end
            if (cur_byte > tr.length) begin
              $display($time,"Error: WRITE transaction is longer than it says by LENGTH signal");
              endloop = 1;
              break;
            end
          end
          
          if (wr.cb.LENGTH != tr.length[11:0]) begin
            $display($time,"Error: LENGTH signal on WRITE interface has changed during transaction");
            endloop = 1;
          end
          
          if (wr.cb.EOF == 1)
            endloop = 1;
          
          @(wr.cb);
          while ((wr.cb.REQ != 1 || wr.cb.RDY != 1) && endloop == 0)
            @(wr.cb);
            
        end while (endloop != 1);
        
        // Callback with writen data
        foreach (cbs[i]) cbs[i].writeTransReceived(tr, memoryId);
      end // while
    endtask : waitForWrite


    //-- Insert random waiting ----------------------------------------------
    task randomNotArdy();
       while (enabled) begin
         @(rd.cb);
         rd.cb.ARDY_ACCEPT <= !delayARDY;
       end;
    endtask : randomNotArdy

    //-- Insert random waiting ----------------------------------------------
    task randomNotRdy();
       while (enabled) begin
         @(wr.cb);
         wr.cb.RDY <= !delayRDY;
       end;
    endtask : randomNotRdy
    
    // Generate delays random values in every cycle -------------------------
    task randomDelays();
      while (enabled) begin
        assert(randomize());
        @(wr.cb);
      end;
    endtask : randomDelays

  endclass : InternalBusMemory

endpackage : ib_memory_pkg
