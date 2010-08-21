/*
 * ib_memory_pkg.sv: Internal Bus Memory
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id: ib_memory.sv 333 2007-09-05 20:07:59Z xkobie00 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_memory_pkg;

  import ib_memory_transaction_pkg::*;
   
  // --------------------------------------------------------------------------
  // -- Internal Bus Memory Callbacks
  // --------------------------------------------------------------------------
  /* This is a abstract class for creating objects which get benefits from
   * function callback. This object can be used with InternalBusMemory
   * class. Inheritence from this basic class is neaded for functionality.
   */
  class MemoryCbs;

    // ------------------------------------------------------------------------
    // Function is called after any memory request, completition
    virtual task memory_transaction(MemoryTransaction transaction, integer memoryId);
         // By default, callback does nothing
    endtask

  endclass : MemoryCbs


  // --------------------------------------------------------------------------
  // -- Internal Bus Memory Delays
  // --------------------------------------------------------------------------
  /*
   * This class provides random values for delays in Internal Bus Memory
   */
  class InternalBusMemoryDelay;
     rand bit delayRDY;           // Do not assert RDY to delay WRITE operation
     rand bit delayARDY;          // Do not assert ARDY to delay READ operation
     rand bit delayDATA;          // Put some delay in returning read data
     rand int delayLengthDATA;    // Delay length for read data

     int delayRDYen_wt        = 1; //
     int delayRDYdisable_wt   = 5; //
     int delayARDYen_wt       = 1; //
     int delayARDYdisable_wt  = 5; // Delays probalities
     int delayDATAen_wt       = 1; //
     int delayDATAdisable_wt  = 5; //

     bit delayLengthLow       = 1; //
     bit delayLengthHigh      = 3; // Delay length limits

     constraint cRanges {
        delayLengthDATA inside {[delayLengthLow:delayLengthHigh]};
     }

     constraint cDelays {
        delayRDY dist { 1'b1 := delayRDYen_wt,
                        1'b0 := delayRDYdisable_wt};
        delayARDY dist { 1'b1 := delayARDYen_wt,
                         1'b0 := delayARDYdisable_wt};
        delayDATA dist { 1'b1 := delayDATAen_wt,
                         1'b0 := delayDATAdisable_wt};
     }

  endclass : InternalBusMemoryDelay


  // --------------------------------------------------------------------------
  // -- Internal Bus Memory
  // --------------------------------------------------------------------------
  /* This class has memory behaviour with random delays. It is intended for
   * connection with ib_endpoint.
   */
  class InternalBusMemory;
    virtual iIbEndpointWrite64.user WR; // Write interface
    virtual iIbEndpointRead64s.user RD; // Read interface
    bit enabled;                        // Enable
    integer memoryId;                   // ID
    logic [7:0] assoc_mem[*];           // Associative memory
    MemoryCbs cbs[$];                   // Callbacks list
    tMemoryTransMbx replyMbx;           // Mailbox for planned replies
    InternalBusMemoryDelay delays;      // Random delays generator

    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new(virtual iIbEndpointWrite64.user WR,
                 virtual iIbEndpointRead64s.user RD,
                 integer memoryId);
      this.WR       = WR;
      this.RD       = RD;
      this.memoryId = memoryId;
      this.enabled  = 0;
      replyMbx      = new();
      delays        = new;
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
      WR.RDY     <= 0;
      RD.ARDY    <= 0;
      RD.SRC_RDY <= 0; // Default state
      RD.DATA    <= 0;
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
      MemoryTransaction transaction;
      logic active;

      while (enabled) begin
        // Sampling input values
        do begin
          @(posedge RD.CLK);
          #0;
          //#1ns; // TODO: As in honeywell
          active = RD.REQ && RD.ARDY;
        end while (! active);

        // Creating Read request
        transaction           = new; // Prepare READ_REQ MemoryTransaction
        transaction.addr      = RD.ADDR;
        transaction.be        = RD.BE;
        transaction.data      = 0; // No valid data with READ_REQ type
        transaction.transType = READ_REQ;

        // Send SlaveTransaction to callbacks
        foreach (cbs[i]) cbs[i].memory_transaction(transaction, memoryId);

        // Store SlaveTransaction to mailbox - kind of reply buffer
        replyMbx.put(transaction);
      end // while enabled
    endtask : waitForRead

    // -- Reply for readed data ----------------------------------------------
    // Send read data (with delays)
    task replyForRead();
      MemoryTransaction transaction, newTransaction;
      logic done;
      logic curr_bit;
      logic [63:0] data;
      
      while (enabled) begin
         
        // Get transaction to reply to (blocking)
        replyMbx.get(transaction);

//        if (delays.delayDATA) 
//          repeat (delays.delayLengthDATA) @(posedge RD.CLK); // Random delay
        
        for (integer i = 0; i < 64; i++) begin // Resolve byte enables
          if (assoc_mem.exists(transaction.addr+i/8))
            data[i] = assoc_mem[transaction.addr+i/8][i%8];
          else
            data[i] = 1'b0; // Return zeros when reading from empty location
        end // for
        
        newTransaction           = new;  // Prepare READ_DATA SlaveTransaction
        newTransaction.addr      = transaction.addr; 
        newTransaction.be        = transaction.be;   
        newTransaction.data      = data;
        newTransaction.transType = READ_DATA;
        
        RD.DATA    <= data; // Send Data
        RD.SRC_RDY <= 1;    // Start reply

        // Proceed only if DST_RDY is 1
        do begin    
          #0; 
          done = RD.DST_RDY;
          @(posedge RD.CLK);
        end while (!done);
        RD.SRC_RDY <= 0; // Default state
        RD.DATA    <= 0;
        
        // Send transaction to callbacks
        foreach (cbs[i]) cbs[i].memory_transaction(newTransaction, memoryId);

       end // while enabled
    endtask : replyForRead

    // -- Receive write request -----------------------------------------------
    task waitForWrite();
      MemoryTransaction transaction;
      while (enabled) begin
        
        // Wait for right moment to sample data
        do begin
          @(posedge WR.CLK);
          #9ns; // TODO: Ask in honeywell
        end while (!(WR.REQ==1 && WR.RDY==1));
  
        // Recieve and store WRITE memory Transaction
        transaction           = new; 
        transaction.transType = WRITE; 
        transaction.addr      = WR.ADDR;
        transaction.be        = WR.BE;
        transaction.data      = WR.DATA;
        
        // Store data into associative memory (solve be)
        for(int i=0; i < 8; i++) 
          if (transaction.be[i])
            for (int j=0; j < 8; j++)
              assoc_mem[transaction.addr+i][j] = transaction.data[i*8+j];

        // Callback with writen data
        foreach (cbs[i]) cbs[i].memory_transaction(transaction, memoryId);
       end // while
    endtask : waitForWrite

      // Insert random waiting
      task randomNotArdy();
         while (enabled) begin
           RD.ARDY <= RD.REQ && !delays.delayARDY;
           @(posedge RD.CLK);
         end;
      endtask : randomNotArdy

      //-- Insert random waiting ----------------------------------------------
      task randomNotRdy();
         while (enabled) begin
           WR.RDY <= WR.REQ && !delays.delayRDY;
           @(posedge WR.CLK);
         end; // while
      endtask : randomNotRdy

      // Generate delays random values in every cycle -------------------------
      task randomDelays();
        while (enabled) begin
          assert(delays.randomize);
          @(posedge WR.CLK);
        end; // while
      endtask : randomDelays

   endclass : InternalBusMemory

endpackage : ib_memory_pkg
