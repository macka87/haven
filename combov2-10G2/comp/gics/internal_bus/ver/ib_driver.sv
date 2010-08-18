/*
 * ib_driver.sv: Internal Bus Driver
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
 * $Id: ib_driver.sv 11163 2009-09-14 13:47:00Z washek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
// -- Internal Bus Driver Class
// ----------------------------------------------------------------------------
/* This class is responsible for generating signals to Internal Bus
 * interface. Transactions are received by 'transMbx'(Mailbox) property.
 * Unit must be enabled by "setEnable()" function call. Generation can be
 * stoped by "setDisable()" function call. You can send your custom
 * transcaction by calling "sendTransaction" function.
 */
class InternalBusDriver #(int DATA_WIDTH=64);
  
  parameter int LOG2DWB = max(log2(DATA_WIDTH/8),1);
  
  // -- Private Class Atributes --
  string    inst;                             // Driver identification
  bit       enabled;                          // Driver is enabled
  bit       busy;                             // Driver is sending transaction
  tTransMbx transMbx;                         // Transaction mailbox
  DriverCbs cbs[$];                           // Callbacks list
  virtual   iInternalBusRx.tb #(DATA_WIDTH) ib;  // IB interface
  
  // Delays probabilities and limits
  pIbDriverDelays D;
  
  rand bit enDelay;        // Enable/Disable delays between transactions
  rand int delay;          // Delay between transactions
  rand bit enInsideDelay;  // Enable/Disable delays inside transaction
  rand int insideDelay;    // Delay inside transactions
  
  // -- Constrains --
  constraint cDelays {
    enDelay dist { 1'b1 := D.outEnWt,
                   1'b0 := D.outDisWt };

    delay inside { [D.outLow : D.outHigh] };

    enInsideDelay dist { 1'b1 := D.inEnWt,
                         1'b0 := D.inDisWt };
    
    insideDelay inside { [D.inLow : D.inHigh] };
  }
  
  
  // -- Public Class Methods --

  // -- Constructor -----------------------------------------------------------
  // Create driver object 
  function new ( string          inst, 
                 virtual iInternalBusRx.tb #(DATA_WIDTH)  ib,
                 tTransMbx       transMbx,
                 pIbDriverDelays delays = dIbDriverDelays );
    
    this.enabled   = 0;            // Driver is disabled by default
    this.ib        = ib;           // Store pointer interface 
    this.transMbx  = transMbx;     // Store pointer to mailbox
    this.inst      = inst;         // Store driver identifier
    this.D         = delays;
    
    // Setting default values for Internal Bus interface
    this.ib.cb.DATA      <= 'x;
    this.ib.cb.SOF_N     <= 'x;
    this.ib.cb.EOF_N     <= 'x;
    this.ib.cb.SRC_RDY_N <= 1;
    
  endfunction : new
  
  // -- Set Callbacks ---------------------------------------------------------
  // Put callback object into List 
  function void setCallbacks(DriverCbs cbs);
    this.cbs.push_back(cbs);
  endfunction : setCallbacks
  
  // -- Enable Driver ---------------------------------------------------------
  // Enable driver and runs driver process
  task setEnabled();
    enabled = 1; // Driver Enabling
    fork         
      run();     // Creating driver subprocess
    join_none;   // Don't wait for ending
  endtask : setEnabled
      
  // -- Disable Driver --------------------------------------------------------
  // Disable generator
  task setDisabled();
    enabled = 0; // Disable driver, after sending last transaction it ends
  endtask : setDisabled
  
  // -- Send Transaction ------------------------------------------------------
  // Send transaction to Internal Bus interface
  task sendTransaction( InternalBusTransaction tr );
    Transaction trans;
    logic[127:0] header;
    $cast(trans, tr);
    
    busy = 1;
    
    // Call transaction preprocesing, if is available
    foreach (cbs[i]) cbs[i].pre_tx(trans, inst);
    
    // randomize waits
    assert(randomize());
    
    // Wait before sending transaction
    if (enDelay) repeat (delay) @(ib.cb);
    
    // * Send header *
    header = {tr.globalAddr[63:32], tr.localAddr, tr.globalAddr[31:0],
              8'h00, tr.tag, tr.length[11:0], tr.transType};
    
    for (int i=0; i < 128/DATA_WIDTH; i++) begin
      
      ib.cb.SRC_RDY_N <= 0;
      
      //set SOF_N and EOF_N
      //first part of header
      if (i == 0)
        ib.cb.SOF_N <= 0;
      else
        ib.cb.SOF_N <= 1;
      
      //last part of header
      if (i == 128/DATA_WIDTH-1 && tr.data.size() == 0)
        ib.cb.EOF_N <= 0;
      else
        ib.cb.EOF_N <= 1;
      
      for (int j=0; j < DATA_WIDTH; j++)
        ib.cb.DATA[j] <= header[i*DATA_WIDTH+j];
      
      waitForAccept();
      
      assert(randomize());
      randomWait();
    end
    
    // * Send data, if any *
    if (tr.data.size() > 0) begin
      logic[DATA_WIDTH:0] partOfData;
      logic[LOG2DWB-1:0] offset;
      int numOfParts;
      int curByte = 0;
      int j0;

      //count offset (data alignment)
      if (DATA_WIDTH > 8)
        offset = tr.globalAddr[LOG2DWB-1:0];
      else
        offset = 0;
      
      //count number of parts
      if ((tr.data.size+offset)%(DATA_WIDTH/8) == 0)
        numOfParts = (tr.data.size+offset)/(DATA_WIDTH/8);
      else
        numOfParts = (tr.data.size+offset)/(DATA_WIDTH/8) + 1;
      
      //send parts of data
      for (int i=0; i < numOfParts; i++) begin
        ib.cb.SRC_RDY_N <= 0;
        ib.cb.SOF_N     <= 1;
        if (i == numOfParts-1)
          ib.cb.EOF_N <= 0;
        else
          ib.cb.EOF_N <= 1;
        
        partOfData = 0;
        
        //copy bytes
        if (i==0) j0 = offset; else j0 = 0;
        for (int j=j0; j < DATA_WIDTH/8 && curByte < tr.data.size; j++) begin
          for (int k = 0; k < 8; k++) //one byte
            partOfData[j*8+k] = tr.data[curByte][k];
          curByte++;
        end

        ib.cb.DATA <= partOfData;
        
        waitForAccept();
        
        assert(randomize());
        randomWait();
      end
    end
    
    // Set not ready 
    ib.cb.SRC_RDY_N <= 1;
    ib.cb.SOF_N     <= 'x;
    ib.cb.EOF_N     <= 'x;
    ib.cb.DATA      <= 'x;
    
    // Call transaction postprocesing, if is available
    foreach (cbs[i]) cbs[i].post_tx(tr, inst);
    
    busy = 0;

  endtask : sendTransaction

  // -- Private Class Methods --
  
  // -- Run Driver ------------------------------------------------------------
  // Take transactions from mailbox and generate them to interface
  task run();
    InternalBusTransaction transaction;
    Transaction tr;
    @(ib.cb);                        // Wait for clock
    while (enabled) begin            // Repeat while enabled
      transMbx.get(tr);              // Get transaction from mailbox
      $cast(transaction, tr);
      sendTransaction(transaction);  // Send Transaction
    end
  endtask : run
  
  // -- Wait for accept -------------------------------------------------------
  // Wait for accepting word of transaction
  task waitForAccept();
     @(ib.cb);
     wait (ib.cb.DST_RDY_N == 0);
  endtask : waitForAccept
  
  // -- Random wait -----------------------------------------------------------
  // Random wait during sending transaction (Set SRC_RDY_N to 1)
  task randomWait();
    repeat (enInsideDelay ? $urandom_range(D.inLow, D.inHigh) : 0) begin
      ib.cb.SRC_RDY_N <= 1;
      ib.cb.SOF_N     <= 'x;
      ib.cb.EOF_N     <= 'x;
      ib.cb.DATA      <= 'x;
      @(ib.cb);
    end;
  endtask : randomWait

endclass : InternalBusDriver
