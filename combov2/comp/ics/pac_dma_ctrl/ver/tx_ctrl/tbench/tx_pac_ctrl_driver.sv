/*
 * tx_pac_ctrl_driver.sv: TX PAC DMA Controller Driver
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
 * $Id: tx_pac_ctrl_driver.sv 9259 2009-07-09 14:48:03Z xsanta06 $
 *
 * TODO:
 *
 */
 
  import sv_tx_pac_ctrl_pkg::*;
  import sv_fl_pkg::*;
  import math_pkg::*;
   
  // --------------------------------------------------------------------------
  // -- TX DMA Controller Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for simulating RAM. Transactions are received 
   * by 'transMbx'(Mailbox) property. Unit must be enabled by "setEnable()" 
   * function call. Generation can be stoped by "setDisable()" function call. 
   */
  class TxDmaCtrlDriver #(int pFlows = 2, int pNumFlags = 8, 
                          int pRamSize = 4096, int pMaxDescLength = 1520);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string    inst;                             // Driver identification
    bit       enabled;                          // Driver is enabled
    tTransMbx transMbx;                         // Transaction mailbox
    tDescriptor  descQue[pFlows][$];            // Descriptors Queue
    DriverCbs cbs[$];                           // Callbacks list
    
    TxDescManager #(pFlows) descManager;        // Descriptor interface driver
    
    byte          ram[];                        // Software memory
    bit           validFlag[];                  // Valid data flag
    int unsigned  ramPtr = 0;                   // Lastly used RAM address
    bit           newSpaceFlag;                 // New space in RAM

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   tTransMbx transMbx,
                   TxDescManager #(pFlows) descManager
                   );
      this.enabled     = 0;            // Driver is disabled by default
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier
      this.descManager = descManager;
      
      // Allocate memory RAM
      ram        = new[pRamSize];
      validFlag  = new[pRamSize];

      foreach(validFlag[i]) validFlag[i] = 0;
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
  
    // -- Get Data Byte -------------------------------------------------------
    // Get byte of data from RAM
    task getDataByte(int address, output byte data);
      data = ram[address]; 
//      $write("OUTPUT FROM GET DATA: addr:%1x data:%0h\n", address, data);
    endtask : getDataByte
    
    // -- Send Status update ---------------------------------------------------
    // Receives Status Update
    task sendStatusUpdate(int flow, logic [pNumFlags-1:0] flags);
      tDescriptor descriptor;
//      $write("pop for flow:%0d\n",flow);
      do begin
        descriptor = descQue[flow].pop_front();
        freeSpace(descriptor.address, descriptor.length);
      end while (descriptor.flags[1]==0);

      // Check flags
      assert (descriptor.flags == flags)
      else $write("Incorrect flags");
    endtask : sendStatusUpdate  
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and put them into RAM
    task run();
      FrameLinkTransaction transaction;
      Transaction to;
      int ifcNo;                       // Number of output FL interface
      string label;                    // Label of appropriate transaction table

      while (enabled) begin            // Repeat while enabled        
        transMbx.get(to);              // Get transaction from mailbox
        $cast(transaction,to);

        // Get interface number
        ifcNo = $urandom_range(pFlows-1);
        $swrite(label, "Driver %0d", ifcNo);
        
        // Call transaction preprocesing, if is available
        foreach (cbs[i]) cbs[i].pre_tx(to, label);
        // Put Transaction into RAM
        putTransaction(transaction, ifcNo);
//        transaction.display(label);
        
        // Call transaction postprocesing, if is available
        foreach (cbs[i]) cbs[i].post_tx(to, label);
      end
    endtask : run
    
   
    // -- Put Transaction -----------------------------------------------------
    // Puts transaction into RAM 
    task putTransaction(FrameLinkTransaction tr, int ifcNo);
   
      tDescriptor descriptor;
      int unsigned address;
      int descLength;
      int trPtr = 0;

      do begin
        if (tr.data[0].size - trPtr > pMaxDescLength)
          descLength = pMaxDescLength;
        else
          descLength = tr.data[0].size - trPtr;
        $write("Searching free space %0h\n",descLength );
        // Find free space for storing transaction
        while (!findFreeSpace(descLength,address)) waitForSpace();
        $write("Free space at %0h\n",address);

        ramPtr = address + descLength;
        
        // Copy data from FL transaction into the RAM
        for (int i=0;i<descLength; i++)
        begin
          assert(validFlag[address+i]==0)
          else $error("Invalid address %0h",address+i);
          // Copy data
          ram[address+i] = tr.data[0][trPtr]; 
          trPtr++;
          // Set valid bit
          validFlag[address+i] = 1;
        end  
       
        // Send descriptor
        descriptor.address  = address;
        descriptor.length   = descLength;
        descriptor.flags    = 0;
        descriptor.flags[0] = $urandom_range(2);
        if (trPtr < tr.data[0].size) begin 
          descriptor.flags[1] = 0;
          $write("Setting LFF = 0\n");
        end  
        else 
          descriptor.flags[1] = 1;

  //      $write("sending descriptor\n");
        descManager.addDescriptor(ifcNo, descriptor); 
        descQue[ifcNo].push_back(descriptor);
  //      $write("descriptor sended flow:%0d\n",ifcNo);
      end while (trPtr < tr.data[0].size);
      
    endtask : putTransaction
    
    // -- Find Free Space -----------------------------------------------------
    // Finds RAM space for storing transaction data
    function bit findFreeSpace(int trSize, inout int address);
      int freeSpace = 0;
      
//      validFlagDisplay();
      for (int i=ramPtr; i<pRamSize; i++)
      begin
        if (validFlag[i]==0) begin
          freeSpace = 0;
          for (int j=i; j<pRamSize; j++)
          begin
            if (validFlag[j]==0) freeSpace++;
            else break;
//            $write("%0x:freeSpace %0d\n",j,freeSpace);
            if (freeSpace==trSize) begin
              address = i;
              return 1;
            end  
          end
        end
      end
      
      for (int i=0; i<ramPtr; i++)
      begin
        if (validFlag[i]==0) begin
          freeSpace = 0;
          for (int j=i; j<ramPtr; j++)
          begin
            if (validFlag[j]==0) freeSpace++;
            else break;
//            $write("%0x:freeSpace %0d\n",j,freeSpace);
            if (freeSpace==trSize) begin
              address = i;
              return 1;
            end  
          end
        end
      end         

      return 0;         
    endfunction : findFreeSpace

    // -- Wait for space ------------------------------------------------------
    // Waits for new space in RAM
    task waitForSpace();
      while (!newSpaceFlag) @(descManager.desc.desc_cb);
      newSpaceFlag = 0;
    endtask : waitForSpace
    
    // -- Free Space ----------------------------------------------------------
    // Frees space in RAM
    task freeSpace(int address, int length);
      for (int i=0; i<length; i++)
        validFlag[address+i] = 0;
        
      newSpaceFlag = 1;  
    endtask : freeSpace 


    // -- Display functions -----------
    
    // -- RAM Display ---------------------------------------------------------
    // Displays RAM content
    task ramDisplay();
      $write ("-----------------------------------\n");
      $write ("-- RAM\n");
      $write ("-----------------------------------\n");
      
/*      for (int i=0; i<ram.size; i++)
      begin
        if (i%(pPageSize/(pDataWidth/8))==0) $write("\n\n");
        $write("%4x: ",i*(pDataWidth/8));
        for (int j=0; j < ram[i].size; j++)
          $write("%x ",ram[i][j]);
        $write("\n");
      end 
*/      $write ("-----------------------------------\n"); 
    endtask : ramDisplay
    
    // -- Valid Flag Display --------------------------------------------------
    // Displays RAM content
    function void validFlagDisplay();
      int j = 0;
      $write ("-----------------------------------\n");
      $write ("-- Valid Flag\n");
      $write ("-----------------------------------\n");
      
      for (int i=0; i<validFlag.size; i++)
      begin
        if (i%16==0) $write("\n%5x: ",i);
        j++;
        $write("%0x ",validFlag[i]);
      end 
      $write("\n");
      $write ("-----------------------------------\n"); 
    endfunction : validFlagDisplay
    
endclass : TxDmaCtrlDriver
