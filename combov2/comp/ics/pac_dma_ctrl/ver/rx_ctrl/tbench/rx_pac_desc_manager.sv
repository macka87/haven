/*
 * rx_pac_desc_manager.sv: Descriptor Download manager for RX DMA Controller
 * Copyright (C) 2009 CESNET
 * Author(s): Marcela Šimková <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: rx_pac_desc_manager.sv 10127 2009-08-06 11:17:41Z xsimko03 $
 *
 * TODO:
 *
 */

    import test_pkg::*;
   
  // --------------------------------------------------------------------------
  // -- Descriptor Manager Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to descriptor FIFO 
   * interface. Descriptors are stored by 'descQue'(Queue) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. 
   */
  class RxDescManager #(int pFlows = 2, int pRamSize = 1024, int pMaxSizeOfPacket = 1520, int pBufferDataWidth = 64);
    
    // -----------------------------
    // -- Private Class Atributes --
    // -----------------------------
    string  inst;                               // Modul identification
    bit  enabled;                               // Modul is enabled
    logic[63:0]  descManQueue[$];               // Descriptor Manager Queue
    logic[63:0]  monitorQueue[][$];             // Monitor Queues
    
    // Descriptor Manager interface 
    virtual iPacDmaCtrl.desc_tb #(pFlows) desc;
    
    // ----
    rand bit enDelay;   // Enable/Disable DO_VLD delay
      // Enable/Disable DO_VLD delay (weights)
      int delayEn_wt             = 1; 
      int delayDisable_wt        = 3;

    rand int delay; // DO_VLD delay
      // DO_VLD delay limits
      int delayLow          = 0;
      int delayHigh         = 3;
    // ----
   
    // -- Constrains --
    constraint cDelays {
      enDelay dist { 1'b1 := delayEn_wt,
                     1'b0 := delayDisable_wt
                   };

      delay inside {
                    [delayLow:delayHigh]
                   };
         
      }
    
    // -------------------
    // -- Class Methods --
    // -------------------
    
    // -- Constructor ---------------------------------------------------------
    // Create Descriptor Manager object 
    function new ( string inst, 
                   virtual iPacDmaCtrl.desc_tb #(pFlows) desc
                   );
      
      logic[63:0] descriptor;          // Half part of descriptor
      logic[63:0]  counter=0;          // Counter of packets with pMaxSizeOfPacket size in RAM 
            
      this.enabled     = 0;            // Modul is disabled by default
      this.inst        = inst;         // Store Modul identifier
      this.desc        = desc;         // Store pointer interface 
      
      this.desc.desc_cb.DESC_DO    <= 0;
      this.desc.desc_cb.DESC_DO_VLD<= 0;
      this.desc.desc_cb.DESC_EMPTY <= 0;
      
      monitorQueue =new[pFlows];       // Monitor Queues store used descriptors and propagate them to Monitor if needed
       
      // Descriptor Queue is filled up with descriptors
      for (int i=0; i<(pRamSize/(pMaxSizeOfPacket/(pBufferDataWidth/8))); i++)begin
        descriptor[31:0] = pMaxSizeOfPacket;
        if (i%10==0) descriptor[63:32] = 3;
        else descriptor[63:32] = 2;
        descManQueue.push_back(descriptor);
        descriptor[63:0]=counter;
        descManQueue.push_back(descriptor);
        counter+=pMaxSizeOfPacket;
      end
    endfunction: new          
    
    // -- Enable Descriptor Manager -------------------------------------------
    // Enable Descriptor Manager and runs Descriptor Manager process
    task setEnabled();
      enabled = 1; // Descriptor Manager Enabling
      fork         
        run();     // Creating Modul subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Descriptor Manager ------------------------------------------
    // Disable Descriptor Manager
    task setDisabled();
      enabled = 0; // Descriptor Manager Disabling
    endtask : setDisabled
  
    // -- Run Descriptor Manager ----------------------------------------------
    // Take descriptor from queue and generate them to interface
    task run();
      int flow;
      while (enabled) begin                     // Repeat while enabled   
        waitForDescRead();                      // Waiting for DESC_READ
        flow = desc.desc_cb.DESC_ADDR;          // Number of used interface
        waitForNotEmpty(flow);                  // Set DESC_EMPTY
        readDescManQueue(descManQueue.pop_front(),flow);  // Send Descriptor
      end
    endtask : run
    
    // -- Wait For Desc Read --------------------------------------------------
    // Waits until DESC_READ
    task waitForDescRead();
      while (!desc.desc_cb.DESC_READ) 
        @(desc.desc_cb);
    endtask : waitForDescRead
    
    // -- Wait For Not Empty --------------------------------------------------
    // Waits while descQue is empty
    task waitForNotEmpty(int flow);
      int rand_value;

      rand_value = $urandom_range(0,10);

      if(rand_value == 0)begin
        desc.desc_cb.DESC_EMPTY[flow] <= 1;
        #(1000*CLK_PERIOD);
        while (descManQueue.size()==0) @(desc.desc_cb);
        desc.desc_cb.DESC_EMPTY[flow] <= 0;     
      end
      else begin  
        desc.desc_cb.DESC_EMPTY[flow] <= 1;
        while (descManQueue.size()==0) @(desc.desc_cb);
        desc.desc_cb.DESC_EMPTY[flow] <= 0;
      end
      endtask : waitForNotEmpty
    
    // -- Read Descriptor Manager Queue ---------------------------------------
    // Read descriptor from Descriptor Manager Queue and sends it to DUT and to Monitor Queue
    task readDescManQueue(logic[63:0] descriptor, int flow);
      // send descriptor to DUT
      desc.desc_cb.DESC_DO <= descriptor;
      randomDoVldWait();
      desc.desc_cb.DESC_DO_VLD <= 1; 
      @(desc.desc_cb);
      desc.desc_cb.DESC_DO <= 0;
      desc.desc_cb.DESC_DO_VLD <= 0;
      // send descriptor to monitorQueue
      monitorQueue[flow].push_back(descriptor); 
    endtask : readDescManQueue
    
    // -- Read Monitor Queue --------------------------------------------------
    // Read descriptor from Monitor Queue and sends it back to Descriptor Manager Queue 
    task readMonitorQueue(inout logic[127:0] descriptor, int flow);
      logic[63:0] desc1,desc2;

      desc1 = monitorQueue[flow].pop_front();
      descManQueue.push_back(desc1);
      desc2 = monitorQueue[flow].pop_front();
      descManQueue.push_back(desc2);
      
      descriptor[63:0]= desc1;
      descriptor[127:64] = desc2;
      
      // display size of monitor queues
      //$write("FLOW:  %d SIZE OF MONITOR QUEUE: %d\n",flow,monitorQueue[flow].size());
    endtask : readMonitorQueue 
    
    // -- Random wait ---------------------------------------------------------
    // Random wait during sending descriptor to controller
    task randomDoVldWait();
      if (enDelay)
        repeat (delay)
          @(desc.desc_cb);
    endtask : randomDoVldWait

  endclass : RxDescManager
