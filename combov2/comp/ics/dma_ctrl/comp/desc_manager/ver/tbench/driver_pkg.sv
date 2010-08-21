/*
 * driver_pkg.sv: Descriptor Manager Driver
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
 * $Id: driver_pkg.sv 5192 2008-08-25 07:45:17Z xsimko03 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package driver_pkg;
   
   import dm_transaction_pkg::*; // Transaction package
   import sv_common_pkg::*;
   import math_pkg::*;               // Package for math's functions (log2,pow)   
  
  typedef struct{
    longint global_address;
    int local_address;
  } tGlobLocAddr;
  
  
  // --------------------------------------------------------------------------
  // --Descriptor Manager Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to TX Buffer. 
   * Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transaction by calling "sendTransaction" function.
   */
  class descManagerDriver #(pBaseAddr=0, pFlows=4, pBlSize=32, range=4096, pInitOffset=32'h02200000+20'h40000);   
    string    inst;                             // Driver identification
    bit       enabled;                          // Driver is enabled
    tTransMbx transMbx;                         // Transaction mailbox
    DriverCbs cbs[$];                           // Callbacks list
    tGlobLocAddr globLocAddrQue[$];             // Queue for store global and local address
    virtual descManagerWrite.writeDesc_tb #(pBaseAddr,pFlows,pBlSize,range) d_w;
    
    logic [63:0] inicial_address[]      = new [pFlows];                         // Inicial Addresses
    logic [63:0] expected_global_addr[] = new [pFlows];                         // Expected global address
    logic [1:0]  sign[]                 = new [pFlows*range+(pFlows+1)*(range/2)];   // Array of signs
    int range_of_bad_values;                                                    // Range of bad values in RAM
        
    rand bit enFwDelay;   // Enable/Disable delays between transactions
      // Enable/Disable delays between transaction (weights)
      int fwDelayEn_wt             = 1; 
      int fwDelayDisable_wt        = 3;
      
    rand integer fwDelay; // Delay between transactions
      // Delay between transactions limits
      int fwDelayLow          = 0;
      int fwDelayHigh         = 3;
    // ----
    
    // -- Constrains --
    constraint cDelays {
      enFwDelay dist { 1'b1 := fwDelayEn_wt,
                       1'b0 := fwDelayDisable_wt
                     };

      fwDelay inside {
                      [fwDelayLow:fwDelayHigh]
                     };
      }
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   tTransMbx transMbx,
                   virtual descManagerWrite.writeDesc_tb #(pBaseAddr,pFlows,pBlSize,range) d_w
                         );
      logic [31:0] ram_addr;
           
      this.enabled     = 0;            // Driver is disabled by default
      this.d_w         = d_w;          // Store pointer interface 
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier
      this.range_of_bad_values = 0;    // Range of bad values is zero by default
                  
      for (int j=0; j<pFlows;j++)begin 
         this.inicial_address[j]=0;
      end   
   
      range_of_bad_values=range/2;    // Range of bad values is set as half of range
       
      // Array of signs (size of RAM)   
      for (int j=0; j<(pFlows*range+(pFlows+1)*range_of_bad_values); j++)
          this.sign[j]=0; 
          
      this.d_w.writeDesc_cb.WR_ADDR      <= 0;
      this.d_w.writeDesc_cb.WR_BE        <= 8'hFF;
      this.d_w.writeDesc_cb.WR_REQ       <= 0;
      this.d_w.writeDesc_cb.WR_DATA      <= 0;
      this.d_w.writeDesc_cb.BM_ACK       <= 0;
      this.d_w.writeDesc_cb.ENABLE       <= 0;
       
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
    // Send transaction to interface
    task sendTransaction( descManagerTransaction transaction, int write_address, int counter );
      Transaction tr;
      $cast(tr, transaction);
      
      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);

      // Wait before sending transaction
//      if (enFwDelay) repeat (fwDelay) @(d_w.writeDesc_cb);
      
      // Send transaction
      sendData(transaction,write_address, counter);
      // Set not ready
      d_w.writeDesc_cb.WR_REQ       <= 0;
       
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);
     
    endtask : sendTransaction
    
    // -- Private Class Methods --
    
    // -- Wait for BM_REQ ---------------------------------------------------
    // It waits until BM_REQ is active
    task waitForBmReq(); 
      do begin
        @(d_w.writeDesc_cb.BM_REQ); 
        if(d_w.writeDesc_cb.BM_REQ==1) begin
          checkBmReq();
          break;
        end
                
      end while (1); 
    endtask : waitForBmReq
    
    // -- Check BM_REQ ---------------------------------------------------
    // It checks BM_REQ is active
    task checkBmReq();
      tGlobLocAddr addressInfo;
      
      if (d_w.writeDesc_cb.BM_REQ) begin
        addressInfo.global_address = d_w.writeDesc_cb.BM_GLOBAL_ADDR;
        addressInfo.local_address = d_w.writeDesc_cb.BM_LOCAL_ADDR;
        globLocAddrQue.push_back(addressInfo);
        
        //$write("add to fifo>>Global:%x, Local:%x\n",addressInfo.global_address, addressInfo.local_address); // display adding to fifo
        
        @(d_w.writeDesc_cb); 
        d_w.writeDesc_cb.BM_ACK <= 1;            // BM_ACK signal is set
        @(d_w.writeDesc_cb); 
        d_w.writeDesc_cb.BM_ACK <= 0;            // after one clock BM_ACK signal is zero 
      end
    endtask : checkBmReq  
    
    //-- Inicialization ------------------------------------------------------ 
    // Every descriptor space has a inicial address
      task inicial();
      logic [31:0] address =0;
      logic [log2(pFlows)-1:0] offset; 
      int m=0; 
      int ram=range_of_bad_values;
      longint global=range_of_bad_values;
      int block=0;
      
      for (int k=0;k<pFlows;k++)begin     // Offset is the main part of address <=> counter
                  
         address=pInitOffset+k*8;
  
         d_w.writeDesc_cb.WR_ADDR <= address;            // Set WR_ADDR Signal 
         d_w.writeDesc_cb.WR_DATA <= ram;                // Set WR_DATA Signal 
         inicial_address[k]=global;                      // Inicial values 
         expected_global_addr[k]=global;
         ram+=range_of_bad_values+range; 
         global+=range_of_bad_values+range;
         @(d_w.writeDesc_cb);
      end
      
    endtask : inicial
    
    //-- Generate Descriptors ---------------------------  
    // generDesc - generate descriptors of all types
    task generDesc (longint global_address, int length, inout logic [63:0] dataToSend, int desc);
      logic[63:0] new_value;
      int m=1,j=0;
            
      do 
        global_address++;
      while(global_address%length!=0);  // new global address is the nearest multiple of length 
      
      new_value=global_address;
            
      // generate descriptor type 1
      if (desc==1) begin
        dataToSend[0]=1;
        for (int i=1;i<64;i++)
          dataToSend[i]=new_value[m++];  
      end
      // generate descriptor type 0 after appears decriptor type 1
      else if (desc==0)begin
        for (int i=0;i<12;i++)
          dataToSend[i]=0;
        for (int i=12;i<64;i++)
           dataToSend[i]=new_value[m++];  
      end
      // generate descriptor type 1 with inicial value
      else if (desc==2)begin
        while (global_address>inicial_address[j]) j++;
        new_value=inicial_address[j-1];
        expected_global_addr[j-1]=inicial_address[j-1];

        dataToSend[0]=1;
        for (int i=1;i<64;i++)
          dataToSend[i]=new_value[m++];  
      end
      
    endtask : generDesc
    
    //-- Array of Signs -------------------------------------------  
    // create the array of signs
    task setSign();
      int j=0;
      int flow=0;
      
      // boundaries of flows space     
      int bound1= flow*(range_of_bad_values+range);
      int bound2= range_of_bad_values + flow*(range_of_bad_values+range);
      int bound3= range+range_of_bad_values+flow*(range_of_bad_values+range)-9;
      int bound_final= pFlows*range+(pFlows+1)*range_of_bad_values;
      // signs are set
      do begin
        if(j>=bound1 && j<bound2)sign[j]=3;
        if(j>=bound2 && j<bound3)begin
          if(j%70==0) begin
                        if (j>=bound3-pBlSize*8) sign[j]=0;
                        else sign[j]=1;
          end              
          else sign[j]=0;
        end  
        if(j==bound3+1) begin
          sign[j]=2;
          flow++;
          bound1= flow*(range_of_bad_values+range);
          bound2= range_of_bad_values + flow*(range_of_bad_values+range);
          bound3= range+range_of_bad_values+flow*(range_of_bad_values+range)-9;
        end
        j++;
      end while((j-1)!= bound_final);
      
      // display array of signs 
     // for(int i=0; i<bound_final; i++) 
      //  $write("%d:  %d, ",i,sign[i]);
    endtask : setSign
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      longint global_address;                   // global address
      int local_address,write_address;          // local address, write address
      int length;                               // length
      logic [pFlows-1:0] enable;                // ENABLE
      descManagerTransaction transaction;       
      Transaction to;
      logic [63:0] dataToSend = 0;              // Data to Send
      int indicate=0;                           // indicate the state, when appers descriptor type 1
      int desc;                                 // indicate what type of descriptor is generate
      tGlobLocAddr addressInfo;
      
      // Array of Signs is create
      setSign();                                   
      @(d_w.writeDesc_cb);          
      
      // Inicial Phase
      d_w.writeDesc_cb.WR_REQ <= 1; 
      inicial();
      d_w.writeDesc_cb.WR_REQ <= 0; 
      
      for(int i=0; i<pFlows; i++) enable[i]=1;
           
      while (enabled)begin
        // Enable signal id set to 1 for each flow
        d_w.writeDesc_cb.ENABLE <= enable;
        // Waiting for active signal BM_REQ        
        if (!globLocAddrQue.size()) waitForBmReq();   
      
        // we can work with output signals now
        addressInfo = globLocAddrQue.pop_front;
        global_address = addressInfo.global_address; 
        local_address = addressInfo.local_address;
        length = d_w.writeDesc_cb.BM_LENGTH/8;
      
        indicate=0;
        
        for (int i=0; i<pFlows; i++) 
          if (global_address==expected_global_addr[i]) begin
            expected_global_addr[i]+=length*8;
            indicate=1;
            break;
          end
         
        if (!indicate) begin
          $write("Unexpected global address: %x, expected ", global_address);
          foreach (expected_global_addr[i]) $write("%x ",expected_global_addr[i]);
          $write("\n");
          $stop;
        end  
        
        $write("global: %x,  local:  %x,  length:  %d\n",global_address,local_address,length);
       
        write_address= local_address-pBaseAddr;
        indicate=0;                             // indicate is zero - there is no descritor type 1
        
        // we need number of descriptors == length
        for (int i=0; i<length; i++) begin
          
          if (!enabled) break;
          
             //$write("global_address:  %x\n",global_address);
             // sign = 0
             if (sign[global_address]==0)begin
               if(indicate==0) begin          
                 // we take transaction from mailbox - only if descriptor is type 0 and indicate is 0
                 transMbx.get(to);              // Get transaction from mailbox
                 $cast(transaction,to);
                 assert(randomize());
                 sendTransaction(transaction,write_address,i);  // Send Transaction
                 //transaction.display("DRIVER"); // Display Transaction sended by Driver
               end
               else begin                       // descriptor type 1 appears, we can't take transaction from mailbox
                 desc=0;                        // we need descriptor type 0
                 getAddress(write_address,i);
                 generDesc(global_address, length*8, dataToSend, desc);
                 global_address+=8; 
                 d_w.writeDesc_cb.WR_DATA <= dataToSend; 
                 @(d_w.writeDesc_cb); 
               end
               global_address+=8;
             end
             // sign = 1
             else if (sign[global_address]==1) begin
               desc=1;                          // we need descriptor type 1
               if (indicate==0) $write("Descriptor type 1!!\n");
               getAddress(write_address,i);
               generDesc(global_address, length*8, dataToSend, desc);
               global_address+=8; 
                if (indicate==0) $write("dataToSend:  %h\n",dataToSend);
               d_w.writeDesc_cb.WR_DATA <= dataToSend;
               indicate++;                      // increases indicate   
               @(d_w.writeDesc_cb);   
             end
             // sign = 2 
             else if (sign[global_address]==2) begin
               desc=2;                          // we need descritor type 1
               if (indicate==0)$write("Descriptor type 1 + END OF BLOCK!!\n");
               getAddress(write_address,i);
               generDesc(global_address, length*8, dataToSend, desc);
               global_address+=8;
               if (indicate==0)$write("dataToSend:  %h\n",dataToSend);
               d_w.writeDesc_cb.WR_DATA <= dataToSend;  
               indicate++;
               @(d_w.writeDesc_cb);
             end
             // sign = 3
             else begin
               $write("BAD ACCESS !!!\n");
               $stop;
             end  
             d_w.writeDesc_cb.WR_REQ <= 0; 
             checkBmReq();           
        end  // end for
        
      end // end while
      
    endtask : run
    
    // -- Get Address ---------------------------------------------------------
    // Make address of transaction 
    task getAddress(int write_address,int counter);
       logic [31:0] address =0;
       
       address=write_address+counter*8;           
        
       //$write("Address:  %x\n",address);                // Display Address
       d_w.writeDesc_cb.WR_REQ <= 1;
       d_w.writeDesc_cb.WR_ADDR <= address;          // Set WR_ADDR Signal 
    endtask : getAddress     
              
    // -- Send transaction data -----------------------------------------------
    // Send transaction data
    task sendData(descManagerTransaction tr, int write_address, int counter);
    logic [63:0] dataToSend = 0;    
                
        getAddress(write_address,counter);
         
        for (int i=0;i<64; i++)
        dataToSend[i]=tr.data[i];
            
        d_w.writeDesc_cb.WR_DATA <= dataToSend;  
            
        @(d_w.writeDesc_cb); 
              
    endtask : sendData

  endclass : descManagerDriver 
endpackage : driver_pkg  


   
