/*
 * driver_pkg.sv: txBuffer Driver
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
 * $Id: driver_pkg.sv 5083 2008-08-20 13:21:28Z solanka $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package driver_pkg;
   
   import txbuff_transaction_pkg::*; // Transaction package
   import sv_common_pkg::*;
   import math_pkg::*;               // Package for math's functions (log2,pow)   
  
  // --------------------------------------------------------------------------
  // --tx Buffer Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to TX Buffer. 
   * Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transaction by calling "sendTransaction" function.
   */
  class txBuffDriver #(int pDataWidth=64, int pBlSize=512, int pFlows=2, int pTotFlSize=16384, int pSLen=16);   
   
    // -- Private Class Atributes --
    string    inst;                             // Driver identification
    bit       enabled;                          // Driver is enabled
    tTransMbx transMbx;                         // Transaction mailbox
    DriverCbs cbs[$];                           // Callbacks list
    virtual txBuffWrite.txbuff_write_tb #(pDataWidth,pBlSize,pFlows,pTotFlSize,pSLen) b_w;
    
    int new_len_count[] = new [pFlows];         // TX_NEWLEN values     
    int rel_len_count[] = new [pFlows];         // TX_RELLEN values
    int difference[] = new [pFlows];            // aktual difference between sum of new_len_count[] and sum of rel_len_count[] 
    logic bad_block[]= new[pFlows];             // indicate which block is full        
    int boundary;                               // limit for difference[]
    
    logic [(pFlows*16)-1:0] rel_len;            // store TX_RELLEN signal          
    
    int  address_count[] = new [pFlows];        // Address counter        
    
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
                   virtual txBuffWrite.txbuff_write_tb #(pDataWidth,pBlSize,pFlows,pTotFlSize,pSLen) b_w
                         );
      this.enabled     = 0;            // Driver is disabled by default
      this.b_w         = b_w;          // Store pointer interface 
      this.transMbx    = transMbx;     // Store pointer to mailbox
      this.inst        = inst;         // Store driver identifier
      
      for (int j=0; j<pFlows;j++) begin
         this.address_count[j]=0;
         this.new_len_count[j]=0;
         this.rel_len_count[j]=0;
         this.difference[j]=0; 
         this.bad_block[j]=0; 
      end   
      
      this.rel_len=0;
      this.boundary=4096; 
        
      this.b_w.txbuff_write_cb.WR_ADDR      <= 0;
      this.b_w.txbuff_write_cb.WR_BE        <= 8'hFF;
      this.b_w.txbuff_write_cb.WR_REQ       <= 0;
      this.b_w.txbuff_write_cb.WR_DATA      <= 0;
      this.b_w.txbuff_write_cb.TX_NEWLEN    <= 0;
      this.b_w.txbuff_write_cb.TX_NEWLEN_DV <= 0;
      
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
    // Send transaction to Frame Link interface
    task sendTransaction(txBuffTransaction transaction,int header_size,int data_size,int header_round_size,int frame_round_size,int block);
      Transaction tr;
      $cast(tr, transaction);
      
      // Call transaction preprocesing, if is available
      foreach (cbs[i]) cbs[i].pre_tx(tr, inst);

      // Wait before sending transaction
      if (enFwDelay) repeat (fwDelay) begin
        relLenCount();
        @(b_w.txbuff_write_cb);
        end
      // Send transaction
      sendData(transaction,header_size,data_size,header_round_size,frame_round_size,block);
      // Set not ready
      b_w.txbuff_write_cb.WR_REQ       <= 0;
       
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);
     
    endtask : sendTransaction
    
    // -- Private Class Methods --
    
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      txBuffTransaction transaction;
      Transaction to;
      int diff_count=0;                // Number of flows, where difference[flow]>=4016 
      int header_size, data_size, transaction_size;
      int header_round_size,frame_round_size;
      int count_to_round;
      int block;
      
      @(b_w.txbuff_write_cb);          // Wait for clock
      while (enabled) begin            // Repeat while enabled
        while (transMbx.num()==0) begin
          relLenCount();
          @(b_w.txbuff_write_cb);
        end 
        
        // Get transaction from mailbox
        transMbx.get(to);              
        $cast(transaction,to);
        assert(randomize());
        
        for (int i=0;i<transaction.packetCount;i=i+2) begin
          // Size of header part 
          header_size=transaction.data[i].size;
          //$write("header_size: %d\n",header_size);
          // Size of frame part
          data_size=transaction.data[i+1].size;
          //$write("data_size: %d\n",data_size);
        end
      
        count_to_round=pDataWidth/8;
        while((4+header_size)>count_to_round) count_to_round+=pDataWidth/8;
      
        // Round size
        header_round_size=count_to_round-(4+header_size);
        //$write("round_size for header: %d\n",header_round_size);
        
        count_to_round=pDataWidth/8;
        while(data_size>count_to_round) count_to_round+=pDataWidth/8;
         
        // Round size
        frame_round_size=count_to_round-data_size;
        //$write("frame_round_size: %d\n",frame_round_size);
        //whole transaction size
        transaction_size=header_size+data_size+4+frame_round_size+header_round_size;
        //$write("transaction_size : %d\n",transaction_size);


        // Check if the transaction is not larger than TX_BUFFER size
        assert(transaction_size <= boundary)
        else begin
          $error("Transaction size (%.1d) cannot be larger than the TX buffer size (%.1d)\n", transaction_size,  boundary);
          $stop;
        end
        
        do begin 
          block=$urandom_range(pFlows-1);

          if (difference[block]+transaction_size > boundary)
            bad_block[block]=1;
          else
            bad_block[block]=0; 
           
          diff_count=0;   
          for(int i=0;i<pFlows;i++)
           if(bad_block[i]==1) diff_count++;
          
          // all blocks are full
          if (diff_count==pFlows)begin
            //$write("ONLY REL_LEN\n");  
            relLenCount();
            @(b_w.txbuff_write_cb);
          end    
        end while(bad_block[block]==1);
        
        transaction.num_block_addr=block;
        sendTransaction(transaction,header_size,data_size,header_round_size,frame_round_size,block);  // Send Transaction
        //transaction.display("DRIVER"); // Display Transaction sended by Driver
                      
      end // end while
    endtask : run
    
    // -- RelLenCount ---------------------------------------------------------
    // detect TX_RELLEN signal
    task relLenCount();
    static int cnt = 0;
    int block;
    logic [15:0] rel;  // actual value of rel_len for one flow
    int m=0;
    
    if (b_w.txbuff_write_cb.TX_RELLEN_DV) begin
      rel_len = b_w.txbuff_write_cb.TX_RELLEN;
            
      for (int j=0; j<pFlows; j++)begin
        m=0;
        if (b_w.txbuff_write_cb.TX_RELLEN_DV[j]==1) begin
          block = j;
          // actual value of rel_len for one flow
          for(int i=block*16; i<(block+1)*16; i++)
            rel[m++]=rel_len[i]; 
          // set difference
          rel_len_count[block]= rel;  
          difference[block]-=rel;
          $write("cnt: %d: block:  %d,  rel_len_count:  %d,  difference:  %d\n",cnt, block,rel_len_count[block],difference[block]);
          cnt++;
        end  
      end  
    end
    endtask : relLenCount
    
    // -- Get Address ---------------------------------------------------------
    // Make address of transaction 
    task getAddress(inout int address_count,int block);
       logic [31:0] address =0;
       logic [log2(pBlSize)-1:0] offset =0;
       logic [log2(pFlows)-1:0]flows =0;
       int pre;           
       int m=0;
                  
       offset=address_count;            // Offset is the main part of address <=> counter
       flows=block;                     // Flow part off address 
       pre=log2(pDataWidth/8); 
                  
       for(int i=0;i<pre;i++)           // Ignore bits
       address[m++]=0;
                  
       for(int i=0;i<log2(pBlSize);i++) // Bits from pre to log2(BLOCK_SIZE) are offset part
       address[m++]=offset[i];
                  
       for(int i=m; i<14;i++)           // Ignore bits
       address[m++]=0;
                  
       for(int i=0; i<log2(pFlows);i++) // Bits from 15 to log2(FLOWS) are flows part
       address[m++]=flows[i];
                  
       for(int i=m; i<31;i++)           // Ignore bits
       address[m++]=0;
                  
      // $write("Address:  %x\n",address);                // Display Address
       b_w.txbuff_write_cb.WR_ADDR <= address;          // Set WR_ADDR Signal 
        
    endtask : getAddress
                
                
    // -- Send transaction data -----------------------------------------------
    // Send transaction data
    task sendData(txBuffTransaction tr,int header_size,int data_size,int header_round_size,int frame_round_size,int block);
      static int cnt = 0;
      int frame_size,round_size;
      int t,g,counter,m;
      int bitcounter_of_header, bitcounter_of_frame, bitcounter_of_datasize;
      int block;
      logic [(pFlows*16)-1:0] size=0;
      logic [15:0] vel;
      
            
      logic [pDataWidth-1:0] dataToSend = 0;
      logic [15:0] frame = 0;
      logic [15:0] header = 0;
      logic [7:0] data = 0;
      
      //generate Frame
      header=header_size;
      round_size=header_round_size;
      
      frame_size=header_size+data_size+round_size+4;
      frame=frame_size;
      //$write("frame_size: %d\n",frame_size);
      // Set WR_REQ signal
      b_w.txbuff_write_cb.WR_REQ <= 1;
      
      //SIZE ITEMS AND HEADER`S DATA
      bitcounter_of_header=0; bitcounter_of_datasize=0; t=0; counter=0; g=0;
      do begin 
            // Size of frame is stored to dataToSend
            if (bitcounter_of_header<16) dataToSend[bitcounter_of_datasize]=frame[bitcounter_of_datasize]; 
            // Size of header is stored to dataToSend
            if (bitcounter_of_header<32 && bitcounter_of_header>=16) dataToSend[bitcounter_of_datasize]=header[t++]; 
            // Header's data 
            if (bitcounter_of_header>=32) begin
              
              // Round zero bits
              if(bitcounter_of_header>=(tr.data[0].size*8+32)) dataToSend[bitcounter_of_datasize]=0;
              // Data
              else begin
                data=tr.data[0][counter];
                dataToSend[bitcounter_of_datasize]=data[g++];
                
                if (g==8) begin
                  counter++;g=0;
                end   
                if (counter==header_size) counter=0; 
              end
            end  
            
            bitcounter_of_datasize++; // this counter counts to pDataWidth bits
            bitcounter_of_header++;   // this counter counts to whole header size
            
            // Ends pDataWidth bit transaction
            if ((bitcounter_of_header%pDataWidth)==0)begin
                bitcounter_of_datasize=0;                    // Counter goes to null    
                //$write("dataToSend: %x\n",dataToSend);       // Display 64 bit data
                getAddress(address_count[block],block);      // Get new Address
                address_count[block]++;                      // Address counter is incremented
                b_w.txbuff_write_cb.WR_DATA <= dataToSend;   // Set WR_DATA signal
                relLenCount();
                @(b_w.txbuff_write_cb); 
                
                b_w.txbuff_write_cb.WR_DATA <= 0;
            end  
      end while (bitcounter_of_header!=(header_size*8+32+round_size*8)); 
      
      // FRAME DATA
      bitcounter_of_frame=0; bitcounter_of_datasize=0; t=0; counter=0; g=0;
      
      round_size=frame_round_size;
      //$write("round_size for data: %d\n",round_size);      
      do begin
        // Round zero bits
        if(bitcounter_of_frame>=(tr.data[1].size*8)) dataToSend[bitcounter_of_datasize]=0;
        // Data
        else begin
          data=tr.data[1][counter];
          dataToSend[bitcounter_of_datasize]=data[g++];
                
          if (g==8) begin
            counter++;g=0;
          end  
          if (counter==data_size) counter=0; 
        end
                        
        bitcounter_of_datasize++;  // this counter counts to 64 bits
        bitcounter_of_frame++;     // this counter counts to whole frame data size
        
        // Ends pDataWidth bit transaction    
        if ((bitcounter_of_frame%pDataWidth)==0)begin   
          bitcounter_of_datasize=0;                     // Counter goes to null
          //$write("dataToSend: %x\n",dataToSend);        // Display pDataWidth bit data
          getAddress(address_count[block],block);       // Get new Address
          address_count[block]++;                       // Address counter is incremented
          b_w.txbuff_write_cb.WR_DATA <= dataToSend;    // Set WR_DATA signal
          relLenCount();
          @(b_w.txbuff_write_cb); 
          b_w.txbuff_write_cb.WR_DATA <= 0;
        end
      end while (bitcounter_of_frame!=(data_size*8+round_size*8));
      
      // Set signals
      b_w.txbuff_write_cb.WR_REQ <= 0;
      
      vel = frame_size+round_size;
      new_len_count[block] = vel;
      difference[block] += vel;
      $write("cnt:  %d, block:  %d, new_len_count:  %d, difference:  %d\n",cnt, block, new_len_count[block],difference[block]);
      cnt++;
            
      b_w.txbuff_write_cb.TX_NEWLEN_DV[block] <= 1;
      m=0;
      for (int i=block*16; i<(block+1)*16; i++)
        size[i] = vel[m++];
         
      b_w.txbuff_write_cb.TX_NEWLEN <= size;
      relLenCount();
      @(b_w.txbuff_write_cb);
      b_w.txbuff_write_cb.TX_NEWLEN <= 0;
      b_w.txbuff_write_cb.TX_NEWLEN_DV<= 0;
        
  endtask : sendData

  endclass : txBuffDriver 
endpackage : driver_pkg  


   
