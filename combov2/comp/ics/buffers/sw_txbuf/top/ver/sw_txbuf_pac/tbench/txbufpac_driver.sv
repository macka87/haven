/*
 * txbufpac_driver.sv: txBuffer Driver
 * Copyright (C) 2009 CESNET
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
 * $Id: txbufpac_driver.sv 8893 2009-06-20 17:09:47Z xsimko03 $
 *
 * TODO:
 *
 */
   
  import math_pkg::*;               // Package for math's functions (log2,pow) 
  import sv_txbufpac_pkg::*; 
  
  // --------------------------------------------------------------------------
  // --TX Buffer Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to TX Buffer. 
   * Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transaction by calling "sendTransaction" function.
   */
  class txBuffPacDriver #(int pDataWidth=64, int pBlSize=512, int pFlows=2, int pTotFlSize=16384);   
   
    // -- Private Class Atributes --
    string    inst;                             // Driver identification
    bit       enabled;                          // Driver is enabled
    tTransMbx transMbx;                         // Transaction mailbox
    DriverCbs cbs[$];                           // Callbacks list
    virtual txBuffWrite.txbuff_write_tb #(pDataWidth,pBlSize,pFlows,pTotFlSize) b_w;
    
    int new_len_count[] = new [pFlows];         // TX_NEWLEN values     
    int rel_len_count[] = new [pFlows];         // TX_RELLEN values
    int difference[] = new [pFlows];            // aktual difference between sum of new_len_count[] and sum of rel_len_count[] 
    logic bad_block[]= new[pFlows];             // indicate which block is full 
    int rest[] = new [pFlows];                  // number of free Bytes in pDataWidth for last address in flow       
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
                   virtual txBuffWrite.txbuff_write_tb #(pDataWidth,pBlSize,pFlows,pTotFlSize) b_w
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
         this.rest[j]=0;
      end  
      
      this.rel_len=0;
      this.boundary=4096; // size of buffer
        
      this.b_w.txbuff_write_cb.WR_ADDR      <= 0;
      this.b_w.txbuff_write_cb.WR_BE        <= 0;
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
    
    // -- Private Class Methods --
        
    // -- Run Driver ----------------------------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      txBuffTransaction transaction;
      Transaction to;
      int diff_count=0;                // Number of flows, where difference[flow]>=4016 
      int block;
      int data_size, transaction_size;
      
      @(b_w.txbuff_write_cb);          // Wait for clock
      while (enabled) begin            // Repeat while enabled
        while (transMbx.num()==0) begin  // empty mailbox - only rellen, without newlen
          relLenCount();
          @(b_w.txbuff_write_cb);
        end 
        
        // Get transaction from mailbox
        transMbx.get(to);              
        $cast(transaction,to);
        assert(randomize());
        
        data_size=transaction.data[0].size;
        
        transaction_size=pDataWidth/8;
        while(data_size>transaction_size) transaction_size+=pDataWidth/8;
        
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
            relLenCount();
            @(b_w.txbuff_write_cb);
          end    
        end while(bad_block[block]==1);
        
        transaction.num_block_addr=block;
        sendTransaction(transaction);  // Send Transaction
        //transaction.display("DRIVER"); // Display Transaction sended by Driver
      end // end while
    endtask : run
    
    // -- Send Transaction ----------------------------------------------------
    // Send transaction to Frame Link interface
    task sendTransaction(txBuffTransaction transaction);
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
      sendData(transaction);
      // Set not ready
      b_w.txbuff_write_cb.WR_REQ <= 0;
       
      // Call transaction postprocesing, if is available
      foreach (cbs[i]) cbs[i].post_tx(tr, inst);
     
    endtask : sendTransaction
    
    // -- RelLenCount ---------------------------------------------------------
    // detect TX_RELLEN signal
    task relLenCount();
    static int cnt = 0;
    int block;          // number of flow         
    logic [15:0] rel;   // actual value of rel_len for one flow
    int relfull;        // aligned rel_len
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
          rel_len_count[block]= rel; //real rel_len
          
          relfull=rel; 
          //aligned rel_len
          if(relfull%8!=0) relfull=(relfull/8+1)*8;
          else relfull=(relfull/8)*8;
           
          //difference is important to detect, if the buffer is full or not          
          difference[block]-=relfull;
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
                  
       for(int i=0; i<log2(pFlows);i++) // Bits from 14 to log2(FLOWS) are flows part
       address[m++]=flows[i];
                  
       for(int i=m; i<31;i++)           // Ignore bits
       address[m++]=0;
                  
      // $write("Address:  %x\n",address);                // Display Address
       b_w.txbuff_write_cb.WR_ADDR <= address;          // Set WR_ADDR Signal 
        
    endtask : getAddress
  
    // -- Send transaction data -----------------------------------------------
    // Send transaction data
    task sendData(txBuffTransaction tr);
      int m;
      logic data[];  // Data to write
      static int cnt = 0;
      logic [(pFlows*16)-1:0] size=0;
      logic [15:0] vel;                 // new_len
      int velfull;                      // aligned new_len
      int block = tr.num_block_addr;    // number of flow
      int notfree=0;                    // transaction size mod 64
      int numberOfFull=0;               // transaction size div 64
      int numberOfPart=0;               // counter of numberOfFull
      logic [7:0] notfreetosend=0;      // byte enable
      int c=0;                          // counter of words in transaction
      int random_value=0;               // random value - whole transaction is send or parts of transaction (BE)
      int noparts=0;                    
      int position=0;                   
       
      numberOfFull=(tr.data[0].size*8)/64; // transaction size div 64
      notfree=(tr.data[0].size*8)%64;      // transaction size mod 64
      
      // Set WR_REQ signal
      b_w.txbuff_write_cb.WR_REQ <= 1;
      
      data = new[tr.data[0].size*8];
      
      // transaction data are copied to array data
      for (integer i=0; i < tr.data[0].size; i++) 
        for (integer j=0; j < 8; j++)
          data[8*i+j] = tr.data[0][i][j]; 
      
      // transaction size, words can be sent complete (BE = 11111111) or stepwise (different BE)
      for (int i=0; i<(tr.data[0].size*8); i=i+pDataWidth) begin
      
        numberOfPart++; // counter of numberOfFull
        random_value=$urandom_range(2); // testcases
       
        // words of transaction are send stepwise, ratio is: 3:3:2 
        if (random_value==1) begin   
          logic [pDataWidth-1:0] dataToSend1 = 0;
          logic [pDataWidth-1:0] dataToSend2 = 0;
          logic [pDataWidth-1:0] dataToSend3 = 0;
                            
          getAddress(address_count[block],block);       // Get new Address
          address_count[block]++;                       // Address counter is incremented
          
          // last bytes of transaction are send complete  
          if (numberOfPart>numberOfFull) begin
            for (int j=0; j < pDataWidth; j++)begin
              if (j<notfree) dataToSend1[j] = data[c++];
              else dataToSend1[j] = 0;
            end  
            b_w.txbuff_write_cb.WR_DATA <= dataToSend1;
            
            for (int p=0; p<8; p++)
              if (p<(notfree/8)) notfreetosend[p]=1;
                b_w.txbuff_write_cb.WR_BE <= notfreetosend;
           
            relLenCount();
            @(b_w.txbuff_write_cb); 
            b_w.txbuff_write_cb.WR_DATA <= 0;
          
          end
          // full 8B of transaction
          else begin
            position=0;
            noparts=3;
            for (int j=0; j < pDataWidth; j++)begin
              if ((j>=(position*8)) && (j<((position+noparts)*8)))
                dataToSend1[j] = data[c++];
            end
            //$write("dataToSend: %x\n",dataToSend1);  
            b_w.txbuff_write_cb.WR_DATA <= dataToSend1;
            b_w.txbuff_write_cb.WR_BE <= 8'b00000111; 
            relLenCount();
            @(b_w.txbuff_write_cb); 
            b_w.txbuff_write_cb.WR_DATA <= 0;
        
            position+=noparts;
            noparts=3;
            for (int j=0; j < pDataWidth; j++)begin
              if ((j>=(position*8)) && (j<((position+noparts)*8)))
                dataToSend2[j] = data[c++];
            end
            //$write("dataToSend: %x\n",dataToSend2);  
            b_w.txbuff_write_cb.WR_DATA <= dataToSend2;
            b_w.txbuff_write_cb.WR_BE <= 8'b00111000;
            relLenCount();
            @(b_w.txbuff_write_cb); 
            b_w.txbuff_write_cb.WR_DATA <= 0;
        
            position+=noparts;
            noparts=2;
            for (int j=0; j < pDataWidth; j++)begin
              if ((j>=(position*8)) && (j<((position+noparts)*8)))
                dataToSend3[j] = data[c++];
            end
            //$write("dataToSend: %x\n",dataToSend3);  
            b_w.txbuff_write_cb.WR_DATA <= dataToSend3;
            b_w.txbuff_write_cb.WR_BE <= 8'b11000000;
            relLenCount();
            @(b_w.txbuff_write_cb); 
            b_w.txbuff_write_cb.WR_DATA <= 0;
          end //end part
        end//end random1   
        
        // words of transaction are send stepwise, ratio is: 1:1:1:1:1:1:1:1
        if (random_value==2) begin
          logic [pDataWidth-1:0] dataToSend1 = 0;
          
          getAddress(address_count[block],block);       // Get new Address
          address_count[block]++;                       // Address counter is incremented  
        
          // last bytes of transaction are send complete
          if (numberOfPart>numberOfFull) begin
            for (int j=0; j < pDataWidth; j++)begin
              if (j<notfree) dataToSend1[j] = data[c++];
              else dataToSend1[j] = 0;
            end  
            //$write("dataToSend zvysok 1:1: %x\n",dataToSend1);  
            b_w.txbuff_write_cb.WR_DATA <= dataToSend1;
            
            for (int p=0; p<8; p++)
              if (p<(notfree/8)) notfreetosend[p]=1;
                b_w.txbuff_write_cb.WR_BE <= notfreetosend;
           
            relLenCount();
            @(b_w.txbuff_write_cb); 
            b_w.txbuff_write_cb.WR_DATA <= 0;
          end//end full
          // full 8B of transaction
          else begin
            noparts=1;
            for (int t=0; t<8; t++)begin
              dataToSend1 = 0;
              for (int j=0; j < pDataWidth; j++)begin
                if ((j>=(t*8)) && (j<((t+noparts)*8)))
                  dataToSend1[j] = data[c++];
              end
              //$write("dataToSend: %x\n",dataToSend1);  
              b_w.txbuff_write_cb.WR_DATA <= dataToSend1;
              
              for (int p=0; p<8; p++)
                if (p==t) notfreetosend[p]=1;
                else notfreetosend[p]=0; 
              b_w.txbuff_write_cb.WR_BE <= notfreetosend;
              relLenCount();
              @(b_w.txbuff_write_cb); 
              b_w.txbuff_write_cb.WR_DATA <= 0;
            end  
          end//end part
        end//end rand
        
        // words of transaction are send complete
        if (random_value==0) begin
          logic [pDataWidth-1:0] dataToSend = 0;
               
          // last bytes of transaction 
          if(numberOfPart>numberOfFull) begin
            for (int j=0; j < pDataWidth; j++)begin
              if (j<notfree) dataToSend[j] = data[c++];
              else dataToSend[j] = 0;
            end 
          end
          // bytes of transaction
          else begin
            for (int j=0; j < pDataWidth; j++)
              dataToSend[j] = data[c++];
          end    
        
          //$write("dataToSend v else: %x\n",dataToSend);        // Display pDataWidth bit data
          getAddress(address_count[block],block);       // Get new Address
          address_count[block]++;                       // Address counter is incremented
          b_w.txbuff_write_cb.WR_DATA <= dataToSend;    // Set WR_DATA signal
        
          // WR_BE for last word 
          if(numberOfPart>numberOfFull) begin
            for (int i=0; i<8; i++)
              if (i<(notfree/8)) notfreetosend[i]=1;
            b_w.txbuff_write_cb.WR_BE <= notfreetosend;  
          end 
          // WR_BE for other words
          else b_w.txbuff_write_cb.WR_BE <= 8'hFF;  
           
          relLenCount();
          @(b_w.txbuff_write_cb); 
          b_w.txbuff_write_cb.WR_DATA <= 0;  
        end 
      end 
                
      // newlen part 
      b_w.txbuff_write_cb.WR_REQ <= 0;
      
      vel = tr.data[0].size;
      new_len_count[block] = vel;
      
      // aligned newlen
      velfull=vel;
      if(velfull%8!=0) velfull=(velfull/8+1)*8;
      else velfull=(velfull/8)*8;
      // difference between newlens and rellens     
      difference[block] += velfull;
      $write("cnt:  %d, block:  %d, new_len_count:  %d, difference:  %d\n",cnt, block, new_len_count[block],difference[block]);
      cnt++;
       
      // newlen cannot be valid, if fifo of newlen items is full  
      assert(b_w.txbuff_write_cb.TX_NEWLEN_RDY[block]==1)
      else begin
        $error("Zaplnenie FIFA pre velkosti newlen!\n");
        $stop;
      end
        
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
  endclass : txBuffPacDriver 
 