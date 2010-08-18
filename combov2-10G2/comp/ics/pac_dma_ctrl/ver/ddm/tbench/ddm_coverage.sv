/*
 * \file ddm_coverage.sv
 * \brief Descriptor Download Manager Coverage class
 * \date Copyright (C) 2009 CESNET
 * \author Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: ddm_coverage.sv 11320 2009-09-28 17:54:58Z xsimko03 $
 *
 * TODO:
 *
 */
  
  // --------------------------------------------------------------------------
  // -- DDM Command Coverage for DMA Interface 
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
  class CommandsCoverageDMA #(int pCtrlDmaDataWidth = 16);
  
    // Interface on witch is covering measured
    virtual iDmaCtrl.dma_tb #(pCtrlDmaDataWidth) dma;
    
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic dma_req;
    logic dma_ack;
    logic dma_done;
        
    //-- Covering transactions ------------------------------------------------
    covergroup CommandsCovergroup;
      
      // dma request coverpoint
      dma_req: coverpoint dma_req {
        bins dma_req0 = {0};        
        bins dma_req1 = {1};
        }
      // dma acknowledge coverpoint
      dma_ack: coverpoint dma_ack {
        bins dma_ack0 = {0};        
        bins dma_ack1 = {1};
        }  
      // dma done coverpoint
      dma_done: coverpoint dma_done {
        bins dma_done0 = {0};        
        bins dma_done1 = {1};
        }
     
    option.per_instance=1; // Also per instance statistics
    endgroup
    
    // ------------------------------------------------------------------------
    // Constructor
    function new (virtual iDmaCtrl.dma_tb #(pCtrlDmaDataWidth) dma,
                  string instanceName
                  );
      this.dma = dma;                 // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
    endfunction

    // -- Enable command coverage measures ------------------------------------
    // Enable commands coverage measures
    task setEnabled();
      enabled = 1; // Coverage Enabling
      fork         
        run();     // Creating coverage subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
         
    // -- Disable command coverage measures -----------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable measures
    endtask : setDisabled
   
    // -- Run command coverage measures ---------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      while (enabled) begin            // Repeat while enabled
         @(dma.dma_cb);                // Wait for clock
         // Sample signals values
         dma_req = dma.dma_cb.DMA_REQ;
         dma_ack = dma.dma_cb.DMA_ACK;
         dma_done = dma.dma_cb.DMA_DONE;
         CommandsCovergroup.sample();
      end
    endtask : run
  
    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Command coverage for %s:%d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display    
    
  endclass: CommandsCoverageDMA
  
  // --------------------------------------------------------------------------
  // -- DDM Command Coverage for RX REQ FIFO Interface 
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
  class CommandsCoverageRXREQ #(int pFlows = 4, int pBlockSize = 128);
  
    // Interface on witch is covering measured
    virtual iDdm.rxreq_tb #(pFlows, pBlockSize) rxreq;
    
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic rx_rf_data_vld;
        
    //-- Covering transactions ------------------------------------------------
    covergroup CommandsCovergroup;
      // rx request data valid coverpoint
      rx_rf_data_vld: coverpoint rx_rf_data_vld {
        bins rx_rf_data_vld0 = {0};        
        bins rx_rf_data_vld1 = {1};
        }
    option.per_instance=1; // Also per instance statistics
    endgroup
    
    // ------------------------------------------------------------------------
    // Constructor
    function new (virtual iDdm.rxreq_tb #(pFlows, pBlockSize) rxreq,
                  string instanceName
                  );
      this.rxreq = rxreq;             // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
    endfunction

    // -- Enable command coverage measures ------------------------------------
    // Enable commands coverage measures
    task setEnabled();
      enabled = 1; // Coverage Enabling
      fork         
        run();     // Creating coverage subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
         
    // -- Disable command coverage measures -----------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable measures
    endtask : setDisabled
   
    // -- Run command coverage measures ---------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      while (enabled) begin            // Repeat while enabled
         @(rxreq.rxreq_cb);              // Wait for clock
         // Sample signals values
         rx_rf_data_vld = rxreq.rxreq_cb.RX_RF_DATA_VLD;
         CommandsCovergroup.sample();
      end
    endtask : run
  
    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Command coverage for %s:%d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display    
  endclass: CommandsCoverageRXREQ
  
  // --------------------------------------------------------------------------
  // -- DDM Command Coverage for RX NFIFO Interface 
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
  class CommandsCoverageRXNFIFO #(int pFlows = 4, int pBlockSize = 128);
  
    // Interface on witch is covering measured
    virtual iDdm.rxnfifo_tb #(pFlows, pBlockSize) rxnfifo;
    
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic rx_nfifo_dout_vld;
    logic rx_nfifo_rd;
        
    //-- Covering transactions ------------------------------------------------
    covergroup CommandsCovergroup;
      // rx nfifo data out valid coverpoint
      rx_nfifo_dout_vld: coverpoint rx_nfifo_dout_vld {
        bins rx_nfifo_dout_vld0 = {0};        
        bins rx_nfifo_dout_vld1 = {1};
        }
        
      // rx nfifo read valid coverpoint
      rx_nfifo_rd: coverpoint rx_nfifo_rd {
        bins rx_nfifo_rd0 = {0};        
        bins rx_nfifo_rd1 = {1};
        }
    option.per_instance=1; // Also per instance statistics
    endgroup
    
    // ------------------------------------------------------------------------
    // Constructor
    function new (virtual iDdm.rxnfifo_tb #(pFlows, pBlockSize) rxnfifo,
                  string instanceName
                  );
      this.rxnfifo = rxnfifo;         // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
    endfunction

    // -- Enable command coverage measures ------------------------------------
    // Enable commands coverage measures
    task setEnabled();
      enabled = 1; // Coverage Enabling
      fork         
        run();     // Creating coverage subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
         
    // -- Disable command coverage measures -----------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable measures
    endtask : setDisabled
   
    // -- Run command coverage measures ---------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      while (enabled) begin            // Repeat while enabled
         @(rxnfifo.rxnfifo_cb);              // Wait for clock
         // Sample signals values
         rx_nfifo_dout_vld = rxnfifo.rxnfifo_cb.RX_NFIFO_DOUT_VLD;
         rx_nfifo_rd = rxnfifo.rxnfifo_cb.RX_NFIFO_RD;
         CommandsCovergroup.sample();
      end
    endtask : run
  
    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Command coverage for %s:%d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display    
  endclass: CommandsCoverageRXNFIFO
  
  // --------------------------------------------------------------------------
  // -- DDM Command Coverage for TX NFIFO Interface 
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
  class CommandsCoverageTXNFIFO #(int pFlows = 4, int pBlockSize = 128);
  
    // Interface on witch is covering measured
    virtual iDdm.txnfifo_tb #(pFlows, pBlockSize) txnfifo;
    
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic tx_nfifo_dout_vld;
    logic tx_nfifo_rd;
        
    //-- Covering transactions ------------------------------------------------
    covergroup CommandsCovergroup;
      // tx nfifo data out valid coverpoint
      tx_nfifo_dout_vld: coverpoint tx_nfifo_dout_vld {
        bins tx_nfifo_dout_vld0 = {0};        
        bins tx_nfifo_dout_vld1 = {1};
        }
      // tx nfifo read valid coverpoint
      tx_nfifo_rd: coverpoint tx_nfifo_rd {
        bins tx_nfifo_rd0 = {0};        
        bins tx_nfifo_rd1 = {1};
        }
    option.per_instance=1; // Also per instance statistics
    endgroup
    
    // ------------------------------------------------------------------------
    // Constructor
    function new (virtual iDdm.txnfifo_tb #(pFlows, pBlockSize) txnfifo,
                  string instanceName
                  );
      this.txnfifo = txnfifo;         // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
    endfunction

    // -- Enable command coverage measures ------------------------------------
    // Enable commands coverage measures
    task setEnabled();
      enabled = 1; // Coverage Enabling
      fork         
        run();     // Creating coverage subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
         
    // -- Disable command coverage measures -----------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable measures
    endtask : setDisabled
   
    // -- Run command coverage measures ---------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      while (enabled) begin            // Repeat while enabled
         @(txnfifo.txnfifo_cb);              // Wait for clock
         // Sample signals values
         tx_nfifo_dout_vld = txnfifo.txnfifo_cb.TX_NFIFO_DOUT_VLD;
         tx_nfifo_rd = txnfifo.txnfifo_cb.TX_NFIFO_RD;
         CommandsCovergroup.sample();
      end
    endtask : run
  
    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Command coverage for %s:%d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display    
  endclass: CommandsCoverageTXNFIFO
  
  // --------------------------------------------------------------------------
  // -- DDM Command Coverage for Internal Bus Interface 
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
  class CommandsCoverageIB #(int pDataWidth = 64);
  
  // Interface on witch is covering measured
    virtual iInternalBus.ib_write_tb #(pDataWidth) ibus;
    
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic wr_req;
    logic wr_rdy;
        
    //-- Covering transactions ------------------------------------------------
    covergroup CommandsCovergroup;
      // wr request coverpoint
      wr_req: coverpoint wr_req {
        bins wr_req0 = {0};        
        bins wr_req1 = {1};
        }
      // wr address ready coverpoint
      wr_rdy: coverpoint wr_rdy {
        bins wr_rdy0 = {0};        
        bins wr_rdy1 = {1};
        }  
    option.per_instance=1; // Also per instance statistics
    endgroup
    
    // ------------------------------------------------------------------------
    // Constructor
    function new (virtual iInternalBus.ib_write_tb  #(pDataWidth) ibus,
                  string instanceName
                  );
      this.ibus = ibus;               // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
    endfunction

    // -- Enable command coverage measures ------------------------------------
    // Enable commands coverage measures
    task setEnabled();
      enabled = 1; // Coverage Enabling
      fork         
        run();     // Creating coverage subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
         
    // -- Disable command coverage measures -----------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable measures
    endtask : setDisabled
   
    // -- Run command coverage measures ---------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      while (enabled) begin             // Repeat while enabled
         @(ibus.ib_write_cb);            // Wait for clock
         // Sample signals values
         wr_req = ibus.ib_write_cb.WR_REQ;
         wr_rdy = ibus.ib_write_cb.WR_RDY;
         CommandsCovergroup.sample();
      end
    endtask : run
  
    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Command coverage for %s:%d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display    
    
  endclass: CommandsCoverageIB  
  
  // --------------------------------------------------------------------------
  // -- DDM Command Coverage for MI32 Interface 
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
  class CommandsCoverageSW #(int pCtrlDmaDataWidth = 16);
  
    // Interface on witch is covering measured
    virtual iMi32.mi32_tb sw;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic sw_rd;
    logic sw_wr;
    logic sw_drdy; 
    
    //-- Covering transactions ------------------------------------------------
    covergroup CommandsCovergroup;
      // sw read coverpoint
      sw_rd: coverpoint sw_rd {
        bins sw_rd0 = {0};        
        bins sw_rd1 = {1};
        }
      // sw write coverpoint
      sw_wr: coverpoint sw_wr {
        bins sw_wr0 = {0};        
        bins sw_wr1 = {1};
        }  
      // sw data ready coverpoint
      sw_drdy: coverpoint sw_drdy {
        bins sw_drdy0 = {0};        
        bins sw_drdy1 = {1};
        }      
        
    option.per_instance=1; // Also per instance statistics
    endgroup
    
    // ------------------------------------------------------------------------
    // Constructor
    function new (virtual iMi32.mi32_tb sw,
                  string instanceName
                  );
      this.sw = sw;                   // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
    endfunction

    // -- Enable command coverage measures ------------------------------------
    // Enable commands coverage measures
    task setEnabled();
      enabled = 1; // Coverage Enabling
      fork         
        run();     // Creating coverage subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
         
    // -- Disable command coverage measures -----------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable measures
    endtask : setDisabled
   
    // -- Run command coverage measures ---------------------------------------
    // Take transactions from mailbox and generate them to interface
    task run();
      while (enabled) begin            // Repeat while enabled
         @(sw.mi32_cb);                // Wait for clock
         // Sample signals values
         sw_rd = sw.mi32_cb.SW_RD;
         sw_wr = sw.mi32_cb.SW_WR;
         sw_drdy = sw.mi32_cb.SW_DRDY;
         CommandsCovergroup.sample();
      end
    endtask : run
  
    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Command coverage for %s:%d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display    
    
  endclass: CommandsCoverageSW
       
  // --------------------------------------------------------------------------
  // -- DDM Coverage
  // --------------------------------------------------------------------------
  // This class measure coverage of commands
  class DdmCoverage #(int pDataWidth = 32, int pCtrlDmaDataWidth = 16, int pBlockSize = 128, int pFlows = 4);
    CommandsCoverageDMA #(pCtrlDmaDataWidth)           cmdListDMA[$];     // Commands coverage list
    CommandsCoverageIB #(pDataWidth)                   cmdListIB[$];      // Commands coverage list
    CommandsCoverageSW #(pCtrlDmaDataWidth)            cmdListSW[$];      // Commands coverage list 
    CommandsCoverageRXREQ #(pFlows, pBlockSize)        cmdListRXREQ[$];   // Commands coverage list
    CommandsCoverageRXNFIFO #(pFlows, pBlockSize)      cmdListRXNFIFO[$]; // Commands coverage list
    CommandsCoverageTXNFIFO #(pFlows, pBlockSize)      cmdListTXNFIFO[$]; // Commands coverage list
        
    // -- Add dma's interface for command coverage ----------------------------
    task addDmaInterface (virtual iDmaCtrl.dma_tb #(pCtrlDmaDataWidth) port,
                          string name
                          );
      // Create commands coverage class
      CommandsCoverageDMA #(pCtrlDmaDataWidth) cmdCoverageDMA = new(port, name);  
      // Insert class into list
      cmdListDMA.push_back(cmdCoverageDMA);
    endtask : addDmaInterface
    
    // -- Add Internal Bus interface for command coverage ----------------------
    task addInternalBusInterface (virtual iInternalBus.ib_write_tb #(pDataWidth) port,
                                  string name
                                  );
      // Create commands coverage class
      CommandsCoverageIB #(pDataWidth) cmdCoverageIB = new(port, name);  
      // Insert class into list
      cmdListIB.push_back(cmdCoverageIB);
    endtask : addInternalBusInterface
    
    // -- Add MI32 interface for command coverage ------------------------------
    task addSoftwareInterface (virtual iMi32.mi32_tb port,
                               string name
                               );
      // Create commands coverage class
      CommandsCoverageSW #(pCtrlDmaDataWidth) cmdCoverageSW = new(port, name);  
      // Insert class into list
      cmdListSW.push_back(cmdCoverageSW);
    endtask : addSoftwareInterface
    
    // -- Add RX request interface for command coverage -------------
    task addRxReqFifoInterface (virtual iDdm.rxreq_tb #(pFlows, pBlockSize) port,
                                string name
                                 );
      // Create commands coverage class
      CommandsCoverageRXREQ #(pFlows, pBlockSize) cmdCoverageRXREQ = new(port, name);  
      // Insert class into list
      cmdListRXREQ.push_back(cmdCoverageRXREQ);
    endtask : addRxReqFifoInterface
    
    // -- Add RX nfifo interface for command coverage -------------
    task addRxNfifoInterface (virtual iDdm.rxnfifo_tb #(pFlows, pBlockSize) port,
                              string name
                              );
      // Create commands coverage class
      CommandsCoverageRXNFIFO #(pFlows, pBlockSize) cmdCoverageRXNFIFO = new(port, name);  
      // Insert class into list
      cmdListRXNFIFO.push_back(cmdCoverageRXNFIFO);
    endtask : addRxNfifoInterface
    
    // -- Add tx nfifo interface for command coverage -------------
    task addTxNfifoInterface (virtual iDdm.txnfifo_tb #(pFlows, pBlockSize) port,
                              string name
                              );
      // Create commands coverage class
      CommandsCoverageTXNFIFO #(pFlows, pBlockSize) cmdCoverageTXNFIFO = new(port, name);  
      // Insert class into list
      cmdListTXNFIFO.push_back(cmdCoverageTXNFIFO);
    endtask : addTxNfifoInterface
         
    // -- Enable coverage measures ---------------------------------------------
    // Enable coverage measres
    task setEnabled();
      foreach (cmdListDMA[i])     cmdListDMA[i].setEnabled();   // Enable for commands
      foreach (cmdListIB[i])      cmdListIB[i].setEnabled();    // Enable for commands 
      foreach (cmdListSW[i])      cmdListSW[i].setEnabled();    // Enable for commands
      foreach (cmdListRXREQ[i])   cmdListRXREQ[i].setEnabled(); // Enable for commands
      foreach (cmdListRXNFIFO[i]) cmdListRXNFIFO[i].setEnabled(); // Enable for commands
      foreach (cmdListTXNFIFO[i]) cmdListTXNFIFO[i].setEnabled(); // Enable for commands
    endtask : setEnabled
         
    // -- Disable coverage measures --------------------------------------------
    // Disable coverage measures
    task setDisabled();
      foreach (cmdListDMA[i])     cmdListDMA[i].setDisabled();  // Disable for commands
      foreach (cmdListIB[i])      cmdListIB[i].setDisabled();   // Disable for commands
      foreach (cmdListSW[i])      cmdListSW[i].setDisabled();   // Enable for commands
      foreach (cmdListRXREQ[i])   cmdListRXREQ[i].setDisabled();   // Enable for commands
      foreach (cmdListRXNFIFO[i]) cmdListRXNFIFO[i].setDisabled(); // Enable for commands
      foreach (cmdListTXNFIFO[i]) cmdListTXNFIFO[i].setDisabled(); // Enable for commands
    endtask : setDisabled

    // -------------------------------------------------------------------------
    // Display coverage statistic
    virtual task display();
      $write("----------------------------------------------------------------\n");
      $write("-- COVERAGE STATISTICS:\n");
      $write("----------------------------------------------------------------\n");
      foreach (cmdListDMA[i]) cmdListDMA[i].display();
      foreach (cmdListIB[i])  cmdListIB[i].display();
      foreach (cmdListSW[i])  cmdListSW[i].display();
      foreach (cmdListRXREQ[i])    cmdListRXREQ[i].display();
      foreach (cmdListRXNFIFO[i])  cmdListRXNFIFO[i].display();
      foreach (cmdListTXNFIFO[i])  cmdListTXNFIFO[i].display();
      $write("----------------------------------------------------------------\n");
    endtask
  endclass : DdmCoverage


