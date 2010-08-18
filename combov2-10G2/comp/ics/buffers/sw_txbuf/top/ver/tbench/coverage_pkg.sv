/*
 * command_coverage: Tx Buffer Coverage class - transaction coverage
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simková <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: coverage_pkg.sv 4487 2008-08-07 08:09:14Z xsanta06 $
 *
 * TODO:
 *
 */
package coverage_pkg;

  import txbuff_transaction_pkg::*; // Transaction package
  import sv_common_pkg::*;          // Calls back class
  import math_pkg::*;  
  
  // --------------------------------------------------------------------------
  // -- txBuffer Command Coverage for Interface txBuffWrite.txbuff_write_cb
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
    
  class CommandsCoverageWrite #(int pDataWidth=64, int pBlSize=512, int pFlows=2, int pTotFlSize=16384, int pSLen=16);
  
    // Interface on witch is covering measured
    virtual txBuffWrite.txbuff_write_tb #(pDataWidth,pBlSize,pFlows,pTotFlSize,pSLen) b_w;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic [31:0]                wr_addr;
    logic [7:0]                 wr_be;
    logic                       wr_req;
    logic                       wr_rdy;
    logic [pFlows*16-1:0]       tx_newlen;
    logic [pFlows-1:0]          tx_newlen_dv;
    logic [pFlows-1:0]          tx_newlen_rdy;
    logic [pFlows*16-1:0]       tx_rellen;
    logic [pFlows-1:0]          tx_rellen_dv;
    
    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      
      
      // wr_addr coverpoint - small number of used address
      // wr_addr: coverpoint wr_addr;
      
      // wr_be coverpoint
      wr_be: coverpoint wr_be{
        bins wr_be0 = {8'b11111111};
      }
      
      // wr_req coverpoint
      wr_req: coverpoint wr_req {
        bins wr_req0 = {0};
        bins wr_req1 = {1};
      }
      
      // wr_rdy coverpoint
      wr_rdy: coverpoint wr_rdy {
        //bins wr_rdy0 = {0};
        bins wr_rdy1 = {1};
      }
      
      // tx_newlen coverpoint
      //tx_newlen: coverpoint tx_newlen;
      
      // wr_addr coverpoint
      tx_newlen_dv: coverpoint tx_newlen_dv{
        bins tx_newlen_dv0 = {8'b00000001};
        bins tx_newlen_dv1 = {8'b00000010};
        bins tx_newlen_dv2 = {8'b00000100};
        bins tx_newlen_dv3 = {8'b00001000};
        bins tx_newlen_dv4 = {8'b00010000};
        bins tx_newlen_dv5 = {8'b00100000};
        bins tx_newlen_dv6 = {8'b01000000};
        bins tx_newlen_dv7 = {8'b10000000};
      }
      
      // tx_newlen coverpoint
      tx_newlen_rdy: coverpoint tx_newlen_rdy{
        bins tx_newlen_rdy0 = {8'b11111111};
      }
      
      // tx_newlen coverpoint
      //tx_rellen: coverpoint tx_rellen;
      
      // wr_addr coverpoint
      tx_rellen_dv: coverpoint tx_rellen_dv{
        bins tx_rellen_dv0 = {8'b00000001};
        bins tx_rellen_dv1 = {8'b00000010};
        bins tx_rellen_dv2 = {8'b00000100};
        bins tx_rellen_dv3 = {8'b00001000};
        bins tx_rellen_dv4 = {8'b00010000};
        bins tx_rellen_dv5 = {8'b00100000};
        bins tx_rellen_dv6 = {8'b01000000};
        bins tx_rellen_dv7 = {8'b10000000};
      }
      
      option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor
    
    function new (virtual txBuffWrite.txbuff_write_tb #(pDataWidth,pBlSize,pFlows,pTotFlSize,pSLen) b_w,
                  string instanceName);
      this.b_w = b_w;                 // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
    endfunction

    // -- Enable command coverage measures ------------------------------------
    // Enable commands coverage measures
    task setEnabled();
      enabled = 1; // Coverage Enabling
      fork         
         run();    // Creating coverage subprocess
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
         @(b_w.txbuff_write_cb);           // Wait for clock
         // Sample signals values
         wr_addr       = b_w.txbuff_write_cb.WR_ADDR;
         wr_be         = b_w.txbuff_write_cb.WR_BE;
         wr_req        = b_w.txbuff_write_cb.WR_REQ;
         wr_rdy        = b_w.txbuff_write_cb.WR_RDY;
         tx_newlen     = b_w.txbuff_write_cb.TX_NEWLEN;
         tx_newlen_dv  = b_w.txbuff_write_cb.TX_NEWLEN_DV;
         tx_newlen_rdy = b_w.txbuff_write_cb.TX_NEWLEN_RDY;
         tx_rellen     = b_w.txbuff_write_cb.TX_RELLEN;
         tx_rellen_dv  = b_w.txbuff_write_cb.TX_RELLEN_DV;
         
         CommandsCovergroup.sample();
      end
    endtask : run
  
    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Commands coverage for %s: %d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display

  endclass: CommandsCoverageWrite

  // --------------------------------------------------------------------------
  // -- Memory Command Coverage for Interface txBuffRead.monitor_cb
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
  
  class CommandsCoverageMonitor #(int pDataWidth=64, int pBlSize=512, int pFlows=2, int pTotFlSize=16384, int pSLen=16);
  
    // Interface on witch is covering measured
    virtual txBuffRead.monitor #(pDataWidth,pBlSize,pFlows,pTotFlSize,pSLen) b_r;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic [pFlows-1:0]                      tx_sof_n;
    logic [pFlows-1:0]                      tx_sop_n;
    logic [pFlows-1:0]                      tx_eof_n;
    logic [pFlows-1:0]                      tx_eop_n;
    logic [(log2(pDataWidth/8)*pFlows)-1:0] tx_rem;
    logic [pFlows-1:0]                      tx_src_rdy_n;
    logic [pFlows-1:0]                      tx_dst_rdy_n;
    
    
    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      // Start of frame coverpoint
      tx_sof: coverpoint tx_sof_n {
        bins tx_sof0 = {0};        
        bins tx_sof1 = {1};
        }
      // End of frame coverpoint
      tx_eof: coverpoint tx_eof_n {
        bins tx_eof0 = {0};
        bins tx_eof1 = {1};
        }
      // Start of packet coverpoint
      tx_sop: coverpoint tx_sop_n {
        bins tx_sop0 = {0};
        bins tx_sop1 = {1};
        }
      // End of packet coverpoint
      tx_eop: coverpoint tx_eop_n {
        bins tx_eop0 = {0};
        bins tx_eop1 = {1};
        }
      // Drem coverpoint
      tx_rem: coverpoint tx_rem;

      // Source ready coverpoint
      tx_src_rdy: coverpoint tx_src_rdy_n {
        bins tx_src_rdy0 = {0};
        bins tx_src_rdy1 = {1};
      }
      // Destination ready coverpoint
      tx_dst_rdy: coverpoint tx_dst_rdy_n {
        bins tx_dst_rdy0 = {0};
        bins tx_dst_rdy1 = {1};
      }

      // End of packet crosspoint
      cross tx_sof, tx_sop, tx_eof, tx_eop, tx_src_rdy, tx_dst_rdy {
        // Ilegal values
        illegal_bins ilegal_vals0 = binsof(tx_sop.tx_sop1) && binsof(tx_sof.tx_sof0) && binsof(tx_src_rdy.tx_src_rdy0);
        illegal_bins ilegal_vals1 = binsof(tx_eop.tx_eop1) && binsof(tx_eof.tx_eof0) && binsof(tx_src_rdy.tx_src_rdy0);
        }   
          
      // Drem crospoint
      cross tx_rem, tx_eop {
        // Ilegal values
        ignore_bins drem_ignore_vals0 = binsof(tx_eop.tx_eop1);
        }
        
      option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor
    
    function new (virtual txBuffRead.monitor #(pDataWidth,pBlSize,pFlows,pTotFlSize,pSLen) b_r,
                  string instanceName);
      this.b_r = b_r;                 // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
    endfunction

    // -- Enable command coverage measures ------------------------------------
    // Enable commands coverage measures
    task setEnabled();
      enabled = 1; // Coverage Enabling
      fork         
         run();    // Creating coverage subprocess
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
         @(b_r.monitor_cb);        // Wait for clock
         // Sample signals values
         
         tx_sof_n = b_r.monitor_cb.TX_SOF_N;
         tx_sop_n = b_r.monitor_cb.TX_SOP_N;
         tx_eof_n = b_r.monitor_cb.TX_EOF_N;
         tx_eop_n = b_r.monitor_cb.TX_EOP_N;
         tx_rem   = b_r.monitor_cb.TX_REM;
         tx_src_rdy_n = b_r.monitor_cb.TX_SRC_RDY_N;
         tx_dst_rdy_n = b_r.monitor_cb.TX_DST_RDY_N;
         CommandsCovergroup.sample();
      end
    endtask : run
  
    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Commands coverage for %s: %d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display

  endclass: CommandsCoverageMonitor

  // --------------------------------------------------------------------------
  // -- Mem2nFifo Coverage
  // --------------------------------------------------------------------------
  // This class measure coverage of commands
  class Coverage #(int pWDataWidth=64, int pRDataWidth=64, int pBlSize=512, int pFlows=2, int pTotFlSize=16384, int pSLen=16);
    // Commands coverage lists
    CommandsCoverageWrite   #(pWDataWidth,pBlSize,pFlows,pTotFlSize,pSLen) cmdListWrite[$];    
    CommandsCoverageMonitor #(pRDataWidth,pBlSize,pFlows,pTotFlSize,pSLen) cmdListMonitor[$];
        
    // -- Add interface Write for command coverage ----------------------------------
    task addGeneralInterfaceWrite (virtual txBuffWrite.txbuff_write_tb #(pWDataWidth,pBlSize,pFlows,pTotFlSize,pSLen) port,
                                   string name);
      // Create commands coverage class
      CommandsCoverageWrite #(pWDataWidth,pBlSize,pFlows,pTotFlSize,pSLen) cmdCoverageWrite = new(port, name);  
      // Insert class into list
      cmdListWrite.push_back(cmdCoverageWrite);
    endtask : addGeneralInterfaceWrite
    
    // -- Add interface Tx for command coverage ----------------------------------
    task addGeneralInterfaceMonitor (virtual txBuffRead.monitor #(pRDataWidth,pBlSize,pFlows,pTotFlSize,pSLen) port,
                                     string name);
      // Create commands coverage class
      CommandsCoverageMonitor #(pRDataWidth,pBlSize,pFlows,pTotFlSize,pSLen) cmdCoverageMonitor = new(port, name);  
      // Insert class into list
      cmdListMonitor.push_back(cmdCoverageMonitor);
    endtask : addGeneralInterfaceMonitor

    // -- Enable coverage measures --------------------------------------------
    // Enable coverage measres
    task setEnabled();
      foreach (cmdListWrite[i])   cmdListWrite[i].setEnabled();     // Enable for commands
      foreach (cmdListMonitor[i]) cmdListMonitor[i].setEnabled();   // Enable for commands
    endtask : setEnabled
         
    // -- Disable coverage measures -------------------------------------------
    // Disable coverage measures
    task setDisabled();
      foreach (cmdListWrite[i])   cmdListWrite[i].setDisabled();     // Disable for commands
      foreach (cmdListMonitor[i]) cmdListMonitor[i].setDisabled();   // Disable for commands
    endtask : setDisabled

    // ------------------------------------------------------------------------
    // Display coverage statistic
    virtual task display();
      $write("----------------------------------------------------------------\n");
      $write("-- COVERAGE STATISTICS:\n");
      $write("----------------------------------------------------------------\n");
      foreach (cmdListWrite[i])   cmdListWrite[i].display();
      foreach (cmdListMonitor[i]) cmdListMonitor[i].display();
      $write("----------------------------------------------------------------\n");
    endtask
  endclass : Coverage
endpackage : coverage_pkg

