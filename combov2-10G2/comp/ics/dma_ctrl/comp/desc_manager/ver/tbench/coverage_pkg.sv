/*
 * command_coverage: Descriptor Manager Coverage class - transaction coverage
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
 * $Id: coverage_pkg.sv 4519 2008-08-07 11:59:30Z xsimko03 $
 *
 * TODO:
 *
 */
package coverage_pkg;

  import dm_transaction_pkg::*; // Transaction package
  import sv_common_pkg::*;          // Calls back class
  import math_pkg::*;  
  
  // --------------------------------------------------------------------------
  // -- Descriptor Manager Command Coverage for Interface descManagerWrite.writeDesc_cb
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
    
  class CommandsCoverageWrite #(pBaseAddr=32'h00000000, pFlows=4, pBlSize=32);
  
    // Interface on witch is covering measured
    virtual descManagerWrite.writeDesc_tb #(pBaseAddr,pFlows,pBlSize) d_w;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic [7:0]                 wr_be;
    logic                       wr_req;
    logic                       wr_rdy;
    logic [11:0]                bm_length;
    logic                       bm_req;
    logic                       bm_ack;
    logic [pFlows-1:0]          enable;
    
    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      
      
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
      
      // bm_length coverpoint
      bm_length: coverpoint bm_length {
        bins bm_length1 = {pBlSize*8};
      }
      
      // bm_req coverpoint
      bm_req: coverpoint bm_req {
        bins bm_req0 = {0};
        bins bm_req1 = {1};
      }
      
      // bm_ack coverpoint
      bm_ack: coverpoint bm_ack {
        bins bm_ack0 = {0};
        bins bm_ack1 = {1};
      }
      
      // enable coverpoint
      enable: coverpoint enable{
        bins enable = {4'b1111};
      }
      
      option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor
    
    function new (virtual descManagerWrite.writeDesc_tb #(pBaseAddr,pFlows,pBlSize) d_w,
                  string instanceName);
      this.d_w = d_w;                 // Store interface
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
         @(d_w.writeDesc_cb);           // Wait for clock
         // Sample signals values
         wr_be         = d_w.writeDesc_cb.WR_BE;
         wr_req        = d_w.writeDesc_cb.WR_REQ;
         wr_rdy        = d_w.writeDesc_cb.WR_RDY;
         bm_length     = d_w.writeDesc_cb.BM_LENGTH;
         bm_req        = d_w.writeDesc_cb.BM_REQ;
         bm_ack        = d_w.writeDesc_cb.BM_ACK;
         enable        = d_w.writeDesc_cb.ENABLE;
         
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
  // -- Ibus Command Coverage for Interface descManagerRead.monitor_cb
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
  
  class CommandsCoverageMonitor #(pBaseAddr=32'h00000000, pFlows=4, pBlSize=32);
  
    // Interface on witch is covering measured
    virtual descManagerRead.monitor #(pBaseAddr,pFlows,pBlSize) d_r;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    logic [pFlows-1:0]          empty;
    logic [pFlows-1:0]          read;
        
    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      
      // empty coverpoint
      empty: coverpoint empty {
        bins empty0 = {0};        
        bins empty1 = {1};
        }
      // read coverpoint
      read: coverpoint read {
        bins read0 = {0};
        bins read1 = {1};
        }
              
      option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor
    
    function new (virtual descManagerRead.monitor #(pBaseAddr,pFlows,pBlSize) d_r,
                  string instanceName);
      this.d_r = d_r;                 // Store interface
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
         @(d_r.monitor_cb);        // Wait for clock
         // Sample signals values
         
         empty = d_r.monitor_cb.EMPTY;
         read = d_r.monitor_cb.READ;
         
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
  class Coverage #(pBaseAddr=32'h00000000, pFlows=4, pBlSize=32);
    // Commands coverage lists
    CommandsCoverageWrite   #(pBaseAddr,pFlows,pBlSize) cmdListWrite[$];    
    CommandsCoverageMonitor #(pBaseAddr,pFlows,pBlSize) cmdListMonitor[$];
        
    // -- Add interface Write for command coverage ----------------------------------
    task addGeneralInterfaceWrite (virtual descManagerWrite.writeDesc_tb #(pBaseAddr,pFlows,pBlSize) port,
                                   string name);
      // Create commands coverage class
      CommandsCoverageWrite #(pBaseAddr,pFlows,pBlSize) cmdCoverageWrite = new(port, name);  
      // Insert class into list
      cmdListWrite.push_back(cmdCoverageWrite);
    endtask : addGeneralInterfaceWrite
    
    // -- Add interface Tx for command coverage ----------------------------------
    task addGeneralInterfaceMonitor (virtual descManagerRead.monitor #(pBaseAddr,pFlows,pBlSize) port,
                                     string name);
      // Create commands coverage class
      CommandsCoverageMonitor #(pBaseAddr,pFlows,pBlSize) cmdCoverageMonitor = new(port, name);  
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

