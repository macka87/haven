/*
 * au_command_coverage: Align Unit Coverage class - transaction coverage
 * Copyright (C) 2008 CESNET
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
 * $Id: au_command_coverage.sv 3590 2008-07-16 09:05:59Z xsanta06 $
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- Align Unit Command Coverage for Interface FrameLinkRx
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
  
  class CommandsCoverageRx ;
  
    // Interface on witch is covering measured
    virtual iAlignUnit.rx_tb rx;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic in_sof;
    logic in_eof;
    logic in_src_rdy;
    logic in_dst_rdy;
    logic [2:0] src_addr;
    logic [2:0] dst_addr;
    logic [2:0] data_len;
     
    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      // Start of frame coverpoint
      in_sof: coverpoint in_sof {
        bins sof0 = {0};        
        bins sof1 = {1};
        }
        
      // End of frame coverpoint
      in_eof: coverpoint in_eof {
        bins eof0 = {0};
        bins eof1 = {1};
        }

      // Source ready coverpoint
      in_src_rdy: coverpoint in_src_rdy {
        bins src_rdy0 = {0};
        bins src_rdy1 = {1};
      }
      
      // Destination ready coverpoint
      in_dst_rdy: coverpoint in_dst_rdy {
        bins dst_rdy0 = {0};
        bins dst_rdy1 = {1};
      }
      
      // Source address coverpoint
      src_addr: coverpoint src_addr;
      
      // Source address coverpoint
      dst_addr: coverpoint dst_addr;
      
      // Data length coverpoint
      data_len: coverpoint data_len;

      // Control signals crosspoint
      cross in_sof, in_eof, in_src_rdy, in_dst_rdy;
          
      // Src_addr, dst_addr, data_len crosspoint
      cross src_addr, dst_addr, data_len, in_sof; 

        option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor
    
    function new (virtual iAlignUnit.rx_tb rx,
                  string instanceName);
      this.rx = rx;                   // Store interface
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
         @(rx.rx_cb);             // Wait for clock
         // Sample signals values
         in_sof = rx.rx_cb.IN_SOF;
         in_eof = rx.rx_cb.IN_EOF;
         in_src_rdy = rx.rx_cb.IN_SRC_RDY;
         in_dst_rdy = rx.rx_cb.IN_DST_RDY;
         src_addr = rx.rx_cb.SRC_ADDR;
         dst_addr = rx.rx_cb.DST_ADDR;
         data_len = rx.rx_cb.DATA_LEN;
         CommandsCovergroup.sample();
      end
    endtask : run
  
    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Commands coverage for %s: %d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display

  endclass: CommandsCoverageRx

  // --------------------------------------------------------------------------
  // -- Align Unit Command Coverage for Interface FrameLinkTx
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
  
  class CommandsCoverageTx;
  
    // Interface on witch is covering measured
    virtual iAlignUnit.monitor monitor;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic out_sof;
    logic out_eof;
    logic out_src_rdy;
    logic out_dst_rdy;
     
    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      // Start of frame coverpoint
      out_sof: coverpoint out_sof {
        bins sof0 = {0};        
        bins sof1 = {1};
        }
      // End of frame coverpoint
      out_eof: coverpoint out_eof {
        bins eof0 = {0};
        bins eof1 = {1};
        }
      // Source ready coverpoint
      out_src_rdy: coverpoint out_src_rdy {
        bins src_rdy0 = {0};
        bins src_rdy1 = {1};
      }
      // Destination ready coverpoint
      out_dst_rdy: coverpoint out_dst_rdy {
        bins dst_rdy0 = {0};
        bins dst_rdy1 = {1};
      }

      // Control signals crosspoint
      cross out_sof, out_eof, out_src_rdy, out_dst_rdy;
        
      option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor
    
    function new (virtual iAlignUnit.monitor monitor,
                  string instanceName);
      this.monitor = monitor;         // Store interface
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
         @(monitor.monitor_cb);             // Wait for clock
         // Sample signals values
         out_sof = monitor.monitor_cb.OUT_SOF;
         out_eof = monitor.monitor_cb.OUT_EOF;
         out_src_rdy = monitor.monitor_cb.OUT_SRC_RDY;
         out_dst_rdy = monitor.monitor_cb.OUT_DST_RDY;
         CommandsCovergroup.sample();
      end
    endtask : run
  
    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Commands coverage for %s: %d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display

  endclass: CommandsCoverageTx

  // --------------------------------------------------------------------------
  // -- Frame Link Coverage
  // --------------------------------------------------------------------------
  // This class measure coverage of commands
  class Coverage ;
    CommandsCoverageRx    cmdListRx[$];  // Commands coverage list
    CommandsCoverageTx    cmdListTx[$];  // Commands coverage list
        
    // -- Add interface Rx for command coverage ----------------------------------
    task addAlignUnitInterfaceRx ( virtual iAlignUnit.rx_tb port,
                                   string name);
      // Create commands coverage class
      CommandsCoverageRx cmdCoverageRx = new(port, name);  
      // Insert class into list
      cmdListRx.push_back(cmdCoverageRx);
    endtask : addAlignUnitInterfaceRx
    
    // -- Add interface Tx for command coverage ----------------------------------
    task addAlignUnitInterfaceTx ( virtual iAlignUnit.monitor port,
                                   string name);
      // Create commands coverage class
      CommandsCoverageTx cmdCoverageTx = new(port, name);  
      // Insert class into list
      cmdListTx.push_back(cmdCoverageTx);
    endtask : addAlignUnitInterfaceTx

    // -- Enable coverage measures --------------------------------------------
    // Enable coverage measres
    task setEnabled();
      foreach (cmdListRx[i])   cmdListRx[i].setEnabled();   // Enable for commands
      foreach (cmdListTx[i])   cmdListTx[i].setEnabled();   // Enable for commands
    endtask : setEnabled
         
    // -- Disable coverage measures -------------------------------------------
    // Disable coverage measures
    task setDisabled();
      foreach (cmdListRx[i]) cmdListRx[i].setDisabled();     // Disable for commands
      foreach (cmdListTx[i]) cmdListTx[i].setDisabled();     // Disable for commands
    endtask : setDisabled

    // ------------------------------------------------------------------------
    // Display coverage statistic
    virtual task display();
      $write("----------------------------------------------------------------\n");
      $write("-- COVERAGE STATISTICS:\n");
      $write("----------------------------------------------------------------\n");
      foreach (cmdListRx[i]) cmdListRx[i].display();
      foreach (cmdListTx[i]) cmdListTx[i].display();
      $write("----------------------------------------------------------------\n");
    endtask
  endclass : Coverage


