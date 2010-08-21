/*
 * rxbuf_command_coverage: SW RX Buffer Coverage class - transaction coverage
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
 * $Id: rxbuf_command_coverage.sv 13927 2010-06-03 14:46:50Z xkoran01 $
 *
 * TODO:
 *
 */
  
  // --------------------------------------------------------------------------
  // -- SW RX Buffer Command Coverage for Interface FrameLink
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
  
  class CommandsCoverageRx #(int pDataWidth = 64, int pBlockSize = 512, int pFlows = 2);
  
    // Interface on witch is covering measured
    virtual iSwRxBuffer.fl_tb #(pDataWidth,pBlockSize,pFlows) fl;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic rx_sof_n;
    logic rx_eof_n;
    logic rx_sop_n;
    logic rx_eop_n;
    logic [log2(pDataWidth/8)-1:0] rx_rem; 
    logic rx_src_rdy_n;
    logic rx_dst_rdy_n;
     
    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      // Start of frame coverpoint
      rx_sof: coverpoint rx_sof_n {
        bins sof0 = {0};        
        bins sof1 = {1};
        }
      // End of frame coverpoint
      rx_eof: coverpoint rx_eof_n {
        bins eof0 = {0};
        bins eof1 = {1};
        }
      // Start of packet coverpoint
      rx_sop: coverpoint rx_sop_n {
        bins sop0 = {0};
        bins sop1 = {1};
        }
      // End of packet coverpoint
      rx_eop: coverpoint rx_eop_n {
        bins eop0 = {0};
        bins eop1 = {1};
        }
      // Drem coverpoint
      rx_rem: coverpoint rx_rem;

      // Source ready coverpoint
      rx_src_rdy: coverpoint rx_src_rdy_n {
        bins src_rdy0 = {0};
        bins src_rdy1 = {1};
      }
      // Destination ready coverpoint
      rx_dst_rdy: coverpoint rx_dst_rdy_n {
        bins dst_rdy0 = {0};
        bins dst_rdy1 = {1};
      }

      // End of packet crosspoint
      cross rx_sof, rx_sop, rx_eof, rx_eop, rx_src_rdy, rx_dst_rdy {
        // Ilegal values
        illegal_bins ilegal_vals0 = binsof(rx_sop.sop1) && binsof(rx_sof.sof0);
        illegal_bins ilegal_vals1 = binsof(rx_eop.eop1) && binsof(rx_eof.eof0);
        }   
          
      // Drem crospoint
      cross rx_rem, rx_eop {
        // Ilegal values
        ignore_bins drem_ignore_vals0 = binsof(rx_eop.eop1);
        } 

        option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor
    
    function new (virtual iSwRxBuffer.fl_tb #(pDataWidth,pBlockSize,pFlows) fl,
                  string instanceName);
      this.fl = fl;                   // Store interface
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
         @(fl.fl_cb);                   // Wait for clock
         // Sample signals values
         rx_rem  = fl.fl_cb.RX_REM;
         rx_sof_n = fl.fl_cb.RX_SOF_N;
         rx_eof_n = fl.fl_cb.RX_EOF_N;
         rx_sop_n = fl.fl_cb.RX_SOP_N;
         rx_eop_n = fl.fl_cb.RX_EOP_N;
         rx_src_rdy_n = fl.fl_cb.RX_SRC_RDY_N;
         rx_dst_rdy_n = fl.fl_cb.RX_DST_RDY_N;
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
  // -- SW RX Buffer Command Coverage for Interface InternalBus
  // --------------------------------------------------------------------------
  // This class measures exercised combinations of interface signals
  
  class CommandsCoverageTx #(int pDataWidth = 64, int pBlockSize = 512, int pFlows = 2);
  
    // Interface on witch is covering measured
    virtual iSwRxBuffer.monitor #(pDataWidth,pBlockSize,pFlows) monitor;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic [31:0] rd_addr;
    logic rd_req;
    logic rd_ardy;
    logic rd_src_rdy;
    logic rd_dst_rdy;
    logic rx_newlen_dv;
    logic [abs(log2(FLOWS)-1):0] rx_newlen_ifc;
    logic rx_rellen_dv;
    logic [abs(log2(FLOWS)-1):0] rx_rellen_ifc;
     
    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      // Read address coverpoint
      rd_addr: coverpoint rd_addr;
      
      // Read request coverpoint
      rd_req: coverpoint rd_req {
        bins rd_req0 = {0};        
        bins rd_req1 = {1};
        }
      // Address ready coverpoint
      rd_ardy: coverpoint rd_ardy {
        bins rd_ardy0 = {0};
        bins rd_ardy1 = {1};
        }
      // Source ready coverpoint
      rd_src_rdy: coverpoint rd_src_rdy {
        bins src_rdy0 = {0};
        bins src_rdy1 = {1};
      }
      // Destination ready coverpoint
      rd_dst_rdy: coverpoint rd_dst_rdy {
        bins dst_rdy0 = {0};
        bins dst_rdy1 = {1};
      }
      // NewLenDv coverpoint
      rx_newlen_dv: coverpoint rx_newlen_dv;
      rx_newlen_ifc: coverpoint rx_newlen_ifc;
      // RelLenDv coverpoint
      rx_rellen_dv: coverpoint rx_rellen_dv;
      rx_rellen_ifc: coverpoint rx_rellen_ifc;

      // Control signals crosspoint
      cross rd_req, rd_ardy, rd_src_rdy, rd_dst_rdy {
        ignore_bins rd_ardy1__rd_req0 = binsof(rd_ardy.rd_ardy1) && binsof(rd_req.rd_req0);
      }
        
        option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor
    
    function new (virtual iSwRxBuffer.monitor #(pDataWidth,pBlockSize,pFlows) monitor,
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
         rd_addr = monitor.monitor_cb.RD_ADDR;
         rd_req  = monitor.monitor_cb.RD_REQ;
         rd_ardy = monitor.monitor_cb.RD_ARDY;
         rd_src_rdy = monitor.monitor_cb.RD_SRC_RDY;
         rd_dst_rdy = monitor.monitor_cb.RD_DST_RDY;
         rx_newlen_dv = monitor.monitor_cb.RX_NEWLEN_DV;
         rx_rellen_dv = monitor.monitor_cb.RX_RELLEN_DV;
         rx_newlen_ifc = monitor.monitor_cb.RX_NEWLEN_IFC;
         rx_rellen_ifc = monitor.monitor_cb.RX_RELLEN_IFC;
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
  class Coverage #(int pDataWidth = 64, int pTxDataWidth = 64, int pBlockSize = 512, int pFlows = 2) ;
    CommandsCoverageRx #(pDataWidth,pBlockSize,pFlows)   cmdListRx[$];  // Commands coverage list
    CommandsCoverageTx #(pTxDataWidth,pBlockSize,pFlows) cmdListTx[$];  // Commands coverage list
        
    // -- Add interface Rx for command coverage ----------------------------------
    task addSwRxBufferInterfaceRx ( virtual iSwRxBuffer.fl_tb #(pDataWidth,pBlockSize,pFlows) port,
                                   string name);
      // Create commands coverage class
      CommandsCoverageRx #(pDataWidth,pBlockSize,pFlows) cmdCoverageRx = new(port, name);  
      // Insert class into list
      cmdListRx.push_back(cmdCoverageRx);
    endtask : addSwRxBufferInterfaceRx
    
    // -- Add interface Tx for command coverage ----------------------------------
    task addSwRxBufferInterfaceTx ( virtual iSwRxBuffer.monitor #(pTxDataWidth,pBlockSize,pFlows) port,
                                   string name);
      // Create commands coverage class
      CommandsCoverageTx #(pTxDataWidth,pBlockSize,pFlows) cmdCoverageTx = new(port, name);  
      // Insert class into list
      cmdListTx.push_back(cmdCoverageTx);
    endtask : addSwRxBufferInterfaceTx

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


