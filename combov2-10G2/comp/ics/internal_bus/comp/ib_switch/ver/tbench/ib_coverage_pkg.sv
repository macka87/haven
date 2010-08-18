/*
 * ib_coverage_pkg.sv: Internal Bus Coverage class - transaction coverage
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id: ib_coverage_pkg.sv 334 2007-09-05 20:13:22Z xkobie00 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_coverage_pkg;

  import ib_transaction_pkg::*; // Transaction package
  import ib_driver_pkg::*;      // Driver calls back class

  // --------------------------------------------------------------------------
  // -- Internal Bus Transaction Coverage
  // --------------------------------------------------------------------------
  // This class measure some specific transaction coverage. Transaction are
  // send to this class by callback methods.
  class TransactionCoverage extends DriverCbs;
      
      InternalBusTransaction transaction; // Internal Bus transaction
      bit enabled;                        // Enable transaction coverage 
      string instanceName;

      //-- Covering transactions ----------------------------------------------
      covergroup TransactionsCovergroup;

        // Transaction type coverage
        tt  : coverpoint transaction.transType;

        // Transaction length coverage
        len : coverpoint transaction.length {
          bins two_words = { [0:16] };  // Coverage of two words
          bins maximum   = { 12'h111 }; // Maximal Length
          }

        // Local Address coverage (all address alligment)
        la : coverpoint transaction.localAddr[2:0];

        // Globa Address coverage (all address alligment)
        ga : coverpoint transaction.globalAddr[2:0];

        // Cross coverage
        cross tt, len, la, ga;

        option.per_instance=1; // Also per instance statistics
        endgroup

    // ------------------------------------------------------------------------
    // Constructor
    function new(string instanceName);
      TransactionsCovergroup = new; // Create covergroup
      enabled = 0;
      this.instanceName = instanceName;
    endfunction

    // -- Enable transactions coverage measures -------------------------------
    // Enable commands coverage measres
    task setEnabled();
      enabled = 1; // Coverage Enabling
    endtask : setEnabled
         
    // -- Disable transactions coverage measures ------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0; // Disable measures
    endtask : setDisabled
   
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended 
    virtual task post_tx(InternalBusTransaction transaction, integer driverId);
      if (enabled) begin;
        this.transaction=transaction;    // Save current transaction
        TransactionsCovergroup.sample(); // Sample statistics
      end
    endtask

    // ------------------------------------------------------------------------
    // Display coverage statistic
    virtual task display();
       $write("Transaction coverage for %s: %d percent\n",
              instanceName, TransactionsCovergroup.get_inst_coverage());
    endtask

  endclass : TransactionCoverage



  // --------------------------------------------------------------------------
  // -- Internal Bus Driver Callbacks
  // --------------------------------------------------------------------------
  class CommandsCoverage;
    // Interface on witch is covering measured
    virtual iInternalBusLink.monitor internalBus;
    string  instanceName;

    // Sampling is enabled
    bit enabled;

    // Sampled values from interface
    logic sop_n;
    logic eop_n;
    logic src_rdy_n;
    logic dst_rdy_n;
     
    //-- Covering transactions ----------------------------------------------
    covergroup CommandsCovergroup;
      // Start of packet coverpoint
      sop: coverpoint sop_n {
        bins sop0 = {0};
        bins sop1 = {1};
        }
      // End of packet coverpoint
      eop: coverpoint eop_n {
        bins eop0 = {0};
        bins eop1 = {1};
        }
      // Source ready coverpoint
      src_rdy: coverpoint src_rdy_n {
        bins src_rdy0 = {0};
        bins src_rdy1 = {1};
      }
      // Destination ready coverpoint
      dst_rdy: coverpoint dst_rdy_n {
        bins dst_rdy0 = {0};
        bins dst_rdy1 = {1};
      }

      // Start of packet crospoint
      cross sop, src_rdy, dst_rdy  {
        // Illegal values
        illegal_bins sop_illegal_vals0 = binsof(sop.sop0) && 
                                     binsof(src_rdy.src_rdy1) && 
                                     binsof(dst_rdy.dst_rdy1);
        illegal_bins sop_illegal_vals1 = binsof(sop.sop0) && 
                                     binsof(src_rdy.src_rdy1) && 
                                     binsof(dst_rdy.dst_rdy0);
        }

      // End of packet crosspoint
      cross eop, src_rdy, dst_rdy  {
          // Ilegal values
          illegal_bins eop_illegal_vals0 = binsof(eop.eop0) && 
                                       binsof(src_rdy.src_rdy1) && 
                                       binsof(dst_rdy.dst_rdy1);
          illegal_bins eop_illegal_vals1 = binsof(eop.eop0) && 
                                       binsof(src_rdy.src_rdy1) && 
                                       binsof(dst_rdy.dst_rdy0);
          }
        option.per_instance=1; // Also per instance statistics
     endgroup

    // ------------------------------------------------------------------------
    // Constructor
    function new (virtual iInternalBusLink.monitor internalBus,
                  string instanceName);
      this.internalBus = internalBus; // Store interface
      CommandsCovergroup = new;       // Create covergroup
      enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
    endfunction

    // -- Enable command coverage measures ------------------------------------
    // Enable commands coverage measres
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
         @(posedge internalBus.CLK);    // Wait for clock
         // Sample signals values
         sop_n = internalBus.SOP_N;
         eop_n = internalBus.EOP_N;
         src_rdy_n = internalBus.SRC_RDY_N;
         dst_rdy_n = internalBus.DST_RDY_N;
         CommandsCovergroup.sample();
      end
    endtask : run
  
    // ------------------------------------------------------------------------
    // Display coverage statistic
    task display();
       $write("Commands coverage for %s: %d percent\n",
               instanceName, CommandsCovergroup.get_inst_coverage());
    endtask : display

  endclass: CommandsCoverage



  // --------------------------------------------------------------------------
  // -- Internal Bus Coverage
  // --------------------------------------------------------------------------
  // This class measure  coverage of transactions and commands
  class Coverage;
    CommandsCoverage    cmdList[$];   // Commands coverage list
    TransactionCoverage transList[$]; // Transactions coverage list
    
    // -- Add interface for command coverage ----------------------------------
    task addInternalBusInterface ( virtual iInternalBusLink.monitor port,
                                   string name );
      // Create commands coverage class
      CommandsCoverage cmdCoverage = new(port, name);  
      // Insert class into list
      cmdList.push_back(cmdCoverage);
    endtask : addInternalBusInterface

    // -- Add driver for transaction coverage ---------------------------------
    task addDriver (InternalBusDriver driver, string name);
      // Create transaction coverage class
      TransactionCoverage transCoverage = new(name); 
      // Insert transaction into List
      transList.push_back(transCoverage);
      // Set driver callback to transaction coverage instance
      driver.setCallbacks(transCoverage);
    endtask : addDriver

    // -- Enable coverage measures --------------------------------------------
    // Enable coverage measres
    task setEnabled();
      foreach (transList[i]) transList[i].setEnabled(); // Enable fro transactions
      foreach (cmdList[i])   cmdList[i].setEnabled();   // Enable for commands
    endtask : setEnabled
         
    // -- Disable coverage measures -------------------------------------------
    // Disable coverage measures
    task setDisabled();
      foreach (transList[i]) transList[i].setDisabled(); // Disable for transactions
      foreach (cmdList[i]) cmdList[i].setDisabled();     // Disable for commands
    endtask : setDisabled

    // ------------------------------------------------------------------------
    // Display coverage statistic
    virtual task display();
      $write("----------------------------------------------------------------\n");
      $write("-- COVERAGE STATISTICS:\n");
      $write("----------------------------------------------------------------\n");
      foreach (transList[i]) transList[i].display();
      foreach (cmdList[i]) cmdList[i].display();
      $write("----------------------------------------------------------------\n");
    endtask
  endclass : Coverage


endpackage : ib_coverage_pkg

