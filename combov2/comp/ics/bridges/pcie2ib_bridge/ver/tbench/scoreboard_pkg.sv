//
// scoreboard_pkg.sv: Scoreboard
// Copyright (C) 2007 CESNET
// Author(s): Tomas Malek <tomalek@liberouter.org>
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
// 3. Neither the name of the Company nor the names of its contributors
//    may be used to endorse or promote products derived from this
//    software without specific prior written permission.
//
// This software is provided ``as is'', and any express or implied
// warranties, including, but not limited to, the implied warranties of
// merchantability and fitness for a particular purpose are disclaimed.
// In no event shall the company or contributors be liable for any
// direct, indirect, incidental, special, exemplary, or consequential
// damages (including, but not limited to, procurement of substitute
// goods or services; loss of use, data, or profits; or business
// interruption) however caused and on any theory of liability, whether
// in contract, strict liability, or tort (including negligence or
// otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// $Id: scoreboard_pkg.sv 688 2007-10-19 16:11:56Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package scoreboard_pkg;

  import ib_transaction_pkg::*;        // Internal Bus Transaction package
  import ib_driver_pkg::*;             // Internal Bus Driver package
  import ib_monitor_pkg::*;            // Internal Bus Monitor package
  import ib_table_pkg::*;              // Internal Bus transaction table package

  import pcie_transaction_pkg::*;      // PCIE Transaction package
  import pcie_driver_pkg::*;           // PCIE Driver package
  import pcie_monitor_pkg::*;          // PCIE Monitor package  
  import pcie_table_pkg::*;            // PCIE transaction table package  

  import bm_transaction_pkg::*;        // BM Transaction package
  import bm_driver_pkg::*;             // BM Driver package  
  import bm_monitor_pkg::*;            // BM Monitor package  
  import bm_table_pkg::*;              // BM transaction table package    
    
  import ib_scoreboard_pkg::*;         // Internal Bus part of scoreboard 
  import pcie_scoreboard_pkg::*;       // PCIE part of scoreboard  
  import bm_scoreboard_pkg::*;         // BM part of scoreboard    
  
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    IbTransactionTable        ibTransactionTable;
    PcieTransactionTable      pcieTransactionTable;  
    BmTransactionTable        bmTransactionTable;    
    tIbTransMbx               ibTransMbx;
    tPcieTransMbx             pcieTransMbx;  
    tBmTransMbx               bmTransMbx;
    ScoreboardIbMonitorCbs    ibMonitorCbs;
    ScoreboardIbDriverCbs     ibDriverCbs;    
    ScoreboardPcieDriverCbs   pcieDriverCbs;
    ScoreboardPcieMonitorCbs  pcieMonitorCbs;    
    ScoreboardBmDriverCbs     bmDriverCbs;
    ScoreboardBmMonitorCbs    bmMonitorCbs;    
    virtual iPcieCfg.bridge   pcieCFG;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (virtual iPcieCfg.bridge   pcieCFG);
      this.pcieCFG                  = pcieCFG; 
      this.ibTransactionTable       = new;
      this.pcieTransactionTable     = new;
      this.bmTransactionTable       = new;
      this.ibTransMbx               = new();
      this.pcieTransMbx             = new();
      this.bmTransMbx               = new();
      this.ibMonitorCbs             = new(ibTransactionTable,ibTransMbx);
      this.ibDriverCbs              = new(pcieTransactionTable,ibTransactionTable,ibTransMbx,this.pcieCFG);      
      this.pcieDriverCbs            = new(ibTransactionTable,pcieTransactionTable,pcieTransMbx,this.pcieCFG);
      this.pcieMonitorCbs           = new(pcieTransactionTable,pcieTransMbx,this.pcieCFG);   
      this.bmDriverCbs              = new(pcieTransactionTable,ibTransactionTable,bmTransactionTable,this.pcieCFG);      
      this.bmMonitorCbs             = new(bmTransactionTable);            
    endfunction

    // -- Enable Master Transaction -------------------------------------------
    // IB driver not only generates completions for local requests
    function void enableMasterTransactions ();
      this.ibDriverCbs.masterEnable    = 1;
    endfunction    

    // -- Disable Master Transaction ------------------------------------------
    // IB driver only generates completions for local requests
    function void disableMasterTransactions ();
      this.ibDriverCbs.masterEnable    = 0;
    endfunction        

    // -- Enable Slave Transaction -------------------------------------------
    // PCIE driver not only generates completions for global requests
    function void enableSlaveTransactions ();
      this.pcieDriverCbs.slaveEnable    = 1;
    endfunction    

    // -- Disable Slave Transaction ------------------------------------------
    // PCIE driver only generates completions for global requests
    function void disableSlaveTransactions ();
      this.pcieDriverCbs.slaveEnable    = 0;           
    endfunction       

    // -- Enable Bus Master Transaction ---------------------------------------
    // Enabling of bus master transactions
    function void enableBmTransactions ();
      integer aux;
      BusMasterTransaction tr      = new();       
      this.bmDriverCbs.bmEnable    = 1;
      aux = this.bmDriverCbs.bmTransMbx.try_put(tr);
    endfunction    

    // -- Disable Bus Master Transaction --------------------------------------
    // Enabling of bus master transactions 
    function void disableBmTransactions ();
      integer aux;
      BusMasterTransaction tr      = new();       
      this.bmDriverCbs.bmEnable    = 0;
      aux = this.bmDriverCbs.bmTransMbx.try_get(tr);      
    endfunction           
  
  endclass : Scoreboard

endpackage : scoreboard_pkg



