/*
 * switch_coverage.sv: Internal Bus Switch functional coverage class
 * Copyright (C) 2009 CESNET
 * Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 0. Redistributions of source code must retain the above copyright
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
 * $Id: switch_coverage.sv 12297 2009-12-16 18:17:27Z washek $
 *
 * TODO:
 *
 */
  
package switch_coverage_pkg;
  
  import math_pkg::*;
  import sv_common_pkg::*;
  import coverage_pkg::*;
  import ib_common_pkg::*;
  import ib_params_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- Internal Bus Transaction Coverage
  // --------------------------------------------------------------------------
  // This class measure some specific transaction coverage. Transactions are
  // sent to this class by callback methods.
  class IbTransCoverage #(pIbSwitchGenerics G = dIbSwitchGenerics)
                                                              extends Coverage;
      
    InternalBusTransaction tr;   // Internal Bus transaction
    string instanceName;
    
    parameter int PORT1_BASE  = G.PORT1_BASE;
    parameter int PORT2_BASE  = G.PORT2_BASE;
    parameter int PORT1_TOP   = G.PORT1_BASE  + G.PORT1_LIMIT  - 1;
    parameter int PORT2_TOP   = G.PORT2_BASE  + G.PORT2_LIMIT  - 1;
    
    //-- Covering transactions ----------------------------------------------
    covergroup IbTransCovergroup;

      // Transaction type coverage
      tt : coverpoint tr.transType {
        bins loc = {L2LW, L2LR, RDC, RDCL};
        bins glob  = {L2GW, G2LR};
        option.weight = 0; //only cross has weight
      }

      // Global Address (address alligment)
      addr : coverpoint tr.globalAddr {
        bins in1 = {[PORT1_BASE +2 : PORT1_TOP -2]};
        bins in2 = {[PORT2_BASE +2 : PORT2_TOP -2]};
        bins b1[] = {PORT1_BASE,  PORT1_TOP};
        bins b2[] = {PORT2_BASE,  PORT2_TOP};
        bins b1_1[]={PORT1_BASE +1,PORT1_TOP +1,PORT1_BASE -1,PORT1_TOP -1};
        bins b2_1[]={PORT2_BASE +1,PORT2_TOP +1,PORT2_BASE -1,PORT2_TOP -1};
        bins b1_7[]={PORT1_BASE +7,PORT1_TOP +7,PORT1_BASE -7,PORT1_TOP -7};
        bins b2_7[]={PORT2_BASE +7,PORT2_TOP +7,PORT2_BASE -7,PORT2_TOP -7};
        bins b1_8[]={PORT1_BASE +8,PORT1_TOP +8,PORT1_BASE -8,PORT1_TOP -8};
        bins b2_8[]={PORT2_BASE +8,PORT2_TOP +8,PORT2_BASE -8,PORT2_TOP -8};
        bins b1_9[]={PORT1_BASE +9,PORT1_TOP +9,PORT1_BASE -9,PORT1_TOP -9};
        bins b2_9[]={PORT2_BASE +9,PORT2_TOP +9,PORT2_BASE -9,PORT2_TOP -9};
       bins b1_15[]={PORT1_BASE +15,PORT1_TOP +15,PORT1_BASE -15,PORT1_TOP -15};
       bins b2_15[]={PORT2_BASE +15,PORT2_TOP +15,PORT2_BASE -15,PORT2_TOP -15};
       bins b1_16[]={PORT1_BASE +16,PORT1_TOP +16,PORT1_BASE -16,PORT1_TOP -16};
       bins b2_16[]={PORT2_BASE +16,PORT2_TOP +16,PORT2_BASE -16,PORT2_TOP -16};
       bins b1_17[]={PORT1_BASE +17,PORT1_TOP +17,PORT1_BASE -17,PORT1_TOP -17};
       bins b2_17[]={PORT2_BASE +17,PORT2_TOP +17,PORT2_BASE -17,PORT2_TOP -17};
       bins b1_31[]={PORT1_BASE +31,PORT1_TOP +31,PORT1_BASE -31,PORT1_TOP -31};
       bins b2_31[]={PORT2_BASE +31,PORT2_TOP +31,PORT2_BASE -31,PORT2_TOP -31};
       bins b1_32[]={PORT1_BASE +32,PORT1_TOP +32,PORT1_BASE -32,PORT1_TOP -32};
       bins b2_32[]={PORT2_BASE +32,PORT2_TOP +32,PORT2_BASE -32,PORT2_TOP -32};
       bins b1_33[]={PORT1_BASE +33,PORT1_TOP +33,PORT1_BASE -33,PORT1_TOP -33};
       bins b2_33[]={PORT2_BASE +33,PORT2_TOP +33,PORT2_BASE -33,PORT2_TOP -33};
       bins b1_63[]={PORT1_BASE +63,PORT1_TOP +63,PORT1_BASE -63,PORT1_TOP -63};
       bins b2_63[]={PORT2_BASE +63,PORT2_TOP +63,PORT2_BASE -63,PORT2_TOP -63};
       bins b1_64[]={PORT1_BASE +64,PORT1_TOP +64,PORT1_BASE -64,PORT1_TOP -64};
       bins b2_64[]={PORT2_BASE +64,PORT2_TOP +64,PORT2_BASE -64,PORT2_TOP -64};
       bins b1_65[]={PORT1_BASE +65,PORT1_TOP +65,PORT1_BASE -65,PORT1_TOP -65};
       bins b2_65[]={PORT2_BASE +65,PORT2_TOP +65,PORT2_BASE -65,PORT2_TOP -65};
       bins b1_127[]={PORT1_BASE +127,PORT1_TOP +127,PORT1_BASE -127,PORT1_TOP -127};
       bins b2_127[]={PORT2_BASE +127,PORT2_TOP +127,PORT2_BASE -127,PORT2_TOP -127};
       bins b1_128[]={PORT1_BASE +128,PORT1_TOP +128,PORT1_BASE -128,PORT1_TOP -128};
       bins b2_128[]={PORT2_BASE +128,PORT2_TOP +128,PORT2_BASE -128,PORT2_TOP -128};
       bins b1_129[]={PORT1_BASE +129,PORT1_TOP +129,PORT1_BASE -129,PORT1_TOP -129};
       bins b2_129[]={PORT2_BASE +129,PORT2_TOP +129,PORT2_BASE -129,PORT2_TOP -129};
       bins b1_255[]={PORT1_BASE +255,PORT1_TOP +255,PORT1_BASE -255,PORT1_TOP -255};
       bins b2_255[]={PORT2_BASE +255,PORT2_TOP +255,PORT2_BASE -255,PORT2_TOP -255};
       bins b1_256[]={PORT1_BASE +256,PORT1_TOP +256,PORT1_BASE -256,PORT1_TOP -256};
       bins b2_256[]={PORT2_BASE +256,PORT2_TOP +256,PORT2_BASE -256,PORT2_TOP -256};
       bins b1_257[]={PORT1_BASE +257,PORT1_TOP +257,PORT1_BASE -257,PORT1_TOP -257};
       bins b2_257[]={PORT2_BASE +257,PORT2_TOP +257,PORT2_BASE -257,PORT2_TOP -257};
       bins b1_65535[]={PORT1_BASE +65535,PORT1_TOP +65535,PORT1_BASE -65535,PORT1_TOP -65535};
       bins b2_65535[]={PORT2_BASE +65535,PORT2_TOP +65535,PORT2_BASE -65535,PORT2_TOP -65535};
       bins b1_65536[]={PORT1_BASE +65536,PORT1_TOP +65536,PORT1_BASE -65536,PORT1_TOP -65536};
       bins b2_65536[]={PORT2_BASE +65536,PORT2_TOP +65536,PORT2_BASE -65536,PORT2_TOP -65536};
       bins b1_65537[]={PORT1_BASE +65537,PORT1_TOP +65537,PORT1_BASE -65537,PORT1_TOP -65537};
       bins b2_65537[]={PORT2_BASE +65537,PORT2_TOP +65537,PORT2_BASE -65537,PORT2_TOP -65537};
        bins out = default;
        option.weight = 0; //only cross has weight
      }
      
      tt_addr : cross tt, addr {
        ignore_bins glob = binsof(tt.glob);
      }

      option.per_instance=1; // Also per instance statistics
    endgroup
      
      
    // -- Constructor ---------------------------------------------------------
    // Constructor
    function new(string instanceName);
      enabled = 0;
      this.instanceName = instanceName;
      IbTransCovergroup = new;
    endfunction

    // -- Function is called after a transaction is sent ----------------------
    virtual task post_tx(Transaction transaction, string inst);
      InternalBusTransaction tr;
      if (enabled) begin;
        $cast(tr,transaction);
        this.tr=tr;  // Save current transaction
        IbTransCovergroup.sample();
      end
    endtask
    
    // -- Get actual coverage -------------------------------------------------
    function real getCoverage();
      getCoverage = IbTransCovergroup.get_inst_coverage();
    endfunction : getCoverage
    
    // -- Display coverage statistic ------------------------------------------
    function void display();
       $write("Transaction coverage for %s: \t%3.2f %%\n",
              instanceName, getCoverage());
    endfunction

  endclass : IbTransCoverage
  
    
  // --------------------------------------------------------------------------
  // -- Switch Coverage
  // --------------------------------------------------------------------------
  class IbSwitchCoverage #(pIbSwitchGenerics G = dIbSwitchGenerics)
                                                       extends CoverageWrapper;
    parameter int DATA_WIDTH = G.DATA_WIDTH;
    
    IbTransCoverage #(G) p0TransCoverage;
    IbTransCoverage #(G) p1TransCoverage;
    IbTransCoverage #(G) p2TransCoverage;
    
    IbIfcRxCoverage #(DATA_WIDTH) p0IfcRxCoverage;
    IbIfcTxCoverage #(DATA_WIDTH) p0IfcTxCoverage;
    IbIfcRxCoverage #(DATA_WIDTH) p1IfcRxCoverage;
    IbIfcTxCoverage #(DATA_WIDTH) p1IfcTxCoverage;
    IbIfcRxCoverage #(DATA_WIDTH) p2IfcRxCoverage;
    IbIfcTxCoverage #(DATA_WIDTH) p2IfcTxCoverage;
    
    // -- Constructor ---------------------------------------------------------
    function new (InternalBusDriver #(DATA_WIDTH) p0Driver,
                  InternalBusDriver #(DATA_WIDTH) p1Driver,
                  InternalBusDriver #(DATA_WIDTH) p2Driver,
                  virtual iInternalBusRx.tb #(DATA_WIDTH) iP0Rx,
                  virtual iInternalBusTx.tb #(DATA_WIDTH) iP0Tx,
                  virtual iInternalBusRx.tb #(DATA_WIDTH) iP1Rx,
                  virtual iInternalBusTx.tb #(DATA_WIDTH) iP1Tx,
                  virtual iInternalBusRx.tb #(DATA_WIDTH) iP2Rx,
                  virtual iInternalBusTx.tb #(DATA_WIDTH) iP2Tx,
                  string instNamePrefix = "");
      
      //create transaction coverage and set callbacks to drivers
      p0TransCoverage = new({instNamePrefix,"Port0 Driver"});
      p1TransCoverage = new({instNamePrefix,"Port1 Driver"});
      p2TransCoverage = new({instNamePrefix,"Port2 Driver"});
      p0Driver.setCallbacks(p0TransCoverage);
      p1Driver.setCallbacks(p1TransCoverage);
      p2Driver.setCallbacks(p2TransCoverage);
      
      //create interface coverage
      p0IfcRxCoverage = new(iP0Rx, {instNamePrefix,"Port0 RX Interface"});
      p0IfcTxCoverage = new(iP0Tx, {instNamePrefix,"Port0 TX Interface"});
      p1IfcRxCoverage = new(iP1Rx, {instNamePrefix,"Port1 RX Interface"});
      p1IfcTxCoverage = new(iP1Tx, {instNamePrefix,"Port1 TX Interface"});
      p2IfcRxCoverage = new(iP2Rx, {instNamePrefix,"Port2 RX Interface"});
      p2IfcTxCoverage = new(iP2Tx, {instNamePrefix,"Port2 TX Interface"});
      
      //put coverages to list
      covList.push_back(p0TransCoverage);
      covList.push_back(p1TransCoverage);
      covList.push_back(p2TransCoverage);
      covList.push_back(p0IfcRxCoverage);
      covList.push_back(p0IfcTxCoverage);
      covList.push_back(p1IfcRxCoverage);
      covList.push_back(p1IfcTxCoverage);
      covList.push_back(p2IfcRxCoverage);
      covList.push_back(p2IfcTxCoverage);
      
    endfunction
    
  endclass: IbSwitchCoverage
  
endpackage : switch_coverage_pkg

