/*
 * transformer_coverage.sv: Internal Bus Transformer functional coverage class
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
 * $Id: transformer_coverage.sv 8657 2009-06-04 10:57:57Z washek $
 *
 * TODO:
 *
 */
  
package transformer_coverage_pkg;
  
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
  class IbTransCoverage #(int UP_DW = 64) extends Coverage;
      
    InternalBusTransaction tr;   // Internal Bus transaction
    string instanceName;
    
    parameter int LOG2DWB = log2(UP_DW/8);
    
    //-- Covering transactions ----------------------------------------------
    covergroup IbTransCovergroup;

      // Transaction type coverage
      tt : coverpoint tr.transType {
        bins write = {L2LW, L2GW, RDC, RDCL};
        ignore_bins read  = {L2LR, G2LR}; //only write trans have data
        option.weight = 0; //only cross has weight
      }

      // Transaction length coverage
      len : coverpoint tr.length {
        bins lo[]  = {[1:2*UP_DW/8]};
        bins other = {[2*UP_DW/8+1:13'h0FFE]};
        bins hi    = {13'h0FFF};
        bins max   = {13'h1000};
        illegal_bins illegal = default;
        option.weight = 0; //only cross has weight
      }
      
      // Global Address (address alligment)
      ga : coverpoint tr.globalAddr[LOG2DWB-1:0] {
        option.weight = 0; //only cross has weight
      }

      // Global Address + Length (end of transaction alignment)
      ga_len: coverpoint tr.globalAddr[LOG2DWB-1:0] + tr.length[LOG2DWB-1:0] {
        option.weight = 0; //only cross has weight
      }
      
      // Cross coverages with TransType
      tt_len   : cross tt, len;
      tt_align : cross tt, ga, ga_len;

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
  // -- Transformer Coverage
  // --------------------------------------------------------------------------
  class IbTransformerCoverage #(int UP_DW = 64, int DOWN_DW = 8)
                                                       extends CoverageWrapper;
    
    IbTransCoverage  #(UP_DW)   upTransCoverage;
    IbTransCoverage  #(UP_DW)   downTransCoverage;
    
    IbIfcRxCoverage  #(UP_DW)   upIfcRxCoverage;
    IbIfcTxCoverage  #(UP_DW)   upIfcTxCoverage;
    IbIfcRxCoverage  #(DOWN_DW) downIfcRxCoverage;
    IbIfcTxCoverage  #(DOWN_DW) downIfcTxCoverage;
    
    // -- Constructor ---------------------------------------------------------
    function new (InternalBusDriver #(UP_DW)    upDriver,
                  InternalBusDriver #(DOWN_DW)  downDriver,
                  virtual iInternalBusRx.tb   #(UP_DW)   iUpRx,
                  virtual iInternalBusTx.tb   #(UP_DW)   iUpTx,
                  virtual iInternalBusRx.tb   #(DOWN_DW) iDownRx,
                  virtual iInternalBusTx.tb   #(DOWN_DW) iDownTx,
                  string instNamePrefix = "");
      
      //create transaction coverage and set callbacks to drivers
      upTransCoverage = new({instNamePrefix,"UP Driver"});
      downTransCoverage = new({instNamePrefix,"DOWN Driver"});
      upDriver.setCallbacks(upTransCoverage);
      downDriver.setCallbacks(downTransCoverage);
      
      //create interface coverage
      upIfcRxCoverage = new(iUpRx, {instNamePrefix,"UP RX Interface"});
      upIfcTxCoverage = new(iUpTx, {instNamePrefix,"UP TX Interface"});
      downIfcRxCoverage = new(iDownRx, {instNamePrefix,"DOWN RX Interface"});
      downIfcTxCoverage = new(iDownTx, {instNamePrefix,"DOWN TX Interface"});
      
      //put coverages to list
      covList.push_back(upTransCoverage);
      covList.push_back(downTransCoverage);
      covList.push_back(upIfcRxCoverage);
      covList.push_back(upIfcTxCoverage);
      covList.push_back(downIfcRxCoverage);
      covList.push_back(downIfcTxCoverage);
      
    endfunction
    
  endclass: IbTransformerCoverage
  
  
endpackage : transformer_coverage_pkg

