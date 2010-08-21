/*
 * endpoint_coverage.sv: Internal Bus Endpoint functional coverage class
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
 * $Id: endpoint_coverage.sv 8657 2009-06-04 10:57:57Z washek $
 *
 * TODO:
 *
 */
  
package endpoint_coverage_pkg;
  
  import sv_common_pkg::*;
  import ib_common_pkg::*;
  import ib_params_pkg::*;
  import coverage_pkg::*;
  import math_pkg::*;
  
  
  // --------------------------------------------------------------------------
  // -- Internal Bus Transaction Coverage
  // --------------------------------------------------------------------------
  // This class measure some specific transaction coverage. Transactions are
  // send to this class by callback methods.
  // BUS_MASTER: 0 - BM disabled
  //             1 - BM enabled, IB Driver
  //             2 - BM enabled, BM driver (generates BM transactions)
  class IbTransCoverage #(int DATA_WIDTH = 64, bit ALIGNED_ADDR = 0,
                          int BUS_MASTER = 0) extends Coverage;
      
      parameter int DATA_WIDTH_B = DATA_WIDTH/8;
      parameter int LOG2DWB = max(log2(DATA_WIDTH_B),1);
      
      InternalBusTransaction tr;   // Internal Bus transaction
      string instanceName;
      
      //-- Covering transactions ----------------------------------------------
      covergroup IbTransCovergroup;

        // Transaction type coverage
        tt : coverpoint tr.transType {
          bins L2LW = {L2LW};
          bins L2LR = {L2LR};
          illegal_bins glob = {RDC,RDCL,L2GW,G2LR};
          option.weight = 0; //only cross has weight
        }

        // Transaction length coverage
        len : coverpoint tr.length {
          bins lo[]  = {[1:2*DATA_WIDTH_B]};
          bins other = {[2*DATA_WIDTH_B+1:13'h0FFE]};
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
        tt_len    : cross tt, len;
        tt_ga     : cross tt, ga;
        tt_ga_len : cross tt, ga_len;

        option.per_instance=1; // Also per instance statistics
      endgroup
      
      covergroup IbTransCovergroup_bm1;

        // Transaction type coverage
        tt : coverpoint tr.transType {
          bins L2LW = {L2LW};
          bins L2LR = {L2LR};
          bins RDC  = {RDC};
          bins RDCL = {RDCL};
          illegal_bins glob = {L2GW,G2LR};
          option.weight = 0; //only cross has weight
        }

        // Transaction length coverage
        len : coverpoint tr.length {
          bins lo[]  = {[1:2*DATA_WIDTH_B]};
          bins other = {[2*DATA_WIDTH_B+1:13'h0FFE]};
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
        tt_len    : cross tt, len;
        tt_ga     : cross tt, ga;
        tt_ga_len : cross tt, ga_len;

        option.per_instance=1; // Also per instance statistics
      endgroup
      
      covergroup IbTransCovergroup_bm2;

        // Transaction type coverage
        tt : coverpoint tr.transType {
          bins L2LW = {L2LW};
          bins L2LR = {L2LR};
          bins L2GW = {L2GW};
          bins G2LR = {G2LR};
          illegal_bins compl = {RDC,RDCL};
          option.weight = 0; //only cross has weight
        }

        // Transaction length coverage
        len : coverpoint tr.length {
          bins lo[]  = {[1:2*DATA_WIDTH_B]};
          bins other = {[2*DATA_WIDTH_B+1:13'h0FFE]};
          bins hi    = {13'h0FFF};
          bins max   = {13'h1000};
          illegal_bins illegal = default;
          option.weight = 0; //only cross has weight
        }
        
        // Local Address (address alligment)
        la : coverpoint tr.localAddr[LOG2DWB-1:0] {
          option.weight = 0; //only cross has weight
        }

        // Local Address + Length (end of transaction alignment)
        la_len: coverpoint tr.localAddr[LOG2DWB-1:0] + tr.length[LOG2DWB-1:0] {
          option.weight = 0; //only cross has weight
        }
        
        // Cross coverages with TransType
        tt_len    : cross tt, len;
        tt_la     : cross tt, la;
        tt_la_len : cross tt, la_len;

        option.per_instance=1; // Also per instance statistics
      endgroup
      
      covergroup IbTransCovergroup_aligned;

        // Transaction type coverage
        tt : coverpoint tr.transType {
          bins L2LW = {L2LW};
          bins L2LR = {L2LR};
          illegal_bins glob = {RDC,RDCL,L2GW,G2LR};
          option.weight = 0; //only cross has weight
        }

        // Transaction length coverage
        len : coverpoint tr.length {
          bins lo[]  = {[1:2*DATA_WIDTH_B]};
          bins other = {[2*DATA_WIDTH_B+1:13'h0FFE]};
          bins hi    = {13'h0FFF};
          bins max   = {13'h1000};
          illegal_bins illegal = default;
          option.weight = 0; //only cross has weight
        }
        
        // Cross length with TransType
        tt_len : cross tt, len;

        option.per_instance=1; // Also per instance statistics
      endgroup
      
      covergroup IbTransCovergroup_bm1_aligned;

        // Transaction type coverage
        tt : coverpoint tr.transType {
          bins L2LW = {L2LW};
          bins L2LR = {L2LR};
          bins RDC  = {RDC};
          bins RDCL = {RDCL};
          illegal_bins glob = {L2GW,G2LR};
          option.weight = 0; //only cross has weight
        }

        // Transaction length coverage
        len : coverpoint tr.length {
          bins lo[]  = {[1:2*DATA_WIDTH_B]};
          bins other = {[2*DATA_WIDTH_B+1:13'h0FFE]};
          bins hi    = {13'h0FFF};
          bins max   = {13'h1000};
          illegal_bins illegal = default;
          option.weight = 0; //only cross has weight
        }
        
        // Cross length with TransType
        tt_len : cross tt, len;

        option.per_instance=1; // Also per instance statistics
      endgroup
      
      covergroup IbTransCovergroup_bm2_aligned;

        // Transaction type coverage
        tt : coverpoint tr.transType {
          bins L2LW = {L2LW};
          bins L2LR = {L2LR};
          bins L2GW = {L2GW};
          bins G2LR = {G2LR};
          illegal_bins compl = {RDC,RDCL};
          option.weight = 0; //only cross has weight
        }

        // Transaction length coverage
        len : coverpoint tr.length {
          bins lo[]  = {[1:2*DATA_WIDTH_B]};
          bins other = {[2*DATA_WIDTH_B+1:13'h0FFE]};
          bins hi    = {13'h0FFF};
          bins max   = {13'h1000};
          illegal_bins illegal = default;
          option.weight = 0; //only cross has weight
        }
        
        // Cross length with TransType
        tt_len : cross tt, len;

        option.per_instance=1; // Also per instance statistics
      endgroup
      
      
    // -- Constructor ---------------------------------------------------------
    // Constructor
    function new(string instanceName);
      enabled = 0;
      this.instanceName = instanceName;
      
      // Create covergroup
      if (ALIGNED_ADDR) begin
        case (BUS_MASTER)
          0: IbTransCovergroup_aligned = new;
          1: IbTransCovergroup_bm1_aligned = new;
          2: IbTransCovergroup_bm2_aligned = new;
        endcase;
      end else begin
        case (BUS_MASTER)
          0: IbTransCovergroup = new;
          1: IbTransCovergroup_bm1 = new;
          2: IbTransCovergroup_bm2 = new;
        endcase;
      end
      
    endfunction

    // -- Function is called after a transaction is sent ----------------------
    virtual task post_tx(Transaction transaction, string inst);
      InternalBusTransaction tr;
      if (enabled) begin;
        $cast(tr,transaction);
        this.tr=tr;  // Save current transaction
        
        // Sample statistics
        if (ALIGNED_ADDR) begin
          case (BUS_MASTER)
            0: IbTransCovergroup_aligned.sample();
            1: IbTransCovergroup_bm1_aligned.sample();
            2: IbTransCovergroup_bm2_aligned.sample();
          endcase;
        end else begin
          case (BUS_MASTER)
            0: IbTransCovergroup.sample();
            1: IbTransCovergroup_bm1.sample();
            2: IbTransCovergroup_bm2.sample();
          endcase;
        end
        
      end
    endtask
    
    // -- Get actual coverage -------------------------------------------------
    function real getCoverage();
      if (ALIGNED_ADDR) begin
        case (BUS_MASTER)
          0: getCoverage = IbTransCovergroup_aligned.get_inst_coverage();
          1: getCoverage = IbTransCovergroup_bm1_aligned.get_inst_coverage();
          2: getCoverage = IbTransCovergroup_bm2_aligned.get_inst_coverage();
        endcase;
      end else begin
        case (BUS_MASTER)
          0: getCoverage = IbTransCovergroup.get_inst_coverage();
          1: getCoverage = IbTransCovergroup_bm1.get_inst_coverage();
          2: getCoverage = IbTransCovergroup_bm2.get_inst_coverage();
        endcase;
      end
    endfunction : getCoverage
    
    // -- Display coverage statistic ------------------------------------------
    function void display();
       $write("Transaction coverage for %s: \t%3.2f %%\n",
              instanceName, getCoverage());
    endfunction

  endclass : IbTransCoverage
  
  
  // --------------------------------------------------------------------------
  // -- Endpoint Write Interface Coverage
  // --------------------------------------------------------------------------
  class IbEndpointWriteCoverage #(int DATA_WIDTH = 64, int ADDR_WIDTH = 32)
                                                              extends Coverage;

    // Interface on which coverage is measured
    virtual iIbEndpointWrite.tb #(DATA_WIDTH, ADDR_WIDTH) ifc;
    string  instanceName;

    // Sampled values from interface
    logic req;
    logic rdy;
    
    //-- Request and ready covergroup -----------------------------------------
    covergroup covReqRdy @(ifc.cb);
      
      // Request transition coverpoint
      req: coverpoint req {
        bins t000 = (0 => 0 => 0);
        bins t001 = (0 => 0 => 1);
        bins t010 = (0 => 1 => 0);
        bins t011 = (0 => 1 => 1);
        bins t100 = (1 => 0 => 0);
        bins t101 = (1 => 0 => 1);
        bins t110 = (1 => 1 => 0);
        bins t111 = (1 => 1 => 1);
        option.weight = 0; //only cross has weight
      }
      // Ready transition coverpoint
      rdy: coverpoint rdy {
        bins t000 = (0 => 0 => 0);
        bins t001 = (0 => 0 => 1);
        bins t010 = (0 => 1 => 0);
        bins t011 = (0 => 1 => 1);
        bins t100 = (1 => 0 => 0);
        bins t101 = (1 => 0 => 1);
        bins t110 = (1 => 1 => 0);
        bins t111 = (1 => 1 => 1);
        option.weight = 0; //only cross has weight
      }
      
      // Request and ready crosspoints
      req_rdy: cross req, rdy {
        //if rdy is zero, req shouldn't change from one to zero
        ignore_bins rdy0a = ( binsof(rdy.t000) || binsof(rdy.t001) ||
                              binsof(rdy.t010) || binsof(rdy.t011) ) &&
                            ( binsof(req.t100) || binsof(req.t101) );
        ignore_bins rdy0b = ( binsof(rdy.t000) || binsof(rdy.t001) ||
                              binsof(rdy.t100) || binsof(rdy.t101) ) &&
                            ( binsof(req.t010) || binsof(req.t110) );
      }
      
      option.per_instance=1; // Also per instance statistics
    endgroup : covReqRdy

    
    // -- Constructor ---------------------------------------------------------
    function new (virtual iIbEndpointWrite.tb #(DATA_WIDTH, ADDR_WIDTH) ifc,
                  string instanceName);
      
      enabled=0;                       // Disable interface sampling
      this.ifc = ifc;                  // Store interface
      this.instanceName = instanceName;
      covReqRdy = new;
    endfunction

    // -- Run coverage measures -----------------------------------------------
    task run();
       while (enabled) begin   // Repeat while enabled
         @(ifc.cb);            // Wait for clock
         // Sample signals values
         req     = ifc.cb.REQ;
         rdy     = ifc.cb.RDY;
      end
    endtask : run
    
    // -- Get actual coverage -------------------------------------------------
    function real getCoverage();
      getCoverage = covReqRdy.get_inst_coverage();
    endfunction : getCoverage
    
    // -- Display coverage statistic ------------------------------------------
    function void display();
       $write("Interface coverage for %s: \t%3.2f %%\n",
               instanceName, getCoverage());
    endfunction : display

  endclass: IbEndpointWriteCoverage
  
  

  // --------------------------------------------------------------------------
  // -- Endpoint Read Interface Coverage
  // --------------------------------------------------------------------------
  class IbEndpointReadCoverage #(pIbEndpointGenerics G = dIbEndpointGenerics)
                                                              extends Coverage;
    
    parameter int DW = G.DATA_WIDTH;
    parameter int AW = G.ADDR_WIDTH;
    
    // Interface on which coverage is measured
    virtual iIbEndpointRead.tb #(DW, AW) ifc;
    string  instanceName;

    // Sampled values from interface
    logic req;
    logic ardy;
    logic src_rdy;
    logic dst_rdy;

    //-- Request and ready covergroup (read_type = continual) -----------------
    covergroup covReqArdy_cont @(ifc.cb);
      
      // Request transition coverpoint
      req: coverpoint req {
        bins t000 = (0 => 0 => 0);
        bins t001 = (0 => 0 => 1);
        bins t010 = (0 => 1 => 0);
        bins t011 = (0 => 1 => 1);
        bins t100 = (1 => 0 => 0);
        bins t101 = (1 => 0 => 1);
        bins t110 = (1 => 1 => 0);
        bins t111 = (1 => 1 => 1);
        option.weight = 0; //only cross has weight
      }
      // Ready transition coverpoint
      ardy: coverpoint ardy {
        bins t000 = (0 => 0 => 0);
        bins t001 = (0 => 0 => 1);
        bins t010 = (0 => 1 => 0);
        bins t011 = (0 => 1 => 1);
        bins t100 = (1 => 0 => 0);
        bins t101 = (1 => 0 => 1);
        bins t110 = (1 => 1 => 0);
        bins t111 = (1 => 1 => 1);
        option.weight = 0; //only cross has weight
      }
      
      // Request and ready crosspoints
      req_ardy: cross req, ardy {
        //if ardy is zero, req shouldn't change from one to zero
        ignore_bins ardy0a = ( binsof(ardy.t000) || binsof(ardy.t001) ||
                               binsof(ardy.t010) || binsof(ardy.t011) ) &&
                             ( binsof(req.t100)  || binsof(req.t101) );
        ignore_bins ardy0b = ( binsof(ardy.t000) || binsof(ardy.t001) ||
                               binsof(ardy.t100) || binsof(ardy.t101) ) &&
                             ( binsof(req.t010)  || binsof(req.t110) );
      }
      
      option.per_instance=1; // Also per instance statistics
    endgroup : covReqArdy_cont
    
    //-- Request and ready covergroup (read_type = packet) --------------------
    covergroup covReqArdy_packet @(ifc.cb);
      
      // Request transition coverpoint
      req: coverpoint req {
        bins t000 = (0 => 0 => 0);
        bins t001 = (0 => 0 => 1);
        bins t010 = (0 => 1 => 0);
        bins t011 = (0 => 1 => 1);
        bins t100 = (1 => 0 => 0);
        //bins t101 = (1 => 0 => 1);
        bins t110 = (1 => 1 => 0);
        bins t111 = (1 => 1 => 1);
      }
      // Ready transition coverpoint
      ardy: coverpoint ardy {
        bins t000 = (0 => 0 => 0);
        bins t001 = (0 => 0 => 1);
        bins t010 = (0 => 1 => 0);
        bins t011 = (0 => 1 => 1);
        bins t100 = (1 => 0 => 0);
        bins t101 = (1 => 0 => 1);
        bins t110 = (1 => 1 => 0);
        bins t111 = (1 => 1 => 1);
      }
      
      option.per_instance=1; // Also per instance statistics
    endgroup : covReqArdy_packet
    
    //-- Source and destination ready covergroup ------------------------------
    covergroup covSrcDstRdy @(ifc.cb);
      
      // Source ready transition coverpoint
      src_rdy: coverpoint src_rdy {
        bins t000 = (0 => 0 => 0);
        bins t001 = (0 => 0 => 1);
        bins t010 = (0 => 1 => 0);
        bins t011 = (0 => 1 => 1);
        bins t100 = (1 => 0 => 0);
        bins t101 = (1 => 0 => 1);
        bins t110 = (1 => 1 => 0);
        bins t111 = (1 => 1 => 1);
        option.weight = 0; //only cross has weight
      }
      // Destination ready transition coverpoint
      dst_rdy: coverpoint dst_rdy {
        bins t000 = (0 => 0 => 0);
        bins t001 = (0 => 0 => 1);
        bins t010 = (0 => 1 => 0);
        bins t011 = (0 => 1 => 1);
        bins t100 = (1 => 0 => 0);
        bins t101 = (1 => 0 => 1);
        bins t110 = (1 => 1 => 0);
        bins t111 = (1 => 1 => 1);
        option.weight = 0; //only cross has weight
      }
      
      // src_rdy and dst_rdy crosspoint
      src_dst_rdy: cross src_rdy, dst_rdy {
        //if src_rdy is zero, dst_rdy shouldn't change from one to zero
        ignore_bins src0a = ( binsof(src_rdy.t000) || binsof(src_rdy.t001) ||
                              binsof(src_rdy.t010) || binsof(src_rdy.t011) ) &&
                            ( binsof(dst_rdy.t100) || binsof(dst_rdy.t101) );
        ignore_bins src0b = ( binsof(src_rdy.t000) || binsof(src_rdy.t001) ||
                              binsof(src_rdy.t100) || binsof(src_rdy.t101) ) &&
                            ( binsof(dst_rdy.t010) || binsof(dst_rdy.t110) );
      }
      
      option.per_instance=1; // Also per instance statistics
    endgroup : covSrcDstRdy
    
    // -- Constructor ---------------------------------------------------------
    function new (virtual iIbEndpointRead.tb #(DW, AW) ifc,
                  string instanceName);
      
      enabled=0;                       // Disable interface sampling
      this.ifc = ifc;                  // Store interface
      this.instanceName = instanceName;
      
      if (G.READ_TYPE == CONTINUAL)
        covReqArdy_cont = new;
      else
        covReqArdy_packet = new;
      
      covSrcDstRdy = new;
      
    endfunction

    // -- Run coverage measures -----------------------------------------------
    task run();
       while (enabled) begin   // Repeat while enabled
         @(ifc.cb);            // Wait for clock
         // Sample signals values
         req     = ifc.cb.REQ;
         ardy    = ifc.cb.ARDY_ACCEPT;
         src_rdy = ifc.cb.SRC_RDY;
         dst_rdy = ifc.cb.DST_RDY;
      end
    endtask: run
    
    // -- Get actual coverage -------------------------------------------------
    function real getCoverage();
      getCoverage = covSrcDstRdy.get_inst_coverage();
      
      if (G.READ_TYPE == CONTINUAL)
        getCoverage += covReqArdy_cont.get_inst_coverage(); 
      else
        getCoverage += covReqArdy_packet.get_inst_coverage();
      
      getCoverage /= 2;
    endfunction : getCoverage
    
    // -- Display coverage statistic ------------------------------------------
    function void display();
       $write("Interface coverage for %s: \t%3.2f %%\n",
               instanceName, getCoverage());
    endfunction : display

  endclass: IbEndpointReadCoverage
  
  
  
  // --------------------------------------------------------------------------
  // -- Endpoint Coverage
  // --------------------------------------------------------------------------
  class IbEndpointCoverage #(pIbEndpointGenerics G = dIbEndpointGenerics)
                                                       extends CoverageWrapper;
    
    IbTransCoverage         #(G.DATA_WIDTH,!G.DATA_REORDER,
                              G.BUS_MASTER_ENABLE)   ibTransCoverage;
    IbTransCoverage         #(G.DATA_WIDTH,!G.DATA_REORDER,2) bmTransCoverage;
    IbIfcRxCoverage         #(G.DATA_WIDTH)                   ibIfcRxCoverage;
    IbIfcTxCoverage         #(G.DATA_WIDTH)                   ibIfcTxCoverage;
    IbEndpointWriteCoverage #(G.DATA_WIDTH, G.ADDR_WIDTH)     writeCoverage;
    IbEndpointReadCoverage  #(G)                              readCoverage;
    
    parameter int DW = G.DATA_WIDTH;
    parameter int AW = G.ADDR_WIDTH;
    
    // -- Constructor ---------------------------------------------------------
    function new (InternalBusDriver #(DW)  ibDriver,
                  InternalBusDriver #(DW)  bmDriver,
                  virtual iInternalBusRx.tb  #(DW)    iIbRx,
                  virtual iInternalBusTx.tb  #(DW)    iIbTx,
                  virtual iIbEndpointWrite.tb#(DW,AW) iWrite,
                  virtual iIbEndpointRead.tb #(DW,AW) iRead,
                  string instNamePrefix = "");
      
      //create transaction coverage and set callbacks to drivers
      ibTransCoverage = new({instNamePrefix,"IB Driver"});
      ibDriver.setCallbacks(ibTransCoverage);
      covList.push_back(ibTransCoverage);
      if (G.BUS_MASTER_ENABLE) begin
        bmTransCoverage = new({instNamePrefix,"BM Driver"});
        bmDriver.setCallbacks(bmTransCoverage);
        covList.push_back(bmTransCoverage);
      end
      
      //create interface coverage
      ibIfcRxCoverage = new(iIbRx, {instNamePrefix,"IB Down"});
      ibIfcTxCoverage = new(iIbTx, {instNamePrefix,"IB Up"});
      writeCoverage   = new(iWrite,{instNamePrefix,"Write"});
      readCoverage    = new(iRead, {instNamePrefix,"Read"});
      covList.push_back(ibIfcRxCoverage);
      covList.push_back(ibIfcTxCoverage);
      covList.push_back(writeCoverage);
      covList.push_back(readCoverage);
      
    endfunction
    
  endclass: IbEndpointCoverage
  
endpackage : endpoint_coverage_pkg
