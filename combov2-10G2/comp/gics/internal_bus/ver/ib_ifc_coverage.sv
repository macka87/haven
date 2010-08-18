/*
 * ib_ifc_coverage.sv: Internal Bus functional coverage class
 * Copyright (C) 2009 CESNET
 * Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
 * $Id: ib_ifc_coverage.sv 8517 2009-05-28 10:55:58Z washek $
 *
 * TODO:
 *
 */
  
  import coverage_pkg::Coverage;
  
  // --------------------------------------------------------------------------
  // -- Internal Bus Interface Coverage
  // --------------------------------------------------------------------------
  // Doesn't work as is, must be specialized to RX or TX version
  virtual class IbIfcCoverage extends Coverage;

    string  instanceName;

    // Sampled values from interface
    logic sof_n;
    logic eof_n;
    logic src_rdy_n;
    logic dst_rdy_n;
     
    //-- Covering transactions ----------------------------------------------
    covergroup IbIfcCovergroup;
      
      // Source ready transition coverpoint
      src_rdy: coverpoint src_rdy_n {
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
      dst_rdy: coverpoint dst_rdy_n {
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
        //if src_rdy_n is 1, dst_rdy_n probably don't change from 0 to 1
        //(but it can)
        ignore_bins src1a = ( binsof(src_rdy.t111) || binsof(src_rdy.t110) ||
                              binsof(src_rdy.t101) || binsof(src_rdy.t100) ) &&
                            ( binsof(dst_rdy.t011) || binsof(dst_rdy.t010) );
        ignore_bins src1b = ( binsof(src_rdy.t111) || binsof(src_rdy.t110) ||
                              binsof(src_rdy.t011) || binsof(src_rdy.t010) ) &&
                            ( binsof(dst_rdy.t101) || binsof(dst_rdy.t001) );
        //if dst_rdy_n is 1, src_rdy_n probably don't change from 0 to 1
        //(but it can)
        ignore_bins dst1a = ( binsof(dst_rdy.t111) || binsof(dst_rdy.t110) ||
                              binsof(dst_rdy.t101) || binsof(dst_rdy.t100) ) &&
                            ( binsof(src_rdy.t011) || binsof(src_rdy.t010) );
        ignore_bins dst1b = ( binsof(dst_rdy.t111) || binsof(dst_rdy.t110) ||
                              binsof(dst_rdy.t011) || binsof(dst_rdy.t010) ) &&
                            ( binsof(src_rdy.t101) || binsof(src_rdy.t001) );
      }
      
      // Start of packet crosspoint
      sof: cross sof_n, src_rdy_n, dst_rdy_n {
        ignore_bins sof_src_rdy = binsof(src_rdy_n) intersect {1} && 
                                  binsof(sof_n) intersect {0};
      }

      // End of packet crosspoint
      eof: cross eof_n, src_rdy_n, dst_rdy_n {
        ignore_bins eof_src_rdy = binsof(src_rdy_n) intersect {1} && 
                                  binsof(eof_n) intersect {0}; 
      }
      
      option.per_instance=1; // Also per instance statistics
    endgroup
    
    // -- Constructor ---------------------------------------------------------
    function new (string instanceName);
      IbIfcCovergroup = new;       // Create covergroup
      //enabled=0;                      // Disable interface sampling
      this.instanceName = instanceName;
    endfunction

    // -- Get actual coverage -------------------------------------------------
    function real getCoverage();
      getCoverage = IbIfcCovergroup.get_inst_coverage();
    endfunction : getCoverage
    
    // -- Display coverage statistic ------------------------------------------
    function void display();
       $write("Interface coverage for %s: \t%3.2f %%\n",
               instanceName, IbIfcCovergroup.get_inst_coverage());
    endfunction : display

  endclass: IbIfcCoverage


  // --------------------------------------------------------------------------
  // -- Internal Bus Interface Rx Coverage
  // --------------------------------------------------------------------------
  class IbIfcRxCoverage #(int DATA_WIDTH=64) extends IbIfcCoverage;
  
    // Interface on which coverage is measured
    virtual iInternalBusRx.tb #(DATA_WIDTH) internalBus;

    // -- Constructor ---------------------------------------------------------
    function new (virtual iInternalBusRx.tb #(DATA_WIDTH) internalBus,
                  string instanceName);
      super.new(instanceName);
      this.internalBus = internalBus; // Store interface
    endfunction

    // -- Run command coverage measures ---------------------------------------
    task run();
       while (enabled) begin   // Repeat while enabled
         @(internalBus.cb);    // Wait for clock
         // Sample signals values
         sof_n = internalBus.cb.SOF_N;
         eof_n = internalBus.cb.EOF_N;
         src_rdy_n = internalBus.cb.SRC_RDY_N;
         dst_rdy_n = internalBus.cb.DST_RDY_N;
         IbIfcCovergroup.sample();
      end
    endtask : run

  endclass: IbIfcRxCoverage

  
  // --------------------------------------------------------------------------
  // -- Internal Bus Interface Tx Coverage
  // --------------------------------------------------------------------------
  class IbIfcTxCoverage #(int DATA_WIDTH=64) extends IbIfcCoverage;
  
    // Interface on which coverage is measured
    virtual iInternalBusTx.tb #(DATA_WIDTH) internalBus;

    // -- Constructor ---------------------------------------------------------
    function new (virtual iInternalBusTx.tb #(DATA_WIDTH) internalBus,
                  string instanceName);
      super.new(instanceName);
      this.internalBus = internalBus; // Store interface
    endfunction

    // -- Run command coverage measures ---------------------------------------
    task run();
       while (enabled) begin   // Repeat while enabled
         @(internalBus.cb);    // Wait for clock
         // Sample signals values
         sof_n = internalBus.cb.SOF_N;
         eof_n = internalBus.cb.EOF_N;
         src_rdy_n = internalBus.cb.SRC_RDY_N;
         dst_rdy_n = internalBus.cb.DST_RDY_N;
         IbIfcCovergroup.sample();
      end
    endtask : run

  endclass: IbIfcTxCoverage
