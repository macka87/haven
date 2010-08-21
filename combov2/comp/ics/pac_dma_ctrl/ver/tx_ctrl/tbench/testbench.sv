/*
 * testbench.sv: Top Entity for TX DMA Controller automatic test
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
 * $Id: testbench.sv 9399 2009-07-14 19:51:39Z xsanta06 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//                                 TESTBENCH
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module testbench;

  // -- Testbench wires and interfaces ----------------------------------------
  logic            CLK   = 0;
  logic            RESET;
  iInternalBus                              IB   (CLK, RESET);
  iPacDmaCtrl      #(FLOWS)                 MISC (CLK, RESET);
  iPacDmaCtrl      #(FLOWS)                 DESC (CLK, RESET);
  iPacDmaCtrl      #(FLOWS)                 SU   (CLK, RESET);
  iDmaCtrl         #(CTRL_DMA_DATA_WIDTH)   DMA  (CLK, RESET);
  iFrameLinkTx     #(TXDWIDTH, TXDREMWIDTH) FL   [FLOWS] (CLK, RESET);

  
  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET),
               .IB      (IB),
               .MISC    (MISC),
               .DESC    (DESC),
               .SU      (SU),
               .DMA     (DMA),
               .FL      (FL)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK     (CLK),
               .RESET   (RESET),
               .IB      (IB),
               .MISC    (MISC),
               .DESC    (DESC),
               .SU      (SU),
               .DMA     (DMA),
               .FL      (FL),
               .MONITOR (FL)
              );
  // --------------------------------------------------------------------------
  // -- MISC Interface properties/assertions
  // --------------------------------------------------------------------------            

  // -- Not DESC_READ and DMA_REQ when IDLE -----------------------------------
  // DESC_READ and DMA_REQ can not be active if IDLE is active
  property READREQIDLE;
     @(posedge CLK) (MISC.IDLE)|->(!DESC.DESC_READ&&!DMA.DMA_REQ); 
  endproperty
  
  assert property (READREQIDLE)
     else $error("DESC_READ and DMA_REQ are active at the same cycle with IDLE.");
     
  // -- DESC_READ together with RUN [DESC_ADDR] -------------------------------
  // If DESC_READ is active, RUN signal for corresponding flow is active.
  property READRUN;
     int flow;
     @(posedge CLK) disable iff (RESET)
       ($rose(DESC.DESC_READ), flow = DESC.DESC_ADDR)|->
         (MISC.RUN[DESC.DESC_ADDR])|=>
           ##[0:$] ($rose(DESC.DESC_READ) && (flow == DESC.DESC_ADDR));
  endproperty
  
  assert property (READRUN)
     else $error("DESC_READ and RUN[DESC_ADDR] for corresponding block signals are not active at the same cycle.");  
  
  // -- Not DESC_READ if HFULL ------------------------------------------------
  // If HFULL is active, there is no active DESC_READ for corresponding block.
  for (genvar i=0; i<FLOWS; i++) begin   
    property HFULL0;
       @(posedge CLK) (SU.SU_HFULL[i])|->(!(DESC.DESC_READ && (DESC.DESC_ADDR==i))); 
    endproperty
  
    assert property (HFULL0)
       else $error("DESC_READ for flow %d can not be active together with HFULL[%d].",i,i);   
  end

  // -- DMA_REQ after DESC_READ -----------------------------------------------
  // After read rescriptor, there is matching DMA_REQ
  property DESCRIPTOR;
     int flow;
     @(posedge CLK) disable iff (RESET)
       ($rose(DESC.DESC_READ), flow = DESC.DESC_ADDR)|=>
         ##[0:$] ($rose(DESC.DESC_READ) && (flow == DESC.DESC_ADDR))|=>
           ##[0:$] (DMA.DMA_REQ); 
  endproperty
  
  assert property (DESCRIPTOR)
     else $error("DMA_REQ is not active after descriptor read.");
 
endmodule : testbench
