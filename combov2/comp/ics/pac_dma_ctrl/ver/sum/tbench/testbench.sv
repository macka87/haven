/*
 * testbench.sv: Top Entity for Status Update Manager automatic test
 * Copyright (C) 2009 CESNET
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
 * $Id: testbench.sv 11736 2009-10-25 11:01:35Z xsanta06 $
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
  iSum             #(FLOWS, BLOCK_SIZE)      MISC (CLK, RESET);
  iInternalBus                               IB   (CLK, RESET);
  iDmaCtrl         #(DMA_DATA_WIDTH)         DMA  (CLK, RESET);
  iMi32                                      MI32 (CLK, RESET);
  iSum             #(FLOWS, BLOCK_SIZE)      REQ  (CLK, RESET);
  iSu              #(FLOWS, RX_SU_DATA_SIZE) RX_SU(CLK, RESET);
  iSu              #(FLOWS, TX_SU_DATA_SIZE) TX_SU(CLK, RESET);

  
  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET),
               .MISC    (MISC),
               .IB      (IB),
               .DMA     (DMA),
               .MI32    (MI32),
               .REQ     (REQ),
               .RX_SU   (RX_SU),
               .TX_SU   (TX_SU)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK     (CLK),
               .RESET   (RESET),
               .MISC    (MISC),
               .IB      (IB),
               .DMA     (DMA),
               .MI32    (MI32),
               .REQ     (REQ),
               .RX_SU   (RX_SU),
               .TX_SU   (TX_SU)
              );
  // -- TX IDLE ACTIVE --------------------------------------------------------
  // TX IDLE is active until update is incomming. First we define a sequence
  // of waiting for incomming update. Than we decare, that after rising IDLE
  // signal IDLE is active during that sequence (until incomming update).
  for(genvar i=0; i<FLOWS;i++) begin
    sequence txIdle1_seq(int flow);
      ##[0:$] ((TX_SU.SU_DVLD==1) && (TX_SU.SU_ADDR==flow));
    endsequence

    property TXIDLE1;
      int flow;
      @(posedge CLK) disable iff (RESET)
        ($rose(MISC.IDLE[2*i+1]))|->
          (MISC.IDLE[2*i+1]==1) throughout txIdle1_seq(i); 
    endproperty
    
    assert property (TXIDLE1)
      else $error("IDLE[%0d] is not active before incomming update",2*i+1);
  end
 
  // -- TX IDLE UPDATE --------------------------------------------------------
  // After receiving update, IDLE is inactive.
  property TXIDLEUPDATE;
    int flow;
    @(posedge CLK) disable iff (RESET)
      (TX_SU.SU_DVLD==1, flow=TX_SU.SU_ADDR)|=>
        MISC.IDLE[2*flow+1]==0; 
  endproperty
  
  assert property (TXIDLEUPDATE)
    else $error("IDLE is active after receiving update");

  // -- TX IDLE INACTIVE ------------------------------------------------------
  // TX IDLE is inactive until counter status is exported. First we define a 
  // sequence of waiting for exporting counter status. Than we decare, that after
  // falling IDLE signal IDLE is inactive during that sequence (until exporting
  // counter status).
  for(genvar i=0; i<FLOWS;i++) begin
    sequence txIdle0_seq(int flow);
      ##[0:$] (IB.RD_REQ==1 && IB.RD_ADDR=='h1000+(flow/2)*8) 
        ##[1:$] IB.RD_SRC_RDY==1;
    endsequence

    property TXIDLE0;
      int flow;
      @(posedge CLK) disable iff (RESET)
        ($fell(MISC.IDLE[2*i+1]) && !($past(IB.RD_REQ, 1) 
         && $past(IB.RD_ADDR, 1)=='h1000+(i/2)*8)) |->
          (MISC.IDLE[2*i+1]==0) throughout txIdle0_seq(i); 
    endproperty
    
    assert property (TXIDLE0)
      else $error("IDLE[%0d] is active before counter status exporting",2*i+1);
  end
 
  // -- TX IDLE EXPORT --------------------------------------------------------
  // After exporting counter status, IDLE is active.
  for(genvar i=0; i<FLOWS;i++) begin
    property TXIDLEEXPORT;
      @(posedge CLK) disable iff (RESET)
        (IB.RD_REQ==1 && IB.RD_ADDR==(32'h1000+(i/2)*8))|=> 
          (IB.RD_SRC_RDY==1) && (TX_SU.SU_DVLD==0 || TX_SU.SU_ADDR!=i) |=> 
            (MISC.IDLE[2*i+1]==1); 
    endproperty
    
    assert property (TXIDLEEXPORT)
      else $error("IDLE[%0d] is not active after exporting counter status",2*i+1);
  end

endmodule : testbench
