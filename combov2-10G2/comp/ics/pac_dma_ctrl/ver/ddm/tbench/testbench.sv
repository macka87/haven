  /*
   * testbench.sv: Top Entity for RX DMA Controller automatic test
   * Copyright (C) 2009 CESNET
   * Author(s): Marcela Šimková <xsimko03@stud.fit.vutbr.cz>
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
     * $Id: testbench.sv 10986 2009-09-03 15:41:23Z xsimko03 $
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
    iDdm #(FLOWS, BLOCK_SIZE)                     MISC (CLK, RESET);
    iInternalBus                                  IB   (CLK, RESET);
    iDmaCtrl  #(DMA_DATA_WIDTH)                   DMA  (CLK, RESET);
    iMi32                                         SW   (CLK, RESET); 
    iDdm #(FLOWS, BLOCK_SIZE)                     RXREQ(CLK, RESET);
    iDdm #(FLOWS, BLOCK_SIZE)                     RXFIFO (CLK, RESET);
    iDdm #(FLOWS, BLOCK_SIZE)                     TXFIFO (CLK, RESET);
    
    //-- Clock generation -------------------------------------------------------
    always #(CLK_PERIOD/2) CLK = ~CLK;

    //-- Design Under Test ------------------------------------------------------
    DUT DUT_U   (.CLK     (CLK),
                 .RESET   (RESET),
                 .MISC    (MISC),
                 .IB      (IB),
                 .DMA     (DMA),
                 .SW      (SW),
                 .RXREQ   (RXREQ),
                 .RXFIFO  (RXFIFO),
                 .TXFIFO  (TXFIFO)
                );

    //-- Test -------------------------------------------------------------------
    TEST TEST_U (.CLK     (CLK),
                 .RESET   (RESET),
                 .MISC    (MISC),
                 .IB      (IB),
                 .DMA     (DMA),
                 .SW      (SW),
                 .RXREQ   (RXREQ),
                 .RXFIFO  (RXFIFO),
                 .TXFIFO  (TXFIFO)
                );

  // --------------------------------------------------------------------------
  // -- MISC Interface properties/assertions
  // --------------------------------------------------------------------------            

  // -- DMA_REQ together with RUN [DMA_IFC] -----------------------------------
  // If DMA_REQ Is active, RUN signal for corresponding flow is active.
  // We have to ignore requests in 3 CLK from STOP and 2 CLK from RUN state.
  property REQRUN;
     int x;
     @(posedge CLK) (DMA.DMA_REQ, x =($rtoi($pow(2, MISC.DMA_IFC))))|->
                                    (($past(MISC.RUN, 2) & x) ||        // Don't works with $past(MISC.RUN[MISC.DMA_IFC], 2)
                                     ($past(MISC.RUN, 3) & x));
  endproperty
  
  assert property (REQRUN) 
    else $error("DMA Request is generated, when RUN[DMA_IFC] is inactive (tolerance 4 CLKs), interface %d", MISC.DMA_IFC);
  
  // -- inactive RUN after SW_DWR = 1 (PAUSE) --------------------------------- 
  // 1 CLK after SW.SW_DWR = 1, RUN signal for corresponding flow is inactive
  for (genvar i=0; i<8; i++)begin
    property PAUSE;
      @(posedge CLK)
        ((SW.SW_DWR == 1) && (SW.SW_ADDR == i*64)) |=>
          (MISC.RUN[i] == 0);    
    endproperty
    
    assert property (PAUSE)
      else $error("RUN is active one clk after pause signal for flow %d",i);
  end  

  // -- inactive RUN after SW_DWR = 0 (STOP) ---------------------------------- 
  // 1 CLK after SW.SW_DWR = 0, RUN signal for corresponding flow is inactive
  for (genvar i=0; i<8; i++)begin
    property STOP;
      @(posedge CLK)
        ((SW.SW_DWR == 0) && (SW.SW_ADDR == i*64)) |=>
          (MISC.RUN[i] == 0);    
    endproperty
    
    assert property (STOP)
      else $error("RUN is active one clk after stop signal for flow %d",i);
  end  
 
  // -- active RUN after SW_DWR = 2 (RUN) ------------------------------------- 
  // 1 CLK after SW.SW_DWR = 2, RUN signal for corresponding flow is activei
  for (genvar i=0; i<8; i++)begin
    property RUN;
      @(posedge CLK)
        ((SW.SW_DWR == 2) && (SW.SW_ADDR == i*64)) |=>
          (MISC.RUN[i] == 1);    
    endproperty
    
    assert property (RUN)
      else $error("RUN is inactive one clk after run signal for flow %d",i);
  end 
  
  // -- active INIT when STOP ------------------------------------------------- 
  // INIT for coresponding block is active when SW_RD = 1 && SW_DRD = 0 && ADDR = block
  for (genvar i=0; i<8; i++)begin
    property INITSTOP;
      @(posedge CLK)
        ((SW.SW_RD == 1) && (SW.SW_DRD == 0) && (SW.SW_ADDR == i*64)) |->
          (MISC.INIT[i] == 1);    
    endproperty
    
    assert property (INITSTOP)
      else $error("INIT for coresponding block is inactive when status register is in state STOP");
  end 

  // -- active RXREQ.RX_RF_DATA_VLD together with DMA.DMA_DONE ---------------
  property RXREQDATAVLD;
     @(posedge CLK) (RXREQ.RX_RF_DATA_VLD)|->(DMA.DMA_DONE); 
  endproperty
  
  assert property (RXREQDATAVLD)
     else $error("RX_RF_DATA_VLD and DMA_DONE signals are not active at the same cycle.");

  // -- active DMA.DMA_REQ for RX0 together with inactive RXREQ.FULL[0] ------
  property RX0DMAREQFULL;
     @(posedge CLK) (DMA.DMA_REQ && (MISC.DMA_IFC == 0))|-> 
                     ((($past(RXREQ.RX_RF_FULL, 2) & 1) == 0) ||
                      (($past(RXREQ.RX_RF_FULL, 3) & 1) == 0));
  endproperty

  assert property (RX0DMAREQFULL)
    else $error("DMA REQ and RX_RF_FULL for RX0 signals are active at the same cycle.");


  // -- active DMA.DMA_REQ for RX1 together with inactive RXREQ.FULL[0] ------
  property RX1DMAREQFULL;
    @(posedge CLK) (DMA.DMA_REQ && (MISC.DMA_IFC == 2))|->
                    ((($past(RXREQ.RX_RF_FULL, 2) & 2) == 0) || 
                     (($past(RXREQ.RX_RF_FULL, 3) & 2) == 0));
  endproperty
  
  assert property (RX1DMAREQFULL)
    else $error("DMA REQ and RX_RF_FULL signals for RX1 are active at the same cycle.");
  
  // -- active DMA.DMA_REQ for RX2 together with inactive RXREQ.FULL[0] ------
  property RX2DMAREQFULL;
    @(posedge CLK) (DMA.DMA_REQ && (MISC.DMA_IFC == 4))|->
                    ((($past(RXREQ.RX_RF_FULL, 2) & 4) == 0) || 
                     (($past(RXREQ.RX_RF_FULL, 3) & 4) == 0));
  endproperty
  
  assert property (RX2DMAREQFULL)
    else $error("DMA REQ and RX_RF_FULL signals for RX2 are active at the same cycle.");
  
  // -- active DMA.DMA_REQ for RX3 together with inactive RXREQ.FULL[0] ------
  property RX3DMAREQFULL;
    @(posedge CLK) (DMA.DMA_REQ && (MISC.DMA_IFC == 6))|->
                    ((($past(RXREQ.RX_RF_FULL, 2) & 8) == 0) || 
                     (($past(RXREQ.RX_RF_FULL, 3) & 8) == 0));
  endproperty
  
  assert property (RX3DMAREQFULL)
    else $error("DMA REQ and RX_RF_FULL signals for RX3 are active at the same cycle.");
endmodule : testbench
