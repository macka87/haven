/*
 * DUT.sv: Design under test
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
 * $Id: dut.sv 10701 2009-08-25 15:07:45Z xspinl00 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants
import math_pkg::*; // log2

module DUT (
   input logic                  CLK,
   input logic                  RESET,
   iDdm.misc                    MISC,
   iInternalBus.ib_write        IB,
   iDmaCtrl.dma                 DMA,
   iMi32.mi32                   SW,
   iDdm.rxreq                   RXREQ,
   iDdm.rxnfifo                 RXFIFO,
   iDdm.txnfifo                 TXFIFO
  );

// -------------------- Module body -------------------------------------------
ddm #(
        .IFCS                   (FLOWS),
        .BASE_ADDR              (BASE_ADDR),
        .BLOCK_SIZE             (BLOCK_SIZE),
        .DMA_ID                 (DMA_ID),
        .DMA_DATA_WIDTH         (DMA_DATA_WIDTH),
        .NFIFO_LUT_MEMORY       (NFIFO_LUT_MEMORY)
   )

   VHDL_DUT_U  (
     // Common Interface
     .CLK            (CLK),
     .RESET          (RESET),
    
     // Misc signals 
     .RUN            (MISC.RUN),
     .DMA_IFC        (MISC.DMA_IFC),
     .IDLE           (MISC.IDLE),
     .INIT           (MISC.INIT),
  
     // InternalBus Interface
     .IB_WR_ADDR     (IB.WR_ADDR),
     .IB_WR_DATA     (IB.WR_DATA), 
     .IB_WR_BE       (IB.WR_BE),
     .IB_WR_REQ      (IB.WR_REQ),
     .IB_WR_RDY      (IB.WR_RDY),
     
     // DMA Interface 
     .DMA_ADDR       (DMA.DMA_ADDR),
     .DMA_DOUT       (DMA.DMA_DOUT),
     .DMA_REQ        (DMA.DMA_REQ),
     .DMA_ACK        (DMA.DMA_ACK),
     .DMA_DONE       (DMA.DMA_DONE),
     .DMA_TAG        (DMA.DMA_TAG),
     
     // MI32 Interface
     .MI_SW_DWR      (SW.SW_DWR),
     .MI_SW_ADDR     (SW.SW_ADDR),
     .MI_SW_RD       (SW.SW_RD),
     .MI_SW_WR       (SW.SW_WR),
     .MI_SW_BE       (SW.SW_BE),
     .MI_SW_DRD      (SW.SW_DRD),
     .MI_SW_ARDY     (SW.SW_ARDY),
     .MI_SW_DRDY     (SW.SW_DRDY),
     
     // RX Request fifo Interface
     .RX_RF_ADDR     (RXREQ.RX_RF_ADDR),
     .RX_RF_DATA     (RXREQ.RX_RF_DATA),
     .RX_RF_DATA_VLD (RXREQ.RX_RF_DATA_VLD),
     .RX_RF_FULL     (RXREQ.RX_RF_FULL),
     .RX_RF_INIT     (RXREQ.RX_RF_INIT),

     // RX Nfifo Interface to RX DMA Controller
     .RX_NFIFO_DOUT  (RXFIFO.RX_NFIFO_DOUT),
     .RX_NFIFO_DOUT_VLD  (RXFIFO.RX_NFIFO_DOUT_VLD),
     .RX_NFIFO_RADDR (RXFIFO.RX_NFIFO_RADDR),
     .RX_NFIFO_RD    (RXFIFO.RX_NFIFO_RD),
     .RX_NFIFO_EMPTY (RXFIFO.RX_NFIFO_EMPTY),

     // TX Nfifo Interface to TX DMA Controller
     .TX_NFIFO_DOUT  (TXFIFO.TX_NFIFO_DOUT),
     .TX_NFIFO_DOUT_VLD  (TXFIFO.TX_NFIFO_DOUT_VLD),
     .TX_NFIFO_RADDR (TXFIFO.TX_NFIFO_RADDR),
     .TX_NFIFO_RD    (TXFIFO.TX_NFIFO_RD),
     .TX_NFIFO_EMPTY (TXFIFO.TX_NFIFO_EMPTY)
     );

endmodule : DUT
