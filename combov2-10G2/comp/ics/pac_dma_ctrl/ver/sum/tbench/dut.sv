/*
 * DUT.sv: Design under test
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
 * $Id: dut.sv 10483 2009-08-18 13:14:26Z xsanta06 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic            CLK,
   input logic            RESET,
   iSum.misc_dut          MISC,
   iInternalBus.ib_read   IB,
   iDmaCtrl.dma           DMA,
   iMi32.dut              MI32,
   iSum.reqFifo_dut       REQ,
   iSu.su_dut             RX_SU,
   iSu.su_dut             TX_SU
);

// -------------------- Module body -------------------------------------------
sum #(
        .BASE_ADDR          (BASE_ADDR),      
        .IFCS               (FLOWS),
        .BLOCK_SIZE         (BLOCK_SIZE),
        .DMA_ID             (DMA_ID),           
        .DMA_DATA_WIDTH     (DMA_DATA_WIDTH),   
        .NFIFO_LUT_MEMORY   (NFIFO_LUT_MEMORY)       
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK            (CLK),
     .RESET          (RESET),
    
    // Misc signals 
     .INTERRUPT      (MISC.INTERRUPT),
     .IDLE           (MISC.IDLE),         
     .FLUSH          (MISC.FLUSH),
     .INIT           (MISC.INIT),
 
    // Write interface (InternalBus)
     .IB_RD_ADDR        (IB.RD_ADDR),
     .IB_RD_DATA        (IB.RD_DATA),
     .IB_RD_BE          (IB.RD_BE),
     .IB_RD_REQ         (IB.RD_REQ),
     .IB_RD_ARDY        (IB.RD_ARDY),
     .IB_RD_SRC_RDY     (IB.RD_SRC_RDY),

    // DMA Interface 
     .DMA_ADDR       (DMA.DMA_ADDR),
     .DMA_DOUT       (DMA.DMA_DOUT),
     .DMA_REQ        (DMA.DMA_REQ),
     .DMA_ACK        (DMA.DMA_ACK),
     .DMA_DONE       (DMA.DMA_DONE),
     .DMA_TAG        (DMA.DMA_TAG),

    // SW memory interface
     .MI_SW_DWR      (MI32.DWR),
     .MI_SW_ADDR     (MI32.ADDR),
     .MI_SW_RD       (MI32.RD), 
     .MI_SW_WR       (MI32.WR),
     .MI_SW_BE       (MI32.BE),
     .MI_SW_DRD      (MI32.DRD),
     .MI_SW_ARDY     (MI32.ARDY),
     .MI_SW_DRDY     (MI32.DRDY),     

    // RxReqFifo interface
     .RX_RF_RADDR    (REQ.RX_RF_RADDR), 
     .RX_RF_DOUT     (REQ.RX_RF_DOUT),  
     .RX_RF_DVLD     (REQ.RX_RF_DVLD),  
     .RX_RF_EMPTY    (REQ.RX_RF_EMPTY), 
     .RX_RF_READ     (REQ.RX_RF_READ),  
     .RX_RF_STATUS   (REQ.RX_RF_STATUS),

    // RX Status update interface
     .RX_SU_ADDR     (RX_SU.SU_ADDR),
     .RX_SU_DATA     (RX_SU.SU_DATA),
     .RX_SU_DVLD     (RX_SU.SU_DVLD),
     .RX_SU_HFULL    (RX_SU.SU_HFULL),
    
    // TX Status update interface
     .TX_SU_ADDR     (TX_SU.SU_ADDR),
     .TX_SU_DATA     (TX_SU.SU_DATA),
     .TX_SU_DVLD     (TX_SU.SU_DVLD),
     .TX_SU_HFULL    (TX_SU.SU_HFULL)
);

endmodule : DUT
