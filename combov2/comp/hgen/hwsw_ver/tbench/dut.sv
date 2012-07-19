/* *****************************************************************************
 * Project Name: HGEN Functional Verification
 * File Name:    dut.sv - Design Under Test
 * Description:  DUT interfaces
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         24.4.2011 
 * ************************************************************************** */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

/*
 *  Module declaration
 */

module DUT (
   input logic CLK,
   input logic RESET,
   iFrameLinkRx.dut RX,
   iFrameLinkTx.dut TX,
   iFrameLinkTx.dut MONITOR,
   iMi32.dut        MI32_RXTX
  );

/*
 *  Module body
 */
 //DOUBLE_MULTI_HGEN_VER_COVER #(
 MULTI_HGEN_VER_COVER #(
 //HGEN #(
 //HGEN_VER_COVER #(
     .DATA_WIDTH     (DATA_WIDTH),
     .BRANCH_COUNT   (BRANCH_COUNT),
     .USE_BRAMS_FOR_HGEN_FIFO  (USE_BRAMS_FOR_HGEN_FIFO)
     //.UH_SIZE        (UH_SIZE),
     //.FLOWID_WIDTH   (FLOWID_WIDTH),
     //.ITEMS          (ITEMS)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK           (CLK),
     .RESET         (RESET),
 
    // Port 0
     .RX_DATA       (RX.DATA),
     .RX_REM        (RX.DREM),
     .RX_SOF_N      (RX.SOF_N),
     .RX_EOF_N      (RX.EOF_N),
     .RX_SOP_N      (RX.SOP_N),
     .RX_EOP_N      (RX.EOP_N),
     .RX_SRC_RDY_N  (RX.SRC_RDY_N),
     .RX_DST_RDY_N  (RX.DST_RDY_N),

    // Port 0
     .TX_DATA       (TX.DATA),
     .TX_REM        (TX.DREM),
     .TX_SOF_N      (TX.SOF_N),
     .TX_EOF_N      (TX.EOF_N),
     .TX_SOP_N      (TX.SOP_N),
     .TX_EOP_N      (TX.EOP_N),
     .TX_SRC_RDY_N  (TX.SRC_RDY_N),
     .TX_DST_RDY_N  (TX.DST_RDY_N)
     
     /*.MI_DWR        (MI32_RXTX.DWR),
     .MI_ADDR       (MI32_RXTX.ADDR),
     .MI_RD         (MI32_RXTX.RD),
     .MI_WR         (MI32_RXTX.WR),
     .MI_BE         (MI32_RXTX.BE),
     .MI_DRD        (MI32_RXTX.DRD),
     .MI_ARDY       (MI32_RXTX.ARDY),
     .MI_DRDY       (MI32_RXTX.DRDY),
     
     .MASK          (HGEN_MASK)*/ 
  );
endmodule : DUT
