/*
 * ib_switch.sv: IB_SWITCH System Verilog envelope
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
 * $Id: ib_switch.sv 12297 2009-12-16 18:17:27Z washek $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------

import ib_params_pkg::*;

module IB_SWITCH_SV #(pIbSwitchGenerics G = dIbSwitchGenerics) (
   input logic CLK,
   input logic RESET,
   iInternalBusRx.dut    UP_RX,
   iInternalBusTx.dut    UP_TX,
   iInternalBusRx.dut    D1_RX,
   iInternalBusTx.dut    D1_TX,
   iInternalBusRx.dut    D2_RX,
   iInternalBusTx.dut    D2_TX
   );
   
   if (G.MASTER)
      IB_SWITCH_MASTER #(
         .DATA_WIDTH       (G.DATA_WIDTH),
         .HEADER_NUM       (G.HEADER_NUM),
         .PORT1_BASE       (G.PORT1_BASE),
         .PORT1_LIMIT      (G.PORT1_LIMIT),
         .PORT2_BASE       (G.PORT2_BASE),
         .PORT2_LIMIT      (G.PORT2_LIMIT)
      ) IB_SWITCH_INST (
         .CLK                    (CLK),
         .RESET                  (RESET),
   
         .PORT0_DOWN_DATA        (UP_RX.DATA),
         .PORT0_DOWN_SOF_N       (UP_RX.SOF_N),
         .PORT0_DOWN_EOF_N       (UP_RX.EOF_N),
         .PORT0_DOWN_SRC_RDY_N   (UP_RX.SRC_RDY_N),
         .PORT0_DOWN_DST_RDY_N   (UP_RX.DST_RDY_N),
   
         .PORT0_UP_DATA          (UP_TX.DATA),
         .PORT0_UP_SOF_N         (UP_TX.SOF_N),
         .PORT0_UP_EOF_N         (UP_TX.EOF_N),
         .PORT0_UP_SRC_RDY_N     (UP_TX.SRC_RDY_N),
         .PORT0_UP_DST_RDY_N     (UP_TX.DST_RDY_N),
         
         .PORT1_DOWN_DATA        (D1_TX.DATA),
         .PORT1_DOWN_SOF_N       (D1_TX.SOF_N),
         .PORT1_DOWN_EOF_N       (D1_TX.EOF_N),
         .PORT1_DOWN_SRC_RDY_N   (D1_TX.SRC_RDY_N),
         .PORT1_DOWN_DST_RDY_N   (D1_TX.DST_RDY_N),
   
         .PORT1_UP_DATA          (D1_RX.DATA),
         .PORT1_UP_SOF_N         (D1_RX.SOF_N),
         .PORT1_UP_EOF_N         (D1_RX.EOF_N),
         .PORT1_UP_SRC_RDY_N     (D1_RX.SRC_RDY_N),
         .PORT1_UP_DST_RDY_N     (D1_RX.DST_RDY_N),
         
         .PORT2_DOWN_DATA        (D2_TX.DATA),
         .PORT2_DOWN_SOF_N       (D2_TX.SOF_N),
         .PORT2_DOWN_EOF_N       (D2_TX.EOF_N),
         .PORT2_DOWN_SRC_RDY_N   (D2_TX.SRC_RDY_N),
         .PORT2_DOWN_DST_RDY_N   (D2_TX.DST_RDY_N),
   
         .PORT2_UP_DATA          (D2_RX.DATA),
         .PORT2_UP_SOF_N         (D2_RX.SOF_N),
         .PORT2_UP_EOF_N         (D2_RX.EOF_N),
         .PORT2_UP_SRC_RDY_N     (D2_RX.SRC_RDY_N),
         .PORT2_UP_DST_RDY_N     (D2_RX.DST_RDY_N)
      );
   else
      IB_SWITCH_SLAVE #(
         .DATA_WIDTH       (G.DATA_WIDTH),
         .HEADER_NUM       (G.HEADER_NUM)
      ) IB_SWITCH_INST (
         .CLK                    (CLK),
         .RESET                  (RESET),
   
         .PORT0_DOWN_DATA        (UP_RX.DATA),
         .PORT0_DOWN_SOF_N       (UP_RX.SOF_N),
         .PORT0_DOWN_EOF_N       (UP_RX.EOF_N),
         .PORT0_DOWN_SRC_RDY_N   (UP_RX.SRC_RDY_N),
         .PORT0_DOWN_DST_RDY_N   (UP_RX.DST_RDY_N),
   
         .PORT0_UP_DATA          (UP_TX.DATA),
         .PORT0_UP_SOF_N         (UP_TX.SOF_N),
         .PORT0_UP_EOF_N         (UP_TX.EOF_N),
         .PORT0_UP_SRC_RDY_N     (UP_TX.SRC_RDY_N),
         .PORT0_UP_DST_RDY_N     (UP_TX.DST_RDY_N),
         
         .PORT1_DOWN_DATA        (D1_TX.DATA),
         .PORT1_DOWN_SOF_N       (D1_TX.SOF_N),
         .PORT1_DOWN_EOF_N       (D1_TX.EOF_N),
         .PORT1_DOWN_SRC_RDY_N   (D1_TX.SRC_RDY_N),
         .PORT1_DOWN_DST_RDY_N   (D1_TX.DST_RDY_N),
   
         .PORT1_UP_DATA          (D1_RX.DATA),
         .PORT1_UP_SOF_N         (D1_RX.SOF_N),
         .PORT1_UP_EOF_N         (D1_RX.EOF_N),
         .PORT1_UP_SRC_RDY_N     (D1_RX.SRC_RDY_N),
         .PORT1_UP_DST_RDY_N     (D1_RX.DST_RDY_N),
         
         .PORT2_DOWN_DATA        (D2_TX.DATA),
         .PORT2_DOWN_SOF_N       (D2_TX.SOF_N),
         .PORT2_DOWN_EOF_N       (D2_TX.EOF_N),
         .PORT2_DOWN_SRC_RDY_N   (D2_TX.SRC_RDY_N),
         .PORT2_DOWN_DST_RDY_N   (D2_TX.DST_RDY_N),
   
         .PORT2_UP_DATA          (D2_RX.DATA),
         .PORT2_UP_SOF_N         (D2_RX.SOF_N),
         .PORT2_UP_EOF_N         (D2_RX.EOF_N),
         .PORT2_UP_SRC_RDY_N     (D2_RX.SRC_RDY_N),
         .PORT2_UP_DST_RDY_N     (D2_RX.DST_RDY_N)
      );

endmodule
