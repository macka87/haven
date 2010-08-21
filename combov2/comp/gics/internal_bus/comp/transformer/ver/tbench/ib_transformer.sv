/*
 * ib_transformer.sv: IB_TRANSFORMER System Verilog envelope
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
 * $Id: ib_transformer.sv 8657 2009-06-04 10:57:57Z washek $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------

import ib_params_pkg::*; //test parameters

module IB_TRANSFORMER_SV #(pIbTransformerGenerics G = dIbTransformerGenerics) (
   input logic CLK,
   input logic RESET,
   iInternalBusRx.dut    UP_RX,
   iInternalBusTx.dut    UP_TX,
   iInternalBusRx.dut    DOWN_RX,
   iInternalBusTx.dut    DOWN_TX
   );

   IB_TRANSFORMER #(
      .UP_DATA_WIDTH           (G.UP_DATA_WIDTH),
      .DOWN_DATA_WIDTH         (G.DOWN_DATA_WIDTH),
      .UP_INPUT_BUFFER_ITEMS   (G.UP_INPUT_BUFFER_ITEMS),
      .DOWN_INPUT_BUFFER_ITEMS (G.DOWN_INPUT_BUFFER_ITEMS),
      .UP_OUTPUT_PIPE          (G.UP_OUTPUT_PIPE),
      .DOWN_OUTPUT_PIPE        (G.DOWN_OUTPUT_PIPE)
      
   ) IB_TRANSFORMER_INST (
      .CLK              (CLK),
      .RESET            (RESET),

      .UP_IN_DATA       (UP_RX.DATA),
      .UP_IN_SOF_N      (UP_RX.SOF_N),
      .UP_IN_EOF_N      (UP_RX.EOF_N),
      .UP_IN_SRC_RDY_N  (UP_RX.SRC_RDY_N),
      .UP_IN_DST_RDY_N  (UP_RX.DST_RDY_N),

      .UP_OUT_DATA       (UP_TX.DATA),
      .UP_OUT_SOF_N      (UP_TX.SOF_N),
      .UP_OUT_EOF_N      (UP_TX.EOF_N),
      .UP_OUT_SRC_RDY_N  (UP_TX.SRC_RDY_N),
      .UP_OUT_DST_RDY_N  (UP_TX.DST_RDY_N),
      
      .DOWN_IN_DATA       (DOWN_RX.DATA),
      .DOWN_IN_SOF_N      (DOWN_RX.SOF_N),
      .DOWN_IN_EOF_N      (DOWN_RX.EOF_N),
      .DOWN_IN_SRC_RDY_N  (DOWN_RX.SRC_RDY_N),
      .DOWN_IN_DST_RDY_N  (DOWN_RX.DST_RDY_N),

      .DOWN_OUT_DATA       (DOWN_TX.DATA),
      .DOWN_OUT_SOF_N      (DOWN_TX.SOF_N),
      .DOWN_OUT_EOF_N      (DOWN_TX.EOF_N),
      .DOWN_OUT_SRC_RDY_N  (DOWN_TX.SRC_RDY_N),
      .DOWN_OUT_DST_RDY_N  (DOWN_TX.DST_RDY_N)
   );

endmodule
