/*
 * IB_ENDPOINT.v: IB_ENDPOINT System Verilog envelope
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id: ib_endpoint_slave.sv 333 2007-09-05 20:07:59Z xkobie00 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------

module IB_ENDPOINT_SV (
   input logic                 CLK,
   input logic                 RESET,
   iIbEndpointWrite64.endpoint WR,
   iIbEndpointRead64s.endpoint RD,
   iInternalBusLink.rx         IB_DOWN,
   iInternalBusLink.tx         IB_UP);

   IB_ENDPOINT_NOREC IB_ENDPOINT_INST (
      .IB_CLK            (CLK),
      .IB_RESET          (RESET),

      .IB_UP_DATA        (IB_UP.DATA),
      .IB_UP_SOP_N       (IB_UP.SOP_N),
      .IB_UP_EOP_N       (IB_UP.EOP_N),
      .IB_UP_SRC_RDY_N   (IB_UP.SRC_RDY_N),
      .IB_UP_DST_RDY_N   (IB_UP.DST_RDY_N),

      .IB_DOWN_DATA      (IB_DOWN.DATA),
      .IB_DOWN_SOP_N     (IB_DOWN.SOP_N),
      .IB_DOWN_EOP_N     (IB_DOWN.EOP_N),
      .IB_DOWN_SRC_RDY_N (IB_DOWN.SRC_RDY_N),
      .IB_DOWN_DST_RDY_N (IB_DOWN.DST_RDY_N),

      .WR_ADDR           (WR.ADDR),
      .WR_DATA           (WR.DATA),
      .WR_BE             (WR.BE),
      .WR_REQ            (WR.REQ),
      .WR_RDY            (WR.RDY),
      .WR_LENGTH         (WR.LENGTH),
      .WR_SOF            (WR.SOF),
      .WR_EOF            (WR.EOF),

      .RD_ADDR           (RD.ADDR),
      .RD_BE             (RD.BE),
      .RD_REQ            (RD.REQ),
      .RD_ARDY           (RD.ARDY),
      .RD_SOF_IN         (RD.SOF_IN),
      .RD_EOF_IN         (RD.EOF_IN),
      .RD_DATA           (RD.DATA),
      .RD_SRC_RDY        (RD.SRC_RDY),
      .RD_DST_RDY        (RD.DST_RDY)
   );

endmodule
