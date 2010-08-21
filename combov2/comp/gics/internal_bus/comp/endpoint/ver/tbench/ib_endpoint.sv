/*
 * ib_endpoint.sv: IB_ENDPOINT System Verilog envelope
 * Copyright (C) 2008 CESNET
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
 * $Id: ib_endpoint.sv 8619 2009-06-02 16:17:47Z washek $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------

import ib_params_pkg::*;

module IB_ENDPOINT_SV #(pIbEndpointGenerics G = dIbEndpointGenerics) (
   input logic CLK,
   input logic RESET,
   iIbEndpointWrite.dut     WR,
   iIbEndpointRead.dut      RD,   
   iInternalBusRx.dut       IB_DOWN,
   iInternalBusTx.dut       IB_UP,
   iInternalBusRx.dut       BM,
   iIbEndpointBMDone.dut    BM_DONE
   );
   
   IB_ENDPOINT #(
      .DATA_WIDTH         (G.DATA_WIDTH),
      .ADDR_WIDTH         (G.ADDR_WIDTH),
      .BUS_MASTER_ENABLE  (G.BUS_MASTER_ENABLE),
      .ENDPOINT_BASE      (G.ENDPOINT_BASE),
      .ENDPOINT_LIMIT     (G.ENDPOINT_LIMIT),
      .CONNECTED_TO       (G.CONNECTED_TO),
      .STRICT_ORDER       (G.STRICT_ORDER),
      .DATA_REORDER       (G.DATA_REORDER),
      .READ_IN_PROCESS    (G.READ_IN_PROCESS),
      .READ_TYPE          (G.READ_TYPE),
      .INPUT_BUFFER_SIZE  (G.INPUT_BUFFER_SIZE),
      .OUTPUT_BUFFER_SIZE (G.OUTPUT_BUFFER_SIZE)
      
   ) IB_ENDPOINT_INST (
      .CLK              (CLK),
      .RESET            (RESET),

      .IB_UP_DATA       (IB_UP.DATA),
      .IB_UP_SOF_N      (IB_UP.SOF_N),
      .IB_UP_EOF_N      (IB_UP.EOF_N),
      .IB_UP_SRC_RDY_N  (IB_UP.SRC_RDY_N),
      .IB_UP_DST_RDY_N  (IB_UP.DST_RDY_N),

      .IB_DOWN_DATA     (IB_DOWN.DATA),
      .IB_DOWN_SOF_N    (IB_DOWN.SOF_N),
      .IB_DOWN_EOF_N    (IB_DOWN.EOF_N),
      .IB_DOWN_SRC_RDY_N(IB_DOWN.SRC_RDY_N),
      .IB_DOWN_DST_RDY_N(IB_DOWN.DST_RDY_N),

      .WR_ADDR    (WR.ADDR),
      .WR_DATA    (WR.DATA),
      .WR_BE      (WR.BE),
      .WR_REQ     (WR.REQ),
      .WR_RDY     (WR.RDY),
      .WR_LENGTH  (WR.LENGTH),
      .WR_SOF     (WR.SOF),
      .WR_EOF     (WR.EOF),

      .RD_ADDR    (RD.ADDR),
      .RD_BE      (RD.BE),
      .RD_REQ     (RD.REQ),
      .RD_ARDY_ACCEPT (RD.ARDY_ACCEPT),
      .RD_LENGTH  (RD.LENGTH),
      .RD_SOF     (RD.SOF),
      .RD_EOF     (RD.EOF),
      .RD_DATA    (RD.DATA),
      .RD_SRC_RDY (RD.SRC_RDY),
      .RD_DST_RDY (RD.DST_RDY),
      
      .BM_DATA       (BM.DATA),
      .BM_SOF_N      (BM.SOF_N),
      .BM_EOF_N      (BM.EOF_N),
      .BM_SRC_RDY_N  (BM.SRC_RDY_N),
      .BM_DST_RDY_N  (BM.DST_RDY_N),
      .BM_TAG        (BM_DONE.TAG),
      .BM_TAG_VLD    (BM_DONE.TAG_VLD)      
   );
   
endmodule
