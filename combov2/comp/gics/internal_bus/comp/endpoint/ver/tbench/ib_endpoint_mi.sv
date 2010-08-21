/*
 * ib_endpoint_mi.sv: IB_ENDPOINT_MI System Verilog envelope
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
 * $Id: ib_endpoint_mi.sv 12322 2009-12-23 18:55:15Z washek $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------

import ib_params_pkg::*;

module IB_ENDPOINT_MI_SV #(pIbEndpointGenerics G = dIbEndpointGenerics) (
   input logic CLK,
   input logic RESET,
   iIbEndpointWrite.dut     WR,
   iIbEndpointRead.dut      RD,   
   iInternalBusRx.dut       IB_DOWN,
   iInternalBusTx.dut       IB_UP,
   iInternalBusRx.dut       BM,
   iIbEndpointBMDone.dut    BM_DONE
   );
   
   iMI #(G.DATA_WIDTH, G.ADDR_WIDTH) MI(CLK, RESET);
   
   IB_ENDPOINT_MI #(
      .DATA_WIDTH         (G.DATA_WIDTH),
      .ADDR_WIDTH         (G.ADDR_WIDTH),
      .BUS_MASTER_ENABLE  (G.BUS_MASTER_ENABLE),
      .ENDPOINT_BASE      (G.ENDPOINT_BASE),
      .ENDPOINT_LIMIT     (G.ENDPOINT_LIMIT),
      .CONNECTED_TO       (G.CONNECTED_TO),
      .DATA_REORDER       (G.DATA_REORDER),
      .READ_IN_PROCESS    (G.READ_IN_PROCESS),
      .INPUT_BUFFER_SIZE  (G.INPUT_BUFFER_SIZE),
      .OUTPUT_BUFFER_SIZE (G.OUTPUT_BUFFER_SIZE)
      
   ) IB_ENDPOINT_MI_INST (
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
      
      .MI_DWR     (MI.DWR),
      .MI_ADDR    (MI.ADDR),
      .MI_RD      (MI.RD),
      .MI_WR      (MI.WR),
      .MI_ARDY    (MI.ARDY),
      .MI_BE      (MI.BE),
      .MI_DRD     (MI.DRD),
      .MI_DRDY    (MI.DRDY),
      
      .BM_DATA       (BM.DATA),
      .BM_SOF_N      (BM.SOF_N),
      .BM_EOF_N      (BM.EOF_N),
      .BM_SRC_RDY_N  (BM.SRC_RDY_N),
      .BM_DST_RDY_N  (BM.DST_RDY_N),
      .BM_TAG        (BM_DONE.TAG),
      .BM_TAG_VLD    (BM_DONE.TAG_VLD)
   );
   
   
   MI2EPI #(
      .DATA_WIDTH  (G.DATA_WIDTH),
      .ADDR_WIDTH  (G.ADDR_WIDTH)
   ) MI2EPI_INST (
      .MI   (MI),
      .WR   (WR),
      .RD   (RD)
   );
   
endmodule
