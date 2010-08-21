/*
 * IB_SWITCH.sv: IB_SWITCH System Verilog envelope
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
 * $Id: ib_switch.sv 334 2007-09-05 20:13:22Z xkobie00 $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*;

module IB_SWITCH (
   input logic CLK,
   input logic RESET,
   iInternalBusLink.rx PORT0_DOWN,
   iInternalBusLink.tx PORT0_UP,
   iInternalBusLink.tx PORT1_DOWN,
   iInternalBusLink.rx PORT1_UP,
   iInternalBusLink.tx PORT2_DOWN,
   iInternalBusLink.rx PORT2_UP
);


// -------------------- Module body -------------------------------------------

IB_SWITCH_CORE// # (
//   .DATA_WIDTH(64)
// Problem with std_logic, cant be passed
   // Port 0 Address Space 
//   .SWITCH_BASE(32'h00000000),
//   .SWITCH_LIMIT(32'h33333333),
//   // Port 1 Address Space
//   .DOWNSTREAM0_BASE(32'h00000000),
//   .DOWNSTREAM0_LIMIT(32'h11111111),
//   // Port 2 Address Space
//   .DOWNSTREAM1_BASE(32'h11111111),
//   .DOWNSTREAM1_LIMIT(32'h22222222)
//  )
  IB_SWITCH_CORE_U (
    // Common Interface
    .IB_CLK               (CLK),
    .IB_RESET             (RESET),
 
    // Port 0
    .PORT0_DOWN_DATA      (PORT0_DOWN.DATA),
    .PORT0_DOWN_SOP_N     (PORT0_DOWN.SOP_N),
    .PORT0_DOWN_EOP_N     (PORT0_DOWN.EOP_N),
    .PORT0_DOWN_SRC_RDY_N (PORT0_DOWN.SRC_RDY_N),
    .PORT0_DOWN_DST_RDY_N (PORT0_DOWN.DST_RDY_N),
    .PORT0_UP_DATA        (PORT0_UP.DATA),
    .PORT0_UP_SOP_N       (PORT0_UP.SOP_N),
    .PORT0_UP_EOP_N       (PORT0_UP.EOP_N),
    .PORT0_UP_SRC_RDY_N   (PORT0_UP.SRC_RDY_N),
    .PORT0_UP_DST_RDY_N   (PORT0_UP.DST_RDY_N),
    // Port 1
    .PORT1_DOWN_DATA      (PORT1_DOWN.DATA),
    .PORT1_DOWN_SOP_N     (PORT1_DOWN.SOP_N),
    .PORT1_DOWN_EOP_N     (PORT1_DOWN.EOP_N),
    .PORT1_DOWN_SRC_RDY_N (PORT1_DOWN.SRC_RDY_N),
    .PORT1_DOWN_DST_RDY_N (PORT1_DOWN.DST_RDY_N),
    .PORT1_UP_DATA        (PORT1_UP.DATA),
    .PORT1_UP_SOP_N       (PORT1_UP.SOP_N),
    .PORT1_UP_EOP_N       (PORT1_UP.EOP_N),
    .PORT1_UP_SRC_RDY_N   (PORT1_UP.SRC_RDY_N),
    .PORT1_UP_DST_RDY_N   (PORT1_UP.DST_RDY_N),
    // Port 2
    .PORT2_DOWN_DATA      (PORT2_DOWN.DATA),
    .PORT2_DOWN_SOP_N     (PORT2_DOWN.SOP_N),
    .PORT2_DOWN_EOP_N     (PORT2_DOWN.EOP_N),
    .PORT2_DOWN_SRC_RDY_N (PORT2_DOWN.SRC_RDY_N),
    .PORT2_DOWN_DST_RDY_N (PORT2_DOWN.DST_RDY_N),
    .PORT2_UP_DATA        (PORT2_UP.DATA),
    .PORT2_UP_SOP_N       (PORT2_UP.SOP_N),
    .PORT2_UP_EOP_N       (PORT2_UP.EOP_N),
    .PORT2_UP_SRC_RDY_N   (PORT2_UP.SRC_RDY_N),
    .PORT2_UP_DST_RDY_N   (PORT2_UP.DST_RDY_N)
);

endmodule : IB_SWITCH
