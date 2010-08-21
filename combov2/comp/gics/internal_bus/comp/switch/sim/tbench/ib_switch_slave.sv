/*
 * IB_SWITCH_SLAVE.sv: IB_SWITCH System Verilog envelope
 * Copyright (C) 2008 CESNET
 * Author(s): Tomas Malek <tomalek@liberouter.org>
 *            Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id: ib_switch_slave.sv 1364 2008-02-18 15:23:10Z tomalek $
 *
 * TODO:
 *
 */
 
module IB_SWITCH_SV (
   input logic CLK,
   input logic RESET,
   iIB.rx PORT0_DOWN,
   iIB.tx PORT0_UP,
   iIB.tx PORT1_DOWN,
   iIB.rx PORT1_UP,
   iIB.tx PORT2_DOWN,
   iIB.rx PORT2_UP);

   IB_SWITCH_SLAVE_SIM SWITCH_SLAVE_INST (
      // Common Interface
      .CLK               (CLK),
      .RESET             (RESET),
  
      // Port 0
      .PORT0_DOWN_DATA      (PORT0_DOWN.DATA),
      .PORT0_DOWN_SOF_N     (PORT0_DOWN.SOF_N),
      .PORT0_DOWN_EOF_N     (PORT0_DOWN.EOF_N),
      .PORT0_DOWN_SRC_RDY_N (PORT0_DOWN.SRC_RDY_N),
      .PORT0_DOWN_DST_RDY_N (PORT0_DOWN.DST_RDY_N),
      .PORT0_UP_DATA        (PORT0_UP.DATA),
      .PORT0_UP_SOF_N       (PORT0_UP.SOF_N),
      .PORT0_UP_EOF_N       (PORT0_UP.EOF_N),
      .PORT0_UP_SRC_RDY_N   (PORT0_UP.SRC_RDY_N),
      .PORT0_UP_DST_RDY_N   (PORT0_UP.DST_RDY_N),
      // Port 1
      .PORT1_DOWN_DATA      (PORT1_DOWN.DATA),
      .PORT1_DOWN_SOF_N     (PORT1_DOWN.SOF_N),
      .PORT1_DOWN_EOF_N     (PORT1_DOWN.EOF_N),
      .PORT1_DOWN_SRC_RDY_N (PORT1_DOWN.SRC_RDY_N),
      .PORT1_DOWN_DST_RDY_N (PORT1_DOWN.DST_RDY_N),
      .PORT1_UP_DATA        (PORT1_UP.DATA),
      .PORT1_UP_SOF_N       (PORT1_UP.SOF_N),
      .PORT1_UP_EOF_N       (PORT1_UP.EOF_N),
      .PORT1_UP_SRC_RDY_N   (PORT1_UP.SRC_RDY_N),
      .PORT1_UP_DST_RDY_N   (PORT1_UP.DST_RDY_N),
      // Port 2
      .PORT2_DOWN_DATA      (PORT2_DOWN.DATA),
      .PORT2_DOWN_SOF_N     (PORT2_DOWN.SOF_N),
      .PORT2_DOWN_EOF_N     (PORT2_DOWN.EOF_N),
      .PORT2_DOWN_SRC_RDY_N (PORT2_DOWN.SRC_RDY_N),
      .PORT2_DOWN_DST_RDY_N (PORT2_DOWN.DST_RDY_N),
      .PORT2_UP_DATA        (PORT2_UP.DATA),
      .PORT2_UP_SOF_N       (PORT2_UP.SOF_N),
      .PORT2_UP_EOF_N       (PORT2_UP.EOF_N),
      .PORT2_UP_SRC_RDY_N   (PORT2_UP.SRC_RDY_N),
      .PORT2_UP_DST_RDY_N   (PORT2_UP.DST_RDY_N)
);

endmodule : IB_SWITCH_SV



