//
// test_pkg.sv: Test package
// Copyright (C) 2007 CESNET
// Author(s): Tomas Malek <tomalek@liberouter.org>
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
// 3. Neither the name of the Company nor the names of its contributors
//    may be used to endorse or promote products derived from this
//    software without specific prior written permission.
//
// This software is provided ``as is'', and any express or implied
// warranties, including, but not limited to, the implied warranties of
// merchantability and fitness for a particular purpose are disclaimed.
// In no event shall the company or contributors be liable for any
// direct, indirect, incidental, special, exemplary, or consequential
// damages (including, but not limited to, procurement of substitute
// goods or services; loss of use, data, or profits; or business
// interruption) however caused and on any theory of liability, whether
// in contract, strict liability, or tort (including negligence or
// otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// $Id: test_pkg.sv 7231 2009-02-24 18:03:37Z xkobie00 $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;

   // Clock and Reset constants
   const time cClkPeriod = 8ns;
   const time cResetTime = 10*cClkPeriod;
   
   // IB Constants
   parameter pIB_DATA_WIDTH = 64;
   
   // DUT generics (Must be set to same values in pcie2ib_bridge.vhd"
   parameter pBRIDGE_BASE_ADDR = 32'hFFFFFFF0;
   parameter pBAR0_REMAP       = 32'h01000000;
   parameter pBAR1_REMAP       = 32'h02000000;
   parameter pBAR2_REMAP       = 32'h03000000;
   parameter pBAR3_REMAP       = 32'h04000000;
   parameter pBAR4_REMAP       = 32'h05000000;
   parameter pBAR5_REMAP       = 32'h06000000;
   parameter pEXP_ROM_REMAP    = 32'h0A000000;

   parameter pBAR0_MASK        = 32'h00FFFFFF;
   parameter pBAR1_MASK        = 32'h00FFFFFF;
   parameter pBAR2_MASK        = 32'h00FFFFFF;
   parameter pBAR3_MASK        = 32'h00FFFFFF;
   parameter pBAR4_MASK        = 32'h00FFFFFF;
   parameter pBAR5_MASK        = 32'h00FFFFFF;
   parameter pEXP_ROM_MASK     = 32'h00FFFFFF;

   // PCIe Bridge CFG interface
   parameter pBUS_NUM               = 8'b11001010;
   parameter pDEVICE_NUM            = 5'b11111;
   parameter pFUNC_NUM              = 3'b110;
   parameter pMAX_PAYLOAD_SIZE      = 128;
   parameter pMAX_READ_REQUEST_SIZE = 128;

   // Include this file if you want to use standard SystemVerilog Scoreboard
   `include "pcie2ib_check.sv"
   `include "ib2pcie_check.sv"
   `include "pcie_posted_check.sv"
   `include "ib_posted_check.sv"

endpackage










