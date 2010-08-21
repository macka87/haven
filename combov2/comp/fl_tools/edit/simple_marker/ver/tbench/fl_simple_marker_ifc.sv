/*
 * fl_simple_marker_ifc.sv: FrameLink SIMPLE_MARKER Control Interface
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
 * $Id: fl_simple_marker_ifc.sv 10305 2009-08-12 05:34:35Z xsanta06 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//           FrameLink SIMPLE MARKER Control Interface declaration
// ----------------------------------------------------------------------------

// -- FrameLink SIMPLE MARKER Control Interface -------------------------------
interface iFrameLinkSimpleMarker #(MARK_SIZE = 1) (input logic CLK, RESET);  
  // Marker Interface
  logic [MARK_SIZE*8-1:0] MARK_NO = 0;   // Input mark inserted into packets  
  logic MARK_VALID                = 0;   // Valid mark value
  logic MARK_NEXT                    ;   // Mark inserted
    

  // Clocking blocks  
  clocking mark_cb @(posedge CLK);
    input  MARK_NEXT;
    output MARK_NO, MARK_VALID;
  endclocking: mark_cb

  // Marker Modport
  modport mark_dut (input  MARK_NO,
                    input  MARK_VALID,
                    output MARK_NEXT
                   );
  
  modport mark_tb (clocking mark_cb);

endinterface : iFrameLinkSimpleMarker
