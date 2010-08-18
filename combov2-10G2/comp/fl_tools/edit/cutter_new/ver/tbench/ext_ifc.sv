/*
 * ext_ifc.sv: Extraction data Interface
 * Copyright (C) 2009 CESNET
 * Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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
 * $Id: ext_ifc.sv 10412 2009-08-14 15:00:48Z xstour03 $
 *
 * TODO:
 *
 */
 

// ----------------------------------------------------------------------------
//                         Extraction data Interface declaration
// ----------------------------------------------------------------------------

// -- Extraction data Interface -----------------------------------------------
interface iExt_data #(EXT_SIZE = 4) (input logic CLK, RESET);  
  logic [EXT_SIZE*8-1:0] EXTRACTED_DATA;  // Extraction data
  logic EXTRACTED_DONE;                   // Extraction ended active in high
  logic EXTRACTED_ERR;                    // Extraction error active in high
  

 clocking cb @(posedge CLK);
   input EXTRACTED_DATA, EXTRACTED_DONE, EXTRACTED_ERR;  
 endclocking: cb;

  clocking monitor_cb @(posedge CLK);
    input EXTRACTED_DATA, EXTRACTED_DONE, EXTRACTED_ERR; 
  endclocking: monitor_cb;

  // Receive Modport
  modport dut (output  EXTRACTED_DATA,
               output  EXTRACTED_DONE,
               output  EXTRACTED_ERR);
  
  // Transitive Modport
  modport tb (clocking cb);

  // Monitor Modport
  modport monitor (clocking monitor_cb);

  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------

endinterface : iExt_data
