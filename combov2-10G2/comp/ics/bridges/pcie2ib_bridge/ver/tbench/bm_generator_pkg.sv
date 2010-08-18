//
// bm_generator_pkg.sv: Bus Master Random Transaction Generator
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
// $Id: bm_generator_pkg.sv 688 2007-10-19 16:11:56Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package bm_generator_pkg;

  import bm_transaction_pkg::*; // Transaction package

  // --------------------------------------------------------------------------
  // -- Bus Master Generator Class
  // --------------------------------------------------------------------------

  class BusMasterGenerator;
  
    // -- Public Class Atributes --
  
    BusMasterTransaction blueprint;   // Transaction for copying

    // -- Private Class Atributes --
    
    tBmTransMbx            bmTransMbx;  // Transaction MailBox
    bit                    enabled;     // Generator is enabled

    // -- Public Class Methods --
  
    // -- Constructor ---------------------------------------------------------
    // Create a class connected to driver transaction mailbox
    function new ( tBmTransMbx bmTransMbx );
      this.bmTransMbx  = bmTransMbx;
      this.blueprint = new;
      this.enabled   = 0;        
    endfunction : new

    // -- Enable Generator ----------------------------------------------------
    // Enable generator and runs generator process
    task setEnabled();
      enabled = 1; // Generator Enabling
      fork         
        run();     // Creating generator subprocess
      join_none;    // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Generator ---------------------------------------------------
    // Disable generator
    task setDisabled();
      enabled = 0;
    endtask : setDisabled
 
    // -- Private Class Methods --

    // -- Run Generator -------------------------------------------------------
    // Take transactions drom mailbox and generate them to interface
    task run();
      BusMasterTransaction tr;
      while (enabled) begin           // Stay in loop while enabled
        assert(blueprint.randomize);  // Randomize transaction
        tr = blueprint.copy;          // Copy transaction
        bmTransMbx.put(tr);             // Put transaction into mailbox
      end;
    endtask : run

  endclass : BusMasterGenerator


endpackage : bm_generator_pkg

