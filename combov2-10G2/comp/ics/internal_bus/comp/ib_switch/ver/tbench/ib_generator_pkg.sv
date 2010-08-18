/*
 * ib_generator_pkg.sv: Internal Bus Random Transaction Generator
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
 * $Id: ib_generator_pkg.sv 334 2007-09-05 20:13:22Z xkobie00 $
 *
 * - Fully functional generator
 *      
 */


// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_generator_pkg;

  import ib_transaction_pkg::*; // Transaction package

  // --------------------------------------------------------------------------
  // -- Internal Bus Generator Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating random Internal Bus transactions.
   * Generated transactions is sended throw transMbx(Mailbox) to driver, which
   * generete transaction on Internal Bus interface. Properties of transaction
   * generation can be changed using "blueprint" propery. Transaction genera-
   * tion must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call.
   */
  class InternalBusGenerator;
  
    // -- Public Class Atributes --
  
    InternalBusTransaction blueprint;   // Transaction for copying

    // -- Private Class Atributes --
    
    tTransMbx              transMbx;    // Transaction MailBox
    bit                    enabled;     // Generator is enabled

    // -- Public Class Methods --
  
    // -- Constructor ---------------------------------------------------------
    // Create a class connected to driver transaction mailbox
    function new ( tTransMbx transMbx );
      this.transMbx  = transMbx;
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
      InternalBusTransaction tr;
      while (enabled) begin           // Stay in loop while enabled
        assert(blueprint.randomize);  // Randomize transaction
        tr = blueprint.copy;          // Copy transaction
        transMbx.put(tr);             // Put transaction into mailbox
      end;
    endtask : run

  endclass : InternalBusGenerator


endpackage : ib_generator_pkg

