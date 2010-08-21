/*
 * done_trans.sv: Bus Master Done Transaction
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
 * $Id: done_trans.sv 14041 2010-06-15 13:15:55Z washek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package done_transaction_pkg;
  
  import sv_common_pkg::*;  //Transaction class
  
  // --------------------------------------------------------------------------
  // -- Done Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe done transaction
   */
  class DoneTransaction extends Transaction;
  
    logic [7:0] tag;
    
    logic [31:0] addr;
    bit          done = 1;

    //-- Compare -------------------------------------------------------------- 
    // Compare transaction with another. Return 1 for same transactions
    virtual function bit compare(input Transaction to, 
                                     output string diff, input int kind = -1);
      DoneTransaction tr;
      $cast(tr, to);
      
      if (tag == tr.tag && done == tr.done)
        compare = 1;
      else
        compare = 0;
    endfunction : compare

    //-- Show transaction -----------------------------------------------------
    // Function show transaction in text format
    virtual function void display(string prefix = "");
      if (prefix != "") begin
        $write("---------------------------------------------------------\n");
        $write("-- %s\n",prefix);
        $write("---------------------------------------------------------\n");
      end
      $display("Done transaction TAG=%2x ADDR=%x DONE=%x", tag, addr, done);
      
    endfunction : display

   endclass : DoneTransaction

   // Mailbox
   typedef mailbox #(DoneTransaction) tDoneTransMbx;

endpackage : done_transaction_pkg
