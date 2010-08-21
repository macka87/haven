/*
 * ib_transaction_pkg.sv: Internal Bus Transaction
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
 * $Id: ib_memory_trans.sv 333 2007-09-05 20:07:59Z xkobie00 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_memory_transaction_pkg;

  // -- Memory transactions Types ---------------------------------------------
  typedef enum {READ_REQ, READ_DATA, WRITE} eMemoryTransType;

  // --------------------------------------------------------------------------
  // -- Memory Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe memory transaction
   */
  class MemoryTransaction;
    logic [31:0] addr;
    logic [7 :0] be;
    logic [63:0] data;
    eMemoryTransType transType;

    //-- Compare -------------------------------------------------------------- 
    // Compare transaction with another. Return 1 for same transactions
    function int compare(MemoryTransaction tr);
      int same = 1; // Suppose that are same
      if (addr != tr.addr) same = 0;
      if (be   != tr.be) same = 0;
      if (data != tr.data) same = 0;
      if (transType != tr.transType) same = 0;
      compare = same;
    endfunction : compare

    //-- Show transaction -----------------------------------------------------
    // Function show transaction in text format
    function void display();
      $write("Memory transaction TYPE=");
      case (transType)
        READ_REQ:
          $write("READ_REQ, ADDR=%0x, BE=%0x.\n", addr, be);
        READ_DATA:
          $write("READ_DATA, ADDR=%0x, BE=%0x, DATA=%0x.\n", addr, be, data);
        WRITE:
          $write("WRITE, ADDR=%0x, BE=%0x, DATA=%0x.\n", addr, be, data);
        endcase;
      endfunction : display


      

   endclass : MemoryTransaction

   // Mailbox for interernal memory comunication
   typedef mailbox #(MemoryTransaction) tMemoryTransMbx;

endpackage : ib_memory_transaction_pkg
