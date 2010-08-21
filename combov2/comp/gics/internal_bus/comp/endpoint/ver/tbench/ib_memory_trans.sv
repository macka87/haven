/*
 * ib_memory_trans.sv: Memory Transaction
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
 * $Id: ib_memory_trans.sv 8517 2009-05-28 10:55:58Z washek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_memory_transaction_pkg;
  
  import sv_common_pkg::*;  //Transaction class
  
  // -- Memory transactions Types ---------------------------------------------
  typedef enum {READ_REQ, READ_DATA, WRITE} eMemoryTransType;

  // --------------------------------------------------------------------------
  // -- Memory Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe memory transaction
   */
  class MemoryTransaction extends Transaction;
  
    logic [31:0]      addr;
    logic [12:0]      length;
    logic [7:0]       data[];
    eMemoryTransType  transType;

    //-- Compare -------------------------------------------------------------- 
    // Compare transaction with another. Return 1 for same transactions
    virtual function bit compare(input Transaction to, 
                                     output string diff, input int kind = -1);
      MemoryTransaction tr;
      int same = 1; // Suppose that are same
      $cast(tr, to);
      
      if (transType != tr.transType) same = 0;
      if (addr   != tr.addr) same = 0;
      if (length != tr.length) same = 0;
      if (kind == 1 && same == 1)
        for (int i = 0; i < data.size; i++)
          if (data[i] != tr.data[i])
            same = 0;
      compare = same;
    endfunction : compare

    //-- Show transaction -----------------------------------------------------
    // Function show transaction in text format
    virtual function void display(string prefix = "");
      bit dots_written = 0;
      
      if (prefix != "") begin
        $write("---------------------------------------------------------\n");
        $write("-- %s\n",prefix);
        $write("---------------------------------------------------------\n");
      end
      $write("Memory transaction TYPE=");
      case (transType)
        READ_REQ:
          $write("READ_REQ, ADDR=%0x, LENGTH=%0x\n", addr, length);
        READ_DATA:
          $write("READ_DATA, ADDR=%0x, LENGTH=%0x\n", addr, length);
        WRITE:
          $write("WRITE, ADDR=%0x, LENGTH=%0x\n", addr, length);
        endcase;
      
      if (transType == READ_DATA || transType == WRITE)
        for (int i=0; i < data.size; i=i+8) begin
          if (i > 8 && i < data.size - 16) begin
            if (dots_written == 0)
              $write("DATA: ...\n");
            dots_written = 1;
          end
          else begin
            $write("DATA: 0x");
            for (int j=i+7; j >= i; j--) begin
              if (j < data.size)
                $write("%2x", data[j]);
              else
                $write("00");
              if (j == i)
                $write("\n");
            end
          end
        end
      
    endfunction : display

  endclass : MemoryTransaction

  // Mailbox for interernal memory comunication
  typedef mailbox #(MemoryTransaction) tMemoryTransMbx;

endpackage : ib_memory_transaction_pkg
