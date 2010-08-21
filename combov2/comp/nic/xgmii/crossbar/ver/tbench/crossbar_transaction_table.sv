/* \file ibuf_transaction_table.sv
 * \brief XGMII IBUF Transaction Table
 * \author Marek Santa <santa@liberouter.org> 
 * \date 2010 
 */
/*  
 * Copyright (C) 2010 CESNET
 * 
 * LICENSE TERMS  
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
 *
 *
 * TODO:
 *
 */


  // --------------------------------------------------------------------------
  // -- Ibuf Transaction Table
  // --------------------------------------------------------------------------
  /*!
   * \brief IBUF Transaction Table
   * 
   * This class changed the default way of removing transactions from
   * transaction table due to specific demand of XGMII IBUF 
   */

  class IbufTransactionTable extends TransactionTable #();
    // ---------------------
    // -- Class Variables --
    // ---------------------
    // Behaviour of transaction table
    int firstOnly = 0;
    int discarded;               // Items discarded from TransactionTable
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      super.new();
      discarded = 0;
    endfunction
    
    // ------------------------------------------------------------------------
    //Remove item from the table
    task remove(TransType transaction, ref bit status, input int kind = -1);
      string diff;
      status=0;
      lock();

      // Compare first packet only
      if (firstOnly==TR_TABLE_FIRST_ONLY && tr_table.size > 0) begin
        if (this.tr_table[0].compare(transaction,diff, kind)==1) begin
          this.tr_table.delete(0);
          status=1;
          removed++;
        end
      end 
      // Compare packet until match and discard previous packets
      else
        for(int i=0; i < this.tr_table.size; i++) begin 
          if (this.tr_table[i].compare(transaction,diff, kind)==1) begin
            this.tr_table.delete(i);
            status=1;
            removed++;
            // If matching transaction is not the first, previous transactions
            // was discarded by IBUF
            if (i!=0) begin
              for (int j=0; j < i; j++) begin
                this.tr_table.delete(0);
                discarded++;
              end
            end
            break;
          end
        end
        
      unlock();     
    endtask: remove 
   
    // ------------------------------------------------------------------------
    // Display the actual state of transaction table
    task display(integer full=1, string inst = "");
      lock();
      $write("------------------------------------------------------------\n");
      $write("-- %s TRANSACTION TABLE\n", inst);
      $write("------------------------------------------------------------\n");
      $write("Size: %d\n", tr_table.size);
      $write("Items added: %d\n", added);
      $write("Items removed: %d\n", removed);
      $write("Items discarded due to buffer overflow: %d\n", discarded);
      if (full)
         foreach(tr_table[i]) tr_table[i].display();
      $write("------------------------------------------------------------\n");
      unlock();
    endtask: display
endclass : IbufTransactionTable

