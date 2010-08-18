//
// bm_table_pkg.sv: BM transaction table
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
// $Id: bm_table_pkg.sv 688 2007-10-19 16:11:56Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package bm_table_pkg;

  import bm_transaction_pkg::*;        // Internal Bus Transaction package

  // --------------------------------------------------------------------------
  // -- IB Transaction table
  // --------------------------------------------------------------------------
  class BmTransactionTable;
     // ---------------------
     // -- Class Variables --
     // ---------------------
     BusMasterTransaction tab[$]; // table
     semaphore sem;
     integer added;
     integer removed;
     integer addedG2LR;
     integer addedL2GW;
     integer removedG2LR;
     integer removedL2GW;
     integer addedOther;
     integer removedOther;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      sem = new(1);
      added = 0;
      removed = 0;
      addedG2LR = 0;
      addedL2GW = 0;
      removedG2LR = 0;
      removedL2GW = 0;
      addedOther = 0;
      removedOther = 0;
    endfunction
    
    // ------------------------------------------------------------------------
    // Add item to table
    task add(BusMasterTransaction item);
       lock();
       this.tab.push_back(item); // Insert item to table
       plus(item);
       unlock();
    endtask: add
    
    // ------------------------------------------------------------------------
    // Remove item from table
    task remove(BusMasterTransaction transaction);
      bit auxRemove = 0;
      lock();
      for (integer i=0; i < tab.size; i++) begin
        if (tab[i].tag == transaction.tag) begin
          auxRemove = 1;
          minus(tab[i]);
          tab.delete(i);
          break;
          end
      end
      unlock();
      
      if (!auxRemove) begin 
        $write("Error (%t): Unable to remove Bus Master transaction:  \n",$time());
        transaction.display();
        end
    endtask: remove

    // ------------------------------------------------------------------------
    // Add new transaction to statisctics
    task plus(BusMasterTransaction transaction);
      added++;
      
      case (transaction.transType)
        BM_L2GW: begin
          addedL2GW++;
          end
        BM_G2LR: begin
          addedG2LR++;
          end    
        BM_L2LR: begin
          addedOther++;
          end    
        BM_L2LW: begin
          addedOther++;
          end                        
      endcase     
    endtask: plus

    // ------------------------------------------------------------------------
    // Remove new transaction from statisctics
    task minus(BusMasterTransaction transaction);
      removed++;
      
      case (transaction.transType)
        BM_L2GW: begin
          removedL2GW++;
          end
        BM_G2LR: begin
          removedG2LR++;
          end   
        BM_L2LR: begin
          removedOther++;
          end    
        BM_L2LW: begin
          removedOther++;
          end                   
      endcase                  
    endtask: minus        
    
    // ------------------------------------------------------------------------
    // Lock table
    task lock();
       sem.get(1);
    endtask: lock

    // ------------------------------------------------------------------------
    // Unlock table
    task unlock();
       sem.put(1);
    endtask: unlock
    
    // ------------------------------------------------------------------------
    // Belongs to Switch address space
    task display();
       lock();
       $write("----------------------------------------------------------------------\n");
       $write("-- BmTransaction Table\n");
       $write("----------------------------------------------------------------------\n");
       $write("                     IN SUM          L2GW          G2LR         OTHER \n");       
       $write("Size:          %d | %d | %d | %d |\n", tab.size,addedL2GW-removedL2GW,addedG2LR-removedG2LR,addedOther-removedOther);
       $write("Items added:   %d | %d | %d | %d |\n", added,addedL2GW,addedG2LR,addedOther);
       $write("Items removed: %d | %d | %d | %d |\n", removed,removedL2GW,removedG2LR,removedOther);
       foreach(tab[i]) tab[i].display();
       $write("----------------------------------------------------------------------\n");
       unlock();
    endtask: display
  endclass : BmTransactionTable
  
endpackage : bm_table_pkg



