//
// ib_table_pkg.sv: IB transaction table
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
// $Id: ib_table_pkg.sv 688 2007-10-19 16:11:56Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_table_pkg;

  import ib_transaction_pkg::*;        // Internal Bus Transaction package

  // --------------------------------------------------------------------------
  // -- IB Transaction table
  // --------------------------------------------------------------------------
  class IbTransactionTable;
     // ---------------------
     // -- Class Variables --
     // ---------------------
     InternalBusTransaction tab[$]; // table
     semaphore sem;
     integer added;
     integer removed;
     integer addedL2LR;
     integer addedL2LW;
     integer addedRDCL;
     integer removedL2LR;
     integer removedL2LW;
     integer removedRDCL;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      sem = new(1);
      added = 0;
      removed = 0;
      addedL2LR = 0;
      addedL2LW = 0;
      addedRDCL = 0;
      removedL2LR = 0;
      removedL2LW = 0;
      removedRDCL = 0;
    endfunction
    
    // ------------------------------------------------------------------------
    // Add item to table
    task add(InternalBusTransaction item);
       lock();
       this.tab.push_back(item); // Insert item to table
       plus(item);
       unlock();
    endtask: add
    
    // ------------------------------------------------------------------------
    // Remove item from table
    task remove(InternalBusTransaction transaction);
      bit auxRemove = 0;
      lock();
      for (integer i=0; i < tab.size; i++) begin
        if (tab[i].compare(transaction) == 1) begin
          auxRemove = 1;
          minus(tab[i]);
          tab.delete(i);
          break;
          end
      end
      unlock();
      
      if (!auxRemove) begin 
        $write("Error (%t): Unable to remove Internal Bus transaction:  \n",$time());
        transaction.display(1);
        end
    endtask: remove

    // ------------------------------------------------------------------------
    // Remove item from table (control only header)
    task removeNoData(InternalBusTransaction transaction);
      bit auxRemove = 0;
      lock();
      for (integer i=0; i < tab.size; i++) begin
        if (tab[i].compare(transaction,0) == 1) begin
          auxRemove = 1;
          minus(tab[i]);
          tab.delete(i);
          break;
          end
      end
      unlock();
      
      if (!auxRemove) begin 
        $write("Error: Unable to remove Internal Bus transaction:  ");
        transaction.display();
        end
    endtask: removeNoData
    
    // ------------------------------------------------------------------------
    // Remove item from table (cheks only data and type)
    task removeCplData(InternalBusTransaction transaction);
      bit auxRemove = 0;
      lock();
      for (integer i=0; i < tab.size; i++) begin

        if ((tab[i].compareData(transaction) == 1) && 
            (tab[i].transType == transaction.transType)) begin
          minus(tab[i]);
          auxRemove = 1;
          tab.delete(i);
          break;
        end
        
      end
      unlock();
      
      if (!auxRemove) begin 
        $write("Error (%t): Unable to remove Internal Bus transaction (CPL data):  \n",$time());
        transaction.display(1);
        end
    endtask: removeCplData    

    // ------------------------------------------------------------------------
    // Add new transaction to statisctics
    task plus(InternalBusTransaction transaction);
      added++;
      
      case (transaction.transType)
        L2LW: begin
          if (transaction.tag[8:7] == 2'b11) addedRDCL++; // it remarks {last_compl,BM_RESULT}
          addedL2LW++;
          end
        L2LR: begin
          addedL2LR++;
          end          
        RDCL: begin
          if (transaction.data.size == 0) addedRDCL++;
          end                    
      endcase     
    endtask: plus

    // ------------------------------------------------------------------------
    // Remove new transaction from statisctics
    task minus(InternalBusTransaction transaction);
      removed++;
      
      case (transaction.transType)
        L2LW: begin
          removedL2LW++;
          end
        L2LR: begin
          removedL2LR++;
          end          
        RDCL: begin
          if (transaction.data.size > 0) removedRDCL++;
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
    task display(integer full=0);
       lock();
       $write("----------------------------------------------------------------------\n");
       $write("-- IbTransaction Table\n");
       $write("----------------------------------------------------------------------\n");
       $write("                     IN SUM          L2LW          L2LR          RDCL\n");       
       $write("Size:          %d | %d | %d | %d |\n", tab.size,addedL2LW-removedL2LW,addedL2LR-removedL2LR,addedRDCL-removedRDCL);
       $write("Items added:   %d | %d | %d | %d |\n", added,addedL2LW,addedL2LR,addedRDCL);
       $write("Items removed: %d | %d | %d | %d |\n", removed,removedL2LW,removedL2LR,removedRDCL);
       foreach(tab[i]) tab[i].display(full);
       $write("----------------------------------------------------------------------\n");
       unlock();
    endtask: display
  endclass : IbTransactionTable
  
endpackage : ib_table_pkg



