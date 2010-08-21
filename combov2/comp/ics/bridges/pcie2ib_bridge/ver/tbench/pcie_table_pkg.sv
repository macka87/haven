//
// pcie_table_pkg.sv: PCIe transaction table
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
// $Id: pcie_table_pkg.sv 688 2007-10-19 16:11:56Z tomalek $
//

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package pcie_table_pkg;

  import pcie_transaction_pkg::*;        // PCIE Transaction package

  // --------------------------------------------------------------------------
  // -- PCIE Transaction table
  // --------------------------------------------------------------------------
  class PcieTransactionTable;
     // ---------------------
     // -- Class Variables --
     // ---------------------
     PcieTransaction tab[$]; // table
     semaphore sem;
     integer added;
     integer removed;
     integer addedWR;
     integer addedRD;
     integer addedCPLD;
     integer removedWR;     
     integer removedRD;
     integer removedCPLD;
     
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      sem = new(1);
      added = 0;
      removed = 0;
      addedWR = 0; 
      addedRD = 0;
      addedCPLD = 0;
      removedWR = 0;     
      removedRD = 0;
      removedCPLD = 0;
    endfunction
    
    // ------------------------------------------------------------------------
    // Add item to table
    task add(PcieTransaction item);
       lock();
       this.tab.push_back(item); // Insert item to table       
       plus(item);
       unlock();
    endtask: add
    
    // ------------------------------------------------------------------------
    // Remove item from table
    task remove(PcieTransaction transaction);
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
        $write("Error (%t): Unable to remove Pcie transaction:  \n",$time());
        transaction.display(1);
        end
    endtask: remove

    // ------------------------------------------------------------------------
    // Remove item from table
    task removeNoData(PcieTransaction transaction);
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
        $write("Error (%t):Unable to remove Pcie transaction:\n  ",$time());
        transaction.display();
        end
    endtask: removeNoData
 
    // ------------------------------------------------------------------------
    // Remove item from table
    task removeOnlyData(PcieTransaction transaction);
      bit auxRemove = 0;
      lock();
      for (integer i=0; i < tab.size; i++) begin
        int same = 1; // Suppose that are same
        for (integer j=0; j < transaction.data.size; j++) if (transaction.data[j] != tab[i].data[j]) same=0;         
        if (transaction.transType != tab[i].transType) same=0;
        
        if (same) begin
          auxRemove = 1;
          minus(tab[i]);
          tab.delete(i);
          break;
        end
      end
      unlock();
      
      if (!auxRemove) begin 
        $write("Error: Unable to remove Pcie transaction (CPLD data):  ");
        transaction.display(1);
        end
    endtask: removeOnlyData    

    // ------------------------------------------------------------------------
    // Remove item from table
    task removeCpldData(PcieTransaction transaction); 
      bit auxRemove = 0;                                               
      lock();
      for (integer i=0; i < tab.size; i++) begin        
        int same = 1; // Suppose that are same 

        // check data and transaction type
        for (integer j=0; j < transaction.data.size; j++) begin
           if (tab[i].data.size == j) begin same=0; break; end
           if (transaction.data[j] != tab[i].data[j]) same=0;                    
        end
        
        if (transaction.transType != tab[i].transType) same=0;
        
        // remove whole transaction or only its part
        if (same) begin
          int ind=0;
          logic [7:0] data[] = new[tab[i].data.size-transaction.data.size]; 
          auxRemove = 1;

          // delete matched part of CPLD transaction and shift data (copy,delete,new)
          for (integer j=transaction.data.size; j < tab[i].data.size; j++) data[ind++] = tab[i].data[j];
          tab[i].data.delete;
          tab[i].data = new[data.size];
          for (integer j=0; j < data.size; j++) tab[i].data[j] = data[j];
          
          // if all data are removed, remove whole transaction
          if (tab[i].data.size == 0) begin
            minus(tab[i],1);
            tab.delete(i);
          end
          break;
        end
      end
      unlock();
      
      if (!auxRemove) begin 
        $write("Error: Unable to remove Pcie transaction (CPLD data):  ");
        transaction.display();
        end        
    endtask: removeCpldData        

    // ------------------------------------------------------------------------
    // Add new transaction to statisctics
    task plus(PcieTransaction transaction);
      added++;

      case (transaction.transType)
        WR32: begin
          addedWR++;
          end
        WR64: begin
          addedWR++;
          end
        RD32: begin
          addedRD++;
          end
        RD64: begin
          addedRD++;
          end          
        CPLD: begin
          if (transaction.data.size > 0) addedCPLD++;          
          end                    
      endcase     
    endtask: plus

    // ------------------------------------------------------------------------
    // Remove new transaction from statisctics
    task minus(PcieTransaction transaction, bit lastCPLD = 0);
      removed++;
      
      case (transaction.transType)
        WR32: begin
          removedWR++;
          end
        WR64: begin
          removedWR++;
          end
        RD32: begin
          removedRD++;
          end
        RD64: begin
          removedRD++;
          end                   
        CPLD: begin
          if (lastCPLD) removedCPLD++;
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
    // display transaction table
    task display(integer full=0);
       lock();
       $write("----------------------------------------------------------------------\n");
       $write("-- PcieTransaction Table\n");
       $write("----------------------------------------------------------------------\n");
       $write("                     IN SUM            WR            RD          CPLD\n");       
       $write("Size:          %d | %d | %d | %d |\n", tab.size,addedWR-removedWR,addedRD-removedRD,addedCPLD-removedCPLD);
       $write("Items added:   %d | %d | %d | %d |\n", added,addedWR,addedRD,addedCPLD);
       $write("Items removed: %d | %d | %d | %d |\n", removed,removedWR,removedRD,removedCPLD);
       foreach(tab[i]) tab[i].display(full);
       $write("----------------------------------------------------------------------\n");
       unlock();
    endtask: display
  endclass : PcieTransactionTable
  
endpackage : pcie_table_pkg



