/*
 * scoreboard.sv: Scoreboard for ib_switch verification
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
 * $Id: scoreboard.sv 12297 2009-12-16 18:17:27Z washek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package scoreboard_pkg;

  import sv_common_pkg::*;   // Verification common package
  import ib_common_pkg::*;   // InternalBus common package
  import ib_params_pkg::*;
  

  // --------------------------------------------------------------------------
  // -- Driver0 Callbacks
  // --------------------------------------------------------------------------
  class SwitchDriver0Cbs #(pIbSwitchGenerics G = dIbSwitchGenerics)
                                                             extends DriverCbs;
    TransactionTable #(0) tab1, tab2;
    
    function new (TransactionTable #(0) tab1, TransactionTable #(0) tab2);
      this.tab1 = tab1;
      this.tab2 = tab2;
    endfunction
    
    virtual task pre_tx(ref Transaction transaction, string inst);
      InternalBusTransaction tr;
      logic [31:0] addr;
      $cast(tr,transaction);
      
      if (G.MASTER) begin
         addr = tr.globalAddr[31:0];
         if (tr.transType != L2GW && tr.transType != G2LR) begin
            if (addr >= G.PORT1_BASE && addr < G.PORT1_BASE + G.PORT1_LIMIT)
               tab1.add(transaction);
            if (addr >= G.PORT2_BASE && addr < G.PORT2_BASE + G.PORT2_LIMIT)
               tab2.add(transaction);
         end
      end else begin
         tab1.add(transaction);
         tab2.add(transaction);
      end
      
    endtask

  endclass : SwitchDriver0Cbs
  
  
  // --------------------------------------------------------------------------
  // -- Driver1 Callbacks
  // --------------------------------------------------------------------------
  class SwitchDriver1Cbs #(pIbSwitchGenerics G = dIbSwitchGenerics)
                                                             extends DriverCbs;  
    TransactionTable #(0) tab0, tab2;
    
    function new (TransactionTable #(0) tab0, TransactionTable #(0) tab2);
      this.tab0 = tab0;
      this.tab2 = tab2;
    endfunction
    
    virtual task pre_tx(ref Transaction transaction, string inst);
      InternalBusTransaction tr;
      logic [31:0] addr;
      $cast(tr,transaction);

      if (G.MASTER) begin
         addr = tr.globalAddr[31:0];
         if (tr.transType != L2GW && tr.transType != G2LR &&
             addr >= G.PORT2_BASE && addr < G.PORT2_BASE + G.PORT2_LIMIT)
            tab2.add(transaction);
         else 
            tab0.add(transaction);
      end else
         tab0.add(transaction);
      
    endtask

  endclass : SwitchDriver1Cbs


  // --------------------------------------------------------------------------
  // -- Driver2 Callbacks
  // --------------------------------------------------------------------------
  class SwitchDriver2Cbs #(pIbSwitchGenerics G = dIbSwitchGenerics)
                                                             extends DriverCbs;  
    TransactionTable #(0) tab0, tab1;
    
    function new (TransactionTable #(0) tab0, TransactionTable #(0) tab1);
      this.tab0 = tab0;
      this.tab1 = tab1;
    endfunction
    
    virtual task pre_tx(ref Transaction transaction, string inst);
      InternalBusTransaction tr;
      logic [31:0] addr;
      $cast(tr,transaction);
      
      if (G.MASTER) begin
         addr = tr.globalAddr[31:0];
         if (tr.transType != L2GW && tr.transType != G2LR &&
             addr >= G.PORT1_BASE && addr < G.PORT1_BASE + G.PORT1_LIMIT)
            tab1.add(transaction);
         else 
            tab0.add(transaction);
      end else
         tab0.add(transaction);
      
    endtask

  endclass : SwitchDriver2Cbs
  
  // --------------------------------------------------------------------------
  // -- Monitor Callbacks
  // --------------------------------------------------------------------------
  class SwitchMonitorCbs extends MonitorCbs;
    
    TransactionTable #(0) tab;
    
    function new (TransactionTable #(0) tab);
      this.tab = tab;
    endfunction
    
    virtual task post_rx(Transaction transaction, string inst);
      bit status = 0;
      tab.remove(transaction,status,1);
      if (status == 0) begin
        $write($time," ",inst,": Unable to remove transaction:  ");
        transaction.display();
      end
    endtask

  endclass : SwitchMonitorCbs


  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard #(pIbSwitchGenerics G = dIbSwitchGenerics);
    
    // -- Class Variables --
    TransactionTable #(0) table0;
    TransactionTable #(0) table1;
    TransactionTable #(0) table2;
    
    SwitchMonitorCbs      monitor0Cbs;
    SwitchMonitorCbs      monitor1Cbs;
    SwitchMonitorCbs      monitor2Cbs;
    SwitchDriver0Cbs #(G) driver0Cbs;
    SwitchDriver1Cbs #(G) driver1Cbs;
    SwitchDriver2Cbs #(G) driver2Cbs;

    // -- Constructor ---------------------------------------------------------
    function new();
      table0 = new;
      table1 = new;
      table2 = new;

      driver0Cbs  = new(table1,table2);
      driver1Cbs  = new(table0,table2);
      driver2Cbs  = new(table0,table1);
      
      monitor0Cbs = new(table0);
      monitor1Cbs = new(table1);
      monitor2Cbs = new(table2);
    endfunction
    
    // -- Tables are empty ----------------------------------------------------
    // Returns 1 if all transaction tables are empty, else returns 0.
    function bit tablesEmpty();
      if (table0.tr_table.size() == 0 &&
          table1.tr_table.size() == 0 &&
          table2.tr_table.size() == 0 )
        tablesEmpty = 1;
      else
        tablesEmpty = 0;
    endfunction
    
    // -- Reset ---------------------------------------------------------------
    // Clears all tables
    task reset();
      table0.tr_table = new[0];
      table1.tr_table = new[0];
      table2.tr_table = new[0];
    endtask
    
    // -- Display -------------------------------------------------------------
    task display();
      table0.display(1,"Table 0 (Upstream)");
      table1.display(1,"Table 1 (Downstream 1)");
      table2.display(1,"Table 2 (Downstream 2)");
    endtask
    
  endclass : Scoreboard
  
endpackage : scoreboard_pkg

