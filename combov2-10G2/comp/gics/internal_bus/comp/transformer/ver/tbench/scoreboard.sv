/*
 * scoreboard.sv: Scoreboard for ib_transformer verification
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
 * $Id: scoreboard.sv 8657 2009-06-04 10:57:57Z washek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package scoreboard_pkg;

  import sv_common_pkg::*;    // Verification common package
  //import ib_common_pkg::*;    // InternalBus common package
  

  // --------------------------------------------------------------------------
  // -- Driver Callbacks
  // --------------------------------------------------------------------------
  class TransformerDriverCbs extends DriverCbs;
    TransactionTable #(.behav(1)) tab;
    
    function new (TransactionTable #(.behav(1)) tab);
      this.tab = tab;
    endfunction
    
    virtual task pre_tx(ref Transaction transaction, string inst);
      tab.add(transaction);
    endtask

  endclass : TransformerDriverCbs
  

  // --------------------------------------------------------------------------
  // -- Monitor Callbacks
  // --------------------------------------------------------------------------
  class TransformerMonitorCbs extends MonitorCbs;
    TransactionTable #(.behav(1)) tab;
    
    function new (TransactionTable #(.behav(1)) tab);
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

  endclass : TransformerMonitorCbs


  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard;

    // -- Class Variables --
    TransactionTable #(.behav(1)) downTable;
    TransactionTable #(.behav(1)) upTable;
    
    TransformerMonitorCbs    upMonitorCbs;
    TransformerMonitorCbs    downMonitorCbs;
    TransformerDriverCbs     upDriverCbs;
    TransformerDriverCbs     downDriverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      downTable = new;
      upTable = new;

      upDriverCbs     = new(downTable);
      downDriverCbs   = new(upTable);
      upMonitorCbs    = new(upTable);
      downMonitorCbs  = new(downTable);
    endfunction
    
    // -- Tables are empty ----------------------------------------------------
    // Returns 1 if all transaction tables are empty, else returns 0.
    function bit tablesEmpty();
      if (downTable.tr_table.size() == 0 &&
          upTable.tr_table.size() == 0 )
        tablesEmpty = 1;
      else
        tablesEmpty = 0;
    endfunction
    
    // -- Reset ---------------------------------------------------------------
    // Clears all tables
    task reset();
      downTable.tr_table = new[0];
      upTable.tr_table   = new[0];
    endtask
    
    // -- Display -------------------------------------------------------------
    task display();
      downTable.display(1,"DOWN");
      upTable.display(1,"UP");
    endtask
    
  endclass : Scoreboard

endpackage : scoreboard_pkg

