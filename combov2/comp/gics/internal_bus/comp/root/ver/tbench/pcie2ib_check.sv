/*
 * pcie2ib_check.sv: Pcie2IB check
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobierský <kobiersky@liberouter.org>
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

import sv_common_pkg::*;
import sv_ib_pkg::*;
import sv_pcie_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- Pcie2Ib Checker Driver Callbacks
  // --------------------------------------------------------------------------
  class Pcie2IbCheckDriverCbs extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable sc_table;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable sc_table);
      this.sc_table = sc_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called before is transaction sended 
    // Allow modify transaction before is sended
    virtual task pre_tx(ref Transaction transaction, string inst);
//      $write("PRE_TX_PCIE:\n");
//      transaction.display();
    endtask
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended 
    virtual task post_tx(Transaction transaction, string inst);
       sc_table.add(pcie2ib(transaction));
    endtask

    // ------------------------------------------------------------------------
    // Function transform PCIE transaction to IB transaction 
    function Transaction pcie2ib(input Transaction tr);
      PcieTransaction pcie;
      InternalBusTransaction result = new;
      $cast(pcie, tr);

      // Get transaction type
      case (pcie.transType)
        RD32, RD64: result.transType = L2LR;
        WR32, WR64: result.transType = L2LW;
        CPLD:       result.transType = RDC;
        CPLD_LAST:  result.transType = RDCL;
      endcase;

      // Get length
      result.length = getLength(pcie);

      // Set tag ( IN THIS TEST WE DON'T CARE )
      result.tag = 16'h0000;

      // Get Local Address
      result.localAddr = getLocalAddr(pcie);


      // Set global addr
      result.globalAddr[63:32] = 32'h00000000;
      case (pcie.transType)
        RD32, RD64,WR32,WR64: result.globalAddr[31:0]  = pBRIDGE_BASE_ADDR;
        CPLD, CPLD_LAST:result.globalAddr[31:0]  = 32'hDDDDDDDD; // Dont CARE
      endcase;

      if (pcie.transType != RD32 && pcie.transType!= RD64)
        result.data=pcie.data;

      pcie2ib = result;
    endfunction;

    // ------------------------------------------------------------------------
    // Function return length in bytes of read, write or completition 
    function int getLength(input PcieTransaction pcie);
      int length_10_0;
      int read_write_len;
      int cmpl_len;
      length_10_0 = (pcie.length == 0) ? 1024 : pcie.length;
      read_write_len = length_10_0*4 - pcie.minusBE();
      cmpl_len       = length_10_0*4 - pcie.lowerAddr[1:0];
      if (cmpl_len > pcie.byteCount)
        cmpl_len = pcie.byteCount;

      // Get transaction type
      case (pcie.transType)
        RD32, RD64: getLength = read_write_len;
        WR32, WR64: getLength = read_write_len;
        CPLD:       getLength = cmpl_len;
        CPLD_LAST:  getLength = cmpl_len;
      endcase;
    endfunction;

    // ------------------------------------------------------------------------
    // Function return local addr 
    function logic [31:0] getLocalAddr(input PcieTransaction pcie);
      logic [31:0] result;

      case (pcie.barHitN) 
        B1111110 : result = (pcie.address[31:0] & pBAR0_MASK) + pBAR0_REMAP;
        B1111101 : result = (pcie.address[31:0] & pBAR1_MASK) + pBAR1_REMAP;
        B1111011 : result = (pcie.address[31:0] & pBAR2_MASK) + pBAR2_REMAP;
        B1110111 : result = (pcie.address[31:0] & pBAR3_MASK) + pBAR3_REMAP;
        B1101111 : result = (pcie.address[31:0] & pBAR4_MASK) + pBAR4_REMAP;
        B1011111 : result = (pcie.address[31:0] & pBAR5_MASK) + pBAR5_REMAP;
        B0111111 : result = (pcie.address[31:0] & pEXP_ROM_MASK) + pEXP_ROM_REMAP;
      endcase;

      case (pcie.firstBE)
        F1111: result[1:0] = 2'b00;
        F1110: result[1:0] = 2'b01;
        F1100: result[1:0] = 2'b10;
        F1000: result[1:0] = 2'b11;   
        F0111: result[1:0] = 2'b00;
        F0011: result[1:0] = 2'b00; 
        F0110: result[1:0] = 2'b01;
        F0100: result[1:0] = 2'b10;
        F0010: result[1:0] = 2'b01;
        F0001: result[1:0] = 2'b00;
      endcase  

      if (pcie.transType == CPLD || pcie.transType == CPLD_LAST)
        result = pBRIDGE_BASE_ADDR;
      getLocalAddr = result;
    endfunction;

   endclass : Pcie2IbCheckDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class Pcie2IbCheckMonitorCbs extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable sc_table;
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable sc_table);
      this.sc_table = sc_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    
    virtual task post_rx(Transaction transaction, string inst);
      InternalBusTransaction ib;
      bit status=0;
//      $write("POST_RX_IB:\n");
//      transaction.display();

      $cast(ib, transaction);
      // Read, Write compare
      if (ib.transType != RDC && ib.transType != RDCL)
        sc_table.remove(transaction, status, CMP_PCIE2IB_RD_WR);
      else // Completition compare (don't look at adresses)
        sc_table.remove(transaction, status, CMP_PCIE2IB_CMPL);
     
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         transaction.display(); 
         sc_table.display();
         $stop;
      end;
    endtask
  endclass : Pcie2IbCheckMonitorCbs



  // -- Constructor ---------------------------------------------------------
  // Create a class 
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Pcie2IbCheck;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable       scoreTable;
    Pcie2IbCheckMonitorCbs monitorCbs;
    Pcie2IbCheckDriverCbs  driverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      this.scoreTable = new;
      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    // Create a class 
    task display();
      scoreTable.display();
    endtask
  endclass : Pcie2IbCheck

