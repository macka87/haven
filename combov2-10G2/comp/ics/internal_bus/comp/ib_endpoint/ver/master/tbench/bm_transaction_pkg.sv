/*
 * bm_transaction_pkg.sv: Bus Master Transaction
 * Copyright (C) 2007 CESNET
 * Author(s): Tomas Malek <tomalek@liberouter.org>
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
 * $Id: bm_transaction_pkg.sv 333 2007-09-05 20:07:59Z xkobie00 $
 *
 * TODO:
 *
 */


// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package bm_transaction_pkg; 
  
  // -- Bus Master Transaction Types Constants ------------------------------
  const logic [1:0] BM_G2LR_TYPE  = 2'b00; // G2LW transaction
  const logic [1:0] BM_L2GW_TYPE  = 2'b01; // L2GW transaction
  const logic [1:0] BM_L2LR_TYPE  = 2'b10; // L2LR transaction
  const logic [1:0] BM_L2LW_TYPE  = 2'b11; // L2LW transaction

  // -- Internal Bus Transaction Types ----------------------------------------
  typedef enum {BM_G2LR=0, BM_L2GW=1, BM_L2LR=2, BM_L2LW=3} eBmTransactionType;

  // --------------------------------------------------------------------------
  // -- Bus Master Transaction Class
  // --------------------------------------------------------------------------
  /* This class describe transaction and simplyfy transaction random
   * generation.
   */
  class BusMasterTransaction;

    // -- Public Class Atributes --
    rand logic [31:0]     localAddr;  // Transaction Local Address
    rand logic [63:0]     globalAddr; // Transaction Global Address
    rand logic [15:0]     tag;        // Transaction Tag
    rand logic [11:0]     length;     // Transaction Length
    rand eBmTransactionType transType;  // Transaction Type

    // Delays in driver
    rand integer txDelay;    // Wait txDelay clock cycles before transaction send
    
    // Transaction types probability weights (set 0 to switch off)
    int G2LR_wt = 1; // Write transaction
    int L2GW_wt = 1; // Read transaction
    int L2LR_wt = 1; // Write transaction
    int L2LW_wt = 1; // Read transaction

    // Transaction parameter limits
    logic [31:0] localAddrLow   = 32'h00000000;
    logic [31:0] localAddrHigh  = 32'h00010000;
    logic [63:0] globalAddrLow  = 64'h000000000000000;
    logic [63:0] globalAddrHigh = 64'h000000000010000;
    logic [15:0] tagLow         = 16'h0000;
    logic [15:0] tagHigh        = 16'hFFFF;
    logic [11:0] lengthLow      = 12'h001;
    logic [11:0] lengthHigh     = 12'h01F;

    // Delays limits
    integer txDelayLow          = 0;
    integer txDelayHigh         = 4;

    // -- Private Class Atributes --
    
    // -- Constrains --

    // Constrain for Transactions Types
    constraint cTransactions {
      transType dist { BM_G2LR := G2LR_wt, BM_L2GW := L2GW_wt,
                       BM_L2LR := L2LR_wt, BM_L2LW := L2LW_wt
                     };
    }

    // Delays constrains
    constraint cDelays {
      txDelay inside {[txDelayLow:txDelayHigh]};
      }

    // Constrain for Data ranges
    constraint cRanges {
      localAddr  inside {[localAddrLow:localAddrHigh]};
      globalAddr inside {[globalAddrLow:globalAddrHigh]};
      tag        inside {[tagLow:tagHigh]};
      length     inside {[lengthLow:lengthHigh]};
    }

    // -- Public Class Methods --

    //-- Copy ----------------------------------------------------------------- 
    // Copy constructor
    virtual function BusMasterTransaction copy();
       copy = new;
       copyData(copy);
    endfunction : copy

    //-- Show transaction -----------------------------------------------------
    // Function show transaction in text format
    function void display();
      $write("Transaction LOCAL_ADDR=%0x, GLOBAL_ADDR=%0x, TAG=%0x, \
              LENGTH=%0x, TYPE=", localAddr, globalAddr, tag, length);
      case (transType)
        BM_L2GW:
          $write("L2GW\n");
        BM_G2LR:
          $write("G2LR\n");
        BM_L2LW:
          $write("L2LW\n");
        BM_L2LR:
          $write("L2LR\n");
      endcase;

    endfunction

    // -- Private Class Methods --

    //-- Copy Data ------------------------------------------------------------ 
    // Function copy data from actual object to copy object
    virtual function void copyData(BusMasterTransaction copy);
      copy.localAddr   = localAddr;
      copy.globalAddr  = globalAddr;
      copy.tag         = tag;
      copy.length      = length;
      copy.transType   = transType;   

      copy.txDelay = txDelay; 
    
      copy.G2LR_wt = G2LR_wt;
      copy.L2GW_wt = L2GW_wt;
      copy.L2LR_wt = L2LR_wt;
      copy.L2LW_wt = L2LW_wt;
    
      copy.localAddrLow   = localAddrLow;
      copy.localAddrHigh  = localAddrHigh;
      copy.globalAddrLow  = globalAddrLow;
      copy.globalAddrHigh = globalAddrHigh;
      copy.tagLow         = tagLow;
      copy.tagHigh        = tagHigh;
      copy.lengthLow      = lengthLow;
      copy.lengthHigh     = lengthHigh;
    endfunction : copyData
  
  endclass : BusMasterTransaction


  // -- Trnsaction mailbox ----------------------------------------------------
  typedef mailbox #(BusMasterTransaction) tBmTransMbx;

endpackage : bm_transaction_pkg
