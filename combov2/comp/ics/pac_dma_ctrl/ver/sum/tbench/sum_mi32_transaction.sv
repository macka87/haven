
/*
 * \file sum_mi32_transaction.sv
 * \brief SUM MI32 initialsation transaction
 * \author Marek Santa <xsanta06@stud.fit.vutbr.cz>
 * \date 2009  
 */
 /*
 * Copyright (C) 2009 CESNET
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
 * $Id: 
 *
 * TODO:
 *
 */
 
  import sv_mi32_pkg::*;

  // --------------------------------------------------------------------------
  // -- SUM MI32 Transaction Class
  // --------------------------------------------------------------------------
  
  /*!
   * \brief SUM MI32 Transaction
   *
   * This class constrains general MI32 transaction for SUM initialisation 
   */ 
  class SumMi32Transaction extends Mi32Transaction;
    
    // -- Private Class Atributes --
    logic [63:0] txGAddr = 0;

    constraint SumInit {
      if (data_id == 0) {
        address == 32'h18;
        data    == txGAddr[31:0];
      }
      else if (data_id == 1) {
        address == 32'h1C;
        data    == txGAddr[63:32];
      }
      else {
        address == {(data_id-2)*2,6'h14};
        data    == 0;
      }
      be == '1;
      rw == 1;
    }


    // -- Public Class Methods --

    //-- Copy -----------------------------------------------------------------
    // Copy constructor
    virtual function Transaction copy(Transaction to = null);
      SumMi32Transaction tr;

      if (to == null) 
      begin
        tr = new();
        to = tr;
      end  

      to = super.copy(to);
      $cast(tr, to);

      tr.txGAddr       = txGAddr;

      copy = tr;
   endfunction: copy

   // -- Private Class Methods --

  endclass: SumMi32Transaction  
