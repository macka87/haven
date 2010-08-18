/*
 * \file mi32_ibuf_init_vector.sv
 * \brief MI32 initialisation vector for IBUF
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
 * $Id: mi32_ibuf_init_vector.sv 13005 2010-03-01 20:30:24Z xsanta06 $
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- MI32 IBUF Init Vector Class
  // --------------------------------------------------------------------------
  /*!
   * \brief MI32 IBUF Init Vector Class
   * 
   * This class describe IBUF initialisation vector as MI32 transactions.
   */
  class Mi32IbufInitVector extends Mi32Transaction;

    // -- Public Class Atributes --
    tIbufConfig ibufConfig;

    constraint IbufInit {
      // MAC address check mode
      if (data_id == 0) {
        address == 32'h38;
        data    == ibufConfig.pMacCheck;
      }
      // Error mask register
      if (data_id == 1) {
        address == 32'h24;
        data    == {ibufConfig.pErrMaskRegMac, ibufConfig.pErrMaskRegMtu, 
                    ibufConfig.pErrMaskRegMintu, ibufConfig.pErrMaskRegCrc, 
                    ibufConfig.pErrMaskRegXgmii};
      }
      // Min TU register
      if (data_id == 2) {
        address == 32'h30;
        data    == ibufConfig.pMintu;
      }
      // MTU register
      if (data_id == 3) {
        address == 32'h34;
        data    == ibufConfig.pMtu;
      }
      // Enable register
      if (data_id == 4) {
        address == 32'h20;
        data    == 32'h1;
      }
      be == '1;
      rw == 1;
    }  

    //-- New ------------------------------------------------------------------
    // Constructor
    function new(tIbufConfig ibufConfig = null);
      this.ibufConfig = ibufConfig;
    endfunction : new

    //-- Copy -----------------------------------------------------------------
    // Copy constructor
    virtual function Transaction copy(Transaction to = null);
      Mi32IbufInitVector tr;

      if (to == null) 
      begin
        tr = new();
        to = tr;
      end  

      to = super.copy(to);
      $cast(tr, to);

      tr.ibufConfig = ibufConfig;

      copy = tr;
   endfunction: copy

  endclass: Mi32IbufInitVector  
