/*
 * \file ibuf_xgmii_transaction.sv
 * \brief IBUF XGMII Transaction
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
 * $Id: crossbar_xgmii_transaction.sv 13933 2010-06-03 15:48:44Z xvikto03 $
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- IBUF XGMII Transaction Class
  // --------------------------------------------------------------------------
  /*!
   * \brief IBUF XGMII Transaction Class
   * 
   * This class describe IBUF XGMII transaction and simplyfy destination MAC 
   * address random generation.
   */
  class IbufXgmiiTransaction extends XgmiiTransaction;

    typedef enum {BROADCAST, MULTICAST, AVAILABLE_UNICAST, UNICAST} tMacType; 

    // -- Public Class Attributes --
    //! Randomization parameters
     //! Number of MAC addresses
    int macCount = 0; 
     //! MAC addresses
    byte unsigned macAddr[16][6] = '{default: 0};
   

    // -- Public Class Methods --

    //------------------------------------------------------------------------- 
    //! Copy
    /*!
     * Copy constructor
     *
     * \param to - 
     */
    virtual function Transaction copy(Transaction to = null);
      IbufXgmiiTransaction tr;
      if (to == null) begin
        tr = new();
        to = tr;
      end 

      to = super.copy(to);
      $cast(tr, to);

      tr.macCount      = macCount;
      tr.macAddr       = macAddr;

      copy = tr;
    endfunction: copy
      

    // -- Private Class Methods --

    //------------------------------------------------------------------------- 
    //! Post Randomize
    /*!
     * Function is called after randomization. It computes correct CRC or
     * inject error into it.
     */
    function void post_randomize();
      int macIndex;

      randcase
        // BROADCAST
        1: begin
          for (int i=0; i < 6; i++)
            data[i] = 8'hFF;
        end
        // MULTICAST
        1: begin
          data[0][0] = 1;
        end
        // AVAILABLE UNICAST
        1: begin
          if (macCount > 0) begin
            macIndex = $urandom_range(macCount-1);
            for (int i=0; i<6; i++)
              data[i] = macAddr[macIndex][i];
          end
        end
        // UNICAST
        1: ;
      endcase

      super.post_randomize();
    endfunction : post_randomize

  endclass : IbufXgmiiTransaction
