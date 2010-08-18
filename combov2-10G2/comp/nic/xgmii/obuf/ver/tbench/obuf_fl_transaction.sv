/* \file obuf_fl_transaction.sv
 * \brief OBUF FrameLink Transaction
 * \author Marek Santa <santa@liberouter.org> 
 * \date 2010
 */
/*
 * Copyright (C) 2010 CESNET
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
 * $Id: obuf_fl_transaction.sv 14773 2010-08-03 12:17:38Z xsanta06 $
 *
 * TODO:
 *
 */ 

  // --------------------------------------------------------------------------
  // -- OBUF FrameLink Transaction Class
  // --------------------------------------------------------------------------
  /*!
   * \brief OBUF FrameLink Transaction Class
   * 
   * This class describe OBUF FL transaction and simplyfy transaction random
   * generation.
   */
  class ObufFrameLinkTransaction extends FrameLinkTransaction;
      
     // -- Public Class Atributes --
     //! Randomization parameters
      //! Frame footer bit 0 (discard frame) set to 0 
     int discardZero_wt        = 0;     
      //! Frame footer bit 0 (discard frame) set to 1 
     int discardOne_wt         = 1;     
      //! Frame footer bit 0 (replace MAC address) set to 0 
     int replaceMacZero_wt     = 0;     
      //! Frame footer bit 0 (replace MAC address) set to 1 
     int replaceMacOne_wt      = 1;     
   
     // -- Constrains --
     constraint c2 {
       if (packetCount > 1) {
         (data[1][0][0]) dist { 1'b0 := discardZero_wt,
                                1'b1 := discardOne_wt
                              };

         (data[1][0][1]) dist { 1'b0 := replaceMacZero_wt,
                                1'b1 := replaceMacOne_wt
                              };
       } 
       };


    // -- Public Class Methods --
  
    //------------------------------------------------------------------------- 
    //! Copy
    /*!
     * Copy constructor
     *
     * \param to - 
     */
     virtual function Transaction copy(Transaction to = null);
       ObufFrameLinkTransaction tr;
       if (to == null) begin
         tr = new();
         to = tr;
       end 

       to = super.copy(to);
       $cast(tr, to);

       tr.discardZero_wt      = discardZero_wt;
       tr.discardOne_wt       = discardOne_wt;
       tr.replaceMacZero_wt   = replaceMacZero_wt;
       tr.replaceMacOne_wt    = replaceMacOne_wt;
       
       copy = tr;
     endfunction: copy
       
   endclass: ObufFrameLinkTransaction

