/*
 * ethernet_type_pkg.sv: SystemVerilog Ethernet type package
 * Copyright (C) 2009 CESNET
 * Author(s):  Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
 * TODO:
 */

/*
 * This package contains values for Ethernet type field.
 */
package ethernet_type_pkg; 
   const bit   [15:0]   IPV4 = 16'h0800;
   const bit   [15:0]   IPV6 = 16'h86DD;
   const bit   [15:0]   MPLSUNI = 16'h8847;
   const bit   [15:0]   MPLSMULTI = 16'h8848;
   const bit   [15:0]   ARP = 16'h0806;
   const bit   [15:0]   RARP = 16'h8035;
   const bit   [15:0]   VLANTAG = 16'h8100;
   const bit   [15:0]   VLANQ_in_QTAG1 = 16'h9100;
   const bit   [15:0]   VLANQ_in_QTAG2 = 16'h9200;
   const bit   [15:0]   VLANQ_in_QTAG3 = 16'h9300;
   const bit   [15:0]   VLANADTAG = 16'h88a8;
endpackage : ethernet_type_pkg