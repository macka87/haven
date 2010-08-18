/*
 * ip_protocol_pkg.sv: SystemVerilog IP protocol package
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
 * This package contains values for IPv4/IPv6 protocol/next header field.
 * See IANA list of protocol numbers or RFC 791 for more.
 */
package ip_protocol_pkg; 
   const bit   [7:0]   PROTO_IPV4 = 8'd4;
   const bit   [7:0]   PROTO_IPV6 = 8'd41;
   const bit   [7:0]   PROTO_ICMP = 8'd1;
   const bit   [7:0]   PROTO_ICMPv6 = 8'd58;
   const bit   [7:0]   PROTO_TCP = 8'd6;
   const bit   [7:0]   PROTO_UDP = 8'd17;
   const bit   [7:0]   PROTO_ETHERNET = 8'd97;
   const bit   [7:0]   PROTO_RAW = 8'hFF;
endpackage : ip_protocol_pkg