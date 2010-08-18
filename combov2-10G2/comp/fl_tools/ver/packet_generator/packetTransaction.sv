/*
 * packetTransaction.sv: Packet transaction
 * Copyright (C) 2008 CESNET
 * Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
 * $Id: packetTransaction.sv 7607 2009-03-19 15:49:12Z xkosar02 $
 *
 * TODO:
 *
 */
 
import sv_fl_pkg::*;
import sv_common_pkg::*;
 
/*
 * This class implements PacketFrameLinkTransaction. Class inherates from
 * FrameLinkTransaction class. Protocol list is added to standart FrameLink
 * transaction.
 */
class PacketFrameLinkTransaction extends FrameLinkTransaction;
   /*
    * Class attributes:
    * packet        - double linked list, which contain used protocol classes
    *                 in this packet
    * split         - indicate if packet data should be splited to saparete
    *                 header and paylod. (Header is protocol headers(IP, TCP,
    *                 ...) and payload are unstructured data (RAW, ...))
    * splitPosition - split position in bytes
    */
   Layer   packet;
   bit     split;
   int     splitPosition;

    /*
     * This function is used to set FrameLink data according to protocol data.
     */
   function void connect();
      byte unsigned helper[];
      int length;
      
      // This variant is used for flowmon project
      if (split == 0)
      begin
         // one part frame will be created
         packetCount = 1;
         data = new[packetCount];
         data[0] = packet.getData;
         splitPosition = packet.getLength(1);
      end
      // This varian is for IDS project
      else
      begin
         // three part frame with fixed header will be created
         packetCount = 3;
         data = new[packetCount];
         
         data[0][0] = 0;
         data[0][1] = 0;
         
         helper = packet.getData;
         length = packet.getLength(0);
         
         splitPosition = packet.getLength(1);
         data[1] = new[splitPosition];
         
         for (int i = 0; i<splitPosition;i++)
            data[1][i] = helper[i];
            
         data[2] = new[length - splitPosition];
         
         for (int i = splitPosition; i<length;i++)
            data[2][i-splitPosition] = helper[i];
      end   
   endfunction: connect
    
   /*
    * Copy function.
    */
   virtual function Transaction copy(Transaction to = null);
      PacketFrameLinkTransaction tr;
      if (tr == null)
         tr = new();
      else 
         $cast(tr, to);

      tr.packetCount   = packetCount;
      tr.packetSizeMax = new[packetCount];
      tr.packetSizeMin = new[packetCount];
      tr.data          = new [packetCount];
      for (integer i=0; i < packetCount; i++)
        tr.data[i]     = new[data[i].size];

      tr.packetSizeMax = packetSizeMax;
      tr.packetSizeMin = packetSizeMin;
      tr.data=data;
      tr.packet = packet;
      tr.split = split;
      tr.splitPosition = splitPosition; 
      copy = tr;
   endfunction: copy
    
   
   /*
    * Displays informations about frame and used protocols.
    */   
   virtual function void display(string prefix = "");
      super.display(prefix);
      packet.display;
   endfunction : display
       
endclass: PacketFrameLinkTransaction
