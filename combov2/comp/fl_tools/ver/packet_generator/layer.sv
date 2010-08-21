/*
 * layer.sv: Packet Layer
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
 * $Id: layer.sv 12526 2010-01-27 11:14:00Z xkosar02 $
 *
 * TODO:
 *
 */
  
   /*
    * Definition of type data as array of byte.
    */
   typedef byte unsigned data [];
 

   /*
    * Abstract class Layer is inherated by all protocol's classes. It defines
    * common atributes and method's prototypes.
    */
   class Layer;
      /*
       * Class attributes:
       * typ              - Type of protocol such as ETHERNET, IP, etc.
       * subtype          - Subtype of protocol such as 4/6 for IPv4/IPv6.
       * name             - Name of class.
       * level            - Level of protocol, currently unused.
       * next             - Pointer to next protocol layer.
       * previous         - Pointer to previous protocol layer.
       * errorProbability - Probability of error in frame, currently unused.
       * minMTU           - Minimal size of data for current protocol.
       * maxMTU           - Maximal size of data for current protocol.
       */
      string typ;
      string subtype;
      string name;
      int level;
      Layer next;
      Layer previous;
      int errorProbability;
      int minMTU;
      int maxMTU;
         
      /*
       * Returns array of bytes, which contains protocol header.
       */
      virtual function data getHeader();
         data vystup = new[0];
         return vystup;
      endfunction: getHeader
      
      /*
       * Returns array of bytes, which contains protocol footer.
       */ 
      virtual function data getFooter();
         data vystup = new[0];
         return vystup;
      endfunction: getFooter
      
      /*
       * Returns class atribute by it's name in form of array of bytes.
       */ 
      virtual function data getAttributeByName(string name);
         data vystup = new[0];
         return vystup;
      endfunction: getAttributeByName
      
      /*
       * Returns array of bytes containing protocol and upper layers 
       * protocol data.
       */  
      virtual function data getData();
         data vystup = new[0];
         return vystup;
      endfunction: getData
      
      /*
       * Copy function.
       */
      virtual function Layer copy();
         return null;
      endfunction : copy
    
      /*
       * Check if upper layer protocol is compatibile with current protocol.
       * This function is used by generator.
       *
       * Parameters:
       * typ     - type of protocol
       * subtype - subtype of protocol
       * name    - name of protocol (for special cases, mostly unused)
       */  
      virtual function bit checkType(string typ, string subtype ,string name);
         return 0;
      endfunction: checkType
      
      /*
       * Displays informations about protocol including upper layer protocols.
       */
      virtual function void display();
      endfunction: display
      
      /*
       * Returns length of protocol data plus all upper level protocols data 
       * length.
       *
       * Parameters:
       * split - if set length of RAW protocol layer isn't returned, otherwise
       *         the length of RAW protocol layer is returned.
       */  
      virtual function int getLength(bit split);
         return 0;
      endfunction: getLength
      
   endclass : Layer