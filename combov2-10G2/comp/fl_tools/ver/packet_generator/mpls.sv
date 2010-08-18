/*
 * mpls.sv: MPLS protocol
 * Copyright (C) 2009 CESNET
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
 * $Id: mpls.sv 12526 2010-01-27 11:14:00Z xkosar02 $
 *
 * TODO:
 *
 */

/*
 * This class implements MPLS(Multi protocol label switching) protocol. Class
 * inherates from Layer abstract class. 
 */  
class MPLS extends Layer;
   /*
   * Randomizations constraints:
   * minLabel - minimal MPLS label for randomization
   * maxLabel - maximal MPLS label for randomization
   * 
   * Class atributes affected by randomization:
   * label          - MPLS label
   * exp            - experimental / currently used for implementing QoS 
   * ttl            - time to live
   *
   * Class atributes not affected by randomization:
   * stack - indicate bottom of MPLS stack, set post randomization according
   *         upper layer protocol. 1 means bottom of stack(last MPLS label),
   *         0 means that current MPLS label isn't last.
   *
   * Class constants:
   * headerSize - size of protocol header
   */
         bit unsigned   [19:0]   minLabel;
         bit unsigned   [19:0]   maxLabel;
   rand  bit unsigned   [19:0]   label;
   rand  bit unsigned   [2:0]    exp;
         bit unsigned            stack;
   rand  bit unsigned   [7:0]    ttl;
 
   const int unsigned            headerSize = 4;
   
   /*
    * Class constructor.
    */
   function new();
      typ = "MPLS";
      subtype = "";
      name = "MPLS";
      level = 5;
      next = null;
      previous = null;
      errorProbability = 0;
      minLabel = '0;
      maxLabel = '1;
   endfunction: new
 
   /*
    * Constraint for randomization. Sets value ranges for random variables.
    */
   constraint c
   {
      label inside {[minLabel:maxLabel]};
   }
 
   /*
    * Sets bottom of MPLS stack according upper layer protocol. If upper layer
    * protocol is MPLS stack is set to 0, otherwise is set to 1. It also set 
    * data length boundaries for upper layer protocol.
    */
   function void post_randomize();
      if (next != null)
      begin
         if (this.next.typ != "MPLS")
            this.stack = 1;
         else
            this.stack = 0;
         next.minMTU = (minMTU - headerSize > 0) ? minMTU - headerSize : 0;
         next.maxMTU = (maxMTU - headerSize > 0) ? maxMTU - headerSize : 0;
         void'(next.randomize);    
      end
   endfunction: post_randomize
 
   /*
    * Returns array of bytes, which contains protocol header.
    */
   function data getHeader();
      data result = new[headerSize];
      bit [31:0] word;
      word[7:0] = ttl;
      word[8] = stack;
      word[11:9] = exp;
      word[31:12] = label;
      
      result[0] =  word[31:24];
      result[1] =  word[23:16];
      result[2] =  word[15:8];
      result[3] =  word[7:0];

      return result;
   endfunction: getHeader
   
    /*
     * Returns array of bytes, which contains protocol footer. It returns zero
     * sized array.
     */     
   function data getFooter();
      data result;
      return result;
   endfunction: getFooter
   
    /*
     * Returns class atribute by it's name in form of array of bytes.
     * Not implemented yet.
     */     
   function data getAttributeByName(string name);
      data result;
      return result;
   endfunction: getAttributeByName
   
    /*
     * Returns array of bytes containing protocol and upper layers protocol
     * data.
     */      
   function data getData();
      data header, payload, footer, result;
      header = getHeader();
      payload = next.getData();
      footer = getFooter();
      result = new [header.size() + payload.size()];
      foreach (header[j])
         result[j] = header[j];
      foreach (payload[j])
         result[header.size() + j] = payload[j];
      return result; 
   endfunction: getData
 
    /*
     * Copy function.
     */
   function Layer copy();
      MPLS protocol;
      protocol = new();
      protocol.label = label;
      protocol.minLabel = minLabel;
      protocol.maxLabel = maxLabel;
      protocol.exp = exp;
      protocol.stack = stack;
      protocol.ttl = ttl;
       
      protocol.typ = typ;
      protocol.subtype = subtype;
      protocol.name = name;
      protocol.level = level;
      protocol.next = next;
      protocol.previous = previous;
      protocol.errorProbability = errorProbability;
      protocol.minMTU = minMTU;
      protocol.maxMTU = maxMTU;
    
      return protocol;
   endfunction: copy
 
    /*
     * Check if upper layer protocol is compatibile with MPLS.
     * This function is used by generator.
     *
     * Parameters:
     * typ     - type of protocol
     * subtype - subtype of protocol
     * name    - name of protocol (for special cases, mostly unused)
     *
     * Supported protocols:
     * IPv4, IPv6
     */
   function bit checkType(string typ, string subtype ,string name);
      if (typ == "IP")
      begin
         if (subtype == "4")
            return 1'b1;
         if (subtype == "6")
            return 1'b1;
      end;
      return 1'b0;
   endfunction: checkType
 
    /*
     * Displays informations about protocol including upper layer protocols.
     */
   function void display();
      $display("MPLS");
      $display("Label: %d", label);
      $display("Exp/QoS: %d", exp);
      $display("Stack: %d", stack);
      $display("TTL: %d", ttl);
      $display("-----------------------\n\n");
      if (next != null)
         next.display();
   endfunction: display
   
    /*
     * Returns length of protocol data plus all upper level protocols data 
     * length.
     *
     * Parameters:
     * split - if set length of RAW protocol layer isn't returned, otherwise
     *         the length of RAW protocol layer is returned.
     */    
   function int getLength(bit split);
      if (next != null)
         return headerSize + next.getLength(split);
      else
         return headerSize;
   endfunction: getLength
 
endclass: MPLS
