/*
 * raw_pattern.sv: RAW layer with patterns
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
 * $Id: raw_pattern.sv 12581 2010-02-01 16:59:01Z xkosar02 $
 *
 * TODO:
 *
 */

/*
 * This structure containts pattern and it's probability.
 */ 
typedef struct
{
   string   pattern;
   int      probability;
   int      position; // 0 - any
                      // 1 - start
                      // 2 - end 
                      // >2 - reserved (do nothing with the pattern)
} TPattern;

/*
 * This class implements RAWPattern protocol (unstructured data with patterns).
 * Class inherates from RAW abstract class. 
 */  
class RAWPattern extends RAW;
   /*
    * Class atributes not affected by randomization:
    * patterns       - array of patterns with their's probability
    * patternCount   - number of patterns
    * probabilitySum - sum of probabilities
    *
    * Class constants:
    * arrayGrow - size which is added to array size when array reallocation
    *             is necessary
    */
         TPattern patterns [];
         int      patternCount;
         int      probabilitySum;
   
   const int      arrayGrow = 5;
  
   /*
    * Post randomization includes random pattern to random unstructured data.
    */
   function void post_randomize();
      int      random = 0;
      int      currentProbabilitySum = 0;
      random = {$random} %  probabilitySum;

      foreach (patterns[j])
      begin
         // if radom value is smaller than sum of pattern probability and
         // current probability sum and size of data is big enough to contain
         // pattern size, then pattern is included.
         if ((random < patterns[j].probability + currentProbabilitySum) && (dataB.size - patterns[j].pattern.len >= 0))
         begin
            // insert pattern anywhere
            if (patterns[j].position == 0)
            begin
               random = {$random} % (dataB.size - patterns[j].pattern.len);
               for (int i = random; i<random + patterns[j].pattern.len; i++)
                  dataB[i] = patterns[j].pattern[i-random];
               break;
            end
            // insert pattern at the start
            if (patterns[j].position == 1)
            begin
               for (int i = 0; i<patterns[j].pattern.len; i++)
                  dataB[i] = patterns[j].pattern[i];
               break;
            end
            // insert pattern at the end
            if (patterns[j].position == 2)
            begin
               int start = dataB.size - patterns[j].pattern.len;
               for (int i = start; i<start + patterns[j].pattern.len; i++)
                  dataB[i] = patterns[j].pattern[i-start];
               break;
            end
         end
         else
            currentProbabilitySum = currentProbabilitySum + patterns[j].probability;
      end;
      
   endfunction:  post_randomize
  
   /*
    * Class constructor.
    */
   function new();
      typ = "RAW";
      subtype = "Pattern";
      name = "RAW with patterns";
      level = 30;
      next = null;
      previous = null;
      errorProbability = 0;
      patternCount = 0;
      probabilitySum = 0;
      patterns = new[arrayGrow];
   endfunction: new
 
   /*
    * Copy function.
    */
   function Layer copy();
      RAWPattern protocol;
      protocol = new();
      protocol.dataB = dataB;
      protocol.patterns = patterns;
      protocol.patternCount = patternCount;
      protocol.probabilitySum = probabilitySum;
        
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
    * Displays informations about protocol including upper layer protocols.
    */
   function void display();
      $display("RAW with patterns\n");
      $display("Length: %d \n", dataB.size());
      $display("-----------------------\n\n");
   endfunction: display
 
   /*
    * This function add pattern with it's probability to array of patters.
    * Parametrs:
    * pattern     - string containing pattern
    * probability - pattern probability
    */
   function void addPattern(string pattern, int probability, int position);
      // reallocate size of array
      if (patternCount == patterns.size)
      begin
         patterns = new[patterns.size + arrayGrow](patterns);
      end;
     
      patternCount = patternCount + 1;
      patterns[patternCount - 1].pattern = pattern;
      patterns[patternCount - 1].probability = probability;
      patterns[patternCount - 1].position = position;
      probabilitySum = probabilitySum + probability;
   endfunction: addPattern
 
endclass: RAWPattern