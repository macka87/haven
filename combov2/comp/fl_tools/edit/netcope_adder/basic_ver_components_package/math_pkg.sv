/*
 * math_pkg.sv: FrameLink Monitor
 * Copyright (C) 2008 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
 * $Id$
 *
 * TODO:
 *
 */
   
// ----------------------------------------------------------------------------
//                        Package declaration
// ---------------------------------------------------------------------------- 

package math_pkg;

// ------------- log2() -------------------------------------------------------
function int log2 (input int n);
  int a;
  int m;  
  a=0;
  m=1;
  while (m<n) begin
    a=a+1;
    m=m*2;
  end
  log2=a;
endfunction : log2

// ------------- pow() --------------------------------------------------------
function longint pow (input int x, int a);
  longint mocnina; 
  
  if (a==0) mocnina=1;
  else begin
    mocnina=1;
    for (int i=0; i<a; i++)
    mocnina=mocnina*x;
  end
  
  pow=mocnina;
  
 endfunction : pow
 
// ----------- abs() ----------------------------------------------------------
function int abs (input int n);
  if (n<0) return -n;
  else return n;
endfunction : abs

// ----------- max() ----------------------------------------------------------
function int max (input int x, int y);
  if (x < y)
    return y;
  else
    return x;
endfunction : max

// ----------- min() ----------------------------------------------------------
function int min (input int x, int y);
  if (x < y)
    return x;
  else
    return y;
endfunction : min
 
endpackage : math_pkg
