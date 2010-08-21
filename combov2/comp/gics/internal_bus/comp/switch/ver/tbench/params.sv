/*
 * params.sv: Parameters of ib_switch test
 * Copyright (C) 2009 CESNET
 * Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
 * $Id: params.sv 12297 2009-12-16 18:17:27Z washek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package params;
  
  import ib_params_pkg::*;
  import math_pkg::log2;
  
  //------------------------- Global test params ------------------------------
  
  // Random seed
  const int SEED = 29;
  
  // Maximum number of transactions sent in one test
  const int TRANSACTION_COUNT = 10000;
  
  // Clock and Reset constants
  const time CLK_PERIOD = 10ns;
  const time RESET_TIME = 10*CLK_PERIOD;
   
  //--------------------------- Switch generics -------------------------------
  parameter pIbSwitchGenerics G = '{
    /* MASTER       */ 1,
    /* DATA_WIDTH   */ 64,
    /* HEADER_NUM   */ 4,
    /* PORT1_BASE   */ 32'h01010234,
    /* PORT1_LIMIT  */ 32'h05000000,
    /* PORT2_BASE   */ 32'h062300aa,
    /* PORT2_LIMIT  */ 32'hA0000bb0
  };
  
  
  //--------------------------- Parameter lists -------------------------------
  
  //-- Transaction parameters --
  
  const pIbTransaction parsTransUp[] = '{
    '{0,1,0,0,0,0,32'h0F000000,32'h0F000001,
      64'h0000000000000000,64'h0000000000000010,8'h00,8'hFF,13'h0001,13'h0010},
    '{0,1,0,0,0,0,32'h0F000000,32'h0F000001,
      64'h0000000001000000,64'h0000000001000010,8'h00,8'hFF,13'h0001,13'h0010}/*,
    '{2,2,0,0,1,1,32'h00000000,32'hFFFFFFFF,
      64'h0000000010000000,64'h0000000040000000,8'h00,8'hFF,13'h0001,13'h1000},
    '{2,2,0,0,1,1,32'h00000000,32'hFFFFFFFF,
      64'h000000000A000000,64'h0000000025000000,8'h00,8'hFF,13'h0001,13'h1000},
    '{2,2,0,0,1,1,32'h00000000,32'hFFFFFFFF,
      64'h000000001C000000,64'h0000000042000000,8'h00,8'hFF,13'h0001,13'h1000}*/
  };
  
  const pIbTransaction parsTransDown[] = '{
    '{0,0,0,0,0,1,32'h00000000,32'h00000010,
      64'h000000000F000000,64'h000000000F000001,8'h00,8'hFF,13'h0001,13'h0010},
    '{0,0,0,0,0,1,32'h01000000,32'h01000010,
      64'h000000000F000000,64'h000000000F000001,8'h00,8'hFF,13'h0001,13'h0010}/*,
    '{1,1,1,1,1,1,32'h00000000,32'hFFFFFFFF,
      64'h0000000000000000,64'h00000000FFFFFFFF,8'h00,8'hFF,13'h0001,13'h1000},
    '{1,1,0,0,1,1,32'h00000000,32'hFFFFFFFF,
      64'h000000000A000000,64'h0000000025000000,8'h00,8'hFF,13'h0001,13'h1000},
    '{1,1,0,0,1,1,32'h00000000,32'hFFFFFFFF,
      64'h000000001C000000,64'h0000000042000000,8'h00,8'hFF,13'h0001,13'h1000},
    '{0,0,1,1,0,0,32'h00000000,32'hFFFFFFFF,
      64'h0000000000000000,64'h0000000060000000,8'h00,8'hFF,13'h0001,13'h1000},
    '{1,1,0,0,1,1,32'h00000000,32'hFFFFFFFF,
      64'h0000000000000000,64'h0000000060000000,8'h00,8'hFF,13'h0001,13'h1000}*/
  };
  
  //-- Delays --
  
  const pIbDriverDelays parsDrvD[] = '{
    '{0,1,0,0,0,1,0,0}, //no delays
    '{1,3,0,5,1,3,0,3}, //many short delays
    '{1,1,0,100,0,1,0,0}, //only between transactions
    '{1,100,0,1000,1,100,0,1000} //few long delays
  };
  
  const pIbMonitorDelays parsMonD[] = '{
    '{0,1,0,0,0,1,0,0}, //no delays
    '{1,3,0,5,1,3,0,3}, //many short delays
    '{1,1,0,50,0,1,0,0}, //only between transactions
    '{1,100,0,1000,1,100,0,1000} //few long delays
  };
  
endpackage
