/*
 * params.sv: Parameters of ib_transformer test
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
 * $Id: params.sv 8657 2009-06-04 10:57:57Z washek $
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
  const int SEED = 5;
  
  // Maximum number of transactions sent in one test
  const int TRANSACTION_COUNT = 5000;
  
  // Clock and Reset constants
  const time CLK_PERIOD = 10ns;
  const time RESET_TIME = 10*CLK_PERIOD;
   
  //--------------------------- Transformer generics --------------------------
  parameter pIbTransformerGenerics G = '{
    /* UP_DATA_WIDTH           */ 64,
    /* DOWN_DATA_WIDTH         */ 8,
    /* UP_INPUT_BUFFER_ITEMS   */ 0,
    /* DOWN_INPUT_BUFFER_ITEMS */ 0,
    /* UP_OUTPUT_PIPE          */ 0,
    /* DOWN_OUTPUT_PIPE        */ 0
  };
  
  
  //--------------------------- Parameter lists -------------------------------
  
  //-- Transaction parameters --

  const pIbTransaction parsTransUp[] = '{
    '{1,1,1,1,1,1,32'h00000000,32'hFFFFFFFF,
      64'h0000000000000000,64'hFFFFFFFFFFFFFFFF,8'h00,8'hFF,13'h0001,13'h1000}
  };
  
  const pIbTransaction parsTransDown[] = parsTransUp;
  
  
  //-- Delays --
  
  const pIbDriverDelays parsDrvD[] = '{
    '{1,3,0,5,1,3,0,3}, //many short delays
    '{0,1,0,0,0,1,0,0}, //no delays
    '{1,1,0,100,0,1,0,0}, //only between transactions
    '{1,100,0,1000,1,100,0,1000} //few long delays
  };
  
  const pIbMonitorDelays parsMonD[] = '{
    '{1,3,0,5,1,3,0,3}, //many short delays
    '{0,1,0,0,0,1,0,0}, //no delays
    '{1,1,0,100,0,1,0,0}, //only between transactions
    '{1,100,0,1000,1,100,0,1000} //few long delays
  };
  
endpackage
