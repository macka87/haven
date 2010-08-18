/*
 * params.sv: Parameters of ib_endpoint test
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
 * $Id: params.sv 14139 2010-06-23 08:50:28Z washek $
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
  const int SEED = 121;
  
  // Maximum number of transactions sent in one test
  const int TRANSACTION_COUNT = 10000;
  
  // Test of EP2MI converter
  parameter bit MI_TEST = 0;
  
  // Clock and Reset constants
  const time CLK_PERIOD = 10ns;
  const time RESET_TIME = 10*CLK_PERIOD;
   
  //--------------------------- Endpoint generics -----------------------------
  parameter pIbEndpointGenerics G = '{
    /* DATA_WIDTH         */ 32,
    /* ADDR_WIDTH         */ 32,
    /* BUS_MASTER_ENABLE  */ 0,
    /* ENDPOINT_BASE      */ 32'h00000000,
    /* ENDPOINT_LIMIT     */ 32'h02000000,
    /* CONNECTED_TO       */ SWITCH_MASTER,
    /* STRICT_ORDER       */ 1,
    /* DATA_REORDER       */ 0,
    /* READ_TYPE          */ CONTINUAL,
    /* READ_IN_PROCESS    */ 1,
    /* INPUT_BUFFER_SIZE  */ 2,
    /* OUTPUT_BUFFER_SIZE */ 2
  };
  
  
  //--------------------------- Parameter lists -------------------------------
  
  const bit BM = G.BUS_MASTER_ENABLE;
  
  //-- Transaction parameters --

  const pIbTransaction parsTransIB[] = '{
    '{5,5,0,0,1*BM,3*BM,32'h00000000,32'h00010000,
      64'h0000000000001000,64'h0000000000003000,8'h00,8'hFF,13'h0001,13'h1000},
    '{1,0,0,0,0*BM,0*BM,32'h00000000,32'h00010000,
      64'h0000000000001000,64'h0000000000003000,8'h00,8'hFF,13'h0001,13'h1000},
    '{0,2,0,0,1*BM,1*BM,32'h00000000,32'h00010000,
      64'h0000000000001000,64'h0000000000003000,8'h00,8'hFF,13'h0001,13'h1000},
    '{5,5,0,0,1*BM,3*BM,32'h00000000,32'h00010000,
      64'h0000000000001000,64'h0000000000003000,8'h00,8'hFF,13'h0001,13'h0050}
  };
  
  const pIbTransaction parsTransBM[] = '{
    '{2,1,2,1,0,0,32'h00001000,32'h00003000,
      64'h0000000000000000,64'h0000000000010000,8'h00,8'hFF,13'h0001,13'h1000},
    '{1,1,0,0,0,0,32'h00001000,32'h00003000,
      64'h0000000000000000,64'h0000000000010000,8'h00,8'hFF,13'h0001,13'h1000},
    '{0,0,1,1,0,0,32'h00001000,32'h00003000,
      64'h0000000000000000,64'h0000000000010000,8'h00,8'hFF,13'h0001,13'h1000},
    '{1,0,1,0,0,0,32'h00001000,32'h00003000,
      64'h0000000000000000,64'h0000000000010000,8'h00,8'hFF,13'h0001,13'h1000},
    '{0,1,0,1,0,0,32'h00001000,32'h00003000,
      64'h0000000000000000,64'h0000000000010000,8'h00,8'hFF,13'h0001,13'h1000}
  };
  
  
  //-- Delays --
  
  const pIbDriverDelays parsDrvD[] = '{
    '{0,1,0,0,0,1,0,0}, //no delays
    '{1,1,0,100,0,1,0,0}, //only between transactions
    '{1,3,0,5,1,3,0,3}, //many short delays
    '{1,100,0,1000,1,100,0,1000} //few long delays
  };
  
  const pIbMonitorDelays parsMonD[] = '{
    '{0,1,0,0,0,1,0,0}, //no delays
    '{1,3,0,5,1,3,0,3}, //many short delays
    '{1,1,0,100,0,1,0,0}, //only between transactions
    '{1,100,0,1000,1,100,0,1000} //few long delays
  };
  
  const pIbDriverDelays parsDrvBmD[] = '{
    '{0,1,0,0,0,1,0,0}, //no delays
    '{3,1,0,10,1,3,0,3}, //short delays
    '{1,1,0,100,0,1,0,0}, //only between transactions
    '{1,1,0,1000,1,1,0,1000} //long delays
  };
  
  const pIbMemoryDelays parsMemD[] = '{
    '{0,1,0,1,0,1,0,0}, //always ready, no delays on DATA
    '{0,1,0,1,1,3,0,5}, //always ready, short delays on DATA
    '{1,4,1,4,1,5,1,3}, //normal RDYs
    '{1,2,1,2,1,20,0,100} //sometimes not ready, few long delays on DATA
  };
  
endpackage
