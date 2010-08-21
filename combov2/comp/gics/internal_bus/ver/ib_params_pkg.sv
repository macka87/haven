/*
 * ib_params_pkg.sv: Declaration of structs for internal bus test parameters 
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
 * $Id: ib_params_pkg.sv 12297 2009-12-16 18:17:27Z washek $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package ib_params_pkg;
   
  // -- Endpoint generics --
  typedef enum {CONTINUAL, PACKET} tReadType;
  typedef enum {SWITCH_SLAVE, SWITCH_MASTER, ROOT} tIbComp;
  
  typedef struct {
    int         DATA_WIDTH;
    int         ADDR_WIDTH;
    bit         BUS_MASTER_ENABLE;
    logic[31:0] ENDPOINT_BASE;
    logic[31:0] ENDPOINT_LIMIT;
    tIbComp     CONNECTED_TO;      // SWITCH_MASTER / SWITCH_SLAVE      
    bit         STRICT_ORDER;      // not implemented in endpoint yet
    bit         DATA_REORDER;      // not implemented in endpoint yet
    tReadType   READ_TYPE;         // CONTINUAL / PACKET
    int         READ_IN_PROCESS;
    int         INPUT_BUFFER_SIZE;
    int         OUTPUT_BUFFER_SIZE;
  } pIbEndpointGenerics;
  
  parameter pIbEndpointGenerics dIbEndpointGenerics = 
     '{64,32,0,32'h00000000,32'h00003000,SWITCH_MASTER,0,0,CONTINUAL,1, 0, 0};
  
  
  // -- Switch generics --
  typedef struct {
    bit          MASTER; //1-master; 0-slave
    int          DATA_WIDTH;
    int          HEADER_NUM;
    logic [31:0] PORT1_BASE;
    logic [31:0] PORT1_LIMIT;
    logic [31:0] PORT2_BASE;
    logic [31:0] PORT2_LIMIT;
  } pIbSwitchGenerics;
  
  parameter pIbSwitchGenerics dIbSwitchGenerics =
    '{1,64,1,32'h10000000,32'h10000000,32'h20000000,32'h20000000};
  
  
  // -- Transformer generics --
  typedef struct {
    int UP_DATA_WIDTH;
    int DOWN_DATA_WIDTH;
    int UP_INPUT_BUFFER_ITEMS;
    int DOWN_INPUT_BUFFER_ITEMS;
    bit UP_OUTPUT_PIPE;
    bit DOWN_OUTPUT_PIPE;
  } pIbTransformerGenerics;
  
  parameter pIbTransformerGenerics dIbTransformerGenerics = '{64,8,0,0,0,0};
  
  
  // -- Transaction parameters (constraints of random vars) --
  typedef struct {
    // Probabilities of transaction types
    int L2LW_WT;  // Local to Local Write
    int L2LR_WT;  // Local to Local Read
    int L2GW_WT;  // Local to Global Write
    int G2LR_WT;  // Global to Local Read
    int RDC_WT;   // Read completition (not last packet)
    int RDCL_WT;  // Read completition (last packet)
                
    logic [31:0] localAddrLow;
    logic [31:0] localAddrHigh;
    logic [63:0] globalAddrLow;
    logic [63:0] globalAddrHigh;
    logic [15:0] tagLow;
    logic [15:0] tagHigh;
    logic [12:0] lengthLow;
    logic [12:0] lengthHigh;
  } pIbTransaction;
  
  const pIbTransaction dIbTransaction = '{
    5,5,0,0,1,3,
    32'h00000000,32'h00010000,
    64'h0000000000001000,64'h0000000000003000,
    8'h00,8'hFF,
    13'h0001,13'h1000
  };
  
  
  // -- Driver delays --
  typedef struct {
    int outEnWt;    // Enable delays between transactions (weight)
    int outDisWt;   // Disable delays between transactions (weight)
    int outLow;     // Min delay between transactions
    int outHigh;    // Max delay between transactions
    int inEnWt;     // Enable delays inside transactions (weight)
    int inDisWt;    // Disable delays inside transactions (weight)
    int inLow;      // Min delay inside transactions
    int inHigh;     // Max delay inside transactions
  } pIbDriverDelays;
  
  const pIbDriverDelays dIbDriverDelays = '{1,3,0,5,1,3,0,3};
  
  // -- Driver delays --
  typedef struct {
    int outEnWt;    // Enable delays between transactions (weight)
    int outDisWt;   // Disable delays between transactions (weight)
    int outLow;     // Min delay between transactions
    int outHigh;    // Max delay between transactions
    int inEnWt;     // Enable delays inside transactions (weight)
    int inDisWt;    // Disable delays inside transactions (weight)
    int inLow;      // Min delay inside transactions
    int inHigh;     // Max delay inside transactions
  } pIbMonitorDelays;
  
  const pIbMonitorDelays dIbMonitorDelays = '{1,3,0,5,1,3,0,3};
  
  // -- Memory delays --
  typedef struct {
    int rdyEnWt;
    int rdyDisWt;
    int ardyEnWt;
    int ardyDisWt;
    int dataEnWt;
    int dataDisWt;
    int dataLow;
    int dataHigh;
  } pIbMemoryDelays;
  
  const pIbMemoryDelays dIbMemoryDelays = '{1,5,1,5,1,5,1,3};
  
endpackage

