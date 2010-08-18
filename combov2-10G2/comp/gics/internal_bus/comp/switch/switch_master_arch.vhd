--
-- switch_master_arch.vhd : IB Master Switch architecture
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
--
-- $Id$
--
-- TODO:
--

library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION  --  IB Master Switch               --
-- ----------------------------------------------------------------------------

architecture ib_switch_master_arch of IB_SWITCH_MASTER is
  
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------   

   -- PORT 0 auxiliary signals ------------------------------------------------
   signal buf_in0_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal buf_in0_sof_n     : std_logic;
   signal buf_in0_eof_n     : std_logic;
   signal buf_in0_wr        : std_logic;
   signal buf_in0_full      : std_logic;
                       
   signal buf_in0_req_vec   : std_logic_vector(2 downto 0);
   signal buf_in0_req_we    : std_logic;                       
        
   signal buf_out0_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal buf_out0_data_vld : std_logic; 
   signal buf_out0_sof_n    : std_logic;
   signal buf_out0_eof_n    : std_logic;
   signal buf_out0_rd_vec   : std_logic_vector(2 downto 0);
                      
   signal buf_out0_req_vec  : std_logic_vector(2 downto 0);
   signal buf_out0_ack_vec  : std_logic_vector(2 downto 0);

   -- PORT 1 auxiliary signals ------------------------------------------------
   signal buf_in1_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal buf_in1_sof_n     : std_logic;
   signal buf_in1_eof_n     : std_logic;
   signal buf_in1_wr        : std_logic;
   signal buf_in1_full      : std_logic;
                       
   signal buf_in1_req_vec   : std_logic_vector(2 downto 0);
   signal buf_in1_req_we    : std_logic;
                               
   signal buf_out1_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal buf_out1_data_vld : std_logic; 
   signal buf_out1_sof_n    : std_logic;
   signal buf_out1_eof_n    : std_logic;
   signal buf_out1_rd_vec   : std_logic_vector(2 downto 0);
                      
   signal buf_out1_req_vec  : std_logic_vector(2 downto 0);
   signal buf_out1_ack_vec  : std_logic_vector(2 downto 0);

   -- PORT 2 auxiliary signals ------------------------------------------------
   signal buf_in2_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal buf_in2_sof_n     : std_logic;
   signal buf_in2_eof_n     : std_logic;
   signal buf_in2_wr        : std_logic;
   signal buf_in2_full      : std_logic;
                       
   signal buf_in2_req_vec   : std_logic_vector(2 downto 0);
   signal buf_in2_req_we    : std_logic;
                               
   signal buf_out2_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal buf_out2_data_vld : std_logic; 
   signal buf_out2_sof_n    : std_logic;
   signal buf_out2_eof_n    : std_logic;
   signal buf_out2_rd_vec   : std_logic_vector(2 downto 0);
                      
   signal buf_out2_req_vec  : std_logic_vector(2 downto 0);
   signal buf_out2_ack_vec  : std_logic_vector(2 downto 0);   
  
begin
   
   -- Asserts -----------------------------------------------------------------
   assert DATA_WIDTH =  8 or DATA_WIDTH = 16 or DATA_WIDTH = 32 or
          DATA_WIDTH = 64 or DATA_WIDTH = 128
      report "DATA_WIDTH must be one of {8,16,32,64,128}."
      severity error;
   
   assert HEADER_NUM > 0
      report "HEADER_NUM must be at least 1."
      severity error;
   
   -- Overlapping spaces - error  
   assert PORT1_BASE + PORT1_LIMIT <= PORT2_BASE or
          PORT2_BASE + PORT2_LIMIT <= PORT1_BASE
      report "Overlapping address spaces of down ports."
      severity error;
   
   -- Warning if some address space is empty
   assert PORT1_BASE + PORT1_LIMIT > PORT1_BASE
      report "Empty address space of port1. It can happen if PORT1_LIMIT is 0" &
             " or PORT1_BASE + PORT1_LIMIT is greater than max 32bit value."
      severity warning;
   
   assert PORT2_BASE + PORT2_LIMIT > PORT2_BASE
      report "Empty address space of port2. It can happen if PORT2_LIMIT is 0" &
             " or PORT2_BASE + PORT2_LIMIT is greater than max 32bit value."
      severity warning;
   
   -- -------------------------------------------------------------------------
   --                              INPUT logic                               --
   -- ------------------------------------------------------------------------- 

   U_ib_switch_input: entity work.IB_SWITCH_INPUT
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH    => DATA_WIDTH,
      -- Port 1 Address Space
      PORT1_BASE    => PORT1_BASE,
      PORT1_LIMIT   => PORT1_LIMIT,
      -- Port 2 Address Space
      PORT2_BASE    => PORT2_BASE,
      PORT2_LIMIT   => PORT2_LIMIT
   ) 
   port map (
      -- Common interface -----------------------------------------------------
      CLK           => CLK,
      RESET         => RESET,

      -- Upstream Port #0 -----------------------------------------------------
      -- input ifc --            
      IN0_DATA      => PORT0_DOWN_DATA,     
      IN0_SOF_N     => PORT0_DOWN_SOF_N,    
      IN0_EOF_N     => PORT0_DOWN_EOF_N,    
      IN0_SRC_RDY_N => PORT0_DOWN_SRC_RDY_N,
      IN0_DST_RDY_N => PORT0_DOWN_DST_RDY_N,

      -- output ifc --
      OUT0_DATA     => buf_in0_data,
      OUT0_SOF_N    => buf_in0_sof_n,
      OUT0_EOF_N    => buf_in0_eof_n,
      OUT0_WR       => buf_in0_wr,
      OUT0_FULL     => buf_in0_full,
                                        
      OUT0_REQ_VEC  => buf_in0_req_vec,
      OUT0_REQ_WE   => buf_in0_req_we,

      -- Downstream Port #1 ---------------------------------------------------
      -- input ifc --            
      IN1_DATA      => PORT1_UP_DATA,     
      IN1_SOF_N     => PORT1_UP_SOF_N,    
      IN1_EOF_N     => PORT1_UP_EOF_N,    
      IN1_SRC_RDY_N => PORT1_UP_SRC_RDY_N,
      IN1_DST_RDY_N => PORT1_UP_DST_RDY_N,
        
      -- output ifc --
      OUT1_DATA     => buf_in1_data,
      OUT1_SOF_N    => buf_in1_sof_n,
      OUT1_EOF_N    => buf_in1_eof_n,
      OUT1_WR       => buf_in1_wr,
      OUT1_FULL     => buf_in1_full,
                                        
      OUT1_REQ_VEC  => buf_in1_req_vec,
      OUT1_REQ_WE   => buf_in1_req_we,
      
      -- Downstream Port #2 ---------------------------------------------------
      -- input ifc --            
      IN2_DATA      => PORT2_UP_DATA,     
      IN2_SOF_N     => PORT2_UP_SOF_N,    
      IN2_EOF_N     => PORT2_UP_EOF_N,    
      IN2_SRC_RDY_N => PORT2_UP_SRC_RDY_N,
      IN2_DST_RDY_N => PORT2_UP_DST_RDY_N,

      -- output ifc --
      OUT2_DATA     => buf_in2_data,
      OUT2_SOF_N    => buf_in2_sof_n,
      OUT2_EOF_N    => buf_in2_eof_n,
      OUT2_WR       => buf_in2_wr,
      OUT2_FULL     => buf_in2_full,
                                        
      OUT2_REQ_VEC  => buf_in2_req_vec,
      OUT2_REQ_WE   => buf_in2_req_we
   );

   -- -------------------------------------------------------------------------
   --                                BUFFER                                  --
   -- -------------------------------------------------------------------------   

   U_ib_switch_buffer: entity work.IB_SWITCH_BUFFER
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH    => DATA_WIDTH,  
      -- The number of headers to be stored
      HEADER_NUM    => HEADER_NUM
   ) 
   port map (
      -- Common interface -----------------------------------------------------
      CLK           => CLK,
      RESET         => RESET,

      -- Upstream Port #0 -----------------------------------------------------
      -- input ifc --            
      IN0_DATA      => buf_in0_data,
      IN0_SOF_N     => buf_in0_sof_n,
      IN0_EOF_N     => buf_in0_eof_n,
      IN0_WR        => buf_in0_wr,
      IN0_FULL      => buf_in0_full,

      IN0_REQ_VEC   => buf_in0_req_vec,
      IN0_REQ_WE    => buf_in0_req_we,

      -- output ifc --      
      OUT0_DATA     => buf_out0_data,
      OUT0_DATA_VLD => buf_out0_data_vld,
      OUT0_SOF_N    => buf_out0_sof_n,
      OUT0_EOF_N    => buf_out0_eof_n,
      OUT0_RD_VEC   => buf_out0_rd_vec,
                                          
      OUT0_REQ_VEC  => buf_out0_req_vec,
      OUT0_ACK_VEC  => buf_out0_ack_vec,

      -- Downstream Port #1 ---------------------------------------------------
      IN1_DATA      => buf_in1_data,
      IN1_SOF_N     => buf_in1_sof_n,
      IN1_EOF_N     => buf_in1_eof_n,
      IN1_WR        => buf_in1_wr,
      IN1_FULL      => buf_in1_full,
                                        
      IN1_REQ_VEC   => buf_in1_req_vec,
      IN1_REQ_WE    => buf_in1_req_we,

      -- output ifc --      
      OUT1_DATA     => buf_out1_data,
      OUT1_DATA_VLD => buf_out1_data_vld,
      OUT1_SOF_N    => buf_out1_sof_n,
      OUT1_EOF_N    => buf_out1_eof_n,
      OUT1_RD_VEC   => buf_out1_rd_vec,
                                          
      OUT1_REQ_VEC  => buf_out1_req_vec,
      OUT1_ACK_VEC  => buf_out1_ack_vec,
      
      -- Downstream Port #2 ---------------------------------------------------
      IN2_DATA      => buf_in2_data,
      IN2_SOF_N     => buf_in2_sof_n,
      IN2_EOF_N     => buf_in2_eof_n,
      IN2_WR        => buf_in2_wr,
      IN2_FULL      => buf_in2_full,
                                        
      IN2_REQ_VEC   => buf_in2_req_vec,
      IN2_REQ_WE    => buf_in2_req_we,

      -- output ifc --      
      OUT2_DATA     => buf_out2_data,
      OUT2_DATA_VLD => buf_out2_data_vld,
      OUT2_SOF_N    => buf_out2_sof_n,
      OUT2_EOF_N    => buf_out2_eof_n,
      OUT2_RD_VEC   => buf_out2_rd_vec,
                                          
      OUT2_REQ_VEC  => buf_out2_req_vec,
      OUT2_ACK_VEC  => buf_out2_ack_vec
   );

   -- -------------------------------------------------------------------------
   --                             OUTPUT logic                               --
   -- -------------------------------------------------------------------------

   U_ib_switch_output: entity work.IB_SWITCH_OUTPUT
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH     => DATA_WIDTH
   )                
   port map (
      -- Common interface -----------------------------------------------------
      CLK            => CLK,
      RESET          => RESET,

      -- Upstream Port #0 -----------------------------------------------------
      -- input ifc --
      IN0_DATA       => buf_out0_data,
      IN0_DATA_VLD   => buf_out0_data_vld,
      IN0_SOF_N      => buf_out0_sof_n,
      IN0_EOF_N      => buf_out0_eof_n,
      IN0_RD_VEC     => buf_out0_rd_vec,
                     
      IN0_REQ_VEC    => buf_out0_req_vec,
      IN0_ACK_VEC    => buf_out0_ack_vec,

      -- output ifc --
      OUT0_DATA      => PORT0_UP_DATA,     
      OUT0_SOF_N     => PORT0_UP_SOF_N,    
      OUT0_EOF_N     => PORT0_UP_EOF_N,    
      OUT0_SRC_RDY_N => PORT0_UP_SRC_RDY_N,
      OUT0_DST_RDY_N => PORT0_UP_DST_RDY_N,

      -- Downstream Port #1 ---------------------------------------------------
      -- input ifc --      
      IN1_DATA       => buf_out1_data,
      IN1_DATA_VLD   => buf_out1_data_vld,
      IN1_SOF_N      => buf_out1_sof_n,
      IN1_EOF_N      => buf_out1_eof_n,
      IN1_RD_VEC     => buf_out1_rd_vec,
                                           
      IN1_REQ_VEC    => buf_out1_req_vec,
      IN1_ACK_VEC    => buf_out1_ack_vec,
 
      -- output ifc --
      OUT1_DATA      => PORT1_DOWN_DATA,     
      OUT1_SOF_N     => PORT1_DOWN_SOF_N,    
      OUT1_EOF_N     => PORT1_DOWN_EOF_N,    
      OUT1_SRC_RDY_N => PORT1_DOWN_SRC_RDY_N,
      OUT1_DST_RDY_N => PORT1_DOWN_DST_RDY_N,
 
      -- Downstream Port #2 ---------------------------------------------------
      -- input ifc --      
      IN2_DATA       => buf_out2_data,
      IN2_DATA_VLD   => buf_out2_data_vld,
      IN2_SOF_N      => buf_out2_sof_n,
      IN2_EOF_N      => buf_out2_eof_n,
      IN2_RD_VEC     => buf_out2_rd_vec,
                                           
      IN2_REQ_VEC    => buf_out2_req_vec,
      IN2_ACK_VEC    => buf_out2_ack_vec,

      -- output ifc --
      OUT2_DATA      => PORT2_DOWN_DATA,     
      OUT2_SOF_N     => PORT2_DOWN_SOF_N,    
      OUT2_EOF_N     => PORT2_DOWN_EOF_N,    
      OUT2_SRC_RDY_N => PORT2_DOWN_SRC_RDY_N,
      OUT2_DST_RDY_N => PORT2_DOWN_DST_RDY_N
   );
                                  
end ib_switch_master_arch;                   



