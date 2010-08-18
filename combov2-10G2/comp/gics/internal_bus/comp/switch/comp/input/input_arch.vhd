--
-- input_arch.vhd : IB Switch Input architecture
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

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION  --  IB Switch Input                --
-- ----------------------------------------------------------------------------

architecture ib_switch_input_arch of IB_SWITCH_INPUT is
  
begin

   -- -------------------------------------------------------------------------
   --                               PORT #0                                  --
   -- -------------------------------------------------------------------------

   U_ib_switch_input_port0: entity work.IB_SWITCH_INPUT_PORT
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- Port number (0/1/2)
      PORT_NUM     => 0,
      -- Port 1 Address Space
      PORT1_BASE   => PORT1_BASE, 
      PORT1_LIMIT  => PORT1_LIMIT,
      -- Port 2 Address Space
      PORT2_BASE   => PORT2_BASE, 
      PORT2_LIMIT  => PORT2_LIMIT
   )
   port map (
      -- Common interface -----------------------------------------------------
      CLK          => CLK,  
      RESET        => RESET,

      -- Input interface ------------------------------------------------------ 
      IN_DATA      => IN0_DATA,     
      IN_SOF_N     => IN0_SOF_N,    
      IN_EOF_N     => IN0_EOF_N,    
      IN_SRC_RDY_N => IN0_SRC_RDY_N,
      IN_DST_RDY_N => IN0_DST_RDY_N,
                   
      -- Output interface -----------------------------------------------------
      OUT_DATA     => OUT0_DATA,   
      OUT_SOF_N    => OUT0_SOF_N,  
      OUT_EOF_N    => OUT0_EOF_N,  
      OUT_WR       => OUT0_WR,     
      OUT_FULL     => OUT0_FULL,   
                                  
      OUT_REQ_VEC  => OUT0_REQ_VEC,
      OUT_REQ_WE   => OUT0_REQ_WE 
   );

   -- -------------------------------------------------------------------------
   --                               PORT #1                                  --
   -- -------------------------------------------------------------------------

   U_ib_switch_input_port1: entity work.IB_SWITCH_INPUT_PORT
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- Port number (0/1/2)
      PORT_NUM     => 1,
      -- Port 1 Address Space
      PORT1_BASE   => PORT1_BASE, 
      PORT1_LIMIT  => PORT1_LIMIT,
      -- Port 2 Address Space
      PORT2_BASE   => PORT2_BASE, 
      PORT2_LIMIT  => PORT2_LIMIT
   )
   port map (
      -- Common interface -----------------------------------------------------
      CLK          => CLK,  
      RESET        => RESET,

      -- Input interface ------------------------------------------------------ 
      IN_DATA      => IN1_DATA,     
      IN_SOF_N     => IN1_SOF_N,    
      IN_EOF_N     => IN1_EOF_N,    
      IN_SRC_RDY_N => IN1_SRC_RDY_N,
      IN_DST_RDY_N => IN1_DST_RDY_N,
                   
      -- Output interface -----------------------------------------------------
      OUT_DATA     => OUT1_DATA,   
      OUT_SOF_N    => OUT1_SOF_N,  
      OUT_EOF_N    => OUT1_EOF_N,  
      OUT_WR       => OUT1_WR,     
      OUT_FULL     => OUT1_FULL,   
                                  
      OUT_REQ_VEC  => OUT1_REQ_VEC,
      OUT_REQ_WE   => OUT1_REQ_WE 
   );   
 
   -- -------------------------------------------------------------------------
   --                               PORT #2                                  --
   -- -------------------------------------------------------------------------

   U_ib_switch_input_port2: entity work.IB_SWITCH_INPUT_PORT
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- Port number (0/1/2)
      PORT_NUM     => 2,
      -- Port 1 Address Space
      PORT1_BASE   => PORT1_BASE, 
      PORT1_LIMIT  => PORT1_LIMIT,
      -- Port 2 Address Space
      PORT2_BASE   => PORT2_BASE, 
      PORT2_LIMIT  => PORT2_LIMIT
   )
   port map (
      -- Common interface -----------------------------------------------------
      CLK          => CLK,  
      RESET        => RESET,

      -- Input interface ------------------------------------------------------ 
      IN_DATA      => IN2_DATA,     
      IN_SOF_N     => IN2_SOF_N,    
      IN_EOF_N     => IN2_EOF_N,    
      IN_SRC_RDY_N => IN2_SRC_RDY_N,
      IN_DST_RDY_N => IN2_DST_RDY_N,
                   
      -- Output interface -----------------------------------------------------
      OUT_DATA     => OUT2_DATA,   
      OUT_SOF_N    => OUT2_SOF_N,  
      OUT_EOF_N    => OUT2_EOF_N,  
      OUT_WR       => OUT2_WR,     
      OUT_FULL     => OUT2_FULL,   
                                  
      OUT_REQ_VEC  => OUT2_REQ_VEC,
      OUT_REQ_WE   => OUT2_REQ_WE 
   );   
   
end ib_switch_input_arch;   



