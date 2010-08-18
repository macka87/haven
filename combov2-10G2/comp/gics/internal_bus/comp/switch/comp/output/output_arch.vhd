--
-- output_arch.vhd : IB Switch Output architecture
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

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION  --  IB Switch Output               --
-- ----------------------------------------------------------------------------

architecture ib_switch_output_arch of IB_SWITCH_OUTPUT is
  
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------   

   -- PORT 0 (UP) -------------------------------------------------------------

   -- PORT 1 (DOWN) -----------------------------------------------------------

   -- PORT 2 (DOWN) -----------------------------------------------------------
 
begin

   -- -------------------------------------------------------------------------
   --                             PORT 0 (UP)                                --
   -- -------------------------------------------------------------------------

   U_ib_switch_output_port0: entity work.IB_SWITCH_OUTPUT_PORT
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH     => DATA_WIDTH,
      -- Port number (0/1/2)
      PORT_NUM       => 0
   ) 
   port map (
      -- Common interface -----------------------------------------------------
      CLK            => CLK,  
      RESET          => RESET,

      -- Upstream Port #0 -----------------------------------------------------
      IN0_DATA       => IN0_DATA,    
      IN0_DATA_VLD   => IN0_DATA_VLD,
      IN0_SOF_N      => IN0_SOF_N,   
      IN0_EOF_N      => IN0_EOF_N,   
      IN0_RD         => IN0_RD_VEC(0),      
                     
      IN0_REQ        => IN0_REQ_VEC(0),
      IN0_ACK        => IN0_ACK_VEC(0),

      -- Downstream Port #1 ---------------------------------------------------
      IN1_DATA       => IN1_DATA,    
      IN1_DATA_VLD   => IN1_DATA_VLD,
      IN1_SOF_N      => IN1_SOF_N,   
      IN1_EOF_N      => IN1_EOF_N,   
      IN1_RD         => IN1_RD_VEC(0),      
                     
      IN1_REQ        => IN1_REQ_VEC(0),
      IN1_ACK        => IN1_ACK_VEC(0),
 
      -- Downstream Port #2 ---------------------------------------------------
      IN2_DATA       => IN2_DATA,    
      IN2_DATA_VLD   => IN2_DATA_VLD,
      IN2_SOF_N      => IN2_SOF_N,   
      IN2_EOF_N      => IN2_EOF_N,   
      IN2_RD         => IN2_RD_VEC(0),      
                                    
      IN2_REQ        => IN2_REQ_VEC(0), 
      IN2_ACK        => IN2_ACK_VEC(0), 

      -- OUTPUT Port ----------------------------------------------------------
      OUT_DATA       => OUT0_DATA,     
      OUT_SOF_N      => OUT0_SOF_N,    
      OUT_EOF_N      => OUT0_EOF_N,    
      OUT_SRC_RDY_N  => OUT0_SRC_RDY_N,
      OUT_DST_RDY_N  => OUT0_DST_RDY_N
   );

   -- -------------------------------------------------------------------------
   --                            PORT 1 (DOWN)                               --
   -- -------------------------------------------------------------------------

   U_ib_switch_output_port1: entity work.IB_SWITCH_OUTPUT_PORT
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH     => DATA_WIDTH,
      -- Port number (0/1/2)
      PORT_NUM       => 1
   ) 
   port map (
      -- Common interface -----------------------------------------------------
      CLK            => CLK,  
      RESET          => RESET,

      -- Upstream Port #0 -----------------------------------------------------
      IN0_DATA       => IN0_DATA,    
      IN0_DATA_VLD   => IN0_DATA_VLD,
      IN0_SOF_N      => IN0_SOF_N,   
      IN0_EOF_N      => IN0_EOF_N,   
      IN0_RD         => IN0_RD_VEC(1),      
                     
      IN0_REQ        => IN0_REQ_VEC(1),
      IN0_ACK        => IN0_ACK_VEC(1),

      -- Downstream Port #1 ---------------------------------------------------
      IN1_DATA       => IN1_DATA,    
      IN1_DATA_VLD   => IN1_DATA_VLD,
      IN1_SOF_N      => IN1_SOF_N,   
      IN1_EOF_N      => IN1_EOF_N,   
      IN1_RD         => IN1_RD_VEC(1),      
                     
      IN1_REQ        => IN1_REQ_VEC(1),
      IN1_ACK        => IN1_ACK_VEC(1),
 
      -- Downstream Port #2 ---------------------------------------------------
      IN2_DATA       => IN2_DATA,    
      IN2_DATA_VLD   => IN2_DATA_VLD,
      IN2_SOF_N      => IN2_SOF_N,   
      IN2_EOF_N      => IN2_EOF_N,   
      IN2_RD         => IN2_RD_VEC(1),      
                                    
      IN2_REQ        => IN2_REQ_VEC(1), 
      IN2_ACK        => IN2_ACK_VEC(1), 

      -- OUTPUT Port ----------------------------------------------------------
      OUT_DATA       => OUT1_DATA,     
      OUT_SOF_N      => OUT1_SOF_N,    
      OUT_EOF_N      => OUT1_EOF_N,    
      OUT_SRC_RDY_N  => OUT1_SRC_RDY_N,
      OUT_DST_RDY_N  => OUT1_DST_RDY_N
   );

   -- -------------------------------------------------------------------------
   --                            PORT 2 (DOWN)                               --
   -- -------------------------------------------------------------------------   

   U_ib_switch_output_port2: entity work.IB_SWITCH_OUTPUT_PORT
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH     => DATA_WIDTH,
      -- Port number (0/1/2)
      PORT_NUM       => 2
   ) 
   port map(
      -- Common interface -----------------------------------------------------
      CLK            => CLK,  
      RESET          => RESET,

      -- Upstream Port #0 -----------------------------------------------------
      IN0_DATA       => IN0_DATA,    
      IN0_DATA_VLD   => IN0_DATA_VLD,
      IN0_SOF_N      => IN0_SOF_N,   
      IN0_EOF_N      => IN0_EOF_N,   
      IN0_RD         => IN0_RD_VEC(2),      
                     
      IN0_REQ        => IN0_REQ_VEC(2),
      IN0_ACK        => IN0_ACK_VEC(2),

      -- Downstream Port #1 ---------------------------------------------------
      IN1_DATA       => IN1_DATA,    
      IN1_DATA_VLD   => IN1_DATA_VLD,
      IN1_SOF_N      => IN1_SOF_N,   
      IN1_EOF_N      => IN1_EOF_N,   
      IN1_RD         => IN1_RD_VEC(2),      
                     
      IN1_REQ        => IN1_REQ_VEC(2),
      IN1_ACK        => IN1_ACK_VEC(2),
 
      -- Downstream Port #2 ---------------------------------------------------
      IN2_DATA       => IN2_DATA,    
      IN2_DATA_VLD   => IN2_DATA_VLD,
      IN2_SOF_N      => IN2_SOF_N,   
      IN2_EOF_N      => IN2_EOF_N,   
      IN2_RD         => IN2_RD_VEC(2),      
                                    
      IN2_REQ        => IN2_REQ_VEC(2), 
      IN2_ACK        => IN2_ACK_VEC(2), 

      -- OUTPUT Port ----------------------------------------------------------
      OUT_DATA       => OUT2_DATA,     
      OUT_SOF_N      => OUT2_SOF_N,    
      OUT_EOF_N      => OUT2_EOF_N,    
      OUT_SRC_RDY_N  => OUT2_SRC_RDY_N,
      OUT_DST_RDY_N  => OUT2_DST_RDY_N
   );   

end ib_switch_output_arch;   



