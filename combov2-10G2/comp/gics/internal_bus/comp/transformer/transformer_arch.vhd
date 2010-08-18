--
-- transformer_arch.vhd : IB Transformer architecture
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
--              ARCHITECTURE DECLARATION  --  IB Transformer                 --
-- ----------------------------------------------------------------------------

architecture ib_transformer_arch of IB_TRANSFORMER is
  
begin
   
   -- Asserts -----------------------------------------------------------------
   assert UP_DATA_WIDTH =  2 or UP_DATA_WIDTH =  4 or UP_DATA_WIDTH =  8 or 
          UP_DATA_WIDTH = 16 or UP_DATA_WIDTH = 32 or UP_DATA_WIDTH = 64 or
          UP_DATA_WIDTH = 128
      report "UP_DATA_WIDTH must be one of {2,4,8,16,32,64,128}."
      severity error;
   
   assert DOWN_DATA_WIDTH = 1 or DOWN_DATA_WIDTH =  2 or DOWN_DATA_WIDTH =  4 or 
          DOWN_DATA_WIDTH = 8 or DOWN_DATA_WIDTH = 16 or DOWN_DATA_WIDTH = 32 or
          DOWN_DATA_WIDTH = 64
      report "DOWN_DATA_WIDTH must be one of {1,2,4,8,16,32,64}."
      severity error;
   
   assert DOWN_DATA_WIDTH < UP_DATA_WIDTH
      report "UP_DATA_WIDTH must be greater than DOWN_DATA_WIDTH."
      severity error;
   
   
   -- -------------------------------------------------------------------------
   --                           TRANSFORMER DOWN                             --
   -- ------------------------------------------------------------------------- 

   U_ib_transformer_down: entity work.IB_TRANSFORMER_DOWN
   generic map (
      -- Input Data Width (2-128)
      IN_DATA_WIDTH   => UP_DATA_WIDTH,
      -- Output Data Width (1-64)
      OUT_DATA_WIDTH  => DOWN_DATA_WIDTH,
      -- The length of input buffer (>=0)
      IN_BUFFER_ITEMS => UP_INPUT_BUFFER_ITEMS, 
      -- Output pipe enable
      OUT_PIPE        => DOWN_OUTPUT_PIPE 
   )   
   port map (
      -- Common interface ---------------------------------
      CLK             => CLK,
      RESET           => RESET,
      
      -- Input interface ----------------------------------
      IN_DATA         => UP_IN_DATA,     
      IN_SOF_N        => UP_IN_SOF_N,    
      IN_EOF_N        => UP_IN_EOF_N,    
      IN_SRC_RDY_N    => UP_IN_SRC_RDY_N,
      IN_DST_RDY_N    => UP_IN_DST_RDY_N,
 
      -- Output interface ---------------------------------
      OUT_DATA        => DOWN_OUT_DATA,     
      OUT_SOF_N       => DOWN_OUT_SOF_N,    
      OUT_EOF_N       => DOWN_OUT_EOF_N,    
      OUT_SRC_RDY_N   => DOWN_OUT_SRC_RDY_N,
      OUT_DST_RDY_N   => DOWN_OUT_DST_RDY_N
   );

   -- -------------------------------------------------------------------------
   --                           TRANSFORMER UP                               --
   -- ------------------------------------------------------------------------- 

   U_ib_transformer_up: entity work.IB_TRANSFORMER_UP
   generic map (
      -- Input Data Width (1-64)
      IN_DATA_WIDTH   => DOWN_DATA_WIDTH, 
      -- Output Data Width (2-128)
      OUT_DATA_WIDTH  => UP_DATA_WIDTH,
      -- The length of input buffer (>=0)
      IN_BUFFER_ITEMS => DOWN_INPUT_BUFFER_ITEMS,
      -- Output pipe enable
      OUT_PIPE        => UP_OUTPUT_PIPE
   )   
   port map (
      -- Common interface ---------------------------------
      CLK             => CLK,
      RESET           => RESET,
      
      -- Input interface ----------------------------------
      IN_DATA         => DOWN_IN_DATA,     
      IN_SOF_N        => DOWN_IN_SOF_N,    
      IN_EOF_N        => DOWN_IN_EOF_N,    
      IN_SRC_RDY_N    => DOWN_IN_SRC_RDY_N,
      IN_DST_RDY_N    => DOWN_IN_DST_RDY_N,
 
      -- Output interface ---------------------------------
      OUT_DATA        => UP_OUT_DATA,     
      OUT_SOF_N       => UP_OUT_SOF_N,    
      OUT_EOF_N       => UP_OUT_EOF_N,    
      OUT_SRC_RDY_N   => UP_OUT_SRC_RDY_N,
      OUT_DST_RDY_N   => UP_OUT_DST_RDY_N
   );
                                        
end ib_transformer_arch;  



