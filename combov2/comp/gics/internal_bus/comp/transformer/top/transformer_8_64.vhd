--
-- transformer_8_64.vhd : Internal Bus Transformer (8 bits <-> 64 bits)
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

use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_transformer_pkg.all; 

-- ----------------------------------------------------------------------------
--     ENTITY DECLARATION -- Internal Bus Transformer (8 bits <-> 64 bits)   -- 
-- ----------------------------------------------------------------------------

entity IB_TRANSFORMER_8_64 is
   generic(
      -- The length of upstream input buffer (>=0)
      UP_INPUT_BUFFER_ITEMS   : integer :=  0;
      -- The length of downstream input buffer (>=0)
      DOWN_INPUT_BUFFER_ITEMS : integer :=  0;      
      -- Upstream output pipe enable
      UP_OUTPUT_PIPE          : boolean := false;
      -- Downstream output pipe enable
      DOWN_OUTPUT_PIPE        : boolean := false      
   ); 
   port(
      -- Common interface -----------------------------------------------------   
      CLK   : in std_logic; -- FPGA clock
      RESET : in std_logic; -- Reset active high 
      
      -- Transformer Ports ----------------------------------------------------
      UP    : inout t_ib64; -- Upstream port  
      DOWN  : inout t_ib8   -- Downstream port
   );
end entity IB_TRANSFORMER_8_64;

-- ----------------------------------------------------------------------------
-- ARCHITECTURE DECLARATION -- Internal Bus Transformer (8 bits <-> 64 bits) --
-- ----------------------------------------------------------------------------

architecture ib_transformer_8_64_arch of IB_TRANSFORMER_8_64 is

begin

   U_transformer: entity work.IB_TRANSFORMER
   generic map (
      -- Upstream Data Width (2-128)
      UP_DATA_WIDTH           => 64,
      -- Downstream Data Width (1-64)
      DOWN_DATA_WIDTH         =>  8,
      -- The length of upstream input buffer (>=0)
      UP_INPUT_BUFFER_ITEMS   => UP_INPUT_BUFFER_ITEMS,
      -- The length of downstream input buffer (>=0)
      DOWN_INPUT_BUFFER_ITEMS => DOWN_INPUT_BUFFER_ITEMS,
      -- Upstream output pipe enable
      UP_OUTPUT_PIPE          => UP_OUTPUT_PIPE,
      -- Downstream output pipe enable
      DOWN_OUTPUT_PIPE        => DOWN_OUTPUT_PIPE
   ) 
   port map (
      -- Common interface -----------------------------------------------------
      CLK                => CLK,
      RESET              => RESET,
      
      -- Upstream Port --------------------------------------------------------
      UP_IN_DATA         => UP.DOWN.DATA,      
      UP_IN_SOF_N        => UP.DOWN.SOF_N,     
      UP_IN_EOF_N        => UP.DOWN.EOF_N,     
      UP_IN_SRC_RDY_N    => UP.DOWN.SRC_RDY_N, 
      UP_IN_DST_RDY_N    => UP.DOWN.DST_RDY_N, 
                            
      UP_OUT_DATA        => UP.UP.DATA,     
      UP_OUT_SOF_N       => UP.UP.SOF_N,    
      UP_OUT_EOF_N       => UP.UP.EOF_N,    
      UP_OUT_SRC_RDY_N   => UP.UP.SRC_RDY_N,
      UP_OUT_DST_RDY_N   => UP.UP.DST_RDY_N,

      -- Downstream Port ------------------------------------------------------
      DOWN_OUT_DATA      => DOWN.DOWN.DATA,     
      DOWN_OUT_SOF_N     => DOWN.DOWN.SOF_N,    
      DOWN_OUT_EOF_N     => DOWN.DOWN.EOF_N,    
      DOWN_OUT_SRC_RDY_N => DOWN.DOWN.SRC_RDY_N,
      DOWN_OUT_DST_RDY_N => DOWN.DOWN.DST_RDY_N,
                            
      DOWN_IN_DATA       => DOWN.UP.DATA,      
      DOWN_IN_SOF_N      => DOWN.UP.SOF_N,     
      DOWN_IN_EOF_N      => DOWN.UP.EOF_N,     
      DOWN_IN_SRC_RDY_N  => DOWN.UP.SRC_RDY_N, 
      DOWN_IN_DST_RDY_N  => DOWN.UP.DST_RDY_N 
   );
              
end ib_transformer_8_64_arch;

                     

