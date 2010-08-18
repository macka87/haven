-- top_level.vhd: SP_BMEM toplevel for synthesis
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobierský <xkobie00@liberouter.org>
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
--
library IEEE;
use IEEE.std_logic_1164.all;
use work.math_pack.all; -- FrameLink package


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity SP_BMEM_TOP is
   port(
      -- Common interface
      RESET  : in    std_logic; -- Reset only if output_reg

      -- Interface A
      CLK   : in    std_logic; -- Clock A
      PIPE_EN : in  std_logic; -- Pipe Enable
      RE    : in    std_logic; -- Read Enable
      WE    : in    std_logic; -- Write Enable
      ADDR  : in    std_logic_vector(11-1 downto 0); -- Address A
      DI    : in    std_logic_vector(72-1 downto 0); -- Data A In
      DO_DV : out   std_logic; -- Data A Valid
      DO    : out   std_logic_vector(72-1 downto 0) -- Data A Out
   );
end entity SP_BMEM_TOP;

ARCHITECTURE synth OF SP_BMEM_top IS
   begin
   uut: entity work.SP_BMEM
   generic map(
      DATA_WIDTH  => 72,
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS       => 2048,
      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      BRAM_TYPE   => 18,
      -- Output directly from BlockRams or throw register
      -- TRUE, FALSE, AUTO (when column count > 1 then true)
      OUTPUT_REG  => true,
      -- debug prints
      DEBUG       => false
   )

   port map(
      -- Common interface
      RESET    => RESET,

      -- Interface A
      CLK     => CLK,
      PIPE_EN => PIPE_EN,
      RE      => RE,
      WE      => WE,
      ADDR    => ADDR,
      DI      => DI,
      DO_DV   => DO_DV,
      DO      => DO
   );
end;
