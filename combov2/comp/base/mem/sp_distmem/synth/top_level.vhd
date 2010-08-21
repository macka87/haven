-- top_level.vhd: DP_BMEM toplevel for synthesis
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
entity SP_DISTMEM_TOP is
   port(
      -- Common interface
      RESET  : in    std_logic; -- Reset only if output_reg

      -- R/W Port
      DI     : in std_logic_vector(64-1 downto 0);
      WE     : in std_logic;
      WCLK   : in std_logic;
      ADDR   : in std_logic_vector (5-1 downto 0);
      DO     : out std_logic_vector(64-1 downto 0)
   );
end entity SP_DISTMEM_TOP;

ARCHITECTURE synth OF SP_DISTMEM_top IS
   begin
   uut: entity work.SP_DISTMEM
   generic map(
      -- Data Width
      DATA_WIDTH   => 64,
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS        => 32,
      -- Distributed Ram Type(capacity) only 16, 32, 64 bits
      DISTMEM_TYPE => 32
   )

   port map(
      -- Common interface
      RESET    => RESET,

      -- R/W Port
      DI       => DI,
      WE       => WE,
      WCLK     => WCLK,
      ADDR     => ADDR,
      DO       => DO
   );
end;
