-- top_level.vhd: DP_BMEM toplevel for synthesis
-- Copyright (C) 2007 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
entity DP_BMEM_TOP is
   port(
      -- Common interface
      RESET  : in    std_logic; -- Reset only if output_reg

      -- Interface A
      CLKA   : in    std_logic; -- Clock A
      PIPE_ENA : in  std_logic; -- Pipe Enable
      REA    : in    std_logic; -- Read Enable
      WEA    : in    std_logic; -- Write Enable
      ADDRA  : in    std_logic_vector(11-1 downto 0); -- Address A
      DIA    : in    std_logic_vector(72-1 downto 0); -- Data A In
      DOA_DV : out   std_logic; -- Data A Valid
      DOA    : out   std_logic_vector(72-1 downto 0); -- Data A Out

      -- Interface B
      CLKB   : in    std_logic; -- Clock B
      PIPE_ENB : in  std_logic; -- Pipe Enable
      REB    : in    std_logic; -- Read Enable
      WEB    : in    std_logic; -- Write Enable
      ADDRB  : in    std_logic_vector(11-1 downto 0); -- Address B
      DIB    : in    std_logic_vector(72-1 downto 0); -- Data B In
      DOB_DV : out   std_logic; -- Data B Valid
      DOB    : out   std_logic_vector(72-1 downto 0) -- Data B Out
   );
end entity DP_BMEM_TOP;

ARCHITECTURE synth OF dp_bmem_top IS
   begin
   uut: entity work.dp_bmem
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
      CLKA     => CLKA,
      PIPE_ENA => PIPE_ENA,
      REA      => REA,
      WEA      => WEA,
      ADDRA    => ADDRA,
      DIA      => DIA,
      DOA_DV   => DOA_DV,
      DOA      => DOA,

      -- Interface B
      CLKB     => CLKB,
      PIPE_ENB => PIPE_ENB,
      REB      => REB,
      WEB      => WEB,
      ADDRB    => ADDRB,
      DIB      => DIB,
      DOB_DV   => DOB_DV,
      DOB      => DOB
   );
end;
