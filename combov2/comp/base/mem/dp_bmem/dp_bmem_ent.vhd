--
-- dp_bmem_ent.vhd: Dual port generic memory composed from Block Rams - entity 
-- declaration
-- Copyright (C) 2004 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
-- auxilarity functions and constant needed to evaluate generic address etc.
use WORK.math_pack.all;
use WORK.bmem_func.all;

-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity DP_BMEM is
   -- Capacity of 1, 2, 4 Block rams is 16384 bits
   -- Capacity of 9, 18, 36 Block rams is 18432 bits
   generic(
      DATA_WIDTH     : integer := 32;
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS          : integer := 1024;
      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      BRAM_TYPE      : integer := 4;
      -- What operation will be performed first when both WE and RE are
      -- active? Only for behavioral simulation purpose.
      -- WRITE_FIRST(default) | READ_FIRST | NO_CHANGE
      WRITE_MODE_A   : string := "WRITE_FIRST";
      WRITE_MODE_B   : string := "WRITE_FIRST";
      -- Output directly from BlockRams or throw register
      -- TRUE, FALSE, AUTO (when column count > 1 then true)
      OUTPUT_REG     : TOUTPUT_REG := auto;
      -- debug prints
      DEBUG          : boolean := false
   );

   port(
      -- Common interface
      RESET  : in    std_logic; -- Reset only if output_reg

      -- Interface A
      CLKA   : in    std_logic; -- Clock A
      PIPE_ENA : in  std_logic; -- Pipe Enable
      REA    : in    std_logic; -- Read Enable
      WEA    : in    std_logic; -- Write Enable
      ADDRA  : in    std_logic_vector(LOG2(ITEMS)-1 downto 0); -- Address A
      DIA    : in    std_logic_vector(DATA_WIDTH-1 downto 0); -- Data A In
      DOA_DV : out   std_logic; -- Data A Valid
      DOA    : out   std_logic_vector(DATA_WIDTH-1 downto 0); -- Data A Out

      -- Interface B
      CLKB   : in    std_logic; -- Clock B
      PIPE_ENB : in  std_logic; -- Pipe Enable
      REB    : in    std_logic; -- Read Enable
      WEB    : in    std_logic; -- Write Enable
      ADDRB  : in    std_logic_vector(LOG2(ITEMS)-1 downto 0); -- Address B
      DIB    : in    std_logic_vector(DATA_WIDTH-1 downto 0); -- Data B In
      DOB_DV : out   std_logic; -- Data B Valid
      DOB    : out   std_logic_vector(DATA_WIDTH-1 downto 0) -- Data B Out
   );
end entity DP_BMEM;
