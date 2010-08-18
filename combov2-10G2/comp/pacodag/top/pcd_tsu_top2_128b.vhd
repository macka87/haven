-- pcd_tsu_top2_128b.vhd: PACODAG for NIC project, data width 128b, 2 instances
-- Copyright (C) 2009 CESNET, Liberouter project
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

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

use work.math_pack.ALL;
use work.ibuf_general_pkg.ALL;

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity pacodag_tsu_top2_128b is
   generic (
      HEADER_EN : boolean := true; -- Generate headers
      FOOTER_EN : boolean := false -- Generate footers
   );
   port (
      -- Common interface
      RESET    : in std_logic;

      -- IBUF 0 interface
      PCD0_CTRL_CLK       :  in std_logic;
      PCD0_CTRL_DATA      : out std_logic_vector(127 downto 0);
      PCD0_CTRL_REM       : out std_logic_vector(  3 downto 0);
      PCD0_CTRL_SRC_RDY_N : out std_logic;
      PCD0_CTRL_SOP_N     : out std_logic;
      PCD0_CTRL_EOP_N     : out std_logic;
      PCD0_CTRL_DST_RDY_N :  in std_logic;
      PCD0_CTRL_RDY       : out std_logic; -- PACODAG is ready for next request
      PCD0_SOP            : in std_logic;
      PCD0_STAT           : in t_ibuf_general_stat;
      PCD0_STAT_DV        : in std_logic;

      -- IBUF 1 interface
      PCD1_CTRL_CLK       :  in std_logic;
      PCD1_CTRL_DATA      : out std_logic_vector(127 downto 0);
      PCD1_CTRL_REM       : out std_logic_vector(  3 downto 0);
      PCD1_CTRL_SRC_RDY_N : out std_logic;
      PCD1_CTRL_SOP_N     : out std_logic;
      PCD1_CTRL_EOP_N     : out std_logic;
      PCD1_CTRL_DST_RDY_N :  in std_logic;
      PCD1_CTRL_RDY       : out std_logic; -- PACODAG is ready for next request
      PCD1_SOP            : in std_logic;
      PCD1_STAT           : in t_ibuf_general_stat;
      PCD1_STAT_DV        : in std_logic;

      -- TSU interface
      TS       : in std_logic_vector(63 downto 0);
      TS_DV    : in std_logic
   );
end pacodag_tsu_top2_128b;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of pacodag_tsu_top2_128b is
begin

   PACODAG0_I: entity work.pacodag_tsu_128b
   generic map(
      IFC_ID      => "0001"
   )
   port map(
      -- Common interface
      RESET    => RESET,
      -- IBUF interface
      CTRL_CLK      => PCD0_CTRL_CLK,
      CTRL_DATA     => PCD0_CTRL_DATA,
      CTRL_REM      => PCD0_CTRL_REM,
      CTRL_SRC_RDY_N=> PCD0_CTRL_SRC_RDY_N,
      CTRL_SOP_N    => PCD0_CTRL_SOP_N,
      CTRL_EOP_N    => PCD0_CTRL_EOP_N,
      CTRL_DST_RDY_N=> PCD0_CTRL_DST_RDY_N,
      CTRL_RDY      => PCD0_CTRL_RDY,
      SOP           => PCD0_SOP,
      STAT          => PCD0_STAT,
      STAT_DV       => PCD0_STAT_DV,
      -- TSU interface
      TS       => TS,
      TS_DV    => TS_DV
   ); 

   PACODAG1_I: entity work.pacodag_tsu_128b
   generic map(
      IFC_ID      => "0010"
   )
   port map(
      -- Common interface
      RESET    => RESET,
      -- IBUF interface
      CTRL_CLK      => PCD1_CTRL_CLK,
      CTRL_DATA     => PCD1_CTRL_DATA,
      CTRL_REM      => PCD1_CTRL_REM,
      CTRL_SRC_RDY_N=> PCD1_CTRL_SRC_RDY_N,
      CTRL_SOP_N    => PCD1_CTRL_SOP_N,
      CTRL_EOP_N    => PCD1_CTRL_EOP_N,
      CTRL_DST_RDY_N=> PCD1_CTRL_DST_RDY_N,
      CTRL_RDY      => PCD1_CTRL_RDY,
      SOP           => PCD1_SOP,
      STAT          => PCD1_STAT,
      STAT_DV       => PCD1_STAT_DV,
      -- TSU interface
      TS       => TS,
      TS_DV    => TS_DV
   ); 

end behavioral;

