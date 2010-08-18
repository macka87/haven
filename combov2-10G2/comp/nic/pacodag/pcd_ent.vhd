-- pcd.vhd: PAcket COntrol DAta Generator entity
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
--            Libor Polcak <polcak_l@liberouter.org>
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
-- TODO: - 

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

entity pacodag is
   generic (
      IFC_ID   : std_logic_vector(3 downto 0);
      DATA_PATHS : integer;    -- Must be the same value as IBUF's
      HEADER_EN : boolean := true; -- Generate headers
      FOOTER_EN : boolean := false -- Generate footers
   );
   port (
      -- Common interface
      RESET    : in std_logic;

      -- IBUF interface
      CTRL_CLK    : in std_logic;
      CTRL_DATA      : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      CTRL_REM       : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      CTRL_SRC_RDY_N : out std_logic;
      CTRL_SOP_N     : out std_logic;
      CTRL_EOP_N     : out std_logic;
      CTRL_DST_RDY_N : in std_logic;
      CTRL_RDY    : out std_logic; -- PACODAG is ready for next request

      -- IBUF status interface
      SOP         : in std_logic;
      STAT        : in t_ibuf_general_stat;
      STAT_DV     : in std_logic
   );
end pacodag;

