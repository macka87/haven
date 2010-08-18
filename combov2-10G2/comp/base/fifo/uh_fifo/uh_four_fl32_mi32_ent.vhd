--
-- uh_four_fl32_mi32_ent.vhd: 4 x Unified header FIFO - entity declaration
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--            Petr Mikusek <petr.mikusek@liberouter.org>
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
use work.fl_pkg.all;
use work.lb_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity UH_FOUR_FL32_MI32 is
      port(
      -- ------- Control signals --------
      HFE_CLK           : in std_logic;
      LUP_CLK           : in std_logic;
      RESET             : in std_logic;

      -- -------- HFE interface ---------
      UH0_HFE           : inout t_fl32;
      UH1_HFE           : inout t_fl32;
      UH2_HFE           : inout t_fl32;
      UH3_HFE           : inout t_fl32;

      -- ------- LUP interface ----------
      -- Interface 0
      UH0_LUP_SR_VALID  : out std_logic;       -- If cell contains un. header
      UH0_LUP_SR_CLEAN  : in  std_logic;       -- Clean addressed cell
      UH0_LUP_DATA      : out std_logic_vector(31 downto 0); -- UH data
      UH0_LUP_ADDR      : in  std_logic_vector(8 downto 0);  -- Cell addr.
      -- Interface 1
      UH1_LUP_SR_VALID  : out std_logic;       -- If cell contains un. header
      UH1_LUP_SR_CLEAN  : in  std_logic;       -- Clean addressed cell
      UH1_LUP_DATA      : out std_logic_vector(31 downto 0); -- UH data
      UH1_LUP_ADDR      : in  std_logic_vector(8 downto 0);  -- Cell addr.
      -- Interface 2
      UH2_LUP_SR_VALID  : out std_logic;       -- If cell contains un. header
      UH2_LUP_SR_CLEAN  : in  std_logic;       -- Clean addressed cell
      UH2_LUP_DATA      : out std_logic_vector(31 downto 0); -- UH data
      UH2_LUP_ADDR      : in  std_logic_vector(8 downto 0);  -- Cell addr.
      -- Interface 3
      UH3_LUP_SR_VALID  : out std_logic;       -- If cell contains un. header
      UH3_LUP_SR_CLEAN  : in  std_logic;       -- Clean addressed cell
      UH3_LUP_DATA      : out std_logic_vector(31 downto 0); -- UH data
      UH3_LUP_ADDR      : in  std_logic_vector(8 downto 0);  -- Cell addr.

      -- Address decoder interface
      MI                : inout t_mi32
   );
end entity UH_FOUR_FL32_MI32;

