-- fl_ent.vhd: Entity of FL part of XGMII OBUF
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.xgmii_obuf_pkg.all;

entity obuf_xgmii_fl is

   generic(
      -- Frames contain control part
      CTRL_CMD          : boolean;
      -- FrameLink width
      DATA_WIDTH        : integer
   );

   port(
      -- Clock signal
      CLK               : in std_logic;
      -- Synchronous reset
      RESET             : in std_logic;

      -- Input FrameLink interface
      RX_DATA           : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM            : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOF_N          : in std_logic;
      RX_SOP_N          : in std_logic;
      RX_EOP_N          : in std_logic;
      RX_EOF_N          : in std_logic;
      RX_SRC_RDY_N      : in std_logic;
      RX_DST_RDY_N      : out std_logic;

      -- Output DFIFO interface
      TX_DATA           : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_N          : out std_logic;
      TX_EOP_N          : out std_logic;
      TX_EOP_POS        : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_WR             : out std_logic;
      TX_MARK           : out std_logic;
      TX_DFIFO_FULL     : in std_logic;
      TX_DFIFO_OVF      : in std_logic;

      -- Output HFIFO interface
      TX_HDATA          : out std_logic_vector(C_FTR_MAX_BIT downto 0);
      TX_HFIFO_WR       : out std_logic;
      TX_HFIFO_FULL     : in std_logic
   );

end entity obuf_xgmii_fl;
