-- obuf_emac_top2_ent.vhd: Output Buffer - 2 obufs + LB entity
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
--
library IEEE;
use IEEE.std_logic_1164.all;
use work.math_pack.all;
use work.lb_pkg.all;
use work.emac_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_emac_top2_mi32 is
   generic(
      DATA_PATHS     : integer;
      DFIFO_SIZE     : integer;
      SFIFO_SIZE     : integer;
      CTRL_CMD       : boolean;
      EMAC0_USECLKEN : boolean;
      EMAC1_USECLKEN : boolean
   );
   port(

      -- ---------------- Control signal -----------------
      RESET         : in  std_logic;
      WRCLK         : in  std_logic;

      -- -------------- Buffer interface -----------------
      -- Interface 0
      OBUF0_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      OBUF0_DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      OBUF0_SRC_RDY_N  : in std_logic;
      OBUF0_SOF_N      : in std_logic;
      OBUF0_SOP_N      : in std_logic;
      OBUF0_EOF_N      : in std_logic;
      OBUF0_EOP_N      : in std_logic;
      OBUF0_DST_RDY_N  : out std_logic;
      -- Interface 1 
      OBUF1_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      OBUF1_DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      OBUF1_SRC_RDY_N  : in std_logic;
      OBUF1_SOF_N      : in std_logic;
      OBUF1_SOP_N      : in std_logic;
      OBUF1_EOF_N      : in std_logic;
      OBUF1_EOP_N      : in std_logic;
      OBUF1_DST_RDY_N  : out std_logic;

      -- -------------- TX interface -----------------
      -- Interface 0
      OBUF0_EMAC_CLK   : in std_logic;
      OBUF0_EMAC_CE    : in std_logic;
      OBUF0_TX_EMAC    : inout t_emac_tx;
      -- Interface 1
      OBUF1_EMAC_CLK   : in std_logic;
      OBUF1_EMAC_CE    : in std_logic;
      OBUF1_TX_EMAC    : inout t_emac_tx;

      -- ---------- MI_32 bus signals ----------------
      MI               : inout t_mi32
   );
end entity obuf_emac_top2_mi32;
-- ----------------------------------------------------------------------------
