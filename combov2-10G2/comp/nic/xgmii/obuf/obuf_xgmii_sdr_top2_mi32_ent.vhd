-- obuf_xgmii_sdr_top2_mi32_ent.vhd: Output Buffer - 2 SDR obufs + LB entity
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
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_xgmii_sdr_top2_mi32 is
   generic(
      CTRL_CMD          : boolean;
      FL_WIDTH_RX       : integer;
      DFIFO_SIZE        : integer;
      HFIFO_SIZE        : integer;
      HFIFO_MEMTYPE     : mem_type
   );
   port(
      -- ---------------- Control signal -----------------
      FL_RESET       : in std_logic;
      FL_CLK         : in std_logic;

      -- 2 XGMII interfaces
      XGMII_RESET          :  in std_logic_vector(  1 downto 0);
      XGMII_TXCLK          :  in std_logic_vector(  1 downto 0);
      XGMII_TXD            : out std_logic_vector(127 downto 0);
      XGMII_TXC            : out std_logic_vector( 15 downto 0);

      -- -------------- Buffer interface -----------------
      -- Interface 0
      OBUF0_RX_DATA        :  in std_logic_vector(FL_WIDTH_RX-1 downto 0);
      OBUF0_RX_REM         :  in std_logic_vector(log2(FL_WIDTH_RX/8)-1 downto 0);
      OBUF0_RX_SRC_RDY_N   :  in std_logic;
      OBUF0_RX_SOF_N       :  in std_logic;
      OBUF0_RX_SOP_N       :  in std_logic;
      OBUF0_RX_EOF_N       :  in std_logic;
      OBUF0_RX_EOP_N       :  in std_logic;
      OBUF0_RX_DST_RDY_N   : out std_logic;
      -- Interface 1 
      OBUF1_RX_DATA        :  in std_logic_vector(FL_WIDTH_RX-1 downto 0);
      OBUF1_RX_REM         :  in std_logic_vector(log2(FL_WIDTH_RX/8)-1 downto 0);
      OBUF1_RX_SRC_RDY_N   :  in std_logic;
      OBUF1_RX_SOF_N       :  in std_logic;
      OBUF1_RX_SOP_N       :  in std_logic;
      OBUF1_RX_EOF_N       :  in std_logic;
      OBUF1_RX_EOP_N       :  in std_logic;
      OBUF1_RX_DST_RDY_N   : out std_logic;

      -- Status interface
      OUTGOING_PCKT        : out std_logic_vector(1 downto 0);

      -- ---------- MI_32 bus signals ----------------
      MI               : inout t_mi32;
      MI_CLK           : in std_logic;
      MI_RESET         : in std_logic
   );
end entity obuf_xgmii_sdr_top2_mi32;
-- ----------------------------------------------------------------------------
