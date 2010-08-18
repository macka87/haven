-- ibuf_xgmii_top2_mi32_ent.vhd: Input Buffer - 2 ibufs + MI_32 interface
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
--

library IEEE;
use IEEE.std_logic_1164.all;
use work.math_pack.all;
use work.fifo_pkg.all;
use work.ibuf_general_pkg.all;
use work.lb_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ibuf_xgmii_top2_mi32 is
   generic(
      -- Number of items in Data FIFO (FL_WIDTH_TX + control signals wide).
      -- !!!!!!!!!!! Must be 2^n, n>=2 !!!!!!!!!!!!!!!!!!!!!!
      DFIFO_SIZE        : integer := 1024;
      -- Number of items in Header and Footer FIFO
      -- (FL_WIDTH_TX + control signals wide)
      HFIFO_SIZE        : integer := 128;
       -- Type of the memory used in HFIFO
      HFIFO_MEMTYPE     : mem_type:= LUT;
      -- Enables frame headers
      CTRL_HDR_EN       : boolean := true;
      -- Enables frame footers
      CTRL_FTR_EN       : boolean := false;
      -- Number of supported MAC addresses (up to 16)
      MACS              : integer := 16;
      -- Remove FCS from the packet (false -> remove, true -> don't remove)
      INBANDFCS      	: boolean := true;
      -- Determines the length of the counter which guards the link for errors
      -- If error dont occur for 2^CNT_ERROR_SIZE cycles the link is declared to
      -- be up
      CNT_ERROR_SIZE : integer := 5;
      -- FrameLink output width (at least 64)
      FL_WIDTH_TX       : integer := 64;
      -- Put FL Relay to the output
      FL_RELAY          : boolean := true
   );
   port(
      -- Common signals
      -- Global reset
      RESET             : in std_logic;
      FL_CLK            : in std_logic;

      -- =====================================================================
      --                               IBUF 0
      -- =====================================================================

      -- XGMII Receive Interface
      IBUF0_RXCLK       : in std_logic;
      IBUF0_RXD         : in std_logic_vector(31 downto 0);
      IBUF0_RXC         : in std_logic_vector(3 downto 0);

      -- Sampling unit interface
      IBUF0_SAU_CLK     : out std_logic;
      IBUF0_SAU_RESET   : out std_logic;
      IBUF0_SAU_REQ     : out std_logic;
      IBUF0_SAU_ACCEPT  :  in std_logic;
      IBUF0_SAU_DV      :  in std_logic;

      -- Control data generator interface
      IBUF0_CTRL_CLK          : out std_logic;
      IBUF0_CTRL_RESET        : out std_logic;
      IBUF0_CTRL_DATA         :  in std_logic_vector(FL_WIDTH_TX-1 downto 0);
      IBUF0_CTRL_REM          :  in std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
      IBUF0_CTRL_SRC_RDY_N    :  in std_logic;
      IBUF0_CTRL_SOP_N        :  in std_logic;
      IBUF0_CTRL_EOP_N        :  in std_logic;
      IBUF0_CTRL_DST_RDY_N    : out std_logic;
      IBUF0_CTRL_SOP          : out std_logic;
      IBUF0_CTRL_RDY          : in  std_logic;

      -- Statistic data
      IBUF0_STAT              : out t_ibuf_general_stat;
      IBUF0_STAT_DV           : out std_logic;

      -- State of the link signals
      -- Active when link is up
      IBUF0_LINK_UP           : out std_logic;
      -- Active when a packet is being received
      IBUF0_INCOMING_PCKT     : out std_logic;

      -- Output FrameLink inteface
      IBUF0_TX_SOF_N          : out std_logic;
      IBUF0_TX_SOP_N          : out std_logic;
      IBUF0_TX_EOP_N          : out std_logic;
      IBUF0_TX_EOF_N          : out std_logic;
      IBUF0_TX_SRC_RDY_N      : out std_logic;
      IBUF0_TX_DST_RDY_N      : in  std_logic;
      IBUF0_TX_DATA           : out std_logic_vector(FL_WIDTH_TX-1 downto 0);
      IBUF0_TX_REM            : out std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);

      -- =====================================================================
      --                               IBUF 1
      -- =====================================================================

      -- XGMII Receive Interface
      IBUF1_RXCLK       : in std_logic;
      IBUF1_RXD         : in std_logic_vector(31 downto 0);
      IBUF1_RXC         : in std_logic_vector(3 downto 0);

      -- Sampling unit interface
      IBUF1_SAU_CLK     : out std_logic;
      IBUF1_SAU_RESET   : out std_logic;
      IBUF1_SAU_REQ     : out std_logic;
      IBUF1_SAU_ACCEPT  :  in std_logic;
      IBUF1_SAU_DV      :  in std_logic;

      -- Control data generator interface
      IBUF1_CTRL_CLK          : out std_logic;
      IBUF1_CTRL_RESET        : out std_logic;
      IBUF1_CTRL_DATA         :  in std_logic_vector(FL_WIDTH_TX-1 downto 0);
      IBUF1_CTRL_REM          :  in std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
      IBUF1_CTRL_SRC_RDY_N    :  in std_logic;
      IBUF1_CTRL_SOP_N        :  in std_logic;
      IBUF1_CTRL_EOP_N        :  in std_logic;
      IBUF1_CTRL_DST_RDY_N    : out std_logic;
      IBUF1_CTRL_SOP          : out std_logic;
      IBUF1_CTRL_RDY          :  in std_logic;

      -- Statistic data
      IBUF1_STAT              : out t_ibuf_general_stat;
      IBUF1_STAT_DV           : out std_logic;

      -- State of the link signals
      -- Active when link is up
      IBUF1_LINK_UP           : out std_logic;
      -- Active when a packet is being received
      IBUF1_INCOMING_PCKT     : out std_logic;

      -- Output FrameLink inteface
      IBUF1_TX_SOF_N          : out std_logic;
      IBUF1_TX_SOP_N          : out std_logic;
      IBUF1_TX_EOP_N          : out std_logic;
      IBUF1_TX_EOF_N          : out std_logic;
      IBUF1_TX_SRC_RDY_N      : out std_logic;
      IBUF1_TX_DST_RDY_N      :  in std_logic;
      IBUF1_TX_DATA           : out std_logic_vector(FL_WIDTH_TX-1 downto 0);
      IBUF1_TX_REM            : out std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);

      -- =====================================================================
      --                         Memory Interface
      -- =====================================================================
      -- MI32 interface
      MI                : inout t_mi32;
      -- Clock for MI32 interface
      MI_CLK            : in std_logic
   );
end entity ibuf_xgmii_top2_mi32;
