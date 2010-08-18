--
-- ibuf_xgmii_fl128.vhd: XGMII Input buffer - 128b TX interface cover
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
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
use work.lb_pkg.all;
use work.fl_pkg.all;
use work.fifo_pkg.all;
use work.math_pack.all;
use work.ibuf_general_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ibuf_xgmii_fl128 is
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
      -- Determines the length of the counter which guards the link for errors
      -- If error dont occur for 2^CNT_ERROR_SIZE cycles the link is declared to
      -- be up
      CNT_ERROR_SIZE : integer := 5;
      -- Number of supported MAC addresses (up to 16)
      MACS              : integer := 16;
      -- Put FL Relay to the output
      FL_RELAY          : boolean := true
   );
   port(
      -- Common signals
      -- Global reset
      RESET             : in  std_logic;

      -- XGMII interface
      -- XGMII Receive Clock
      XGMII_RXCLK       : in  std_logic;
      -- XGMII Receive Data
      XGMII_RXD         : in  std_logic_vector(31 downto 0);
      -- XGMII Receive Control
      XGMII_RXC         : in  std_logic_vector(3 downto 0);

      -- Internal clock
      -- Clock for SAU and PACODAG component
      INT_CLK           : out std_logic;

      -- Sampling unit interface
      -- Request for sampling information
      SAU_REQ           : out std_logic;
      -- Accept incoming frame
      SAU_ACCEPT        : in std_logic;
      -- Sampling information valid
      SAU_DV            : in std_logic;
   
      -- PACODAG interface
      PCD               : inout t_pacodag128;

      -- Link state interface
      -- Active when link is up
      LINK_UP        : out std_logic;
      -- Active when a packet is being received
      INCOMING_PCKT  : out std_logic;

      -- Output FrameLink inteface
      TX                : inout t_fl128;
      -- Clock for FrameLink interface. Might be asynchronous to IBUF clock
      FL_CLK            : in std_logic;

      -- MI32 interface
      MI                : inout t_mi32;
      -- Clock for MI32 interface
      MI_CLK            : in std_logic
   );
end entity ibuf_xgmii_fl128;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_xgmii_fl128 is

begin

   -- Generic IBUF instantion ----------------------------------------------
   GENERIC_IBUF_I: entity work.ibuf_xgmii
   generic map (
      DFIFO_SIZE        => DFIFO_SIZE,
      HFIFO_SIZE        => HFIFO_SIZE,
      HFIFO_MEMTYPE     => HFIFO_MEMTYPE,
      CTRL_HDR_EN       => CTRL_HDR_EN,
      CTRL_FTR_EN       => CTRL_FTR_EN,
      CNT_ERROR_SIZE    => CNT_ERROR_SIZE,
      MACS              => MACS,
      FL_WIDTH_TX       => 128,
      FL_RELAY          => FL_RELAY
   )
   port map (
      -- Global reset
      RESET             => RESET,

      -- XGMII interface
      XGMII_RXCLK       => XGMII_RXCLK,
      XGMII_RXD         => XGMII_RXD,
      XGMII_RXC         => XGMII_RXC,

      -- Internal clock
      INT_CLK           => INT_CLK,

      -- Sampling unit interface
      SAU_REQ           => SAU_REQ,
      SAU_ACCEPT        => SAU_ACCEPT,
      SAU_DV            => SAU_DV,
   
      -- Control data generator interface
      CTRL_CLK          => PCD.CLK,
      CTRL_DATA         => PCD.DATA,
      CTRL_REM          => PCD.DREM,
      CTRL_SRC_RDY_N    => PCD.SRC_RDY_N,
      CTRL_SOP_N        => PCD.SOP_N,
      CTRL_EOP_N        => PCD.EOP_N,
      CTRL_DST_RDY_N    => PCD.DST_RDY_N,
      CTRL_REQ          => PCD.SOP,
      CTRL_SEND         => PCD.STAT_DV,
      CTRL_RELEASE      => open,
      CTRL_RDY          => PCD.PACODAG_RDY,

      -- Statistic data, active in '1'
      STAT              => PCD.STAT,
      STAT_VLD          => open, -- active when CTRL_SEND = '1'

      LINK_UP           => LINK_UP,
      INCOMING_PCKT     => INCOMING_PCKT,

      -- Output FrameLink inteface
      TX_SOF_N          => TX.SOF_N,
      TX_SOP_N          => TX.SOP_N,
      TX_EOP_N          => TX.EOP_N,
      TX_EOF_N          => TX.EOF_N,
      TX_SRC_RDY_N      => TX.SRC_RDY_N,
      TX_DST_RDY_N      => TX.DST_RDY_N,
      TX_DATA           => TX.DATA,
      TX_REM            => TX.DREM,
      -- Clock for FrameLink interface. Might be asynchronous to IBUF clock
      FL_CLK            => FL_CLK,

      -- MI32 interface
      MI                => MI,
      MI_CLK            => MI_CLK
   );

end architecture full;
-- ----------------------------------------------------------------------------


