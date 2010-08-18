-- ibuf_xgmii_sdr_pcd_norec_ent.vhd: Input Buffer with unified PACODAG interface
-- Copyright (C) 2009 CESNET
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
entity ibuf_xgmii_sdr_pcd_norec is
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
      INBANDFCS         : boolean := true;
      -- Determines the length of the counter which guards the link for errors
      -- If error dont occur for 2^CNT_ERROR_SIZE cycles the link is declared to
      -- be up
      CNT_ERROR_SIZE : integer := 5;
      -- FrameLink output width (at least 64)
      FL_WIDTH_TX       : integer := 64;
      -- Put FL Relay to the output
      FL_RELAY          : boolean := false
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
      RXCLK       : in std_logic;
      RXD         : in std_logic_vector(63 downto 0);
      RXC         : in std_logic_vector( 7 downto 0);

      -- Sampling unit interface
      SAU_CLK     : out std_logic;
      SAU_RESET   : out std_logic;
      SAU_REQ     : out std_logic;
      SAU_ACCEPT  :  in std_logic;
      SAU_DV      :  in std_logic;

      -- Control data generator interface
      CTRL_CLK          : out std_logic;
      CTRL_RESET        : out std_logic;
      CTRL_DATA         :  in std_logic_vector(FL_WIDTH_TX-1 downto 0);
      CTRL_REM          :  in std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
      CTRL_SRC_RDY_N    :  in std_logic;
      CTRL_SOP_N        :  in std_logic;
      CTRL_EOP_N        :  in std_logic;
      CTRL_DST_RDY_N    : out std_logic;
      CTRL_SOP          : out std_logic;
      CTRL_RDY          : in  std_logic;

      -- Statistic data
      STAT              : out t_ibuf_general_stat;
      STAT_DV           : out std_logic;
      -- Signals active in '1' for one cycle for every processed packet
      FRAME_RECEIVED : out std_logic;
      FRAME_DISCARDED: out std_logic;
      -- When active in '1' frame was discarded due to buffer overflow. Can be active only together
      -- with FRAME_DISCARDED
      BUFFER_OVF     : out std_logic;

      -- State of the link signals
      -- Active when link is up
      LINK_UP           : out std_logic;
      -- Active when a packet is being received
      INCOMING_PCKT     : out std_logic;

      -- Output FrameLink inteface
      TX_SOF_N          : out std_logic;
      TX_SOP_N          : out std_logic;
      TX_EOP_N          : out std_logic;
      TX_EOF_N          : out std_logic;
      TX_SRC_RDY_N      : out std_logic;
      TX_DST_RDY_N      : in  std_logic;
      TX_DATA           : out std_logic_vector(FL_WIDTH_TX-1 downto 0);
      TX_REM            : out std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);

      -- =====================================================================
      --                         Memory Interface
      -- =====================================================================
      -- MI32 interface
      MI_DWR      	: in  std_logic_vector(31 downto 0); -- Input Data
      MI_ADDR     	: in  std_logic_vector(31 downto 0); -- Address
      MI_RD       	: in  std_logic;                     -- Read Request
      MI_WR       	: in  std_logic;                     -- Write Request
      MI_BE       	: in  std_logic_vector(3  downto 0); -- Byte Enable
      MI_DRD      	: out std_logic_vector(31 downto 0); -- Output Data
      MI_ARDY     	: out std_logic;                     -- Address Ready
      MI_DRDY     	: out std_logic;                     -- Data Ready
      -- Clock for MI32 interface
      MI_CLK         : in std_logic
   );
end entity ibuf_xgmii_sdr_pcd_norec;
