-- obuf_xgmii_ent.vhd: XGMII Output buffer - entity declaration
-- Copyright (C) 2008 CESNET
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
use work.fifo_pkg.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_xgmii_sdr_norec is
   generic(
      -- Frames contain control part
      CTRL_CMD          : boolean := true;
      -- FrameLink width
      FL_WIDTH_RX       : integer := 64;
      -- Number of items in Data FIFO (FL_WIDTH_RX + control signals wide).
      -- !!!!!!!!!!! Must be 2^n, n>=2 !!!!!!!!!!!!!!!!!!!!!!
      DFIFO_SIZE        : integer := 1024;
      -- HFIFO item count (1-bit wide)
      HFIFO_SIZE        : integer := 256;
      -- Type of memory used by HFIFO
      HFIFO_MEMTYPE     : mem_type := LUT
   );
   port(
      -- XGMII interface
      -- XGMII Transmit Clock
      CLK_INT           : in std_logic;
      -- Synchronous reset for XGMII inteface
      RESET_XGMII       : in  std_logic;
      -- XGMII Transmit Data
      XGMII_SDR_TXD     : out std_logic_vector(63 downto 0);
      -- XGMII Transmit Control
      XGMII_SDR_TXC     : out std_logic_vector(7 downto 0);

      -- Input FrameLink inteface
      RX_SOF_N          : in  std_logic;
      RX_SOP_N          : in  std_logic;
      RX_EOP_N          : in  std_logic;
      RX_EOF_N          : in  std_logic;
      RX_SRC_RDY_N      : in  std_logic;
      RX_DST_RDY_N      : out std_logic;
      RX_DATA           : in  std_logic_vector(FL_WIDTH_RX-1 downto 0);
      RX_REM            : in  std_logic_vector(log2(FL_WIDTH_RX/8)-1 downto 0);
      -- Clock for FrameLink interface.
      FL_CLK            : in std_logic;
      -- Synchronous reset for FrameLink inteface
      RESET_FL          : in std_logic;

      -- Status interface
      OUTGOING_PCKT     : out std_logic;

      -- MI32 interface
      MI_DWR      	   : in  std_logic_vector(31 downto 0); -- Input Data
      MI_ADDR     	   : in  std_logic_vector(31 downto 0); -- Address
      MI_RD       	   : in  std_logic;                     -- Read Request
      MI_WR       	   : in  std_logic;                     -- Write Request
      MI_BE       	   : in  std_logic_vector(3  downto 0); -- Byte Enable
      MI_DRD      	   : out std_logic_vector(31 downto 0); -- Output Data
      MI_ARDY     	   : out std_logic;                     -- Address Ready
      MI_DRDY     	   : out std_logic;                     -- Data Ready
      -- Clock for MI32 interface
      MI_CLK            : in std_logic;
      -- Synchronous reset for MI32 inteface
      RESET_MI          : in std_logic
   );
end entity;

