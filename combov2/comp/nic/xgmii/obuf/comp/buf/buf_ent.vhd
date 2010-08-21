-- buf_ent.vhd: Entity of buf part of XGMII OBUF
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
use work.xgmii_obuf_pkg.all;
use work.math_pack.all;
use work.fifo_pkg.all;


-- -----------------------------------------------------------------------------
--                             Entity
-- -----------------------------------------------------------------------------
entity obuf_xgmii_buf is

   generic(
      -- FrameLink width
      DATA_WIDTH        : integer;
      -- DFIFO item count (DATA_WIDTH wide)
      DFIFO_SIZE        : integer;
      -- HFIFO item count (1-bit wide)
      HFIFO_SIZE        : integer;
      -- Type of memory used by HFIFO
      HFIFO_MEMTYPE     : mem_type := LUT
   );

   port(
      -- FrameLink Clock signal
      FL_CLK            : in std_logic;
		-- Synchronous reset for FL_CLK domain
		RESET_FL          : in std_logic;
      -- Output XGMII Clock signal
      XGMII_CLK         : in std_logic;
      -- Synchronous reset for XGMII domain
		RESET_XGMII       : in std_logic;

      -- DFIFO input interface
      RX_DATA           : in std_logic_vector(DATA_WIDTH-1  downto 0);
      RX_SOP_N          : in std_logic;
      RX_EOP_N          : in std_logic;
      RX_EOP_POS        : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_WR             : in std_logic;
      RX_MARK           : in std_logic;
      RX_DFIFO_FULL     : out std_logic;
      RX_DFIFO_OVF      : out std_logic;

      -- HFIFO input interface
      RX_HDATA          : in std_logic_vector(C_FTR_MAX_BIT downto 0);
      RX_HFIFO_WR       : in std_logic;
      RX_HFIFO_FULL     : out std_logic;

      -- Process interface
      TX_DATA           : out std_logic_vector(63 downto 0);
      TX_SOP            : out std_logic;
      TX_EOP            : out std_logic;
      TX_EOP_POS        : out std_logic_vector(log2(64/8)-1 downto 0);
      TX_DV             : out std_logic;
      -- '1' Replace source MAC address, '0' keep the one present in frame
      SRC_MAC_RPLC      : out std_logic;
      -- Send next SRC_MAC_RPLC, active in '1'
      NEXT_SRC_MAC_RPLC : in std_logic;
      -- Destination is ready, active in '1'
      TX_DST_RDY        : in std_logic;
      -- MAC address register (MSB is byte 47 downto 40)
      -- http://en.wikipedia.org/wiki/MAC_Address
      REG_MAC_ADDR      : out std_logic_vector(47 downto 0);

      -- OBUF MI32 interface
      MI_DWR      	   : in  std_logic_vector(31 downto 0); -- Input Data
      MI_ADDR     	   : in  std_logic_vector(31 downto 0); -- Address
      MI_RD       	   : in  std_logic;                     -- Read Request
      MI_WR       	   : in  std_logic;                     -- Write Request
      MI_BE       	   : in  std_logic_vector(3  downto 0); -- Byte Enable
      MI_DRD      	   : out std_logic_vector(31 downto 0); -- Output Data
      MI_ARDY     	   : out std_logic;                     -- Address Ready
      MI_DRDY     	   : out std_logic;                     -- Data Ready
      MI_CLK            : in std_logic;
		-- Synchronous reset for MI_CLK domain
		RESET_MI          : in std_logic

   );

end entity obuf_xgmii_buf;
