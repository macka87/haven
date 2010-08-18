-- ibuf_emac_ent.vhd: Input buffer for Ethernet MAC - entity
--
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
--

library IEEE;
use IEEE.std_logic_1164.all;
use work.math_pack.all;
use work.ibuf_general_pkg.all;
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ibuf_emac is
   generic(
      DATA_PATHS     : integer;     		-- Output data width in bytes
      DFIFO_SIZE     : integer;     		-- Packet data fifo size
      HFIFO_SIZE     : integer;     		-- Header fifo size
      HFIFO_DISTMEMTYPE  : integer;             -- Distributed Ram Type (capacity ) used for HFIFO
      CTRL_HDR_EN    : boolean := true;   -- Header enable
      CTRL_FTR_EN    : boolean := false;  -- Footer enable
      MACS           : integer := 16;		-- Number of MAC addresses (up to 16)
      INBANDFCS      : boolean := true   -- frame contains FCS (true) or not (false)
   );

   port (
      RESET       	: in  std_logic;
     
      -- EMAC RX interface
      RXCLK          : in std_logic;
      RXCE           : in std_logic;
      RXD            : in std_logic_vector(7 downto 0);
      RXDV           : in std_logic;
      RXGOODFRAME    : in std_logic;
      RXBADFRAME     : in std_logic;
      RXSTATS        : in std_logic_vector(6 downto 0);
      RXSTATSVLD     : in std_logic;

      -- PACODAG interface
      CTRL_CLK       : out std_logic;
      CTRL_RESET     : out std_logic;
      CTRL_DI        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      CTRL_SRC_RDY_N : in std_logic;
      CTRL_SOP_N     : in std_logic;
      CTRL_EOP_N     : in std_logic;
      CTRL_DST_RDY_N : out std_logic;
      CTRL_RDY       : in std_logic; -- PACODAG is ready

      -- IBUF status interface
      SOP            : out std_logic;
      STAT           : out t_ibuf_general_stat;
      STAT_DV        : out std_logic;

      -- Sampling unit interface
      SAU_ACCEPT     : in std_logic;
      SAU_DV         : in std_logic;
      SAU_REQ        : out std_logic;

      -- FrameLink interface
      RDCLK      		: in  std_logic;
      DATA       		: out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      DREM       		: out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      SRC_RDY_N  		: out std_logic;
      SOF_N      		: out std_logic;
      SOP_N      		: out std_logic;
      EOF_N      		: out std_logic;
      EOP_N      		: out std_logic;
      DST_RDY_N  		: in std_logic;

      -- Address decoder interface
      ADC_CLK  		: out std_logic;
      ADC_RD   		: in  std_logic;
      ADC_WR   		: in  std_logic;
      ADC_ADDR 		: in  std_logic_vector(5 downto 0);
      ADC_DI   		: in  std_logic_vector(31 downto 0);
      ADC_DO   		: out std_logic_vector(31 downto 0);
      ADC_BE            : in  std_logic_vector(3 downto 0);
      ADC_DRDY 		: out std_logic
   );
   
end entity ibuf_emac;
