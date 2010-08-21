-- ibuf_emac_top2_mi32_ent.vhd: Input Buffer - 2 ibufs + MI_32 interface
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
--

library IEEE;
use IEEE.std_logic_1164.all;
use work.math_pack.all;
use work.ibuf_general_pkg.all;
use work.lb_pkg.all;
use work.emac_pkg.all;
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ibuf_emac_top2_mi32 is
   generic(
      DATA_PATHS  	: integer;     		-- Output data width in bytes
      DFIFO_SIZE  	: integer;     		-- Packet data fifo size
      HFIFO_SIZE  	: integer;     		-- Control fifo size
      HFIFO_DISTMEMTYPE : integer := 32;   		-- Distributed Ram Type (capacity) used for HFIFO
      CTRL_HDR_EN 	: boolean := true; 	-- Enables Packet Headers
      CTRL_FTR_EN 	: boolean := false; 	-- Enables Packet Footers
      MACS        	: integer := 16;  		-- Number of MAC addresses (up to 16)
      INBANDFCS   	: boolean := true    -- Frame contains FCS (true) or not (false)
   );
   port(

      -- ---------------- Common signal -----------------
      RESET         			: in  std_logic;
      IBUF_CLK      			: in  std_logic;

      -- ------------------------------------------------
      -- -------------- IBUF interfaces -----------------
      
      -- -----------
      -- INTERFACE 0
      -- EMAC RX interface
      IBUF0_RXCLK          : in std_logic;
      IBUF0_RXCE           : in std_logic;
      IBUF0_RX             : in t_emac_rx;

      -- PACODAG interface
      IBUF0_CTRL_CLK       : out std_logic;
      IBUF0_CTRL_RESET     : out std_logic;
      IBUF0_CTRL_DI        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF0_CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF0_CTRL_SRC_RDY_N : in std_logic;
      IBUF0_CTRL_SOP_N     : in std_logic;
      IBUF0_CTRL_EOP_N     : in std_logic;
      IBUF0_CTRL_DST_RDY_N : out std_logic;

      IBUF0_CTRL_RDY       : in std_logic;

      -- IBUF status interface
      IBUF0_SOP            : out std_logic;
      IBUF0_STAT           : out t_ibuf_general_stat;
      IBUF0_STAT_DV        : out std_logic;

      -- Sampling unit interface
      IBUF0_SAU_ACCEPT     : in std_logic;
      IBUF0_SAU_DV         : in std_logic;
      IBUF0_SAU_REQ        : out std_logic;

      -- FrameLink interface
      IBUF0_DATA       		: out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF0_DREM       		: out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF0_SRC_RDY_N  		: out std_logic;
      IBUF0_SOF_N      		: out std_logic;
      IBUF0_SOP_N      		: out std_logic;
      IBUF0_EOF_N      		: out std_logic;
      IBUF0_EOP_N      		: out std_logic;
      IBUF0_DST_RDY_N 		: in std_logic;
      
      -- -----------
      -- INTERFACE 1
      -- EMAC RX interface
      IBUF1_RXCLK          : in std_logic;
      IBUF1_RXCE           : in std_logic;
      IBUF1_RX             : in t_emac_rx;

      -- PACODAG interface
      IBUF1_CTRL_CLK       : out std_logic;
      IBUF1_CTRL_RESET     : out std_logic;
      IBUF1_CTRL_DI        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF1_CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF1_CTRL_SRC_RDY_N : in std_logic;
      IBUF1_CTRL_SOP_N     : in std_logic;
      IBUF1_CTRL_EOP_N     : in std_logic;
      IBUF1_CTRL_DST_RDY_N : out std_logic;
      IBUF1_CTRL_RDY       : in std_logic;

      -- IBUF status interface
      IBUF1_SOP            : out std_logic;
      IBUF1_STAT           : out t_ibuf_general_stat;
      IBUF1_STAT_DV        : out std_logic;

      -- Sampling unit interface
      IBUF1_SAU_ACCEPT     : in std_logic;
      IBUF1_SAU_DV         : in std_logic;
      IBUF1_SAU_REQ        : out std_logic;

      -- FrameLink interface
      IBUF1_DATA       		: out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF1_DREM       		: out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF1_SRC_RDY_N  		: out std_logic;
      IBUF1_SOF_N      		: out std_logic;
      IBUF1_SOP_N      		: out std_logic;
      IBUF1_EOF_N      		: out std_logic;
      IBUF1_EOP_N     		: out std_logic;
      IBUF1_DST_RDY_N  		: in std_logic;

      -- ------------------------------------------------
      -- ------------ MI_32 bus signals -----------------
      MI               : inout t_mi32
   );
end entity ibuf_emac_top2_mi32;
