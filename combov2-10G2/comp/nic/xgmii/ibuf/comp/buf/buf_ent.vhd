-- buf_ent.vhd: Entity of buffer component of XGMII IBUF
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
use work.ibuf_pkg.all;
use work.fifo_pkg.all;
use work.ibuf_general_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity XGMII_IBUF_BUF is

   generic(
      -- Number of items in Data FIFO (FL_WIDTH_TX + control signals wide).
      -- !!!!!!!!!!! Must be 2^n, n>=2 !!!!!!!!!!!!!!!!!!!!!!
      DFIFO_SIZE     : integer := 1024;
      -- Number of items in Header and Footer FIFO
      -- (FL_WIDTH_TX + control signals wide)
      HFIFO_SIZE     : integer := 128;
      -- Type of the memory used in HFIFO
      HFIFO_MEMTYPE  : mem_type:= LUT;
      -- FrameLink output width (at least 64)
      FL_WIDTH_TX    : integer := 64
   );

   port(
      -- Common IBUF signals
      -- Clock sigal
      CLK            : in std_logic;
      -- Asynchronous reset, active in '1'
      RESET          : in std_logic;

      -- Input
      -- Packet data
      RX_DATA        : in std_logic_vector(63 downto 0);
      -- Start of the packet, active in '1'
      RX_SOP         : in std_logic;
      -- End of the packet, active in '1'.
      RX_EOP         : in std_logic;
      -- Position of the end of the packet, valid only if RX_EOP is set to '1'.
      RX_EOP_POS     : in std_logic_vector(2 downto 0);
      -- Error inside the packet was detected, active in '1'.
      RX_ERR         : in std_logic;

      -- Statistic
      -- Input
      STATS          : in t_stats;
      -- Statistic data of the frame currently being processed in FSM
      STATS_OUT      : out t_ibuf_general_stat;
      -- STATS_OUT and XGMII_ERR_OUT are valid, active in '1'
      STATS_OUT_VLD  : out std_logic;
      -- Signals active in '1' for one cycle for every processed packet
      FRAME_RECEIVED : out std_logic;
      FRAME_DISCARDED: out std_logic;
      -- When active in '1' frame was discarded due to buffer overflow. Can be active only together
      -- with FRAME_DISCARDED
      BUFFER_OVF     : out std_logic;


      -- Output
      -- Output clock
      FL_CLK         : in std_logic;

      -- Payload
      -- Data
      TX_DATA        : out std_logic_vector(FL_WIDTH_TX-1 downto 0);
      -- Position of the end of the part, valid only if TX_EOP_N is set to '0'.
      TX_REM         : out std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
      -- Start of the part, active in '0'
      TX_SOP_N       : out std_logic;
      -- End of the packet, active in '0'.
      TX_EOP_N       : out std_logic;
      -- Source is ready, active in '0'
      TX_SRC_RDY_N   : out std_logic;
      -- Destination is ready, active in '0'
      TX_DST_RDY_N   : in std_logic;

      -- Packet headres/footers
      -- Part data
      TX_HDATA       : out std_logic_vector(FL_WIDTH_TX-1 downto 0);
      -- Position of the end of the part, valid only if TX_HEOP_N is set to '0'.
      TX_HREM        : out std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
      -- Start of the part, active in '0'
      TX_HSOP_N      : out std_logic;
      -- End of the packet, active in '0'.
      TX_HEOP_N      : out std_logic;
      -- Source is ready, active in '0'
      TX_HSRC_RDY_N  : out std_logic;
      -- Destination is ready, active in '0'
      TX_HDST_RDY_N  : in std_logic;


      -- MI_INT Interface
      MI2BUF         : in t_mi2buf;
      BUF2MI         : out t_buf2mi;


      -- Control data generator interface
      -- Control data
      CTRL_DATA         : in std_logic_vector(FL_WIDTH_TX-1 downto 0);
      -- Specifies the number of valid bytes in the last CTRL_DATA beat;
      -- valid only when CTRL_EOP is asserted
      CTRL_REM          : in std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
      -- Asserted when the input signals from control data generator are valid
      CTRL_SRC_RDY_N    : in std_logic;
      -- Signals the start of the incoming control data
      CTRL_SOP_N        : in std_logic;
      -- Signals the end of the incoming control data
      CTRL_EOP_N        : in std_logic;
      -- Asserted when data from control data generator will be accepted
      CTRL_DST_RDY_N    : out std_logic;
      -- New frame is being received; prepare to generate new control data
      CTRL_REQ          : out std_logic;
      -- Send control data
      CTRL_SEND         : out std_logic;
      -- Discard control data
      CTRL_RELEASE      : out std_logic;
      -- Control data generator is ready to receive new request
      CTRL_RDY          : in std_logic
 
   ); 

end entity XGMII_IBUF_BUF;

