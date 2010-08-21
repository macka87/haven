-- discard_ent.vhd: FrameLink Discard entity.
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity fl_discard is
   generic (
      -- FrameLink data width
      DATA_WIDTH  : integer := 64;
      -- Number of channels
      CHANNELS    : integer := 2;
      -- Width of the STATUS signal for each channel, up to 16 bits
      -- Target buffer size is considered to be 2^(STATUS_WIDTH-1) words.
      STATUS_WIDTH  : integer := 10; -- For 4 KiB buffers
      -- Generate output register on output FrameLink signals
      -- (It's possible because on output FrameLink is not used dst_rdy_n signal)
      OUTPUT_REG    : boolean := true
   );
   port (
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- Write interface
        -- RX_DATA must carry frame length in the lowest 16 bits of the
        -- first frame word.
      RX_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_DREM     : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N: in  std_logic;
      RX_DST_RDY_N: out std_logic_vector(CHANNELS-1 downto 0);
      RX_SOP_N    : in  std_logic;
      RX_EOP_N    : in  std_logic;
      RX_SOF_N    : in  std_logic;
      RX_EOF_N    : in  std_logic;

      -- Must be valid with SOF
      RX_CHAN     : in  std_logic_vector(log2(CHANNELS) - 1 downto 0);

      -- Read interfaces
      TX_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_DREM     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N: out std_logic;
      --TX_DST_RDY_N: in  std_logic;
      TX_SOP_N    : out std_logic;
      TX_EOP_N    : out std_logic;
      TX_SOF_N    : out std_logic;
      TX_EOF_N    : out std_logic;

      -- Is valid during the whole frame
      TX_CHAN     : out std_logic_vector(log2(CHANNELS) - 1 downto 0);

      -- STATUS interface displays number of non-free WORDS
      STATUS      : in  std_logic_vector(CHANNELS*STATUS_WIDTH - 1 downto 0);

      -- Statistic interface
      STAT_PASS   : out std_logic; -- Frame passed (1-cycle pulse)
      STAT_DROP   : out std_logic; -- Frame dropped (1-cycle pulse
         -- Channel number (active with PASS od DROP)
      STAT_CHAN   : out std_logic_vector(log2(CHANNELS) - 1 downto 0); 
         -- Frame length (active with PASS od DROP)
      STAT_LEN    : out std_logic_vector(15 downto 0); 
         -- Free space (active with PASS od DROP)
      STAT_FREE   : out std_logic_vector(15 downto 0);
         -- Cannot process frames, because counters are being cleared
      STAT_CLEARING:in  std_logic
   );
end entity fl_discard;
