-- align_unit.vhd: Align unit for fifo2nfifo splitter
-- Copyright (C) 2009 CESNET
-- Author(s): Jakub Olbert <xolber00@stud.fit.vutbr.cz>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_SPLITTER_ALIGN_UNIT is
   generic(
      INPUT_WIDTH  : integer; -- input data width (from fifo2nfifo)
      JUICE_WIDTH  : integer; -- JUICE signal width
      OUTPUT_WIDTH : integer; -- output framelink width
      REM_WIDTH    : integer  -- input rem width
   );
   port(
   -- common interface
      CLK          : in std_logic;
      RESET        : in std_logic;

   -- input interface (from fifo2nfifo)
      FRAME_PART   : in std_logic; -- signal from FL_COMPRESS
      DATA_IN      : in std_logic_vector(INPUT_WIDTH - 1 downto 0);
      READ         : out std_logic; -- read signal for fifo2nfifo
      DATA_VLD     : in std_logic; -- valid data
      EMPTY        : in std_logic;

   -- output framelink interface
      TX_DATA      : out std_logic_vector(OUTPUT_WIDTH - 1 downto 0);
      TX_REM       : out std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0);
      TX_SOF_N     : out std_logic;
      TX_SOP_N     : out std_logic;
      TX_EOP_N     : out std_logic;
      TX_EOF_N     : out std_logic;
      TX_SRC_RDY_N : out std_logic;
      TX_DST_RDY_N : in std_logic

   );
end entity FL_SPLITTER_ALIGN_UNIT;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_SPLITTER_ALIGN_UNIT is
   signal discard : std_logic;
   signal data_valid : std_logic;
begin

   -- fl_decompress units -----------------------------------------------------
   DECOMPRESS : entity work.FL_DECOMPRESS
   generic map(
      WIRES => JUICE_WIDTH,
      PARTS => 0
   )
   port map(
      -- common interface
      CLK => CLK,
      RESET => RESET,

      TX_SRC_RDY_N => data_valid,
      TX_DST_RDY_N => TX_DST_RDY_N,

      -- decompressed output Framelink control signals
      TX_SOF_N => TX_SOF_N,
      TX_SOP_N => TX_SOP_N,
      TX_EOP_N => TX_EOP_N,
      TX_EOF_N => TX_EOF_N,

      -- compressed Framelink control signals
      FL_JUICE => DATA_IN(JUICE_WIDTH downto 1),

      DISCARD => '0',  -- never discard whole frame
 
      -- detect number of frame parts (from fl_compress unit)
      FRAME_PART => FRAME_PART
   );

   -- directly mapped signals -------------------------------------------------
   discard      <= DATA_IN(0);
   data_valid   <= not DATA_VLD or discard or EMPTY;
   READ         <= (not TX_DST_RDY_N AND not EMPTY) OR discard;
   TX_SRC_RDY_N <= data_valid;
   TX_DATA      <= DATA_IN(INPUT_WIDTH-1 downto REM_WIDTH+JUICE_WIDTH+1);

   -- REM reconstruction ------------------------------------------------------
   TX_REM       <= DATA_IN(REM_WIDTH+JUICE_WIDTH downto JUICE_WIDTH+1);

end architecture full;

