-- splitter_x3_norec.vhd: FrameLink Splitter 3 output interfaces, NO RECORDS
-- Copyright (C) 2009 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
entity FL_SPLITTER_X3_NOREC is
   generic(
      -- Input data width
      DATA_WIDTH     : integer;
      -- number of frame parts
      FRAME_PARTS    : integer
   );
   port(

      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface
      RX_SOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      
      -- output interfaces
      TX0_SOF_N      : out std_logic;
      TX0_SOP_N      : out std_logic;
      TX0_EOP_N      : out std_logic;
      TX0_EOF_N      : out std_logic;
      TX0_SRC_RDY_N  : out std_logic;
      TX0_DST_RDY_N  : in  std_logic;
      TX0_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX0_REM        : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

      TX1_SOF_N      : out std_logic;
      TX1_SOP_N      : out std_logic;
      TX1_EOP_N      : out std_logic;
      TX1_EOF_N      : out std_logic;
      TX1_SRC_RDY_N  : out std_logic;
      TX1_DST_RDY_N  : in  std_logic;
      TX1_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX1_REM        : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

      TX2_SOF_N      : out std_logic;
      TX2_SOP_N      : out std_logic;
      TX2_EOP_N      : out std_logic;
      TX2_EOF_N      : out std_logic;
      TX2_SRC_RDY_N  : out std_logic;
      TX2_DST_RDY_N  : in  std_logic;
      TX2_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX2_REM        : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0)
   );
end entity FL_SPLITTER_X3_NOREC;

architecture full of FL_SPLITTER_X3_NOREC is
   signal tx_data_i        : std_logic_vector(3*DATA_WIDTH-1 downto 0);
   signal tx_rem_i         : std_logic_vector(3*log2(DATA_WIDTH/8)-1 downto 0);
begin

   TX0_DATA <= tx_data_i((0+1)*DATA_WIDTH-1 downto 0*DATA_WIDTH);
   TX1_DATA <= tx_data_i((1+1)*DATA_WIDTH-1 downto 1*DATA_WIDTH);
   TX2_DATA <= tx_data_i((2+1)*DATA_WIDTH-1 downto 2*DATA_WIDTH);

   TX0_REM  <= tx_rem_i((0+1)*log2(DATA_WIDTH/8)-1 downto 0*log2(DATA_WIDTH/8));
   TX1_REM  <= tx_rem_i((1+1)*log2(DATA_WIDTH/8)-1 downto 1*log2(DATA_WIDTH/8));
   TX2_REM  <= tx_rem_i((2+1)*log2(DATA_WIDTH/8)-1 downto 2*log2(DATA_WIDTH/8));

   FL_SPLITTER_I: entity work.FL_SPLITTER
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      OUTPUT_COUNT   => 3,
      FRAME_PARTS    => FRAME_PARTS
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- input interface
      RX_SOF_N       => RX_SOF_N,
      RX_SOP_N       => RX_SOP_N,
      RX_EOP_N       => RX_EOP_N,
      RX_EOF_N       => RX_EOF_N,
      RX_SRC_RDY_N   => RX_SRC_RDY_N,
      RX_DST_RDY_N   => RX_DST_RDY_N,
      RX_DATA        => RX_DATA,
      RX_REM         => RX_REM,
      
      -- output interfaces
      TX_SOF_N(0)             => TX0_SOF_N,
      TX_SOF_N(1)             => TX1_SOF_N,
      TX_SOF_N(2)             => TX2_SOF_N,

      TX_SOP_N(0)             => TX0_SOP_N,
      TX_SOP_N(1)             => TX1_SOP_N,
      TX_SOP_N(2)             => TX2_SOP_N,

      TX_EOP_N(0)             => TX0_EOP_N,
      TX_EOP_N(1)             => TX1_EOP_N,
      TX_EOP_N(2)             => TX2_EOP_N,

      TX_EOF_N(0)             => TX0_EOF_N,
      TX_EOF_N(1)             => TX1_EOF_N,
      TX_EOF_N(2)             => TX2_EOF_N,

      TX_SRC_RDY_N(0)         => TX0_SRC_RDY_N,
      TX_SRC_RDY_N(1)         => TX1_SRC_RDY_N,
      TX_SRC_RDY_N(2)         => TX2_SRC_RDY_N,

      TX_DST_RDY_N(0)         => TX0_DST_RDY_N,
      TX_DST_RDY_N(1)         => TX1_DST_RDY_N,
      TX_DST_RDY_N(2)         => TX2_DST_RDY_N,

      TX_DATA                 => tx_data_i,
      TX_REM                  => tx_rem_i
   ); 

end architecture full; 

