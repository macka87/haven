-- splitter_fl128_fl8x16.vhd: FrameLink Splitter 128b --> 8x16b
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity fl_splitter_fl128_fl8x16 is
   generic(
      -- number of frame parts
      FRAME_PARTS    : integer
   );
   port(

      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface
      RX             : inout t_fl128;
      
      -- output interfaces
      TX0            : inout t_fl16;
      TX1            : inout t_fl16;
      TX2            : inout t_fl16;
      TX3            : inout t_fl16;
      TX4            : inout t_fl16;
      TX5            : inout t_fl16;
      TX6            : inout t_fl16;
      TX7            : inout t_fl16
   );
end entity;

architecture full of fl_splitter_fl128_fl8x16 is
begin

   FL_SPLITTER_I: entity work.FL_SPLITTER_GENERIC_OUTPUT
   generic map(
      DATA_WIDTH     => 128,
      OUTPUT_COUNT   => 8,
      OUTPUT_WIDTH   => 16,
      FRAME_PARTS    => FRAME_PARTS
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- input interface
      RX_SOF_N       => RX.SOF_N,
      RX_SOP_N       => RX.SOP_N,
      RX_EOP_N       => RX.EOP_N,
      RX_EOF_N       => RX.EOF_N,
      RX_SRC_RDY_N   => RX.SRC_RDY_N,
      RX_DST_RDY_N   => RX.DST_RDY_N,
      RX_DATA        => RX.DATA,
      RX_REM         => RX.DREM,
      
      -- output interfaces
      TX_SOF_N(0)             => TX0.SOF_N,
      TX_SOF_N(1)             => TX1.SOF_N,
      TX_SOF_N(2)             => TX2.SOF_N,
      TX_SOF_N(3)             => TX3.SOF_N,
      TX_SOF_N(4)             => TX4.SOF_N,
      TX_SOF_N(5)             => TX5.SOF_N,
      TX_SOF_N(6)             => TX6.SOF_N,
      TX_SOF_N(7)             => TX7.SOF_N,

      TX_SOP_N(0)             => TX0.SOP_N,
      TX_SOP_N(1)             => TX1.SOP_N,
      TX_SOP_N(2)             => TX2.SOP_N,
      TX_SOP_N(3)             => TX3.SOP_N,
      TX_SOP_N(4)             => TX4.SOP_N,
      TX_SOP_N(5)             => TX5.SOP_N,
      TX_SOP_N(6)             => TX6.SOP_N,
      TX_SOP_N(7)             => TX7.SOP_N,

      TX_EOP_N(0)             => TX0.EOP_N,
      TX_EOP_N(1)             => TX1.EOP_N,
      TX_EOP_N(2)             => TX2.EOP_N,
      TX_EOP_N(3)             => TX3.EOP_N,
      TX_EOP_N(4)             => TX4.EOP_N,
      TX_EOP_N(5)             => TX5.EOP_N,
      TX_EOP_N(6)             => TX6.EOP_N,
      TX_EOP_N(7)             => TX7.EOP_N,

      TX_EOF_N(0)             => TX0.EOF_N,
      TX_EOF_N(1)             => TX1.EOF_N,
      TX_EOF_N(2)             => TX2.EOF_N,
      TX_EOF_N(3)             => TX3.EOF_N,
      TX_EOF_N(4)             => TX4.EOF_N,
      TX_EOF_N(5)             => TX5.EOF_N,
      TX_EOF_N(6)             => TX6.EOF_N,
      TX_EOF_N(7)             => TX7.EOF_N,

      TX_SRC_RDY_N(0)         => TX0.SRC_RDY_N,
      TX_SRC_RDY_N(1)         => TX1.SRC_RDY_N,
      TX_SRC_RDY_N(2)         => TX2.SRC_RDY_N,
      TX_SRC_RDY_N(3)         => TX3.SRC_RDY_N,
      TX_SRC_RDY_N(4)         => TX4.SRC_RDY_N,
      TX_SRC_RDY_N(5)         => TX5.SRC_RDY_N,
      TX_SRC_RDY_N(6)         => TX6.SRC_RDY_N,
      TX_SRC_RDY_N(7)         => TX7.SRC_RDY_N,

      TX_DST_RDY_N(0)         => TX0.DST_RDY_N,
      TX_DST_RDY_N(1)         => TX1.DST_RDY_N,
      TX_DST_RDY_N(2)         => TX2.DST_RDY_N,
      TX_DST_RDY_N(3)         => TX3.DST_RDY_N,
      TX_DST_RDY_N(4)         => TX4.DST_RDY_N,
      TX_DST_RDY_N(5)         => TX5.DST_RDY_N,
      TX_DST_RDY_N(6)         => TX6.DST_RDY_N,
      TX_DST_RDY_N(7)         => TX7.DST_RDY_N,

      TX_DATA( 15 downto   0) => TX0.DATA,
      TX_DATA( 31 downto  16) => TX1.DATA,
      TX_DATA( 47 downto  32) => TX2.DATA,
      TX_DATA( 63 downto  48) => TX3.DATA,
      TX_DATA( 79 downto  64) => TX4.DATA,
      TX_DATA( 95 downto  80) => TX5.DATA,
      TX_DATA(111 downto  96) => TX6.DATA,
      TX_DATA(127 downto 112) => TX7.DATA,

      TX_REM(0 downto 0)      => TX0.DREM,
      TX_REM(1 downto 1)      => TX1.DREM,
      TX_REM(2 downto 2)      => TX2.DREM,
      TX_REM(3 downto 3)      => TX3.DREM,
      TX_REM(4 downto 4)      => TX4.DREM,
      TX_REM(5 downto 5)      => TX5.DREM,
      TX_REM(6 downto 6)      => TX6.DREM,
      TX_REM(7 downto 7)      => TX7.DREM
   ); 

end architecture full; 

