-- splitter_fl128x2.vhd: FrameLink Splitter 128x2
-- Copyright (C) 2007 CESNET
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
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity fl_splitter_fl128x2 is
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
      TX0            : inout t_fl128;
      TX1            : inout t_fl128

   );
end entity;

architecture full of fl_splitter_fl128x2 is
begin

   FL_SPLITTER_I: entity work.FL_SPLITTER
   generic map(
      DATA_WIDTH     => 128,
      OUTPUT_COUNT   => 2,
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

      TX_SOP_N(0)             => TX0.SOP_N,
      TX_SOP_N(1)             => TX1.SOP_N,

      TX_EOP_N(0)             => TX0.EOP_N,
      TX_EOP_N(1)             => TX1.EOP_N,

      TX_EOF_N(0)             => TX0.EOF_N,
      TX_EOF_N(1)             => TX1.EOF_N,

      TX_SRC_RDY_N(0)         => TX0.SRC_RDY_N,
      TX_SRC_RDY_N(1)         => TX1.SRC_RDY_N,

      TX_DST_RDY_N(0)         => TX0.DST_RDY_N,
      TX_DST_RDY_N(1)         => TX1.DST_RDY_N,

      TX_DATA(127 downto 0)    => TX0.DATA,
      TX_DATA(255 downto 128)   => TX1.DATA,

      TX_REM(3 downto 0)      => TX0.DREM,
      TX_REM(7 downto 4)      => TX1.DREM

   ); 

end architecture full; 

