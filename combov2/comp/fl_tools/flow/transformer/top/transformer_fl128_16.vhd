-- transformer_fl128_16.vhd: 128-bit -> 16bit FrameLink cover of FL_TRANSFORMER
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
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

-- library containing log2 function
use work.math_pack.all;

-- package with FL records
use work.fl_pkg.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity FL_TRANSFORMER_FL128_16 is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      RX             : inout t_fl128;
      TX             : inout t_fl16
   );
end entity FL_TRANSFORMER_FL128_16;

architecture full of FL_TRANSFORMER_FL128_16 is
begin

   FL_TRANSFORMER : entity work.FL_TRANSFORMER
      generic map(
         RX_DATA_WIDTH  => 128,
         TX_DATA_WIDTH  => 16
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- RX interface
         RX_DATA        => RX.DATA,
         RX_REM         => RX.DREM,
         RX_SOF_N       => RX.SOF_N,
         RX_EOF_N       => RX.EOF_N,
         RX_SOP_N       => RX.SOP_N,
         RX_EOP_N       => RX.EOP_N,
         RX_SRC_RDY_N   => RX.SRC_RDY_N,
         RX_DST_RDY_N   => RX.DST_RDY_N,
         -- TX interface
         TX_DATA        => TX.DATA,
         TX_REM         => TX.DREM,
         TX_SOF_N       => TX.SOF_N,
         TX_EOF_N       => TX.EOF_N,
         TX_SOP_N       => TX.SOP_N,
         TX_EOP_N       => TX.EOP_N,
         TX_SRC_RDY_N   => TX.SRC_RDY_N,
         TX_DST_RDY_N   => TX.DST_RDY_N
      );

end architecture full; 

