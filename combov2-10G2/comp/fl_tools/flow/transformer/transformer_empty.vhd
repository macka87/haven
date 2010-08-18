-- transformer_empty.vhd: Empty architecture of FrameLink Transformer
-- component.
-- Copyright (C) 2006 CESNET
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
-- TODO:
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- ------------------------------------------------------------------------
--                      Architecture declaration
-- ------------------------------------------------------------------------
architecture empty of FL_TRANSFORMER is

signal empty_sig  : std_logic_vector(8+RX_DATA_WIDTH+log2(RX_DATA_WIDTH/8)-1 downto 0);

begin
   empty_sig <=   CLK   & -- 1
                  RESET & -- 1 = 2
                  --
                  RX_DATA        & -- RX_DATA_WIDTH
                  RX_REM         & -- log2(RX_DATA_WIDTH/8)
                  RX_SOF_N       & -- 1
                  RX_EOF_N       & -- 1
                  RX_SOP_N       & -- 1
                  RX_EOP_N       & -- 1
                  RX_SRC_RDY_N   & -- 1 = 5 + RX_DATA_WIDTH + log2(RX_DATA_WIDTH/8)
                  --
                  TX_DST_RDY_N; -- 1 = 1
                  --------------------
                  -- = 8 + RX_DATA_WIDTH + log2(RX_DATA_WIDTH/8)

   RX_DST_RDY_N   <= 'Z';
   --
   TX_DATA        <= (others => 'Z');
   TX_REM         <= (others => 'Z');
   TX_SOF_N       <= 'Z';
   TX_EOF_N       <= 'Z';
   TX_SOP_N       <= 'Z';
   TX_EOP_N       <= 'Z';
   TX_SRC_RDY_N   <= 'Z';

end architecture empty;
