-- fl2cmd_empty.vhd: Empty architecture of FL2CMD component.
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
architecture empty of Fl2CMD is

signal empty_sig  : std_logic_vector(8+DATA_WIDTH+log2(DATA_WIDTH/8)-1 downto 0);

begin
   empty_sig <=   CLK   & -- 1
                  RESET & -- 1 = 2
                  --
                  FL_DATA        & -- DATA_WIDTH
                  FL_REM         & -- log2(DATA_WIDTH/8)
                  FL_SOF_N       & -- 1
                  FL_EOF_N       & -- 1
                  FL_SOP_N       & -- 1
                  FL_EOP_N       & -- 1
                  FL_SRC_RDY_N   & -- 1 = 5 + DATA_WIDTH + log2(DATA_WIDTH/8)
                  --
                  CMD_DST_RDY; -- 1 = 1
                  --------------------
                  -- = 8 + DATA_WIDTH + log2(DATA_WIDTH/8)

   FL_DST_RDY_N   <= 'Z';
   --
   CMD_DATA       <= (others => 'Z');
   CMD_COMMAND    <= (others => 'Z');
   CMD_SRC_RDY    <= 'Z';

end architecture empty;
