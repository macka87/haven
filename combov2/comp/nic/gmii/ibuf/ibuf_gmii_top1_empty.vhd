--
-- ibuf_gmii_top1_empty.vhd: ibuf top level - empty architecture
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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

use work.math_pack.all;

----------------------------------------------------------------------------
--                      Architecture declaration
----------------------------------------------------------------------------
architecture empty of ibuf_gmii_top1 is

signal empty_sig : std_logic_vector(37+8*DATA_PATHS+LOG2(DATA_PATHS)-1 downto 0);
begin
   empty_sig <= RESET            & --  1

		RXCLK            & --  1
                RXD              & --  8
                RXDV             & --  1
                RXER             & --  1

                CTRL_DI          & --  8*DATA_PATHS
                CTRL_REM         & --  LOG2(DATA_PATHS)
                CTRL_SRC_RDY_N   & --  1
                CTRL_SOP_N       & --  1
                CTRL_EOP_N       & --  1
                CTRL_HDR_EN      & --  1
                CTRL_FTR_EN      & --  1
                CTRL_RDY         & --  1

                SAU_ACCEPT       & --  1
                SAU_DV           & --  1

                RDCLK            & --  1
                DST_RDY_N        & --  1

                LBCLK            & --  1
		LBFRAME          & --  1
                LBAS             & --  1
                LBRW             & --  1
                LBLAST           & --  1
                LBAD;              -- 16
                                   -- --
                                   -- 36+8*DATA_PATHS+LOG2(DATA_PATHS)
   
   CTRL_CLK       <= '0';
   CTRL_DST_RDY_N <= '0';

   SOP            <= '0';
   --STAT
   STAT_DV        <= '0';

   DATA           <= (others => '0');
   DREM           <= (others => '0');
   SRC_RDY_N      <= '1';
   SOF_N          <= '1';
   EOF_N          <= '1';
   SOP_N          <= '1';
   EOP_N          <= '1';

   LBHOLDA        <= 'Z';
   LBRDY          <= 'Z';
   LBAD           <= (others => 'Z');

end architecture empty;

