-- switch_empty.vhd: FrameLink 1-N switch empty architecture.
-- Copyright (C) 2004 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

architecture empty of fl_switch_1toN is
begin

   CLK   => open,
   RESET => open,

   RX_DATA  => open,
   RX_REM   => open,
   RX_SOF_N => open,
   RX_EOF_N => open,
   RX_SOP_N => open,
   RX_EOP_N => open,
   RX_SRC_RDY_N   => '1',
   RX_DST_RDY_N   => open,

   TX_DATA  => (others => 'X'),
   TX_REM   => (others => 'X'),
   TX_SOF_N => (others => 'X'),
   TX_EOF_N => (others => 'X'),
   TX_SOP_N => (others => 'X'),
   TX_EOP_N => (others => 'X'),
   TX_SRC_RDY_N   => (others => '1'),
   TX_DST_RDY_N   => open,

end architecture;

