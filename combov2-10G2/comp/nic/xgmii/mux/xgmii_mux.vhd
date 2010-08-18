-- xgmii_mux.vhd : Generic multiplexor for XGMII
-- Copyright (C) 2010 CESNET
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

-- --------------------------------------------------------------------
--                       Architecture declaration
-- --------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;

-- Math package - log2 function
use work.math_pack.all;

architecture arch of xgmii_mux is

begin
   
   ---
   -- XGMII DATA MUX
   ---
   data_mux : entity work.GEN_MUX
   generic map (
      DATA_WIDTH => 64,
      MUX_WIDTH => XGMII_COUNT
   )
   port map (
      DATA_IN => XGMII_RXD,
      SEL => SEL,
      DATA_OUT => XGMII_TXD
   );

   ---
   -- XGMII CTRL MUX
   ---
   ctrl_mux : entity work.GEN_MUX
   generic map (
      DATA_WIDTH => 8,
      MUX_WIDTH => XGMII_COUNT
   )
   port map (
      DATA_IN => XGMII_RXC,
      SEL => SEL,
      DATA_OUT => XGMII_TXC
   );

   ---
   -- XGMII SOP MUX
   ---
   sop_mux : entity work.GEN_MUX
   generic map (
      DATA_WIDTH => 1,
      MUX_WIDTH => XGMII_COUNT
   )
   port map (
      DATA_IN     => RX_SOP,
      SEL         => SEL,
      DATA_OUT(0) => TX_SOP
   );

   ---
   -- XGMII EOP MUX
   ---
   eop_mux : entity work.GEN_MUX
   generic map (
      DATA_WIDTH => 1,
      MUX_WIDTH => XGMII_COUNT
   )
   port map (
      DATA_IN     => RX_EOP,
      SEL         => SEL,
      DATA_OUT(0) => TX_EOP
   );

end architecture;

