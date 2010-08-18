-- eop_dec_ent.vhd: XGMII eon-of-packet decoder
-- Copyright (C) 2010 CESNET
-- Author(s):  Jan Viktorin <xvikto03@liberouter.org>
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
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

use work.math_pack.ALL;
use work.xgmii_pkg.ALL; -- C_XGMII_TERMINATE, C_XGMII_SOP

architecture behav of xgmii_packet_dec is

   signal cmp_terminate : std_logic_vector(7 downto 0);
   signal cmp_sop_lane0 : std_logic;
   signal cmp_sop_lane4 : std_logic;

   signal sop_detected  : std_logic;
   signal eop_detected  : std_logic;

begin

   SOP <= sop_detected;
   EOP <= eop_detected;

   ---
   -- Searching for TERMINATE byte
   ---
   gen_terminate_comparators:
   for i in 0 to 7 generate

      cmp_terminate(i)  <= '1' when
         XGMII_RXD((i + 1) * 8 - 1 downto i * 8) = C_XGMII_TERMINATE
         else '0';

   end generate;
   
   ---
   -- EOP detection
   -- generate OR over all lanes
   ---
   gen_eop_detection:
   process(XGMII_RXC, cmp_terminate)
      variable lane_eop : std_logic;
   begin
      lane_eop := '0';

      for i in 0 to 7 loop
         lane_eop := lane_eop or 
                     (XGMII_RXC(i) and cmp_terminate(i));
      end loop;

      eop_detected <= lane_eop;
   end process;


   ---
   -- SOP detection on lane 0 and 4
   ---
   cmp_sop_lane0  <= '1' when XGMII_RXD( 7 downto  0) = C_XGMII_SOP else '0';
   cmp_sop_lane4  <= '1' when XGMII_RXD(39 downto 32) = C_XGMII_SOP else '0';

   sop_detected <= (XGMII_RXC(0) and cmp_sop_lane0)
                or (XGMII_RXC(4) and cmp_sop_lane4);

end architecture;
