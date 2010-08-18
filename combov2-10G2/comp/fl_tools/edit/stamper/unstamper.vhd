-- unstamper.vhd: FrameLink UnStamper architecture
-- Copyright (C) 2008 CESNET
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
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_UNSTAMPER is

   -- ------------------ Constants declaration --------------------------------
   

   -- ------------------ Signals declaration ----------------------------------
   -- registers
   signal reg_remove_stamp      : std_logic;
   signal reg_remove_stamp_s    : std_logic;
   signal reg_remove_stamp_c    : std_logic;
   signal reg_create_sof        : std_logic;
   signal reg_create_sof_s      : std_logic;
   signal reg_create_sof_c      : std_logic;
   
   -- others
   signal dv                  : std_logic;
   signal removing_stamp       : std_logic;

begin
   -- ------------------ Directly mapped signals ------------------------------
   dv                   <= not (RX_SRC_RDY_N or TX_DST_RDY_N);
   removing_stamp       <= reg_remove_stamp and (not RX_SRC_RDY_N);

   reg_remove_stamp_s   <= dv and (not RX_EOF_N);  -- frame ended
   reg_remove_stamp_c   <= removing_stamp;
   reg_create_sof_s     <= removing_stamp;
   reg_create_sof_c     <= dv;

   -- output ports mapping
   RX_DST_RDY_N      <= not (reg_remove_stamp or (not TX_DST_RDY_N));
   TX_SRC_RDY_N      <= RX_SRC_RDY_N or reg_remove_stamp;
   TX_SOF_N          <= not reg_create_sof;
   TX_SOP_N          <= not (reg_create_sof or ((not RX_SOP_N) and (not reg_remove_stamp)));
   TX_EOP_N          <= not ((not RX_EOP_N) and (not reg_remove_stamp));
   TX_EOF_N          <= not ((not RX_EOF_N) and (not reg_remove_stamp));
   TX_DATA           <= RX_DATA;
   TX_REM            <= RX_REM;

   -- register reg_remove_stamp
   reg_remove_stampp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_remove_stamp <= '1';
         else
            if (reg_remove_stamp_S = '1') then
               reg_remove_stamp <= '1';
            elsif (reg_remove_stamp_C = '1') then
               reg_remove_stamp <= '0';
            end if;
         end if;
      end if;
   end process;

   -- register reg_create_sof
   reg_create_sofp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_create_sof <= '0';
         else
            if (reg_create_sof_S = '1') then
               reg_create_sof <= '1';
            elsif (reg_create_sof_C = '1') then
               reg_create_sof <= '0';
            end if;
         end if;
      end if;
   end process;

end architecture full;
