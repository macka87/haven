-- crossbar_config.vhd: XGMII to XGMII crossbar configurator
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

architecture behav of xgmii_crossbar_config is

   -- width of the mapping for one port
   constant PORT_WIDTH     : integer := log2(XGMII_COUNT);
   constant REG_MAP_WIDTH  : integer := XGMII_COUNT * PORT_WIDTH;
   constant REG_MAP_SIZE   : integer := REG_MAP_WIDTH / 8;
   constant REG_MAP_REMINDER : integer := REG_MAP_WIDTH rem 8;

   --+ Register to hold mapping for crossbar
   signal reg_map    : std_logic_vector(REG_MAP_WIDTH - 1 downto 0);

begin

   assert XGMII_COUNT <= 8
      report "Too many XGMII ports (supported maximum: 8)"
      severity error;

   -- mapping from MI32 to reg_map
   -- the MI32 word is connected directly ro reg_map
   gen_1to1_mapping:
   if REG_MAP_WIDTH <= DWR'length generate

      -- reading from reg_map
      process(CLK, reg_map, RD)
      begin
         if CLK'event and CLK = '1' then
            if RD = '1' then
               DRD(REG_MAP_WIDTH - 1 downto 0) <= reg_map;
               DRD(DRD'left downto REG_MAP_WIDTH) <= (others => '0');
            end if;

            DRDY   <= RD;
         end if;
      end process;

      -- writing to reg_map
      process(CLK, WR, DWR, BE)
      begin
         if CLK'event and CLK = '1' then
            if RESET = '1' then
               reg_map <= (others => '0');

            elsif WR = '1' then

               -- assign bytes from MI32 one by one while there is a
               -- place in the reg_map
               for i in 0 to 3 loop
                  if i < REG_MAP_SIZE then
                     -- read byte from MI32:
                     if BE(i) = '1' then
                        reg_map((i + 1) * 8 - 1 downto i * 8) 
                                 <= DWR((i + 1) * 8 - 1 downto i * 8);

                     end if;
                  elsif i = REG_MAP_SIZE then 
                     -- read the rest from MI32:
                     if BE(i) = '1' then
                        reg_map(i * 8 + REG_MAP_REMINDER - 1 downto i * 8) 
                                 <= DWR(i * 8 + REG_MAP_REMINDER - 1 downto i * 8);
                     end if;
                  end if;
               end loop;

            end if;
         end if;
      end process;

   end generate;

   -- not supported, maybe in the future is there is a reason...
   gen_1toN_mapping:
   if REG_MAP_WIDTH > DWR'length generate
      assert false
         report "Not implemented yet"
         severity error;
   end generate;

   -- latch of WR signal
   wr_latch : process(CLK, WR)
   begin
      if CLK'event and CLK = '1' then
         MAPPING_WE  <= WR;
      end if;
   end process;
   
   ---
   -- SIGNAL CONNECTIONS
   ---

   -- providing the reg_map out from the component
   MAPPING     <= reg_map;

   -- ARDY signal
   ARDY   <= RD or WR;

end architecture;

