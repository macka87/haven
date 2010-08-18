--
-- fpga.vhd: Top Level
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas <martinek@liberouter.org>
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
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity fpga is
port(
   RESET    : in  std_logic;
   CLK      : in  std_logic;

   DI       : in  std_logic_vector(7 downto 0);
   INIT     : in  std_logic;
   DO       : out std_logic_vector(31 downto 0);
   DO_DV    : out std_logic
);
end entity fpga;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of fpga is

   signal reg_di     : std_logic_vector(7 downto 0);
   signal reg_init   : std_logic;
   signal reg_do     : std_logic_vector(31 downto 0);
   signal reg_dodv   : std_logic;
   signal do_i       : std_logic_vector(31 downto 0);
   signal dodv_i     : std_logic;

begin

-- reg_di register
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_di   <= (others => '0');
      reg_init <= '0';
      reg_do   <= (others => '0');
      reg_dodv <= '0';
   elsif (CLK'event AND CLK = '1') then
      reg_di   <= DI;
      reg_init <= INIT;
      reg_do   <= do_i;
      reg_dodv <= dodv_i;
   end if;
end process;

DO <= reg_do;

CRC_U: entity work.crc8s
port map(
   CLK         => CLK,
   RESET       => RESET,
   INIT        => reg_init,
   DATA        => reg_di,
   REG_OUT     => do_i,
   DATA_VALID  => dodv_i
);

DO       <= reg_do;
DO_DV    <= reg_dodv;

end architecture behavioral;

