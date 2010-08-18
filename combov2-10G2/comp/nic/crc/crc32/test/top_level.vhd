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

   DI       : in  std_logic_vector(31 downto 0);
   DI_DV    : in  std_logic;
   DI_MASK  : in  std_logic_vector(1 downto 0);
   EOP      : in  std_logic;
   DO       : out std_logic_vector(31 downto 0);
   RDY      : out std_logic;
   DO_DV    : out std_logic
);
end entity fpga;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of fpga is

   signal reg_di     : std_logic_vector(31 downto 0);
   signal reg_didv   : std_logic;
   signal reg_dimask : std_logic_vector(1 downto 0);
   signal reg_eop    : std_logic;
   signal reg_do     : std_logic_vector(31 downto 0);
   signal reg_dodv   : std_logic;
   signal reg_rdy    : std_logic;

   signal do_i       : std_logic_vector(31 downto 0);
   signal dodv_i     : std_logic;
   signal rdy_i      : std_logic;

begin

-- reg_di register
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_di   <= (others => '0');
      reg_didv <= '0';
      reg_dimask <= (others => '0');
      reg_eop  <= '0';
      reg_do   <= (others => '0');
      reg_dodv <= '0';
      reg_rdy  <= '0';
   elsif (CLK'event AND CLK = '1') then
      reg_di   <= DI;
      reg_didv <= DI_DV;
      reg_dimask <= DI_MASK;
      reg_eop  <= EOP;
      reg_do   <= do_i;
      reg_dodv <= dodv_i;
      reg_rdy  <= rdy_i;
   end if;
end process;

CRC_U: entity work.crc32_32b
port map(
   CLK         => CLK,
   RESET       => RESET,
   DI          => reg_di,
   DI_DV       => reg_didv,
   DI_MASK     => reg_dimask,
   EOP         => reg_eop,
   CRC         => do_i,
   RDY         => rdy_i,
   DO_DV       => dodv_i
);

DO       <= reg_do;
DO_DV    <= reg_dodv;
RDY      <= reg_rdy;

end architecture behavioral;

