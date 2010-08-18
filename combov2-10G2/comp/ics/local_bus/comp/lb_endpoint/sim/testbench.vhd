-- testbench.vhd: LBEP module testbench
-- Copyright (C) 2009 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.numeric_std.all;
use work.lb_pkg.all; -- Internal Bus package
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture testbench_arch of testbench is
   signal clk : std_logic;
   signal reset : std_logic;

   signal lb : t_local_bus16;
   signal mi : t_mi32;

   -- Simulation constants
   constant period      : time := 10 ns;
   constant half_period : time := period  / 2;

begin
-- clock generator
   clk_gen : process
   begin
      clk <= '1';
      wait for half_period;
      clk <= '0';
      wait for half_period;
   end process;

uut : entity work.lb_endpoint
generic map(
   BASE_ADDR => X"00010000",
   LIMIT => X"00002000",
   FREQUENCY => 100,
   BUFFER_EN => false
)
port map(
   CLK      => CLK,
   RESET    => RESET,
   LB_CLK   => CLK,
   LOCALBUS => lb,
   MI32     => mi
);

mi.drdy <= mi.rd;
mi.ardy <= mi.rd or mi.wr;

tb : process
begin
   RESET       <= '1';
   lb.dwr <= X"0000";
   lb.be <= "11";
   lb.ads_n <= '1';
   lb.rd_n <= '1';
   lb.wr_n <= '1';
   lb.abort_n <= '1';
   mi.drd <= X"10002000";
   --mi.ardy <= '0';
   --mi.drdy <= '0';
   wait for 5*period;
   wait for 2 ns;
   RESET       <= '0';
   wait for 5*period;

   lb.ads_n <= '0';
   lb.dwr <= X"0000";
   wait for period;
   lb.dwr <= X"0003";
   wait for period;
   lb.ads_n <= '1';
   lb.rd_n <= '0';
   wait for 2*period;
   lb.rd_n <= '1';

   wait for 5*period;

   lb.ads_n <= '0';
   lb.dwr <= X"0000";
   wait for period;
   lb.dwr <= X"0001";
   wait for period;
   lb.ads_n <= '1';
   lb.rd_n <= '0';
   wait for 2*period;
   lb.rd_n <= '1';

   wait for 5*period;

   lb.ads_n <= '0';
   lb.dwr <= X"0000";
   wait for period;
   lb.dwr <= X"0003";
   wait for period;
   lb.ads_n <= '1';
   lb.wr_n <= '0';
   wait for 2*period;
   lb.wr_n <= '1';

   wait for 5*period;

   lb.ads_n <= '0';
   lb.dwr <= X"0000";
   wait for period;
   lb.dwr <= X"0001";
   wait for period;
   lb.ads_n <= '1';
   lb.wr_n <= '0';
   wait for 2*period;
   lb.wr_n <= '1';

   wait for 5*period;
   wait;
	
end process;
end architecture testbench_arch;
