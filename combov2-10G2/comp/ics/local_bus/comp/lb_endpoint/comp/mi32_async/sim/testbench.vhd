-- testbench.vhd: mi32_async testbench
-- Copyright (C) 2006 CESNET
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

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;
use ieee.std_logic_arith.all;
use work.lb_pkg.all;

library work;

ENTITY testbench IS
END testbench;

ARCHITECTURE testbench OF testbench IS

constant mclkper :time := 10 ns;
constant sclkper :time := 100 ns;

signal RESET          : std_logic;
signal CLK_M          : std_logic;
signal MI_M           : t_mi32;
signal CLK_S          : std_logic;
signal MI_S           : t_mi32;

begin

uut: entity work.mi32_async
port map(
   RESET          => RESET,
   CLK_M          => CLK_M,
   MI_M           => MI_M,
   CLK_S          => CLK_S,
   MI_S           => MI_S
);

-- Master clock generation
mclock: process
begin
   CLK_M <= '1';
   wait for mclkper/2;
   CLK_M <= '0';
   wait for mclkper/2;
end process;

-- Slave clock generation
sclock: process
begin
   CLK_S <= '1';
   wait for sclkper/2;
   CLK_S <= '0';
   wait for sclkper/2;
end process;

-- Master test process
mtest: process
begin
   wait for 2 ns;

   MI_M.DWR <= (others => '0');
   MI_M.ADDR <= (others => '0');
   MI_M.RD <= '0';
   MI_M.WR <= '0';
   MI_M.BE <= "0000";

   RESET <= '1'; 
   wait for 50 ns;
   RESET <= '0';
   wait for 50 ns;

   -- Write
   MI_M.ADDR <= X"01234567";
   MI_M.DWR <= X"87654321";
   MI_M.BE <= "0111";
   MI_M.WR <= '1';
   wait for mclkper;
   MI_M.WR <= '0';

   -- Read
   wait for 1000*mclkper;
   wait for 1 ns;
   wait for 5*mclkper;
   MI_M.ADDR <= X"00000001";
   MI_M.RD <= '1';
   wait for mclkper;
   MI_M.RD <= '0';

   -- Read
   wait for 1000*mclkper;
   wait for 1 ns;
   wait for 1*mclkper;
   MI_M.ADDR <= X"00000002";
   MI_M.RD <= '1';
   wait for mclkper;
   MI_M.RD <= '0';

   wait;
end process;

-- Slave test process
stest : process
begin
   wait for 2 ns;

   MI_S.DRD <= (others => '0');
   MI_S.DRDY <= '0';
   MI_S.ARDY <= '0';

   wait for 100 ns;

   -- Wait for write, but allow it (by ARDY) two cycles later
   wait until MI_S.WR = '1';
   wait for 1 ns;
   wait for 2*sclkper;
   MI_S.ARDY <= '1';
   wait for sclkper;
   MI_S.ARDY <= '0';

   -- Wait for read, return data after 1 cycle
   wait until MI_S.RD = '1';
--   wait for 1 ns;
   MI_S.ARDY <= '1';
   wait for sclkper;
   MI_S.ARDY <= '0';
   --wait for 2*sclkper;
   MI_S.DRD <= X"11121314";
   MI_S.DRDY <= '1';
   wait for sclkper;
   MI_S.DRDY <= '0';

   -- Wait for read, return data immediately
   wait until MI_S.RD = '1';
   wait for 1 ns;
   MI_S.DRD <= X"01020304";
   MI_S.DRDY <= '1';
   MI_S.ARDY <= '1';
   wait for sclkper;
   MI_S.DRDY <= '0';
   MI_S.ARDY <= '0';


end process;

end;
