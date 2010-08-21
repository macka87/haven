--
-- cnt_tb.vhd: Testbench of fast counter up or down
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
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;

use WORK.cnt_types.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
signal clk     : std_logic;
signal reset   : std_logic;
signal do_up   : std_logic_vector(3 downto 0);
signal do_down : std_logic_vector(3 downto 0);
signal clr     : std_logic;
signal ce      : std_logic;

begin

uut_up : entity work.cnt
generic map(
   WIDTH => 4,
   DIR   => up,
   CLEAR => true
)
port map(
   RESET => reset,
   CLK   => clk,
   DO    => do_up,
   CLR   => clr,
   CE    => ce
);

uut_down : entity work.cnt
generic map(
   WIDTH => 4,
   DIR   => down,
   CLEAR => false
)
port map(
   RESET => reset,
   CLK   => clk,
   DO    => do_down,
   CLR   => '0',
   CE    => ce
);

clk_p : process
begin
   clk <= '1';
   wait for 4 ns;
   clk <= '0';
   wait for 4 ns;
end process;

-- main testbench process
tb : process
begin
   reset <= '1';
   ce <= '0';
   clr <= '0';
   wait for 100 ns;
   reset <= '0';
   wait for 30 ns;
   ce <= '1';
   wait for 200 ns;
   clr <= '1';
   wait until clk='1' and clk'event;
   clr <= '0';
   wait for 200 ns;
   ce <= '0';
   wait for 50 ns;
   ce <= '1';
   wait;
end process;

end architecture behavioral;
