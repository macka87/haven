-- testbench.vhd: fl_guard testbench
-- Copyright (C) 2007 CESNET
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
use work.math_pack.all;
use work.lb_pkg.all;

library work;

ENTITY testbench IS
END testbench;

ARCHITECTURE testbench OF testbench IS

constant clkper :time := 10 ns;

signal CLK            : std_logic;
signal RESET          : std_logic;
signal SOF_N          : std_logic;
signal EOF_N          : std_logic;
signal SOP_N          : std_logic;
signal EOP_N          : std_logic;
signal DST_RDY_N      : std_logic;
signal SRC_RDY_N      : std_logic;
signal invalid        : std_logic;

begin

uut: entity work.fl_guard
generic map(
   HEADER      => true,
   FOOTER      => true
)
port map(
CLK            => CLK,
RESET          => RESET,
SOF_N          => SOF_N,
EOF_N          => EOF_N,
SOP_N          => SOP_N,
EOP_N          => EOP_N,
DST_RDY_N      => DST_RDY_N,
SRC_RDY_N      => SRC_RDY_N,
INVALID        => INVALID
);

-- Clock generation
local_clock: process
begin
   CLK <= '1';
   wait for clkper/2;
   CLK <= '0';
   wait for clkper/2;
end process;

-- Test process
test: process
begin
   wait for 2 ns;
   SOF_N <= '1';
   EOF_N <= '1';
   SOP_N <= '1';
   EOP_N <= '1';
   DST_RDY_N <= '1';
   SRC_RDY_N <= '1';

   RESET <= '1'; 
   wait for 5*clkper;
   RESET <= '0';
   wait for 5*clkper;

   -- first packet
   DST_RDY_N <= '0';
   wait for clkper;
   SRC_RDY_N <= '0';
   SOF_N <= '0';
   SOP_N <= '0';
   wait for clkper;
   SOF_N <= '1';
   SOP_N <= '1';
   EOP_N <= '0';
   wait for clkper;
   EOP_N <= '1';
   SOP_N <= '0';
   wait for clkper;
   SOP_N <= '1';
   wait for clkper;
   SRC_RDY_N <= '1';
   wait for clkper;
   SRC_RDY_N <= '0';
   wait for clkper;
   DST_RDY_N <= '1';
   wait for clkper;
   DST_RDY_N <= '0';
   wait for clkper;
   wait for clkper;
   EOP_N <= '0';
   wait for clkper;
   EOF_N <= '0';
   SOP_N <= '0';
   wait for clkper;
   EOP_N <= '1';
   SOP_N <= '1';
   EOF_N <= '1';
   SRC_RDY_N <= '1';

   -- second packet
   wait for 5*clkper; 
   SRC_RDY_N <= '0';
   SOF_N <= '0';
   SOP_N <= '0';
   wait for clkper;
   SOF_N <= '1';
   SOP_N <= '1';
   EOP_N <= '0';
   wait for clkper;
   EOP_N <= '1';
   SOP_N <= '0';
   wait for clkper;
   SOP_N <= '1';
   wait for clkper;
   SRC_RDY_N <= '1';
   wait for clkper;
   SRC_RDY_N <= '0';
   wait for clkper;
   DST_RDY_N <= '1';
   wait for clkper;
   DST_RDY_N <= '0';
   wait for clkper;
   wait for clkper;
   EOP_N <= '0';
   wait for clkper;
   EOP_N <= '1';
   SOP_N <= '0';
   wait for clkper;
   EOP_N <= '0';
   SOP_N <= '1';
   EOF_N <= '0';
   wait for clkper;
   SRC_RDY_N <= '1';


   wait;
end process;

end;
