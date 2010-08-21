--
-- cnt_tb.vhd: Testbench of generic shift register with reset
-- Copyright (C) 2006 CESNET
-- Author(s): Michal Spacek <xspace14@stud.fit.vutbr.cz>
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
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;

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
signal din   : std_logic;
signal ce      : std_logic;
signal dout : std_logic;

begin

uut_sh_reg_resload : entity work.sh_reg_resload
generic map(
   NUM_BITS => 16,
   INIT   => X"A00E",
   INIT_EXT00 => X"0000000000000000"
)
port map(
   RESET => reset,
   CLK   => clk,
   DIN    => din,
   CE    => ce,
   DOUT  => dout
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
   reset <= '0';
   din <= '0';
   ce <= '1';
   wait for 400 ns;
   reset <= '1';
   wait for 200 ns;
   reset <= '0';
   din <= '0';
   wait for 500 ns;
end process;

end architecture behavioral;
