--
-- conv_tb.vhd: Testbench for conv
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
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant clkper     : time    :=  10 ns;

   signal reset        : std_logic;
   signal clk          : std_logic;

   signal di           : std_logic_vector(15 downto 0);
   signal di_dv        : std_logic_vector(1 downto 0);
   signal di_rd        : std_logic;
   signal di_empty     : std_logic;
   
   signal do           : std_logic_vector(7 downto 0);
   signal do_req       : std_logic;
   signal do_dv        : std_logic_vector(0 downto 0);

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- ----------------------------------------------------
-- UUT mapping
-- ----------------------------------------------------

UUT : entity work.conv
--generic map(
--)
port map(
   RESET => reset,
   CLK   => clk,

   DI       => di,
   DI_DV    => di_dv,
   DI_RD    => di_rd,
   DI_EMPTY => di_empty,

   DO     => do,
   DO_DV  => do_dv,
   DO_REQ => do_req
);


-- ----------------------------------------------------
-- clock generator
clk_clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;


-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------

in_p : process

begin
   di       <= (others=>'0');
   di_dv    <= (others=>'0');
   di_empty <= '1';

   reset <= '1';
   wait for 100 ns;
   reset <= '0';
   
   wait for 100 ns;

   wait until (clk='1' and clk'event);
   di_empty <= '0';
   di       <= X"0201";
   di_dv    <= "11";

   wait until (clk='1' and clk'event and di_rd='1');
   di_empty <= '0';
   di       <= X"0403";
   di_dv    <= "11";

   wait until (clk='1' and clk'event and di_rd='1');
   di_empty <= '1';
   di       <= X"0403";
   di_dv    <= "11";

   wait for 50 ns;

   wait until (clk='1' and clk'event);
   di_empty <= '0';
   di       <= X"0605";
   di_dv    <= "11";

   wait until (clk='1' and clk'event and di_rd='1');
   di_empty <= '0';
   di       <= X"FF07";
   di_dv    <= "01";
   
   wait until (clk='1' and clk'event and di_rd='1');
   di_empty <= '1';
   

   wait;
end process;

out_p : process
begin
   do_req <= '0';

   wait until reset='0';
   
   wait until (clk='1' and clk'event);
   do_req <= '1';
   wait until (clk='1' and clk'event and do=X"07");
   do_req <= '0';

   wait;
end process;

end architecture behavioral;
