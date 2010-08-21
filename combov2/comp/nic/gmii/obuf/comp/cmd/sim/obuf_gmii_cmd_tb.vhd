--
-- obuf_gmii_cmd_tb.vhd: Testbench for obuf gmii cmd part
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
entity obuf_gmii_cmd_tb is
end entity obuf_gmii_cmd_tb;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of obuf_gmii_cmd_tb is

   constant clkper     : time    := 10 ns;
   constant DATA_PATHS : integer := 4;

   signal clk          : std_logic;
   signal reset        : std_logic;
   
   signal wr           : std_logic;
   signal di           : std_logic_vector(DATA_PATHS*8-1 downto 0);
   signal di_cmd       : std_logic_vector(DATA_PATHS-1   downto 0);
   signal full         : std_logic;

   signal dfifo_do     : std_logic_vector(DATA_PATHS*9-1 downto 0);
   signal dfifo_wr     : std_logic;
   signal dfifo_full   : std_logic;
   signal sfifo_do     : std_logic_vector(0 downto 0);
   signal sfifo_wr     : std_logic;
   signal sfifo_full   : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- ----------------------------------------------------
-- UUT mapping
-- ----------------------------------------------------

UUT : entity work.obuf_gmii_cmd
generic map(
   DATA_PATHS => 4,
   CTRL_CMD   => true
)
port map(
   RESET        => reset,
   CLK          => clk,

   WR           => wr,
   DI           => di,
   DI_CMD       => di_cmd,
   FULL         => full,

   DFIFO_DO     => dfifo_do,
   DFIFO_WR     => dfifo_wr,
   DFIFO_FULL   => dfifo_full,
   
   SFIFO_DO     => sfifo_do,
   SFIFO_WR     => sfifo_wr,
   SFIFO_FULL   => sfifo_full
);


-- ----------------------------------------------------
-- clk clock generator
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

tb_p : process

begin
   wr     <= '0';
   di     <=X"07070707";
   di_cmd <= (others=>'1');
   
   dfifo_full <= '0';
   sfifo_full <= '0';

   reset        <= '1';

   wait for 100 ns;
   reset <= '0';
   
   --for i in 0 to 2 loop
   
      wait until clk'event and clk='1' and full='0';
      wr     <= '1';
      di     <= X"070707FB";
      di_cmd <= "1111";

      wait until clk'event and clk='1' and full='0';
      wr     <= '1';
      di     <= X"07030201";
      di_cmd <= "1000";

      wait until clk'event and clk='1' and full='0';
      wr     <= '1';
      di     <= X"07070504";
      di_cmd <= "1100";

      wait until clk'event and clk='1' and full='0';
      wr     <= '1';
      di     <= X"07070707";
      di_cmd <= "1111";

      wait until clk'event and clk='1' and full='0';
      wr     <= '1';
      di     <= X"070707FD";
      di_cmd <= "1111";

      wait until clk'event and clk='1' and full='0';
      wr     <= '1';
      di     <= X"07070708";
      di_cmd <= "1111";

      wait until clk'event and clk='1' and full='0';
      wr     <= '1';
      di     <= X"0707FD01";
      di_cmd <= "1110";



      wait until clk'event and clk='1' and full='0';
      wr     <= '1';
      di     <= X"070707FB";
      di_cmd <= "1111";

      wait until clk'event and clk='1' and full='0';
      wr     <= '1';
      di     <= X"07FD1211";
      di_cmd <= "1100";

      wait until clk'event and clk='1' and full='0';
      wr     <= '1';
      di     <= X"07070708";
      di_cmd <= "1111";

      wait until clk'event and clk='1' and full='0';
      wr     <= '1';
      di     <= X"0707FD00";
      di_cmd <= "1110";

      wait until clk'event and clk='1' and full='0';
      wr     <= '0';
      di     <= (others=>'0');
      di_cmd <= (others=>'0');

   wait;
end process;

end architecture behavioral;
