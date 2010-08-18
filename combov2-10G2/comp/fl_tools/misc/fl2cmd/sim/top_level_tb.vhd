-- top_level_tb.vhd: fl2cmd testbench file
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
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
use ieee.numeric_std.all;
use ieee.std_logic_arith.all;

library work;
use work.math_pack.all;
use work.commands.all;

entity testbench is
end testbench;

architecture testbench of testbench is

constant CLKPER      : time      := 10 ns;
constant DATA_WIDTH  : integer   := 16;

signal CLK           : std_logic;
signal RESET         : std_logic;

signal CMD_DATA      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal CMD_COMMAND   : std_logic_vector((DATA_WIDTH/8)-1 downto 0);
signal CMD_SRC_RDY   : std_logic;
signal CMD_DST_RDY   : std_logic;

signal FL_DATA       : std_logic_vector(DATA_WIDTH-1 downto 0);
signal FL_REM        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal FL_SOF_N      : std_logic;
signal FL_EOF_N      : std_logic;
signal FL_SOP_N      : std_logic;
signal FL_EOP_N      : std_logic;
signal FL_SRC_RDY_N  : std_logic;
signal FL_DST_RDY_N  : std_logic;

begin

uut: entity work.FL2CMD
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      HEADER         => True,
      FOOTER         => True
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      --
      FL_DATA        => FL_DATA,
      FL_REM         => FL_REM,
      FL_SOF_N       => FL_SOF_N,
      FL_EOF_N       => FL_EOF_N,
      FL_SOP_N       => FL_SOP_N,
      FL_EOP_N       => FL_EOP_N,
      FL_SRC_RDY_N   => FL_SRC_RDY_N,
      FL_DST_RDY_N   => FL_DST_RDY_N,
      --
      CMD_DATA       => CMD_DATA,
      CMD_COMMAND    => CMD_COMMAND,
      CMD_SRC_RDY    => CMD_SRC_RDY,
      CMD_DST_RDY    => CMD_DST_RDY
   );

clkgen: process
   begin
   CLK <= '1';
   wait for clkper/2;
   CLK <= '0';
   wait for clkper/2;
   end process;

tb: process
   begin

   FL_DATA(15 downto 8)   <= "00000000";
   FL_DATA(7 downto 0)    <= "00000000";
   FL_REM         <= "1";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '1';
   FL_EOP_N       <= '1';
   FL_SRC_RDY_N   <= '1';
   CMD_DST_RDY    <= '0';
   reset          <= '1';

   wait for 1 us;
   wait for 2 ns;
   reset          <= '0';
   wait for 10*clkper;

   FL_SRC_RDY_N   <= '0';
   CMD_DST_RDY    <= '1';

   -- Header
   FL_DATA(15 downto 8)   <= "00000001";
   FL_DATA(7 downto 0)    <= "00000000";
   FL_REM         <= "1";
   FL_SOF_N       <= '0';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '0';
   FL_EOP_N       <= '1';
   wait for clkper;

   FL_DATA(15 downto 8)   <= "00000011";
   FL_DATA(7 downto 0)    <= "00000010";
   FL_REM         <= "0";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '1';
   FL_EOP_N       <= '0';
   wait for clkper;

   -- Payload
   FL_DATA(15 downto 8)   <= "00000101";
   FL_DATA(7 downto 0)    <= "00000100";
   FL_REM         <= "1";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '0';
   FL_EOP_N       <= '1';
   wait for clkper;

   FL_DATA(15 downto 8)   <= "00000111";
   FL_DATA(7 downto 0)    <= "00000110";
   FL_REM         <= "1";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '1';
   FL_EOP_N       <= '1';
   wait for clkper;
   wait for clkper;
   CMD_DST_RDY    <= '0';

   FL_DATA(15 downto 8)   <= "00001001";
   FL_DATA(7 downto 0)    <= "00001000";
   FL_REM         <= "0";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '1';
   FL_EOP_N       <= '0';
   wait for clkper;
   CMD_DST_RDY    <= '1';
   wait for clkper;

   -- Footer
   FL_DATA(15 downto 8)   <= "00001011";
   FL_DATA(7 downto 0)    <= "00001010";
   FL_REM         <= "0";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '0';
   FL_SOP_N       <= '0';
   FL_EOP_N       <= '0';
   wait for clkper;

   -- Idle
   FL_DATA(15 downto 8)   <= "00000000";
   FL_DATA(7 downto 0)    <= "00000000";
   FL_REM         <= "1";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '1';
   FL_EOP_N       <= '1';

--    FL_SRC_RDY_N   <= '1';
--    CMD_DST_RDY    <= '0';

--    wait for clkper*2;

--    FL_SRC_RDY_N   <= '0';
--    CMD_DST_RDY    <= '1';

   -- Header
   FL_DATA(15 downto 8)   <= "00000001";
   FL_DATA(7 downto 0)    <= "00000000";
   FL_REM         <= "1";
   FL_SOF_N       <= '0';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '0';
   FL_EOP_N       <= '1';
   wait for clkper;
   wait for clkper;

   FL_DATA(15 downto 8)   <= "00000011";
   FL_DATA(7 downto 0)    <= "00000010";
   FL_REM         <= "1";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '1';
   FL_EOP_N       <= '0';
   wait for clkper;
   wait for clkper;

   FL_SRC_RDY_N   <= '1';
   wait for clkper;
   FL_SRC_RDY_N   <= '0';

   -- Payload
   FL_DATA(15 downto 8)   <= "00000101";
   FL_DATA(7 downto 0)    <= "00000100";
   FL_REM         <= "1";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '0';
   FL_EOP_N       <= '1';
   wait for clkper;

   FL_DATA(15 downto 8)   <= "00000111";
   FL_DATA(7 downto 0)    <= "00000110";
   FL_REM         <= "1";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '1';
   FL_EOP_N       <= '1';
   wait for clkper;
   wait for clkper;
   wait for clkper;

   FL_DATA(15 downto 8)   <= "00001001";
   FL_DATA(7 downto 0)    <= "00001000";
   FL_REM         <= "1";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '1';
   FL_EOP_N       <= '0';
   wait for clkper;

   -- Footer
   FL_DATA(15 downto 8)   <= "00001011";
   FL_DATA(7 downto 0)    <= "00001010";
   FL_REM         <= "1";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '0';
   FL_SOP_N       <= '0';
   FL_EOP_N       <= '0';
   wait for clkper;

   -- Idle
   FL_DATA(15 downto 8)   <= "00000000";
   FL_DATA(7 downto 0)    <= "00000000";
   FL_REM         <= "1";
   FL_SOF_N       <= '1';
   FL_EOF_N       <= '1';
   FL_SOP_N       <= '1';
   FL_EOP_N       <= '1';

   FL_SRC_RDY_N   <= '1';
   wait for 4*clkper;
   CMD_DST_RDY    <= '0';

   wait;
   end process;

end;
