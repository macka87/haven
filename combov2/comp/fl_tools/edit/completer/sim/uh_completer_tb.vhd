-- uh_completer_tb.vhd: FlowMon UH completer testbench file
-- Copyright (C) 2007 CESNET
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

-- package with FL records
use work.fl_pkg.all;
-- package with LB records
use work.lb_pkg.all;

entity testbench is
end testbench;

architecture testbench of testbench is

constant CLKPER   : time   := 8 ns;

signal clk     : std_logic;
signal reset   : std_logic;

signal di      : t_fl32;
signal do      : t_fl32;
signal mi      : t_mi32;

signal uh_di   : t_fl32;
signal uh_do   : t_fl16;
signal uh_mi   : t_mi32;

begin

uut: entity work.completer
   generic map(
      DATA_SIZE   => 128,
      DATA_WIDTH  => 32
   )
   port map(
      CLK      => clk,
      RESET    => reset,
      --
      IN_DATA        => di.data,
      IN_REM         => di.drem,
      IN_SOF_N       => di.sof_n,
      IN_EOF_N       => di.eof_n,
      IN_SOP_N       => di.sop_n,
      IN_EOP_N       => di.eop_n,
      IN_SRC_RDY_N   => di.src_rdy_n,
      IN_DST_RDY_N   => di.dst_rdy_n,
      --
      OUT_DATA       => do.data,
      OUT_REM        => do.drem,
      OUT_SOF_N      => do.sof_n,
      OUT_EOF_N      => do.eof_n,
      OUT_SOP_N      => do.sop_n,
      OUT_EOP_N      => do.eop_n,
      OUT_SRC_RDY_N  => do.src_rdy_n,
      OUT_DST_RDY_N  => do.dst_rdy_n,
      --
      MI       => mi
   );

uut_uh: entity work.uh_completer
   generic map(
      UH_SIZE  => 64
   )
   port map(
      CLK      => clk,
      RESET    => reset,
      --
      DI       => uh_di,
      DO       => uh_do,
      --
      MI       => uh_mi
   );

clkgen: process
   begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
   end process;

tb: process
begin

   -- idle
   di.data        <= (others => '0');
   di.drem        <= (others => '1');
   di.sof_n       <= '1';
   di.eof_n       <= '1';
   di.sop_n       <= '1';
   di.eop_n       <= '1';
   di.src_rdy_n   <= '1';

   do.dst_rdy_n   <= '0';

   mi.dwr         <= (others => '0');
   mi.addr        <= (others => '0');
   mi.rd          <= '0';
   mi.wr          <= '0';
   mi.be          <= (others => '1');

   reset <= '1';
   wait for 0.5 us;
   wait for 2 ns;
   reset <= '0';
   wait for 10*clkper;

   -- frame
   di.data(15 downto 0)    <= (others => '0');
   di.data(31 downto 16)   <= (others => '0');
   di.sof_n        <= '0';
   di.eof_n        <= '1';
   di.sop_n        <= '0';
   di.eop_n        <= '1';
   di.src_rdy_n    <= '0';
   wait for clkper;
   di.data(15 downto 0)    <= (others => '0');
   di.data(31 downto 16)   <= (others => '1');
   di.sof_n        <= '1';
   di.eof_n        <= '1';
   di.sop_n        <= '1';
   di.eop_n        <= '1';
   di.src_rdy_n    <= '0';
   wait for clkper;
   -- wait
   di.src_rdy_n    <= '1';
   wait for clkper;
   wait for clkper;
   -- 128 B
   for i in 1 to 30 loop
      di.data(15 downto 0)    <= conv_std_logic_vector(i, 16);
      di.data(31 downto 16)   <= conv_std_logic_vector(i, 16);
      di.sof_n        <= '1';
      di.eof_n        <= '1';
      di.sop_n        <= '1';
      di.eop_n        <= '1';
      di.src_rdy_n    <= '0';
      wait for clkper;
      if (i = 9) then
         -- wait
         di.src_rdy_n   <= '1';
         wait for clkper;
      end if;
      di.data(15 downto 0)    <= conv_std_logic_vector(i, 16);
      di.data(31 downto 16)   <= (others => '1');
      di.sof_n        <= '1';
      di.eof_n        <= '1';
      di.sop_n        <= '1';
      di.eop_n        <= '1';
      di.src_rdy_n    <= '0';
      wait for clkper;
   end loop;
   di.data(15 downto 0)    <= conv_std_logic_vector(31, 16);
   di.data(31 downto 16)   <= conv_std_logic_vector(31, 16);
   di.sof_n        <= '1';
   di.eof_n        <= '1';
   di.sop_n        <= '1';
   di.eop_n        <= '1';
   di.src_rdy_n    <= '0';
   wait for clkper;
   di.data(15 downto 0)    <= conv_std_logic_vector(31, 16);
   di.data(31 downto 16)   <= (others => '0');
   di.sof_n        <= '1';
   di.eof_n        <= '0';
   di.sop_n        <= '1';
   di.eop_n        <= '0';
   di.src_rdy_n    <= '0';
   wait for clkper;
   di.src_rdy_n   <= '1';
   -- end of frame

   -- frame
   di.data(15 downto 0)    <= (others => '0');
   di.data(31 downto 16)   <= conv_std_logic_vector(31, 16);
   di.sof_n        <= '0';
   di.eof_n        <= '1';
   di.sop_n        <= '0';
   di.eop_n        <= '1';
   di.src_rdy_n    <= '0';
   wait for clkper;
   di.data(15 downto 0)    <= conv_std_logic_vector(31, 16);
   di.data(31 downto 16)   <= (others => '1');
   di.sof_n        <= '1';
   di.eof_n        <= '1';
   di.sop_n        <= '1';
   di.eop_n        <= '1';
   di.src_rdy_n    <= '0';
   wait for clkper;
   -- 128 B
   for i in 1 to 30 loop
      di.data(15 downto 0)    <= conv_std_logic_vector(i, 16);
      di.data(31 downto 16)   <= conv_std_logic_vector(31-i, 16);
      di.sof_n        <= '1';
      di.eof_n        <= '1';
      di.sop_n        <= '1';
      di.eop_n        <= '1';
      di.src_rdy_n    <= '0';
      wait for clkper;
      di.data(15 downto 0)    <= conv_std_logic_vector(31-i, 16);
      di.data(31 downto 16)   <= (others => '1');
      di.sof_n        <= '1';
      di.eof_n        <= '1';
      di.sop_n        <= '1';
      di.eop_n        <= '1';
      di.src_rdy_n    <= '0';
      wait for clkper;
   end loop;
   di.data(15 downto 0)    <= conv_std_logic_vector(31, 16);
   di.data(31 downto 16)   <= conv_std_logic_vector(0, 16);
   di.sof_n        <= '1';
   di.eof_n        <= '1';
   di.sop_n        <= '1';
   di.eop_n        <= '1';
   di.src_rdy_n    <= '0';
   wait for clkper;
   di.data(15 downto 0)    <= conv_std_logic_vector(0, 16);
   di.data(31 downto 16)   <= (others => '1');
   di.sof_n        <= '1';
   di.eof_n        <= '0';
   di.sop_n        <= '1';
   di.eop_n        <= '0';
   di.src_rdy_n    <= '0';
   wait for clkper;
   di.src_rdy_n   <= '1';
   -- end of frame

   wait for 10*clkper;

   -- idle
   di.data        <= (others => '0');
   di.drem        <= (others => '1');
   di.sof_n       <= '1';
   di.eof_n       <= '1';
   di.sop_n       <= '1';
   di.eop_n       <= '1';
   di.src_rdy_n   <= '1';

   do.dst_rdy_n   <= '0';

   wait;
   end process;

tb_uh: process
begin

   -- idle
   uh_di.data        <= (others => '0');
   uh_di.drem        <= (others => '1');
   uh_di.sof_n       <= '1';
   uh_di.eof_n       <= '1';
   uh_di.sop_n       <= '1';
   uh_di.eop_n       <= '1';
   uh_di.src_rdy_n   <= '1';

   uh_do.dst_rdy_n   <= '0';

   uh_mi.dwr         <= (others => '0');
   uh_mi.addr        <= (others => '0');
   uh_mi.rd          <= '0';
   uh_mi.wr          <= '0';
   uh_mi.be          <= (others => '1');

   -- wait for reset
   wait for 0.5 us;
   wait for 2 ns;
   wait for 10*clkper;

   -- frame
   uh_di.data(15 downto 0)    <= conv_std_logic_vector(63, 16);
   uh_di.data(31 downto 16)   <= (others => '0');
   uh_di.sof_n        <= '0';
   uh_di.eof_n        <= '1';
   uh_di.sop_n        <= '0';
   uh_di.eop_n        <= '1';
   uh_di.src_rdy_n    <= '0';
   wait for clkper;
   -- 64 B
   for i in 1 to 30 loop
      uh_di.data(15 downto 0)    <= conv_std_logic_vector(63-i, 16);
      uh_di.data(31 downto 16)   <= conv_std_logic_vector(i, 16);
      uh_di.sof_n        <= '1';
      uh_di.eof_n        <= '1';
      uh_di.sop_n        <= '1';
      uh_di.eop_n        <= '1';
      uh_di.src_rdy_n    <= '0';
      wait for clkper;
   end loop;
   uh_di.data(15 downto 0)    <= conv_std_logic_vector(32, 16);
   uh_di.data(31 downto 16)   <= conv_std_logic_vector(31, 16);
   uh_di.sof_n        <= '1';
   uh_di.eof_n        <= '0';
   uh_di.sop_n        <= '1';
   uh_di.eop_n        <= '0';
   uh_di.src_rdy_n    <= '0';
   wait for clkper;
   uh_di.src_rdy_n   <= '1';
   -- end of frame

   wait for 10*clkper;

   -- idle
   uh_di.data        <= (others => '0');
   uh_di.drem        <= (others => '1');
   uh_di.sof_n       <= '1';
   uh_di.eof_n       <= '1';
   uh_di.sop_n       <= '1';
   uh_di.eop_n       <= '1';
   uh_di.src_rdy_n   <= '1';

   uh_do.dst_rdy_n   <= '0';

   wait;
   end process;

end;
