-- testbench.vhd: lb_switch testbench
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

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;
use ieee.std_logic_arith.all;

library work;

ENTITY testbench IS
END testbench;

ARCHITECTURE testbench OF testbench IS

constant clkper :time := 10 ns;
constant PORT_COUNT : integer := 3;

signal lb_clk        : std_logic;
signal lb_reset      : std_logic;
      
      -- upstream link
signal port0_dwr     : std_logic_vector(15 downto 0);
signal port0_be      : std_logic_vector(1 downto 0);
signal port0_ads_n   : std_logic;
signal port0_rd_n    : std_logic;
signal port0_wr_n    : std_logic;
signal port0_drd     : std_logic_vector(15 downto 0);
signal port0_rdy_n   : std_logic;
signal port0_err_n   : std_logic;
signal port0_abort_n : std_logic;

      -- Assigned to one of downstream links
signal port1_dwr     : std_logic_vector(15 downto 0);
signal port1_be      : std_logic_vector(1 downto 0);
signal port1_ads_n   : std_logic;
signal port1_rd_n    : std_logic;
signal port1_wr_n    : std_logic;
signal port1_drd     : std_logic_vector(15 downto 0);
signal port1_rdy_n   : std_logic;
signal port1_err_n   : std_logic;
signal port1_abort_n : std_logic;

      -- Assigned to one of downstream links
signal port2_dwr     : std_logic_vector(15 downto 0);
signal port2_be      : std_logic_vector(1 downto 0);
signal port2_ads_n   : std_logic;
signal port2_rd_n    : std_logic;
signal port2_wr_n    : std_logic;
signal port2_drd     : std_logic_vector(15 downto 0);
signal port2_rdy_n   : std_logic;
signal port2_err_n   : std_logic;
signal port2_abort_n : std_logic;

      -- Assigned to one of downstream links
signal port3_dwr     : std_logic_vector(15 downto 0);
signal port3_be      : std_logic_vector(1 downto 0);
signal port3_ads_n   : std_logic;
signal port3_rd_n    : std_logic;
signal port3_wr_n    : std_logic;
signal port3_drd     : std_logic_vector(15 downto 0);
signal port3_rdy_n   : std_logic;
signal port3_err_n   : std_logic;
signal port3_abort_n : std_logic;

begin

   uut: entity work.LB_SWITCH_NOREC
   generic map(
      PORT_COUNT  => PORT_COUNT
   )
   port map(
      LB_CLK        => LB_CLK,
      LB_RESET      => LB_RESET,
                       
      -- Upstream port
      PORT0_DWR     => port0_dwr,
      PORT0_BE      => port0_be,
      PORT0_ADS_N   => port0_ads_n,
      PORT0_RD_N    => port0_rd_n,
      PORT0_WR_N    => port0_wr_n,
      PORT0_DRD     => port0_drd,
      PORT0_RDY_N   => port0_rdy_n,
      PORT0_ERR_N   => port0_err_n,
      PORT0_ABORT_N => port0_abort_n,
                                    
      -- Downstream ports
      DWR(15 downto 0)  => port1_dwr,
      DWR(31 downto 16) => port2_dwr,
      DWR(47 downto 32) => port3_dwr,
      BE(1 downto 0)    => port1_be,
      BE(3 downto 2)    => port2_be,
      BE(5 downto 4)    => port3_be,
      ADS_N(0)          => port1_ads_n,
      ADS_N(1)          => port2_ads_n,
      ADS_N(2)          => port3_ads_n,
      RD_N(0)           => port1_rd_n,
      RD_N(1)           => port2_rd_n,
      RD_N(2)           => port3_rd_n,
      WR_N(0)           => port1_wr_n,
      WR_N(1)           => port2_wr_n,
      WR_N(2)           => port3_wr_n,
      DRD(15 downto 0)  => port1_drd,
      DRD(31 downto 16) => port2_drd,
      DRD(47 downto 32) => port3_drd,
      RDY_N(0)          => port1_rdy_n,
      RDY_N(1)          => port2_rdy_n,
      RDY_N(2)          => port3_rdy_n,
      ERR_N(0)          => port1_err_n,
      ERR_N(1)          => port2_err_n,
      ERR_N(2)          => port3_err_n,
      ABORT_N(0)        => port1_abort_n,
      ABORT_N(1)        => port2_abort_n,
      ABORT_N(2)        => port3_abort_n
   );


   clock_p : process
   begin
      LB_CLK <= '1';
      wait for clkper/2;
      LB_CLK <= '0';
      wait for clkper/2;
   end process;

   test : process
   begin
      LB_RESET <= '1';

      port0_dwr <= X"0000";
      port0_be <= "00";
      port0_ads_n <= '1';
      port0_rd_n <= '1';
      port0_wr_n <= '1';
      port0_abort_n <= '1';

      port1_drd <= X"0000";
      port1_rdy_n <= '1';
      port1_err_n <= '1';

      port2_drd <= X"0000";
      port2_rdy_n <= '1';
      port2_err_n <= '1';

      port3_drd <= X"0000";
      port3_rdy_n <= '1';
      port3_err_n <= '1';

      wait for 1 ns;
      wait for 5*clkper;

      LB_RESET <= '0';

      -- Send data 0x12345678 to address 0x4
      port0_dwr <= X"0004";
      port0_be <= "11";
      port0_ads_n <= '0';
      wait for clkper;
      port0_dwr <= X"0000";
      wait for clkper;
      port0_ads_n <= '1';
      port0_wr_n <= '0';
      port0_dwr <= X"5678";
      wait for clkper;
      port0_dwr <= X"1234";
      wait for clkper;
      port0_wr_n <= '1';
      wait for 5*clkper;
      
      -- Send read request for 32bits from address 0x8
      port0_dwr <= X"0008";
      port0_ads_n <= '0';
      wait for clkper;
      port0_dwr <= X"0000";
      wait for clkper;
      port0_ads_n <= '1';
      port0_rd_n <= '0';
      wait for 2*clkper;
      port0_rd_n <= '1';
      wait for 2*clkper;

      -- Reply from port1: data 0xABCDEF01
      -- WHILE port2 has IDLE 0xFFFF !!!
      port1_rdy_n <= '0';
      port1_drd <= X"EF01";
      port2_drd <= X"FFFF";
      wait for clkper;
      port1_drd <= X"ABCD";
      wait for clkper;
      port1_rdy_n <= '1';
      wait for 5*clkper;

      -- Send read request for 32bits from address 0xC
      port0_dwr <= X"000C";
      port0_ads_n <= '0';
      wait for clkper;
      port0_dwr <= X"0000";
      wait for clkper;
      port0_ads_n <= '1';
      port0_rd_n <= '0';
      wait for 2*clkper;
      port0_rd_n <= '1';
      wait for 1*clkper;

      -- Reply from port1: data 0xABCDEF01
      -- WHILE port2 has ACTIVE 0xFFFFAAAA !!!
      port1_rdy_n <= '0';
      port2_rdy_n <= '0';
      port1_drd <= X"EF01";
      port2_drd <= X"FFFF";
      wait for clkper;
      port1_drd <= X"ABCD";
      port2_drd <= X"AAAA";
      wait for clkper;
      port1_rdy_n <= '1';
      port2_rdy_n <= '1';
      wait for 5*clkper;

      -- Test ABORT_N propagation
      port0_abort_n <= '0';
      wait for clkper;
      port0_abort_n <= '1';
      wait for clkper;

      -- Test ERR_N propagation
      port3_err_n <= '0';
      wait for clkper;
      port3_err_n <= '1';

      wait;
   end process;

end architecture;
