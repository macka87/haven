-- testbench.vhd: Testbench of top level entity
-- Copyright (C) 2009 CESNET
-- Author(s): Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;


-- ----------------------------------------------------------------------------
--                           Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- -------------------------------------------------------------------------
   --                              Constants
   -- -------------------------------------------------------------------------
   
   -- period of generated clock signal
   constant clk_period  : time := 8 ns;
   
   -- -------------------------------------------------------------------------
   --                                Signals
   -- -------------------------------------------------------------------------

   ---------- Common Signals ----------
   -- 125 MHz clock signal
   signal clk           : std_logic;
   -- reset signal
   signal reset         : std_logic;

   signal mi32_dwr      : std_logic_vector(31 downto 0);
   signal mi32_addr     : std_logic_vector(31 downto 0);
   signal mi32_rd       : std_logic;
   signal mi32_wr       : std_logic;
   signal mi32_be       : std_logic_vector( 3 downto 0);
   signal mi32_drd      : std_logic_vector(31 downto 0);
   signal mi32_adry     : std_logic;
   signal mi32_drdy     : std_logic;

   ---------- Host Bus interface ----------
   signal emac0hostclk       : std_logic;
   signal emac0hostopcode    : std_logic_vector(1 downto 0);
   signal emac0hostaddr      : std_logic_vector(9 downto 0);
   signal emac0hostwrdata    : std_logic_vector(31 downto 0);
   signal emac0hostrddata    : std_logic_vector(31 downto 0);
   signal emac0hostmiimsel   : std_logic;
   signal emac0hostemac1sel  : std_logic;
   signal emac0hostreq       : std_logic;
   signal emac0hostmiimrdy   : std_logic;
   
   ---------- Host Bus interface ----------
   signal emac1hostclk       : std_logic;
   signal emac1hostopcode    : std_logic_vector(1 downto 0);
   signal emac1hostaddr      : std_logic_vector(9 downto 0);
   signal emac1hostwrdata    : std_logic_vector(31 downto 0);
   signal emac1hostrddata    : std_logic_vector(31 downto 0);
   signal emac1hostmiimsel   : std_logic;
   signal emac1hostemac1sel  : std_logic;
   signal emac1hostreq       : std_logic;
   signal emac1hostmiimrdy   : std_logic;
   
-- ----------------------------------------------------------------------------
--                           Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                         Clock generation
   -- -------------------------------------------------------------------------
   -- generation of clock signal with period 8 ns => frequency = 125 MHz
   
   clkgen : process
   begin
      clk <= '1';
      wait for clk_period/2;
      clk <= '0';
      wait for clk_period/2;
   end process clkgen;
   
   -- -------------------------------------------------------------------------
   --                          Unit under test
   -- -------------------------------------------------------------------------
   
   uut : entity work.mdio_emac_mi32_norec
      port map(
         ---------- Common signals ----------
         CLK            => clk,
         RESET          => reset,

         MI32_DWR       => mi32_dwr,
         MI32_ADDR      => mi32_addr,
         MI32_RD        => mi32_rd,
         MI32_WR        => mi32_wr,
         MI32_BE        => mi32_be,
         MI32_DRD       => mi32_drd,
         MI32_ARDY      => mi32_adry,
         MI32_DRDY      => mi32_drdy,

         ---------- Host Bus interface ----------
         EMAC0HOSTCLK        => emac0hostclk,
         EMAC0HOSTOPCODE     => emac0hostopcode,
         EMAC0HOSTADDR       => emac0hostaddr,
         EMAC0HOSTWRDATA     => emac0hostwrdata,
         EMAC0HOSTRDDATA     => emac0hostrddata,
         EMAC0HOSTMIIMSEL    => emac0hostmiimsel,
         EMAC0HOSTEMAC1SEL   => emac0hostemac1sel,
         EMAC0HOSTREQ        => emac0hostreq,
         EMAC0HOSTMIIMRDY    => emac0hostmiimrdy,
   
         ---------- Host Bus interface ----------
         EMAC1HOSTCLK        => emac1hostclk,
         EMAC1HOSTOPCODE     => emac1hostopcode,
         EMAC1HOSTADDR       => emac1hostaddr,
         EMAC1HOSTWRDATA     => emac1hostwrdata,
         EMAC1HOSTRDDATA     => emac1hostrddata,
         EMAC1HOSTMIIMSEL    => emac1hostmiimsel,
         EMAC1HOSTEMAC1SEL   => emac1hostemac1sel,
         EMAC1HOSTREQ        => emac1hostreq,
         EMAC1HOSTMIIMRDY    => emac1hostmiimrdy
      );

   -- -------------------------------------------------------------------------
   --                          Main testbench process
   -- -------------------------------------------------------------------------
   
   tb : process
   begin
      reset <= '1';
      emac0hostrddata <= X"00000000";
      emac0hostmiimrdy <= '0';
      emac1hostrddata <= X"00000000";
      emac1hostmiimrdy <= '0';
      mi32_dwr <= X"00000000";
      mi32_addr <= X"00000000";
      mi32_wr <= '0';
      mi32_rd <= '0';
      mi32_be <= "0000";
      wait for 10*clk_period;
      wait for 2 ns;

      reset <= '0';
      wait for 2100*clk_period;
      
      -- test 1 - write over MDIO bus into EMAC0EMAC0
      mi32_dwr <= X"12345678";
      mi32_addr <= X"00000000";
      mi32_wr <= '1';
      wait for clk_period;

      mi32_wr <= '0';
      wait for 10*clk_period;
      
      -- test 2 - write over MDIO bus into EMAC1EMAC1
      mi32_dwr <= X"12345678";
      mi32_addr <= X"00000034";
      mi32_wr <= '1';
      wait for clk_period;

      mi32_wr <= '0';
      wait for 10*clk_period;

      -- test 3 - read status when busy
      mi32_addr <= X"0000000C";
      mi32_rd <= '1';
      wait for clk_period;

      mi32_rd <= '0';
      wait for clk_period;
      
      -- test 4 - return data from MDIO
      emac0hostmiimrdy <= '1';
      emac0hostrddata <= X"0000ABCD";
      wait for clk_period;
      wait for 10*clk_period;

      -- test 5 - read status when not busy
      mi32_addr <= X"0000000C";
      mi32_rd <= '1';
      wait for clk_period;

      mi32_rd <= '0';
      wait for clk_period;
      
      -- test 6 - read data from MDIO over MI32
      mi32_addr <= X"00000008";
      mi32_rd <= '1';
      wait for clk_period;

      mi32_rd <= '0';
      wait for 10*clk_period;

      -- test 7  - return data from MDIO
      emac1hostmiimrdy <= '1';
      emac1hostrddata <= X"12345678";
      wait for 10*clk_period;

      -- test 8 - read data from MDIO over MI32
      mi32_addr <= X"00000038";
      mi32_rd <= '1';
      wait for clk_period;

      mi32_rd <= '0';
      wait for 10*clk_period;

      -- test 9 - write FFFFFFFF
      mi32_dwr <= X"FFFFFFFF";
      mi32_addr <= X"00000000";
      mi32_wr <= '1';
      wait for clk_period;

      mi32_wr <= '0';


      wait;


   end process tb;
   
end architecture;
