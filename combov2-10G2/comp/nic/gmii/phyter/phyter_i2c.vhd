-- phyter_i2c.vhd: Phyter control & status component.
-- Copyright (C) 2006 CESNET
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
-- TODO:
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

-- pragma translate_off
library UNISIM;
use UNISIM.VCOMPONENTS.all;
-- pragma translate_on

-- ------------------------------------------------------------------------
--                      Architecture declaration
-- ------------------------------------------------------------------------
architecture full of PHYTER_I2C is

   type phy_wr_arr   is array(3 downto 0) of std_logic_vector(4 downto 0);
   type phy_rd_arr   is array(3 downto 0) of std_logic_vector(1 downto 0);
   type logic_arr    is array(3 downto 0) of std_logic;

   constant LB_ADDR_WIDTH  : integer := 2;

   -- adc2lb signals
   signal adc_rd     : std_logic;
   signal adc_wr     : std_logic;
   signal adc_addr   : std_logic_vector(LB_ADDR_WIDTH-2 downto 0);
   signal adc_di     : std_logic_vector(31 downto 0);
   signal adc_do     : std_logic_vector(31 downto 0);

   -- lbconn_mem signals
   signal data_out   : std_logic_vector(15 downto 0);
   signal data_in    : std_logic_vector(15 downto 0);
   signal addr       : std_logic_vector(LB_ADDR_WIDTH-1 downto 0);
   signal rw         : std_logic;
   signal en         : std_logic;
   signal drdy       : std_logic;

   signal write      : logic_arr;
   signal reg_write  : logic_arr;
   signal i2c_scl    : logic_arr;
   signal i2c_sda    : logic_arr;

   signal phy_rd     : phy_rd_arr;
   signal reg_phy_rd : phy_rd_arr;
   signal reg_phy_wr : phy_wr_arr;

   -- ---------------------------------------------------------------------

begin

   adc_do <= '0' & reg_phy_wr(3) & reg_phy_rd(3)
      & '0' & reg_phy_wr(2) & reg_phy_rd(2)
      & '0' & reg_phy_wr(1) & reg_phy_rd(1)
      & '0' & reg_phy_wr(0) & reg_phy_rd(0);

   gen_write: for i in 0 to 3 generate
      write(i) <= '1'
         when adc_di(2 + 8*i) = '1' and adc_wr = '1' and
            conv_integer(adc_addr) = 0
         else '0';
   end generate;

   i2c_scl(0)  <= SCL0;
   i2c_scl(1)  <= SCL1;
   i2c_scl(2)  <= SCL2;
   i2c_scl(3)  <= SCL3;

   i2c_sda(0)  <= SDA0;
   i2c_sda(1)  <= SDA1;
   i2c_sda(2)  <= SDA2;
   i2c_sda(3)  <= SDA3;

   -- enable phyters
   PHDISA   <= '0';
   PHDISB   <= '0';
   PHDISC   <= '0';
   PHDISD   <= '0';

   -- ---------------------------------------------------------------------
   --                   Components
   -- ---------------------------------------------------------------------
   LB_CONNECTION: entity work.LBCONN_MEM
      generic map(
         BASE        => BASE,
         ADDR_WIDTH  => LB_ADDR_WIDTH
      )
      port map(
         DATA_OUT => data_out,
         DATA_IN  => data_in,
         ADDR     => addr,
         RW       => rw,
         EN       => en,
         SEL      => open,
         DRDY     => drdy,
         ARDY     => '1',
         --
         reset    => RESET,
         lbclk    => LBCLK,
         lbframe  => LBFRAME,
         lbas     => LBAS,
         lbrw     => LBRW,
         lblast   => LBLAST,
         lbad     => LBAD,
         lbholda  => LBHOLDA,
         lbrdy    => LBRDY
      );

   ADC2LB_U: entity work.ADC2LB
      generic map(
         ADDR_WIDTH  => LB_ADDR_WIDTH,
         FREQUENCY   => 100
      )
      port map(
         RESET    => RESET,
         --
         CLK      => CLK,
         ADC_RD   => adc_rd,
         ADC_WR   => adc_wr,
         ADC_ADDR => adc_addr,
         ADC_DI   => adc_di,
         ADC_DO   => adc_do,
         ADC_DRDY => '1',
         --
         LBCLK    => LBCLK,
         LB_EN    => en,
         LB_RW    => rw,
         LB_ADDR  => addr,
         LB_DI    => data_out,
         LB_DO    => data_in,
         LB_DRDY  => drdy
      );

   gen_i2c_sw: for i in 0 to 3 generate
      I2C_SW_U: entity work.I2C_SW
         port map(
            CLK         => CLK,
            RESET       => RESET,
            --
            WR_DATA     => reg_phy_wr(i)(4),
            WR_DATA_Z   => reg_phy_wr(i)(3),
            WR_CLK      => reg_phy_wr(i)(2),
            WR_CLK_Z    => reg_phy_wr(i)(1),
            WRITE       => reg_write(i),
            --
            RD_DATA     => phy_rd(i)(1),
            RD_CLK      => phy_rd(i)(0),
            --
            I2C_CLK     => i2c_scl(i),
            I2C_DATA    => i2c_sda(i)
         );
   end generate;

   -- ---------------------------------------------------------------------
   --                   Registers
   -- ---------------------------------------------------------------------
   gen_reg_phy: for i in 0 to 3 generate

      reg_phy_wrp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_phy_wr(i) <= (others => '0');
         elsif (CLK'event AND CLK = '1') then
            if (write(i) = '1') then
               reg_phy_wr(i) <= adc_di(6 + 8*i) & adc_di(5 + 8*i) &
               adc_di(4 + 8*i) & adc_di(3 + 8*i) & write(i);
            end if;
         end if;
      end process;

      reg_phy_rdp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_phy_rd(i) <= (others => '0');
         elsif (CLK'event AND CLK = '1') then
            reg_phy_rd(i) <= phy_rd(i);
         end if;
      end process;

      reg_writep: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_write(i) <= '0';
         elsif (CLK'event AND CLK = '1') then
            reg_write(i) <= write(i);
         end if;
      end process;

   end generate;

   -- ---------------------------------------------------------------------

end architecture full;
