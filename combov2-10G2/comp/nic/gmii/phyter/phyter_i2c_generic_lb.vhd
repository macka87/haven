-- phyter_i2c_generic_lb.vhd: Phyter control & status component
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

library IEEE;
use IEEE.std_logic_1164.all;

use work.lb_pkg.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity PHYTER_I2C_GENERIC_LB is
   generic(
      BASE     : integer;     -- LB base address
      IFC_CNT  : integer := 4
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      -- I2C interfaces
      SCL      : inout std_logic_vector(IFC_CNT-1 downto 0);
      SDA      : inout std_logic_vector(IFC_CNT-1 downto 0);

      -- Phyter disable signals
      PHDIS    : out std_logic_vector(IFC_CNT-1 downto 0);

      -- Localbus interface
      LBCLK    : in    std_logic;
      LBFRAME  : in    std_logic;
      LBHOLDA  : out   std_logic;
      LBAD     : inout std_logic_vector(15 downto 0);
      LBAS     : in    std_logic;
      LBRW     : in    std_logic;
      LBRDY    : out   std_logic;
      LBLAST   : in    std_logic
   );
end entity PHYTER_I2C_GENERIC_LB;

-- ------------------------------------------------------------------------
--                      Architecture declaration
-- ------------------------------------------------------------------------
architecture full of PHYTER_I2C_GENERIC_LB is

   constant LB_ADDR_WIDTH  : integer := 2+(IFC_CNT-1)/8;

   -- adc2lb signals
   signal adc_rd     : std_logic;
   signal adc_wr     : std_logic;
   signal adc_drdy   : std_logic;
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

   signal sig_mi     : t_mi32;

begin

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
         ADC_DRDY => adc_drdy,
         --
         LBCLK    => LBCLK,
         LB_EN    => en,
         LB_RW    => rw,
         LB_ADDR  => addr,
         LB_DI    => data_out,
         LB_DO    => data_in,
         LB_DRDY  => drdy
      );

   sig_mi.ADDR(31 downto LB_ADDR_WIDTH+1) <= (others => '0');
   sig_mi.ADDR(LB_ADDR_WIDTH downto 2)    <= adc_addr;
   sig_mi.ADDR(1 downto 0)                <= "00";
   sig_mi.WR   <= adc_wr;
   sig_mi.RD   <= adc_rd;
   sig_mi.DWR  <= adc_di;
   sig_mi.BE   <= "1111";
   adc_do      <= sig_mi.DRD;
   adc_drdy    <= sig_mi.DRDY;

   PHYTER_I2C_MI32_I: entity work.phyter_i2c_generic
   generic map(
      IFC_CNT  => IFC_CNT
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,
      --
      SCL      => SCL,
      SDA      => SDA,
      --
      PHDIS    => PHDIS,
      --
      MI32     => sig_mi
   );

end architecture full;
