-- out_debug.vhd:
-- Copyright (C) 2003 CESNET, Liberouter project
-- Author(s): Jan Korenek <korenek@liberouter.org>
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
-- TODO: -

library IEEE;
use IEEE.std_logic_1164.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

entity UH_FIFO is
   port(
      RESET           : in std_logic;
      -- LUP interface
      LUP_SR_VALID    : out std_logic;       -- If cell contains unfied header
      LUP_SR_CLEAN    : in  std_logic;       -- Clean addressed cell
      LUP_DATA        : out std_logic_vector(31 downto 0); -- UH data
      LUP_ADDR        : in  std_logic_vector(8 downto 0);  -- Cell addr.
      LUP_CLK         : in  std_logic;
      -- Address Decoder interface
      LBCLK          : in  std_logic;
      ADC_RW         : in  std_logic;
      ADC_EN         : in  std_logic;
      ADC_ADDR       : in  std_logic_vector(10 downto 0);
      ADC_DI         : in  std_logic_vector(15 downto 0);
      ADC_DO         : out std_logic_vector(15 downto 0);
      ADC_DRDY       : out std_logic
   );
end UH_FIFO;

architecture full of UH_FIFO is
-- ---------------------- BlockRAM component ----------------------------
component RAMB16_S18_S36
   port (
      ADDRA: IN std_logic_vector(9 downto 0);
      ADDRB: IN std_logic_vector(8 downto 0);
      DIA:   IN std_logic_vector(15 downto 0);
      DIB:   IN std_logic_vector(31 downto 0);
      DIPA:  IN std_logic_vector(1 downto 0);
      DIPB:  IN std_logic_vector(3 downto 0);
      WEA:   IN std_logic;
      WEB:   IN std_logic;
      CLKA:  IN std_logic;
      CLKB:  IN std_logic;
      SSRA:  IN std_logic;
      SSRB:  IN std_logic;
      ENA:   IN std_logic;
      ENB:   IN std_logic;
      DOA:   OUT std_logic_vector(15 downto 0);
      DOB:   OUT std_logic_vector(31 downto 0);
      DOPA:  OUT std_logic_vector(1 downto 0);
      DOPB:  OUT std_logic_vector(3 downto 0));
end component;

-- --------------------- Dual port flags component -----------------------
component DP_REGFLAGS
   generic(
      EXADDR   : integer
   );
	port(
      RESET    : in  std_logic;
      -- SET part
      CLK_SET  : in  std_logic;
      SET      : in  std_logic;
      ADDR_SET : in  std_logic_vector(EXADDR-1 downto 0);
      DO_SET   : out std_logic;
      -- CLR part
      CLK_CLR  : in  std_logic;
      CLR      : in  std_logic;
      ADDR_CLR : in  std_logic_vector(EXADDR-1 downto 0);
      DO_CLR   : out std_logic;

      DO_ALL   : out std_logic_vector((2**EXADDR)-1 downto 0)
	);
end component;

-- --------------------- Signals declaration -----------------------

-- Output data multiplex
signal uh_data_do       : std_logic_vector(15 downto 0);
signal uh_sor_do        : std_logic;
signal uh_sor_set       : std_logic;
signal uh_mx_do         : std_logic_vector(15 downto 0);

-- Address multiplex
signal reg_adc_addr     : std_logic_vector(10 downto 0);
signal reg_adc_en       : std_logic;
signal reg1_adc_en      : std_logic;
signal reg_uh_sor_do    : std_logic;
signal reg_uh_data_do   : std_logic_vector(15 downto 0);

signal bram_we          : std_logic;

begin

-- -------------------------------------------------------------------
--                  Address decoder part
-- -------------------------------------------------------------------

-- reg_adc_flags register
process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_adc_addr   <= (others => '0');
      reg_uh_data_do <= (others => '0');
      reg_uh_sor_do  <= '0';
      reg_adc_en     <= '0';
      reg1_adc_en    <= '0';
   elsif (LBCLK'event AND LBCLK = '1') then
      reg_adc_addr   <= ADC_ADDR;
      reg_uh_data_do <= uh_data_do;
      reg_uh_sor_do  <= uh_sor_do;
      reg_adc_en     <= ADC_EN;
      reg1_adc_en    <= reg_adc_en;
   end if;
end process;

-- output data multiplexor
with reg_adc_addr (10) select
   uh_mx_do   <=  uh_data_do                       when '0',
                  (15 downto 0 => reg_uh_sor_do)  when others;

-- Address decoder output
ADC_DO         <= uh_mx_do;
ADC_DRDY       <= reg_adc_en;

bram_we        <= ADC_RW and ADC_EN and (not (ADC_ADDR(10)));
-- ------------------------------------
-- UH data
block_ram: RAMB16_S18_S36 port map(
      -- Local bus part
      CLKA  => LBCLK,
      ENA   => '1',
      WEA   => bram_we,
      ADDRA => ADC_ADDR(9 downto 0),
      DIA   => ADC_DI,
      DIPA  => (1 downto 0 => '0'),
      DOA   => uh_data_do,
      DOPA  => open,
      SSRA  => '0',
      -- Port B
      CLKB  => LUP_CLK,
      ENB   => '1',
      WEB   => '0',
      ADDRB => LUP_ADDR,
      DIB   => (31 downto 0 => '0'),
      DIPB  => "0000",
      DOB   => LUP_DATA,
      DOPB  => open,
      SSRB  => '0'
);

-- ----------------------------------
-- dp_reg_flags instantion
flags: dp_regflags
generic map(
   EXADDR => 4
)
port map(
   RESET       => RESET,
   -- SET part
   CLK_SET     => LBCLK,
   SET         => uh_sor_set,
   ADDR_SET    => ADC_ADDR(3 downto 0),
   DO_SET      => uh_sor_do,
   -- CLR part
   CLK_CLR     => LUP_CLK,
   CLR         => LUP_SR_CLEAN,
   ADDR_CLR    => LUP_ADDR(8 downto 5),
   DO_CLR      => LUP_SR_VALID,
   -- Output
   DO_ALL      => open
);
uh_sor_set  <= ADC_ADDR(10) and (ADC_DI(0) and ADC_RW and ADC_EN);


-- -------------------------------------------------------------------
end full;

