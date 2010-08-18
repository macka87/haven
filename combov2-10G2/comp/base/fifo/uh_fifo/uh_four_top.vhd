-- uh_top.vhd: Unified Header FIFO, top level entity architecture - FULL
-- Copyright (C) 2003-2004 CESNET, Liberouter project
-- Author(s): Filip Hofer fil@liberouter.org
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
use IEEE.std_logic_1164.ALL;
use IEEE.std_logic_arith.ALL;
use IEEE.std_logic_unsigned.ALL;

library unisim;
use unisim.all;

architecture full of UH_FOUR is

component UH_FIFO
   port(
      -- Control signals
      RESET      : in std_logic;

      -- HFE interface
      HFE_DOUT   : in std_logic_vector(15 downto 0); -- SOR data output
      HFE_ADDR   : in std_logic_vector(5 downto 0);  -- SOR address
      HFE_RDY    : out std_logic;   -- Control signals
      HFE_REQ    : in std_logic;
      HFE_WEN    : in std_logic;
      HFE_CLK	  : in std_logic;

      -- LUP interface
      LUP_SR_VALID   : out std_logic;       -- If cell contains unfied header
      LUP_SR_CLEAN   : in  std_logic;       -- Clean addressed cell
      LUP_DATA       : out std_logic_vector(31 downto 0); -- UH data
      LUP_ADDR       : in  std_logic_vector(8 downto 0);  -- Cell addr.
      LUP_CLK	      : in std_logic;

      -- Address Decoder interface
      ADC_RD         : in std_logic;
      ADC_ADDR       : in std_logic_vector(9 downto 0);
      ADC_DO         : out std_logic_vector(31 downto 0)
   );
end component;

   -- address decoder signals
   signal lb_adc_do     : std_logic_vector(15 downto 0);
   signal lb_adc_rw     : std_logic;
   signal lb_adc_en     : std_logic;
   signal lb_adc_sel    : std_logic;
   signal lb_adc_drdy   : std_logic;
   signal lb_adc_addr   : std_logic_vector(ADDR_WIDTH-1 downto 0);

   signal reg_adc_addr100_we  : std_logic;
   signal reg_adc_addr100     : std_logic_vector( 9 downto 0);
   -- signal reg_adc_addr     : std_logic_vector(8 downto 0);
   signal reg_adc_rd          : std_logic;
   signal reg_adc_do          : std_logic_vector(31 downto 0);

   -- Unified header data multiplex
   signal uhf_adc_do          : std_logic_vector(31 downto 0);
   signal i0_uhf_adc_do       : std_logic_vector(31 downto 0);
   signal i1_uhf_adc_do       : std_logic_vector(31 downto 0);
   signal i2_uhf_adc_do       : std_logic_vector(31 downto 0);
   signal i3_uhf_adc_do       : std_logic_vector(31 downto 0);

   signal regsh_adc_addr      : std_logic_vector(0 downto 0);
   signal regsh_adc_drdy      : std_logic_vector(0 downto 0);
   signal regsh_adc_drdy_in   : std_logic_vector(0 downto 0);

   signal regsh_adc_addr_msb1 : std_logic_vector(0 downto 0);
   signal regsh_adc_addr_msb0 : std_logic_vector(0 downto 0);
   signal blockram_switch     : std_logic_vector(1 downto 0);

begin

-- ----------------------- Address Decoder Part ----------------------------

   -- Input signal iterconnect
   DATA_OUT       <= lb_adc_do;
   lb_adc_addr    <= ADDR;
   lb_adc_rw      <= RW;
   lb_adc_en      <= EN;
   lb_adc_sel     <= SEL;
   DRDY           <= lb_adc_drdy;
   ARDY           <= '1';

   -- reg_adc_addr100 register
   reg_adc_addr100_we <= lb_adc_en and (not lb_adc_addr(0));

   process(RESET, LBCLK)
   begin
      if (RESET = '1') then
         reg_adc_addr100 <= (others => '0');
      elsif (LBCLK'event AND LBCLK = '1') then
         if (reg_adc_addr100_we = '1') then
            reg_adc_addr100 <= lb_adc_addr(10 downto 1);
         end if;
      end if;
   end process;


   -- reg_adc_rd register
   process(RESET, LUP_CLK)
   begin
      if (RESET = '1') then
         reg_adc_rd     <= '0';
   --       reg_adc_addr   <= (others => '0');
         reg_adc_do     <= (others => '0');
      elsif (LUP_CLK'event AND LUP_CLK = '1') then
         reg_adc_rd     <= lb_adc_sel;
   --       reg_adc_addr   <= reg_adc_addr100;
         reg_adc_do     <= uhf_adc_do;
      end if;
   end process;

   -- regsh_adc_addr shift register
   SH_ADCADDR_U : entity work.sh_reg
   generic map(
      NUM_BITS => 6,
      INIT     => X"0000"
   )
   port map(
      CLK      => LBCLK,
      DIN      => lb_adc_addr(0),
      CE       => '1',
      DOUT     => regsh_adc_addr(0)
   );


   -- regsh_adc_drdy : DRDY shift register - to be valid in the right time
   regsh_adc_drdy_in(0) <= lb_adc_en and (not lb_adc_rw);

   SH_ADCDRDY_U : entity work.sh_reg
   generic map(
      NUM_BITS => 6,
      INIT     => X"0000"
   )
   port map(
      CLK      => LBCLK,
      DIN      => regsh_adc_drdy_in(0),
      CE       => '1',
      DOUT     => regsh_adc_drdy(0)
   );

   -- output data multiplexor - lower and higher part of the word
   lb_adc_do <= reg_adc_do(15 downto  0) when (regsh_adc_addr(0) = '0') else
                reg_adc_do(31 downto 16);

   -- Data ready signal assignment
   lb_adc_drdy <= regsh_adc_drdy(0);


   -- ------------------- Output data multiplex -----------------------
   -- Two MS bits - BlockRAM multiplex
   SH_ADDR_MSB1 : entity work.sh_reg
   generic map(
      NUM_BITS => 4,
      INIT     => X"0000"
   )
   port map(
      CLK      => LBCLK,
      DIN      => lb_adc_addr(12),
      CE       => '1',
      DOUT     => regsh_adc_addr_msb1(0)
   );
   SH_ADDR_MSB0 : entity work.sh_reg
   generic map(
      NUM_BITS => 4,
      INIT     => X"0000"
   )
   port map(
      CLK      => LBCLK,
      DIN      => lb_adc_addr(11),
      CE       => '1',
      DOUT     => regsh_adc_addr_msb0(0)
   );

   -- Data output multiplex
   blockram_switch   <= (regsh_adc_addr_msb1(0)&regsh_adc_addr_msb0(0));

   mx_data_out :  process (i0_uhf_adc_do, i1_uhf_adc_do,
                           i2_uhf_adc_do, i3_uhf_adc_do,
                           blockram_switch)
   begin
      uhf_adc_do  <= i0_uhf_adc_do;
      case blockram_switch is
         when "00"   => uhf_adc_do  <= i0_uhf_adc_do;
         when "01"   => uhf_adc_do  <= i1_uhf_adc_do;
         when "10"   => uhf_adc_do  <= i2_uhf_adc_do;
         when "11"   => uhf_adc_do  <= i3_uhf_adc_do;
         when others => uhf_adc_do  <= i0_uhf_adc_do;
      end case;
   end process mx_data_out;

   -- ----------------------- Interface 0 -------------------------------
   UH0 : UH_FIFO
   port map(
      -- Control signals
      HFE_CLK    =>  HFE_CLK,
      LUP_CLK    =>  LUP_CLK,
      RESET	     =>  RESET,
      -- HFE interface
      HFE_DOUT   =>  UH0_HFE_DOUT,
      HFE_ADDR   =>  UH0_HFE_ADDR,
      HFE_RDY    =>  UH0_HFE_RDY,
      HFE_REQ    =>  UH0_HFE_REQ,
      HFE_WEN    =>  UH0_HFE_WEN,
      -- LUP interface
      LUP_SR_VALID  => UH0_LUP_SR_VALID,
      LUP_SR_CLEAN  => UH0_LUP_SR_CLEAN,
      LUP_DATA      => UH0_LUP_DATA,
      LUP_ADDR      => UH0_LUP_ADDR,
      -- Address Decoder interface
      ADC_RD         => reg_adc_rd,
      ADC_ADDR       => reg_adc_addr100,
      ADC_DO         => i0_uhf_adc_do
   );
   -- ----------------------- Interface 1 -------------------------------
   UH1 : UH_FIFO
   port map(
      -- Control signals
      HFE_CLK    =>  HFE_CLK,
      LUP_CLK    =>  LUP_CLK,
      RESET	     =>  RESET,
      -- HFE interface
      HFE_DOUT   =>  UH1_HFE_DOUT,
      HFE_ADDR   =>  UH1_HFE_ADDR,
      HFE_RDY    =>  UH1_HFE_RDY,
      HFE_REQ    =>  UH1_HFE_REQ,
      HFE_WEN    =>  UH1_HFE_WEN,
      -- LUP interface
      LUP_SR_VALID  => UH1_LUP_SR_VALID,
      LUP_SR_CLEAN  => UH1_LUP_SR_CLEAN,
      LUP_DATA      => UH1_LUP_DATA,
      LUP_ADDR      => UH1_LUP_ADDR,
      -- Address Decoder interface
      ADC_RD         => reg_adc_rd,
      ADC_ADDR       => reg_adc_addr100,
      ADC_DO         => i1_uhf_adc_do
   );
   -- ----------------------- Interface 2 -------------------------------
   UH2 : UH_FIFO
   port map(
      -- Control signals
      HFE_CLK    =>  HFE_CLK,
      LUP_CLK    =>  LUP_CLK,
      RESET	     =>  RESET,
      -- HFE interface
      HFE_DOUT   =>  UH2_HFE_DOUT,
      HFE_ADDR   =>  UH2_HFE_ADDR,
      HFE_RDY    =>  UH2_HFE_RDY,
      HFE_REQ    =>  UH2_HFE_REQ,
      HFE_WEN    =>  UH2_HFE_WEN,
      -- LUP interface
      LUP_SR_VALID  => UH2_LUP_SR_VALID,
      LUP_SR_CLEAN  => UH2_LUP_SR_CLEAN,
      LUP_DATA      => UH2_LUP_DATA,
      LUP_ADDR      => UH2_LUP_ADDR,
      -- Address Decoder interface
      ADC_RD         => reg_adc_rd,
      ADC_ADDR       => reg_adc_addr100,
      ADC_DO         => i2_uhf_adc_do
   );
   -- ----------------------- Interface 3 -------------------------------
   UH3 : UH_FIFO
   port map(
      -- Control signals
      HFE_CLK    =>  HFE_CLK,
      LUP_CLK    =>  LUP_CLK,
      RESET	     =>  RESET,
      -- HFE interface
      HFE_DOUT   =>  UH3_HFE_DOUT,
      HFE_ADDR   =>  UH3_HFE_ADDR,
      HFE_RDY    =>  UH3_HFE_RDY,
      HFE_REQ    =>  UH3_HFE_REQ,
      HFE_WEN    =>  UH3_HFE_WEN,
      -- LUP interface
      LUP_SR_VALID  => UH3_LUP_SR_VALID,
      LUP_SR_CLEAN  => UH3_LUP_SR_CLEAN,
      LUP_DATA      => UH3_LUP_DATA,
      LUP_ADDR      => UH3_LUP_ADDR,
      -- Address Decoder interface
      ADC_RD         => reg_adc_rd,
      ADC_ADDR       => reg_adc_addr100,
      ADC_DO         => i3_uhf_adc_do
   );
end full;
