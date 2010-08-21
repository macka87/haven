--
-- uh_four_fl32_mi32_lb.vhd: 4 x Unified header FIFO - entity declaration
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Zadnik <zadnik@liberouter.org>
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
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;
use work.fl_pkg.all;
use work.lb_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity UH_FOUR_FL32_MI32_LB is
generic(
   BASE_ADDR  : integer;
   ADDR_WIDTH : integer;
   FREQUENCY  : integer
);
      port(
      -- ------- Control signals --------
      HFE_CLK           : in std_logic;
      LUP_CLK           : in std_logic;
      RESET             : in std_logic;

      -- -------- HFE interface ---------
      UH0_HFE           : inout t_fl32;
      UH1_HFE           : inout t_fl32;
      UH2_HFE           : inout t_fl32;
      UH3_HFE           : inout t_fl32;

      -- ------- LUP interface ----------
      -- Interface 0
      UH0_LUP_SR_VALID  : out std_logic;       -- If cell contains un. header
      UH0_LUP_SR_CLEAN  : in  std_logic;       -- Clean addressed cell
      UH0_LUP_DATA      : out std_logic_vector(31 downto 0); -- UH data
      UH0_LUP_ADDR      : in  std_logic_vector(8 downto 0);  -- Cell addr.
      -- Interface 1
      UH1_LUP_SR_VALID  : out std_logic;       -- If cell contains un. header
      UH1_LUP_SR_CLEAN  : in  std_logic;       -- Clean addressed cell
      UH1_LUP_DATA      : out std_logic_vector(31 downto 0); -- UH data
      UH1_LUP_ADDR      : in  std_logic_vector(8 downto 0);  -- Cell addr.
      -- Interface 2
      UH2_LUP_SR_VALID  : out std_logic;       -- If cell contains un. header
      UH2_LUP_SR_CLEAN  : in  std_logic;       -- Clean addressed cell
      UH2_LUP_DATA      : out std_logic_vector(31 downto 0); -- UH data
      UH2_LUP_ADDR      : in  std_logic_vector(8 downto 0);  -- Cell addr.
      -- Interface 3
      UH3_LUP_SR_VALID  : out std_logic;       -- If cell contains un. header
      UH3_LUP_SR_CLEAN  : in  std_logic;       -- Clean addressed cell
      UH3_LUP_DATA      : out std_logic_vector(31 downto 0); -- UH data
      UH3_LUP_ADDR      : in  std_logic_vector(8 downto 0);  -- Cell addr.

 -- Internal bus signals
      LBCLK       : in    std_logic;  -- internal bus clock, up to 100 MHz
      LBFRAME     : in    std_logic;  -- Frame
      LBHOLDA     : out   std_logic;  -- Hold Ack
      LBAD        : inout std_logic_vector(15 downto 0); -- Address/Data
      LBAS        : in    std_logic;  -- Adress strobe
      LBRW        : in    std_logic;  -- Direction (Read#/Write, low : read)
      LBRDY       : out   std_logic;  -- Ready
      LBLAST      : in    std_logic   -- Last word in transfer 
      
   );
end entity;

architecture struct of UH_FOUR_FL32_MI32_LB is 
   signal mi32_intercon       : t_mi32;

   signal adc_rd              : std_logic;
   signal adc_wr              : std_logic;
   signal adc_addr            : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal adc_di              : std_logic_vector(31 downto 0);
   signal adc_do              : std_logic_vector(31 downto 0);
   signal adc_drdy            : std_logic;

begin

UH_FOUR_FL32_MI32_U: entity work.UH_FOUR_FL32_MI32 
port map(
   HFE_CLK         => hfe_clk,
   LUP_CLK         => lup_clk,
   RESET           => reset,

    -- -------- HFE interface ---------
   UH0_HFE           => UH0_HFE,
   UH1_HFE           => UH1_HFE,
   UH2_HFE           => UH2_HFE,
   UH3_HFE           => UH3_HFE,

   -- ------- UHDRV (IFC_CORE) interface ----------
   -- Interface 0
   UH0_LUP_SR_VALID => UH0_LUP_SR_VALID,
   UH0_LUP_SR_CLEAN => UH0_LUP_SR_CLEAN,
   UH0_LUP_DATA     => UH0_LUP_DATA,
   UH0_LUP_ADDR     => UH0_LUP_ADDR,
   -- Interface 1
   UH1_LUP_SR_VALID => UH1_LUP_SR_VALID,
   UH1_LUP_SR_CLEAN => UH1_LUP_SR_CLEAN,
   UH1_LUP_DATA     => UH1_LUP_DATA,
   UH1_LUP_ADDR     => UH1_LUP_ADDR,
   -- Interface 2
   UH2_LUP_SR_VALID => UH2_LUP_SR_VALID,
   UH2_LUP_SR_CLEAN => UH2_LUP_SR_CLEAN,
   UH2_LUP_DATA     => UH2_LUP_DATA,
   UH2_LUP_ADDR     => UH2_LUP_ADDR,
   -- Interface 3
   UH3_LUP_SR_VALID => UH3_LUP_SR_VALID,
   UH3_LUP_SR_CLEAN => UH3_LUP_SR_CLEAN,
   UH3_LUP_DATA     => UH3_LUP_DATA,
   UH3_LUP_ADDR     => UH3_LUP_ADDR,

   -- Address decoder interface
   MI               => mi32_intercon
);

      mi32_intercon.DWR   <= adc_di;
      mi32_intercon.ADDR  <= (31 downto ADDR_WIDTH-2 => '0') & adc_addr(ADDR_WIDTH-1 downto 2);
      mi32_intercon.RD    <= adc_rd;
      mi32_intercon.WR    <= adc_wr;
      mi32_intercon.BE    <= X"F";
      adc_do              <= mi32_intercon.DRD;
      adc_drdy            <= mi32_intercon.DRDY;
   

-- LB_Connect Component Instantion
LB_CONNECT_U: entity work.lb_connect
generic map(
   BASE_ADDR      => BASE_ADDR,
   ADDR_WIDTH     => ADDR_WIDTH,
   FREQUENCY      => FREQUENCY
)
port map (
   -- Control signals
   RESET      => reset,

   -- LB signals
   LBCLK      => LBCLK,
   LBFRAME    => LBFRAME,
   LBHOLDA    => LBHOLDA,
   LBAD       => LBAD,
   LBAS       => LBAS,
   LBRW       => LBRW,
   LBRDY      => LBRDY,
   LBLAST     => LBLAST,

   -- Address decoder interface
   CLK         => LUP_CLK,
   ADC_RD      => adc_rd,
   ADC_WR      => adc_wr,
   ADC_ADDR    => adc_addr,
   ADC_DI      => adc_di,
   ADC_DO      => adc_do,
   ADC_DRDY    => adc_drdy
);
end architecture;
