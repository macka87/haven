--
-- uh_four_mi32_top.vhd: 4 x Unified Header FIFO - full architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
use work.lb_pkg.all;

architecture full of UH_FOUR_MI32 is
   
   -- ------------------ Components declaration -------------------------------
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

   -- ------------------ Signals declaration ----------------------------------
   signal uh_fifo0_sel     : std_logic;
   signal uh_fifo1_sel     : std_logic;
   signal uh_fifo2_sel     : std_logic;
   signal uh_fifo3_sel     : std_logic;

   signal uh_fifo0_adc_do  : std_logic_vector(31 downto 0);
   signal uh_fifo1_adc_do  : std_logic_vector(31 downto 0);
   signal uh_fifo2_adc_do  : std_logic_vector(31 downto 0);
   signal uh_fifo3_adc_do  : std_logic_vector(31 downto 0);
   
   signal uh_fifo0_adc_rd  : std_logic;
   signal uh_fifo1_adc_rd  : std_logic;
   signal uh_fifo2_adc_rd  : std_logic;
   signal uh_fifo3_adc_rd  : std_logic;

begin
   -- MI signals setting
   MI.DRDY  <= '1';
   MI.ARDY  <= '1';

   -- select signals
   uh_fifo0_sel  <= '1' when MI.ADDR(11 downto 10) = "00" else '0';
   uh_fifo1_sel  <= '1' when MI.ADDR(11 downto 10) = "01" else '0';
   uh_fifo2_sel  <= '1' when MI.ADDR(11 downto 10) = "10" else '0';
   uh_fifo3_sel  <= '1' when MI.ADDR(11 downto 10) = "11" else '0';
   
   -- DATA OUT multiplexing
   MI.DRD     <= uh_fifo0_adc_do when uh_fifo0_sel = '1' else
                 uh_fifo1_adc_do when uh_fifo1_sel = '1' else
                 uh_fifo2_adc_do when uh_fifo2_sel = '1' else
                 uh_fifo3_adc_do;
   
   -- read request signals
   uh_fifo0_adc_rd  <= MI.RD when uh_fifo0_sel = '1' else '0';
   uh_fifo1_adc_rd  <= MI.RD when uh_fifo1_sel = '1' else '0';
   uh_fifo2_adc_rd  <= MI.RD when uh_fifo2_sel = '1' else '0';
   uh_fifo3_adc_rd  <= MI.RD when uh_fifo3_sel = '1' else '0';

   -- UH FIFO 0 ---------------------------------------------------------------
   UH_FIFO0_I : UH_FIFO
   port map(
      -- Control signals
      HFE_CLK        => HFE_CLK,
      LUP_CLK        => LUP_CLK,
      RESET	         => RESET,
      -- HFE interface
      HFE_DOUT       => UH0_HFE_DOUT,
      HFE_ADDR       => UH0_HFE_ADDR,
      HFE_RDY        => UH0_HFE_RDY,
      HFE_REQ        => UH0_HFE_REQ,
      HFE_WEN        => UH0_HFE_WEN,
      -- LUP interface
      LUP_SR_VALID   => UH0_LUP_SR_VALID,
      LUP_SR_CLEAN   => UH0_LUP_SR_CLEAN,
      LUP_DATA       => UH0_LUP_DATA,
      LUP_ADDR       => UH0_LUP_ADDR,
      -- Address Decoder interface
      ADC_RD         => uh_fifo0_adc_rd,
      ADC_ADDR       => MI.ADDR(9 downto 0),
      ADC_DO         => uh_fifo0_adc_do
   );

   -- UH FIFO 1 ---------------------------------------------------------------
   UH_FIFO1_I : UH_FIFO
   port map(
      -- Control signals
      HFE_CLK        => HFE_CLK,
      LUP_CLK        => LUP_CLK,
      RESET	         => RESET,
      -- HFE interface
      HFE_DOUT       => UH1_HFE_DOUT,
      HFE_ADDR       => UH1_HFE_ADDR,
      HFE_RDY        => UH1_HFE_RDY,
      HFE_REQ        => UH1_HFE_REQ,
      HFE_WEN        => UH1_HFE_WEN,
      -- LUP interface
      LUP_SR_VALID   => UH1_LUP_SR_VALID,
      LUP_SR_CLEAN   => UH1_LUP_SR_CLEAN,
      LUP_DATA       => UH1_LUP_DATA,
      LUP_ADDR       => UH1_LUP_ADDR,
      -- Address Decoder interface
      ADC_RD         => uh_fifo1_adc_rd,
      ADC_ADDR       => MI.ADDR(9 downto 0),
      ADC_DO         => uh_fifo1_adc_do
   );

   -- UH FIFO 2 ---------------------------------------------------------------
   UH_FIFO2_I : UH_FIFO
   port map(
      -- Control signals
      HFE_CLK        => HFE_CLK,
      LUP_CLK        => LUP_CLK,
      RESET	         => RESET,
      -- HFE interface
      HFE_DOUT       => UH2_HFE_DOUT,
      HFE_ADDR       => UH2_HFE_ADDR,
      HFE_RDY        => UH2_HFE_RDY,
      HFE_REQ        => UH2_HFE_REQ,
      HFE_WEN        => UH2_HFE_WEN,
      -- LUP interface
      LUP_SR_VALID   => UH2_LUP_SR_VALID,
      LUP_SR_CLEAN   => UH2_LUP_SR_CLEAN,
      LUP_DATA       => UH2_LUP_DATA,
      LUP_ADDR       => UH2_LUP_ADDR,
      -- Address Decoder interface
      ADC_RD         => uh_fifo2_adc_rd,
      ADC_ADDR       => MI.ADDR(9 downto 0),
      ADC_DO         => uh_fifo2_adc_do
   );

   -- UH FIFO 3 ---------------------------------------------------------------
   UH_FIFO3_I : UH_FIFO
   port map(
      -- Control signals
      HFE_CLK        => HFE_CLK,
      LUP_CLK        => LUP_CLK,
      RESET	         => RESET,
      -- HFE interface
      HFE_DOUT       => UH3_HFE_DOUT,
      HFE_ADDR       => UH3_HFE_ADDR,
      HFE_RDY        => UH3_HFE_RDY,
      HFE_REQ        => UH3_HFE_REQ,
      HFE_WEN        => UH3_HFE_WEN,
      -- LUP interface
      LUP_SR_VALID   => UH3_LUP_SR_VALID,
      LUP_SR_CLEAN   => UH3_LUP_SR_CLEAN,
      LUP_DATA       => UH3_LUP_DATA,
      LUP_ADDR       => UH3_LUP_ADDR,
      -- Address Decoder interface
      ADC_RD         => uh_fifo3_adc_rd,
      ADC_ADDR       => MI.ADDR(9 downto 0),
      ADC_DO         => uh_fifo3_adc_do
   );

end full;
