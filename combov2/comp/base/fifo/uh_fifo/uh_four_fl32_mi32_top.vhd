--
-- uh_four_fl32_mi32_top.vhd: 4 x Unified Header FIFO - full architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--            Petr Mikusek <petr.mikusek@liberouter.org>
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
use work.fl_pkg.all;
use work.lb_pkg.all;

architecture full of UH_FOUR_FL32_MI32 is
   
   -- ------------------ Components declaration -------------------------------
   component UH_FIFO_FL
      port(
         -- Control signals
         RESET          : in  std_logic;
   
         -- HFE interface
         HFE_DATA       : in  std_logic_vector(31 downto 0); -- data
         HFE_DREM       : in  std_logic_vector(1 downto 0); -- data remainder
         HFE_SOF_N      : in  std_logic; -- start of frame
         HFE_EOF_N      : in  std_logic; -- end of frame
         HFE_SOP_N      : in  std_logic; -- start of part
         HFE_EOP_N      : in  std_logic; -- end of part
         HFE_SRC_RDY_N  : in  std_logic; -- source ready
         HFE_DST_RDY_N  : out std_logic; -- destination ready
         HFE_CLK	: in  std_logic;
   
         -- LUP interface
         LUP_SR_VALID   : out std_logic;       -- If cell contains unfied header
         LUP_SR_CLEAN   : in  std_logic;       -- Clean addressed cell
         LUP_DATA       : out std_logic_vector(31 downto 0); -- UH data
         LUP_ADDR       : in  std_logic_vector(8 downto 0);  -- Cell addr.
         LUP_CLK	: in  std_logic;
   
         -- Address Decoder interface
         ADC_RD         : in  std_logic;
         ADC_ADDR       : in  std_logic_vector(9 downto 0);
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


   signal reg_rdy : std_logic;
   signal reg2_rdy : std_logic;
   signal reg3_rdy : std_logic;

begin
   -- MI signals setting

process(RESET, LUP_CLK)
begin
   if (RESET = '1') then
      reg_rdy <= '0';
      reg2_rdy <= '0';
      reg3_rdy <= '0';
   elsif (LUP_CLK'event AND LUP_CLK = '1') then
      reg_rdy <= MI.RD;
      reg2_rdy <= reg_rdy;
      reg3_rdy <= reg2_rdy;
   end if;
end process;

   MI.DRDY  <= reg_rdy;
   MI.ARDY  <= MI.RD;

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
   UH_FIFO_FL0_I : UH_FIFO_FL
   port map(
      -- Control signals
      HFE_CLK        => HFE_CLK,
      LUP_CLK        => LUP_CLK,
      RESET	     => RESET,
      -- HFE interface
      HFE_DATA       => UH0_HFE.DATA,
      HFE_DREM       => UH0_HFE.DREM,
      HFE_SOF_N      => UH0_HFE.SOF_N,
      HFE_EOF_N      => UH0_HFE.EOF_N,
      HFE_SOP_N      => UH0_HFE.SOP_N,
      HFE_EOP_N      => UH0_HFE.EOP_N,
      HFE_SRC_RDY_N  => UH0_HFE.SRC_RDY_N,
      HFE_DST_RDY_N  => UH0_HFE.DST_RDY_N,
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
   UH_FIFO_FL1_I : UH_FIFO_FL
   port map(
      -- Control signals
      HFE_CLK        => HFE_CLK,
      LUP_CLK        => LUP_CLK,
      RESET	     => RESET,
      -- HFE interface
      HFE_DATA       => UH1_HFE.DATA,
      HFE_DREM       => UH1_HFE.DREM,
      HFE_SOF_N      => UH1_HFE.SOF_N,
      HFE_EOF_N      => UH1_HFE.EOF_N,
      HFE_SOP_N      => UH1_HFE.SOP_N,
      HFE_EOP_N      => UH1_HFE.EOP_N,
      HFE_SRC_RDY_N  => UH1_HFE.SRC_RDY_N,
      HFE_DST_RDY_N  => UH1_HFE.DST_RDY_N,
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
   UH_FIFO_FL2_I : UH_FIFO_FL
   port map(
      -- Control signals
      HFE_CLK        => HFE_CLK,
      LUP_CLK        => LUP_CLK,
      RESET	     => RESET,
      -- HFE interface
      HFE_DATA       => UH2_HFE.DATA,
      HFE_DREM       => UH2_HFE.DREM,
      HFE_SOF_N      => UH2_HFE.SOF_N,
      HFE_EOF_N      => UH2_HFE.EOF_N,
      HFE_SOP_N      => UH2_HFE.SOP_N,
      HFE_EOP_N      => UH2_HFE.EOP_N,
      HFE_SRC_RDY_N  => UH2_HFE.SRC_RDY_N,
      HFE_DST_RDY_N  => UH2_HFE.DST_RDY_N,
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
   UH_FIFO_FL3_I : UH_FIFO_FL
   port map(
      -- Control signals
      HFE_CLK        => HFE_CLK,
      LUP_CLK        => LUP_CLK,
      RESET	     => RESET,
      -- HFE interface
      HFE_DATA       => UH3_HFE.DATA,
      HFE_DREM       => UH3_HFE.DREM,
      HFE_SOF_N      => UH3_HFE.SOF_N,
      HFE_EOF_N      => UH3_HFE.EOF_N,
      HFE_SOP_N      => UH3_HFE.SOP_N,
      HFE_EOP_N      => UH3_HFE.EOP_N,
      HFE_SRC_RDY_N  => UH3_HFE.SRC_RDY_N,
      HFE_DST_RDY_N  => UH3_HFE.DST_RDY_N,
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
