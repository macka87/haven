--
-- ibuf_gmii_top1.vhd:  Input Buffer - ibuf + LB entity
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
--
--
library ieee;
use ieee.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_gmii_top1 is

   -- Local Bus signals
   signal lb_en      : std_logic;
   signal lb_rw      : std_logic;
   signal lb_drdy    : std_logic;
   signal lb_ardy    : std_logic;
   signal lb_addr    : std_logic_vector(6 downto 0);
   signal lb_di      : std_logic_vector(15 downto 0);
   signal lb_do      : std_logic_vector(15 downto 0);

   -- Address decoder signals
   signal adc_clk    : std_logic;
   signal adc_rd     : std_logic;
   signal adc_wr     : std_logic;
   signal adc_addr   : std_logic_vector(5 downto 0);
   signal adc_di     : std_logic_vector(31 downto 0);
   signal adc_do     : std_logic_vector(31 downto 0);
   signal adc_drdy   : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- OBUF instantination --------------------------------------------------------
IBUF_U : entity work.ibuf_gmii
generic map (
   DATA_PATHS => DATA_PATHS,
   DFIFO_SIZE => DFIFO_SIZE,
   HFIFO_SIZE => HFIFO_SIZE,
   MACS       => MACS
)
port map (
   RESET => RESET,

   -- receive gmii interface
   RXCLK    => RXCLK,
   RXD      => RXD,
   RXDV     => RXDV,
   RXER     => RXER,

   -- PHY status interface
   LINK_STATUS       => '0', --PHY0_LINK_STATUS,
   DUPLEX_MODE       => '0', --PHY0_DUPLEX_MODE,
   SPEED             => "00", --PHY0_SPEED,
   SGMII             => '0', --PHY0_SGMII,

   -- PACODAG interface
   CTRL_CLK    => CTRL_CLK,
   CTRL_DI        => CTRL_DI,
   CTRL_REM       => CTRL_REM,
   CTRL_SRC_RDY_N => CTRL_SRC_RDY_N,
   CTRL_SOP_N     => CTRL_SOP_N,
   CTRL_EOP_N     => CTRL_EOP_N,
   CTRL_DST_RDY_N => CTRL_DST_RDY_N,
   CTRL_HDR_EN => CTRL_HDR_EN,
   CTRL_FTR_EN => CTRL_FTR_EN,
   CTRL_RDY    => CTRL_RDY,

   -- IBUF status interface
   SOP         => SOP,
   STAT        => STAT,
   STAT_DV     => STAT_DV,

   -- Sampling unit interface
   SAU_ACCEPT => SAU_ACCEPT,
   SAU_DV     => SAU_DV,

   -- FrameLink interface
   RDCLK      => RDCLK,
   DATA       => DATA,
   DREM       => DREM,
   SRC_RDY_N  => SRC_RDY_N,
   SOF_N      => SOF_N,
   SOP_N      => SOP_N,
   EOF_N      => EOF_N,
   EOP_N      => EOP_N,
   DST_RDY_N  => DST_RDY_N,
   
   ADC_CLK  => adc_clk,
   ADC_RD   => adc_rd,
   ADC_WR   => adc_wr,
   ADC_ADDR => adc_addr,
   ADC_DI   => adc_di,
   ADC_DO   => adc_do,
   ADC_DRDY => adc_drdy
);

-- LBCONN_MEM instantination --------------------------------------------------
LBCONN_MEM_U : entity work.lbconn_mem
generic map(
   ADDR_WIDTH     => 7, -- address bus width
   BASE           => ADDR_BASE   -- base address
)
port map(
   DATA_OUT => lb_do,
   DATA_IN  => lb_di,
   ADDR     => lb_addr,
   EN       => lb_en,
   RW       => lb_rw,
   SEL      => open,
   DRDY     => lb_drdy,
   ARDY     => '1',

   RESET    => RESET,
   LBCLK    => LBCLK,
   LBFRAME  => LBFRAME,
   LBAS     => LBAS,
   LBRW     => LBRW,
   LBLAST   => LBLAST,
   LBAD     => LBAD,
   LBHOLDA  => LBHOLDA,
   LBRDY    => LBRDY
);

-- LB_ASYNC -------------------------------------------------------------------
LB_ASYNC_U: entity work.lb_async
generic map(
   AS_DATA_DELAY  => 1,
   ADDR_WIDTH     => 7
)
port map(
   -- Global interface
   RESET    => reset,

   -- lbconn_mem interface
   LB_CLK   => LBCLK,
   LB_EN    => lb_en,
   LB_RW    => lb_rw,
   LB_ADDR  => lb_addr,
   LB_DI    => lb_do,
   LB_DO    => lb_di,
   LB_ARDY  => open,
   LB_DRDY  => lb_drdy,

   -- ssynchronous address decoder interface
   AS_CLK   => adc_clk,
   AS_ADDR  => adc_addr,
   AS_DI    => adc_di,
   AS_RD    => adc_rd,
   AS_WR    => adc_wr,
   AS_DO    => adc_do
);

end architecture full;
