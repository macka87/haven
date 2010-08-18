--
-- obuf_gmii_top4.vhd:  Output Buffer - 4 obufs + LB entity
-- Copyright (C) 2005 CESNET
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
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_gmii_top4 is

   constant ADDR_WIDTH  : integer := 9;
   
   signal obuf0_adc_clk  : std_logic;
   signal obuf0_adc_rd   : std_logic;
   signal obuf0_adc_wr   : std_logic;
   signal obuf0_adc_addr : std_logic_vector(5 downto 0);
   signal obuf0_adc_di   : std_logic_vector(31 downto 0);
   signal obuf0_adc_do   : std_logic_vector(31 downto 0);
   signal obuf0_adc_drdy : std_logic;

   signal obuf1_adc_clk  : std_logic;
   signal obuf1_adc_rd   : std_logic;
   signal obuf1_adc_wr   : std_logic;
   signal obuf1_adc_addr : std_logic_vector(5 downto 0);
   signal obuf1_adc_di   : std_logic_vector(31 downto 0);
   signal obuf1_adc_do   : std_logic_vector(31 downto 0);
   signal obuf1_adc_drdy : std_logic;

   signal obuf2_adc_clk  : std_logic;
   signal obuf2_adc_rd   : std_logic;
   signal obuf2_adc_wr   : std_logic;
   signal obuf2_adc_addr : std_logic_vector(5 downto 0);
   signal obuf2_adc_di   : std_logic_vector(31 downto 0);
   signal obuf2_adc_do   : std_logic_vector(31 downto 0);
   signal obuf2_adc_drdy : std_logic;

   signal obuf3_adc_clk  : std_logic;
   signal obuf3_adc_rd   : std_logic;
   signal obuf3_adc_wr   : std_logic;
   signal obuf3_adc_addr : std_logic_vector(5 downto 0);
   signal obuf3_adc_di   : std_logic_vector(31 downto 0);
   signal obuf3_adc_do   : std_logic_vector(31 downto 0);
   signal obuf3_adc_drdy : std_logic;

   signal obuf0_lb_en    : std_logic;
   signal obuf0_lb_di    : std_logic_vector(15 downto 0);
   signal obuf0_lb_drdy  : std_logic;

   signal obuf1_lb_en    : std_logic;
   signal obuf1_lb_di    : std_logic_vector(15 downto 0);
   signal obuf1_lb_drdy  : std_logic;

   signal obuf2_lb_en    : std_logic;
   signal obuf2_lb_di    : std_logic_vector(15 downto 0);
   signal obuf2_lb_drdy  : std_logic;

   signal obuf3_lb_en    : std_logic;
   signal obuf3_lb_di    : std_logic_vector(15 downto 0);
   signal obuf3_lb_drdy  : std_logic;

   signal lb_en          : std_logic;
   signal lb_rw          : std_logic;
   signal lb_addr        : std_logic_vector(8 downto 0);
   signal lb_di          : std_logic_vector(15 downto 0);
   signal lb_do          : std_logic_vector(15 downto 0);
   signal lb_drdy        : std_logic;
   signal lb_ardy        : std_logic;

   signal addr_sel       : std_logic_vector(1 downto 0);
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- OBUF 0 instantination ------------------------------------------------------
OBUF0_U : entity work.obuf_gmii
generic map (
   DATA_PATHS => DATA_PATHS,
   DFIFO_SIZE => DFIFO_SIZE,
   SFIFO_SIZE => SFIFO_SIZE,
   CTRL_CMD   => CTRL_CMD
)
port map (
   RESET    => reset,
   WRCLK    => WRCLK,
   REFCLK   => REFCLK,

   -- FrameLink input interface
   DATA       => OBUF0_DATA,
   DREM       => OBUF0_DREM,
   SRC_RDY_N  => OBUF0_SRC_RDY_N,
   SOF_N      => OBUF0_SOF_N,
   SOP_N      => OBUF0_SOP_N,
   EOF_N      => OBUF0_EOF_N,
   EOP_N      => OBUF0_EOP_N,
   DST_RDY_N  => OBUF0_DST_RDY_N,

   -- gmii interface
   TXCLK    => OBUF0_TXCLK,
   TXD      => OBUF0_TXD,
   TXEN     => OBUF0_TXEN,
   TXER     => OBUF0_TXER,
   
   -- PHY status interface
   LINK_STATUS       => '0',
   DUPLEX_MODE       => '0',
   SPEED             => "00",
   SGMII             => '0',

   ADC_CLK  => obuf0_adc_clk,
   ADC_RD   => obuf0_adc_rd,
   ADC_WR   => obuf0_adc_wr,
   ADC_ADDR => obuf0_adc_addr,
   ADC_DI   => obuf0_adc_di,
   ADC_DO   => obuf0_adc_do,
   ADC_DRDY => obuf0_adc_drdy
);

-- OBUF 1 instantination ------------------------------------------------------
OBUF1_U : entity work.obuf_gmii
generic map (
   DATA_PATHS => DATA_PATHS,
   DFIFO_SIZE => DFIFO_SIZE,
   SFIFO_SIZE => SFIFO_SIZE,
   CTRL_CMD   => CTRL_CMD
)
port map (
   RESET    => reset,
   WRCLK    => WRCLK,
   REFCLK   => REFCLK,

   -- FrameLink input interface
   DATA       => OBUF1_DATA,
   DREM       => OBUF1_DREM,
   SRC_RDY_N  => OBUF1_SRC_RDY_N,
   SOF_N      => OBUF1_SOF_N,
   SOP_N      => OBUF1_SOP_N,
   EOF_N      => OBUF1_EOF_N,
   EOP_N      => OBUF1_EOP_N,
   DST_RDY_N  => OBUF1_DST_RDY_N,

   -- gmii interface
   TXCLK    => OBUF1_TXCLK,
   TXD      => OBUF1_TXD,
   TXEN     => OBUF1_TXEN,
   TXER     => OBUF1_TXER,
   
   -- PHY status interface
   LINK_STATUS       => '0',
   DUPLEX_MODE       => '0',
   SPEED             => "00",
   SGMII             => '0',

   ADC_CLK  => obuf1_adc_clk,
   ADC_RD   => obuf1_adc_rd,
   ADC_WR   => obuf1_adc_wr,
   ADC_ADDR => obuf1_adc_addr,
   ADC_DI   => obuf1_adc_di,
   ADC_DO   => obuf1_adc_do,
   ADC_DRDY => obuf1_adc_drdy
);

-- OBUF 2 instantination ------------------------------------------------------
OBUF2_U : entity work.obuf_gmii
generic map (
   DATA_PATHS => DATA_PATHS,
   DFIFO_SIZE => DFIFO_SIZE,
   SFIFO_SIZE => SFIFO_SIZE,
   CTRL_CMD   => CTRL_CMD
)
port map (
   RESET    => reset,
   WRCLK    => WRCLK,
   REFCLK   => REFCLK,

   -- FrameLink input interface
   DATA       => OBUF2_DATA,
   DREM       => OBUF2_DREM,
   SRC_RDY_N  => OBUF2_SRC_RDY_N,
   SOF_N      => OBUF2_SOF_N,
   SOP_N      => OBUF2_SOP_N,
   EOF_N      => OBUF2_EOF_N,
   EOP_N      => OBUF2_EOP_N,
   DST_RDY_N  => OBUF2_DST_RDY_N,

   -- gmii interface
   TXCLK    => OBUF2_TXCLK,
   TXD      => OBUF2_TXD,
   TXEN     => OBUF2_TXEN,
   TXER     => OBUF2_TXER,
   
   -- PHY status interface
   LINK_STATUS       => '0',
   DUPLEX_MODE       => '0',
   SPEED             => "00",
   SGMII             => '0',

   ADC_CLK  => obuf2_adc_clk,
   ADC_RD   => obuf2_adc_rd,
   ADC_WR   => obuf2_adc_wr,
   ADC_ADDR => obuf2_adc_addr,
   ADC_DI   => obuf2_adc_di,
   ADC_DO   => obuf2_adc_do,
   ADC_DRDY => obuf2_adc_drdy
);

-- OBUF 3 instantination ------------------------------------------------------
OBUF3_U : entity work.obuf_gmii
generic map (
   DATA_PATHS => DATA_PATHS,
   DFIFO_SIZE => DFIFO_SIZE,
   SFIFO_SIZE => SFIFO_SIZE,
   CTRL_CMD   => CTRL_CMD
)
port map (
   RESET    => reset,
   WRCLK    => WRCLK,
   REFCLK   => REFCLK,

   -- FrameLink input interface
   DATA       => OBUF3_DATA,
   DREM       => OBUF3_DREM,
   SRC_RDY_N  => OBUF3_SRC_RDY_N,
   SOF_N      => OBUF3_SOF_N,
   SOP_N      => OBUF3_SOP_N,
   EOF_N      => OBUF3_EOF_N,
   EOP_N      => OBUF3_EOP_N,
   DST_RDY_N  => OBUF3_DST_RDY_N,

   -- gmii interface
   TXCLK    => OBUF3_TXCLK,
   TXD      => OBUF3_TXD,
   TXEN     => OBUF3_TXEN,
   TXER     => OBUF3_TXER,

   -- PHY status interface
   LINK_STATUS       => '0',
   DUPLEX_MODE       => '0',
   SPEED             => "00",
   SGMII             => '0',

   ADC_CLK  => obuf3_adc_clk,
   ADC_RD   => obuf3_adc_rd,
   ADC_WR   => obuf3_adc_wr,
   ADC_ADDR => obuf3_adc_addr,
   ADC_DI   => obuf3_adc_di,
   ADC_DO   => obuf3_adc_do,
   ADC_DRDY => obuf3_adc_drdy
);

-- LBCONN_MEM instantination --------------------------------------------------
LBCONN_MEM_U : entity work.lbconn_mem
generic map(
   ADDR_WIDTH     => ADDR_WIDTH, -- address bus width
   BASE           => ADDR_BASE   -- base address
)
port map(
   DATA_OUT => lb_do,
   DATA_IN  => lb_di,
   ADDR     => lb_addr,
   EN       => lb_en,
   RW       => lb_rw,
   SEL      => open, -- FIXME ???
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

-- LB_ASYNC for each OBUF instantination --------------------------------------
LB_ASYNC0_U: entity work.lb_async
generic map(
   AS_DATA_DELAY  => 0,
   ADDR_WIDTH     => 7
)
port map(
   -- Global interface
   RESET    => reset,

   -- lbconn_mem interface
   LB_CLK   => LBCLK,
   LB_EN    => obuf0_lb_en,
   LB_RW    => lb_rw,
   LB_ADDR  => lb_addr(6 downto 0),
   LB_DI    => lb_do,
   LB_DO    => obuf0_lb_di,
   LB_ARDY  => open,
   LB_DRDY  => obuf0_lb_drdy,

   -- ssynchronous address decoder interface
   AS_CLK   => obuf0_adc_clk,
   AS_ADDR  => obuf0_adc_addr,
   AS_DI    => obuf0_adc_di,
   AS_RD    => obuf0_adc_rd,
   AS_WR    => obuf0_adc_wr,
   AS_DO    => obuf0_adc_do
);

LB_ASYNC1_U: entity work.lb_async
generic map(
   AS_DATA_DELAY  => 0,
   ADDR_WIDTH     => 7
)
port map(
   -- Global interface
   RESET    => reset,

   -- lbconn_mem interface
   LB_CLK   => LBCLK,
   LB_EN    => obuf1_lb_en,
   LB_RW    => lb_rw,
   LB_ADDR  => lb_addr(6 downto 0),
   LB_DI    => lb_do,
   LB_DO    => obuf1_lb_di,
   LB_ARDY  => open,
   LB_DRDY  => obuf1_lb_drdy,

   -- ssynchronous address decoder interface
   AS_CLK   => obuf1_adc_clk,
   AS_ADDR  => obuf1_adc_addr,
   AS_DI    => obuf1_adc_di,
   AS_RD    => obuf1_adc_rd,
   AS_WR    => obuf1_adc_wr,
   AS_DO    => obuf1_adc_do
);

LB_ASYNC2_U: entity work.lb_async
generic map(
   AS_DATA_DELAY  => 0,
   ADDR_WIDTH     => 7
)
port map(
   -- Global interface
   RESET    => reset,

   -- lbconn_mem interface
   LB_CLK   => LBCLK,
   LB_EN    => obuf2_lb_en,
   LB_RW    => lb_rw,
   LB_ADDR  => lb_addr(6 downto 0),
   LB_DI    => lb_do,
   LB_DO    => obuf2_lb_di,
   LB_ARDY  => open,
   LB_DRDY  => obuf2_lb_drdy,

   -- ssynchronous address decoder interface
   AS_CLK   => obuf2_adc_clk,
   AS_ADDR  => obuf2_adc_addr,
   AS_DI    => obuf2_adc_di,
   AS_RD    => obuf2_adc_rd,
   AS_WR    => obuf2_adc_wr,
   AS_DO    => obuf2_adc_do
);

LB_ASYNC3_U: entity work.lb_async
generic map(
   AS_DATA_DELAY  => 0,
   ADDR_WIDTH     => 7
)
port map(
   -- Global interface
   RESET    => reset,

   -- lbconn_mem interface
   LB_CLK   => LBCLK,
   LB_EN    => obuf3_lb_en,
   LB_RW    => lb_rw,
   LB_ADDR  => lb_addr(6 downto 0),
   LB_DI    => lb_do,
   LB_DO    => obuf3_lb_di,
   LB_ARDY  => open,
   LB_DRDY  => obuf3_lb_drdy,

   -- ssynchronous address decoder interface
   AS_CLK   => obuf3_adc_clk,
   AS_ADDR  => obuf3_adc_addr,
   AS_DI    => obuf3_adc_di,
   AS_RD    => obuf3_adc_rd,
   AS_WR    => obuf3_adc_wr,
   AS_DO    => obuf3_adc_do
);

addr_sel  <= lb_addr (8 downto 7);

-- lb_en demultiplexor --------------------------------------------------------
obuf0_lb_en <= lb_en when (addr_sel="00") else '0';
obuf1_lb_en <= lb_en when (addr_sel="01") else '0';
obuf2_lb_en <= lb_en when (addr_sel="10") else '0';
obuf3_lb_en <= lb_en when (addr_sel="11") else '0';

-- lb_di multiplexor ----------------------------------------------------------
lb_di     <= obuf0_lb_di when (addr_sel="00") else
             obuf1_lb_di when (addr_sel="01") else
             obuf2_lb_di when (addr_sel="10") else
             obuf3_lb_di when (addr_sel="11") else
	     (others=>'0');

-- lb_drdy multiplexor --------------------------------------------------------
lb_drdy   <= obuf0_lb_drdy when (addr_sel="00") else
             obuf1_lb_drdy when (addr_sel="01") else
             obuf2_lb_drdy when (addr_sel="10") else
             obuf3_lb_drdy when (addr_sel="11") else
	     '0';

end architecture full;
