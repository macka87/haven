--
-- ibuf_gmii_top4_hfe2.vhd:  Input Buffer - 4 ibufs + LB entity
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
architecture full of ibuf_gmii_top4 is

   signal ibuf0_adc_clk  : std_logic;
   signal ibuf0_adc_rd   : std_logic;
   signal ibuf0_adc_wr   : std_logic;
   signal ibuf0_adc_addr : std_logic_vector(5 downto 0);
   signal ibuf0_adc_di   : std_logic_vector(31 downto 0);
   signal ibuf0_adc_do   : std_logic_vector(31 downto 0);
   signal ibuf0_adc_drdy : std_logic;

   signal ibuf1_adc_clk  : std_logic;
   signal ibuf1_adc_rd   : std_logic;
   signal ibuf1_adc_wr   : std_logic;
   signal ibuf1_adc_addr : std_logic_vector(5 downto 0);
   signal ibuf1_adc_di   : std_logic_vector(31 downto 0);
   signal ibuf1_adc_do   : std_logic_vector(31 downto 0);
   signal ibuf1_adc_drdy : std_logic;

   signal ibuf2_adc_clk  : std_logic;
   signal ibuf2_adc_rd   : std_logic;
   signal ibuf2_adc_wr   : std_logic;
   signal ibuf2_adc_addr : std_logic_vector(5 downto 0);
   signal ibuf2_adc_di   : std_logic_vector(31 downto 0);
   signal ibuf2_adc_do   : std_logic_vector(31 downto 0);
   signal ibuf2_adc_drdy : std_logic;

   signal ibuf3_adc_clk  : std_logic;
   signal ibuf3_adc_rd   : std_logic;
   signal ibuf3_adc_wr   : std_logic;
   signal ibuf3_adc_addr : std_logic_vector(5 downto 0);
   signal ibuf3_adc_di   : std_logic_vector(31 downto 0);
   signal ibuf3_adc_do   : std_logic_vector(31 downto 0);
   signal ibuf3_adc_drdy : std_logic;

   signal ibuf0_lb_en    : std_logic;
   signal ibuf0_lb_di    : std_logic_vector(15 downto 0);
   signal ibuf0_lb_drdy  : std_logic;

   signal ibuf1_lb_en    : std_logic;
   signal ibuf1_lb_di    : std_logic_vector(15 downto 0);
   signal ibuf1_lb_drdy  : std_logic;

   signal ibuf2_lb_en    : std_logic;
   signal ibuf2_lb_di    : std_logic_vector(15 downto 0);
   signal ibuf2_lb_drdy  : std_logic;

   signal ibuf3_lb_en    : std_logic;
   signal ibuf3_lb_di    : std_logic_vector(15 downto 0);
   signal ibuf3_lb_drdy  : std_logic;

   signal lb_en          : std_logic;
   signal lb_rw          : std_logic;
   signal lb_addr        : std_logic_vector(8 downto 0);
   signal lb_di          : std_logic_vector(15 downto 0);
   signal lb_do          : std_logic_vector(15 downto 0);
   signal lb_drdy        : std_logic;
   signal lb_ardy        : std_logic;

   signal addr_sel       : std_logic_vector(1 downto 0);
   signal reg_addr_sel : std_logic_vector(1 downto 0);
   signal reg_addr_sel_we : std_logic;
   signal reg_lb_en     : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- IBUF 0 instantination ------------------------------------------------------
IBUF0_U : entity work.ibuf_gmii
   generic map(
      DATA_PATHS  => DATA_PATHS,
      DFIFO_SIZE  => DFIFO_SIZE,
      HFIFO_SIZE  => HFIFO_SIZE,
      MACS        => MACS,
      INBANDFCS   => INBANDFCS
   )
   port map (
      RESET    => reset,

      -- GMII RX interface
      RXCLK     => IBUF0_RXCLK,
      RXD       => IBUF0_RXD,
      RXDV      => IBUF0_RXDV,
      RXER      => IBUF0_RXER,

      -- PHY status interface
      LINK_STATUS       => '0', --PHY0_LINK_STATUS,
      DUPLEX_MODE       => '0', --PHY0_DUPLEX_MODE,
      SPEED             => "00", --PHY0_SPEED,
      SGMII             => '0', --PHY0_SGMII,

      -- PACODAG interface
      CTRL_CLK    => IBUF0_CTRL_CLK,
      CTRL_DI        => IBUF0_CTRL_DATA,
      CTRL_REM       => IBUF0_CTRL_REM,
      CTRL_SRC_RDY_N => IBUF0_CTRL_SRC_RDY_N,
      CTRL_SOP_N     => IBUF0_CTRL_SOP_N,
      CTRL_EOP_N     => IBUF0_CTRL_EOP_N,
      CTRL_DST_RDY_N => IBUF0_CTRL_DST_RDY_N,
      CTRL_HDR_EN => IBUF0_CTRL_HDR_EN,
      CTRL_FTR_EN => IBUF0_CTRL_FTR_EN,
      CTRL_RDY    => IBUF0_CTRL_RDY,

      -- IBUF status interface
      SOP         => IBUF0_SOP,
      STAT        => IBUF0_STAT,
      STAT_DV     => IBUF0_STAT_DV,

      -- Sampling unit interface
      SAU_ACCEPT => IBUF0_SAU_ACCEPT,
      SAU_DV     => IBUF0_SAU_DV,

      -- FrameLink interface
      RDCLK      => IBUF0_RDCLK,
      DATA       => IBUF0_DATA,
      DREM       => IBUF0_DREM,
      SRC_RDY_N  => IBUF0_SRC_RDY_N,
      SOF_N      => IBUF0_SOF_N,
      SOP_N      => IBUF0_SOP_N,
      EOF_N      => IBUF0_EOF_N,
      EOP_N      => IBUF0_EOP_N,
      DST_RDY_N  => IBUF0_DST_RDY_N,

      -- Address decoder interface
      ADC_CLK  => ibuf0_adc_clk,
      ADC_RD   => ibuf0_adc_rd,
      ADC_WR   => ibuf0_adc_wr,
      ADC_ADDR => ibuf0_adc_addr,
      ADC_DI   => ibuf0_adc_di,
      ADC_DO   => ibuf0_adc_do,
      ADC_DRDY => ibuf0_adc_drdy
);      

-- IBUF 1 instantination ------------------------------------------------------
IBUF1_U : entity work.ibuf_gmii
   generic map(
      DATA_PATHS  => DATA_PATHS,
      DFIFO_SIZE  => DFIFO_SIZE,
      HFIFO_SIZE  => HFIFO_SIZE,
      MACS        => MACS,
      INBANDFCS   => INBANDFCS

   )
   port map (
      RESET    => reset,

      -- GMII RX interface
      RXCLK     => IBUF1_RXCLK,
      RXD       => IBUF1_RXD,
      RXDV      => IBUF1_RXDV,
      RXER      => IBUF1_RXER,

      -- PHY status interface
      LINK_STATUS       => '0', --PHY1_LINK_STATUS,
      DUPLEX_MODE       => '0', --PHY1_DUPLEX_MODE,
      SPEED             => "00", --PHY1_SPEED,
      SGMII             => '0', --PHY1_SGMII,

      -- PACODAG interface
      CTRL_CLK    => IBUF1_CTRL_CLK,
      CTRL_DI        => IBUF1_CTRL_DATA,
      CTRL_REM       => IBUF1_CTRL_REM,
      CTRL_SRC_RDY_N => IBUF1_CTRL_SRC_RDY_N,
      CTRL_SOP_N     => IBUF1_CTRL_SOP_N,
      CTRL_EOP_N     => IBUF1_CTRL_EOP_N,
      CTRL_DST_RDY_N => IBUF1_CTRL_DST_RDY_N,
      CTRL_HDR_EN => IBUF1_CTRL_HDR_EN,
      CTRL_FTR_EN => IBUF1_CTRL_FTR_EN,
      CTRL_RDY    => IBUF1_CTRL_RDY,

      -- IBUF status interface
      SOP         => IBUF1_SOP,
      STAT        => IBUF1_STAT,
      STAT_DV     => IBUF1_STAT_DV,

      -- Sampling unit interface
      SAU_ACCEPT => IBUF1_SAU_ACCEPT,
      SAU_DV     => IBUF1_SAU_DV,

      -- FrameLink interface
      RDCLK      => IBUF1_RDCLK,
      DATA       => IBUF1_DATA,
      DREM       => IBUF1_DREM,
      SRC_RDY_N  => IBUF1_SRC_RDY_N,
      SOF_N      => IBUF1_SOF_N,
      SOP_N      => IBUF1_SOP_N,
      EOF_N      => IBUF1_EOF_N,
      EOP_N      => IBUF1_EOP_N,
      DST_RDY_N  => IBUF1_DST_RDY_N,

      -- Address decoder interface
      ADC_CLK  => ibuf1_adc_clk,
      ADC_RD   => ibuf1_adc_rd,
      ADC_WR   => ibuf1_adc_wr,
      ADC_ADDR => ibuf1_adc_addr,
      ADC_DI   => ibuf1_adc_di,
      ADC_DO   => ibuf1_adc_do,
      ADC_DRDY => ibuf1_adc_drdy
);

-- IBUF 2 instantination ------------------------------------------------------
IBUF2_U : entity work.ibuf_gmii
   generic map(
      DATA_PATHS  => DATA_PATHS,
      DFIFO_SIZE  => DFIFO_SIZE,
      HFIFO_SIZE  => HFIFO_SIZE,
      MACS        => MACS,
      INBANDFCS   => INBANDFCS

   )
   port map (
      RESET    => reset,

      -- GMII RX interface
      RXCLK     => IBUF2_RXCLK,
      RXD       => IBUF2_RXD,
      RXDV      => IBUF2_RXDV,
      RXER      => IBUF2_RXER,

      -- PHY status interface
      LINK_STATUS       => '0', --PHY2_LINK_STATUS,
      DUPLEX_MODE       => '0', --PHY2_DUPLEX_MODE,
      SPEED             => "00", --PHY2_SPEED,
      SGMII             => '0', --PHY2_SGMII,

      -- PACODAG interface
      CTRL_CLK    => IBUF2_CTRL_CLK,
      CTRL_DI        => IBUF2_CTRL_DATA,
      CTRL_REM       => IBUF2_CTRL_REM,
      CTRL_SRC_RDY_N => IBUF2_CTRL_SRC_RDY_N,
      CTRL_SOP_N     => IBUF2_CTRL_SOP_N,
      CTRL_EOP_N     => IBUF2_CTRL_EOP_N,
      CTRL_DST_RDY_N => IBUF2_CTRL_DST_RDY_N,
      CTRL_HDR_EN => IBUF2_CTRL_HDR_EN,
      CTRL_FTR_EN => IBUF2_CTRL_FTR_EN,
      CTRL_RDY    => IBUF2_CTRL_RDY,

      -- IBUF status interface
      SOP         => IBUF2_SOP,
      STAT        => IBUF2_STAT,
      STAT_DV     => IBUF2_STAT_DV,

      -- Sampling unit interface
      SAU_ACCEPT => IBUF2_SAU_ACCEPT,
      SAU_DV     => IBUF2_SAU_DV,

      -- FrameLink interface
      RDCLK      => IBUF2_RDCLK,
      DATA       => IBUF2_DATA,
      DREM       => IBUF2_DREM,
      SRC_RDY_N  => IBUF2_SRC_RDY_N,
      SOF_N      => IBUF2_SOF_N,
      SOP_N      => IBUF2_SOP_N,
      EOF_N      => IBUF2_EOF_N,
      EOP_N      => IBUF2_EOP_N,
      DST_RDY_N  => IBUF2_DST_RDY_N,

      -- Address decoder interface
      ADC_CLK  => ibuf2_adc_clk,
      ADC_RD   => ibuf2_adc_rd,
      ADC_WR   => ibuf2_adc_wr,
      ADC_ADDR => ibuf2_adc_addr,
      ADC_DI   => ibuf2_adc_di,
      ADC_DO   => ibuf2_adc_do,
      ADC_DRDY => ibuf2_adc_drdy
);

-- IBUF 3 instantination ------------------------------------------------------
IBUF3_U : entity work.ibuf_gmii
   generic map(
      DATA_PATHS  => DATA_PATHS,
      DFIFO_SIZE  => DFIFO_SIZE,
      HFIFO_SIZE  => HFIFO_SIZE,
      MACS        => MACS,
      INBANDFCS   => INBANDFCS

   )
   port map (
      RESET    => reset,

      -- GMII RX interface
      RXCLK     => IBUF3_RXCLK,
      RXD       => IBUF3_RXD,
      RXDV      => IBUF3_RXDV,
      RXER      => IBUF3_RXER,

      -- PHY status interface
      LINK_STATUS       => '0', --PHY3_LINK_STATUS,
      DUPLEX_MODE       => '0', --PHY3_DUPLEX_MODE,
      SPEED             => "00", --PHY3_SPEED,
      SGMII             => '0', --PHY3_SGMII,

      -- PACODAG interface
      CTRL_CLK    => IBUF3_CTRL_CLK,
      CTRL_DI        => IBUF3_CTRL_DATA,
      CTRL_REM       => IBUF3_CTRL_REM,
      CTRL_SRC_RDY_N => IBUF3_CTRL_SRC_RDY_N,
      CTRL_SOP_N     => IBUF3_CTRL_SOP_N,
      CTRL_EOP_N     => IBUF3_CTRL_EOP_N,
      CTRL_DST_RDY_N => IBUF3_CTRL_DST_RDY_N,
      CTRL_HDR_EN => IBUF3_CTRL_HDR_EN,
      CTRL_FTR_EN => IBUF3_CTRL_FTR_EN,
      CTRL_RDY    => IBUF3_CTRL_RDY,

      -- IBUF status interface
      SOP         => IBUF3_SOP,
      STAT        => IBUF3_STAT,
      STAT_DV     => IBUF3_STAT_DV,

      -- Sampling unit interface
      SAU_ACCEPT => IBUF3_SAU_ACCEPT,
      SAU_DV     => IBUF3_SAU_DV,

      -- FrameLink interface
      RDCLK      => IBUF3_RDCLK,
      DATA       => IBUF3_DATA,
      DREM       => IBUF3_DREM,
      SRC_RDY_N  => IBUF3_SRC_RDY_N,
      SOF_N      => IBUF3_SOF_N,
      SOP_N      => IBUF3_SOP_N,
      EOF_N      => IBUF3_EOF_N,
      EOP_N      => IBUF3_EOP_N,
      DST_RDY_N  => IBUF3_DST_RDY_N,

      -- Address decoder interface
      ADC_CLK  => ibuf3_adc_clk,
      ADC_RD   => ibuf3_adc_rd,
      ADC_WR   => ibuf3_adc_wr,
      ADC_ADDR => ibuf3_adc_addr,
      ADC_DI   => ibuf3_adc_di,
      ADC_DO   => ibuf3_adc_do,
      ADC_DRDY => ibuf3_adc_drdy
);

-- LBCONN_MEM instantination --------------------------------------------------
LBCONN_MEM_U : entity work.lbconn_mem
generic map(
   BASE           => ADDR_BASE,  -- base address
   ADDR_WIDTH     => 9 -- address bus width
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

-- LB_ASYNC for each IBUF instantination --------------------------------------
LB_ASYNC0_U: entity work.lb_async
generic map(
   AS_DATA_DELAY  => 1,
   ADDR_WIDTH     => 7
)
port map(
   -- Global interface
   RESET    => reset,

   -- lbconn_mem interface
   LB_CLK   => LBCLK,
   LB_EN    => ibuf0_lb_en,
   LB_RW    => lb_rw,
   LB_ADDR  => lb_addr(6 downto 0),
   LB_DI    => lb_do,
   LB_DO    => ibuf0_lb_di,
   LB_ARDY  => open,
   LB_DRDY  => ibuf0_lb_drdy,

   -- ssynchronous address decoder interface
   AS_CLK   => ibuf0_adc_clk,
   AS_ADDR  => ibuf0_adc_addr,
   AS_DI    => ibuf0_adc_di,
   AS_RD    => ibuf0_adc_rd,
   AS_WR    => ibuf0_adc_wr,
   AS_DO    => ibuf0_adc_do
);

LB_ASYNC1_U: entity work.lb_async
generic map(
   AS_DATA_DELAY  => 1,
   ADDR_WIDTH     => 7
)
port map(
   -- Global interface
   RESET    => reset,

   -- lbconn_mem interface
   LB_CLK   => LBCLK,
   LB_EN    => ibuf1_lb_en,
   LB_RW    => lb_rw,
   LB_ADDR  => lb_addr(6 downto 0),
   LB_DI    => lb_do,
   LB_DO    => ibuf1_lb_di,
   LB_ARDY  => open,
   LB_DRDY  => ibuf1_lb_drdy,

   -- ssynchronous address decoder interface
   AS_CLK   => ibuf1_adc_clk,
   AS_ADDR  => ibuf1_adc_addr,
   AS_DI    => ibuf1_adc_di,
   AS_RD    => ibuf1_adc_rd,
   AS_WR    => ibuf1_adc_wr,
   AS_DO    => ibuf1_adc_do
);

LB_ASYNC2_U: entity work.lb_async
generic map(
   AS_DATA_DELAY  => 1,
   ADDR_WIDTH     => 7
)
port map(
   -- Global interface
   RESET    => reset,

   -- lbconn_mem interface
   LB_CLK   => LBCLK,
   LB_EN    => ibuf2_lb_en,
   LB_RW    => lb_rw,
   LB_ADDR  => lb_addr(6 downto 0),
   LB_DI    => lb_do,
   LB_DO    => ibuf2_lb_di,
   LB_ARDY  => open,
   LB_DRDY  => ibuf2_lb_drdy,

   -- ssynchronous address decoder interface
   AS_CLK   => ibuf2_adc_clk,
   AS_ADDR  => ibuf2_adc_addr,
   AS_DI    => ibuf2_adc_di,
   AS_RD    => ibuf2_adc_rd,
   AS_WR    => ibuf2_adc_wr,
   AS_DO    => ibuf2_adc_do
);

LB_ASYNC3_U: entity work.lb_async
generic map(
   AS_DATA_DELAY  => 1,
   ADDR_WIDTH     => 7
)
port map(
   -- Global interface
   RESET    => reset,

   -- lbconn_mem interface
   LB_CLK   => LBCLK,
   LB_EN    => ibuf3_lb_en,
   LB_RW    => lb_rw,
   LB_ADDR  => lb_addr(6 downto 0),
   LB_DI    => lb_do,
   LB_DO    => ibuf3_lb_di,
   LB_ARDY  => open,
   LB_DRDY  => ibuf3_lb_drdy,

   -- ssynchronous address decoder interface
   AS_CLK   => ibuf3_adc_clk,
   AS_ADDR  => ibuf3_adc_addr,
   AS_DI    => ibuf3_adc_di,
   AS_RD    => ibuf3_adc_rd,
   AS_WR    => ibuf3_adc_wr,
   AS_DO    => ibuf3_adc_do
);

addr_sel  <= lb_addr (8 downto 7);

process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_lb_en <= '0';
   elsif (LBCLK'event AND LBCLK = '1') then
      reg_lb_en <= lb_en;
   end if;
end process;

reg_addr_sel_we <= lb_en and not reg_lb_en;
process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_addr_sel <= (others => '0');
   elsif (LBCLK'event AND LBCLK = '1') then
      if (reg_addr_sel_we = '1') then
         reg_addr_sel <= addr_sel;
      end if;
   end if;
end process;

-- lb_en demultiplexor --------------------------------------------------------
ibuf0_lb_en <= lb_en when (addr_sel="00") else '0';
ibuf1_lb_en <= lb_en when (addr_sel="01") else '0';
ibuf2_lb_en <= lb_en when (addr_sel="10") else '0';
ibuf3_lb_en <= lb_en when (addr_sel="11") else '0';

-- lb_di multiplexor ----------------------------------------------------------
lb_di     <= ibuf0_lb_di when (reg_addr_sel="00") else
             ibuf1_lb_di when (reg_addr_sel="01") else
             ibuf2_lb_di when (reg_addr_sel="10") else
             ibuf3_lb_di when (reg_addr_sel="11") else
	     (others=>'0');

-- lb_drdy multiplexor --------------------------------------------------------
lb_drdy   <= ibuf0_lb_drdy when (reg_addr_sel="00") else
             ibuf1_lb_drdy when (reg_addr_sel="01") else
             ibuf2_lb_drdy when (reg_addr_sel="10") else
             ibuf3_lb_drdy when (reg_addr_sel="11") else
	     '0';

end architecture full;
