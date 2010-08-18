--
-- obuf_gmii_top4.vhd:  Output Buffer - 4 obufs + LB entity
-- Copyright (C) 2005 CESNET
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
--            Libor Polcak <polcak_l@liberouter.org>
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
use work.lb_pkg.all; 

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_gmii_top4_mi32 is

component MI32_ASYNC is
   port(
      RESET          : in  std_logic;
      -- Master interface
      CLK_M          : in  std_logic;
      MI_M           : inout t_mi32;
      -- Slave interface
      CLK_S          : in  std_logic;
      MI_S           : inout t_mi32
   );
end component MI32_ASYNC;

   --signal reset          : std_logic;
   
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

   signal mi_m0          : t_mi32;
   signal mi_m1          : t_mi32;
   signal mi_m2          : t_mi32;
   signal mi_m3          : t_mi32;

   signal mi_s0          : t_mi32;
   signal mi_s1          : t_mi32;
   signal mi_s2          : t_mi32;
   signal mi_s3          : t_mi32;

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
   CTRL_CMD   => CTRL_CMD,
   INBANDFCS  => INBANDFCS,
   SKIP_FCS   => SKIP_FCS
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
   ADC_RD   => mi_s0.RD,
   ADC_WR   => mi_s0.WR,
   ADC_ADDR => mi_s0.ADDR(7 downto 2),
   ADC_DI   => mi_s0.DWR,
   ADC_DO   => mi_s0.DRD,
   ADC_DRDY => mi_s0.DRDY
);

-- OBUF 1 instantination ------------------------------------------------------
OBUF1_U : entity work.obuf_gmii
generic map (
   DATA_PATHS => DATA_PATHS,
   DFIFO_SIZE => DFIFO_SIZE,
   SFIFO_SIZE => SFIFO_SIZE,
   CTRL_CMD   => CTRL_CMD,
   INBANDFCS  => INBANDFCS,
   SKIP_FCS   => SKIP_FCS
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
   ADC_RD   => mi_s1.RD,
   ADC_WR   => mi_s1.WR,
   ADC_ADDR => mi_s1.ADDR(7 downto 2),
   ADC_DI   => mi_s1.DWR,
   ADC_DO   => mi_s1.DRD,
   ADC_DRDY => mi_s1.DRDY
);

-- OBUF 2 instantination ------------------------------------------------------
OBUF2_U : entity work.obuf_gmii
generic map (
   DATA_PATHS => DATA_PATHS,
   DFIFO_SIZE => DFIFO_SIZE,
   SFIFO_SIZE => SFIFO_SIZE,
   CTRL_CMD   => CTRL_CMD,
   INBANDFCS  => INBANDFCS,
   SKIP_FCS   => SKIP_FCS
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
   ADC_RD   => mi_s2.RD,
   ADC_WR   => mi_s2.WR,
   ADC_ADDR => mi_s2.ADDR(7 downto 2),
   ADC_DI   => mi_s2.DWR,
   ADC_DO   => mi_s2.DRD,
   ADC_DRDY => mi_s2.DRDY
);

-- OBUF 3 instantination ------------------------------------------------------
OBUF3_U : entity work.obuf_gmii
generic map (
   DATA_PATHS => DATA_PATHS,
   DFIFO_SIZE => DFIFO_SIZE,
   SFIFO_SIZE => SFIFO_SIZE,
   CTRL_CMD   => CTRL_CMD,
   INBANDFCS  => INBANDFCS,
   SKIP_FCS   => SKIP_FCS
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
   ADC_RD   => mi_s3.RD,
   ADC_WR   => mi_s3.WR,
   ADC_ADDR => mi_s3.ADDR(7 downto 2),
   ADC_DI   => mi_s3.DWR,
   ADC_DO   => mi_s3.DRD,
   ADC_DRDY => mi_s3.DRDY
);

mi32_async_u0: MI32_ASYNC
   port map(
      RESET          => reset,
      -- Master interface
      CLK_M          => WRCLK,
      MI_M           => mi_m0,
      -- Slave interface
      CLK_S          => obuf0_adc_clk,
      MI_S           => mi_s0
   );

mi32_async_u1: MI32_ASYNC
   port map(
      RESET          => reset,
      -- Master interface
      CLK_M          => WRCLK,
      MI_M           => mi_m1,
      -- Slave interface
      CLK_S          => obuf1_adc_clk,
      MI_S           => mi_s1
   );

mi32_async_u2: MI32_ASYNC
   port map(
      RESET          => reset,
      -- Master interface
      CLK_M          => WRCLK,
      MI_M           => mi_m2,
      -- Slave interface
      CLK_S          => obuf2_adc_clk,
      MI_S           => mi_s2
   );

mi32_async_u3: MI32_ASYNC
   port map(
      RESET          => reset,
      -- Master interface
      CLK_M          => WRCLK,
      MI_M           => mi_m3,
      -- Slave interface
      CLK_S          => obuf3_adc_clk,
      MI_S           => mi_s3
   );

addr_sel  <= MI.ADDR(9 downto 8);

mi_s0.ARDY <= mi_s0.RD or mi_s0.WR;
mi_s1.ARDY <= mi_s1.RD or mi_s1.WR;
mi_s2.ARDY <= mi_s2.RD or mi_s2.WR;
mi_s3.ARDY <= mi_s3.RD or mi_s3.WR;

-- MI.DWR connection
mi_m0.DWR <= MI.DWR;
mi_m1.DWR <= MI.DWR;
mi_m2.DWR <= MI.DWR;
mi_m3.DWR <= MI.DWR;

-- MI.ADDR connection
mi_m0.ADDR <= MI.ADDR;
mi_m1.ADDR <= MI.ADDR;
mi_m2.ADDR <= MI.ADDR;
mi_m3.ADDR <= MI.ADDR;

-- MI.RD demultiplexor --------------------------------------------------------
mi_m0.RD <= MI.RD when (addr_sel="00") else '0';
mi_m1.RD <= MI.RD when (addr_sel="01") else '0';
mi_m2.RD <= MI.RD when (addr_sel="10") else '0';
mi_m3.RD <= MI.RD when (addr_sel="11") else '0';

-- MI.WR demultiplexor --------------------------------------------------------
mi_m0.WR <= MI.WR when (addr_sel="00") else '0';
mi_m1.WR <= MI.WR when (addr_sel="01") else '0';
mi_m2.WR <= MI.WR when (addr_sel="10") else '0';
mi_m3.WR <= MI.WR when (addr_sel="11") else '0';

-- MI.BE connection
mi_m0.BE <= MI.BE;
mi_m1.BE <= MI.BE;
mi_m2.BE <= MI.BE;
mi_m3.BE <= MI.BE;

-- MI.DRD multiplexor ---------------------------------------------------------
MI.DRD   <= mi_m0.DRD when (addr_sel="00") else
            mi_m1.DRD when (addr_sel="01") else
            mi_m2.DRD when (addr_sel="10") else
            mi_m3.DRD when (addr_sel="11") else
	         (others=>'0');

-- MI.ARDY control --------------------------------------------------------
MI.ARDY   <= mi_m0.ARDY when (addr_sel="00") else
             mi_m1.ARDY when (addr_sel="01") else
             mi_m2.ARDY when (addr_sel="10") else
             mi_m3.ARDY when (addr_sel="11") else
	          '0';

-- MI.DRDY multiplexor --------------------------------------------------------
MI.DRDY   <= mi_m0.DRDY when (addr_sel="00") else
             mi_m1.DRDY when (addr_sel="01") else
             mi_m2.DRDY when (addr_sel="10") else
             mi_m3.DRDY when (addr_sel="11") else
	          '0';

end architecture full;
