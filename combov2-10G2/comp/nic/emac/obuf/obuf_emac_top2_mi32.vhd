-- obuf_emac_top2.vhd:  Output Buffer - 2 obufs + LB entity
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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
use work.emac_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_emac_top2_mi32 is

   signal obuf0_adc_clk  : std_logic;
   signal obuf1_adc_clk  : std_logic;

   signal addr_sel       : std_logic;

   signal mi_m0          : t_mi32;
   signal mi_m1          : t_mi32;

   signal mi_s0          : t_mi32;
   signal mi_s1          : t_mi32;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- OBUF 0 instantination ---------------------------------------------------
   OBUF0_U : entity work.obuf_emac
      generic map(
         DATA_PATHS => DATA_PATHS,
         DFIFO_SIZE => DFIFO_SIZE,
         SFIFO_SIZE => SFIFO_SIZE,
         CTRL_CMD   => CTRL_CMD,
         USECLKEN   => EMAC0_USECLKEN
      )
      port map(
         RESET      => RESET,
   
         -- FrameLink input interface
         WRCLK      => WRCLK,
         DATA       => OBUF0_DATA,
         DREM       => OBUF0_DREM,
         SRC_RDY_N  => OBUF0_SRC_RDY_N,
         SOF_N      => OBUF0_SOF_N,
         SOP_N      => OBUF0_SOP_N,
         EOF_N      => OBUF0_EOF_N,
         EOP_N      => OBUF0_EOP_N,
         DST_RDY_N  => OBUF0_DST_RDY_N,
   
         -- Transmit interface
         EMAC_CLK   => OBUF0_EMAC_CLK,
         EMAC_CE    => OBUF0_EMAC_CE,
         TX_EMAC_D            => OBUF0_TX_EMAC.D,
         TX_EMAC_DVLD         => OBUF0_TX_EMAC.DVLD,
         TX_EMAC_ACK          => OBUF0_TX_EMAC.ACK,
         TX_EMAC_FIRSTBYTE    => OBUF0_TX_EMAC.FIRSTBYTE,
         TX_EMAC_UNDERRUN     => OBUF0_TX_EMAC.UNDERRUN,
         TX_EMAC_COLLISION    => OBUF0_TX_EMAC.COLLISION,
         TX_EMAC_RETRANSMIT   => OBUF0_TX_EMAC.RETRANSMIT,
         TX_EMAC_IFGDELAY     => OBUF0_TX_EMAC.IFGDELAY,
         TX_EMAC_STATS        => OBUF0_TX_EMAC.STATS,
         TX_EMAC_STATSVLD     => OBUF0_TX_EMAC.STATSVLD,
         TX_EMAC_STATSBYTEVLD => OBUF0_TX_EMAC.STATSBYTEVLD,
         TX_EMAC_SPEEDIS10100 => OBUF0_TX_EMAC.SPEEDIS10100,
   
         -- address decoder interface
         ADC_CLK    => obuf0_adc_clk,
         ADC_RD     => mi_s0.rd,
         ADC_WR     => mi_s0.wr,
         ADC_ADDR   => mi_s0.addr(7 downto 2),
         ADC_DI     => mi_s0.dwr,
         ADC_DO     => mi_s0.drd,
         ADC_DRDY   => mi_s0.drdy
      );

   -- OBUF 1 instantination ---------------------------------------------------
   OBUF1_U : entity work.obuf_emac
      generic map(
         DATA_PATHS => DATA_PATHS,
         DFIFO_SIZE => DFIFO_SIZE,
         SFIFO_SIZE => SFIFO_SIZE,
         CTRL_CMD   => CTRL_CMD,
         USECLKEN   => EMAC1_USECLKEN
      )
      port map(
         RESET      => RESET,
   
         -- FrameLink input interface
         WRCLK      => WRCLK,
         DATA       => OBUF1_DATA,
         DREM       => OBUF1_DREM,
         SRC_RDY_N  => OBUF1_SRC_RDY_N,
         SOF_N      => OBUF1_SOF_N,
         SOP_N      => OBUF1_SOP_N,
         EOF_N      => OBUF1_EOF_N,
         EOP_N      => OBUF1_EOP_N,
         DST_RDY_N  => OBUF1_DST_RDY_N,
   
         -- Transmit interface
         EMAC_CLK   => OBUF1_EMAC_CLK,
         EMAC_CE    => OBUF1_EMAC_CE,
         TX_EMAC_D            => OBUF1_TX_EMAC.D,
         TX_EMAC_DVLD         => OBUF1_TX_EMAC.DVLD,
         TX_EMAC_ACK          => OBUF1_TX_EMAC.ACK,
         TX_EMAC_FIRSTBYTE    => OBUF1_TX_EMAC.FIRSTBYTE,
         TX_EMAC_UNDERRUN     => OBUF1_TX_EMAC.UNDERRUN,
         TX_EMAC_COLLISION    => OBUF1_TX_EMAC.COLLISION,
         TX_EMAC_RETRANSMIT   => OBUF1_TX_EMAC.RETRANSMIT,
         TX_EMAC_IFGDELAY     => OBUF1_TX_EMAC.IFGDELAY,
         TX_EMAC_STATS        => OBUF1_TX_EMAC.STATS,
         TX_EMAC_STATSVLD     => OBUF1_TX_EMAC.STATSVLD,
         TX_EMAC_STATSBYTEVLD => OBUF1_TX_EMAC.STATSBYTEVLD,
         TX_EMAC_SPEEDIS10100 => OBUF1_TX_EMAC.SPEEDIS10100,
   
         -- address decoder interface
         ADC_CLK    => obuf1_adc_clk,
         ADC_RD     => mi_s1.rd,
         ADC_WR     => mi_s1.wr,
         ADC_ADDR   => mi_s1.addr(7 downto 2),
         ADC_DI     => mi_s1.dwr,
         ADC_DO     => mi_s1.drd,
         ADC_DRDY   => mi_s1.drdy
      );

   -- MI32 --------------------------------------------------------------------
   mi32_async_u0: entity work.MI32_ASYNC
      port map(
         RESET          => reset,
         -- Master interface
         CLK_M          => WRCLK,
         MI_M           => mi_m0,
         -- Slave interface
         CLK_S          => obuf0_adc_clk,
         MI_S           => mi_s0
      );
   
   mi32_async_u1: entity work.MI32_ASYNC
      port map(
         RESET          => reset,
         -- Master interface
         CLK_M          => WRCLK,
         MI_M           => mi_m1,
         -- Slave interface
         CLK_S          => obuf1_adc_clk,
         MI_S           => mi_s1
      );
   
   addr_sel  <= MI.ADDR(8);
   
   mi_s0.ARDY <= mi_s0.RD or mi_s0.WR;
   mi_s1.ARDY <= mi_s1.RD or mi_s1.WR;
   
   -- MI.DWR connection
   mi_m0.DWR <= MI.DWR;
   mi_m1.DWR <= MI.DWR;
   
   -- MI.ADDR connection
   mi_m0.ADDR <= MI.ADDR;
   mi_m1.ADDR <= MI.ADDR;
   
   -- MI.RD demultiplexor -----------------------------------------------------
   mi_m0.RD <= MI.RD when (addr_sel='0') else '0';
   mi_m1.RD <= MI.RD when (addr_sel='1') else '0';
   
   -- MI.WR demultiplexor -----------------------------------------------------
   mi_m0.WR <= MI.WR when (addr_sel='0') else '0';
   mi_m1.WR <= MI.WR when (addr_sel='1') else '0';
   
   -- MI.BE connection
   mi_m0.BE <= MI.BE;
   mi_m1.BE <= MI.BE;
   
   -- MI.DRD multiplexor ------------------------------------------------------
   MI.DRD   <= mi_m0.DRD when (addr_sel='0') else
               mi_m1.DRD when (addr_sel='1') else
   	         (others=>'0');
   
   -- MI.ARDY control --------------------------------------------------------
   MI.ARDY   <= mi_m0.ARDY when (addr_sel='0') else
                mi_m1.ARDY when (addr_sel='1') else
   	          '0';
   
   -- MI.DRDY multiplexor -----------------------------------------------------
   MI.DRDY   <= mi_m0.DRDY when (addr_sel='0') else
                mi_m1.DRDY when (addr_sel='1') else
   	          '0';

end architecture full;
