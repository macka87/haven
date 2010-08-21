-- obuf_xgmii_sdr_top2_mi32.vhd:  Output Buffer - 2 SDR obufs + LB entity
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

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_xgmii_sdr_top2_mi32 is

   signal addr_sel         : std_logic;
   signal reg_addr_sel     : std_logic;
   signal reg_addr_sel_we  : std_logic;
   
   signal mi0_dwr    : std_logic_vector(31 downto 0);
   signal mi0_addr   : std_logic_vector(31 downto 0);
   signal mi0_rd     : std_logic;
   signal mi0_wr     : std_logic;
   signal mi0_be     : std_logic_vector(3 downto 0);
   signal mi0_drd    : std_logic_vector(31 downto 0);
   signal mi0_ardy   : std_logic;
   signal mi0_drdy   : std_logic;
   
   signal mi1_dwr    : std_logic_vector(31 downto 0);
   signal mi1_addr   : std_logic_vector(31 downto 0);
   signal mi1_rd     : std_logic;
   signal mi1_wr     : std_logic;
   signal mi1_be     : std_logic_vector(3 downto 0);
   signal mi1_drd    : std_logic_vector(31 downto 0);
   signal mi1_ardy   : std_logic;
   signal mi1_drdy   : std_logic;
   
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- OBUF 0 instantination ---------------------------------------------------
   OBUF0_U : entity work.obuf_xgmii_sdr_norec
      generic map(
         CTRL_CMD       => CTRL_CMD,
         FL_WIDTH_RX    => FL_WIDTH_RX,
         DFIFO_SIZE     => DFIFO_SIZE,
         HFIFO_SIZE     => HFIFO_SIZE,
         HFIFO_MEMTYPE  => HFIFO_MEMTYPE
      )
      port map(
         RESET_FL       => FL_RESET,
         FL_CLK         => FL_CLK,
   
         -- XGMII interfaces
         RESET_XGMII    => XGMII_RESET(0),
         CLK_INT        => XGMII_TXCLK(0),
         XGMII_SDR_TXD  => XGMII_TXD(63 downto 0),
         XGMII_SDR_TXC  => XGMII_TXC( 7 downto 0),

         -- FrameLink input interface
         RX_DATA        => OBUF0_RX_DATA,
         RX_REM         => OBUF0_RX_REM,
         RX_SRC_RDY_N   => OBUF0_RX_SRC_RDY_N,
         RX_SOF_N       => OBUF0_RX_SOF_N,
         RX_SOP_N       => OBUF0_RX_SOP_N,
         RX_EOF_N       => OBUF0_RX_EOF_N,
         RX_EOP_N       => OBUF0_RX_EOP_N,
         RX_DST_RDY_N   => OBUF0_RX_DST_RDY_N,

         -- Status interface
         OUTGOING_PCKT  => OUTGOING_PCKT(0),
   
         -- Memory interface
         MI_DWR         => mi0_dwr,
         MI_ADDR        => mi0_addr,
         MI_RD          => mi0_rd,
         MI_WR          => mi0_wr,
         MI_BE          => mi0_be,
         MI_DRD         => mi0_drd,
         MI_ARDY        => mi0_ardy,
         MI_DRDY        => mi0_drdy,
         MI_CLK         => MI_CLK,
         RESET_MI       => MI_RESET
      );

   -- OBUF 1 instantination ---------------------------------------------------
   OBUF1_U : entity work.obuf_xgmii_sdr_norec
      generic map(
         CTRL_CMD       => CTRL_CMD,
         FL_WIDTH_RX    => FL_WIDTH_RX,
         DFIFO_SIZE     => DFIFO_SIZE,
         HFIFO_SIZE     => HFIFO_SIZE,
         HFIFO_MEMTYPE  => HFIFO_MEMTYPE
      )
      port map(
         RESET_FL       => FL_RESET,
         FL_CLK         => FL_CLK,
   
         -- XGMII interfaces
         RESET_XGMII    => XGMII_RESET(1),
         CLK_INT        => XGMII_TXCLK(1),
         XGMII_SDR_TXD  => XGMII_TXD(127 downto 64),
         XGMII_SDR_TXC  => XGMII_TXC( 15 downto  8),

         -- FrameLink input interface
         RX_DATA        => OBUF1_RX_DATA,
         RX_REM         => OBUF1_RX_REM,
         RX_SRC_RDY_N   => OBUF1_RX_SRC_RDY_N,
         RX_SOF_N       => OBUF1_RX_SOF_N,
         RX_SOP_N       => OBUF1_RX_SOP_N,
         RX_EOF_N       => OBUF1_RX_EOF_N,
         RX_EOP_N       => OBUF1_RX_EOP_N,
         RX_DST_RDY_N   => OBUF1_RX_DST_RDY_N,

         -- Status interface
         OUTGOING_PCKT  => OUTGOING_PCKT(1),
   
         -- Memory interface
         MI_DWR         => mi1_dwr,
         MI_ADDR        => mi1_addr,
         MI_RD          => mi1_rd,
         MI_WR          => mi1_wr,
         MI_BE          => mi1_be,
         MI_DRD         => mi1_drd,
         MI_ARDY        => mi1_ardy,
         MI_DRDY        => mi1_drdy,
         MI_CLK         => MI_CLK,
         RESET_MI       => MI_RESET
      );

   -- MI Splitter -------------------------------------------------------------
   MI_SPLITTER_I: entity work.MI_SPLITTER
   generic map(
      ITEMS      => 2,
      ADDR_WIDTH => 8,
      DATA_WIDTH => 32,
      PIPE       => false
   )
   port map(
      -- Common interface
      CLK      => MI_CLK,
      RESET    => MI_RESET,

      -- Input MI interface
      IN_DWR   => MI.DWR,
      IN_ADDR  => MI.ADDR(8 downto 0),
      IN_BE    => MI.BE,
      IN_RD    => MI.RD,
      IN_WR    => MI.WR,
      IN_ARDY  => MI.ARDY,
      IN_DRD   => MI.DRD,
      IN_DRDY  => MI.DRDY,

      -- Output MI interfaces
      OUT_DWR(31 downto  0)  => mi0_dwr,
      OUT_DWR(63 downto 32)  => mi1_dwr,
      OUT_ADDR(7  downto  0) => mi0_addr(7 downto 0),
      OUT_ADDR(15 downto  8) => mi1_addr(7 downto 0),
      OUT_BE(3 downto 0)     => mi0_be,
      OUT_BE(7 downto 4)     => mi1_be,
      OUT_RD(0)   => mi0_rd,
      OUT_RD(1)   => mi1_rd,
      OUT_WR(0)   => mi0_wr,
      OUT_WR(1)   => mi1_wr,
      OUT_ARDY(0) => mi0_ardy,
      OUT_ARDY(1) => mi1_ardy,
      OUT_DRD(31 downto  0) => mi0_drd,
      OUT_DRD(63 downto 32) => mi1_drd,
      OUT_DRDY(0) => mi0_drdy,
      OUT_DRDY(1) => mi1_drdy
   );
   
   mi0_addr(31 downto 8) <= (others => '0');
   mi1_addr(31 downto 8) <= (others => '0');
   

end architecture full;
