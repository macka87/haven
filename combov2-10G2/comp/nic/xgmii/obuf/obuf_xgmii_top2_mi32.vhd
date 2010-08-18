-- obuf_xgmii_top2_mi32.vhd:  Output Buffer - 2 obufs + LB entity
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
architecture full of obuf_xgmii_top2_mi32 is

   signal addr_sel         : std_logic;
   signal reg_addr_sel     : std_logic;
   signal reg_addr_sel_we  : std_logic;

   signal mi0        : t_mi32;
   signal mi1        : t_mi32;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- OBUF 0 instantination ---------------------------------------------------
   OBUF0_U : entity work.obuf_xgmii
      generic map(
         CTRL_CMD       => CTRL_CMD,
         FL_WIDTH_RX    => FL_WIDTH_RX,
         DFIFO_SIZE     => DFIFO_SIZE,
         HFIFO_SIZE     => HFIFO_SIZE,
         HFIFO_MEMTYPE  => HFIFO_MEMTYPE
      )
      port map(
         RESET          => RESET,
         FL_CLK         => FL_CLK,
   
         -- XGMII interfaces
         XGMII_TXCLK    => XGMII_TXCLK(0),
         XGMII_TXD      => XGMII_TXD(31 downto 0),
         XGMII_TXC      => XGMII_TXC(3 downto 0),
         TX_CLK_REF     => TX_CLK_REF,

         -- FrameLink input interface
         RX_DATA        => OBUF0_RX_DATA,
         RX_REM         => OBUF0_RX_REM,
         RX_SRC_RDY_N   => OBUF0_RX_SRC_RDY_N,
         RX_SOF_N       => OBUF0_RX_SOF_N,
         RX_SOP_N       => OBUF0_RX_SOP_N,
         RX_EOF_N       => OBUF0_RX_EOF_N,
         RX_EOP_N       => OBUF0_RX_EOP_N,
         RX_DST_RDY_N   => OBUF0_RX_DST_RDY_N,
   
         -- Memory interface
         MI             => mi0,
         MI_CLK         => MI_CLK
      );

   -- OBUF 1 instantination ---------------------------------------------------
   OBUF1_U : entity work.obuf_xgmii
      generic map(
         CTRL_CMD       => CTRL_CMD,
         FL_WIDTH_RX    => FL_WIDTH_RX,
         DFIFO_SIZE     => DFIFO_SIZE,
         HFIFO_SIZE     => HFIFO_SIZE,
         HFIFO_MEMTYPE  => HFIFO_MEMTYPE
      )
      port map(
         RESET          => RESET,
         FL_CLK         => FL_CLK,
   
         -- XGMII interfaces
         XGMII_TXCLK    => XGMII_TXCLK(1),
         XGMII_TXD      => XGMII_TXD(63 downto 32),
         XGMII_TXC      => XGMII_TXC(7 downto 4),
         TX_CLK_REF     => TX_CLK_REF,

         -- FrameLink input interface
         RX_DATA        => OBUF1_RX_DATA,
         RX_REM         => OBUF1_RX_REM,
         RX_SRC_RDY_N   => OBUF1_RX_SRC_RDY_N,
         RX_SOF_N       => OBUF1_RX_SOF_N,
         RX_SOP_N       => OBUF1_RX_SOP_N,
         RX_EOF_N       => OBUF1_RX_EOF_N,
         RX_EOP_N       => OBUF1_RX_EOP_N,
         RX_DST_RDY_N   => OBUF1_RX_DST_RDY_N,
   
         -- Memory interface
         MI             => mi1,
         MI_CLK         => MI_CLK
      );

   addr_sel  <= MI.ADDR(8);
   
   reg_addr_sel_we <= MI.RD or MI.WR;
   process(RESET, MI_CLK)
   begin
      if (RESET = '1') then
         reg_addr_sel <= '0';
      elsif (MI_CLK'event AND MI_CLK = '1') then
         if (reg_addr_sel_we = '1') then
            reg_addr_sel <= addr_sel;
         end if;
      end if;
   end process;

   -- MI.DWR connection
   mi0.DWR <= MI.DWR;
   mi1.DWR <= MI.DWR;
   
   -- MI.ADDR connection
   mi0.ADDR <= MI.ADDR;
   mi1.ADDR <= MI.ADDR;
   
   -- MI.RD demultiplexor -----------------------------------------------------
   mi0.RD <= MI.RD when (addr_sel='0') else '0';
   mi1.RD <= MI.RD when (addr_sel='1') else '0';
   
   -- MI.WR demultiplexor -----------------------------------------------------
   mi0.WR <= MI.WR when (addr_sel='0') else '0';
   mi1.WR <= MI.WR when (addr_sel='1') else '0';
   
   -- MI.BE connection
   mi0.BE <= MI.BE;
   mi1.BE <= MI.BE;
   
   -- MI.DRD multiplexor ------------------------------------------------------
   MI.DRD   <= mi0.DRD when (addr_sel='0') else
               mi1.DRD when (addr_sel='1') else
   	         (others=>'0');
   
   -- MI.ARDY control --------------------------------------------------------
   MI.ARDY   <= mi0.ARDY when (addr_sel='0') else
                mi1.ARDY when (addr_sel='1') else
   	          '0';
   
   -- MI.DRDY multiplexor -----------------------------------------------------
   MI.DRDY   <= mi0.DRDY when (addr_sel='0') else
                mi1.DRDY when (addr_sel='1') else
   	          '0';

end architecture full;
