-- ibuf_xgmii_top2_mi32.vhd: Input Buffer - 2 ibufs + MI_32 interface
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
--

library IEEE;
use IEEE.std_logic_1164.all;
use work.math_pack.all;
use work.ibuf_general_pkg.all;
use work.lb_pkg.all; 


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_xgmii_top2_mi32 is
   
   signal addr_sel       : std_logic;
   signal reg_addr_sel   : std_logic;
   signal reg_addr_sel_we : std_logic;

   signal mi0          : t_mi32;
   signal mi1          : t_mi32;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- IBUF 0 instantination ---------------------------------------------------
   IBUF0_U : entity work.ibuf_xgmii
      generic map(
         DFIFO_SIZE     => DFIFO_SIZE,
         HFIFO_SIZE     => HFIFO_SIZE,
         HFIFO_MEMTYPE  => HFIFO_MEMTYPE,
         CTRL_HDR_EN    => CTRL_HDR_EN,
         CTRL_FTR_EN    => CTRL_FTR_EN,
         MACS           => MACS,
         INBANDFCS      => INBANDFCS,
         CNT_ERROR_SIZE => CNT_ERROR_SIZE,
         FL_WIDTH_TX    => FL_WIDTH_TX,
         FL_RELAY       => FL_RELAY     
      )
      port map (
         RESET          => RESET,
   
         -- XGMII RX interface
         XGMII_RXCLK    => IBUF0_RXCLK,
         XGMII_RXD      => IBUF0_RXD,
         XGMII_RXC      => IBUF0_RXC,

         -- Sampling unit interface
         INT_CLK        => IBUF0_SAU_CLK,
         INT_RESET      => IBUF0_SAU_RESET,
         SAU_REQ        => IBUF0_SAU_REQ,
         SAU_ACCEPT     => IBUF0_SAU_ACCEPT,
         SAU_DV         => IBUF0_SAU_DV,

         -- PACODAG interface
         CTRL_CLK       => IBUF0_CTRL_CLK,
         CTRL_RESET     => IBUF0_CTRL_RESET,
         CTRL_DATA      => IBUF0_CTRL_DATA,
         CTRL_REM       => IBUF0_CTRL_REM,
         CTRL_SRC_RDY_N => IBUF0_CTRL_SRC_RDY_N,
         CTRL_SOP_N     => IBUF0_CTRL_SOP_N,
         CTRL_EOP_N     => IBUF0_CTRL_EOP_N,
         CTRL_DST_RDY_N => IBUF0_CTRL_DST_RDY_N,
         CTRL_REQ       => IBUF0_CTRL_SOP,
         CTRL_SEND      => IBUF0_STAT_DV,
         CTRL_RELEASE   => open,
         CTRL_RDY       => IBUF0_CTRL_RDY,
   
         -- IBUF status interface
         STAT           => IBUF0_STAT,
         STAT_VLD       => open, -- Active when CTRL_SEND = '1'

         LINK_UP        => IBUF0_LINK_UP,
         INCOMING_PCKT  => IBUF0_INCOMING_PCKT,
   
         -- FrameLink interface
         FL_CLK         => FL_CLK,
         TX_DATA        => IBUF0_TX_DATA,
         TX_REM         => IBUF0_TX_REM,
         TX_SRC_RDY_N   => IBUF0_TX_SRC_RDY_N,
         TX_SOF_N       => IBUF0_TX_SOF_N,
         TX_SOP_N       => IBUF0_TX_SOP_N,
         TX_EOF_N       => IBUF0_TX_EOF_N,
         TX_EOP_N       => IBUF0_TX_EOP_N,
         TX_DST_RDY_N   => IBUF0_TX_DST_RDY_N,
   
         -- Address decoder interface
         MI_CLK   => MI_CLK,
         MI       => mi0
      );


   -- IBUF 1 instantination ---------------------------------------------------
   IBUF1_U : entity work.ibuf_xgmii
      generic map(
         DFIFO_SIZE     => DFIFO_SIZE,
         HFIFO_SIZE     => HFIFO_SIZE,
         HFIFO_MEMTYPE  => HFIFO_MEMTYPE,
         CTRL_HDR_EN    => CTRL_HDR_EN,
         CTRL_FTR_EN    => CTRL_FTR_EN,
         MACS           => MACS,
         CNT_ERROR_SIZE => CNT_ERROR_SIZE,
         FL_WIDTH_TX    => FL_WIDTH_TX,
         FL_RELAY       => FL_RELAY     
      )
      port map (
         RESET          => RESET,
   
         -- XGMII RX interface
         XGMII_RXCLK    => IBUF1_RXCLK,
         XGMII_RXD      => IBUF1_RXD,
         XGMII_RXC      => IBUF1_RXC,
   
         -- Sampling unit interface
         INT_CLK        => IBUF1_SAU_CLK,
         INT_RESET        => IBUF1_SAU_RESET,
         SAU_REQ        => IBUF1_SAU_REQ,
         SAU_ACCEPT     => IBUF1_SAU_ACCEPT,
         SAU_DV         => IBUF1_SAU_DV,
   
         -- PACODAG interface
         CTRL_CLK       => IBUF1_CTRL_CLK,
         CTRL_RESET     => IBUF1_CTRL_RESET,
         CTRL_DATA      => IBUF1_CTRL_DATA,
         CTRL_REM       => IBUF1_CTRL_REM,
         CTRL_SRC_RDY_N => IBUF1_CTRL_SRC_RDY_N,
         CTRL_SOP_N     => IBUF1_CTRL_SOP_N,
         CTRL_EOP_N     => IBUF1_CTRL_EOP_N,
         CTRL_DST_RDY_N => IBUF1_CTRL_DST_RDY_N,
         CTRL_REQ       => IBUF1_CTRL_SOP,
         CTRL_SEND      => IBUF1_STAT_DV,
         CTRL_RELEASE   => open,
         CTRL_RDY       => IBUF1_CTRL_RDY,
   
         -- IBUF status interface
         STAT           => IBUF1_STAT,
         STAT_VLD       => open, -- Active when  CTRL_SEND = '1'

         LINK_UP        => IBUF1_LINK_UP,
         INCOMING_PCKT  => IBUF1_INCOMING_PCKT,
   
         -- FrameLink interface
         FL_CLK         => FL_CLK,
         TX_DATA        => IBUF1_TX_DATA,
         TX_REM         => IBUF1_TX_REM,
         TX_SRC_RDY_N   => IBUF1_TX_SRC_RDY_N,
         TX_SOF_N       => IBUF1_TX_SOF_N,
         TX_SOP_N       => IBUF1_TX_SOP_N,
         TX_EOF_N       => IBUF1_TX_EOF_N,
         TX_EOP_N       => IBUF1_TX_EOP_N,
         TX_DST_RDY_N   => IBUF1_TX_DST_RDY_N,
   
         -- Address decoder interface
         MI_CLK   => MI_CLK,
         MI       => mi1
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
   
   -- MI.RD demultiplexor --------------------------------------------------------
   mi0.RD <= MI.RD when (addr_sel='0') else '0';
   mi1.RD <= MI.RD when (addr_sel='1') else '0';
   
   -- MI.WR demultiplexor --------------------------------------------------------
   mi0.WR <= MI.WR when (addr_sel='0') else '0';
   mi1.WR <= MI.WR when (addr_sel='1') else '0';
   
   -- MI.BE connection
   mi0.BE <= MI.BE;
   mi1.BE <= MI.BE;
   
   -- MI.DRD multiplexor ---------------------------------------------------------
   MI.DRD   <= mi0.DRD when (reg_addr_sel='0') else
               mi1.DRD when (reg_addr_sel='1') else
   	         (others=>'0');
   
   -- MI.ARDY multiplexor --------------------------------------------------------
   MI.ARDY   <= mi0.ARDY when (addr_sel='0') else
                mi1.ARDY when (addr_sel='1') else
   	          '0';
   
   -- MI.DRDY multiplexor --------------------------------------------------------
   MI.DRDY   <= mi0.DRDY when (reg_addr_sel='0') else
                mi1.DRDY when (reg_addr_sel='1') else
   	          '0';

end architecture full;
