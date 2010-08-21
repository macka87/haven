-- ibuf_emac_top2_mi32_ent.vhd: Input Buffer - 2 ibufs + MI_32 interface
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
use work.fifo_pkg.all;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_emac_top2_mi32 is

   signal ibuf0_adc_clk  	: std_logic;
   signal ibuf0_adc_rd   	: std_logic;
   signal ibuf0_adc_wr   	: std_logic;
   signal ibuf0_adc_addr 	: std_logic_vector(5 downto 0);
   signal ibuf0_adc_di   	: std_logic_vector(31 downto 0);
   signal ibuf0_adc_do   	: std_logic_vector(31 downto 0);
   signal ibuf0_adc_drdy 	: std_logic;

   signal ibuf1_adc_clk  	: std_logic;
   signal ibuf1_adc_rd   	: std_logic;
   signal ibuf1_adc_wr   	: std_logic;
   signal ibuf1_adc_addr 	: std_logic_vector(5 downto 0);
   signal ibuf1_adc_di   	: std_logic_vector(31 downto 0);
   signal ibuf1_adc_do   	: std_logic_vector(31 downto 0);
   signal ibuf1_adc_drdy 	: std_logic;

   signal ibuf0_lb_en    	: std_logic;
   signal ibuf0_lb_di    	: std_logic_vector(15 downto 0);
   signal ibuf0_lb_drdy  	: std_logic;

   signal ibuf1_lb_en    	: std_logic;
   signal ibuf1_lb_di    	: std_logic_vector(15 downto 0);
   signal ibuf1_lb_drdy  	: std_logic;

   signal lb_en          	: std_logic;
   signal lb_rw          	: std_logic;
   signal lb_addr        	: std_logic_vector(8 downto 0);
   signal lb_di          	: std_logic_vector(15 downto 0);
   signal lb_do          	: std_logic_vector(15 downto 0);
   signal lb_drdy        	: std_logic;
   signal lb_ardy        	: std_logic;

   signal addr_sel       	: std_logic;
   signal reg_addr_sel   	: std_logic;
   signal reg_addr_sel_we	: std_logic;

   signal mi_m0          	: t_mi32;
   signal mi_m1          	: t_mi32;

   signal mi_s0          	: t_mi32;
   signal mi_s1          	: t_mi32;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- IBUF 0 instantination ---------------------------------------------------
   IBUF0_U : entity work.ibuf_emac
      generic map(
         DATA_PATHS  		=> DATA_PATHS,
         DFIFO_SIZE  		=> DFIFO_SIZE,
         HFIFO_SIZE  		=> HFIFO_SIZE,
         HFIFO_DISTMEMTYPE	=> HFIFO_DISTMEMTYPE,
         CTRL_HDR_EN 		=> CTRL_HDR_EN,
         CTRL_FTR_EN 		=> CTRL_FTR_EN,
         MACS        		=> MACS,
	 INBANDFCS   		=> INBANDFCS
      )
      port map (
         RESET       	=> reset,
   
         -- EMAC RX interface
         RXCLK          => IBUF0_RXCLK,
         RXCE           => IBUF0_RXCE,
         RXD            => IBUF0_RX.D,
         RXDV           => IBUF0_RX.DVLD,
         RXGOODFRAME    => IBUF0_RX.GOODFRAME,
         RXBADFRAME     => IBUF0_RX.BADFRAME,
         RXSTATS        => IBUF0_RX.STATS,
         RXSTATSVLD     => IBUF0_RX.STATSVLD,
   
         -- PACODAG interface
         CTRL_CLK       => IBUF0_CTRL_CLK,
         CTRL_RESET     => IBUF0_CTRL_RESET,
         CTRL_DI        => IBUF0_CTRL_DI,
         CTRL_REM       => IBUF0_CTRL_REM,
         CTRL_SRC_RDY_N => IBUF0_CTRL_SRC_RDY_N,
         CTRL_SOP_N     => IBUF0_CTRL_SOP_N,
         CTRL_EOP_N     => IBUF0_CTRL_EOP_N,
         CTRL_DST_RDY_N => IBUF0_CTRL_DST_RDY_N,
         CTRL_RDY       => IBUF0_CTRL_RDY,
   
         -- IBUF status interface
         SOP            => IBUF0_SOP,
         STAT           => IBUF0_STAT,
         STAT_DV        => IBUF0_STAT_DV,
   
         -- Sampling unit interface
         SAU_ACCEPT     => IBUF0_SAU_ACCEPT,
         SAU_DV         => IBUF0_SAU_DV,
         SAU_REQ        => IBUF0_SAU_REQ,
   
         -- FrameLink interface
         RDCLK      		=> IBUF_CLK,
         DATA       		=> IBUF0_DATA,
         DREM       		=> IBUF0_DREM,
         SRC_RDY_N  		=> IBUF0_SRC_RDY_N,
         SOF_N      		=> IBUF0_SOF_N,
         SOP_N      		=> IBUF0_SOP_N,
         EOF_N     	 	=> IBUF0_EOF_N,
         EOP_N      		=> IBUF0_EOP_N,
         DST_RDY_N  		=> IBUF0_DST_RDY_N,
   
         -- Address decoder interface
         ADC_CLK  		=> ibuf0_adc_clk,
         ADC_RD   		=> mi_s0.RD,
         ADC_WR   		=> mi_s0.WR,
         ADC_ADDR 		=> mi_s0.ADDR(7 downto 2),
         ADC_DI   		=> mi_s0.DWR,
         ADC_DO   		=> mi_s0.DRD,
         ADC_BE                 => mi_s0.BE,
         ADC_DRDY 		=> mi_s0.DRDY
      );


   -- IBUF 1 instantination ---------------------------------------------------
   IBUF1_U : entity work.ibuf_emac
      generic map(
         DATA_PATHS  		=> DATA_PATHS,
         DFIFO_SIZE  		=> DFIFO_SIZE,
         HFIFO_SIZE  		=> HFIFO_SIZE,
         HFIFO_DISTMEMTYPE	=> HFIFO_DISTMEMTYPE,
         CTRL_HDR_EN 		=> CTRL_HDR_EN,
         CTRL_FTR_EN 		=> CTRL_FTR_EN,
         MACS        		=> MACS,
         INBANDFCS   		=> INBANDFCS
      )
      port map (
         RESET       	=> reset,
   
         -- EMAC RX interface
         RXCLK          => IBUF1_RXCLK,
         RXCE           => IBUF1_RXCE,
         RXD            => IBUF1_RX.D,
         RXDV           => IBUF1_RX.DVLD,
         RXGOODFRAME    => IBUF1_RX.GOODFRAME,
         RXBADFRAME     => IBUF1_RX.BADFRAME,
         RXSTATS        => IBUF1_RX.STATS,
         RXSTATSVLD     => IBUF1_RX.STATSVLD,
   
         -- PACODAG interface
         CTRL_CLK       => IBUF1_CTRL_CLK,
         CTRL_RESET     => IBUF1_CTRL_RESET,
         CTRL_DI        => IBUF1_CTRL_DI,
         CTRL_REM       => IBUF1_CTRL_REM,
         CTRL_SRC_RDY_N => IBUF1_CTRL_SRC_RDY_N,
         CTRL_SOP_N     => IBUF1_CTRL_SOP_N,
         CTRL_EOP_N     => IBUF1_CTRL_EOP_N,
         CTRL_DST_RDY_N => IBUF1_CTRL_DST_RDY_N,
         CTRL_RDY       => IBUF1_CTRL_RDY,
   
         -- IBUF status interface
         SOP            => IBUF1_SOP,
         STAT           => IBUF1_STAT,
         STAT_DV        => IBUF1_STAT_DV,
   
         -- Sampling unit interface
         SAU_ACCEPT     => IBUF1_SAU_ACCEPT,
         SAU_DV         => IBUF1_SAU_DV,
         SAU_REQ        => IBUF1_SAU_REQ,
   
         -- FrameLink interface
         RDCLK      		=> IBUF_CLK,
         DATA       		=> IBUF1_DATA,
         DREM       		=> IBUF1_DREM,
         SRC_RDY_N  		=> IBUF1_SRC_RDY_N,
         SOF_N      		=> IBUF1_SOF_N,
         SOP_N      		=> IBUF1_SOP_N,
         EOF_N      		=> IBUF1_EOF_N,
         EOP_N      		=> IBUF1_EOP_N,
         DST_RDY_N  		=> IBUF1_DST_RDY_N,
   
         -- Address decoder interface
         ADC_CLK  		=> ibuf1_adc_clk,
         ADC_RD   		=> mi_s1.RD,
         ADC_WR   		=> mi_s1.WR,
         ADC_ADDR 		=> mi_s1.ADDR(7 downto 2),
         ADC_DI   		=> mi_s1.DWR,
         ADC_DO   		=> mi_s1.DRD,
         ADC_BE                 => mi_s1.BE,
         ADC_DRDY 		=> mi_s1.DRDY
      );

   mi32_async_u0: entity work.MI32_ASYNC
      port map(
         RESET          => reset,
         -- Master interface
         CLK_M          => IBUF_CLK,
         MI_M           => mi_m0,
         -- Slave interface
         CLK_S          => ibuf0_adc_clk,
         MI_S           => mi_s0
      );
   
   mi32_async_u1: entity work.MI32_ASYNC
      port map(
         RESET          => reset,
         -- Master interface
         CLK_M          => IBUF_CLK,
         MI_M           => mi_m1,
         -- Slave interface
         CLK_S          => ibuf1_adc_clk,
         MI_S           => mi_s1
      );
   
   addr_sel  <= MI.ADDR(8);

   reg_addr_sel_we <= MI.RD or MI.WR;
   process(RESET, IBUF_CLK)
   begin
      if (RESET = '1') then
         reg_addr_sel <= '0';
      elsif (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (reg_addr_sel_we = '1') then
            reg_addr_sel <= addr_sel;
         end if;
      end if;
   end process;
   
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
   MI.DRD   <= mi_m0.DRD when (reg_addr_sel='0') else
               mi_m1.DRD when (reg_addr_sel='1') else
   	         (others=>'0');
   
   -- MI.ARDY multiplexor -----------------------------------------------------
   MI.ARDY   <= mi_m0.ARDY when (addr_sel='0') else
                mi_m1.ARDY when (addr_sel='1') else
   	          '0';
   
   -- MI.DRDY multiplexor -----------------------------------------------------
   MI.DRDY   <= mi_m0.DRDY when (reg_addr_sel='0') else
                mi_m1.DRDY when (reg_addr_sel='1') else
   	          '0';

end architecture full;
