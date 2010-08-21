-- ibuf_emac_top4_mi32_ent.vhd: Input Buffer - 4 ibufs + MI_32 interface
-- Copyright (C) 2008 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
--            Martin Kosek <kosek@liberouter.org>
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
use work.emac_pkg.all; 
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ibuf_emac_top4_mi32 is
   generic(
      DATA_PATHS  : integer;     		-- Output data width in bytes
      DFIFO_SIZE  : integer;     		-- Packet data fifo size
      HFIFO_SIZE  : integer;     		-- Control fifo size
      HFIFO_DISTMEMTYPE : integer;              -- Distributed Ram Type (capacity) used for HFIFO
      CTRL_HDR_EN : boolean := true; 	-- Enables Packet Headers
      CTRL_FTR_EN : boolean := false; 	-- Enables Packet Footers
      MACS        : integer := 16;  		-- Number of MAC addresses (up to 16)
      INBANDFCS   : boolean := true    -- frame contains FCS (true) or not (false)
   );
   port(
      -- ---------------- Common signal -----------------
      RESET         			: in  std_logic;
      IBUF_CLK      			: in  std_logic;

      -- ------------------------------------------------
      -- -------------- IBUF interfaces -----------------
      
      -- -----------
      -- INTERFACE 0
      -- EMAC RX interface
      IBUF0_RXCLK          : in std_logic;
      IBUF0_RXCE           : in std_logic;
      IBUF0_RX             : in t_emac_rx;
      
      -- PACODAG interface
      IBUF0_CTRL_CLK       : out std_logic;
      IBUF0_CTRL_RESET     : out std_logic;
      IBUF0_CTRL_DI        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF0_CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF0_CTRL_SRC_RDY_N : in std_logic;
      IBUF0_CTRL_SOP_N     : in std_logic;
      IBUF0_CTRL_EOP_N     : in std_logic;
      IBUF0_CTRL_DST_RDY_N : out std_logic;
      IBUF0_CTRL_RDY       : in std_logic;

      -- IBUF status interface
      IBUF0_SOP            : out std_logic;
      IBUF0_STAT           : out t_ibuf_general_stat;
      IBUF0_STAT_DV        : out std_logic;

      -- Sampling unit interface
      IBUF0_SAU_ACCEPT     : in std_logic;
      IBUF0_SAU_DV         : in std_logic;
      IBUF0_SAU_REQ        : out std_logic;

      -- FrameLink interface
      IBUF0_DATA       		: out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF0_DREM       		: out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF0_SRC_RDY_N  		: out std_logic;
      IBUF0_SOF_N      		: out std_logic;
      IBUF0_SOP_N      		: out std_logic;
      IBUF0_EOF_N      		: out std_logic;
      IBUF0_EOP_N      		: out std_logic;
      IBUF0_DST_RDY_N  		: in std_logic;
      
      -- -----------
      -- INTERFACE 1
      -- EMAC RX interface
      IBUF1_RXCLK          : in std_logic;
      IBUF1_RXCE           : in std_logic;
      IBUF1_RX             : in t_emac_rx;

      -- PACODAG interface
      IBUF1_CTRL_CLK       : out std_logic;
      IBUF1_CTRL_RESET     : out std_logic;
      IBUF1_CTRL_DI        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF1_CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF1_CTRL_SRC_RDY_N : in std_logic;
      IBUF1_CTRL_SOP_N     : in std_logic;
      IBUF1_CTRL_EOP_N     : in std_logic;
      IBUF1_CTRL_DST_RDY_N : out std_logic;
      IBUF1_CTRL_RDY       : in std_logic;

      -- IBUF status interface
      IBUF1_SOP            : out std_logic;
      IBUF1_STAT           : out t_ibuf_general_stat;
      IBUF1_STAT_DV        : out std_logic;

      -- Sampling unit interface
      IBUF1_SAU_ACCEPT     : in std_logic;
      IBUF1_SAU_DV         : in std_logic;
      IBUF1_SAU_REQ        : out std_logic;

      -- FrameLink interface
      IBUF1_DATA       		: out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF1_DREM       		: out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF1_SRC_RDY_N  		: out std_logic;
      IBUF1_SOF_N      		: out std_logic;
      IBUF1_SOP_N      		: out std_logic;
      IBUF1_EOF_N      		: out std_logic;
      IBUF1_EOP_N      		: out std_logic;
      IBUF1_DST_RDY_N  		: in std_logic;

      -- -----------
      -- INTERFACE 2
      -- EMAC RX interface
      IBUF2_RXCLK          : in std_logic;
      IBUF2_RXCE           : in std_logic;
      IBUF2_RX             : in t_emac_rx;

      -- PACODAG interface
      IBUF2_CTRL_CLK       : out std_logic;
      IBUF2_CTRL_RESET     : out std_logic;
      IBUF2_CTRL_DI        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF2_CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF2_CTRL_SRC_RDY_N : in std_logic;
      IBUF2_CTRL_SOP_N     : in std_logic;
      IBUF2_CTRL_EOP_N     : in std_logic;
      IBUF2_CTRL_DST_RDY_N : out std_logic;
      IBUF2_CTRL_RDY       : in std_logic;

      -- IBUF status interface
      IBUF2_SOP            : out std_logic;
      IBUF2_STAT           : out t_ibuf_general_stat;
      IBUF2_STAT_DV        : out std_logic;

      -- Sampling unit interface
      IBUF2_SAU_ACCEPT     : in std_logic;
      IBUF2_SAU_DV         : in std_logic;
      IBUF2_SAU_REQ        : out std_logic;

      -- FrameLink interface
      IBUF2_DATA       		: out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF2_DREM       		: out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF2_SRC_RDY_N  		: out std_logic;
      IBUF2_SOF_N      		: out std_logic;
      IBUF2_SOP_N      		: out std_logic;
      IBUF2_EOF_N      		: out std_logic;
      IBUF2_EOP_N      		: out std_logic;
      IBUF2_DST_RDY_N  		: in std_logic;

      -- -----------
      -- INTERFACE 3
      -- EMAC RX interface
      IBUF3_RXCLK          : in std_logic;
      IBUF3_RXCE           : in std_logic;
      IBUF3_RX             : in t_emac_rx;

      -- PACODAG interface
      IBUF3_CTRL_CLK       : out std_logic;
      IBUF3_CTRL_RESET     : out std_logic;
      IBUF3_CTRL_DI        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF3_CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF3_CTRL_SRC_RDY_N : in std_logic;
      IBUF3_CTRL_SOP_N     : in std_logic;
      IBUF3_CTRL_EOP_N     : in std_logic;
      IBUF3_CTRL_DST_RDY_N : out std_logic;
      IBUF3_CTRL_RDY       : in std_logic;

      -- IBUF status interface
      IBUF3_SOP            : out std_logic;
      IBUF3_STAT           : out t_ibuf_general_stat;
      IBUF3_STAT_DV        : out std_logic;

      -- Sampling unit interface
      IBUF3_SAU_ACCEPT     : in std_logic;
      IBUF3_SAU_DV         : in std_logic;
      IBUF3_SAU_REQ        : out std_logic;

      -- FrameLink interface
      IBUF3_DATA       		: out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF3_DREM       		: out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF3_SRC_RDY_N  		: out std_logic;
      IBUF3_SOF_N      		: out std_logic;
      IBUF3_SOP_N      		: out std_logic;
      IBUF3_EOF_N      		: out std_logic;
      IBUF3_EOP_N      		: out std_logic;
      IBUF3_DST_RDY_N  		: in std_logic;


      -- ------------------------------------------------
      -- ------------ MI_32 bus signals -----------------
      MI               		: inout t_mi32
   );
end entity ibuf_emac_top4_mi32;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_emac_top4_mi32 is

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

   signal ibuf2_adc_clk  	: std_logic;
   signal ibuf2_adc_rd   	: std_logic;
   signal ibuf2_adc_wr   	: std_logic;
   signal ibuf2_adc_addr 	: std_logic_vector(5 downto 0);
   signal ibuf2_adc_di   	: std_logic_vector(31 downto 0);
   signal ibuf2_adc_do   	: std_logic_vector(31 downto 0);
   signal ibuf2_adc_drdy 	: std_logic;

   signal ibuf3_adc_clk  	: std_logic;
   signal ibuf3_adc_rd   	: std_logic;
   signal ibuf3_adc_wr   	: std_logic;
   signal ibuf3_adc_addr 	: std_logic_vector(5 downto 0);
   signal ibuf3_adc_di   	: std_logic_vector(31 downto 0);
   signal ibuf3_adc_do   	: std_logic_vector(31 downto 0);
   signal ibuf3_adc_drdy 	: std_logic;

   signal ibuf0_lb_en    	: std_logic;
   signal ibuf0_lb_di    	: std_logic_vector(15 downto 0);
   signal ibuf0_lb_drdy  	: std_logic;

   signal ibuf1_lb_en    	: std_logic;
   signal ibuf1_lb_di    	: std_logic_vector(15 downto 0);
   signal ibuf1_lb_drdy  	: std_logic;

   signal ibuf2_lb_en    	: std_logic;
   signal ibuf2_lb_di    	: std_logic_vector(15 downto 0);
   signal ibuf2_lb_drdy  	: std_logic;

   signal ibuf3_lb_en    	: std_logic;
   signal ibuf3_lb_di    	: std_logic_vector(15 downto 0);
   signal ibuf3_lb_drdy  	: std_logic;

   signal lb_en          	: std_logic;
   signal lb_rw          	: std_logic;
   signal lb_addr       	: std_logic_vector(8 downto 0);
   signal lb_di          	: std_logic_vector(15 downto 0);
   signal lb_do          	: std_logic_vector(15 downto 0);
   signal lb_drdy        	: std_logic;
   signal lb_ardy        	: std_logic;

   signal addr_sel       	: std_logic_vector(1 downto 0);
   signal reg_addr_sel   	: std_logic_vector(1 downto 0);
   signal reg_addr_sel_we	: std_logic;

   signal mi_m0          	: t_mi32;
   signal mi_m1          	: t_mi32;
   signal mi_m2          	: t_mi32;
   signal mi_m3          	: t_mi32;

   signal mi_s0          	: t_mi32;
   signal mi_s1          	: t_mi32;
   signal mi_s2          	: t_mi32;
   signal mi_s3          	: t_mi32;

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
         HFIFO_DISTMEMTYPE	=>HFIFO_DISTMEMTYPE,
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
         EOF_N      		=> IBUF0_EOF_N,
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

   -- IBUF 2 instantination ---------------------------------------------------
   IBUF2_U : entity work.ibuf_emac
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
         RXCLK          => IBUF2_RXCLK,
         RXCE           => IBUF2_RXCE,
         RXD            => IBUF2_RX.D,
         RXDV           => IBUF2_RX.DVLD,
         RXGOODFRAME    => IBUF2_RX.GOODFRAME,
         RXBADFRAME     => IBUF2_RX.BADFRAME,
         RXSTATS        => IBUF2_RX.STATS,
         RXSTATSVLD     => IBUF2_RX.STATSVLD,
   
         -- PACODAG interface
         CTRL_CLK       => IBUF2_CTRL_CLK,
         CTRL_RESET     => IBUF2_CTRL_RESET,
         CTRL_DI        => IBUF2_CTRL_DI,
         CTRL_REM       => IBUF2_CTRL_REM,
         CTRL_SRC_RDY_N => IBUF2_CTRL_SRC_RDY_N,
         CTRL_SOP_N     => IBUF2_CTRL_SOP_N,
         CTRL_EOP_N     => IBUF2_CTRL_EOP_N,
         CTRL_DST_RDY_N => IBUF2_CTRL_DST_RDY_N,
         CTRL_RDY       => IBUF2_CTRL_RDY,
   
         -- IBUF status interface
         SOP            => IBUF2_SOP,
         STAT           => IBUF2_STAT,
         STAT_DV        => IBUF2_STAT_DV,
   
         -- Sampling unit interface
         SAU_ACCEPT     => IBUF2_SAU_ACCEPT,
         SAU_DV         => IBUF2_SAU_DV,
         SAU_REQ        => IBUF2_SAU_REQ,
   
         -- FrameLink interface
         RDCLK      		=> IBUF_CLK,
         DATA       		=> IBUF2_DATA,
         DREM       		=> IBUF2_DREM,
         SRC_RDY_N  		=> IBUF2_SRC_RDY_N,
         SOF_N      		=> IBUF2_SOF_N,
         SOP_N      		=> IBUF2_SOP_N,
         EOF_N      		=> IBUF2_EOF_N,
         EOP_N      		=> IBUF2_EOP_N,
         DST_RDY_N  		=> IBUF2_DST_RDY_N,
   
         -- Address decoder interface
         ADC_CLK  		=> ibuf2_adc_clk,
         ADC_RD   		=> mi_s2.RD,
         ADC_WR   		=> mi_s2.WR,
         ADC_ADDR 		=> mi_s2.ADDR(7 downto 2),
         ADC_DI   		=> mi_s2.DWR,
         ADC_DO   		=> mi_s2.DRD,
         ADC_BE                 => mi_s2.BE,
         ADC_DRDY 		=> mi_s2.DRDY
      );

   -- IBUF 3 instantination ---------------------------------------------------
   IBUF3_U : entity work.ibuf_emac
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
         RXCLK          => IBUF3_RXCLK,
         RXCE           => IBUF3_RXCE,
         RXD            => IBUF3_RX.D,
         RXDV           => IBUF3_RX.DVLD,
         RXGOODFRAME    => IBUF3_RX.GOODFRAME,
         RXBADFRAME     => IBUF3_RX.BADFRAME,
         RXSTATS        => IBUF3_RX.STATS,
         RXSTATSVLD     => IBUF3_RX.STATSVLD,
   
         -- PACODAG interface
         CTRL_CLK       => IBUF3_CTRL_CLK,
         CTRL_RESET     => IBUF3_CTRL_RESET,
         CTRL_DI        => IBUF3_CTRL_DI,
         CTRL_REM       => IBUF3_CTRL_REM,
         CTRL_SRC_RDY_N => IBUF3_CTRL_SRC_RDY_N,
         CTRL_SOP_N     => IBUF3_CTRL_SOP_N,
         CTRL_EOP_N     => IBUF3_CTRL_EOP_N,
         CTRL_DST_RDY_N => IBUF3_CTRL_DST_RDY_N,
         CTRL_RDY       => IBUF3_CTRL_RDY,
   
         -- IBUF status interface
         SOP            => IBUF3_SOP,
         STAT           => IBUF3_STAT,
         STAT_DV        => IBUF3_STAT_DV,
   
         -- Sampling unit interface
         SAU_ACCEPT     => IBUF3_SAU_ACCEPT,
         SAU_DV         => IBUF3_SAU_DV,
         SAU_REQ        => IBUF3_SAU_REQ,
   
         -- FrameLink interface
         RDCLK      		=> IBUF_CLK,
         DATA       		=> IBUF3_DATA,
         DREM       		=> IBUF3_DREM,
         SRC_RDY_N  		=> IBUF3_SRC_RDY_N,
         SOF_N      		=> IBUF3_SOF_N,
         SOP_N      		=> IBUF3_SOP_N,
         EOF_N      		=> IBUF3_EOF_N,
         EOP_N      		=> IBUF3_EOP_N,
         DST_RDY_N  		=> IBUF3_DST_RDY_N,
   
         -- Address decoder interface
         ADC_CLK  		=> ibuf3_adc_clk,
         ADC_RD   		=> mi_s3.RD,
         ADC_WR   		=> mi_s3.WR,
         ADC_ADDR 		=> mi_s3.ADDR(7 downto 2),
         ADC_DI   		=> mi_s3.DWR,
         ADC_DO   		=> mi_s3.DRD,
         ADC_BE                 => mi_s3.BE,
         ADC_DRDY 		=> mi_s3.DRDY
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

   mi32_async_u2: entity work.MI32_ASYNC
      port map(
         RESET          => reset,
         -- Master interface
         CLK_M          => IBUF_CLK,
         MI_M           => mi_m2,
         -- Slave interface
         CLK_S          => ibuf2_adc_clk,
         MI_S           => mi_s2
      );

   mi32_async_u3: entity work.MI32_ASYNC
      port map(
         RESET          => reset,
         -- Master interface
         CLK_M          => IBUF_CLK,
         MI_M           => mi_m3,
         -- Slave interface
         CLK_S          => ibuf3_adc_clk,
         MI_S           => mi_s3
      );
   
   addr_sel  <= MI.ADDR(9 downto 8);

   reg_addr_sel_we <= MI.RD or MI.WR;
   process(RESET, IBUF_CLK)
   begin
      if (RESET = '1') then
         reg_addr_sel <= (others => '0');
      elsif (IBUF_CLK'event AND IBUF_CLK = '1') then
         if (reg_addr_sel_we = '1') then
            reg_addr_sel <= addr_sel;
         end if;
      end if;
   end process;
   
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
   
   -- MI.RD demultiplexor -----------------------------------------------------
   mi_m0.RD <= MI.RD when (addr_sel="00") else '0';
   mi_m1.RD <= MI.RD when (addr_sel="01") else '0';
   mi_m2.RD <= MI.RD when (addr_sel="10") else '0';
   mi_m3.RD <= MI.RD when (addr_sel="11") else '0';
   
   -- MI.WR demultiplexor -----------------------------------------------------
   mi_m0.WR <= MI.WR when (addr_sel="00") else '0';
   mi_m1.WR <= MI.WR when (addr_sel="01") else '0';
   mi_m2.WR <= MI.WR when (addr_sel="10") else '0';
   mi_m3.WR <= MI.WR when (addr_sel="11") else '0';
   
   -- MI.BE connection
   mi_m0.BE <= MI.BE;
   mi_m1.BE <= MI.BE;
   mi_m2.BE <= MI.BE;
   mi_m3.BE <= MI.BE;
   
   -- MI.DRD multiplexor ------------------------------------------------------
   MI.DRD   <= mi_m0.DRD when (reg_addr_sel="00") else
               mi_m1.DRD when (reg_addr_sel="01") else
               mi_m2.DRD when (reg_addr_sel="10") else
               mi_m3.DRD when (reg_addr_sel="11") else
   	         (others=>'X');
   
   -- MI.ARDY multiplexor -----------------------------------------------------
   MI.ARDY   <= mi_m0.ARDY when (addr_sel="00") else
                mi_m1.ARDY when (addr_sel="01") else
                mi_m2.ARDY when (addr_sel="10") else
                mi_m3.ARDY when (addr_sel="11") else
   	          '0';
   
   -- MI.DRDY multiplexor -----------------------------------------------------
   MI.DRDY   <= mi_m0.DRDY when (reg_addr_sel="00") else
                mi_m1.DRDY when (reg_addr_sel="01") else
                mi_m2.DRDY when (reg_addr_sel="10") else
                mi_m3.DRDY when (reg_addr_sel="11") else
   	          '0';

end architecture full;
