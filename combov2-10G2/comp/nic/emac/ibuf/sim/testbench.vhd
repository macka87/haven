-- testbench.vhd: Testbench of top level entity
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.math_pack.all;
use work.phy_oper.all;
use work.ibuf_general_pkg.all;
use work.fl_sim_oper.all;
use work.emac_pkg.all;



-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant DATA_PATHS 			: integer := 2;
   constant FRAME_PARTS 		: integer := 2;
   constant GND_BYTE   			: std_logic_vector(7 downto 0) := X"00";
   constant PACKETS_DIR  		: string:="../../../../../data/packets/common/";
   constant PACKETS_GMII_DIR  : string:="../../../gmii/ibuf/sim/data/";

   
   -- GMII interface
   signal gmiiclk 			: std_logic;
   signal gmiid   			: std_logic_vector(7 downto 0);
   signal gmiidv  			: std_logic;
   signal gmiier  			: std_logic;

   -- EMAC interface
   signal emac_clk 			: std_logic;
   signal emac_ce  			: std_logic;
   signal emac     			: t_emac_rx;

   -- Output interface
   signal rdclk   			: std_logic;
   signal data    			: std_logic_vector((DATA_PATHS*8-1) downto 0);
   signal drem    			: std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal src_rdy_n  			: std_logic;
   signal sof_n   			: std_logic;
   signal sop_n   			: std_logic;
   signal eof_n   			: std_logic;
   signal eop_n   			: std_logic;
   signal dst_rdy_n  		: std_logic;

   signal adc_addr 			: std_logic_vector(5 downto 0);
   signal adc_di   			: std_logic_vector(31 downto 0);
   signal adc_wr   			: std_logic;
   signal adc_do   			: std_logic_vector(31 downto 0);
   signal adc_drdy 			: std_logic;

   -- Sampling Unit interface
   signal sau_accept 		: std_logic;
   signal sau_dv     		: std_logic;

   -- Pacodag interface
   signal ctrl_clk   		: std_logic;
   signal ctrl_di 			: std_logic_vector((DATA_PATHS*8-1) downto 0);
   signal ctrl_src_rdy_n 	: std_logic;
   signal ctrl_rem			: std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal ctrl_sop_n			: std_logic;
   signal ctrl_eop_n			: std_logic;
   signal ctrl_dst_rdy_n 	: std_logic;
   signal ctrl_hdr_en 		: std_logic;
   signal ctrl_ftr_en 		: std_logic;
   signal ctrl_rdy    		: std_logic;
   signal sop     			: std_logic;
   signal stat    			: t_ibuf_general_stat;
   signal stat_dv 			: std_logic;
   
   signal phy_oper   		: t_phy_oper;
   signal phy_params 		: t_phy_params;
   signal phy_strobe 		: std_logic;
   signal phy_busy   		: std_logic;
   signal done       		: std_logic;
   signal ready      		: std_logic;

   signal phy_ctrl   		: t_phy_ctrl;

   signal reset				: std_logic;

   constant rdclkper 		: time := 10 ns;

   -- FL Sim RX signals
   signal filename_rx      : t_fl_ctrl;
   signal fl_sim_strobe_rx : std_logic;
   signal fl_sim_busy_rx   : std_logic;




-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   rdclk_clkgen : process
   begin
      rdclk <= '1';
      wait for rdclkper/2;
      rdclk <= '0';
      wait for rdclkper/2;
   end process;
   
   PHY_SIM_GMII_IFC : entity work.phy_sim_gmii
	   generic map(
	      INTER_FRAME    			=> 12,
	      FILE_NAME_RCV  			=> "",
	      --1518, we use greater value for testing purposes
	      MAX_UNTAGGED_FRAME_SIZE => 2000,
	      DEBUG_REPORT   			=> true
	   )
	   port map(
	      -- TX interface
	      TX_CLK 	=> gmiiclk,
	      TXD    	=> gmiid,
	      TX_DV  	=> gmiidv,
	      TX_ER  	=> gmiier,
	      -- RX interface
	      RX_CLK 	=> '0',
	      RXD    	=> (others=>'0'),
	      RX_EN  	=> '0',
	      RX_ER  	=> '0',

	      -- Simulation interface
	      OPER     => phy_oper,
	      PARAMS   => phy_params,
	      STROBE   => phy_strobe,
	      BUSY     => phy_busy
	   );

   -- -------------------------------------------------------------------------
   EMAC_SIMi : entity work.emac_sim
      port map(
         RESET       => reset,
   
         -- GMII input
         GMII_CLK		=> gmiiclk,
         RXDI        => gmiid,
         RXDV        => gmiidv,
         RXERR       => gmiier,
      
         -- EMAC output (light version)
         EMAC_CLK    => emac_clk,
         EMAC_CE     => emac_ce,
         EMAC        => emac
      );

   -- -------------------------------------------------------------------------
   uut : entity work.ibuf_emac
      generic map(
         DATA_PATHS  => DATA_PATHS,
         DFIFO_SIZE  => 1024,
         HFIFO_SIZE  => 1024,
         CTRL_HDR_EN => open,
         CTRL_FTR_EN => open,
         MACS        => 16
      )
   
      port map(
         RESET       	=> reset,
   
         -- EMAC RX interface
         RXCLK        	=> emac_clk,
         RXCE           => emac_ce,
         RXD            => emac.D,
         RXDV           => emac.DVLD,
         RXGOODFRAME		=> emac.GOODFRAME,
         RXBADFRAME     => emac.BADFRAME,
         RXSTATS        => emac.STATS,
         RXSTATSVLD     => emac.STATSVLD,
   
         -- PACODAG interface
         CTRL_CLK       => ctrl_clk,
         CTRL_DI        => ctrl_di,
         CTRL_REM       => ctrl_rem,
         CTRL_SRC_RDY_N => ctrl_src_rdy_n,
         CTRL_SOP_N     => ctrl_sop_n,
         CTRL_EOP_N     => ctrl_eop_n,
         CTRL_DST_RDY_N => ctrl_dst_rdy_n,
         CTRL_RDY       => ctrl_rdy,
   
         -- IBUF status interface
         SOP            => sop,
         STAT           => stat,
         STAT_DV        => stat_dv,
   
         -- Sampling unit interface
         SAU_ACCEPT     => sau_accept,
         SAU_DV         => sau_dv,
   
         -- FrameLink interface
         RDCLK      		=> rdclk,
         DATA       		=> data,
         DREM       		=> drem,
         SRC_RDY_N  		=> src_rdy_n,
         SOF_N      		=> sof_n,
         SOP_N      		=> sop_n,
         EOF_N      		=> eof_n,
         EOP_N      		=> eop_n,
         DST_RDY_N  		=> dst_rdy_n,
   
         -- Address decoder interface
         ADC_CLK  		=> open,
         ADC_RD   		=> '0',
         ADC_WR   		=> adc_wr,
         ADC_ADDR 		=> adc_addr,
         ADC_DI   		=> adc_di,
         ADC_DO   		=> adc_do,
         ADC_DRDY 		=> adc_drdy
      );

   -- -------------------------------------------------------------------------
   fl_sim_rx: entity work.FL_SIM
      generic map (
         DATA_WIDTH     => DATA_PATHS*8,
         RX_LOG_FILE    => "fl_sim_rx.txt",
         FRAME_PARTS    => FRAME_PARTS
      )
      port map (
         -- Common interface
         FL_RESET       => RESET,
         FL_CLK         => rdclk,
   
         -- FrameLink Interface
         RX_DATA        => data,
         RX_REM         => drem,
         RX_SOF_N       => sof_n,
         RX_EOF_N       => eof_n,
         RX_SOP_N       => sop_n,
         RX_EOP_N       => eop_n,
         RX_SRC_RDY_N   => src_rdy_n,
         RX_DST_RDY_N   => dst_rdy_n,
   
         TX_DATA        => open,
         TX_REM         => open,
         TX_SOF_N       => open,
         TX_EOF_N       => open,
         TX_SOP_N       => open,
         TX_EOP_N       => open,
         TX_SRC_RDY_N   => open,
         TX_DST_RDY_N   => '0',
   
         -- FL SIM interface
         CTRL           => filename_rx,
         STROBE         => fl_sim_strobe_rx,
         BUSY           => fl_sim_busy_rx
      );


   -- main testbench process
   tb : process
   -- -------------------------------------------------------------------------
   -- Procedure phy_op performs phy operation specified
   -- in data structure t_phy_ctrl
   --
   -- Parameters:
   --       ctrl        - structure for phy controling
   --       block_wait  - blocking waiting for completion of operation
   --
   procedure phy_op(ctrl : in t_phy_ctrl; block_wait : in boolean := false) is
   begin
      --wait until (phy_busy(id) = '0');
      while (phy_busy /= '0') loop
         wait for 0.1 ns;
      end loop;
      phy_oper   <= ctrl.oper;
      phy_params <= ctrl.params;
      phy_strobe <= '1';
   
      wait until (phy_busy = '1');
      phy_strobe <= '0';
   
      -- block waiting, if required
      if (block_wait = true) then
         while (phy_busy /= '0') loop
            wait for 0.1 ns;
         end loop;
      end if;
   end phy_op;
   
   -- -------------------------------------------------------------------------
   --                            Testbench Body
   -- -------------------------------------------------------------------------
   begin
      phy_strobe <= '0';
      --ready      <= '0';
   
      -- reset sfp
      reset <= '1';
      wait for 100 ns;
      reset <= '0';
      wait until emac_clk'event and emac_clk='1';
      -- Disable error checking
      adc_addr <= "001001";
      adc_di   <= X"00000000";
      adc_wr   <= '1';
      wait until emac_clk'event and emac_clk='1';
      adc_wr   <= '0';
      wait until emac_clk'event and emac_clk='1';
      -- Enable ibuf
      adc_addr <= "001000";
      adc_di   <= X"00000001";
      adc_wr   <= '1';
      wait until emac_clk'event and emac_clk='1';
      adc_wr   <= '0';

      wait for 96 ns; -- interframe

      phy_op(send_packet(PACKETS_GMII_DIR & "pkt62.txt", 10, true),true);
      phy_op(send_packet(PACKETS_GMII_DIR & "pkt8.txt", 1, true),true);
      phy_op(send_packet(PACKETS_GMII_DIR & "packet_long.txt", 1, true),true);
      phy_op(send_packet(PACKETS_GMII_DIR & "pkt62.txt", 1, true),true);
      phy_op(send_packet(PACKETS_GMII_DIR & "pkt8.txt", 1, true),true);
      ready <= '1';
      phy_op(send_raw_packet(PACKETS_GMII_DIR & "packet_raw_err.txt", 3),true);
      wait until gmiiclk'event and gmiiclk='1' and done='1';
      ready <= '0'; 
      phy_op(send_tcpdump(PACKETS_DIR & "real_1500.dump"),true);
      
      wait;
   end process;
   
   -- This PACODAG can FREEZE IBUF, it generates control data for discarded
	-- packets
   tb_pacodag_p: process
   begin
      while true loop
         ctrl_di 			<= x"0000";
         ctrl_src_rdy_n <= '1';
         ctrl_rem 		<= "1";
         ctrl_sop_n 		<= '1';
         ctrl_eop_n 		<= '1';
         ctrl_hdr_en 	<= '0';
         ctrl_ftr_en 	<= '1';
         ctrl_rdy 		<= '1';
         wait until sop='1';
         wait until ctrl_clk'event and ctrl_clk='1';
--          ctrl_di <= x"1234";
--          ctrl_src_rdy_n <= '0';
--          ctrl_sop_n <= '0';
--          wait until ctrl_clk'event and ctrl_clk='1';
--          ctrl_di <= x"5600";
--          ctrl_rem <= "0";
--          ctrl_sop_n <= '1';
--          ctrl_eop_n <= '0';
--          wait until ctrl_clk'event and ctrl_clk='1';
         ctrl_di 			<= x"7890";
         ctrl_src_rdy_n <= '0';
         ctrl_sop_n 		<= '0';
         ctrl_eop_n 		<= '1';
         wait until ctrl_clk'event and ctrl_clk='1';
         ctrl_di 			<= x"abcd";
         ctrl_sop_n 		<= '1';
         wait until ctrl_clk'event and ctrl_clk='1';
         ctrl_di 			<= x"ef01";
         ctrl_rem 		<= "1";
         ctrl_eop_n 		<= '0';
         wait until ctrl_clk'event and ctrl_clk='1';
      end loop;
   wait;
   end process;
   
   tb_sau_p: process
   begin
      sau_accept 	<= '0';
      sau_dv 		<= '0';
      wait until ctrl_clk'event and ctrl_clk='1' and sop='1';
      wait until ctrl_clk'event and ctrl_clk='1';
      wait until ctrl_clk'event and ctrl_clk='1';
      wait until ctrl_clk'event and ctrl_clk='1';
      sau_dv 		<= '1';
      sau_accept 	<= '1';
      wait until ctrl_clk'event and ctrl_clk='1';
      
      sau_accept 	<= '0';
      sau_dv 		<= '0';
      wait until ctrl_clk'event and ctrl_clk='1' and sop='1';
      wait until ctrl_clk'event and ctrl_clk='1';
      wait until ctrl_clk'event and ctrl_clk='1';
      wait until ctrl_clk'event and ctrl_clk='1';
      sau_dv 		<= '1';
      sau_accept 	<= '1';
      wait until ctrl_clk'event and ctrl_clk='1';
      
   end process;
   
end architecture;
