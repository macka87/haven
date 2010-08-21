--
-- ibuf_gmii_tb.vhd: Testbench of top level entity
-- Copyright (C) 2005 CESNET
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
--            Martin Mikusek <martin.mikusek@liberouter.org>
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.math_pack.all;
use work.phy_oper.all;
use work.ibuf_general_pkg.all;

use work.fl_sim_oper.all; -- FrameLink Simulation Package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant DATA_PATHS : integer := 4;
   
   constant LINK_STATUS : std_logic := '1';
   constant DUPLEX_MODE : std_logic := '1';
   constant SPEED       : std_logic_vector := "10";
   constant SPEED_INT   : integer := 1000;
   constant SGMII       : std_logic := '0';

   constant INBANDFCS   : boolean := true;
   constant DELAY_OUTPUT: boolean := false;
   
   -- GMII interface
   signal rxclk   : std_logic;
   signal rxd     : std_logic_vector(7 downto 0);
   signal rxdv    : std_logic;
   signal rxer    : std_logic;

   -- Output interface
   signal rdclk   : std_logic;
   signal data    : std_logic_vector((DATA_PATHS*8-1) downto 0);
   signal drem    : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal src_rdy_n  : std_logic;
   signal sof_n   : std_logic;
   signal sop_n   : std_logic;
   signal eof_n   : std_logic;
   signal eop_n   : std_logic;
   signal dst_rdy_n  : std_logic;

   signal del_src_rdy_n : std_logic;
   signal del_dst_rdy_n : std_logic;
   signal delay         : std_logic;

   signal adc_addr : std_logic_vector(5 downto 0);
   signal adc_di   : std_logic_vector(31 downto 0);
   signal adc_wr   : std_logic;
   signal adc_do   : std_logic_vector(31 downto 0);
   signal adc_drdy : std_logic;

   -- Sampling Unit interface
   signal sau_accept : std_logic;
   signal sau_dv     : std_logic;

   -- Pacodag interface
   signal ctrl_clk   : std_logic;
   signal ctrl_di : std_logic_vector((DATA_PATHS*8-1) downto 0);
   signal ctrl_src_rdy_n : std_logic;
   signal ctrl_rem: std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal ctrl_sop_n: std_logic;
   signal ctrl_eop_n: std_logic;
   signal ctrl_dst_rdy_n : std_logic;
   signal ctrl_rdy : std_logic;
   signal sop     : std_logic;
   signal stat    : t_ibuf_general_stat;
   signal stat_dv : std_logic;
   
   signal phy_oper   : t_phy_oper;
   signal phy_params : t_phy_params;
   signal phy_strobe : std_logic;
   signal phy_busy   : std_logic;
   signal done       : std_logic;
   signal ready      : std_logic;

   signal phy_ctrl   : t_phy_ctrl;

   signal reset: std_logic;

   constant rdclkper : time := 10 ns;

   -- FL Sim signals
   signal filename_rx         : t_fl_ctrl;
   signal fl_sim_strobe_rx    : std_logic;
   signal fl_sim_busy_rx      : std_logic;



-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

rdclk_clkgen : process
begin
   rdclk <= '1';
   wait for rdclkper/2;
   rdclk <= '0';
   wait for rdclkper/2;
end process;

PHY_SIM_GMII_IFC : entity work.phy_sim_gmii
generic map(
   INTER_FRAME    => 12,
   FILE_NAME_RCV  => "",
   MAX_UNTAGGED_FRAME_SIZE => 2000, --1518, we use greater value for testing purposes
   DEBUG_REPORT   => false
)
port map(
  -- TX interface -------------------------------------------------------
  TX_CLK => rxclk,
  TXD    => rxd,
  TX_DV  => rxdv,
  TX_ER  => rxer,
  -- RX interface -------------------------------------------------------
  RX_CLK => '0',
  RXD    => (others=>'0'),
  RX_EN  => '0',
  RX_ER  => '0',

  -- Simulation interface
  OPER        => phy_oper,
  PARAMS      => phy_params,
  STROBE      => phy_strobe,
  BUSY        => phy_busy
);

-- -------------------------------------------------------------------------
--                   UUT - GMII IBUF
-- -------------------------------------------------------------------------
uut : entity work.ibuf_gmii
generic map (
   DATA_PATHS => DATA_PATHS,
   DFIFO_SIZE => 511,
   HFIFO_SIZE => 15,
   INBANDFCS  => INBANDFCS
)
port map(
   RESET    => reset,

   -- RX gmii interface
   RXCLK    => rxclk,
   RXDV     => rxdv,
   RXER     => rxer,
   RXD      => rxd,

   -- PHY status interface
   LINK_STATUS       => LINK_STATUS,
   DUPLEX_MODE       => DUPLEX_MODE,
   SPEED             => SPEED,
   SGMII             => SGMII,
  
   -- PACODAG interface
   CTRL_CLK    => ctrl_clk,
   CTRL_DI        => ctrl_di,
   CTRL_REM       => ctrl_rem,
   CTRL_SRC_RDY_N => ctrl_src_rdy_n,
   CTRL_SOP_N     => ctrl_sop_n,
   CTRL_EOP_N     => ctrl_eop_n,
   CTRL_DST_RDY_N => ctrl_dst_rdy_n,
   CTRL_RDY    => ctrl_rdy,

   SOP      => sop,
   STAT     => stat,
   STAT_DV  => stat_dv,

   SAU_ACCEPT => sau_accept,
   SAU_DV     => sau_dv,

   RDCLK      => rdclk,
   DATA       => data,
   DREM       => drem,
   SRC_RDY_N  => src_rdy_n,
   SOF_N      => sof_n,
   SOP_N      => sop_n,
   EOF_N      => eof_n,
   EOP_N      => eop_n,
   DST_RDY_N  => dst_rdy_n,

   ADC_RD   => '0',
   ADC_WR   => adc_wr,
   ADC_ADDR => adc_addr, --(others=>'0'),
   ADC_DI   => adc_di,
   ADC_DO   => adc_do,--open,
   ADC_DRDY => adc_drdy    
);
     
-- -------------------------------------------------------------------------
--                   FL Simulation Component - RX
-- -------------------------------------------------------------------------
fl_sim_rx: entity work.FL_SIM
   generic map (
      DATA_WIDTH     => DATA_PATHS*8,
      RX_LOG_FILE    => "fl_sim_rx.txt",
      FRAME_PARTS    => 2
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
      RX_SRC_RDY_N   => del_src_rdy_n,
      RX_DST_RDY_N   => del_dst_rdy_n,

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

pacodag_i: entity work.pacodag
   generic map (
      IFC_ID         => "0000",
      DATA_PATHS     => DATA_PATHS,
      HEADER_EN      => true,
      FOOTER_EN      => false
   )
   port map (
      -- Common interface
      RESET    => RESET,

      -- IBUF interface
      CTRL_CLK    => ctrl_clk,
      CTRL_DATA      => ctrl_di,
      CTRL_REM       => ctrl_rem,
      CTRL_SRC_RDY_N => ctrl_src_rdy_n,
      CTRL_SOP_N     => ctrl_sop_n,
      CTRL_EOP_N     => ctrl_eop_n,
      CTRL_DST_RDY_N => ctrl_dst_rdy_n,
      CTRL_RDY       => ctrl_rdy,

      -- IBUF status interface
      SOP         => sop,
      STAT        => stat,
      STAT_DV     => stat_dv
   );


-- main testbench process
tb : process
-- ----------------------------------------------------------------
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

-- ----------------------------------------------------------------
--                        Testbench Body
-- ----------------------------------------------------------------

begin
   phy_strobe <= '0';
   --ready      <= '0';

   -- reset sfp
   reset <= '1';
   wait for 100 ns;
   reset <= '0';
   wait until rxclk'event and rxclk='1';
   -- Set speed
   if (SPEED_INT /= 1000) then
      for i in 0 to 11 loop
         wait until rxclk'event and rxclk='1';
      end loop;
      adc_addr <= "001011";
      if (SPEED_INT = 100) then
         adc_di   <= X"00000005";
      end if;
      if (SPEED_INT = 10) then
         adc_di   <= X"00000004";
      end if;
      adc_wr   <= '1';
      wait until rxclk'event and rxclk='1';
      adc_wr   <= '0';
   end if;
   for i in 0 to 11 loop
      wait until rxclk'event and rxclk='1';
   end loop;
   -- Set mode
   adc_addr <= "111000";
   adc_di   <= X"00000011";
   adc_wr   <= '1';
   wait until rxclk'event and rxclk='1';
   adc_wr   <= '0';
   for i in 0 to 11 loop
      wait until rxclk'event and rxclk='1';
   end loop;
   -- Enable ibuf
   adc_addr <= "001000";
   adc_di   <= X"00000001";
   adc_wr   <= '1';
   wait until rxclk'event and rxclk='1';
   adc_wr   <= '0';

   wait for 96 ns; -- interframe
   
   phy_op(send_packet("data/pkt62.txt", 1, true, SPEED_INT), true);
   phy_op(send_packet("data/pkt8.txt", 1, true, SPEED_INT), true);
   --ready <= '1';
   --phy_op(send_raw_packet("data/packet_raw_err.txt", 3), true);
   --wait until rxclk'event and rxclk='1' and done='1';
   --ready <= '0';
   --phy_op(send_packet("data/pkt8.txt", 1, true), true);
   --ready <= '1';
   --wait until rxclk'event and rxclk='1' and done='1';
   --ready <= '0';
   --phy_op(send_packet("data/pkt8.txt", 1, true), true);
   phy_op(send_packet("data/packet_long.txt", 1, true, SPEED_INT), true);
   --phy_op(send_packet("data/packet_long.txt", 1, true), true);
   phy_op(send_packet("data/pkt62.txt", 10, true, SPEED_INT), true);
   phy_op(send_packet("data/pkt8.txt", 20, true, SPEED_INT), true);
   --ready <= '1';

   --phy_op(send_packet("data/pkt48.txt", 20, true), true);
   --phy_op(send_raw_packet("data/packet_raw_err.txt", 3), true);
   
   wait;
end process;

-- Add delay to fill HFIFO at the beginning
delay_gen: if (DELAY_OUTPUT = true) generate
   del_p: process
   begin
      delay <= '1';
      wait for 30 us;
      delay <= '0';
      wait;
   end process;
end generate delay_gen;

-- No delay
nodelay_gen: if (DELAY_OUTPUT = false) generate
   delay <= '0';
end generate nodelay_gen;

del_src_rdy_n <= src_rdy_n or delay;
dst_rdy_n     <= del_dst_rdy_n or delay;

tb_sau_p: process
begin
   sau_accept <= '0';
   sau_dv <= '0';
   wait until rxclk'event and rxclk='1' and sop='1';
   wait until rxclk'event and rxclk='1';
   wait until rxclk'event and rxclk='1';
   wait until rxclk'event and rxclk='1';
   sau_dv <= '1';
   sau_accept <= '1';
   wait until rxclk'event and rxclk='1';
   
   sau_accept <= '0';
   sau_dv <= '0';
   wait until rxclk'event and rxclk='1' and sop='1';
   wait until rxclk'event and rxclk='1';
   wait until rxclk'event and rxclk='1';
   wait until rxclk'event and rxclk='1';
   sau_dv <= '1';
   sau_accept <= '1';
   wait until rxclk'event and rxclk='1';
   
end process;

end architecture behavioral;
