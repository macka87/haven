-- top_level.vhd : CAM + lb_bridge top level architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                          Entity declaration
-- ----------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                       Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of fpga is

   -- ------------------ Constants declaration --------------------------------
   constant CAM_BASE_ADDR     : integer := 16#0000000#;
   constant ADDR_WIDTH        : integer := 10;
   constant DESIGN_FREQUENCY  : integer := 50;
   constant CAM_ROW_WIDTH     : integer := 40;
   constant CAM_ROW_COUNT     : integer := 32;
   
   -- ------------------ Signals declaration ----------------------------------
   -- global signals
   signal reset               : std_logic;
   signal non_lreset          : std_logic;
   signal clk50               : std_logic;
   signal clk100              : std_logic;
   signal clk_lock            : std_logic;
   signal clk_base            : std_logic;

   -- localbus signals
   signal lbframe             : std_logic;
   signal lbholda             : std_logic;
   signal lbad                : std_logic_vector(15 downto 0);
   signal lbas                : std_logic;
   signal lbrw                : std_logic;
   signal lbrdy               : std_logic;
   signal lblast              : std_logic;

   -- CAM hw side signals
   signal cam_addr            : std_logic_vector(log2(CAM_ROW_COUNT)-1 downto 0);
   signal cam_data_in         : std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
   signal cam_mask_in         : std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
   signal cam_write_en        : std_logic;
   signal cam_match_en        : std_logic;
   signal cam_match_rst       : std_logic;

begin

   non_lreset <= (not LRESET);
   reset      <= (not LRESET) or (not clk_lock);

   -- CAM signals
   cam_addr       <= (others => '0');
   cam_data_in    <= (others => '0');
   cam_mask_in    <= (others => '0');
   cam_write_en   <= '0';
   cam_match_en   <= '0';
   cam_match_rst  <= '0';

   -- ------------------- CLK selection ---------------------------------------
   clksel100 : 
      if DESIGN_FREQUENCY = 100 generate 
         clk_base <= clk100;
      end generate;

   clksel50 : 
      if DESIGN_FREQUENCY = 50 generate 
         clk_base <= clk50;
      end generate;

   -- ------------------- Clock gen port map ----------------------------------
   CLK_GEN_I : entity work.CLK_GEN
   port map( 
      -- Input 
      CLK50_IN     => LCLKF,      -- Input clock frequency (50MHz)
      RESET        => non_lreset, -- Global reset signal
      -- Output 
      CLK50_OUT    => clk50,      -- 50MHz  output clock
      CLK100       => clk100,     -- 100MHz output clock
      LOCK         => clk_lock    -- Lock signal
   );

   -- ------------------- Local bus port map ----------------------------------
   LB_I : entity work.LOCAL_BUS 
   port map(
      LAD      => LAD,
      ADS      => ADS,
      BLAST    => BLAST,
      LHOLD    => LHOLD,
      LHOLDA   => LHOLDA,
      LWR      => LWR,
      READY    => READY,
      RESET    => reset,
      LCLKF    => clk50,
      USERO    => USERO,

      LBCLK    => clk100,
      LBFRAME  => lbframe,
      LBHOLDA  => lbholda,
      LBAD     => lbad,
      LBAS     => lbas,
      LBRW     => lbrw,
      LBRDY    => lbrdy,
      LBLAST   => lblast,
      SWQ_REQ  => '0' 
   );

   -- ------------------- CAM top level map -----------------------------------
   CAM_TOP_LEVEL_I : entity work.CAM_TOP_LEVEL
   generic map (
      BASE              => CAM_BASE_ADDR,
      ADDR_WIDTH        => ADDR_WIDTH,
      ADC_FREQUENCY     => DESIGN_FREQUENCY,
      CAM_ROW_WIDTH     => CAM_ROW_WIDTH,
      CAM_ROW_COUNT     => CAM_ROW_COUNT
   )
   port map (
      CLK               => clk_base,
      RESET             => reset,
      -- CAM interface
      ADDR              => cam_addr,
      DATA_IN           => cam_data_in,
      MASK_IN           => cam_mask_in,
      WRITE_EN          => cam_write_en,
      MATCH_EN          => cam_match_en,
      MATCH_RST         => cam_match_rst,
      MATCH_BUS         => open,
      MATCH_BUS_VLD     => open,
      -- control signals between SW and HW side
      RQ                => open,
      ACK               => '1',
      BUSY              => open,
      -- local bus interface
      LBCLK             => clk100,
      LBFRAME           => lbframe,
      LBHOLDA           => lbholda,
      LBAD              => lbad,
      LBAS              => lbas,
      LBRW              => lbrw,
      LBRDY             => lbrdy,
      LBLAST            => lblast
   );

end architecture behavioral;
