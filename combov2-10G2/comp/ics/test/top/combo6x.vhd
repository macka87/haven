-- top_level.vhd: ICS test - top level architecture for the Combo6X 
-- Copyright (C) 2007 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.ALL;
use ieee.std_logic_arith.ALL;
use ieee.std_logic_unsigned.ALL;
use work.ib_pkg.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of fpga_u5 is

   -- Resets and clocks
   signal rst         : std_logic;
   signal reset       : std_logic;
   signal usrclk      : std_logic;
   signal usrclk2     : std_logic;
   signal lock        : std_logic;
   signal clk         : std_logic;
   signal clkf_bufg   : std_logic;
   
   -- RocketIO
   signal rxn_v      : std_logic_vector(1 downto 0);
   signal rxp_v      : std_logic_vector(1 downto 0);
   signal txn_v      : std_logic_vector(1 downto 0);
   signal txp_v      : std_logic_vector(1 downto 0);
   
   -- Internal bus structure
   signal ibus       : t_internal_bus64; 

   -- Clock Buffer 
--   component BUFG is port (I : in  std_logic; O : out std_logic); end component;

begin

   LINT  <= '1';         -- Do not generate interrupt
   rst   <= not LRESET;  -- LRESET is active low
   clk   <= usrclk2;     -- CLK (62,5 MHz)

   -- -------------------------------------------------------------------------
   -- RESETs
   -- -------------------------------------------------------------------------
   RESET_SYNC : process(RST, clk)
   begin      
      if RST = '1' then
         reset <= '1';
      elsif clk'event and clk = '1' then
         reset  <= rst or (not lock); -- internal reset
   end if;
   end process;

--    -- -------------------------------------------------------------------------
--    -- CLKF buffer
--    -- -------------------------------------------------------------------------
--    CLKF_BUFG_U : BUFG
--       port map (
--          I => CLKF,
--          O => clkf_bufg
--       ); 

   -- -------------------------------------------------------------------------
   -- Generate clocks - local bus clock CLK and RocketIO clocks
   -- These clocks are both derived from CLKF (125MHz system clock)
   -- -------------------------------------------------------------------------
   CLK_GENERATOR_RIO: entity work.clkgen_rio 
   port map (
      CLKIN   => CLKF,    -- Input clock (125 MHz)
      RESET   => rst,
      USRCLK  => usrclk,  -- usrclk (125 MHz)
      USRCLK2 => usrclk2, -- usrclk2 (62,5 MHz shifted)
      LOCKED  => lock
   );
   
   -- -------------------------------------------------------------------------
   --  Aurora interface to the PCI FPGA
   -- -------------------------------------------------------------------------
   IB_AURORA: entity work.aurfc 
   generic map (
      LANES         => 2,
      DATA_PATHS    => 8,
      DISCARD_BAD_PACKETS => false,
      TX_FIFO_ITEMS => 512,
      RX_FIFO_ITEMS => 512,
      RX_IS_HEADER  => false,
      RX_IS_FOOTER  => false,
      XON_LIMIT     => "011",
      XOFF_LIMIT    => "110"
   )
   port map (
      -- Common Input
      RESET        => reset,
      REFCLK       => CLKF,
      USRCLK       => usrclk,
      USRCLK2      => usrclk2,
      CMDCLK       => clk,
      -- LocalLink TX
      TX_D         => ibus.up.data,     
      TX_REM       => "111",
      TX_SRC_RDY_N => ibus.up.src_rdy_n,
      TX_SOF_N     => ibus.up.sop_n,
      TX_SOP_N     => ibus.up.sop_n,
      TX_EOF_N     => ibus.up.eop_n,    
      TX_EOP_N     => ibus.up.eop_n,
      TX_DST_RDY_N => ibus.up.dst_rdy_n,
      -- LocalLink RX 
      RX_D         => ibus.down.data,     
      RX_REM       => open,
      RX_SRC_RDY_N => ibus.down.src_rdy_n,
      RX_SOF_N     => ibus.down.sop_n,
      RX_SOP_N     => open,
      RX_EOF_N     => ibus.down.eop_n,
      RX_EOP_N     => open,
      RX_DST_RDY_N => ibus.down.dst_rdy_n,
      -- Upper Layer
      HARD_ERROR   => open,
      SOFT_ERROR   => open,
      FRAME_ERROR  => open,
      -- Status Interface
      TX_STATUS    => open,
      RX_STATUS    => open,
      -- MGT Interface
      RXN          => rxn_v,
      RXP          => rxp_v,
      TXN          => txn_v,
      TXP          => txp_v
   );
   
   -- -------------------------------------------------------------------------
   --  User application - ICS test
   -- -------------------------------------------------------------------------
   USER_APP: entity work.ICS_TEST_APP
   port map(
      -- Common Interface
      CLK           => clk,
      RESET         => reset,
      -- Internal Bus Interface
      INTERNAL_BUS  => ibus
   );
   
   -- -------------------------------------------------------------------------
   --  FPGA port mapping
   -- -------------------------------------------------------------------------
   rxn_v <= RXN3 & RXN2;
   rxp_v <= RXP3 & RXP2;
   TXN2  <= txn_v(0);
   TXN3  <= txn_v(1);
   TXP2  <= txp_v(0);
   TXP3  <= txp_v(1);
       
end Behavioral;
