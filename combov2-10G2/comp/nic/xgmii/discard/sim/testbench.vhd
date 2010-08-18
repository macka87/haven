-- testbench.vhd: Testbench for XGMII_IBUF
-- Copyright (C) 2010 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.xgmii_pkg.all;
--use work.fifo_pkg.all;
use work.math_pack.all;

--use work.lb_pkg.all;
--use work.ib_sim_oper.all;

-- use ieee.std_logic_textio.all;
-- use ieee.numeric_std.all;
-- use std.textio.all;

use work.phy_oper.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant DO_SAMPLING : std_logic := '1';
   constant IFC_COUNT   : integer := 1;

   -- Global Constant Declaration
   constant clkper       : time := 20 ns;
   constant miclkper     : time := 10 ns;
   constant clkper_base  : time := 20 ns;
   constant clkper_xgmii : time := 6.4 ns;

   constant PACKETS_DIR  : string := "../../../../../data/packets/common/";
   constant RESET_DELAY        : time := 1 us;

   constant END_DELAY          : time := 10 us;

   constant INBANDFCS      : boolean := false;
   constant NUMBER_OF_STAT_BITS  : integer := 6;

   --+ delay of the DISCARD signal (SAMPLING unit)
   constant FIFO_DEPTH     : integer   := 7;
   constant DISCARD_DELAY_CLK  : integer   := 4;

   -- Signal declaration
   signal reset         : std_logic;
   signal non_reset     : std_logic;
   signal clk           : std_logic;

   -- xgmii signals
   signal xgmii_discard_clk : std_logic;
   signal xgmii_discard_rxd : std_logic_vector(63 downto 0);
   signal xgmii_discard_rxc : std_logic_vector(7 downto 0);
   signal xgmii_discard_txd : std_logic_vector(63 downto 0);
   signal xgmii_discard_txc : std_logic_vector(7 downto 0);
   
   signal xgmii_rxd : std_logic_vector(63 downto 0);
   signal xgmii_rxc : std_logic_vector(7 downto 0);
   signal xgmii_rxded : std_logic_vector(63 downto 0);
   signal xgmii_rxced : std_logic_vector(7 downto 0);

   signal sop_aligned       : std_logic;
   signal rx_sop            : std_logic;
   signal rx_eop            : std_logic;
   signal tx_sop            : std_logic;
   signal tx_eop            : std_logic;

   signal discard           : std_logic := 'X';
   signal discard_vld       : std_logic := '0';
   signal discard_delay     : std_logic_vector(1 downto 0);
   signal discard_delayed   : std_logic_vector(1 downto 0);

--   signal sau_valid      : std_logic;
--   signal sau_sample     : std_logic;
--   signal sau_req        : std_logic;
--   signal mi             : t_mi32;
--   signal mi_clk         : std_logic;

--   -- MI32 Sim signals
--   signal mi32_sim_ctrl        : t_ib_ctrl;
--   signal mi32_sim_strobe      : std_logic;
--   signal mi32_sim_busy        : std_logic;

   -- PHY simulation component signals
   -- Transmit interface
   
   signal phy_sim_tx_clk      : std_logic;
   signal phy_sim_txd         : std_logic_vector(31 downto 0);
   signal phy_sim_txc         : std_logic_vector( 3 downto 0);

   type t_oper   is array (0 to (IFC_COUNT - 1)) of t_phy_oper;
   type t_params is array (0 to (IFC_COUNT - 1)) of t_phy_params;
   type t_strobe is array (0 to (IFC_COUNT - 1)) of std_logic;
   type t_busy   is array (0 to (IFC_COUNT - 1)) of std_logic;

   signal phy_oper   : t_oper;
   signal phy_params : t_params;
   signal phy_strobe : t_strobe;
   signal phy_busy   : t_busy;

   signal phy_ctrl   : t_phy_ctrl;

   signal rxdcm_lock       : std_logic := '0';

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   clk   <= xgmii_discard_clk;

   DISCARD_U   : entity work.xgmii_discard
   generic map (
      FIFO_DEPTH  => FIFO_DEPTH
   )
   port map (
      CLK   => xgmii_discard_clk,
      RESET => reset,

      XGMII_RXC => xgmii_discard_rxc,
      XGMII_RXD => xgmii_discard_rxd,
      XGMII_TXC => xgmii_discard_txc,
      XGMII_TXD => xgmii_discard_txd,

      RX_SOP   => rx_sop,
      RX_EOP   => rx_eop,
      TX_SOP   => open,
      TX_EOP   => open,

      DISCARD  => discard_delayed(0),
      DISCARD_VLD => discard_delayed(1)
   );

   -- delay of discard signal (simulating SAU unit)
   discard_delay_sh: entity work.sh_reg_bus
   generic map (
      NUM_BITS    => DISCARD_DELAY_CLK,
      DATA_WIDTH  => 2
   )
   port map (
      CLK         => CLK,
      DIN         => discard_delay,
      CE          => '1',
      DOUT        => discard_delayed
   );

   discard_delay(0)  <= discard;
   discard_delay(1)  <= discard_vld;

   -- XGMII_RX instantion
   XGMII_RECEIVERi: entity work.xgmii_rx
   port map(
      XGMII_RX_CLK         => phy_sim_tx_clk,
      XGMII_RXD            => phy_sim_txd,
      XGMII_RXC            => phy_sim_txc,
      RESET                => reset,
      RX_CLK_INT           => xgmii_discard_clk,
      RXD_INT              => xgmii_rxd,
      RXC_INT              => xgmii_rxc,
      RX_DCM_LOCK          => rxdcm_lock,
      RX_DCM_RESET       	=> '0'
   );

   XGMII_PKT_DEC: entity work.xgmii_packet_dec
   port map (
      CLK            => xgmii_discard_clk,

      XGMII_RXD      => xgmii_rxd,
      XGMII_RXC      => xgmii_rxc,
      
      SOP            => rx_sop,
      EOP            => rx_eop
   );

   xgmii_discard_rxd <= xgmii_rxd;
   xgmii_discard_rxc <= xgmii_rxc;


   -- -------------------------------------------------------------------------
   --                       PHY SIM XGMII component
   -- -------------------------------------------------------------------------
      phy_sim_xgmii_u: entity work.phy_sim_xgmii
         port map (
            -- TX interface
            TX_CLK       => phy_sim_tx_clk,
            TXD          => phy_sim_txd,
            TXC          => phy_sim_txc,

            -- RX interface
            RX_CLK       => clk,
            RXD          => X"07070707",
            RXC          => "1111",

            -- Simulation interface
            OPER        => phy_oper(0),
            PARAMS      => phy_params(0),
            STROBE      => phy_strobe(0),
            BUSY        => phy_busy(0)
         );
  
   -- ----------------------------------------------------
   -- Reset generation
   proc_reset : process
   begin
      reset <= '1';
      wait for RESET_DELAY;
      reset <= '0';
      wait;
   end process;
   
   non_reset <= not reset;
  

   discard_p : process
      -- send discard/pass request (like SAU unit)
      procedure pkt_sample(sample : in std_logic) is
      begin
         wait on clk, rx_sop until rx_sop = '1';

         discard <= sample;
         discard_vld <= '1';

         wait until clk'event and clk = '1';
         discard_vld <= '0';
      end procedure;
   begin
      pkt_sample('1');
      pkt_sample('1');
      pkt_sample('0');
      pkt_sample('0');
   end process;

    
   -- ----------------------------------------------------------------------------
   --                         Main testbench process
   -- ----------------------------------------------------------------------------
   
   tb : process
      -- ----------------------------------------------------------------
      --                    Procedures declaration
      -- ----------------------------------------------------------------
  
      -- ----------------------------------------------------------------
      -- Procedure phy_op performs phy operation specified
      -- in data structure t_phy_ctrl
      --
      -- Parameters:
      --       ctrl        - structure for phy controling
      --       id          - interface id
      --       block_wait  - blocking waiting for completion of operation
      --
      procedure phy_op(ctrl : in t_phy_ctrl; id : in integer;
                       block_wait : in boolean := false) is
      begin
         --wait until (phy_busy(id) = '0');
         while (phy_busy(id) /= '0') loop
            wait for 0.1 ns;
         end loop;
         phy_oper(id)   <= ctrl.oper;
         phy_params(id) <= ctrl.params;
         phy_strobe(id) <= '1';
      
         wait until (phy_busy(id) = '1');
         phy_strobe(id)  <= '0';
      
         -- block waiting, if required
         if (block_wait = true) then
            while (phy_busy(id) /= '0') loop
               wait for 0.1 ns;
            end loop;
         end if;
      end phy_op;
    
   -- ----------------------------------------------------------------
   --                        Testbench Body
   -- ----------------------------------------------------------------
   begin

      phy_strobe(0) <= '0';
      -- interface signals init
--       rxda <= X"07070707";
--       rxca <= "1111";

      wait for 2*RESET_DELAY;

      -- Packet reception
--       phy_op(send_tcpdump(PACKETS_DIR & "lo_ack.dump"), 0, false);
--       phy_op(send_tcpdump("../../../../../units/hfe/test/packets/mpls_3pac.dump"), 0, false);
--       wait for 5*clkper;
      phy_op(send_tcpdump_nowait(PACKETS_DIR & "real_1500.dump"), 0, false);

   
   
      wait for END_DELAY; 
   
      wait;
   end process;

--   -- Sampling control.
--   -- We don't have sampling unit yet so this should be enough
--   sau_valid <= '1' when sau_req = '1' else '0';
--   sau_sample<= DO_SAMPLING when sau_req = '1' else '0';
  
end architecture behavioral;
