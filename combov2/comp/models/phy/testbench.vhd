--
-- testbench.vhd: Testbench for phy_sim component
-- Copyright (C) 2003 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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

   constant xgmii_clkper : time := 6.4 ns;
   constant gmii_clkper  : time := 8 ns;

   constant ifc_count    : integer := 6;

-- IFC0 XGMII --------------------------------------------------------------
   -- TX signals --
   signal tx_clk_xgmii_ifc0 : std_logic;
   signal txd_xgmii_ifc0    : std_logic_vector(31 downto 0);
   signal txc_xgmii_ifc0    : std_logic_vector(3 downto 0);
   -- RX signals --
   signal rx_clk_xgmii_ifc0 : std_logic;
   signal rxd_xgmii_ifc0    : std_logic_vector(31 downto 0);
   signal rxc_xgmii_ifc0    : std_logic_vector(3 downto 0);

-- IFC1 XGMII --------------------------------------------------------------
   -- TX signals --
   signal tx_clk_xgmii_ifc1 : std_logic;
   signal txd_xgmii_ifc1    : std_logic_vector(31 downto 0);
   signal txc_xgmii_ifc1    : std_logic_vector(3 downto 0);
   -- RX signals --
   signal rx_clk_xgmii_ifc1 : std_logic;
   signal rxd_xgmii_ifc1    : std_logic_vector(31 downto 0);
   signal rxc_xgmii_ifc1    : std_logic_vector(3 downto 0);

-- IFC2 GMII ---------------------------------------------------------------
   -- TX signals --
   signal tx_clk_gmii_ifc2 : std_logic;
   signal txd_gmii_ifc2    : std_logic_vector(7 downto 0);
   signal tx_dv_gmii_ifc2  : std_logic;
   signal tx_er_gmii_ifc2  : std_logic;
   -- RX signals --
   signal rx_clk_gmii_ifc2 : std_logic;
   signal rxd_gmii_ifc2    : std_logic_vector(7 downto 0);
   signal rx_en_gmii_ifc2  : std_logic;
   signal rx_er_gmii_ifc2  : std_logic;

-- IFC3 GMII ---------------------------------------------------------------
   -- TX signals --
   signal tx_clk_gmii_ifc3 : std_logic;
   signal txd_gmii_ifc3    : std_logic_vector(7 downto 0);
   signal tx_dv_gmii_ifc3  : std_logic;
   signal tx_er_gmii_ifc3  : std_logic;
   -- RX signals --
   signal rx_clk_gmii_ifc3 : std_logic;
   signal rxd_gmii_ifc3    : std_logic_vector(7 downto 0);
   signal rx_en_gmii_ifc3  : std_logic;
   signal rx_er_gmii_ifc3  : std_logic;

-- IFC4 SFP ----------------------------------------------------------------
   -- TX signals --
   signal tx_clk_sfp_ifc4 : std_logic;
   signal tx_d10_sfp_ifc4 : std_logic_vector(9 downto 0);
   -- RX signals --
   signal rx_clk_sfp_ifc4 : std_logic;
   signal rx_d10_sfp_ifc4 : std_logic_vector(9 downto 0);

-- IFC5 SFP ----------------------------------------------------------------
   -- TX signals --
   signal tx_clk_sfp_ifc5 : std_logic;
   signal tx_d10_sfp_ifc5 : std_logic_vector(9 downto 0);
   -- RX signals --
   signal rx_clk_sfp_ifc5 : std_logic;
   signal rx_d10_sfp_ifc5 : std_logic_vector(9 downto 0);

-- common phy simulation signals -------------------------------------------

   signal reset : std_logic;

   type t_oper   is array (0 to (ifc_count - 1)) of t_phy_oper;
   type t_params is array (0 to (ifc_count - 1)) of t_phy_params;
   type t_strobe is array (0 to (ifc_count - 1)) of std_logic;
   type t_busy   is array (0 to (ifc_count - 1)) of std_logic;

   signal phy_oper   : t_oper;
   signal phy_params : t_params;
   signal phy_strobe : t_strobe;
   signal phy_busy   : t_busy;

   signal phy_ctrl   : t_phy_ctrl;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- ----------------------------------------------------
-- UUT mapping

-- ----------------------------------------------------
-- PHY Simulation components

PHY_SIM_XGMII_IFC0 : entity work.phy_sim_xgmii
generic map(
   INTER_FRAME    => 5,
   FILE_NAME_RCV  => "",
   MAX_UNTAGGED_FRAME_SIZE => 1518,
   DEBUG_REPORT   => false
)
port map(
  -- TX interface -------------------------------------------------------
  TX_CLK => tx_clk_xgmii_ifc0,
  TXD    => txd_xgmii_ifc0,
  TXC    => txc_xgmii_ifc0,
  -- RX interface -------------------------------------------------------
  RX_CLK => rx_clk_xgmii_ifc0,
  RXD    => rxd_xgmii_ifc0,
  RXC    => rxc_xgmii_ifc0,


   -- Simulation interface
   OPER        => phy_oper(0),
   PARAMS      => phy_params(0),
   STROBE      => phy_strobe(0),
   BUSY        => phy_busy(0)
);

PHY_SIM_XGMII_IFC1 : entity work.phy_sim_xgmii
generic map(
   INTER_FRAME    => 5,
   FILE_NAME_RCV  => "data/xgmii/received/rcv_packets.txt", -- for store all received packets
   MAX_UNTAGGED_FRAME_SIZE => 1518,
   DEBUG_REPORT   => false
)
port map(
  -- TX interface -------------------------------------------------------
  TX_CLK => tx_clk_xgmii_ifc1,
  TXD    => txd_xgmii_ifc1,
  TXC    => txc_xgmii_ifc1,
  -- RX interface -------------------------------------------------------
  RX_CLK => rx_clk_xgmii_ifc1,
  RXD    => rxd_xgmii_ifc1,
  RXC    => rxc_xgmii_ifc1,


   -- Simulation interface
   OPER        => phy_oper(1),
   PARAMS      => phy_params(1),
   STROBE      => phy_strobe(1),
   BUSY        => phy_busy(1)
);

PHY_SIM_GMII_IFC2 : entity work.phy_sim_gmii
generic map(
   INTER_FRAME    => 5,
   FILE_NAME_RCV  => "",
   MAX_UNTAGGED_FRAME_SIZE => 1518,
   DEBUG_REPORT   => false
)
port map(
  -- TX interface -------------------------------------------------------
  TX_CLK => tx_clk_gmii_ifc2,
  TXD    => txd_gmii_ifc2,
  TX_DV  => tx_dv_gmii_ifc2,
  TX_ER  => tx_er_gmii_ifc2,
  -- RX interface -------------------------------------------------------
  RX_CLK => rx_clk_gmii_ifc2,
  RXD    => rxd_gmii_ifc2,
  RX_EN  => rx_en_gmii_ifc2,
  RX_ER  => rx_er_gmii_ifc2,

   -- Simulation interface
   OPER        => phy_oper(2),
   PARAMS      => phy_params(2),
   STROBE      => phy_strobe(2),
   BUSY        => phy_busy(2)
);

PHY_SIM_GMII_IFC3 : entity work.phy_sim_gmii
generic map(
   INTER_FRAME    => 5,
   FILE_NAME_RCV  => "data/gmii/received/recv_packets.txt",
   MAX_UNTAGGED_FRAME_SIZE => 1518,
   DEBUG_REPORT   => false
)
port map(
  -- TX interface -------------------------------------------------------
  TX_CLK => tx_clk_gmii_ifc3,
  TXD    => txd_gmii_ifc3,
  TX_DV  => tx_dv_gmii_ifc3,
  TX_ER  => tx_er_gmii_ifc3,
  -- RX interface -------------------------------------------------------
  RX_CLK => rx_clk_gmii_ifc3,
  RXD    => rxd_gmii_ifc3,
  RX_EN  => rx_en_gmii_ifc3,
  RX_ER  => rx_er_gmii_ifc3,

   -- Simulation interface
   OPER        => phy_oper(3),
   PARAMS      => phy_params(3),
   STROBE      => phy_strobe(3),
   BUSY        => phy_busy(3)
);

PHY_SIM_SFP_IFC4 : entity work.phy_sim_sfp
generic map(
   INTER_FRAME    => 5,
   FILE_NAME_RCV  => "",
   MAX_UNTAGGED_FRAME_SIZE => 1518,
   DEBUG_REPORT   => false
)
port map(
  -- global -------------------------------------------------------------
  RESET => reset,
  -- TX interface -------------------------------------------------------
  TX_CLK => tx_clk_sfp_ifc4,
  TX_D10 => tx_d10_sfp_ifc4,
  -- RX interface -------------------------------------------------------
  RX_CLK => rx_clk_sfp_ifc4,
  RX_D10 => rx_d10_sfp_ifc4,

   -- Simulation interface
   OPER        => phy_oper(4),
   PARAMS      => phy_params(4),
   STROBE      => phy_strobe(4),
   BUSY        => phy_busy(4)
);

PHY_SIM_SFP_IFC5 : entity work.phy_sim_sfp
generic map(
   INTER_FRAME    => 5,
   FILE_NAME_RCV  => "data/sfp/received/recv_packets.txt",
   MAX_UNTAGGED_FRAME_SIZE => 1518,
   DEBUG_REPORT   => false
)
port map(
  -- global -------------------------------------------------------------
  RESET => reset,
  -- TX interface -------------------------------------------------------
  TX_CLK => tx_clk_sfp_ifc5,
  TX_D10 => tx_d10_sfp_ifc5,
  -- RX interface -------------------------------------------------------
  RX_CLK => rx_clk_sfp_ifc5,
  RX_D10 => rx_d10_sfp_ifc5,

   -- Simulation interface
   OPER        => phy_oper(5),
   PARAMS      => phy_params(5),
   STROBE      => phy_strobe(5),
   BUSY        => phy_busy(5)
);

-- ----------------------------------------------------
-- rx_clk_gmii_ifc2 clock generator
--rx_clk_gmii_ifc2_clkgen : process
--begin
--   rx_clk_gmii_ifc2 <= '1';
--   wait for gmii_clkper/2;
--   rx_clk_gmii_ifc2 <= '0';
--   wait for gmii_clkper/2;
--end process;

-- create loopback on XGMII IFC0 and IFC1
rx_clk_xgmii_ifc0 <= tx_clk_xgmii_ifc1;
rxd_xgmii_ifc0    <= txd_xgmii_ifc1;
rxc_xgmii_ifc0    <= txc_xgmii_ifc1;
rx_clk_xgmii_ifc1 <= tx_clk_xgmii_ifc0;
rxd_xgmii_ifc1    <= txd_xgmii_ifc0;
rxc_xgmii_ifc1    <= txc_xgmii_ifc0;

-- create loopback on GMII IFC2 and IFC3
rx_clk_gmii_ifc2 <= tx_clk_gmii_ifc3;
rxd_gmii_ifc2    <= txd_gmii_ifc3;
rx_en_gmii_ifc2  <= tx_dv_gmii_ifc3;
rx_er_gmii_ifc2  <= tx_er_gmii_ifc3;
rx_clk_gmii_ifc3 <= tx_clk_gmii_ifc2;
rxd_gmii_ifc3    <= txd_gmii_ifc2;
rx_en_gmii_ifc3  <= tx_dv_gmii_ifc2;
rx_er_gmii_ifc3  <= tx_er_gmii_ifc2;

-- create loopback on SFP IFC4 and IFC5
rx_clk_sfp_ifc4  <= tx_clk_sfp_ifc5;
rx_d10_sfp_ifc4  <= tx_d10_sfp_ifc5;
rx_clk_sfp_ifc5 <= tx_clk_sfp_ifc4;
rx_d10_sfp_ifc5 <= tx_d10_sfp_ifc4;


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

-- NOTE:
--      - if you operate with one interface more times consecutively
--      - (send_packet on IFC1, receive_packet on IFC1, send_tcpdump on IFC1)
--      - then you cannot operate other interfaces until last operation
--      - on this interface is done. It's recommended, that you cyclical
--      - operate all interfaces you need (0,1,2,3,0,1,2,3...).
begin
   for i in 0 to (ifc_count - 1) loop
      phy_strobe(i) <= '0';
   end loop;

   -- reset sfp
   reset <= '1';
   wait for 100 ns;
   reset <= '0';

   --phy_op(init); -- empty operation

   phy_op(receive_packet("data/xgmii/received/packet_1.txt"), 1, false);
   --phy_op(send_packet("data/common/packet_1.txt", 1, true), 0, false);

   phy_op(receive_packet("data/sfp/received/packet_1.txt"), 5, false);
   phy_op(send_tcpdump_nowait("data/common/ftp_out.dmp"), 4, false);
   --phy_op(send_raw_packet("data/xgmii/packet_raw_1.txt", 1), 0, false);

   --phy_op(send_raw_packet("data/gmii/packet_raw_1.txt", 1), 2, false);
   phy_op(send_tcpdump_nowait("data/common/ftp_out.dmp"), 0, false);
   wait;
end process;

end architecture behavioral;
