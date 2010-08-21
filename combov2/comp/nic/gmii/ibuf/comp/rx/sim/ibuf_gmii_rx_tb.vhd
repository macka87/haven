--
-- ibuf_gmii_rx_tb.vhd: Testbench of top level entity
-- Copyright (C) 2005 CESNET
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.math_pack.all;
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

   signal rxclk   : std_logic;
   signal rxd     : std_logic_vector(7 downto 0);
   signal rxdv    : std_logic;
   signal rxer    : std_logic;

   signal do      : std_logic_vector(7 downto 0);
   signal do_dv   : std_logic;
   signal stat    : std_logic_vector(1 downto 0);
   signal stat_dv : std_logic;

   signal phy_oper   : t_phy_oper;
   signal phy_params : t_phy_params;
   signal phy_strobe : std_logic;
   signal phy_busy   : std_logic;

   signal phy_ctrl   : t_phy_ctrl;

   signal reset: std_logic;


-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

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

uut : entity work.ibuf_gmii_rx
port map(
   RESET     => reset,

   -- RX gmii interface
   RXCLK    => rxclk,
   RXDV     => rxdv,
   RXER     => rxer,
   RXD      => rxd,

   -- buffer interface
   DO      => do,
   DO_DV   => do_dv,
   STAT    => stat,
   STAT_DV => stat_dv
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

   -- reset sfp
   reset <= '1';
   wait for 100 ns;
   reset <= '0';
   wait until rxclk'event and rxclk='1';
   wait for 96 ns; -- interframe


   --phy_op(send_packet("data/common/packet_1.txt", 1, true), false);
   --phy_op(send_tcpdump_nowait("data/common/ftp_out.dmp"), false);
   --phy_op(send_raw_packet("data/xgmii/packet_raw_1.txt", 1), false);
   phy_op(send_packet("../../../sim/data/packet_1.txt", 1, true), false); -- valid packet
   --phy_op(send_packet("../../../sim/data/rx_packet_01.txt", 1, false), false); -- valid packet
   --phy_op(send_raw_packet("../../../sim/data/packet_raw_short.txt", 1), false); -- short packet
   --phy_op(send_packet("../../../sim/data/packet_long.txt", 1, false), false); -- long packet
   phy_op(send_raw_packet("../../../sim/data/packet_raw_err.txt", 1), false); -- packet with error
   --phy_op(send_tcpdump_nowait("../../../sim/data/ftp_out.dmp"), true);

   wait;
end process;

end architecture behavioral;
