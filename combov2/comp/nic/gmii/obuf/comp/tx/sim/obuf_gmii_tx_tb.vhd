--
-- obuf_gmii_tx_tb.vhd: Testbench for obuf gmii tx part
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use work.phy_oper.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_gmii_tx_tb is
end entity obuf_gmii_tx_tb;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of obuf_gmii_tx_tb is

   constant gmii_clkper  : time := 8 ns;

   signal clk    : std_logic;
   signal refclk : std_logic;
   signal reset  : std_logic;
   signal data   : std_logic_vector(7 downto 0);
   signal en     : std_logic;
   signal er     : std_logic;

   signal di     : std_logic_vector(7 downto 0);
   signal di_dv  : std_logic;
   signal di_er  : std_logic;
   signal busy   : std_logic;

   signal phy_oper   : t_phy_oper;
   signal phy_params : t_phy_params;
   signal phy_strobe : std_logic;
   signal phy_busy   : std_logic;

   signal phy_ctrl   : t_phy_ctrl;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- ----------------------------------------------------
-- UUT mapping

-- ----------------------------------------------------
-- PHY Simulation component

PHY_SIM_GMII : entity work.phy_sim_gmii
generic map(
   INTER_FRAME    => 12,
   FILE_NAME_RCV  => "recv_packets.txt",
   MAX_UNTAGGED_FRAME_SIZE => 1518,
   DEBUG_REPORT   => false
)
port map(
  -- TX interface -------------------------------------------------------
  TX_CLK => open,
  TXD    => open,
  TX_DV  => open,
  TX_ER  => open,
  -- RX interface -------------------------------------------------------
  RX_CLK => clk,
  RXD    => data,
  RX_EN  => en,
  RX_ER  => er,

   -- Simulation interface
   OPER        => phy_oper,
   PARAMS      => phy_params,
   STROBE      => phy_strobe,
   BUSY        => phy_busy
);

UUT : entity work.obuf_gmii_tx
port map(
   RESET => reset,
   REFCLK => refclk,

   -- obuf_gmii_buf interface
   DI    => di,
   DI_DV => di_dv,
   DI_ER => di_er,
   BUSY  => busy,

   -- TX gmii interface
   TXCLK => clk,
   TXD   => data,
   TXEN  => en,
   TXER  => er
);


-- ----------------------------------------------------
-- rx_clk_gmii_ifc2 clock generator
refclk_clkgen : process
begin
   refclk <= '1';
   wait for gmii_clkper/2;
   refclk <= '0';
   wait for gmii_clkper/2;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------

rx_p : process

-- ----------------------------------------------------------------
--                    Procedures declaration
-- ----------------------------------------------------------------

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
   --wait until (phy_busy = '0');
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

begin
   phy_strobe <= '0';

   --phy_op(init); -- empty operation

   --phy_op(receive_packet("packet_1.txt"), false);
   wait;
end process;

tb : process
begin

   -- reset
   reset <= '1';
   di_dv <= '0';
   di_er <= '0';
   di    <= X"00";

   wait for 100 ns;
   reset <= '0';

   wait until (busy='0' and refclk'event and refclk='1');

   di_dv <= '1';

   for i in 0 to 59 loop
      di <= conv_std_logic_vector(i, di'length);
      wait until (refclk'event and refclk='1');
   end loop;

   di_dv <= '0';

   wait until (busy='0' and refclk'event and refclk='1');

   di_dv <= '1';

   for i in 0 to 59 loop
      di <= conv_std_logic_vector(i, di'length);
      wait until (refclk'event and refclk='1');
   end loop;

   di_dv <= '0';
   wait;
end process;

end architecture behavioral;
