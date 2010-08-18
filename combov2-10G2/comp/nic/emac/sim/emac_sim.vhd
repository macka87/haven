-- emac_sim.vhd: Simulation component that imititates Virtex 5 embeded EMAC
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
-- TODO: FCS is left as valid data
--       Statistic data are not generatred, yet
--
-- NOTE: Purpose of this component is not to simulate every signal of Xilinx
--       embedded Ethernet EMAC, but only translation from GMII protocol to
--       EMAC signals. You should also use PHY_SIM from SVN r310 to genrate
--       GMII protocol

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;
use work.emac_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity emac_sim is

   port(

      RESET             : in std_logic;

      -- GMII input
      GMII_CLK          : in std_logic;
      RXDI              : in std_logic_vector(7 downto 0);
      RXDV              : in std_logic;
      RXERR             : in std_logic;
   
      -- EMAC output (light version)
      EMAC_CLK          : out std_logic;
      EMAC_CE           : out std_logic;
      EMAC              : out t_emac_rx
      
   );

end entity emac_sim;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of emac_sim is

   constant EMAC_CLK_PER   : time := 4 ns; -- in phy_sim_gmii TX_CLK has period 8 ns

   signal cnt_cut_preamble : std_logic_vector(2 downto 0);
   signal reg_cut_preamble : std_logic;
   signal reg_err          : std_logic;
   signal reg_sent         : std_logic;
   signal reg_stat_vld     : std_logic_vector(3 downto 0);

begin

   -- Output clock generation
   emac_clk_gen: process
   begin
      EMAC_CLK <= '1';
      wait for EMAC_CLK_PER / 2;
      EMAC_CLK <= '0';
      wait for EMAC_CLK_PER / 2;
   end process;

   -- Clock enable for output clock
   EMAC_CE <= not GMII_CLK;


   -- cnt_cut_preamble counter
   cnt_cut_preamblep: process(RESET, GMII_CLK)
   begin
      if (RESET = '1') then
         cnt_cut_preamble <= (others => '0');
      elsif (GMII_CLK'event AND GMII_CLK = '1') then
         if (RXDV = '0') then
            cnt_cut_preamble <= (others => '0');
         else
            cnt_cut_preamble <= cnt_cut_preamble + 1;
         end if;
      end if;
   end process;

   -- register reg_cut_preamble
   reg_cut_preamblep: process(RESET, GMII_CLK)
   begin
      if (RESET = '1') then
         reg_cut_preamble <= '0';
      elsif (GMII_CLK'event and GMII_CLK = '1') then
         if (RXDV = '0') then
            reg_cut_preamble <= '0';
         elsif (cnt_cut_preamble = "111") then
            reg_cut_preamble <= '1';
         end if;
      end if;
   end process;

   -- register reg_err
   reg_errp: process(RESET, GMII_CLK)
   begin
      if (RESET = '1') then
         reg_err <= '0';
      elsif (GMII_CLK'event and GMII_CLK = '1') then
         if (RXDV = '0') then
            reg_err <= '0';
         elsif (RXERR = '1') then
            reg_err <= '0';
         end if;
      end if;
   end process;

   -- register reg_sent
   reg_sentp: process(RESET, GMII_CLK)
   begin
      if (RESET = '1') then
         reg_sent <= '0';
      elsif (GMII_CLK'event AND GMII_CLK = '1') then
         reg_sent <= RXDV;
      end if;
   end process;

   -- register reg_stat_vld
   reg_stat_vldp: process(RESET, GMII_CLK)
   begin
      if (RESET = '1') then
         reg_stat_vld <= (others => '0');
      elsif (GMII_CLK'event AND GMII_CLK = '1') then
         if (reg_stat_vld = "1000") then
            reg_stat_vld <= "0000";
         elsif (reg_sent = '1' and RXDV = '0') then
            reg_stat_vld <= "0001";
         else
            reg_stat_vld <= reg_stat_vld(2 downto 0) & '0';
         end if;
      end if;
   end process;


   -- Output signals
   EMAC.D <= RXDI;
   EMAC.DVLD <= reg_cut_preamble and RXDV;
   EMAC.GOODFRAME <= reg_sent and not RXDV and not reg_err;
   EMAC.BADFRAME <= reg_sent and not RXDV and reg_err;
   EMAC.FRAMEDROP <= '0';
   EMAC.STATS <= (others => '0');
   EMAC.STATSVLD <= '1' when reg_stat_vld /= "0000" else
                    '0';
   EMAC.STATSBYTEVLD <= '0';

end architecture behavioral;
