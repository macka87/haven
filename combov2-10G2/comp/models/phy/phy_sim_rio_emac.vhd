--
-- phy_sim_rio_emac.vhd: PHY - simulation component for RocketIO - Ethernet over EMAC
-- Copyright (C) 2008 CESNET
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

library IEEE;
use IEEE.std_logic_1164.all;
use work.emac_pkg.all;
use work.phy_oper.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity phy_sim_rio_emac is
   generic(
      INTER_FRAME   : integer := 12; -- 96 bit times, see IEEE 802.3
      FILE_NAME_RCV : string  := "";
      MAX_UNTAGGED_FRAME_SIZE : integer := 1518;
      DEBUG_REPORT  : boolean := false
   );
   port(
      -- Global signals
      EMAC_CLK : in  std_logic;
      RESET    : in  std_logic;
      -- RocketIO interface
      RXP      :  in std_logic;
      RXN      :  in std_logic;
      TXP      : out std_logic;
      TXN      : out std_logic;
      -- Simulation interface ----------------------------------------------
      OPER     : in  t_phy_oper;
      PARAMS   : in  t_phy_params;
      STROBE   : in  std_logic;
      BUSY     : out std_logic := '0'
   );
end entity phy_sim_rio_emac;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of phy_sim_rio_emac is

   -- ------------------ Xilinx components ------------------------------------

   -- Clock Buffer
   component BUFG is
      port (
         I : in  std_logic;
         O : out std_logic
      );
   end component;

   -- ------------------ Signals declaration ----------------------------------
   alias  clk_ds           : std_logic is EMAC_CLK;
   signal clk125_o         : std_logic;
   signal clk125_i         : std_logic;

   -- EMAC
   signal emac0_rx         : t_emac_rx;
   signal emac0_tx         : t_emac_tx;
   signal emac0_control    : t_emac_control;

   signal emac1_rx         : t_emac_rx;
   signal emac1_tx         : t_emac_tx;
   signal emac1_control    : t_emac_control;

   signal emac0_resetdone  : std_logic;
   signal emac1_resetdone  : std_logic;

   signal emac0hostclk        : std_logic;
   signal emac0hostopcode     : std_logic_vector(1 downto 0);
   signal emac0hostaddr       : std_logic_vector(9 downto 0);
   signal emac0hostwrdata     : std_logic_vector(31 downto 0);
   signal emac0hostrddata     : std_logic_vector(31 downto 0);
   signal emac0hostmiimsel    : std_logic;
   signal emac0hostemac1sel   : std_logic;
   signal emac0hostreq        : std_logic;
   signal emac0hostmiimrdy    : std_logic;

begin

   -- 125MHz from transceiver is routed through a BUFG and 
   -- input to the MAC wrappers.
   -- This clock can be shared between multiple MAC instances.
   BUFG_CLK125 : BUFG 
      port map (
         I => clk125_o,
         O => clk125_i
      );

   EMAC_I : entity work.EMAC_TOP2_NOREC
      port map(
         -- EMAC0 Clocking
         -- 125MHz clock output from transceiver
         CLK125_OUT     => clk125_o,
         -- 125MHz clock input from BUFG
         CLK125         => clk125_i,
   
         -- Client Interface - EMAC0
         EMAC0_RX_D           => emac0_rx.D,
         EMAC0_RX_DVLD        => emac0_rx.DVLD,
         EMAC0_RX_GOODFRAME   => emac0_rx.GOODFRAME,
         EMAC0_RX_BADFRAME    => emac0_rx.BADFRAME,
         EMAC0_RX_FRAMEDROP   => emac0_rx.FRAMEDROP,
         EMAC0_RX_STATS       => emac0_rx.STATS,
         EMAC0_RX_STATSVLD    => emac0_rx.STATSVLD,
         EMAC0_RX_STATSBYTEVLD=> emac0_rx.STATSBYTEVLD,

         EMAC0_TX_D           => emac0_tx.D,
         EMAC0_TX_DVLD        => emac0_tx.DVLD,
         EMAC0_TX_ACK         => emac0_tx.ACK,
         EMAC0_TX_FIRSTBYTE   => emac0_tx.FIRSTBYTE,
         EMAC0_TX_UNDERRUN    => emac0_tx.UNDERRUN,
         EMAC0_TX_COLLISION   => emac0_tx.COLLISION,
         EMAC0_TX_RETRANSMIT  => emac0_tx.RETRANSMIT,
         EMAC0_TX_IFGDELAY    => emac0_tx.IFGDELAY,
         EMAC0_TX_STATS       => emac0_tx.STATS,
         EMAC0_TX_STATSVLD    => emac0_tx.STATSVLD,
         EMAC0_TX_STATSBYTEVLD=> emac0_tx.STATSBYTEVLD,

         EMAC0_CONTROL_PAUSEREQ      => emac0_control.PAUSEREQ,
         EMAC0_CONTROL_PAUSEVAL      => emac0_control.PAUSEVAL,
         EMAC0_CONTROL_SYNCACQSTATUS => emac0_control.SYNCACQSTATUS,
         EMAC0_CONTROL_ANINTERRUPT   => emac0_control.ANINTERRUPT,
   
         -- Clock Signals - EMAC0
         -- 1000BASE-X PCS/PMA Interface - EMAC0
         TXP_0          => TXP,
         TXN_0          => TXN,
         RXP_0          => RXP,
         RXN_0          => RXN,
         PHYAD_0        => "00000",
         RESETDONE_0    => emac0_resetdone,

         -- Client Interface - EMAC1
         EMAC1_RX_D           => emac1_rx.D,
         EMAC1_RX_DVLD        => emac1_rx.DVLD,
         EMAC1_RX_GOODFRAME   => emac1_rx.GOODFRAME,
         EMAC1_RX_BADFRAME    => emac1_rx.BADFRAME,
         EMAC1_RX_FRAMEDROP   => emac1_rx.FRAMEDROP,
         EMAC1_RX_STATS       => emac1_rx.STATS,
         EMAC1_RX_STATSVLD    => emac1_rx.STATSVLD,
         EMAC1_RX_STATSBYTEVLD=> emac1_rx.STATSBYTEVLD,

         EMAC1_TX_D           => emac1_tx.D,
         EMAC1_TX_DVLD        => emac1_tx.DVLD,
         EMAC1_TX_ACK         => emac1_tx.ACK,
         EMAC1_TX_FIRSTBYTE   => emac1_tx.FIRSTBYTE,
         EMAC1_TX_UNDERRUN    => emac1_tx.UNDERRUN,
         EMAC1_TX_COLLISION   => emac1_tx.COLLISION,
         EMAC1_TX_RETRANSMIT  => emac1_tx.RETRANSMIT,
         EMAC1_TX_IFGDELAY    => emac1_tx.IFGDELAY,
         EMAC1_TX_STATS       => emac1_tx.STATS,
         EMAC1_TX_STATSVLD    => emac1_tx.STATSVLD,
         EMAC1_TX_STATSBYTEVLD=> emac1_tx.STATSBYTEVLD,

         EMAC1_CONTROL_PAUSEREQ      => emac1_control.PAUSEREQ,
         EMAC1_CONTROL_PAUSEVAL      => emac1_control.PAUSEVAL,
         EMAC1_CONTROL_SYNCACQSTATUS => emac1_control.SYNCACQSTATUS,
         EMAC1_CONTROL_ANINTERRUPT   => emac1_control.ANINTERRUPT,
   
         -- Clock Signals - EMAC1
         -- 1000BASE-X PCS/PMA Interface - EMAC1
         TXP_1          => open,
         TXN_1          => open,
         RXP_1          => '1',
         RXN_1          => '1',
         PHYAD_1        => "00000",
         RESETDONE_1    => emac1_resetdone,


         -- Generic Host Interface
         HOSTCLK        => emac0hostclk,
         HOSTOPCODE     => emac0hostopcode,
         HOSTREQ        => emac0hostreq,
         HOSTMIIMSEL    => emac0hostmiimsel,
         HOSTADDR       => emac0hostaddr,
         HOSTWRDATA     => emac0hostwrdata,
         HOSTMIIMRDY    => emac0hostmiimrdy,
         HOSTRDDATA     => emac0hostrddata,
         HOSTEMAC1SEL   => emac0hostemac1sel,

         -- 1000BASE-X PCS/PMA RocketIO Reference Clock buffer inputs 
         CLK_DS         => clk_ds,
           
         -- Asynchronous Reset
         RESET          => RESET
      );

   -- phy sim emac component instantion
   PHY_SIM_EMAC_I : entity work.phy_sim_emac
      generic map(
         INTER_FRAME   => INTER_FRAME,
         FILE_NAME_RCV => FILE_NAME_RCV,
         -- default value from standard, but for testing frame_toolong check use larger value
         MAX_UNTAGGED_FRAME_SIZE => MAX_UNTAGGED_FRAME_SIZE,
         DEBUG_REPORT  => DEBUG_REPORT
      )
      port map(
         -- Client Interface - EMAC0
         -- Client Receiver Interface - EMAC0
         EMAC_RX_CLK                  => clk125_i,
         EMAC_RX_CE                   => '1',
         EMAC_RX_D                    => emac0_rx.d,
         EMAC_RX_DVLD                 => emac0_rx.dvld,
         EMAC_RX_GOODFRAME            => emac0_rx.goodframe,
         EMAC_RX_BADFRAME             => emac0_rx.badframe,
         EMAC_RX_FRAMEDROP            => emac0_rx.framedrop,
         EMAC_RX_STATS                => emac0_rx.stats,
         EMAC_RX_STATSVLD             => emac0_rx.statsvld,
         EMAC_RX_STATSBYTEVLD         => emac0_rx.statsbytevld,
   
         -- Client Transmitter Interface - EMAC0
         EMAC_TX_CLK                  => clk125_i,
         EMAC_TX_CE                   => '1',
         EMAC_TX_D                    => emac0_tx.d,
         EMAC_TX_DVLD                 => emac0_tx.dvld,
         EMAC_TX_ACK                  => emac0_tx.ack,
         EMAC_TX_FIRSTBYTE            => emac0_tx.firstbyte,
         EMAC_TX_UNDERRUN             => emac0_tx.underrun,
         EMAC_TX_COLLISION            => emac0_tx.collision,
         EMAC_TX_RETRANSMIT           => emac0_tx.retransmit,
         EMAC_TX_IFGDELAY             => emac0_tx.ifgdelay,
         EMAC_TX_STATS                => emac0_tx.stats,
         EMAC_TX_STATSVLD             => emac0_tx.statsvld,
         EMAC_TX_STATSBYTEVLD         => emac0_tx.statsbytevld,
   
         -- MAC Control Interface - EMAC0
         EMAC_CONTROL_PAUSEREQ        => emac0_control.pausereq,
         EMAC_CONTROL_PAUSEVAL        => emac0_control.pauseval,
   
         --EMAC-MGT link status
         EMAC_CONTROL_SYNCACQSTATUS   => emac0_control.syncacqstatus,
         -- EMAC0 Interrupt
         EMAC_CONTROL_ANINTERRUPT     => emac0_control.aninterrupt,
   
         -- Simulation interface ----------------------------------------------
         OPER         => OPER,
         PARAMS       => PARAMS,
         STROBE       => STROBE,
         BUSY         => BUSY
      );
   
end architecture behavioral;

