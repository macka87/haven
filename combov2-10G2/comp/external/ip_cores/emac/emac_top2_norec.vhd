-- emac_pkg.vhd: EMAC layer interface - NO INOUT RECORDS
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

library ieee;
use ieee.std_logic_1164.all;


-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity EMAC_TOP2_NOREC is
   generic(
        INBANDFCS : boolean := true -- true = keep FCS, false = remove FCS
   );
   port(
      -- EMAC0 Clocking
      -- 125MHz clock output from transceiver
      CLK125_OUT     : out std_logic;                 
      -- 125MHz clock input from BUFG
      CLK125         : in  std_logic;

      CLIENT_CLK_OUT_0 : out std_logic;
      CLIENT_CLK_OUT_1 : out std_logic;
   
      -- Client Interface - EMAC0
      -- Client Receiver Interface - EMAC0
      EMAC0_RX_D                    : out std_logic_vector(7 downto 0);
      EMAC0_RX_DVLD                 : out std_logic;
      EMAC0_RX_GOODFRAME            : out std_logic;
      EMAC0_RX_BADFRAME             : out std_logic;
      EMAC0_RX_FRAMEDROP            : out std_logic;
      EMAC0_RX_STATS                : out std_logic_vector(6 downto 0);
      EMAC0_RX_STATSVLD             : out std_logic;
      EMAC0_RX_STATSBYTEVLD         : out std_logic;

      -- Client Transmitter Interface - EMAC0
      EMAC0_TX_D                    : in  std_logic_vector(7 downto 0);
      EMAC0_TX_DVLD                 : in  std_logic;
      EMAC0_TX_ACK                  : out std_logic;
      EMAC0_TX_FIRSTBYTE            : in  std_logic;
      EMAC0_TX_UNDERRUN             : in  std_logic;
      EMAC0_TX_COLLISION            : out std_logic;
      EMAC0_TX_RETRANSMIT           : out std_logic;
      EMAC0_TX_IFGDELAY             : in  std_logic_vector(7 downto 0);
      EMAC0_TX_STATS                : out std_logic;
      EMAC0_TX_STATSVLD             : out std_logic;
      EMAC0_TX_STATSBYTEVLD         : out std_logic;

      -- MAC Control Interface - EMAC0
      EMAC0_CONTROL_PAUSEREQ        : in  std_logic;
      EMAC0_CONTROL_PAUSEVAL        : in  std_logic_vector(15 downto 0);

      --EMAC-MGT link status
      EMAC0_CONTROL_SYNCACQSTATUS   : out std_logic;

      -- Clock Signals - EMAC0
      -- SGMII Interface - EMAC0
      TXP_0                         : out std_logic;
      TXN_0                         : out std_logic;
      RXP_0                         : in  std_logic;
      RXN_0                         : in  std_logic;
      PHYAD_0                       : in  std_logic_vector(4 downto 0);
      RESETDONE_0                   : out std_logic;

      -- Client Interface - EMAC1
      -- Client Receiver Interface - EMAC1
      EMAC1_RX_D                    : out std_logic_vector(7 downto 0);
      EMAC1_RX_DVLD                 : out std_logic;
      EMAC1_RX_GOODFRAME            : out std_logic;
      EMAC1_RX_BADFRAME             : out std_logic;
      EMAC1_RX_FRAMEDROP            : out std_logic;
      EMAC1_RX_STATS                : out std_logic_vector(6 downto 0);
      EMAC1_RX_STATSVLD             : out std_logic;
      EMAC1_RX_STATSBYTEVLD         : out std_logic;

      -- Client Transmitter Interface - EMAC1
      EMAC1_TX_D                    : in  std_logic_vector(7 downto 0);
      EMAC1_TX_DVLD                 : in  std_logic;
      EMAC1_TX_ACK                  : out std_logic;
      EMAC1_TX_FIRSTBYTE            : in  std_logic;
      EMAC1_TX_UNDERRUN             : in  std_logic;
      EMAC1_TX_COLLISION            : out std_logic;
      EMAC1_TX_RETRANSMIT           : out std_logic;
      EMAC1_TX_IFGDELAY             : in  std_logic_vector(7 downto 0);
      EMAC1_TX_STATS                : out std_logic;
      EMAC1_TX_STATSVLD             : out std_logic;
      EMAC1_TX_STATSBYTEVLD         : out std_logic;

      -- MAC Control Interface - EMAC1
      EMAC1_CONTROL_PAUSEREQ        : in  std_logic;
      EMAC1_CONTROL_PAUSEVAL        : in  std_logic_vector(15 downto 0);

      --EMAC-MGT link status
      EMAC1_CONTROL_SYNCACQSTATUS   : out std_logic;

      -- Clock Signals - EMAC1
      -- SGMII Interface - EMAC1
      TXP_1                         : out std_logic;
      TXN_1                         : out std_logic;
      RXP_1                         : in  std_logic;
      RXN_1                         : in  std_logic;
      PHYAD_1                       : in  std_logic_vector(4 downto 0);
      RESETDONE_1                   : out std_logic;

      -- Generic Host Interface
      HOSTCLK                       : in  std_logic;
      HOSTOPCODE                    : in  std_logic_vector(1 downto 0);
      HOSTREQ                       : in  std_logic;
      HOSTMIIMSEL                   : in  std_logic;
      HOSTADDR                      : in  std_logic_vector(9 downto 0);
      HOSTWRDATA                    : in  std_logic_vector(31 downto 0);
      HOSTMIIMRDY                   : out std_logic;
      HOSTRDDATA                    : out std_logic_vector(31 downto 0);
      HOSTEMAC1SEL                  : in  std_logic;

      -- RocketIO Reference Clock buffer inputs
      CLK_DS         : in  std_logic;
        
      -- Asynchronous Reset
      RESET          : in  std_logic
   );
end EMAC_TOP2_NOREC;


-- ----------------------------------------------------------------------------
--                         Architecture declaration
-- ----------------------------------------------------------------------------

architecture top_level of EMAC_TOP2_NOREC is

   -- -------------------------------------------------------------------------
   --                          Signal Declarations
   -- -------------------------------------------------------------------------

   ----- Asynchronous reset signals -----
   signal reset_i                   : std_logic;
   signal reset_r                   : std_logic_vector(3 downto 0);
   signal gtreset                   : std_logic;

   ----- EMAC0 clocking signals -----
   signal client_clk_0_sig          : std_logic;
   signal client_clk_out_0_sig      : std_logic;
   
   ----- EMAC1 clocking signals -----
   signal client_clk_1_sig       : std_logic;
   signal client_clk_out_1_sig   : std_logic;
   
   ----- AN Interrupt signals
   signal emac0_aninterrupt	    : std_logic;
   signal emac1_aninterrupt	    : std_logic;
   
   -- -------------------------------------------------------------------------
   --                        Component Declarations
   -- -------------------------------------------------------------------------
   
   -- Clock Buffer
   component BUFG is
   port (
            I : in  std_logic;
 	         O : out std_logic
   );
   end component;
   
   ----------------------------------------------------------------------------
   --                         Attribute Declarations
   ----------------------------------------------------------------------------

   attribute ASYNC_REG : string;
   attribute ASYNC_REG of reset_r : signal is "TRUE";


begin

    ---------------------------------------------------------------------------
    -- Reset Circuitry
    ---------------------------------------------------------------------------

    reset_i <= RESET;


    process(reset_i, CLK125)
    begin
      if (reset_i = '1') then
	 reset_r <= "1111";
      elsif (CLK125'event and CLK125 = '1') then
         reset_r <= reset_r(2 downto 0) & reset_i;
      end if;	
    end process;

    gtreset <= reset_r(3);

   ----------------------------------------------------------------------------
   --                   Assign signal values to output ports
   ----------------------------------------------------------------------------

   CLIENT_CLK_OUT_0		 <= client_clk_0_sig;
   CLIENT_CLK_OUT_1		 <= client_clk_1_sig;
   
   ----------------------------------------------------------------------------
   --                         EMAC wrapper instantion
   ----------------------------------------------------------------------------

   EMAC_BLOCK : entity work.v5_emac_v1_6_block
      generic map(
         INBANDFCS                       => INBANDFCS
      )
      port map(
         -- EMAC0 Clocking
         -- 125MHz clock output from transciever
	 CLK125_OUT			 => CLK125_OUT,
	 -- 125MHz clock input from BUGF
	 CLK125				 => CLK125,
	 -- Tri-speed clock output from EMAC0
	 CLIENT_CLK_OUT_0		 => client_clk_out_0_sig,
	 -- EMAC0 Tri-speed clock input from BUFG
	 CLIENT_CLK_0			 => client_clk_0_sig, 

         -- Client Receiver Interface - EMAC0
         EMAC0CLIENTRXD                  => EMAC0_RX_D,
         EMAC0CLIENTRXDVLD               => EMAC0_RX_DVLD,
         EMAC0CLIENTRXGOODFRAME          => EMAC0_RX_GOODFRAME,
         EMAC0CLIENTRXBADFRAME           => EMAC0_RX_BADFRAME,
         EMAC0CLIENTRXFRAMEDROP          => EMAC0_RX_FRAMEDROP,
         EMAC0CLIENTRXSTATS              => EMAC0_RX_STATS,
         EMAC0CLIENTRXSTATSVLD           => EMAC0_RX_STATSVLD,
         EMAC0CLIENTRXSTATSBYTEVLD       => EMAC0_RX_STATSBYTEVLD,

         -- Client Transmitter Interface - EMAC0
         CLIENTEMAC0TXD                  => EMAC0_TX_D,
         CLIENTEMAC0TXDVLD               => EMAC0_TX_DVLD,
         EMAC0CLIENTTXACK                => EMAC0_TX_ACK,
         CLIENTEMAC0TXFIRSTBYTE          => EMAC0_TX_FIRSTBYTE,
         CLIENTEMAC0TXUNDERRUN           => EMAC0_TX_UNDERRUN,
         EMAC0CLIENTTXCOLLISION          => EMAC0_TX_COLLISION,
         EMAC0CLIENTTXRETRANSMIT         => EMAC0_TX_RETRANSMIT,
         CLIENTEMAC0TXIFGDELAY           => EMAC0_TX_IFGDELAY,
         EMAC0CLIENTTXSTATS              => EMAC0_TX_STATS,
         EMAC0CLIENTTXSTATSVLD           => EMAC0_TX_STATSVLD,
         EMAC0CLIENTTXSTATSBYTEVLD       => EMAC0_TX_STATSBYTEVLD,

         -- MAC Control Interface - EMAC0
         CLIENTEMAC0PAUSEREQ             => EMAC0_CONTROL_PAUSEREQ,
         CLIENTEMAC0PAUSEVAL             => EMAC0_CONTROL_PAUSEVAL,
         
	 -- EMAC-MGT link status
	 EMAC0CLIENTSYNCACQSTATUS	 => EMAC0_CONTROL_SYNCACQSTATUS,
         -- EMAC0 Interrupt
	 EMAC0ANINTERRUPT		 => emac0_aninterrupt,

 	 -- Clock Signals - EMAC0
	 -- SGMII Interface - EMAC0
	 TXP_0				 => TXP_0,
	 TXN_0				 => TXN_0,
	 RXP_0				 => RXP_0,
	 RXN_0				 => RXN_0,
	 PHYAD_0			 => PHYAD_0,
	 RESETDONE_0			 => RESETDONE_0,

         -- MDIO Interface - EMAC0
         MDC_0                           => open,
         MDIO_0_I                        => '1',
         MDIO_0_O                        => open,
         MDIO_0_T                        => open,


         -- EMAC1 Clocking
	 -- Tri-speed clock output from EMAC1
	 CLIENT_CLK_OUT_1		 => client_clk_out_1_sig,
	 -- EMAC1 Tri-speed clock input from BUFG
	 CLIENT_CLK_1                    => client_clk_1_sig,
	 

         -- Client Receiver Interface - EMAC1
         EMAC1CLIENTRXD                  => EMAC1_RX_D,
         EMAC1CLIENTRXDVLD               => EMAC1_RX_DVLD,
         EMAC1CLIENTRXGOODFRAME          => EMAC1_RX_GOODFRAME,
         EMAC1CLIENTRXBADFRAME           => EMAC1_RX_BADFRAME,
         EMAC1CLIENTRXFRAMEDROP          => EMAC1_RX_FRAMEDROP,
         EMAC1CLIENTRXSTATS              => EMAC1_RX_STATS,
         EMAC1CLIENTRXSTATSVLD           => EMAC1_RX_STATSVLD,
         EMAC1CLIENTRXSTATSBYTEVLD       => EMAC1_RX_STATSBYTEVLD,

         -- Client Transmitter Interface - EMAC1
         CLIENTEMAC1TXD                  => EMAC1_TX_D,
         CLIENTEMAC1TXDVLD               => EMAC1_TX_DVLD,
         EMAC1CLIENTTXACK                => EMAC1_TX_ACK,
         CLIENTEMAC1TXFIRSTBYTE          => EMAC1_TX_FIRSTBYTE,
         CLIENTEMAC1TXUNDERRUN           => EMAC1_TX_UNDERRUN,
         EMAC1CLIENTTXCOLLISION          => EMAC1_TX_COLLISION,
         EMAC1CLIENTTXRETRANSMIT         => EMAC1_TX_RETRANSMIT,
         CLIENTEMAC1TXIFGDELAY           => EMAC1_TX_IFGDELAY,
         EMAC1CLIENTTXSTATS              => EMAC1_TX_STATS,
         EMAC1CLIENTTXSTATSVLD           => EMAC1_TX_STATSVLD,
         EMAC1CLIENTTXSTATSBYTEVLD       => EMAC1_TX_STATSBYTEVLD,
         
         -- MAC Control Interface - EMAC1
         CLIENTEMAC1PAUSEREQ             => EMAC1_CONTROL_PAUSEREQ,
         CLIENTEMAC1PAUSEVAL             => EMAC1_CONTROL_PAUSEVAL,
	 
         -- EMAC-MGT link status
	 EMAC1CLIENTSYNCACQSTATUS	 => EMAC1_CONTROL_SYNCACQSTATUS,
         -- EMAC0 Interrupt
	 EMAC1ANINTERRUPT		 => emac1_aninterrupt,


 	 -- Clock Signals - EMAC0
	 -- SGMII Interface - EMAC0
	 TXP_1				 => TXP_1,
	 TXN_1				 => TXN_1,
	 RXP_1				 => RXP_1,
	 RXN_1				 => RXN_1,
	 PHYAD_1			 => PHYAD_1,
	 RESETDONE_1			 => RESETDONE_1,

         -- MDIO Interface - EMAC1
         MDC_1                           => open,
         MDIO_1_I                        => '1',
         MDIO_1_O                        => open,
         MDIO_1_T                        => open,

         -- Generic Host Interface
         HOSTCLK                         => HOSTCLK,
         HOSTOPCODE                      => HOSTOPCODE,
         HOSTREQ                         => HOSTREQ,
         HOSTMIIMSEL                     => HOSTMIIMSEL,
         HOSTADDR                        => HOSTADDR,
         HOSTWRDATA                      => HOSTWRDATA,
         HOSTMIIMRDY                     => HOSTMIIMRDY,
         HOSTRDDATA                      => HOSTRDDATA,
         HOSTEMAC1SEL                    => HOSTEMAC1SEL,

	 -- SGMII RocketIO Reference Clock buffer inputs
	 CLK_DS				 => CLK_DS,

	 -- RocketIO Reset Input
	 GTRESET			 => gtreset,

         -- Asynchronous Reset
         RESET                           => reset_i
      );


   ----------------------------------------------------------------------------
   --                         Clock Buffer instantions
   ----------------------------------------------------------------------------

   ----- EMAC0 -----
   EMAC0_BUFG : BUFG
   port map(
               O  => client_clk_0_sig,
               I  => client_clk_out_0_sig
   );

   ----- EMAC1 -----
   EMAC1_BUFG : BUFG
   port map(
               O  => client_clk_1_sig,
               I  => client_clk_out_1_sig
   );

end top_level;
