-- combov2_core_ent.vhd : Combov2 top level entity
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

-- --------------------------------------------------------------------
--                          Entity declaration
-- --------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;

entity COMBOV2_CORE is
   port (
      -- ----------------------------------------------------------------------
      -- CLOCKs and RESETs
      -- ----------------------------------------------------------------------
      -- Clock signals from CLK_GEN (which is driven by XCLK2)
      CLK_ICS        : in std_logic; -- Clocks with selectable frequency.
      CLK_USER0      : in std_logic; 
      CLK_USER1      : in std_logic; 
      CLK_USER2      : in std_logic; 
      CLK_USER3      : in std_logic; 
      CLK_USER4      : in std_logic; 
      CLK125         : in std_logic; -- Clocks with fixed frequency.
      CLK100         : in std_logic;
      CLK250         : in std_logic;
      CLK62_5        : in std_logic;
      CLK200         : in std_logic;
      CLK166         : in std_logic;
      -- Reset signals from CLK_GEN
      RESET_ICS      : in std_logic;
      RESET_USER0    : in std_logic;
      RESET_USER1    : in std_logic;
      RESET_USER2    : in std_logic;
      RESET_USER3    : in std_logic;
      RESET_USER4    : in std_logic;
      RESET125       : in std_logic;
      RESET100       : in std_logic;
      RESET250       : in std_logic;
      RESET62_5      : in std_logic;
      RESET200       : in std_logic;
      RESET166       : in std_logic;

      -- ----------------------------------------------------------------------
      -- XGMII SDR interface from IFC1 (2 ports)
      -- ----------------------------------------------------------------------
      -- RX
      XGMII_RESET          : in  std_logic_vector(  1 downto 0);
      XGMII_RXCLK          : in  std_logic_vector(  1 downto 0);
      XGMII_RXD            : in  std_logic_vector(127 downto 0);
      XGMII_RXC            : in  std_logic_vector( 15 downto 0);
      -- TX
      XGMII_TXCLK          :  in std_logic_vector(  1 downto 0);
      XGMII_TXD            : out std_logic_vector(127 downto 0);
      XGMII_TXC            : out std_logic_vector( 15 downto 0);

      -- ----------------------------------------------------------------------
      -- Interconnection system
      -- ----------------------------------------------------------------------
      -- Internal Bus
      IB_DOWN_DATA       : in  std_logic_vector(63 downto 0);
      IB_DOWN_SOF_N      : in  std_logic;
      IB_DOWN_EOF_N      : in  std_logic;
      IB_DOWN_SRC_RDY_N  : in  std_logic;
      IB_DOWN_DST_RDY_N  : out std_logic;
      IB_UP_DATA         : out std_logic_vector(63 downto 0);
      IB_UP_SOF_N        : out std_logic;
      IB_UP_EOF_N        : out std_logic;
      IB_UP_SRC_RDY_N    : out std_logic;
      IB_UP_DST_RDY_N    : in  std_logic;
      -- MI32 to user application
      MI32_USER_DWR        : in  std_logic_vector(31 downto 0);
      MI32_USER_ADDR       : in  std_logic_vector(31 downto 0);
      MI32_USER_RD         : in  std_logic;
      MI32_USER_WR         : in  std_logic;
      MI32_USER_BE         : in  std_logic_vector(3 downto 0);
      MI32_USER_DRD        : out std_logic_vector(31 downto 0);
      MI32_USER_ARDY       : out std_logic;
      MI32_USER_DRDY       : out std_logic;
      -- MI32 to DMA module
      MI32_DMA_DWR        : in  std_logic_vector(31 downto 0);
      MI32_DMA_ADDR       : in  std_logic_vector(31 downto 0);
      MI32_DMA_RD         : in  std_logic;
      MI32_DMA_WR         : in  std_logic;
      MI32_DMA_BE         : in  std_logic_vector(3 downto 0);
      MI32_DMA_DRD        : out std_logic_vector(31 downto 0);
      MI32_DMA_ARDY       : out std_logic;
      MI32_DMA_DRDY       : out std_logic;
      -- MI32 to Network module
      MI32_NET_DWR        : in  std_logic_vector(31 downto 0);
      MI32_NET_ADDR       : in  std_logic_vector(31 downto 0);
      MI32_NET_RD         : in  std_logic;
      MI32_NET_WR         : in  std_logic;
      MI32_NET_BE         : in  std_logic_vector(3 downto 0);
      MI32_NET_DRD        : out std_logic_vector(31 downto 0);
      MI32_NET_ARDY       : out std_logic;
      MI32_NET_DRDY       : out std_logic;
      -- Interrupt system
      INTERRUPT      : out std_logic_vector(31 downto 0);
      INTR_RDY       : in  std_logic;
      SYSMON_ALARM   : in  std_logic;

      -- ----------------------------------------------------------------------
      -- QDRII Memories
      -- ----------------------------------------------------------------------

      -- QDRII Memory 1
         -- Data --
      S0Q            : in std_logic_vector( 17 downto 0 );
      S0D            : out std_logic_vector( 17 downto 0 );
         -- Address --
      S0A            : out std_logic_vector( 20 downto 0 );
         -- Control --
      S0BWS_N        : out std_logic_vector( 1 downto 0 );
      S0CQ_P         : in std_logic;
      S0CQ_N         : in std_logic;
      S0K_P          : out std_logic;
      S0K_N          : out std_logic;
      S0C_P          : out std_logic;
      S0C_N          : out std_logic;
      S0WPS_N        : out std_logic;
      S0RPS_N        : out std_logic;
      S0DOFF_N       : out std_logic;

      -- QDRII Memory 2
         -- Data --
      S1Q            : in std_logic_vector( 17 downto 0 );
      S1D            : out std_logic_vector( 17 downto 0 );
         -- Address --
      S1A            : out std_logic_vector( 20 downto 0 );
         -- Control --
      S1BWS_N        : out std_logic_vector( 1 downto 0 );
      S1CQ_P         : in std_logic;
      S1CQ_N         : in std_logic;
      S1K_P          : out std_logic;
      S1K_N          : out std_logic;
      S1C_P          : out std_logic;
      S1C_N          : out std_logic;
      S1WPS_N        : out std_logic;
      S1RPS_N        : out std_logic;
      S1DOFF_N       : out std_logic;

      -- ----------------------------------------------------------------------
      -- DDR2 DRAM/RLDRAM Memory
      -- ----------------------------------------------------------------------
      -- Adress --
      DA             : out std_logic_vector( 13 downto 0 );
      -- Data --
      DDQ            : inout std_logic_vector( 63 downto 0 );
      -- Control --
      DDM            : out std_logic_vector( 7 downto 0 );
      DBA            : out std_logic_vector( 2 downto 0 );
      DCS_N          : out std_logic_vector( 1 downto 0 );
      DRAS_N         : out std_logic;
      DCAS_N         : out std_logic;
      DWE_N          : out std_logic;
      DCK0_P         : out std_logic;
      DCK0_N         : out std_logic;
      DCK1_P         : out std_logic;
      DCK1_N         : out std_logic;
      DCKE           : out std_logic_vector( 1 downto 0 );
      DDODT          : out std_logic_vector( 1 downto 0 );
      DSDA           : inout std_logic;
      DSCL           : out std_logic;
      DSA            : out std_logic_vector( 1 downto 0 );
      DDQS_P         : inout std_logic_vector( 7 downto 0 );
      DDQS_N         : inout std_logic_vector( 7 downto 0 );

      -- ----------------------------------------------------------------------
      -- Oscillators
      -- ----------------------------------------------------------------------
      MCLK1_P        : in std_logic;
      MCLK1_N        : in std_logic;
      MCLK0_P        : in std_logic;
      MCLK0_N        : in std_logic;
      -- PCI Clk 
      GCLK100_P      : in std_logic;
      GCLK100_N      : in std_logic;
      GCLK250_P      : in std_logic;
      GCLK250_N      : in std_logic;
      -- PLL Clk
      XCLK0_P        : in std_logic;
      XCLK0_N        : in std_logic;
      XCLK1_P        : in std_logic;
      XCLK1_N        : in std_logic;

      -- Dorectly from XCLK2 xtal, only through IBUFGDS
      XCLK2          : in std_logic; 

      -- ----------------------------------------------------------------------
      -- Serial
      -- ----------------------------------------------------------------------
      FQTXD          : out std_logic;
      FQRXD          : in  std_logic;

      -- ----------------------------------------------------------------------
      -- LED
      -- ----------------------------------------------------------------------
      IBUF_LED       : out std_logic_vector(1 downto 0);
      OBUF_LED       : out std_logic_vector(1 downto 0);
      FQLED          : out std_logic_vector(3 downto 0);

      -- -------------------------------------------------------------------
      -- TIMESTAMPS FOR PACODAG
      -- -------------------------------------------------------------------
      TS             : in std_logic_vector(63 downto 0); -- fractional* format of timestamp
      TS_NS          : in std_logic_vector(63 downto 0); -- nanosecond* format of timestamp
      TS_DV          : in std_logic;                     -- data valid timestamp (determines validity of timestamp)
      TS_CLK         : in std_logic                      -- clock at which are timestamps synchronous
                                                         -- * more info about timestamp formats can be found here: https://www.liberouter.org/trac/netcope/wiki/format_timestamp
   );
end COMBOV2_CORE;

