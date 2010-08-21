-- combov2_netcope.vhd : Inner higher-level NetCOPE layer for COMBOv2
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
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.combov2_user_const.all;
use work.combov2_nc_const.all;
use work.combov2_pkg.all;

entity COMBOV2_NETCOPE is
   generic(
      BUILD_TIME      : std_logic_vector(31 downto 0) := X"00000000";
      BUILD_UID       : std_logic_vector(31 downto 0) := X"00000000";
      USER_GENERIC0   : std_logic_vector(31 downto 0) := X"00000000";
      USER_GENERIC1   : std_logic_vector(31 downto 0) := X"00000000";
      USER_GENERIC2   : std_logic_vector(31 downto 0) := X"00000000";
      USER_GENERIC3   : std_logic_vector(31 downto 0) := X"00000000"
   );
   port (
      -- ----------------------------------------------------------------------
      -- CLOCKs and RESETs
      -- ----------------------------------------------------------------------
      -- Clock signal from PCI brigde (125 or 250 MHz)
      USER_CLK             : in std_logic;
      -- Global reset from PCI bridge
      RESET                : in std_logic;

      -- 125 MHz clock (for Spartan interface and XAUI DCMs)
      CLK_125              : out std_logic;
      RESET_125            : out std_logic;

      -- ----------------------------------------------------------------------
      -- XGMII interface from IFC1 (2 ports)
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
      
      -- Mdio interface
      MDCA                 : out   std_logic;
      MDIOA                : inout std_logic;
      MDCB                 : out   std_logic;
      MDIOB                : inout std_logic;

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
      -- Interconnection system
      -- ----------------------------------------------------------------------
      -- Internal Bus

      -- We generate our own ICS clock in clk_gen_cv2 module
      IB_CLK             : out std_logic;
      IB_RST             : out std_logic;

      IB_DOWN_DATA       : in  std_logic_vector(63 downto 0);
      IB_DOWN_SOP_N      : in  std_logic;
      IB_DOWN_EOP_N      : in  std_logic;
      IB_DOWN_SRC_RDY_N  : in  std_logic;
      IB_DOWN_DST_RDY_N  : out std_logic;
      IB_UP_DATA         : out std_logic_vector(63 downto 0);
      IB_UP_SOP_N        : out std_logic;
      IB_UP_EOP_N        : out std_logic;
      IB_UP_SRC_RDY_N    : out std_logic;
      IB_UP_DST_RDY_N    : in  std_logic;
      -- Interrupt system
      INTERRUPT      : out std_logic;
      INTR_DATA      : out std_logic_vector(4 downto 0);
      INTR_RDY       : in  std_logic;

      -- Phyter setting signals
      WANMODEA       : out std_logic;
      TXONOFFA       : out std_logic;
      AUTONEGA       : out std_logic;
      EPCSA          : out std_logic;
      RSTPHYA_N      : out std_logic;
      PDOWNA         : out std_logic;
      TXDISA         : out std_logic;
      MODDESELA      : out std_logic;

      WANMODEB       : out std_logic;
      TXONOFFB       : out std_logic;
      AUTONEGB       : out std_logic;
      EPCSB          : out std_logic;
      RSTPHYB_N      : out std_logic;
      PDOWNB         : out std_logic;
      TXDISB         : out std_logic;
      MODDESELB      : out std_logic;

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

      XCLK2          : in std_logic; -- Already output from IBUFGDS

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

      -- ----------------------------------------------------------------------
      -- PPS_N signal from PTM card with GPS
      -- ----------------------------------------------------------------------
      PPS_N          : in std_logic;
      -- ----------------------------------------------------------------------
      -- CLK signal from PTM card precise crystal
      -- ----------------------------------------------------------------------
      PTM_CLK        : in std_logic
   );
end COMBOV2_NETCOPE;

-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of COMBOV2_NETCOPE is
   -- ------------------ Components declaration -------------------------------
   component netcope_ics is
   port(
      -- ----------------------------------------------------------------------
      -- CLOCKs and RESET
      -- ----------------------------------------------------------------------
      -- CLK:
      CLK               : in std_logic;
      -- reset
      RESET             : in std_logic;
      
      -- Internal Bus CV2_PCI <-> NETCOPE_BASE
      PCI_IB_DOWN_DATA        : in  std_logic_vector(63 downto 0);
      PCI_IB_DOWN_SOP_N       : in  std_logic;
      PCI_IB_DOWN_EOP_N       : in  std_logic;
      PCI_IB_DOWN_SRC_RDY_N   : in  std_logic;
      PCI_IB_DOWN_DST_RDY_N   : out std_logic;
      PCI_IB_UP_DATA          : out std_logic_vector(63 downto 0);
      PCI_IB_UP_SOP_N         : out std_logic;
      PCI_IB_UP_EOP_N         : out std_logic;
      PCI_IB_UP_SRC_RDY_N     : out std_logic;
      PCI_IB_UP_DST_RDY_N     : in  std_logic;

      -- 64bit Internal Bus NETCOPE_BASE <-> COMBOV2_CORE
      USER_IB64_DOWN_DATA        : out std_logic_vector(63 downto 0);
      USER_IB64_DOWN_SOF_N       : out std_logic;
      USER_IB64_DOWN_EOF_N       : out std_logic;
      USER_IB64_DOWN_SRC_RDY_N   : out std_logic;
      USER_IB64_DOWN_DST_RDY_N   : in  std_logic;
      USER_IB64_UP_DATA          : in  std_logic_vector(63 downto 0);
      USER_IB64_UP_SOF_N         : in  std_logic;
      USER_IB64_UP_EOF_N         : in  std_logic;
      USER_IB64_UP_SRC_RDY_N     : in  std_logic;
      USER_IB64_UP_DST_RDY_N     : out std_logic;
      
      -- MI32 interface NETCOPE_BASE <-> COMBOV2_CORE - Application
      USER_MI32_DWR   : out std_logic_vector(31 downto 0);
      USER_MI32_ADDR  : out std_logic_vector(31 downto 0);
      USER_MI32_RD    : out std_logic;
      USER_MI32_WR    : out std_logic;
      USER_MI32_BE    : out std_logic_vector( 3 downto 0);
      USER_MI32_DRD   : in  std_logic_vector(31 downto 0);
      USER_MI32_ARDY  : in  std_logic;
      USER_MI32_DRDY  : in  std_logic;
      
      -- MI32 interface NETCOPE_BASE <-> COMBOV2_CORE - DMA Module
      DMA_DWR   : out std_logic_vector(31 downto 0);
      DMA_ADDR  : out std_logic_vector(31 downto 0);
      DMA_RD    : out std_logic;
      DMA_WR    : out std_logic;
      DMA_BE    : out std_logic_vector( 3 downto 0);
      DMA_DRD   : in  std_logic_vector(31 downto 0);
      DMA_ARDY  : in  std_logic;
      DMA_DRDY  : in  std_logic;
      
      -- MI32 interface NETCOPE_BASE <-> COMBOV2_CORE - Network module
      NET_DWR   : out std_logic_vector(31 downto 0);
      NET_ADDR  : out std_logic_vector(31 downto 0);
      NET_RD    : out std_logic;
      NET_WR    : out std_logic;
      NET_BE    : out std_logic_vector( 3 downto 0);
      NET_DRD   : in  std_logic_vector(31 downto 0);
      NET_ARDY  : in  std_logic;
      NET_DRDY  : in  std_logic;
      
      -- MI32 interface NETCOPE_BASE <-> TSU_CV2_MI32
      TSU_DWR   : out std_logic_vector(31 downto 0);
      TSU_ADDR  : out std_logic_vector(31 downto 0);
      TSU_RD    : out std_logic;
      TSU_WR    : out std_logic;
      TSU_BE    : out std_logic_vector( 3 downto 0);
      TSU_DRD   : in  std_logic_vector(31 downto 0);
      TSU_ARDY  : in  std_logic;
      TSU_DRDY  : in  std_logic;
      
      -- MI32 interface NETCOPE_BASE <-> PHYTER_I2C_MI32
      PHY_DWR   : out std_logic_vector(31 downto 0);
      PHY_ADDR  : out std_logic_vector(31 downto 0);
      PHY_RD    : out std_logic;
      PHY_WR    : out std_logic;
      PHY_BE    : out std_logic_vector( 3 downto 0);
      PHY_DRD   : in  std_logic_vector(31 downto 0);
      PHY_ARDY  : in  std_logic;
      PHY_DRDY  : in  std_logic;
      
      -- MI32 interface NETCOPE_BASE <-> ID_COMP_MI32
      ID_DWR   : out std_logic_vector(31 downto 0);
      ID_ADDR  : out std_logic_vector(31 downto 0);
      ID_RD    : out std_logic;
      ID_WR    : out std_logic;
      ID_BE    : out std_logic_vector( 3 downto 0);
      ID_DRD   : in  std_logic_vector(31 downto 0);
      ID_ARDY  : in  std_logic;
      ID_DRDY  : in  std_logic;
      
      -- MI32 interface NETCOPE_BASE <-> IFC1 Connector space
      IFC1_DWR   : out std_logic_vector(31 downto 0);
      IFC1_ADDR  : out std_logic_vector(31 downto 0);
      IFC1_RD    : out std_logic;
      IFC1_WR    : out std_logic;
      IFC1_BE    : out std_logic_vector( 3 downto 0);
      IFC1_DRD   : in  std_logic_vector(31 downto 0);
      IFC1_ARDY  : in  std_logic;
      IFC1_DRDY  : in  std_logic;
      
      -- MI32 interface NETCOPE_BASE <-> IFC2 Connector space
      IFC2_DWR   : out std_logic_vector(31 downto 0);
      IFC2_ADDR  : out std_logic_vector(31 downto 0);
      IFC2_RD    : out std_logic;
      IFC2_WR    : out std_logic;
      IFC2_BE    : out std_logic_vector( 3 downto 0);
      IFC2_DRD   : in  std_logic_vector(31 downto 0);
      IFC2_ARDY  : in  std_logic;
      IFC2_DRDY  : in  std_logic;
      
      -- MI32 interface NETCOPE_BASE <-> LSC1 Connector space
      LSC1_DWR   : out std_logic_vector(31 downto 0);
      LSC1_ADDR  : out std_logic_vector(31 downto 0);
      LSC1_RD    : out std_logic;
      LSC1_WR    : out std_logic;
      LSC1_BE    : out std_logic_vector( 3 downto 0);
      LSC1_DRD   : in  std_logic_vector(31 downto 0);
      LSC1_ARDY  : in  std_logic;
      LSC1_DRDY  : in  std_logic;
      
      -- MI32 interface NETCOPE_BASE <-> LSC2 Connector space
      LSC2_DWR   : out std_logic_vector(31 downto 0);
      LSC2_ADDR  : out std_logic_vector(31 downto 0);
      LSC2_RD    : out std_logic;
      LSC2_WR    : out std_logic;
      LSC2_BE    : out std_logic_vector( 3 downto 0);
      LSC2_DRD   : in  std_logic_vector(31 downto 0);
      LSC2_ARDY  : in  std_logic;
      LSC2_DRDY  : in  std_logic;
      
      -- MI32 interface NETCOPE_BASE <-> LSC3 Connector space
      LSC3_DWR   : out std_logic_vector(31 downto 0);
      LSC3_ADDR  : out std_logic_vector(31 downto 0);
      LSC3_RD    : out std_logic;
      LSC3_WR    : out std_logic;
      LSC3_BE    : out std_logic_vector( 3 downto 0);
      LSC3_DRD   : in  std_logic_vector(31 downto 0);
      LSC3_ARDY  : in  std_logic;
      LSC3_DRDY  : in  std_logic;
      
      -- MI32 interface NETCOPE_BASE <-> LSC4 Connector space
      LSC4_DWR   : out std_logic_vector(31 downto 0);
      LSC4_ADDR  : out std_logic_vector(31 downto 0);
      LSC4_RD    : out std_logic;
      LSC4_WR    : out std_logic;
      LSC4_BE    : out std_logic_vector( 3 downto 0);
      LSC4_DRD   : in  std_logic_vector(31 downto 0);
      LSC4_ARDY  : in  std_logic;
      LSC4_DRDY  : in  std_logic
   );
   end component;

   component tsu_cv2 is
   generic (
     -- Defines whether to use DSP's for timestamp format conversion
     TS_MULT_USE_DSP              : boolean := true; -- true = use DSP's, false = disable DSP's
     -- Application frequency in Hz
     COMBOV2_REF_CLK_FREQUENCY    : integer := 166666666; -- frequency of combov2 clk
     PTM_PRECISE_CLK_FREQUENCY    : integer := 160000000 -- frequency of ptm precise crystal clk
   );
   port (
      -- Combo clock and reset signals for MI_32 interface
      MI32_CLK   	: in std_logic; 
      MI32_RESET 	: in std_logic;

      -- In / Out SW interface via MI_32
      DWR     	: in std_logic_vector(31 downto 0);
      ADDR		: in std_logic_vector(31 downto 0);
      RD		: in std_logic;
      WR		: in std_logic;
      BE		: in std_logic_vector(3 downto 0);
      DRD		: out std_logic_vector(31 downto 0);
      ARDY		: out std_logic;
      DRDY		: out std_logic;

      -- Input PPS_N signal from GPS
      GPS_PPS_N        : in std_logic;

      -- -------------------------------------------
      -- TSU core clock ----------------------------
      -- -------------------------------------------
      -- COMBOv2 base clock
      COMBOV2_REF_CLK   : in std_logic;
      COMBOV2_REF_RESET : in std_logic;
      -- PTM precise crystal clock
      PTM_PRECISE_CLK   : in std_logic;
      PTM_PRECISE_RESET : in std_logic;

      -- Output clk for tsu_async unit
      TS_CLK            : out std_logic;

      -- Output pacodag interface
      TS  	 	     : out std_logic_vector(63 downto 0);
      TS_NS  	 	     : out std_logic_vector(63 downto 0);
      TS_DV	     : out std_logic  -- timestamp is valid (one cycle)
   );
   end component tsu_cv2;

   component  mdio_ctrl_top2_mi32 is
   port (
      -- Common interface
      RESET    : in    std_logic;
      CLK      : in    std_logic;

      -- Mdio interface
      MDCA     : out std_logic;
      MDIOA_I  : in  std_logic;
      MDIOA_O  : out std_logic;
      MDIOA_OE : out std_logic;
      MDCB     : out std_logic;
      MDIOB_I  : in  std_logic;
      MDIOB_O  : out std_logic;
      MDIOB_OE : out std_logic;

      -- MI32 interface
      MI_DWR            : in  std_logic_vector(31 downto 0);
      MI_ADDR           : in  std_logic_vector(31 downto 0);
      MI_RD             : in  std_logic;
      MI_WR             : in  std_logic;
      MI_BE             : in  std_logic_vector(3  downto 0);
      MI_DRD            : out std_logic_vector(31 downto 0);
      MI_ARDY           : out std_logic;
      MI_DRDY           : out std_logic
      );
   end component mdio_ctrl_top2_mi32;

   -- ------------------ Signals declaration ----------------------------------
   -- Internal Bus signals
   signal ib_user_up_data          : std_logic_vector(63 downto 0);
   signal ib_user_up_sof_n         : std_logic;
   signal ib_user_up_eof_n         : std_logic;
   signal ib_user_up_src_rdy_n     : std_logic;
   signal ib_user_up_dst_rdy_n     : std_logic;
   signal ib_user_down_data        : std_logic_vector(63 downto 0);
   signal ib_user_down_sof_n       : std_logic;
   signal ib_user_down_eof_n       : std_logic;
   signal ib_user_down_src_rdy_n   : std_logic;
   signal ib_user_down_dst_rdy_n   : std_logic;

   -- MI32 signals
   signal mi_user_dwr   : std_logic_vector(31 downto 0);
   signal mi_user_addr  : std_logic_vector(31 downto 0);
   signal mi_user_rd    : std_logic;
   signal mi_user_wr    : std_logic;
   signal mi_user_be    : std_logic_vector( 3 downto 0);
   signal mi_user_drd   : std_logic_vector(31 downto 0);
   signal mi_user_ardy  : std_logic;
   signal mi_user_drdy  : std_logic;
   
   signal mi_dma_dwr    : std_logic_vector(31 downto 0);
   signal mi_dma_addr   : std_logic_vector(31 downto 0);
   signal mi_dma_rd     : std_logic;
   signal mi_dma_wr     : std_logic;
   signal mi_dma_be     : std_logic_vector( 3 downto 0);
   signal mi_dma_drd    : std_logic_vector(31 downto 0);
   signal mi_dma_ardy   : std_logic;
   signal mi_dma_drdy   : std_logic;

   signal mi_net_dwr    : std_logic_vector(31 downto 0);
   signal mi_net_addr   : std_logic_vector(31 downto 0);
   signal mi_net_rd     : std_logic;
   signal mi_net_wr     : std_logic;
   signal mi_net_be     : std_logic_vector( 3 downto 0);
   signal mi_net_drd    : std_logic_vector(31 downto 0);
   signal mi_net_ardy   : std_logic;
   signal mi_net_drdy   : std_logic;

   signal mi_tsu_cv2_dwr     : std_logic_vector(31 downto 0);
   signal mi_tsu_cv2_addr    : std_logic_vector(31 downto 0);
   signal mi_tsu_cv2_rd      : std_logic;
   signal mi_tsu_cv2_wr      : std_logic;
   signal mi_tsu_cv2_be      : std_logic_vector(3 downto 0);
   signal mi_tsu_cv2_drd     : std_logic_vector(31 downto 0);
   signal mi_tsu_cv2_ardy    : std_logic;
   signal mi_tsu_cv2_drdy    : std_logic;

   signal mi_phy_mdio_dwr    : std_logic_vector(31 downto 0);
   signal mi_phy_mdio_addr   : std_logic_vector(31 downto 0);
   signal mi_phy_mdio_rd     : std_logic;
   signal mi_phy_mdio_wr     : std_logic;
   signal mi_phy_mdio_be     : std_logic_vector(3 downto 0);
   signal mi_phy_mdio_drd    : std_logic_vector(31 downto 0);
   signal mi_phy_mdio_ardy   : std_logic;
   signal mi_phy_mdio_drdy   : std_logic;

   signal mi_id_dwr     : std_logic_vector(31 downto 0);
   signal mi_id_addr    : std_logic_vector(31 downto 0);
   signal mi_id_rd      : std_logic;
   signal mi_id_wr      : std_logic;
   signal mi_id_be      : std_logic_vector( 3 downto 0);
   signal mi_id_drd     : std_logic_vector(31 downto 0);
   signal mi_id_ardy    : std_logic;
   signal mi_id_drdy    : std_logic;

   -- Misc
   signal empty_sig  : std_logic_vector(30 downto 0);
   signal sw_reset   : std_logic;

   -- Clocks
   signal clk125        : std_logic;
   signal clk100        : std_logic;
   signal clk250        : std_logic;
   signal clk62_5       : std_logic;
   signal clk200        : std_logic;
   signal clk166        : std_logic;

   signal clk_ics       : std_logic;
   signal clk_user0     : std_logic;
   signal clk_user1     : std_logic;
   signal clk_user2     : std_logic;
   signal clk_user3     : std_logic;
   signal clk_user4     : std_logic;

   signal clkgen_locked : std_logic;

   -- One reset for each clock domain
      -- Register resets once
   signal reg_reset125 : std_logic;
   signal reg_reset100 : std_logic;
   signal reg_reset250 : std_logic;
   signal reg_reset62_5: std_logic;
   signal reg_reset200 : std_logic;
   signal reg_reset166 : std_logic;

   signal reg_reset_ics: std_logic;
   signal reg_reset_user0:std_logic;
   signal reg_reset_user1:std_logic;
   signal reg_reset_user2:std_logic;
   signal reg_reset_user3:std_logic;
   signal reg_reset_user4:std_logic;
      -- Register them for the second time
   signal reset125 : std_logic;
   signal reset100 : std_logic;
   signal reset250 : std_logic;
   signal reset62_5: std_logic;
   signal reset200 : std_logic;
   signal reset166 : std_logic;

   signal reset_ics: std_logic;
   signal reset_user0:std_logic;
   signal reset_user1:std_logic;
   signal reset_user2:std_logic;
   signal reset_user3:std_logic;
   signal reset_user4:std_logic;

   -- Additional resets for ptm_clk and combov2_ref_clk
   signal combov2_ref_reset     : std_logic; 
   signal reg_combov2_ref_reset : std_logic; 
   signal ptm_precise_reset     : std_logic;
   signal reg_ptm_precise_reset : std_logic;

   -- Interrupt and alarm signals
   signal sysmon_alarm  : std_logic;
   signal core_interrupt : std_logic_vector(31 downto 0);
   signal core_intr_rdy  : std_logic;

   -- MDIO signals

   signal mdioa_o    : std_logic;
   signal mdioa_oe   : std_logic;
   signal mdiob_o    : std_logic;
   signal mdiob_oe   : std_logic;

   -- -------------------------------------------------------------------------
   --                         Timestamps data
   -- -------------------------------------------------------------------------
   signal ts                    : std_logic_vector(63 downto 0);
   signal ts_ns                 : std_logic_vector(63 downto 0);
   signal ts_dv                 : std_logic;
   signal ts_clk                : std_logic;

      -- Keep these signals in the design in XST (constraints are applied
      -- to them)
   attribute keep : string;
   attribute keep of reg_reset125 : signal is "TRUE";
   attribute keep of reg_reset100 : signal is "TRUE";
   attribute keep of reg_reset250: signal is "TRUE";
   attribute keep of reg_reset62_5 : signal is "TRUE";
   attribute keep of reg_reset200: signal is "TRUE";
   attribute keep of reg_reset166: signal is "TRUE";
   attribute keep of reg_reset_ics : signal is "TRUE";
   attribute keep of reg_reset_user0 : signal is "TRUE";
   attribute keep of reg_reset_user1 : signal is "TRUE";
   attribute keep of reg_reset_user2 : signal is "TRUE";
   attribute keep of reg_reset_user3 : signal is "TRUE";
   attribute keep of reg_reset_user4 : signal is "TRUE";
   attribute keep of clk_ics : signal is "TRUE";

   signal sig_ib_up_data : std_logic_vector(63 downto 0);
   signal sig_ib_up_sop_n : std_logic;
   signal sig_ib_up_eop_n : std_logic;
   signal sig_ib_up_src_rdy_n : std_logic;
   signal sig_ib_up_dst_rdy_n : std_logic;
   signal sig_ib_down_data : std_logic_vector(63 downto 0);
   signal sig_ib_down_sop_n : std_logic;
   signal sig_ib_down_eop_n : std_logic;
   signal sig_ib_down_src_rdy_n : std_logic;
   signal sig_ib_down_dst_rdy_n : std_logic;


begin

   -- -------------------------------------------------------------------------
   --                                 CLK_GEN
   -- -------------------------------------------------------------------------

   clk_gen_i : entity work.CLK_GEN_CV2
   generic map(
      INPUT_IS_125   => true,          -- means that input frequency is 125 MHz (false = 250MHz)

      CLK_MULT       => CLK_MULT,
      CLK_ICS_DIV    => CLK_ICS_DIV,   -- Constants from combov2_user_const
      CLK_USER0_DIV  => CLK_USER0_DIV,
      CLK_USER1_DIV  => CLK_USER1_DIV,
      CLK_USER2_DIV  => CLK_USER2_DIV,
      CLK_USER3_DIV  => CLK_USER3_DIV,
      CLK_USER4_DIV  => CLK_USER4_DIV
   )
   port map(
      CLK_IN            => USER_CLK,   -- Confusing naming - this is clock
      RESET             => RESET,      -- from XCLK2 @ 125 MHz

      CLK125_OUT        => clk125,
      CLK100_OUT        => clk100,
      CLK250_OUT        => clk250,
      CLK62_5_OUT       => clk62_5,
      CLK200_OUT        => clk200,
      CLK166_OUT        => clk166,

      CLK_ICS_OUT       => clk_ics,
      CLK_USER0_OUT     => clk_user0,
      CLK_USER1_OUT     => clk_user1,
      CLK_USER2_OUT     => clk_user2,
      CLK_USER3_OUT     => clk_user3,
      CLK_USER4_OUT     => clk_user4,

      LOCK              => clkgen_locked
   );

   -- -------------------------------------------------------------------------
   --                       Reset logic and synchronization
   -- -------------------------------------------------------------------------

   reset125_p : process(clk125)
   begin
      if clk125'event and clk125 = '1' then
         reset125 <= reg_reset125;
         reg_reset125 <= RESET or not clkgen_locked;
      end if;
   end process;
   reset100_p : process(clk100)
   begin
      if clk100'event and clk100 = '1' then
         reset100 <= reg_reset100;
         reg_reset100 <= RESET or not clkgen_locked;
      end if;
   end process;
   reset250_p : process(clk250)
   begin
      if clk250'event and clk250 = '1' then
         reset250 <= reg_reset250;
         reg_reset250 <= RESET or not clkgen_locked;
      end if;
   end process;
   reset62_5_p : process(clk62_5)
   begin
      if clk62_5'event and clk62_5 = '1' then
         reset62_5 <= reg_reset62_5;
         reg_reset62_5 <= RESET or not clkgen_locked;
      end if;
   end process;
   reset200_p : process(clk200)
   begin
      if clk200'event and clk200 = '1' then
         reset200 <= reg_reset200;
         reg_reset200 <= RESET or not clkgen_locked;
      end if;
   end process;
   reset166_p : process(clk166)
   begin
      if clk166'event and clk166 = '1' then
         reset166 <= reg_reset166;
         reg_reset166 <= RESET or not clkgen_locked;
      end if;
   end process;
   reset_ics_p : process(clk_ics)
   begin
      if clk_ics'event and clk_ics = '1' then
         reset_ics <= reg_reset_ics;
         reg_reset_ics <= RESET or not clkgen_locked;
      end if;
   end process;
   reset_user0_p : process(clk_user0)
   begin
      if clk_user0'event and clk_user0 = '1' then
         reset_user0 <= reg_reset_user0;
         reg_reset_user0 <= RESET or not clkgen_locked;
      end if;
   end process;
   reset_user1_p : process(clk_user1)
   begin
      if clk_user1'event and clk_user1 = '1' then
         reset_user1 <= reg_reset_user1;
         reg_reset_user1 <= RESET or not clkgen_locked;
      end if;
   end process;
   reset_user2_p : process(clk_user2)
   begin
      if clk_user2'event and clk_user2 = '1' then
         reset_user2 <= reg_reset_user2;
         reg_reset_user2 <= RESET or not clkgen_locked;
      end if;
   end process;
   reset_user3_p : process(clk_user3)
   begin
      if clk_user3'event and clk_user3 = '1' then
         reset_user3 <= reg_reset_user3;
         reg_reset_user3 <= RESET or not clkgen_locked;
      end if;
   end process;
   reset_user4_p : process(clk_user4)
   begin
      if clk_user4'event and clk_user4 = '1' then
         reset_user4 <= reg_reset_user4;
         reg_reset_user4 <= RESET or not clkgen_locked;
      end if;
   end process;

   IB_RST <= reset_ics;
   IB_CLK <= clk_ics;

   CLK_125 <= clk125;
   RESET_125 <= reset125;
   -- -------------------------------------------------------------------------
   --                                  ID32
   -- -------------------------------------------------------------------------
   -- ID component
   ID32_I: entity work.ID_COMP_MI32_NOREC
      generic map(
         PROJECT_ID     => ID_PROJECT,
         SW_MAJOR       => ID_SW_MAJOR,
         SW_MINOR       => ID_SW_MINOR,
         HW_MAJOR       => ID_HW_MAJOR,
         HW_MINOR       => ID_HW_MINOR,
         PROJECT_TEXT   => ID_PROJECT_TEXT,
         TX_CHANNELS    => ID_TX_CHANNELS,
         RX_CHANNELS    => ID_RX_CHANNELS,
         SYSMON_EN      => true,       -- Can be used for Virtex5 chips
         NETCOPE_MAJOR  => NETCOPE_MAJOR,-- Constants from combov2_pkg
         NETCOPE_MINOR  => NETCOPE_MINOR,
         BUILD_TIME     => BUILD_TIME, -- Generics of combov2_netcope entity
         BUILD_UID      => BUILD_UID,
         ICS_FREQUENCY  => conv_std_logic_vector((62 * conv_integer(CLK_MULT) / conv_integer(CLK_ICS_DIV)), 16),
         INTERRUPT_IGNORE=>X"00FF",
         USER_GENERIC0  => USER_GENERIC0,
         USER_GENERIC1  => USER_GENERIC1,
         USER_GENERIC2  => USER_GENERIC2,
         USER_GENERIC3  => USER_GENERIC3
      )
      port map(
         -- ID component interface
         CLK                  => clk_ics,
         RESET                => reset_ics,
         COMMAND(0)           => sw_reset,
         COMMAND(31 downto 1) => empty_sig,
         STATUS               => X"00000000000000000000000000000000",
         WE                   => "1111",
         MI_DWR  => mi_id_dwr,
         MI_ADDR => mi_id_addr,
         MI_RD   => mi_id_rd,
         MI_WR   => mi_id_wr,
         MI_BE   => mi_id_be,
         MI_DRD  => mi_id_drd,
         MI_ARDY => mi_id_ardy,
         MI_DRDY => mi_id_drdy,

         SYSMON_ALARM         => sysmon_alarm,
         INTERRUPT_IN         => core_interrupt,
         INTR_RDY_IN          => core_intr_rdy,
         INTERRUPT_OUT        => INTERRUPT,
         INTR_DATA_OUT        => INTR_DATA,
         INTR_RDY_OUT         => INTR_RDY
      );

      IB_UP_DATA        <= sig_ib_up_data;
      IB_UP_SOP_N       <= sig_ib_up_sop_n;
      IB_UP_EOP_N       <= sig_ib_up_eop_n;
      IB_UP_SRC_RDY_N   <= sig_ib_up_src_rdy_n;
      sig_ib_up_dst_rdy_n   <= IB_UP_DST_RDY_N;
      sig_ib_down_data      <= IB_DOWN_DATA;
      sig_ib_down_sop_n     <= IB_DOWN_SOP_N;
      sig_ib_down_eop_n     <= IB_DOWN_EOP_N;
      sig_ib_down_src_rdy_n <= IB_DOWN_SRC_RDY_N;
      IB_DOWN_DST_RDY_N <= sig_ib_down_dst_rdy_n;


   -- -------------------------------------------------------------------------
   --                         INTERCONNECTION SYSTEM 
   -- -------------------------------------------------------------------------
   netcope_i : netcope_ics
   port map(
      -- ----------------------------------------------------------------------
      -- CLOCKs and RESET
      -- ----------------------------------------------------------------------
      -- CLK:
      CLK               => clk_ics,
      -- reset
      RESET             => reset_ics,
      
      -- Internal Bus CV2_PCI <-> NETCOPE_BASE
      PCI_IB_DOWN_DATA        => sig_ib_down_data,
      PCI_IB_DOWN_SOP_N       => sig_ib_down_sop_n,
      PCI_IB_DOWN_EOP_N       => sig_ib_down_eop_n,
      PCI_IB_DOWN_SRC_RDY_N   => sig_ib_down_src_rdy_n,
      PCI_IB_DOWN_DST_RDY_N   => sig_ib_down_dst_rdy_n,
      PCI_IB_UP_DATA          => sig_ib_up_data,
      PCI_IB_UP_SOP_N         => sig_ib_up_sop_n,
      PCI_IB_UP_EOP_N         => sig_ib_up_eop_n,
      PCI_IB_UP_SRC_RDY_N     => sig_ib_up_src_rdy_n,
      PCI_IB_UP_DST_RDY_N     => sig_ib_up_dst_rdy_n,

      -- Internal Bus NETCOPE_BASE <-> COMBOV2_CORE
      USER_IB64_DOWN_DATA       => ib_user_down_data,
      USER_IB64_DOWN_SOF_N      => ib_user_down_sof_n,
      USER_IB64_DOWN_EOF_N      => ib_user_down_eof_n,
      USER_IB64_DOWN_SRC_RDY_N  => ib_user_down_src_rdy_n,
      USER_IB64_DOWN_DST_RDY_N  => ib_user_down_dst_rdy_n,
      USER_IB64_UP_DATA         => ib_user_up_data,
      USER_IB64_UP_SOF_N        => ib_user_up_sof_n,
      USER_IB64_UP_EOF_N        => ib_user_up_eof_n,
      USER_IB64_UP_SRC_RDY_N    => ib_user_up_src_rdy_n,
      USER_IB64_UP_DST_RDY_N    => ib_user_up_dst_rdy_n,
      
      -- MI32 interface NETCOPE_BASE <-> COMBOV2_CORE - Application
      USER_MI32_DWR   => mi_user_dwr,
      USER_MI32_ADDR  => mi_user_addr,
      USER_MI32_RD    => mi_user_rd,
      USER_MI32_WR    => mi_user_wr,
      USER_MI32_BE    => mi_user_be,
      USER_MI32_DRD   => mi_user_drd,
      USER_MI32_ARDY  => mi_user_ardy,
      USER_MI32_DRDY  => mi_user_drdy,
      
      -- MI32 interface NETCOPE_BASE <-> COMBOV2_CORE - DMA module
      DMA_DWR   => mi_dma_dwr,
      DMA_ADDR  => mi_dma_addr,
      DMA_RD    => mi_dma_rd,
      DMA_WR    => mi_dma_wr,
      DMA_BE    => mi_dma_be,
      DMA_DRD   => mi_dma_drd,
      DMA_ARDY  => mi_dma_ardy,
      DMA_DRDY  => mi_dma_drdy,
      
      -- MI32 interface NETCOPE_BASE <-> COMBOV2_CORE - Network module
      NET_DWR   => mi_net_dwr,
      NET_ADDR  => mi_net_addr,
      NET_RD    => mi_net_rd,
      NET_WR    => mi_net_wr,
      NET_BE    => mi_net_be,
      NET_DRD   => mi_net_drd,
      NET_ARDY  => mi_net_ardy,
      NET_DRDY  => mi_net_drdy,
      
      -- MI32 interface NETCOPE_BASE <-> TSU_CV2_MI32
      TSU_DWR   => mi_tsu_cv2_dwr,
      TSU_ADDR  => mi_tsu_cv2_addr,
      TSU_RD    => mi_tsu_cv2_rd,
      TSU_WR    => mi_tsu_cv2_wr,
      TSU_BE    => mi_tsu_cv2_be,
      TSU_DRD   => mi_tsu_cv2_drd,
      TSU_ARDY  => mi_tsu_cv2_ardy,
      TSU_DRDY  => mi_tsu_cv2_drdy,
      
      -- MI32 interface NETCOPE_BASE <-> PHYTER_I2C_MI32
      PHY_DWR   => mi_phy_mdio_dwr,
      PHY_ADDR  => mi_phy_mdio_addr,
      PHY_RD    => mi_phy_mdio_rd,
      PHY_WR    => mi_phy_mdio_wr,
      PHY_BE    => mi_phy_mdio_be,
      PHY_DRD   => mi_phy_mdio_drd,
      PHY_ARDY  => mi_phy_mdio_ardy,
      PHY_DRDY  => mi_phy_mdio_drdy,

      -- MI32 interface NETCOPE_BASE <-> ID_COMP_MI32
      ID_DWR    => mi_id_dwr,
      ID_ADDR   => mi_id_addr,
      ID_RD     => mi_id_rd,
      ID_WR     => mi_id_wr,
      ID_BE     => mi_id_be,
      ID_DRD    => mi_id_drd,
      ID_ARDY   => mi_id_ardy,
      ID_DRDY   => mi_id_drdy,
      
      -- MI32 interfaces to IFCs and LSCs (not connected)
      IFC1_DWR    => open,
      IFC1_ADDR   => open,
      IFC1_RD     => open,
      IFC1_WR     => open,
      IFC1_BE     => open,
      IFC1_DRD    => X"FFFFFFFF",
      IFC1_ARDY   => '0',  -- connected to one, so it will not stuck endpoint
      IFC1_DRDY   => '0',  -- when reading from this adress
      
      IFC2_DWR    => open,
      IFC2_ADDR   => open,
      IFC2_RD     => open,
      IFC2_WR     => open,
      IFC2_BE     => open,
      IFC2_DRD    => X"FFFFFFFF",
      IFC2_ARDY   => '0',
      IFC2_DRDY   => '0',
      
      LSC1_DWR    => open,
      LSC1_ADDR   => open,
      LSC1_RD     => open,
      LSC1_WR     => open,
      LSC1_BE     => open,
      LSC1_DRD    => X"FFFFFFFF",
      LSC1_ARDY   => '0',
      LSC1_DRDY   => '0',
      
      LSC2_DWR    => open,
      LSC2_ADDR   => open,
      LSC2_RD     => open,
      LSC2_WR     => open,
      LSC2_BE     => open,
      LSC2_DRD    => X"FFFFFFFF",
      LSC2_ARDY   => '0',
      LSC2_DRDY   => '0',
      
      LSC3_DWR    => open,
      LSC3_ADDR   => open,
      LSC3_RD     => open,
      LSC3_WR     => open,
      LSC3_BE     => open,
      LSC3_DRD    => X"FFFFFFFF",
      LSC3_ARDY   => '0',
      LSC3_DRDY   => '0',
      
      LSC4_DWR    => open,
      LSC4_ADDR   => open,
      LSC4_RD     => open,
      LSC4_WR     => open,
      LSC4_BE     => open,
      LSC4_DRD    => X"FFFFFFFF",
      LSC4_ARDY   => '0',
      LSC4_DRDY   => '0'
   );

   -- -------------------------------------------------------------------------
   --                                PHY MDIO
   -- -------------------------------------------------------------------------
   MDIO_CTRL_MI32_I : MDIO_CTRL_TOP2_MI32
   port map (
      -- Common interface
      RESET    => reset_ics,
      CLK      => clk_ics,

      -- Mdio interface
      MDCA     => MDCA,
      MDIOA_I  => MDIOA,
      MDIOA_O  => mdioa_o,
      MDIOA_OE => mdioa_oe,
      MDCB     => MDCB,
      MDIOB_I  => MDIOB,
      MDIOB_O  => mdiob_o,
      MDIOB_OE => mdiob_oe,

      -- MI32 interface
      MI_DWR   => mi_phy_mdio_dwr,
      MI_ADDR  => mi_phy_mdio_addr,
      MI_RD    => mi_phy_mdio_rd,
      MI_WR    => mi_phy_mdio_wr,
      MI_BE    => mi_phy_mdio_be,
      MI_DRD   => mi_phy_mdio_drd,
      MI_ARDY  => mi_phy_mdio_ardy,
      MI_DRDY  => mi_phy_mdio_drdy
   );

   -- Tristate signals
   MDIOA <= mdioa_o when mdioa_oe = '0' else 'Z';
   MDIOB <= mdiob_o when mdiob_oe = '0' else 'Z';

   -- -------------------------------------------------------------------------
   --                         COMBOV2 APPLICATION CORE
   -- -------------------------------------------------------------------------
   COMBOV2_CORE_I: entity work.COMBOV2_CORE
   port map(
      -- CLK:
      CLK125        => clk125,
      CLK100        => clk100,
      CLK250        => clk250,
      CLK200        => clk200,
      CLK166        => clk166,
      CLK62_5       => clk62_5,
      CLK_ICS       => clk_ics,
      CLK_USER0     => clk_user0,
      CLK_USER1     => clk_user1,
      CLK_USER2     => clk_user2,
      CLK_USER3     => clk_user3,
      CLK_USER4     => clk_user4,
      -- reset
      RESET125      => reset125,
      RESET100      => reset100,
      RESET250      => reset250,
      RESET200      => reset200,
      RESET166      => reset166,
      RESET62_5     => reset62_5,
      RESET_ICS     => reset_ics,
      RESET_USER0   => reset_user0,
      RESET_USER1   => reset_user1,
      RESET_USER2   => reset_user2,
      RESET_USER3   => reset_user3,
      RESET_USER4   => reset_user4,

      -- ----------------------------------------------------------------------
      -- XGMII interface from IFC1 (2 ports)
      -- ----------------------------------------------------------------------
      -- RX
      XGMII_RESET    => XGMII_RESET,
      XGMII_RXCLK    => XGMII_RXCLK,
      XGMII_RXD      => XGMII_RXD,
      XGMII_RXC      => XGMII_RXC,
      -- TX
      XGMII_TXCLK    => XGMII_TXCLK,
      XGMII_TXD      => XGMII_TXD,
      XGMII_TXC      => XGMII_TXC,

      -- ----------------------------------------------------------------------
      -- Interconnection system
      -- ----------------------------------------------------------------------
      -- Internal Bus
      IB_DOWN_DATA       => ib_user_down_data,
      IB_DOWN_SOF_N      => ib_user_down_sof_n,
      IB_DOWN_EOF_N      => ib_user_down_eof_n,
      IB_DOWN_SRC_RDY_N  => ib_user_down_src_rdy_n,
      IB_DOWN_DST_RDY_N  => ib_user_down_dst_rdy_n,
      IB_UP_DATA         => ib_user_up_data,
      IB_UP_SOF_N        => ib_user_up_sof_n,
      IB_UP_EOF_N        => ib_user_up_eof_n,
      IB_UP_SRC_RDY_N    => ib_user_up_src_rdy_n,
      IB_UP_DST_RDY_N    => ib_user_up_dst_rdy_n,
      
      -- MI32 to user application
      MI32_USER_DWR   => mi_user_dwr,
      MI32_USER_ADDR  => mi_user_addr,
      MI32_USER_RD    => mi_user_rd,
      MI32_USER_WR    => mi_user_wr,
      MI32_USER_BE    => mi_user_be,
      MI32_USER_DRD   => mi_user_drd,
      MI32_USER_ARDY  => mi_user_ardy,
      MI32_USER_DRDY  => mi_user_drdy,
      
      -- MI32 to DMA module
      MI32_DMA_DWR   => mi_dma_dwr,
      MI32_DMA_ADDR  => mi_dma_addr,
      MI32_DMA_RD    => mi_dma_rd,
      MI32_DMA_WR    => mi_dma_wr,
      MI32_DMA_BE    => mi_dma_be,
      MI32_DMA_DRD   => mi_dma_drd,
      MI32_DMA_ARDY  => mi_dma_ardy,
      MI32_DMA_DRDY  => mi_dma_drdy,
      
      -- MI32 to Network module
      MI32_NET_DWR   => mi_net_dwr,
      MI32_NET_ADDR  => mi_net_addr,
      MI32_NET_RD    => mi_net_rd,
      MI32_NET_WR    => mi_net_wr,
      MI32_NET_BE    => mi_net_be,
      MI32_NET_DRD   => mi_net_drd,
      MI32_NET_ARDY  => mi_net_ardy,
      MI32_NET_DRDY  => mi_net_drdy,
      
      -- Interrupt system
      INTERRUPT      => core_interrupt,
      INTR_RDY       => core_intr_rdy,
      SYSMON_ALARM   => sysmon_alarm,

      -- -------------------------------------------------------------------
      -- QDRII Memories
      -- -------------------------------------------------------------------

      -- QDRII Memory 1
         -- Data --
      S0Q            => S0Q,
      S0D            => S0D,
         -- Address --
      S0A            => S0A,
         -- Control --
      S0BWS_N        => S0BWS_N,
      S0CQ_P         => S0CQ_P,
      S0CQ_N         => S0CQ_N,
      S0K_P          => S0K_P,
      S0K_N          => S0K_N,
      S0C_P          => S0C_P,
      S0C_N          => S0C_N,
      S0WPS_N        => S0WPS_N,
      S0RPS_N        => S0RPS_N,
      S0DOFF_N       => S0DOFF_N,

      -- QDRII Memory 2
         -- Data --
      S1Q            => S1Q,
      S1D            => S1D,
         -- Address --
      S1A            => S1A,
         -- Control --
      S1BWS_N        => S1BWS_N,
      S1CQ_P         => S1CQ_P,
      S1CQ_N         => S1CQ_N,
      S1K_P          => S1K_P,
      S1K_N          => S1K_N,
      S1C_P          => S1C_P,
      S1C_N          => S1C_N,
      S1WPS_N        => S1WPS_N,
      S1RPS_N        => S1RPS_N,
      S1DOFF_N       => S1DOFF_N,

      -- ----------------------------------------------------------------------
      -- DDR2 DRAM/RLDRAM Memory
      -- ----------------------------------------------------------------------
      -- Adress --
      DA             => DA,
      -- Data --
      DDQ            => DDQ,
      -- Control --
      DDM            => DDM,
      DBA            => DBA,
      DCS_N          => DCS_N,
      DRAS_N         => DRAS_N,
      DCAS_N         => DCAS_N,
      DWE_N          => DWE_N,
      DCK0_P         => DCK0_P,
      DCK0_N         => DCK0_N,
      DCK1_P         => DCK1_P,
      DCK1_N         => DCK1_N,
      DCKE           => DCKE,
      DDODT          => DDODT,
      DSDA           => DSDA,
      DSCL           => DSCL,
      DSA            => DSA,
      DDQS_P         => DDQS_P,
      DDQS_N         => DDQS_N,

      -- ----------------------------------------------------------------------
      -- Oscillators
      -- ----------------------------------------------------------------------
      MCLK1_P        => MCLK1_P,
      MCLK1_N        => MCLK1_N,
      MCLK0_P        => MCLK0_P,
      MCLK0_N        => MCLK0_N,

      GCLK250_P      => GCLK250_P,
      GCLK250_N      => GCLK250_N,
      GCLK100_P      => GCLK100_P,
      GCLK100_N      => GCLK100_N,

      XCLK0_P        => XCLK0_P,
      XCLK0_N        => XCLK0_N,
      XCLK1_P        => XCLK1_P,
      XCLK1_N        => XCLK1_N,

      XCLK2          => XCLK2, -- Already output from IBUFGDS

      -- -------------------------------------------------------------------
      -- Serial
      -- -------------------------------------------------------------------
      FQTXD          => FQTXD,
      FQRXD          => FQRXD,

      -- -------------------------------------------------------------------
      -- LED
      -- -------------------------------------------------------------------
      IBUF_LED       => IBUF_LED,
      OBUF_LED       => OBUF_LED,
      FQLED          => FQLED,

      -- -------------------------------------------------------------------
      -- TIMESTAMPS FOR PACODAG
      -- -------------------------------------------------------------------
      TS             => ts,     -- fractional* format of timestamp
      TS_NS          => ts_ns,  -- nanosecond* format of timestamp
      TS_DV          => ts_dv,  -- data valid timestamp (determines validity of timestamp)
      TS_CLK         => ts_clk  -- clock at which are timestamps synchrounous
                                -- * more info about timestamp formats can be found here: https://www.liberouter.org/trac/netcope/wiki/format_timestamp
   );

   -- -------------------------------------------------------------------------
   --                              TS UNIT
   -- -------------------------------------------------------------------------
   -- timestamp unit is about to be generate into design
   ts_true : if TIMESTAMP_UNIT = true generate
      TS_UNIT_I : tsu_cv2
      generic map(
         -- Defines whether to use DSP's for timestamp format conversion
         TS_MULT_USE_DSP           => true, -- true = use DSP's, false = disable DSP's
         -- Application frequency in Hz
         COMBOV2_REF_CLK_FREQUENCY => COMBOV2_REF_CLK_FREQUENCY, -- frequency of combov2 clk
         PTM_PRECISE_CLK_FREQUENCY => PTM_PRECISE_CLK_FREQUENCY -- frequency of ptm precise crystal clk
      )
      port map(
         -- Combo clock and reset signals for MI_32 interface
         MI32_CLK          => clk_ics,
         MI32_RESET        => reset_ics,

         -- In / Out SW interface via MI_32
         DWR          => mi_tsu_cv2_dwr, 
         ADDR         => mi_tsu_cv2_addr,
         RD           => mi_tsu_cv2_rd,  
         WR           => mi_tsu_cv2_wr,  
         BE           => mi_tsu_cv2_be,  
         DRD          => mi_tsu_cv2_drd, 
         ARDY         => mi_tsu_cv2_ardy,
         DRDY         => mi_tsu_cv2_drdy, 

         -- Input PPS_N signal from GPS
         GPS_PPS_N        => PPS_N,

         -- -------------------------------------------
         -- TSU core clock ----------------------------
         -- -------------------------------------------
         -- COMBOv2 base clock
         COMBOV2_REF_CLK   => clk166,
         COMBOV2_REF_RESET => reset166,
         -- PTM precise crystal clock
         PTM_PRECISE_CLK   => PTM_CLK,
         PTM_PRECISE_RESET => ptm_precise_reset,

         -- Pacodag interface
	 TS           => ts,
         TS_NS        => ts_ns,
         TS_DV        => ts_dv,
         TS_CLK       => ts_clk
      );
   end generate ts_true;

   -- timestamp unit won't be generate in design
   ts_false : if TIMESTAMP_UNIT = false generate
      ts    <= X"0000000000000000";
      ts_ns <= X"0000000000000000";
      ts_dv <= '0';
      ts_clk <= clk_ics;

      mi_tsu_cv2_drd <= X"00000000";
      mi_tsu_cv2_ardy <= mi_tsu_cv2_rd or mi_tsu_cv2_wr;
      mi_tsu_cv2_drdy <= mi_tsu_cv2_rd;
   end generate ts_false;

   -- ---------------------------------------------------------------
   --           Generation of reset for TSU_CV2
   -- ---------------------------------------------------------------
   proc_ptm_precise_reset : process(PTM_CLK)
   begin
      if (PTM_CLK'event and PTM_CLK = '1') then
         ptm_precise_reset <= reg_ptm_precise_reset;
         reg_ptm_precise_reset <= reset_ics;
      end if;
   end process;


   -- Constant interface settings
   wanmodea  <= '0'; -- Disable WAN mode (enable LAN mode)
   txonoffa  <= '1'; -- Transmit enable
   autonega  <= '0'; -- Disable autonegotiation
   epcsa     <= '0'; -- Standard PCS
   rstphya_n <= '1'; -- Phyter reset
   pdowna    <= '0'; -- XFP Power down          
   txdisa    <= '0'; -- XFP TX disable                                        
   moddesela <= '0'; -- XFP mode select - must be low for i2c communication   
   --           
   wanmodeb  <= '0'; -- Disable WAN mode (enable LAN mode)
   txonoffb  <= '1'; -- Transmit enable
   autonegb  <= '0'; -- Disable autonegotiation
   epcsb     <= '0'; -- Standard PCS
   rstphyb_n <= '1'; -- Phyter reset  
   pdownb    <= '0'; -- XFP Power down          
   txdisb    <= '0'; -- XFP TX disable
   moddeselb <= '0'; -- XFP mode select - must be low for i2c communication

end architecture behavioral;
