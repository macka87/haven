-- top_level.vhd : Combov2 top level architecture for NetCOPE project
-- Copyright (C) 2008 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;
use work.combov2_nc_const.all;
use work.combov2_user_const.all;

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------
architecture structural of FPGA_U0 is
   -- ------------------ Xilinx components ------------------------------------

   -- input buffer for differencial pair
   component IBUFDS
   port (
      O  : out std_logic;
      I  : in  std_logic;
      IB : in  std_logic
   );
   end component;
  
   -- input clock buffer for differencial pair
   component IBUFGDS
   port (
      O  : out std_logic;
      I  : in  std_logic;
      IB : in  std_logic
   );
   end component;
 
   -- output buffer for differencial pair
   component OBUFDS
   port (
      OB : out std_logic;
      O  : out std_logic;
      I  : in  std_logic
   );
   end component;

   -- input buffer
   component IBUF
   port (
      O : out std_logic;
      I : in std_logic
   );
   end component;

   -- output buffer
   component OBUF
   port (
      O : out std_logic;
      I : in std_logic
   );
   end component;

   -- Clock Buffer
   component BUFG is
      port (
         I : in  std_logic;
         O : out std_logic
      );
   end component;

   component cv2_pci is
      port (
         -- PCIE core system interface -------------------------------------------
         PCIE_CLK                      : in  std_logic;     
         PCIE_RST_N                    : in  std_logic;     
         -- PCIE core lanes ------------------------------------------------------
         PCI_EXP_RXN                   : in  std_logic_vector(7 downto 0);
         PCI_EXP_RXP                   : in  std_logic_vector(7 downto 0);
         PCI_EXP_TXN                   : out std_logic_vector(7 downto 0);
         PCI_EXP_TXP                   : out std_logic_vector(7 downto 0);
         -- PCIE core TRN common interface ---------------------------------------
--          PCIE_CORE_TRN_CLK             : out std_logic;       
         PCIE_CORE_TRN_RST             : out std_logic;       
         -- Spartan common interface ---------------------------------------------
         SP_CLK                        : in  std_logic;      
         SP_RESET                      : in  std_logic;      
         -- Internal Bus common interface ----------------------------------------
         IB_CLK                        : in  std_logic;        
         IB_RST                        : in  std_logic;        
         -- Internal Bus (BAR1) downstream port ----------------------------------
         IB_DOWN_DATA                  : out std_logic_vector(63 downto 0);
         IB_DOWN_SOP_N                 : out std_logic;
         IB_DOWN_EOP_N                 : out std_logic;
         IB_DOWN_SRC_RDY_N             : out std_logic;
         IB_DOWN_DST_RDY_N             : in  std_logic;
         -- Internal Bus (BAR1) upstream port ------------------------------------
         IB_UP_DATA                    : in  std_logic_vector(63 downto 0);
         IB_UP_SOP_N                   : in  std_logic;
         IB_UP_EOP_N                   : in  std_logic;
         IB_UP_SRC_RDY_N               : in  std_logic;
         IB_UP_DST_RDY_N               : out std_logic;
         -- Interrupt interface --------------------------------------------------
         INTERRUPT                     : in  std_logic;                    
         INTR_DATA                     : in  std_logic_vector(4 downto 0); 
         INTR_RDY                      : out std_logic;                    
         -- Spartan 3 interface (internal bus BAR0) ------------------------------
         SP_TX                         : out std_logic_vector(7 downto 0);
         SP_TX_RDY                     : in  std_logic;                   
         SP_RX                         : in  std_logic_vector(7 downto 0);
--          SP_RX_RDY                     : out std_logic;                   
         SP_RST                        : out std_logic                    
   );
   end component;

   component combov2_xaui is
   port (
      -- Asynchronous reset
      RESET             : in std_logic;
      -- Clock signal for DCM circuits
      DCLK              : in std_logic;

      -- Reference 156.25 MHz clock
      REFCLK_156_P      : in std_logic;
      REFCLK_156_N      : in std_logic;
      
      -- XAUI interface (4 RX and TX differential RocketIO lanes)
      GTP_RX_P          : in  std_logic_vector( 3 downto 0 );
      GTP_RX_N          : in  std_logic_vector( 3 downto 0 );
      GTP_TX_P          : out std_logic_vector( 3 downto 0 );
      GTP_TX_N          : out std_logic_vector( 3 downto 0 );

      -- XGMII SDR interface
         -- RX
      XGMII_RXCLK          : out std_logic;
      XGMII_RXD            : out std_logic_vector(63 downto 0);
      XGMII_RXC            : out std_logic_vector( 7 downto 0);
         -- TX
      XGMII_TXCLK          : out std_logic;
      XGMII_TXD            : in  std_logic_vector(63 downto 0);
      XGMII_TXC            : in  std_logic_vector( 7 downto 0)
   );
   end component;

   -- ------------------ Constants declaration --------------------------------

   -- ------------------ Signals declaration ----------------------------------
   -- Clocks & resets

   signal sys_clk          : std_logic;   -- Output from IBUFDS - 250 MHz
   signal pcie_core_trn_clk: std_logic;   -- Output from cv2_pci
   signal pcie_core_trn_rst: std_logic;   -- Output from cv2_pci
   signal reg_reset        : std_logic;   --    Registered once
   signal reset            : std_logic;   --    Registered twice
   signal xclk2_125        : std_logic;   -- xclk2 clk @ 125 MHz

   constant USE_XCLK2   : boolean := true; -- For main_clk setting
   signal main_clk      : std_logic;   -- xclk2 or pcie_core_trn_clk

   signal clk_ics       : std_logic;   -- Output from NetCOPE - configurable
   signal ics_rst       : std_logic;   -- Output from NetCOPE

   signal clk_125       : std_logic;   -- Output from NetCOPE - 125 MHz
   signal reset_125     : std_logic;   -- Output from NetCOPE

   -- ICS
   signal ib_down_data        : std_logic_vector(63 downto 0);
   signal ib_down_sop_n       : std_logic;
   signal ib_down_eop_n       : std_logic;
   signal ib_down_src_rdy_n   : std_logic;
   signal ib_down_dst_rdy_n   : std_logic;
   signal ib_up_data          : std_logic_vector(63 downto 0);
   signal ib_up_sop_n         : std_logic;
   signal ib_up_eop_n         : std_logic;
   signal ib_up_src_rdy_n     : std_logic;
   signal ib_up_dst_rdy_n     : std_logic;

   signal interrupt     : std_logic;
   signal intr_data     : std_logic_vector(4 downto 0);
   signal intr_data_mux     : std_logic_vector(4 downto 0);
   signal intr_rdy      : std_logic;

   -- XGMII signals
   signal xgmii_reset_f : std_logic_vector(  1 downto 0);
   signal xgmii_rxclk_f : std_logic_vector(  1 downto 0);
   signal xgmii_rxd_f   : std_logic_vector(127 downto 0);
   signal xgmii_rxc_f   : std_logic_vector( 15 downto 0);
   signal xgmii_txclk_f : std_logic_vector(  1 downto 0);
   signal xgmii_txd_f   : std_logic_vector(127 downto 0);
   signal xgmii_txc_f   : std_logic_vector( 15 downto 0);
   
   -- Interfaces control signals (constant values)
   signal wanmodea      : std_logic;
   signal txonoffa      : std_logic;
   signal autonega      : std_logic;
   signal pdowna        : std_logic;
   signal epcsa         : std_logic;
   signal txdisa        : std_logic;
   signal moddesela     : std_logic;
   signal rstphya_n     : std_logic;
   signal wanmodeb      : std_logic;
   signal txonoffb      : std_logic;
   signal autonegb      : std_logic;
   signal pdownb        : std_logic;
   signal epcsb         : std_logic;
   signal txdisb        : std_logic;
   signal moddeselb     : std_logic;
   signal rstphyb_n     : std_logic;

   -- LED diods
   signal ibuf_led      : std_logic_vector(1 downto 0);
   signal obuf_led      : std_logic_vector(1 downto 0);

   -- PPS
   signal pps_n         : std_logic;
   -- CLK signal from PTM precise crystal
   signal to_bufg_ptm_clk : std_logic;
   signal ptm_clk       : std_logic;

   -- XST attributes to prevent optimization
   attribute keep : string;
   attribute keep of pcie_core_trn_rst : signal is "true"; 
   attribute keep of pcie_core_trn_clk : signal is "true";
   attribute keep of xclk2_125  : signal is "true";

   -- XST attributes to prevent automatic BUFG insertion
   attribute buffer_type:string;
   attribute buffer_type of xclk2_125:signal is "none";
   attribute buffer_type of pcie_core_trn_clk:signal is "none";
   attribute buffer_type of clk_ics:signal is "none";
   attribute buffer_type of clk_125:signal is "none";

   attribute buffer_type of PCLK0_N:signal is "none";
   attribute buffer_type of PCLK0_P:signal is "none";
   attribute buffer_type of PCLK1_N:signal is "none";
   attribute buffer_type of PCLK1_P:signal is "none";

begin

   -- -------------------------------------------------------------------------
   --                            CLOCKS AND RESETS
   -- -------------------------------------------------------------------------
   
   PCIE_REFCLK_IBUF : IBUFDS
   port map (
      O  => sys_clk,   -- Buffer output
      I  => PCLK250_P, -- Diff_p buffer input
      IB => PCLK250_N  -- Diff_n buffer input
   );

   -- -----------------------------------------------------------------------
   -- Connection XCLK2 differential clock signal
   XCLK2_IBUFGDS : IBUFGDS
   port map(
      O  => xclk2_125,
      I  => XCLK2_P,
      IB => XCLK2_N
   );

   -- -------------------------------------------------------------------------
   --                         PCIE to IB TOP LEVEL                           --
   -- ------------------------------------------------------------------------- 

   PCI_SYSTEM : cv2_pci
   port map (
      PCIE_CLK    => sys_clk,
      PCIE_RST_N  => XHSH(10),

      PCI_EXP_RXP => PER_P,
      PCI_EXP_RXN => PER_N,
      PCI_EXP_TXP => PET_P,
      PCI_EXP_TXN => PET_N,

      -- pcie core trn clock
--       PCIE_CORE_TRN_CLK  => pcie_core_trn_clk,
      PCIE_CORE_TRN_RST  => pcie_core_trn_rst,

      -- Spartan interface clock
      SP_RESET    => reset_125,
      SP_CLK      => clk_125,

      -- Internal Bus Common
      IB_RST            => ics_rst,
      IB_CLK            => clk_ics,
      -- Internal Bus down
      IB_DOWN_DATA      => ib_down_data,
      IB_DOWN_SOP_N     => ib_down_sop_n,
      IB_DOWN_EOP_N     => ib_down_eop_n,
      IB_DOWN_SRC_RDY_N => ib_down_src_rdy_n,
      IB_DOWN_DST_RDY_N => ib_down_dst_rdy_n,
      -- Internal Bus up
      IB_UP_DATA        => ib_up_data,
      IB_UP_SOP_N       => ib_up_sop_n,
      IB_UP_EOP_N       => ib_up_eop_n,
      IB_UP_SRC_RDY_N   => ib_up_src_rdy_n,
      IB_UP_DST_RDY_N   => ib_up_dst_rdy_n,

      -- Interrupt system
      INTERRUPT   => interrupt, -- Interrupt, 1 cycle pulse, valid in '1'
      INTR_DATA   => intr_data_mux, -- MSI vector data
      INTR_RDY    => intr_rdy,

      -- Spartan3 interface (internal bus)
      SP_TX       => XD(7 downto 0),
      SP_TX_RDY   => XHSH(0),
      SP_RX       => XHSH(8 downto 1),
--       SP_RX_RDY   => XHSH(9),  
      SP_RST      => XHSH(11)
   );
    
   -- Spartan is always ready
   XHSH(9) <= '0'; --!!!!

   -- because of partitions (which do not allow constant inputs)
   -- interrupt data are in reset state set to all '1'.
   -- This prevents from optimizing out of some
   -- not used data signals. Be carefull, becouse all '0' willl
   -- be optimized out!  
   INTR_DATA_MUX_P: process (intr_data, ics_rst) 
    begin 
      case ics_rst is  
        when '1'     => intr_data_mux <= "11111";  
        when '0'     => intr_data_mux <= intr_data;  
        when others  => intr_data_mux <= "00000";  
      end case;  
    end process INTR_DATA_MUX_P;


      -- only allowed clocks
--    use_xclk2_gen : if USE_XCLK2 = true generate
      main_clk <= xclk2_125;
--    end generate;

--    use_pcie_core_trn_clk_gen : if USE_XCLK2 = false generate
--       main_clk <= pcie_core_trn_clk;
--    end generate;

   reset_p : process(main_clk)
   begin
      if main_clk'event and main_clk = '1' then
         reset <= reg_reset;
         reg_reset <= pcie_core_trn_rst;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                              XAUI core                                 --
   -- ------------------------------------------------------------------------- 
   XAUI_CORE0_I : combov2_xaui
   port map(
      RESET             => reset_125,
      -- Clock signal for DCM circuits
      DCLK              => clk_125,

      -- Reference 156.25 MHz clock
      REFCLK_156_P      => PCLK0_P,
      REFCLK_156_N      => PCLK0_N,

      -- XAUI interface (4 RX and TX differential RocketIO lanes)
      GTP_RX_P         => GT1R_P,
      GTP_RX_N         => GT1R_N,
      GTP_TX_P         => GT1T_P,
      GTP_TX_N         => GT1T_N,

      -- XGMII SDR interface
         -- RX
      XGMII_RXCLK      => xgmii_rxclk_f(0),
      XGMII_RXD        => xgmii_rxd_f(63 downto 0),
      XGMII_RXC        => xgmii_rxc_f( 7 downto 0),
         -- TX
      XGMII_TXCLK      => xgmii_txclk_f(0),
      XGMII_TXD        => xgmii_txd_f(63 downto 0),
      XGMII_TXC        => xgmii_txc_f( 7 downto 0)
   );

   XAUI_CORE1_I : combov2_xaui
   port map(
      RESET             => reset_125,
      -- Clock signal for DCM circuits
      DCLK              => clk_125,

      -- Reference 156.25 MHz clock
      REFCLK_156_P      => PCLK1_P,
      REFCLK_156_N      => PCLK1_N,

      -- XAUI interface (4 RX and TX differential RocketIO lanes)
      GTP_RX_P          => GT2R_P,
      GTP_RX_N          => GT2R_N,
      GTP_TX_P          => GT2T_P,
      GTP_TX_N          => GT2T_N,

      -- XGMII SDR interface
         -- RX
      XGMII_RXCLK      => xgmii_rxclk_f(1),
      XGMII_RXD        => xgmii_rxd_f(127 downto 64),
      XGMII_RXC        => xgmii_rxc_f( 15 downto 8),
         -- TX
      XGMII_TXCLK      => xgmii_txclk_f(1),
      XGMII_TXD        => xgmii_txd_f(127 downto 64),
      XGMII_TXC        => xgmii_txc_f( 15 downto 8)
   );

   xgmii_reset_f     <= reset_125 & reset_125;

   -- -------------------------------------------------------------------------
   --                            COMBOv2 NetCOPE
   -- -------------------------------------------------------------------------
   COMBOV2_NETCOPE_I : entity work.COMBOV2_NETCOPE
      generic map(
         BUILD_TIME      => BUILD_TIME, -- Toplevel's generics
         BUILD_UID       => BUILD_UID,
         USER_GENERIC0   => USER_GENERIC0,
         USER_GENERIC1   => USER_GENERIC1,
         USER_GENERIC2   => USER_GENERIC2,
         USER_GENERIC3   => USER_GENERIC3
      )
      port map(
         -- CLOCKs and RESET
         USER_CLK       => main_clk,
         -- reset
         RESET          => reset,

         -- 125 MHz clock (for Spartan and XAUI)
         CLK_125        => clk_125,
         RESET_125      => reset_125,

         -- IFC connectors
         XGMII_RESET    => xgmii_reset_f,
         XGMII_RXCLK    => xgmii_rxclk_f,
         XGMII_RXD      => xgmii_rxd_f,
         XGMII_RXC      => xgmii_rxc_f,
         -- TX
         XGMII_TXCLK    => xgmii_txclk_f,
         XGMII_TXD      => xgmii_txd_f,
         XGMII_TXC      => xgmii_txc_f,

         -- Mdio interface
         -- MDCA <=> A33 <=> IF1_1D2_P
         -- MDIOA <=> A34 <=> IF1_1D2_N
         MDCA           => IF1_1D_P(2),
         MDIOA          => IF1_1D_N(2),
         MDCB           => IF2_1D_P(2),
         MDIOB          => IF2_1D_N(2),

         -- -------------------------------------------------------------------
         -- Interconnection system
         -- -------------------------------------------------------------------
         -- Internal Bus
         IB_CLK         => clk_ics,
         IB_RST         => ics_rst,

       	 IB_DOWN_DATA   => ib_down_data,
      	 IB_DOWN_SOP_N  => ib_down_sop_n,
      	 IB_DOWN_EOP_N  => ib_down_eop_n,
      	 IB_DOWN_SRC_RDY_N=> ib_down_src_rdy_n,
      	 IB_DOWN_DST_RDY_N=> ib_down_dst_rdy_n,

      	 IB_UP_DATA     => ib_up_data,
      	 IB_UP_SOP_N    => ib_up_sop_n,
      	 IB_UP_EOP_N    => ib_up_eop_n,
      	 IB_UP_SRC_RDY_N=> ib_up_src_rdy_n,
      	 IB_UP_DST_RDY_N=> ib_up_dst_rdy_n,
         -- Interrupt system
         INTERRUPT   => interrupt, -- Interrupt, 1 cycle pulse, valid in '1'
         INTR_DATA   => intr_data, -- MSI vector data
         INTR_RDY    => intr_rdy,

         -- -------------------------------------------------------------------
         -- QDRII Memories
         -- -------------------------------------------------------------------

         -- QDRII Memory 1
            -- Data --
         S0Q            => S0Q,
         S0D            => S0D,
            -- Address --     -- Ad
         S0A            => S0A,
            -- Control --     -- Co
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
                                   
         -- QDRII Memory 2 -- QDRII
            -- Data --        -- Da
         S1Q            => S1Q,
         S1D            => S1D,
            -- Address --     -- Ad
         S1A            => S1A,
            -- Control --     -- Co
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

         wanmodea       => wanmodea,
         txonoffa       => txonoffa,
         autonega       => autonega,
         pdowna         => pdowna,
         epcsa          => epcsa,
         txdisa         => txdisa,
         moddesela      => moddesela,
         rstphya_n      => rstphya_n,
         wanmodeb       => wanmodeb,
         txonoffb       => txonoffb,
         autonegb       => autonegb,
         pdownb         => pdownb,
         epcsb          => epcsb,
         txdisb         => txdisb,
         moddeselb      => moddeselb,
         rstphyb_n      => rstphyb_n,

         -- -------------------------------------------------------------------
         -- DDR2 DRAM/RLDRAM Memory
         -- -------------------------------------------------------------------
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

         -- -------------------------------------------------------------------
         -- Oscillators
         -- -------------------------------------------------------------------
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

         XCLK2		=> xclk2_125, -- Already output from IBUFGDS

         -- -------------------------------------------------------------------
         -- Serial
         -- -------------------------------------------------------------------
         FQTXD          => FQTXD,
         FQRXD          => FQRXD,

         -- -------------------------------------------------------------------
         -- LED
         -- -------------------------------------------------------------------
         IBUF_LED       => ibuf_led,
         OBUF_LED       => obuf_led,
         FQLED          => FQLED,

         -- -------------------------------------------------------------------
         -- PPS signal from PTM card with GPS
         -- -------------------------------------------------------------------
         PPS_N          => pps_n,

         -- -------------------------------------------------------------------
         -- CLK signal from PTM card precise crystal
         -- -------------------------------------------------------------------
         PTM_CLK        => ptm_clk
      );

      IF1_1D_N(14) <= wanmodea;
      IF1_1D_P(14) <= txonoffa;
      IF1_1D_N(16) <= autonega;
      IF1_1D_P(16) <= epcsa;
      IF1_1D_P(9)  <= txdisa;
      IF1_1D_N(9)  <= pdowna;
      IF1_1D_P(13) <= moddesela;
      IF1_1D_P(15) <= rstphya_n;
      IF2_1D_N(14) <= wanmodeb;
      IF2_1D_P(14) <= txonoffb;
      IF2_1D_N(16) <= autonegb;
      IF2_1D_P(16) <= epcsb;
      IF2_1D_P(9)  <= txdisb;
      IF2_1D_N(9)  <= pdownb;
      IF2_1D_P(13) <= moddeselb;
      IF2_1D_P(15) <= rstphyb_n;
      IF1_1D_P(17) <= ibuf_led(0);
      IF1_1D_N(17) <= obuf_led(0);
      IF2_1D_P(17) <= ibuf_led(1);
      IF2_1D_N(17) <= obuf_led(1);

   -- -----------------------------------------------------------------------
   -- Connection via LSC3 to a PTM card with a GPS module
   -- T => '1' means input from IO to O signal
   -- T => '0' means output from I to IO signal
   -- -----------------------------------------------------------------------
      IOBUF_LSC3_D3_N : IOBUF		-- pps_n <= LSC3_D3_N;
      port map (
         O => pps_n,
         IO => LSC3_D_N(3),			-- PA_RX1    --> RxDO1/RA1
         I => '0',
         T => '1'
      );

      IOBUF_LSC3_D7_P : IOBUF		-- LSC3_D7_P <= LSC3_D3_N;
      port map (
         O => open,
         IO => LSC3_D_P(7),			-- RJ45_LED1
         I => pps_n,
         T => '0'
      );

      IOBUF_LSC3_D0_P : IOBUF		-- LSC3_D0_P <= '1';
      port map (
         O => open,
         IO => LSC3_D_P(0),			-- PA_MODE   --> LB
         I => '1',
         T => '0'
      );

      IOBUF_LSC3_D0_N : IOBUF		-- LSC3_D0_N <= '1';
      port map (
         O => open,
         IO => LSC3_D_N(0),			-- PB_TX1    --> ON/OFF
         I => '1',
         T => '0'
      );

      IOBUF_LSC3_D2_N : IOBUF		-- LSC3_D2_N <= '0';
      port map (
         O => open,
         IO => LSC3_D_N(2),			-- PB_MODE   --> SEL2
         I => '0',
         T => '0'
      );

      IOBUF_LSC3_D4_P : IOBUF		-- LSC3_D4_P <= '0';
      port map (
         O => open,
         IO => LSC3_D_P(4),			-- CNTRL1    --> SEL1
         I => '0',
         T => '0'
      );

      IOBUFDS_LSC3_D8 : IBUFDS         -- clk signal from ptm card precise crystal
      port map(
         O  => to_bufg_ptm_clk,
         I => LSC3_D_P(8),		-- CLK_PLL_P
         IB=> LSC3_D_N(8)		-- CLK_PLL_N
      );

      -- Clock Buffer for PTM_CLK
      BUFG_CLK_PLL : BUFG
      port map (
         I  => to_bufg_ptm_clk,
         O  => ptm_clk
      );

    -- rest of LSC3 is unnecessary, here is shown how it is mapped to COMBOL-GPS card

    IOBUFDS_LSC3_D1 : IOBUFDS
    port map(
       O  => open,
       IO => LSC3_D_P(1),		-- PA_TX1    --> TxD1/DY1
       IOB=> LSC3_D_N(1),		-- PA_TX2/EN --> TxDE1/DZ1
       I  => '1',
       T  => '0'
    );

    IOBUF_LSC3_D2_P : IOBUF
    port map(
       O  => open,
       IO => LSC3_D_P(2),		-- PB_TX2/EN --> TxD2/DY2
       I  => '1',
       T  => '0'
    );

    IOBUF_LSC3_D3_P : IOBUF
    port map(
       O  => open,
       IO => LSC3_D_P(3),		-- PB_RX2    --> RB2
       I  => '1',
       T  => '1'
    );

    IOBUF_LSC3_D4_N : IOBUF
    port map(
       O  => open,
       IO => LSC3_D_N(4),		-- CNTRL2    --> TxDE2/DZ2
       I  => '1',
       T  => '0'
    );

    IOBUFDS_LSC3_D5 : IOBUFDS
    port map(
       O  => open,
       IO => LSC3_D_P(5),		-- PA_RX2    --> RB1
       IOB=> LSC3_D_N(5),		-- PB_RX1    --> RxDO2/RA2
       I  => '1',
       T  => '1'
    );

    IOBUFDS_LSC3_D6 : IOBUFDS
    port map(
       O  => open,
       IO => LSC3_D_P(6),		-- CLK_BUF_P
       IOB=> LSC3_D_N(6),		-- CLK_BUF_N
       I  => '1',
       T  => '1'
    );

    IOBUF_LSC3_D7_N : IOBUF
    port map(
       O  => open,
       IO => LSC3_D_N(7),		-- RJ45_LED2
       I  => '1',
       T  => '0'
    );

    IOBUFDS_LSC3_D9 : IOBUFDS
    port map(
       O  => open,
       IO => LSC3_D_P(9),		-- AUX_LED1
       IOB=> LSC3_D_N(9),		-- AUX_LED2
       I  => '1',
       T  => '0'
    );

    IOBUFDS_LSC3_D10 : IOBUFDS
    port map(
       O  => open,
       IO => LSC3_D_P(10),		-- I2C IO1_VL
       IOB=> LSC3_D_N(10),		-- I2C IO1_VL
       I  => '1',
       T  => '0'
    );

   -- -----------------------------------------------------------------------
   -- These signals are unused in this combination of cards
   -- -----------------------------------------------------------------------
   lsc1_gen : for i in 0 to 17 generate
      LSC1_OBUFDS : OBUFDS
      port map(
         O  => LSC1_D_P(i),
         OB => LSC1_D_N(i),
         I  => '1'
      );
   end generate;
   lsc2_gen : for i in 0 to 17 generate
      LSC2_OBUFDS : OBUFDS
      port map(
         O  => LSC2_D_P(i),
         OB => LSC2_D_N(i),
         I  => '1'
      );
   end generate;

   lsc4_gen : for i in 0 to 10 generate
      LSC4_OBUFDS : OBUFDS
      port map(
         O  => LSC4_D_P(i),
         OB => LSC4_D_N(i),
         I  => '1'
      );
   end generate;

end architecture structural;
