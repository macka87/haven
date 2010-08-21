--
-- combov2_arch.vhd : Example for NetCOPE on the Combov2 board
-- Copyright (C) 2009 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
use work.ib_pkg.all; 

-- ----------------------------------------------------------------------------
--             Architecture declaration  --  ComboLXT Top Level                 --
-- ----------------------------------------------------------------------------

architecture structural of fpga_u0 is

   component IBUFDS
      port (
         O  : out std_logic;
         I  : in  std_logic;
         IB : in  std_logic
      );
   end component;
   
   -- Resets & clocks
   signal sys_clk      : std_logic;        -- PCIE system clock
   signal reset        : std_logic;        -- Internal system reset
   -- Internal bus  
   signal ics_clk      : std_logic;        -- ICS clock 
   signal ics_reset    : std_logic;        -- ICS reset
   signal reg_ics_reset: std_logic;
   signal sp_clk       : std_logic;        -- Spartan clock
   signal sp_reset     : std_logic;        -- Spartan reset
   signal reg_sp_reset : std_logic; 
   signal pcie_core_trn_clk   : std_logic;        -- PCI Endpoint clock
   signal pcie_core_trn_rst   : std_logic;        -- PCI Endpoint reset 
   signal ib           : t_internal_bus64; -- Internal bus
   signal cntr         : std_logic_vector(25 downto 0);        -- ICS clock 
   signal lock         : std_logic;
   
   signal interrupt    : std_logic; 
   signal interrupt_data: std_logic_vector(4 downto 0); 
   signal interrupt_rdy : std_logic;



   attribute buffer_type:string;
   attribute buffer_type of sys_clk:signal is "none";
   attribute buffer_type of ics_clk:signal is "none"; 
   attribute buffer_type of sp_clk:signal is "none"; 
   attribute buffer_type of pcie_core_trn_clk:signal is "none";

   attribute keep : string;
   attribute keep of reg_sp_reset : signal is "TRUE";
   attribute keep of reg_ics_reset : signal is "TRUE";


begin

   PCIE_REFCLK_IBUF : IBUFDS
   port map (
      O  => sys_clk,    -- Buffer output
      I  => PCLK250_P,  -- Diff_p buffer input
      IB => PCLK250_N   -- Diff_n buffer input
   );

-- -------------------------------------------------------------------------
--     PCI-Express core & PCI bridge & IB bridge 
-- -------------------------------------------------------------------------

   PCI_SYSTEM: entity work.cv2_pci
   generic map (
      USE_TRN_ASYNC => true
   )
   port map (
      -- PCIE core system interface -------------------------------------------
      PCIE_CLK    => sys_clk,
      PCIE_RST_N  => XHSH(10),

      -- PCIE core lanes ------------------------------------------------------      
      PCI_EXP_RXP => PER_P,   
      PCI_EXP_RXN => PER_N,
      PCI_EXP_TXP => PET_P,
      PCI_EXP_TXN => PET_N,

      -- PCIE core TRN common interface ---------------------------------------
      PCIE_CORE_TRN_CLK  => pcie_core_trn_clk, 
      PCIE_CORE_TRN_RST  => pcie_core_trn_rst,

      -- Spartan common interface ---------------------------------------------      
      SP_RESET    => sp_reset,
      SP_CLK      => sp_clk,

      -- Internal Bus common interface ----------------------------------------
      IB_RST      => ics_reset, -- in
      IB_CLK      => ics_clk,

      -- Internal Bus (BAR1) downstream port ----------------------------------
      IB_DOWN_DATA      => ib.down.data,
      IB_DOWN_SOP_N     => ib.down.sop_n,
      IB_DOWN_EOP_N     => ib.down.eop_n,
      IB_DOWN_SRC_RDY_N => ib.down.src_rdy_n,
      IB_DOWN_DST_RDY_N => ib.down.dst_rdy_n,

      -- Internal Bus (BAR1) upstream port ------------------------------------
      IB_UP_DATA        => ib.up.data,
      IB_UP_SOP_N       => ib.up.sop_n,
      IB_UP_EOP_N       => ib.up.eop_n,
      IB_UP_SRC_RDY_N   => ib.up.src_rdy_n,
      IB_UP_DST_RDY_N   => ib.up.dst_rdy_n,

      -- Interrupt interface --------------------------------------------------      
      INTERRUPT   => interrupt, 
      INTR_DATA   => interrupt_data, 
      INTR_RDY    => interrupt_rdy,

      -- Spartan 3 interface (internal bus BAR0) ------------------------------
      SP_TX       => XD(7 downto 0),
      SP_TX_RDY   => XHSH(0),
      SP_RX       => XHSH(8 downto 1),
      SP_RX_RDY   => XHSH(9),
      SP_RST      => XHSH(11)
   );
  
-- -------------------------------------------------------------------------
--                          Clock component                               --
-- -------------------------------------------------------------------------

   CLK_GEN_CV2_U: entity work.clk_gen_cv2  
   generic map(
      INPUT_IS_125   => false,  -- Default input freq is 250

      CLK_MULT       => 16,  -- Multiply from 62.5 MHz, from 400 to 1000 MHz

      CLK_ICS_DIV    => 6,   -- Derive from CLK_MULT
      CLK_USER0_DIV  => 6,   -- Derive from CLK_MULT
      CLK_USER1_DIV  => 6,   -- Derive from CLK_MULT
      CLK_USER2_DIV  => 6,   -- Derive from CLK_MULT
      CLK_USER3_DIV  => 6,   -- Derive from CLK_MULT
      CLK_USER4_DIV  => 6    -- Derive from CLK_MULT
   )
   port map(
      CLK_IN         => pcie_core_trn_clk,  -- 250 (or 125) MHz input clock
      RESET          => pcie_core_trn_rst,

      CLK62_5_OUT    => open,   
      CLK100_OUT     => open,   
      CLK125_OUT     => sp_clk, 
      CLK250_OUT     => open,   
      CLK200_OUT     => open, --ics_clk,   
      CLK166_OUT     => open,   

      CLK_ICS_OUT    => ics_clk, --open,
      CLK_USER0_OUT  => open,
      CLK_USER1_OUT  => open,
      CLK_USER2_OUT  => open,   
      CLK_USER3_OUT  => open,   
      CLK_USER4_OUT  => open,   

      LOCK           => lock
   );


   -- reset logic
   sp_clk_p : process(sp_clk)
   begin
      if sp_clk'event and sp_clk = '1' then
         sp_reset <= reg_sp_reset;
         reg_sp_reset <= pcie_core_trn_rst or (not lock);
      end if;
   end process;

   ics_clk_p : process(ics_clk)
   begin
      if ics_clk'event and ics_clk = '1' then
         ics_reset <= reg_ics_reset;
         reg_ics_reset <= pcie_core_trn_rst or (not lock);
      end if;
   end process;

   
-- -------------------------------------------------------------------------
--                          User application                              --
-- -------------------------------------------------------------------------

-- -------------------------------------------------------------------------
-- DMA TEST MODUL
-- -------------------------------------------------------------------------
   DMA_TEST_U : entity work.DMA_TEST
      port map(
         -- Common Interface
         CLK           => ics_clk,
         RESET         => ics_reset,
         -- Internal Bus Interface
         INTERNAL_BUS  => ib,
         -- Interrupt System
         INTERRUPT     => interrupt,
         INTR_DATA     => interrupt_data,
         INTR_RDY      => interrupt_rdy
      );

-- -------------------------------------------------------------------------
--                        Other FPGA outputs                              --
-- -------------------------------------------------------------------------
   
--    LED_CNTR: process(ics_clk)
--    begin
--       if ics_clk'event and ics_clk = '1' then
--          cntr <= cntr + 1;
--       end if;
--    end process;
-- 
--       
--    FQLED(0) <= cntr(cntr'high);
--    FQLED(1) <= cntr(cntr'high-1);
--    FQLED(2) <= cntr(cntr'high-2);
--    FQLED(3) <= cntr(cntr'high-2);
-- 
end structural;
