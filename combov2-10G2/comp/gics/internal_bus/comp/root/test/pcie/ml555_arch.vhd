--
-- ml555_arch.vhd : Example for NetCOPE on the ML555 board
-- Copyright (C) 2007 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
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
--             Architecture declaration  --  Ml555 Top Level                 --
-- ----------------------------------------------------------------------------

architecture structural of ML555 is

component IBUFDS
   port (
      O  : out std_logic;
      I  : in  std_logic;
      IB : in  std_logic
   );
end component;

-- Resets & clocks
signal sys_clk   : std_logic;        -- PCIE system clock
signal reset     : std_logic;        -- Internal system reset
-- Internal bus     
signal ics_clk   : std_logic;        -- ICS clock 
signal ics_reset : std_logic;        -- ICS reset
signal ib        : t_internal_bus64; -- Internal bus
signal cntr      : std_logic_vector(25 downto 0);        -- ICS clock 
-- Interrupt System
signal interrupt : std_logic;
signal intr_data : std_logic_vector(4 downto 0);
signal intr_rdy  : std_logic;

begin

PCIE_REFCLK_IBUF : IBUFDS
port map (
   O  => sys_clk,    -- Buffer output
   I  => PCIE_RCLKP, -- Diff_p buffer input
   IB => PCIE_RCLKN  -- Diff_n buffer input
);

-- Use these or remove used signals from ucf file
SMA_RX_IBUF : IBUFDS
port map (
   O  => open,    -- Buffer output
   I  => SMA_RXP, -- Diff_p buffer input
   IB => SMA_RXN  -- Diff_n buffer input
);

SMA_TX_IBUF : IBUFDS
port map (
   O  => open,    -- Buffer output
   I  => SMA_TXP, -- Diff_p buffer input
   IB => SMA_TXN  -- Diff_n buffer input
);

SFP_MGT_REFCLK_IBUF : IBUFDS
port map (
   O  => open,            -- Buffer output
   I  => SFP_MGT_REFCLKP, -- Diff_p buffer input
   IB => SFP_MGT_REFCLKN  -- Diff_n buffer input
);

SMA_GTPCLK_IBUF : IBUFDS
port map (
   O  => open,         -- Buffer output
   I  => SMA_GTPCLK_P, -- Diff_p buffer input
   IB => SMA_GTPCLK_N  -- Diff_n buffer input
);

SATA_MGT_REFCLK_IBUF : IBUFDS
port map (
   O  => open,             -- Buffer output
   I  => SATA_MGT_REFCLKP, -- Diff_p buffer input
   IB => SATA_MGT_REFCLKN  -- Diff_n buffer input
);

MGT_X0Y0_REFCLK_IBUF : IBUFDS
port map (
   O  => open,             -- Buffer output
   I  => MGT_X0Y0_REFCLKP, -- Diff_p buffer input
   IB => MGT_X0Y0_REFCLKN  -- Diff_n buffer input
);

MGT_X0Y1_REFCLK_IBUF : IBUFDS
port map (
   O  => open,             -- Buffer output
   I  => MGT_X0Y1_REFCLKP, -- Diff_p buffer input
   IB => MGT_X0Y1_REFCLKN  -- Diff_n buffer input
);

SFP1_RX_IBUF : IBUFDS
port map (
   O  => open,     -- Buffer output
   I  => SFP1_RXP, -- Diff_p buffer input
   IB => SFP1_RXN  -- Diff_n buffer input
);

SFP1_TX_IBUF : IBUFDS
port map (
   O  => open,     -- Buffer output
   I  => SFP1_TXP, -- Diff_p buffer input
   IB => SFP1_TXN  -- Diff_n buffer input
);

SFP2_RX_IBUF : IBUFDS
port map (
   O  => open,     -- Buffer output
   I  => SFP2_RXP, -- Diff_p buffer input
   IB => SFP2_RXN  -- Diff_n buffer input
);

SFP2_TX_IBUF : IBUFDS
port map (
   O  => open,     -- Buffer output
   I  => SFP2_TXP, -- Diff_p buffer input
   IB => SFP2_TXN  -- Diff_n buffer input
);

SATA_RX_IBUF : IBUFDS
port map (
   O  => open,     -- Buffer output
   I  => SATA_RXP, -- Diff_p buffer input
   IB => SATA_RXN  -- Diff_n buffer input
);

SATA_TX_IBUF : IBUFDS
port map (
   O  => open,     -- Buffer output
   I  => SATA_TXP, -- Diff_p buffer input
   IB => SATA_TXN  -- Diff_n buffer input
);

-- -------------------------------------------------------------------------
--     PCI-Express core & PCI bridge & IB bridge 
-- -------------------------------------------------------------------------

PCI_SYSTEM: entity work.ml555_pci 
port map (
   PCIE_RST_N  => PCIE_RST,
   PCIE_CLK    => sys_clk,
   PCI_EXP_RXN => PCI_EXP_RXN,
   PCI_EXP_RXP => PCI_EXP_RXP,
   PCI_EXP_TXN => PCI_EXP_TXN,
   PCI_EXP_TXP => PCI_EXP_TXP,
   -- Internal Bus 
   IB_RST      => ics_reset,
   IB_CLK      => ics_clk,
   IB          => ib,
   -- Interrupt System
   INTERRUPT   => interrupt,
   INTR_DATA   => intr_data,
   INTR_RDY    => intr_rdy,
   -- System control 
   CCLK        => FPGA_GCLK_33MHZ,
   CPLD_SPARE1 => CPLD_SPARE1, 
   CPLD_SPARE2 => CPLD_SPARE2,
   CPLD_SPARE3 => CPLD_SPARE3,
   USER_LED0   => open,
   USER_LED1   => open,
   USER_LED2   => open
);

reset <= ics_reset; 

-- -------------------------------------------------------------------------
--                          User application                              --
-- -------------------------------------------------------------------------

DMA_TEST_U : entity work.DMA_TEST
   port map(
      -- Common Interface
      CLK           => ics_clk,
      RESET         => reset,
      -- Internal Bus Interface
      INTERNAL_BUS  => ib,
       -- Interrupt System
      INTERRUPT     => interrupt,
      INTR_DATA     => intr_data,
      INTR_RDY      => intr_rdy
   );

-- -------------------------------------------------------------------------
--                        Other FPGA outputs                              --
-- -------------------------------------------------------------------------
   
LED_CNTR: process(ics_clk)
begin
   if ics_clk'event and ics_clk = '1' then
      cntr <= cntr + 1;
   end if;
end process;
      
USER_LED0 <= cntr(cntr'high);
USER_LED1 <= cntr(cntr'high-1);
USER_LED2 <= cntr(cntr'high-2);

SATA_MGT_CLKSEL <= '0';

end structural;
