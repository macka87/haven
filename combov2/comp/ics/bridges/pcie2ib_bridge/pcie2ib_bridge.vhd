--
-- pcie2ib_bridge.vhd : PCI-e to IB Bridge entity
-- Copyright (C) 2007 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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

use work.ib_pkg.all; 
use work.pcie_pkg.all; 

-- ----------------------------------------------------------------------------
--                   ENTITY DECLARATION -- PCIe to IB Bridge                 --
-- ----------------------------------------------------------------------------
      
entity PCIE2IB_BRIDGE is 
   generic(
      IB_BASE_ADDR     : std_logic_vector(31 downto 0) := X"0F000000"; -- IB Base Address
      LTAG_WIDTH       : integer :=   5;                               -- 'Local Read' Buffer tag width (max. 7)
      GTAG_WIDTH       : integer :=   5;                               -- 'Global Read' Buffer tag width (max. 7)       
      BAR_HIT_MASK     : std_logic_vector( 6 downto 0) :=   "1111111"; -- Base Address Register hit mask
      -- BAR base addresses
      BAR0_BASE        : std_logic_vector(31 downto 0) := X"01000000"; -- BAR0 base address for PCIE->IB transalation
      BAR1_BASE        : std_logic_vector(31 downto 0) := X"02000000"; -- BAR1 base address for PCIE->IB transalation
      BAR2_BASE        : std_logic_vector(31 downto 0) := X"03000000"; -- BAR2 base address for PCIE->IB transalation
      BAR3_BASE        : std_logic_vector(31 downto 0) := X"04000000"; -- BAR3 base address for PCIE->IB transalation
      BAR4_BASE        : std_logic_vector(31 downto 0) := X"06000000"; -- BAR4 base address for PCIE->IB transalation
      BAR5_BASE        : std_logic_vector(31 downto 0) := X"08000000"; -- BAR5 base address for PCIE->IB transalation       
      BAR6_BASE        : std_logic_vector(31 downto 0) := X"0A000000"; -- ROM  base address for PCIE->IB transalation
      -- BAR base addresses masks
      BAR0_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR0 mask for PCIE->IB transalation
      BAR1_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR1 mask for PCIE->IB transalation
      BAR2_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR2 mask for PCIE->IB transalation
      BAR3_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR3 mask for PCIE->IB transalation
      BAR4_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR4 mask for PCIE->IB transalation
      BAR5_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR5 mask for PCIE->IB transalation       
      BAR6_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"  -- ROM  mask for PCIE->IB transalation             
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK              : in std_logic;  -- FPGA clock
      RESET            : in std_logic;  -- Reset active high
      
      -- PCI Express Transaction Layer interface ------------------------------      
      PCIE             : inout t_pcie_trn; -- RX and TX link

      -- Internal Bus interface -----------------------------------------------
      IB               : inout t_internal_bus64; -- UP and DOWN stream

      -- Bus Master interface -------------------------------------------------
      BM               : inout t_ibbm_64; -- Internal Bus BM

      -- Configuration interface ----------------------------------------------
      CFG              : in t_pcie_bridge_config -- PCIe Bridge CFG
   );
end PCIE2IB_BRIDGE;



