-- netcope_ics_ent.vhd : NetCOPE infrastructure entity
-- Copyright (C) 2010 CESNET
-- Author(s): Vaclav Bartos <washek@liberouter.org>
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
use work.combov2_nc_const.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                              Entity declaration
-- ----------------------------------------------------------------------------
entity netcope_ics is
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
end netcope_ics;
