-- combov2_pci_ent.vhd : PCIe and Spartan interface for the ComboLXT card
-- Copyright (C) 2008 CESNET
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
--
-- TODO list :
--


library IEEE;
use IEEE.std_logic_1164.all;

-- --------------------------------------------------------------------
--                          Entity declaration
-- --------------------------------------------------------------------

entity cv2_pci is
   generic (
      -- asynchronous PCIE TRN interface
      USE_TRN_ASYNC : boolean := true
   );
   port (
      -- PCIE core system interface -------------------------------------------
      PCIE_CLK                      : in  std_logic;        -- PCIE core input reference clock (100/250MHz)
      PCIE_RST_N                    : in  std_logic;        -- asynchronous input reset sets core to initial state

      -- PCIE core lanes ------------------------------------------------------
      PCI_EXP_RXN                   : in  std_logic_vector(7 downto 0);
      PCI_EXP_RXP                   : in  std_logic_vector(7 downto 0);
      PCI_EXP_TXN                   : out std_logic_vector(7 downto 0);
      PCI_EXP_TXP                   : out std_logic_vector(7 downto 0);

      -- PCIE core TRN common interface ---------------------------------------
--       PCIE_CORE_TRN_CLK             : out std_logic;        -- output reference clock (125/250MHz)
      PCIE_CORE_TRN_RST             : out std_logic;        -- synchroznized reset

      -- Spartan common interface ---------------------------------------------
      SP_CLK                        : in  std_logic;        -- input clock for Spartan (max. 125MHz)
      SP_RESET                      : in  std_logic;        -- synchronized reset

      -- Internal Bus common interface ----------------------------------------
      IB_CLK                        : in  std_logic;        -- input IB clock (125 to 250 MHz)
      IB_RST                        : in  std_logic;        -- synchronized reset

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
      INTERRUPT                     : in  std_logic;                    -- assert interrupt 
      INTR_DATA                     : in  std_logic_vector(4 downto 0); -- MSI data 
      INTR_RDY                      : out std_logic;                    -- ready signal
      
      -- Spartan 3 interface (internal bus BAR0) ------------------------------
      SP_TX                         : out std_logic_vector(7 downto 0); -- XD(7 downto 0);
      SP_TX_RDY                     : in  std_logic;                    -- XHSH(0) 
      SP_RX                         : in  std_logic_vector(7 downto 0); -- XHSH(8 downto 1)
--       SP_RX_RDY                     : out std_logic;                    -- XHSH(9)
      SP_RST                        : out std_logic                     -- XHSH(11)
   );
end entity cv2_pci;


