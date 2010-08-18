-- ebp_wrapper_ent.vhd : Wrapper entity for Xilinx PCI Express endpoint block plus core
-- Copyright (C) 2010 CESNET
-- Author(s): Pavol Korček <korcek@liberouter.org>
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

entity ebp_wrapper is
   generic (
      -- Enable registers on configuration interface
      USE_CFG_REGS   :  boolean  := true   
   );
   port (
      -- System interface signals ---------------------------------------------
      SYS_RESET_N             : in  std_logic;                    -- an asynchronous input signal reset
      SYS_CLK                 : in  std_logic;                    -- referece clock (100 MHz or 250MHz)

      -- PCI Express interface signals ----------------------------------------
      PCI_EXP_RXN             : in  std_logic_vector(7 downto 0); -- negative RX Express lanes
      PCI_EXP_RXP             : in  std_logic_vector(7 downto 0); -- possitive RX Express lanes
      PCI_EXP_TXN             : out std_logic_vector(7 downto 0); -- negative TX Express lanes
      PCI_EXP_TXP             : out std_logic_vector(7 downto 0); -- possitive TX Express lanes

      -- Common transaction interface signals ---------------------------------
      TRN_CLK                 : out std_logic;                    -- TRN clock (62,5/125/250MHz)
      TRN_RESET_N             : out std_logic;                    -- TRN reset
      TRN_LNK_UP_N            : out std_logic;                    -- TRN link up

      -- Transmit TRN interface signals ---------------------------------------
      TRN_TSOF_N              : in  std_logic;                    -- TRN TX start of frame
      TRN_TEOF_N              : in  std_logic;                    -- TRN TX end of frame
      TRN_TD                  : in  std_logic_vector(63 downto 0);-- TRN TX transmit data
      TRN_TREM_N              : in  std_logic_vector(7 downto 0); -- TRN TX data remainder
      TRN_TSRC_RDY_N          : in  std_logic;                    -- TRN TX source ready
      TRN_TDST_RDY_N          : out std_logic;                    -- TRN TX destination ready
      TRN_TBUF_AV             : out std_logic_vector(3 downto 0); -- TRN TX buffer availability
      
      -- Recieve TRN interface signals ----------------------------------------
      TRN_RSOF_N              : out std_logic;                    -- TRN RX start of frame
      TRN_REOF_N              : out std_logic;                    -- TRN RX end of frame
      TRN_RD                  : out std_logic_vector(63 downto 0);-- TRN RX recieve data
      TRN_RREM_N              : out std_logic_vector(7 downto 0); -- TRN RX data remainder
      TRN_RERRFWD_N           : out std_logic;                    -- TRN RX recieve error forward
      TRN_RSRC_RDY_N          : out std_logic;                    -- TRN RX source ready
      TRN_RDST_RDY_N          : in  std_logic;                    -- TRN RX destination ready
      --TRN_RNP_OK_N            : in  std_logic;                    -- TRN RX non-posted OK
      TRN_RBAR_HIT_N          : out std_logic_vector(6 downto 0); -- TRN RX bar hit

      -- Configuration interface signals --------------------------------------
      CFG_INTERRUPT_N         : in  std_logic;                    -- assert interrupt
      CFG_INTERRUPT_RDY_N     : out std_logic;                    -- interrupt ready
      CFG_INTERRUPT_DI        : in  std_logic_vector( 7 downto 0);-- interrupt data input
      CFG_INTERRUPT_DO        : out std_logic_vector( 7 downto 0);-- interrupt data output
      CFG_INTERRUPT_ASSERT_N  : in  std_logic;                    -- assert legacy interrupt
      CFG_BUS_NUMBER          : out std_logic_vector( 7 downto 0);-- PCI Bus number
      CFG_DEVICE_NUMBER       : out std_logic_vector( 4 downto 0);-- PCI Device number
      CFG_FUNCTION_NUMBER     : out std_logic_vector( 2 downto 0);-- PCI Function number
      CFG_DCOMMAND            : out std_logic_vector(15 downto 0) -- extended command register
   );
end entity ebp_wrapper;


