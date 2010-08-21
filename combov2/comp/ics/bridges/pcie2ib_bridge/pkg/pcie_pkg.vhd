--
-- pcie_pkg.vhd: PCIe Transaction Layer Package
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                       PCIe Transaction Layer Package
-- ----------------------------------------------------------------------------

package pcie_pkg is

   -- PCIe Bridge Configuration Interface
   type t_pcie_bridge_config is record
      BUS_NUM          : std_logic_vector( 7 downto 0); -- Bus number           
      DEVICE_NUM       : std_logic_vector( 4 downto 0); -- Device number  
      FUNC_NUM         : std_logic_vector( 2 downto 0); -- Function number            
      MAX_PAYLOAD_SIZE : std_logic_vector( 2 downto 0); -- Maximum Payload TLP Size      
   end record;

   -- PCIe Transaction Layer Receive Interface
   type t_pcie_trn_receive is record
      SOF_N      : std_logic;                      -- signals the start of a packet
      EOF_N      : std_logic;                      -- signals the end of a packet
      
      DATA       : std_logic_vector(63 downto 0);  -- packet data to be transmitted
      REM_N      : std_logic_vector( 7 downto 0);  -- packet data validity (legal values: 00000000/00001111)
      
      SRC_RDY_N  : std_logic;                      -- source ready
      DST_RDY_N  : std_logic;                      -- destination ready 

      SRC_DSC_N  : std_logic;                      -- source discontinue, asserted when the physical link is going into reset.
      ERR_FWD_N  : std_logic;                      -- error forward, marks the packet in progress as error poisoned
      NP_OK_N    : std_logic;                      -- Non-Posted OK, ready to accept a Non-Posted Request packet

      BAR_HIT_N  : std_logic_vector( 6 downto 0);  -- Indicates BAR(s) targeted by the current receive transaction      

      FC_PH_AV   : std_logic_vector( 7 downto 0);  -- The number of Posted Header FC credits available to the remote link partner.
      FC_PD_AV   : std_logic_vector(11 downto 0);  -- The number of Posted Data FC credits available to the remote link partner
      FC_NPH_AV  : std_logic_vector( 7 downto 0);  -- Number of Non-Posted Header FC credits available to the remote link partner
      FC_NPD_AV  : std_logic_vector(11 downto 0);  -- Number of Non-Posted Data FC credits available to the remote link partner

   end record;
   
   -- PCIe Transaction Layer Transmit Interface
   type t_pcie_trn_transmit is record
      SOF_N      : std_logic;                      -- signals the start of a packet
      EOF_N      : std_logic;                      -- signals the end of a packet
      
      DATA       : std_logic_vector(63 downto 0);  -- packet data to be transmitted
      REM_N      : std_logic_vector( 7 downto 0);  -- packet data validity (legal values: 00000000/00001111)
      
      SRC_RDY_N  : std_logic;                      -- source ready
      DST_RDY_N  : std_logic;                      -- destination ready 

      SRC_DSC_N  : std_logic;                      -- source discontinue, may be asserted any time starting on the first cycle after SOF to EOF, inclusive
      DST_DCS_N  : std_logic;                      -- destination discontinue: Asserted when the physical link is going into reset.

      BUF_AV     : std_logic_vector( 2 downto 0);  -- Indicates transmit buffer availability in the core (0:Non-Posted,1:Posted,2:Completion)
   end record;

   -- PCIe Transaction Layer Interface
   type t_pcie_trn is record
      RX         : t_pcie_trn_receive;
      TX         : t_pcie_trn_transmit;
   end record;

end pcie_pkg;

-- ----------------------------------------------------------------------------
--                      PCIe Transaction Layer Package BODY
-- ----------------------------------------------------------------------------

package body pcie_pkg is
       
end pcie_pkg;



