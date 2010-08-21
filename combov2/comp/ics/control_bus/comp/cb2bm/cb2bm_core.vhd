--
-- cb2bm_core.vhd: CB2BM component CORE entity
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek    <kosek@liberouter.org>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CB2BM_CORE is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;
      
      -- Control Bus Endpoint interface
      UPS_DATA       : out std_logic_vector(15 downto 0);
      UPS_SOP        : out std_logic;
      UPS_EOP        : out std_logic;
      UPS_SRC_RDY    : out std_logic;
      UPS_DST_RDY    : in  std_logic;
      DNS_DATA       : in  std_logic_vector(15 downto 0);
      DNS_SOP        : in  std_logic;
      DNS_EOP        : in  std_logic;
      DNS_SRC_RDY    : in  std_logic;
      DNS_DST_RDY    : out std_logic;
      
      -- Bus Master Controller interface
      GLOBAL_ADDR    : out std_logic_vector(63 downto 0);   -- Global Address
      LOCAL_ADDR     : out std_logic_vector(31 downto 0);   -- Local Address
      LENGTH         : out std_logic_vector(11 downto 0);   -- Length
      TAG            : out std_logic_vector(15 downto 0);   -- Operation TAG
      TRANS_TYPE     : out std_logic_vector(1 downto 0);    -- Trans type
      REQ            : out std_logic;                       -- Request
      ACK            : in  std_logic;                       -- Ack
      OP_TAG         : in  std_logic_vector(15 downto 0);   -- Operation TAG
      OP_DONE        : in  std_logic                        -- Acknowledge
   );
end entity CB2BM_CORE;
