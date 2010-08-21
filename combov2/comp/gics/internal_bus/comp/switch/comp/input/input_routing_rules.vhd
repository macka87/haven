--
-- input_routing_rules.vhd : IB Switch Routing Rules
-- Copyright (C) 2008 CESNET
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
-- TODO:
--

library IEEE;  
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--              ENTITY DECLARATION -- IB Switch Routing Rules                -- 
-- ----------------------------------------------------------------------------

entity IB_SWITCH_ROUTING_RULES is 
   generic(
      -- Port number (0/1/2)
      PORT_NUM     : integer:=  0
   ); 
   port (
      -- Input interface ------------------------------------------------------
      HIT_PORT1_BASE  : in  std_logic;
      HIT_PORT1_HIGH  : in  std_logic;
      HIT_PORT2_BASE  : in  std_logic;
      HIT_PORT2_HIGH  : in  std_logic;
      
      HIT_GLOBAL      : in  std_logic;

      -- Output interface -----------------------------------------------------
      REQUEST_VECTOR  : out std_logic_vector(2 downto 0)
   );
end IB_SWITCH_ROUTING_RULES;

-- ----------------------------------------------------------------------------
--            ARCHITECTURE DECLARATION  --  IB Switch Routing Rules          --
-- ----------------------------------------------------------------------------

architecture ib_switch_routing_rules_arch of IB_SWITCH_ROUTING_RULES is

   signal match_port1  : std_logic;
   signal match_port2  : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                           RANGE MATCH logic                            --
   -- -------------------------------------------------------------------------

   match_port1 <= HIT_PORT1_BASE and HIT_PORT1_HIGH and not HIT_GLOBAL;
   match_port2 <= HIT_PORT2_BASE and HIT_PORT2_HIGH and not HIT_GLOBAL;
 
   -- -------------------------------------------------------------------------
   --                            PORT MATCH logic                            --
   -- -------------------------------------------------------------------------
 
   port0_gen: if (PORT_NUM = 0) generate
      REQUEST_VECTOR <= match_port2 & match_port1 & (not (match_port1 or match_port2));
   end generate;

   port1_gen: if (PORT_NUM = 1) generate
      REQUEST_VECTOR <= match_port2 & '0' & not match_port2;
   end generate;

   port2_gen: if (PORT_NUM = 2) generate
      REQUEST_VECTOR <= '0' & match_port1 & not match_port1;
   end generate; 

end ib_switch_routing_rules_arch;


