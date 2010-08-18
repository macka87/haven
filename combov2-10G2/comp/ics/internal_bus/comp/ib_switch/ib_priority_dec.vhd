--
-- ib_priority_dec.vhd: Internal Bus priority decoder
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
-------------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_PRIORITY_DEC is
   generic (
     PORT_NO    : integer
   );
   port(
      -- FPGA control
      CLK                   : in  std_logic;  -- 100  MHz FPGA clock
      RESET                 : in  std_logic;  -- Reset
      ENABLE                : in  std_logic;  -- Enable
      -- Input Interface
      PORT0_RQ              : in  std_logic;
      PORT1_RQ              : in  std_logic;
      PORT2_RQ              : in  std_logic;
      -- Output Interface
      PORT0_ACK             : out std_logic;
      PORT1_ACK             : out std_logic;
      PORT2_ACK             : out std_logic
      );
end entity IB_PRIORITY_DEC;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_PRIORITY_DEC_ARCH of IB_PRIORITY_DEC is
   
   -- priority counter registers
   signal priority_reg : std_logic;
   signal change_priority : std_logic;

begin

-- register priority_reg -------------------------------------------------------
priority_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      priority_reg <= '0';
   else
      if (CLK'event AND CLK = '1') then
         if (change_priority = '1') then
            priority_reg <= not priority_reg;
         end if;
      end if;
   end if;
end process;

-- Can route from one port to same port

GEN_PORT0: if (PORT_NO=0) generate
  PORT0_ACK <= '0';
  PORT1_ACK <= '1' when  ENABLE = '1' and (
                         (priority_reg='0' and PORT1_RQ  = '1') or
                         (priority_reg='1' and PORT1_RQ  = '1' and PORT2_RQ = '0')
                         ) else '0'; 
  PORT2_ACK <= '1' when  ENABLE = '1' and (
                         (priority_reg='1' and PORT2_RQ  = '1') or
                         (priority_reg='0' and PORT2_RQ  = '1' and PORT1_RQ = '0')
                         ) else '0'; 
  change_priority <= ENABLE and (PORT1_RQ or PORT2_RQ);
end generate;

GEN_PORT1: if (PORT_NO=1) generate
  PORT0_ACK <= '1' when  ENABLE = '1' and (
                         (priority_reg='0' and PORT0_RQ  = '1') or
                         (priority_reg='1' and PORT0_RQ  = '1' and PORT2_RQ = '0')
                         ) else '0'; 
  PORT1_ACK <= '0';
  PORT2_ACK <= '1' when  ENABLE = '1' and (
                         (priority_reg='1' and PORT2_RQ  = '1') or
                         (priority_reg='0' and PORT2_RQ  = '1' and PORT0_RQ = '0')
                         ) else '0'; 
  change_priority <= ENABLE and (PORT0_RQ or PORT2_RQ);
end generate;

GEN_PORT2: if (PORT_NO=2) generate
  PORT0_ACK <= '1' when  ENABLE = '1' and (
                         (priority_reg='0' and PORT0_RQ  = '1') or
                         (priority_reg='1' and PORT0_RQ  = '1' and PORT1_RQ = '0')
                         ) else '0'; 
  PORT1_ACK <= '1' when  ENABLE = '1' and (
                         (priority_reg='1' and PORT1_RQ  = '1') or
                         (priority_reg='0' and PORT1_RQ  = '1' and PORT0_RQ = '0')
                         ) else '0'; 
  PORT2_ACK <= '0';
  change_priority <= ENABLE and (PORT0_RQ or PORT1_RQ);
end generate;

                  
end architecture IB_PRIORITY_DEC_ARCH;

