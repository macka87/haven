--
-- output_priority_dec.vhd: IB Switch Output Priority Decoder
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_switch_pkg.all;

-- ----------------------------------------------------------------------------
--          ENTITY DECLARATION -- IB Switch Output Priority Decoder          --
-- ----------------------------------------------------------------------------

entity IB_SWITCH_OUTPUT_PRIORITY_DEC is
   generic (
     -- Port number (0/1/2)
     PORT_NUM    : integer
   );
   port (
      -- Common interface -----------------------------------------------------
      CLK          : in  std_logic;
      RESET        : in  std_logic;
      ENABLE       : in  std_logic;
      
      -- Input Request Interface ----------------------------------------------
      PORT0_REQ    : in  std_logic;
      PORT1_REQ    : in  std_logic;
      PORT2_REQ    : in  std_logic;
      
      -- Output Acknowledge Interface -----------------------------------------
      PORT0_ACK    : out std_logic;
      PORT1_ACK    : out std_logic;
      PORT2_ACK    : out std_logic
   );
end entity IB_SWITCH_OUTPUT_PRIORITY_DEC;

-- ----------------------------------------------------------------------------
--     ARCHITECTURE DECLARATION  --  IB Switch Output Priority Decoder       --
-- ----------------------------------------------------------------------------

architecture ib_switch_output_priority_dec_arch of IB_SWITCH_OUTPUT_PRIORITY_DEC is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal priority_reg    : std_logic;
   signal change_priority : std_logic;
   signal ack0            : std_logic;
   signal ack1            : std_logic;
   signal ack2            : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                            PRIORITY REGISTER                           --
   -- -------------------------------------------------------------------------

   priority_regp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            priority_reg <= '0';
         elsif (change_priority = '1') then
            priority_reg <= not priority_reg;
         end if;
      end if;
   end process;
   
   -- -------------------------------------------------------------------------
   --                             PRIORITY LOGIC                             --
   -- -------------------------------------------------------------------------

   -- PORT0 -------------------------------------------------------------------
   GEN_PORT0: if (PORT_NUM = 0) generate
      ack1 <= ENABLE and ((not priority_reg and PORT1_REQ) or
                          (    priority_reg and PORT1_REQ and not PORT2_REQ));
      
      ack2 <= ENABLE and ((    priority_reg and PORT2_REQ) or
                          (not priority_reg and PORT2_REQ and not PORT1_REQ));
      
      PORT0_ACK <= ENABLE and PORT0_REQ;
      PORT1_ACK <= ack1;
      PORT2_ACK <= ack2;
      
      change_priority <= ENABLE and (PORT1_REQ or PORT2_REQ);
   end generate;

   -- PORT1 -------------------------------------------------------------------
   GEN_PORT1: if (PORT_NUM = 1) generate
      ack0 <= ENABLE and ((not priority_reg and PORT0_REQ) or
                          (    priority_reg and PORT0_REQ and not PORT2_REQ));
      
      ack2 <= ENABLE and ((    priority_reg and PORT2_REQ) or
                          (not priority_reg and PORT2_REQ and not PORT0_REQ));

      PORT0_ACK <= ack0;
      PORT1_ACK <= ENABLE and PORT1_REQ;
      PORT2_ACK <= ack2;
      
      change_priority <= ENABLE and (PORT0_REQ or PORT2_REQ);
   end generate;

   -- PORT2 -------------------------------------------------------------------
   GEN_PORT2: if (PORT_NUM = 2) generate
      ack0 <= ENABLE and ((not priority_reg and PORT0_REQ) or
                          (    priority_reg and PORT0_REQ and not PORT1_REQ));
      
      ack1 <= ENABLE and ((    priority_reg and PORT1_REQ) or
                          (not priority_reg and PORT1_REQ and not PORT0_REQ));

      PORT0_ACK <= ack0;
      PORT1_ACK <= ack1;
      PORT2_ACK <= ENABLE and PORT2_REQ;
      
      change_priority <= ENABLE and (PORT0_REQ or PORT1_REQ);
   end generate;
   
end architecture ib_switch_output_priority_dec_arch;
   

