-- hgen_mark_fsm.vhd: Workaround for marker 
-- Copyright (C) 2009 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity MARK_FSM is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      MARK_VLD       : in  std_logic;
      SOF_N          : in  std_logic;
      EOF_N          : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
   );
end entity MARK_FSM;

-- ----------------------------------------------------------------------------
--  Architecture: full
-- ----------------------------------------------------------------------------
architecture full of MARK_FSM is
   type tstates is (START, READ, STOP);
   
   signal current_state          : tstates;
   signal next_state             : tstates;
begin

   -- FSM state register
   state_register: process (RESET, CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            current_state <= START;
         else
            current_state <= next_state;
         end if;
      end if;
   end process state_register;
   
      -- transitions in FSM
   transitions_FSM: process (current_state, RX_SRC_RDY_N, TX_DST_RDY_N, SOF_N, MARK_VLD, EOF_N)
   begin
      next_state <= current_state;
      case current_state is
         when START =>
            if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' and SOF_N = '0') then
               if (MARK_VLD = '0') then
                  next_state <= STOP;
               else
                  next_state <= READ;
               end if;
            end if;
         when STOP =>
            if (MARK_VLD = '1') then
               next_state <= READ;
            end if;
         when READ =>
            if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' and EOF_N = '0') then
               next_state <= START;
            end if;
         when others =>
      end case;
   end process transitions_FSM;

   -- outputs of FSM
   outputs_FSM: process (current_state, RX_SRC_RDY_N, TX_DST_RDY_N, SOF_N, MARK_VLD)
   begin
      RX_DST_RDY_N <= '1';
      TX_SRC_RDY_N <= '1';
      
      case current_state is
         when START =>
            if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' and SOF_N = '0') then
               if (MARK_VLD = '0') then
                  RX_DST_RDY_N <= '1';
                  TX_SRC_RDY_N <= '1';
               else
                  RX_DST_RDY_N <= '0';
                  TX_SRC_RDY_N <= '0';
               end if;
            end if;
            if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '1') then
               RX_DST_RDY_N <= '1';
               TX_SRC_RDY_N <= '0';
            end if;
            if (RX_SRC_RDY_N = '1' and TX_DST_RDY_N = '0') then
               RX_DST_RDY_N <= '0';
               TX_SRC_RDY_N <= '1';
            end if;
            if (RX_SRC_RDY_N = '1' and TX_DST_RDY_N = '1') then
               RX_DST_RDY_N <= '0';
               TX_SRC_RDY_N <= '0';
            end if;
         when STOP =>
            if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' and MARK_VLD = '1') then
               RX_DST_RDY_N <= '0';
               TX_SRC_RDY_N <= '0';
            end if;
            if (RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '1') then
               RX_DST_RDY_N <= '1';
               TX_SRC_RDY_N <= '0';
            end if;
            if (RX_SRC_RDY_N = '1' and TX_DST_RDY_N = '0') then
               RX_DST_RDY_N <= '0';
               TX_SRC_RDY_N <= '1';
            end if;
            if (RX_SRC_RDY_N = '1' and TX_DST_RDY_N = '1') then
               RX_DST_RDY_N <= '0';
               TX_SRC_RDY_N <= '0';
            end if;
         when READ => 
               RX_DST_RDY_N <= TX_DST_RDY_N;
               TX_SRC_RDY_N <= RX_SRC_RDY_N;
         when others =>
      end case;
      
   end process outputs_FSM;
   
end architecture full;
