-- desc_we_logic_fsm.vhd: Input FSM for controling write logic.
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity DESC_WE_LOGIC_FSM is
   generic(
      BLOCK_SIZE     : integer := 512   -- downloaded block size 
   );
   port(
      -- global signals 
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input signals
      ENABLE         : in  std_logic;  -- enable/disable write logic. When disabled, driver fills desc.   
      DESC_TYPE      : in  std_logic;  -- last bit from write data
      COUNT          : in  std_logic_vector(log2(BLOCK_SIZE)-1 downto 0); -- number of descriptor in block
      
      -- output signals
      FLAG_CLEAR     : out std_logic;   -- clear selected flag
      FIFO_WE        : out std_logic;   -- write enable to store descriptor in fifo
      REG_ARRAY_WE   : out std_logic;   -- write enable to store next descriptor (pointer) in reg_array
      STORE_ADDR     : out std_logic;   -- indicator for logic to store address of last descriptor
      STATE_DEC      : out std_logic_vector(1 downto 0)  -- Current state
   );
end entity DESC_WE_LOGIC_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of DESC_WE_LOGIC_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( S_INIT, S_DESCRIPTORS, S_NEXT_DESC );
   
   -- ------------------ Signals declaration ----------------------------------
   signal present_state, next_state : t_state;

   -- last downloaded descriptor index 
   signal max_count  : std_logic_vector(log2(BLOCK_SIZE)-1 downto 0);

begin

   max_count <= (others => '1');
   
   -- --------------- Sync logic -------------------------------------------
   sync_logic  : process( RESET, CLK )
   begin
      if (RESET = '1') then
         present_state <= S_INIT;
      elsif (CLK'event AND CLK = '1') then
         present_state <= next_state;
      end if;
   end process sync_logic;

   -- ------------------ Next state logic -------------------------------------
   next_state_logic : process( present_state, ENABLE, DESC_TYPE, COUNT )
   begin
   case (present_state) is

      -- ---------------------------------------------
      when S_INIT =>
         if (ENABLE = '1') then
            if(DESC_TYPE = '1') then      -- type 1
               next_state <= S_NEXT_DESC;
            else                          -- type 0
               next_state <= S_DESCRIPTORS;
            end if;
         else
            next_state <= S_INIT;
         end if;
      
      -- ---------------------------------------------
      when S_DESCRIPTORS =>
         if (ENABLE = '1') then
            if(COUNT = max_count) then    -- last one descriptor
               next_state <= S_INIT;
            elsif(DESC_TYPE = '1') then   -- type 1 and not last
               next_state <= S_NEXT_DESC;
            else
               next_state <= S_DESCRIPTORS;
            end if;
         else
            next_state <= S_DESCRIPTORS;
         end if;
         
      -- ---------------------------------------------
      when S_NEXT_DESC =>
         if(ENABLE = '1') then
            if (COUNT = max_count) then
               next_state <= S_INIT;
            else
               next_state <= S_NEXT_DESC;
            end if;
         else
            next_state <= S_NEXT_DESC;
         end if;
         
      -- ---------------------------------------------

      when others =>
         next_state <= S_INIT;
      -- ---------------------------------------------
      end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process( present_state, ENABLE, DESC_TYPE, COUNT )
   begin
  
      -- ---------------------------------------------
      -- Initial values
      -- no active signals
      FIFO_WE        <= '0';
      REG_ARRAY_WE   <= '0';
      FLAG_CLEAR     <= '0';
      STORE_ADDR     <= '0';
      STATE_DEC      <= "00";
      -- ---------------------------------------------
      case (present_state) is

      when S_INIT =>
         STATE_DEC <= "01";
         if(ENABLE = '1') then
            if(DESC_TYPE = '1') then   -- type 1
               FIFO_WE        <= '0';
               REG_ARRAY_WE   <= '1';
               FLAG_CLEAR     <= '1';  -- end of work, clear
               STORE_ADDR     <= '0'; 
            else                       -- type 0
               FIFO_WE        <= '1';
               REG_ARRAY_WE   <= '1';
               FLAG_CLEAR     <= '0';  -- not ended
               STORE_ADDR     <= '1';
            end if; 
         end if;                 
      -- ---------------------------------------------
     
      when S_DESCRIPTORS =>
         STATE_DEC <= "10";
         if(ENABLE = '1') then
            if(DESC_TYPE = '1') then      -- type 1
               FIFO_WE        <= '0';
               REG_ARRAY_WE   <= '1';
               FLAG_CLEAR     <= '1';     -- end of work, clear   
               STORE_ADDR     <= '0';
            else                          -- type 0
               FIFO_WE        <= '1';
               REG_ARRAY_WE   <= '1';
               STORE_ADDR     <= '1';
               if(COUNT = max_count) then --last one descriptor 
                  FLAG_CLEAR     <= '1';  -- end of work, clear   
               end if;
            end if;
         end if;
      -- ---------------------------------------------

      when S_NEXT_DESC =>     -- wait for last index
         STATE_DEC <= "11";
         REG_ARRAY_WE   <= '0';
         FIFO_WE        <= '0';
         FLAG_CLEAR     <= '0';
         STORE_ADDR     <= '0';
      -- ---------------------------------------------  

      when others =>
         null;
      -- ---------------------------------------------  
      end case;
   end process output_logic;

end architecture full;

