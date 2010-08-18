-- frame_counter.vhd: Frame Counter komponent
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLB_FRAME_COUNTER is
   generic(
      COUNTER_WIDTH  : integer
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;
      
      -- input interface
      INC            : in std_logic;
      DEC            : in std_logic;
      
      -- output interface
      FRAME_RDY      : out std_logic
   );
end entity FLB_FRAME_COUNTER;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of FLB_FRAME_COUNTER is
   -- constants
   constant CNT_FRAMES_CMP1 : std_logic_vector(COUNTER_WIDTH-1 downto 0) 
                           := (others => '0');
   constant CNT_FRAMES_CMP2 : std_logic_vector(COUNTER_WIDTH-1 downto 0) 
                           := conv_std_logic_vector(1, COUNTER_WIDTH);

   -- counters
   signal cnt_frames       : std_logic_vector(COUNTER_WIDTH-1 downto 0);
   signal cnt_frames_ce    : std_logic;
   signal cnt_frames_dir   : std_logic;
   
   -- registers
   signal reg_frame_rdy    : std_logic;
   signal reg_frame_rdy_we : std_logic;
   signal reg_frame_rdy_in : std_logic;

begin
   -- output signals
   reg_frame_rdy_in <= INC and (not DEC);
   reg_frame_rdy_we <= 
         '1' when ((cnt_frames = CNT_FRAMES_CMP1) and INC = '1') 
         or ((cnt_frames = CNT_FRAMES_CMP2) and DEC = '1' and INC = '0')
         else '0';

   -- counter control signals
   cnt_frames_ce  <= INC xor DEC;
   cnt_frames_dir <= INC;

   -- output signals
   FRAME_RDY      <= reg_frame_rdy;

   -- ------------------ counter cnt_frames -----------------------------------
   cnt_framesp: process (CLK) 
   begin
      if CLK='1' and CLK'event then
         if RESET = '1' then 
            cnt_frames <= (others => '0');
         elsif cnt_frames_ce = '1' then
            if cnt_frames_dir = '1' then  
               cnt_frames <= cnt_frames + 1;
            else
               cnt_frames <= cnt_frames - 1;
            end if;
         end if;
      end if;
   end process;

   -- ------------------ register cnt_frames -----------------------------------
   reg_frame_rdyp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_frame_rdy <= '0';
         elsif (reg_frame_rdy_we = '1') then
            reg_frame_rdy <= reg_frame_rdy_in;
         end if;
      end if;
   end process;

end architecture behavioral;

