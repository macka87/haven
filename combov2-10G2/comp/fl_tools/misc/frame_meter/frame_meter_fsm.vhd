-- frame_meter_fsm.vhd: Output FSM
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

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_FRAME_METER_FSM is
   port(
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- input signals
      EOF_VLD_N      : in  std_logic;        -- stop sending data
      EOP_VLD_N      : in  std_logic;        -- stop sending header data
      FIFO_EMPTY     : in  std_logic;        -- if not, send length
      IS_IDLE        : in  std_logic;        -- if, send idle bytes
      NEXT_DATA      : in  std_logic;        -- length sent
      
      -- output signals
      WAIT_STATE     : out std_logic;
      SEND_LENGTH    : out std_logic;
      SEND_HEADER    : out std_logic;
      SEND_IDLE      : out std_logic;
      SEND_DATA      : out std_logic
   );
end entity FL_FRAME_METER_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_FRAME_METER_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( S_IDLE,
                     S_SEND_LENGTH, S_SEND_HEADER, S_SEND_IDLE, S_SEND_DATA);
   
   -- ------------------ Signals declaration ----------------------------------
   signal present_state, next_state : t_state;

begin
   
   -- --------------- Sync logic -------------------------------------------
   sync_logic  : process( RESET, CLK )
   begin
      if (RESET = '1') then
         present_state <= S_IDLE;
      elsif (CLK'event AND CLK = '1') then
         present_state <= next_state;
      end if;
   end process sync_logic;

   -- ------------------ Next state logic -------------------------------------
   next_state_logic : process(present_state, EOF_VLD_N, EOP_VLD_N,
                                 FIFO_EMPTY, IS_IDLE, NEXT_DATA)
   begin
   case (present_state) is

      -- ---------------------------------------------
      when S_IDLE =>
         if (FIFO_EMPTY = '0') then
            next_state <= S_SEND_LENGTH;
         else
            next_state <= S_IDLE;
         end if;
      
      -- ---------------------------------------------
      when S_SEND_LENGTH =>
         if (NEXT_DATA = '1') then
            next_state <= S_SEND_HEADER;
         else
            next_state <= S_SEND_LENGTH;
         end if;
         
      -- ---------------------------------------------
      when S_SEND_HEADER =>
         if (EOP_VLD_N = '0') then
            if(IS_IDLE = '1') then
               next_state <= S_SEND_IDLE;
            else
               next_state <= S_SEND_DATA;
            end if;
         else
            next_state <= S_SEND_HEADER;
         end if;
         
      -- ---------------------------------------------
      when S_SEND_IDLE =>
         if (IS_IDLE = '1') then
            next_state <= S_SEND_IDLE;
         else
            next_state <= S_SEND_DATA;
         end if;
         
      -- ---------------------------------------------
      when S_SEND_DATA =>
         if(EOF_VLD_N = '0') then
            if(FIFO_EMPTY = '0') then
               next_state <= S_SEND_LENGTH;
            else
               next_state <= S_IDLE;
            end if;
         else 
            next_state <= S_SEND_DATA;
         end if;
      -- ---------------------------------------------

      end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process( present_state )
   begin
  
      -- ---------------------------------------------
      -- Initial values
      -- no active signals
      WAIT_STATE     <= '1';
      SEND_LENGTH    <= '0';
      SEND_HEADER    <= '0';
      SEND_IDLE      <= '0';
      SEND_DATA      <= '0';
      -- ---------------------------------------------
      case (present_state) is
      when S_IDLE =>
         WAIT_STATE     <= '1';
         SEND_LENGTH    <= '0';
         SEND_HEADER    <= '0';
         SEND_IDLE      <= '0';
         SEND_DATA      <= '0';

      -- ---------------------------------------------
      when S_SEND_LENGTH =>
         WAIT_STATE     <= '0';
         SEND_LENGTH    <= '1';
         SEND_HEADER    <= '0';
         SEND_IDLE      <= '0';
         SEND_DATA      <= '0';

      -- ---------------------------------------------
      when S_SEND_HEADER =>
         WAIT_STATE     <= '0';
         SEND_LENGTH    <= '0';
         SEND_HEADER    <= '1';
         SEND_IDLE      <= '0';
         SEND_DATA      <= '0';

      -- ---------------------------------------------
      when S_SEND_IDLE =>
         WAIT_STATE     <= '0';
         SEND_LENGTH    <= '0';
         SEND_HEADER    <= '0';
         SEND_IDLE      <= '1';
         SEND_DATA      <= '0';

      -- ---------------------------------------------
      when S_SEND_DATA =>
         WAIT_STATE     <= '0';
         SEND_LENGTH    <= '0';
         SEND_HEADER    <= '0';
         SEND_IDLE      <= '0';
         SEND_DATA      <= '1';
         
      -- ---------------------------------------------
      end case;
   end process output_logic;

end architecture full;
