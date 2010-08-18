-- sb_endpoint_arch.vhd: Service Bus Endpoint component architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
--                               Architecture
-- ----------------------------------------------------------------------------
architecture full of SB_ENDPOINT is

signal shift_in   : std_logic_vector(24 downto 0);
signal sig_id     : std_logic_vector(7 downto 0);
signal sig_rd     : std_logic;
signal sig_addr   : std_logic_vector(7 downto 0);
signal sig_di     : std_logic_vector(7 downto 0);

signal cnt_recv   : std_logic_vector(4 downto 0);
signal cnt_send   : std_logic_vector(4 downto 0);

signal reg_got_id : std_logic;
signal reg_id     : std_logic_vector(7 downto 0);

type t_fsm is (idle, recv, decide, read, read_wait, write, init, send);

signal fsm        : t_fsm;
signal fsm_next   : t_fsm;

begin

-- Load input data into shift register
shift_in_p : process(CLK, RESET)
begin
   if RESET = '1' then
      shift_in <= (others => '0');
   elsif CLK'event and CLK = '1' then
      if TDI_DV = '1' or fsm = send then
         shift_in <= shift_in(23 downto 0) & TDI;
      elsif DRDY = '1' then
         shift_in <= shift_in(24 downto 8) & DRD;
      elsif fsm = read and sig_addr = "00000000" then
         shift_in <= shift_in(24 downto 8) & reg_id;
      end if;
   end if;
end process;

-- map signals to shift register
sig_id <= shift_in(24 downto 17);
sig_rd <= not shift_in(16); -- This means that '0' is read and '1' is write
sig_addr <= shift_in(15 downto 8);
sig_di <= shift_in(7 downto 0);

-- FSM running at CLK frequency
fsm_p : process(CLK, RESET)
begin
   if RESET = '1' then
      fsm <= idle;
   elsif CLK'event and CLK = '1' then
      fsm <= fsm_next;
   end if;
end process;

fsm_next_p : process(fsm, shift_in, cnt_recv, cnt_send, TDI_DV, DRDY,
                     reg_got_id, reg_id)
begin
   fsm_next <= fsm;

   case fsm is
   when idle =>
      if TDI_DV = '1' then
         fsm_next <= recv;
      end if;

   when recv =>
      if cnt_recv = "11000" then    -- Whole message has been recieved
         fsm_next <= decide;
      end if;

   when decide =>
      if sig_rd = '1' then          -- Message is read
         if sig_id = reg_id then       -- To this endpoint
            fsm_next <= read;
         else                          -- To another endpoint
            fsm_next <= send;
         end if;
      else                          -- Message is write
         if reg_got_id = '0' and 
            sig_addr = "00000000" then -- First write to addr 0 sets ID
            fsm_next <= init;
         else                          -- Normal write
            if sig_id = reg_id then       -- To this endpoint
               fsm_next <= write;
            else                          -- To another endpoint
               fsm_next <= send;
            end if;
         end if;
      end if;

   when write =>
      fsm_next <= idle;

   when init =>
      fsm_next <= idle;

   when read =>
      if DRDY = '1' or sig_addr = "00000000" then
         fsm_next <= send;
      else
         fsm_next <= read_wait;
      end if;

   when read_wait =>
      if DRDY = '1' then
         fsm_next <= send;
      end if;

   when send =>
      if cnt_send = "11000" then
         fsm_next <= idle;
      end if;

   end case;
end process;

-- Counter of recieved bits
cnt_recv_p : process(CLK, RESET)
begin
   if RESET = '1' then
      cnt_recv <= (others => '0');
   elsif CLK'event and CLK = '1' then
      if cnt_recv = "11000" then
         cnt_recv <= (others => '0');
      elsif TDI_DV = '1' then
         cnt_recv <= cnt_recv + 1;
      end if;
   end if;
end process;

-- Counter of sent bits
cnt_send_p : process(CLK, RESET)
begin
   if RESET = '1' then
      cnt_send <= (others => '0');
   elsif CLK'event and CLK = '1' then
      if cnt_send = "11000" then
         cnt_send <= (others => '0');
      elsif fsm = send then
         cnt_send <= cnt_send + 1;
      end if;
   end if;
end process;

-- This register goes to 1 when Identification is loaded and never returns to 0
reg_got_id_p : process(RESET, CLK)
begin
   if RESET = '1' then
      reg_got_id <= '0';
   elsif CLK'event and CLK = '1' then
      if fsm = init then
         reg_got_id <= '1';
      end if;
   end if;
end process;

-- This register is once loaded by write to address 0
reg_id_p : process(RESET, CLK)
begin
   if RESET = '1' then
      reg_id <= (others => '0');
   elsif CLK'event and CLK = '1' then
      if fsm = init then
         reg_id <= sig_di;
      end if;
   end if;
end process;

TDO <= shift_in(24);
TDO_DV <= '1' when fsm = send else
          '0';

ADDR <= sig_addr;
RD <= '1' when fsm = read and sig_addr /= "00000000" else 
      '0';
WR <= '1' when fsm = write else
      '0';
DWR <= sig_di;

end architecture full;

