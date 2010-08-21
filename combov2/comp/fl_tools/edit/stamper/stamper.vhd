-- stamper.vhd: FrameLink Stamper architecture
-- Copyright (C) 2008 CESNET
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_STAMPER is

   -- ------------------ Constants declaration --------------------------------
   

   -- ------------------ Signals declaration ----------------------------------
   -- registers
   signal reg_send_stamp      : std_logic;
   signal reg_send_stamp_s    : std_logic;
   signal reg_send_stamp_c    : std_logic;
   signal reg_omit_sof        : std_logic;
   signal reg_omit_sof_s      : std_logic;
   signal reg_omit_sof_c      : std_logic;

   -- multiplexers
   signal mx_data             : std_logic_vector(DATA_WIDTH-1 downto 0);
   
   -- others
   signal dv                  : std_logic;
   signal sig_dst_rdy_n       : std_logic;
   signal sending_stamp       : std_logic;

begin
   -- ------------------ Directly mapped signals ------------------------------
   dv                <= not (RX_SRC_RDY_N or TX_DST_RDY_N);
   sending_stamp     <= reg_send_stamp and (not TX_DST_RDY_N);
   sig_dst_rdy_n     <= reg_send_stamp or TX_DST_RDY_N;

   reg_send_stamp_s  <= dv and (not RX_EOF_N);  -- frame ended
   reg_send_stamp_c  <= sending_stamp;
   reg_omit_sof_s    <= sending_stamp;
   reg_omit_sof_c    <= dv and (not RX_SOF_N);  -- first word of frame sent

   -- output ports mapping
   RX_DST_RDY_N      <= sig_dst_rdy_n;
   TX_SRC_RDY_N      <= not (reg_send_stamp or (not RX_SRC_RDY_N));
   TX_SOF_N          <= not reg_send_stamp;
   TX_SOP_N          <= not (reg_send_stamp or ((not RX_SOP_N) and (not reg_omit_sof)));
   TX_EOP_N          <= RX_EOP_N or reg_send_stamp;
   TX_EOF_N          <= RX_EOF_N or reg_send_stamp;
   TX_DATA           <= mx_data;
   TX_REM            <= RX_REM;
   
   
   -- multiplex data and user stamp
   mx_datap: process( reg_send_stamp, RX_DATA )
   begin
      case reg_send_stamp is
         when '0'  => mx_data <= RX_DATA;
         when '1'  => mx_data <= STAMP(DATA_WIDTH-1 downto 0);
         when others => mx_data <= (others => 'X');
      end case;
   end process;

   -- register reg_send_stamp
   reg_send_stampp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_send_stamp <= '1';
         else
            if (reg_send_stamp_S = '1') then
               reg_send_stamp <= '1';
            elsif (reg_send_stamp_C = '1') then
               reg_send_stamp <= '0';
            end if;
         end if;
      end if;
   end process;

   -- register reg_omit_sof
   reg_omit_sofp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_omit_sof <= '0';
         else
            if (reg_omit_sof_S = '1') then
               reg_omit_sof <= '1';
            elsif (reg_omit_sof_C = '1') then
               reg_omit_sof <= '0';
            end if;
         end if;
      end if;
   end process;

end architecture full;
