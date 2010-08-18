-- nicprobe.vhd: Implementation of NIC Probe FrameLink debug unit
-- Copyright (C) 2009 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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
--                               Architecture
-- ----------------------------------------------------------------------------

architecture FL_NICPROBE_ARCH of FL_NICPROBE is

   -- Signals
   signal cnt_length          : std_logic_vector(15 downto 0);
   signal reg_segment_size    : std_logic_vector(15 downto 0);
   signal reg_eof             : std_logic;
   signal cmp_len_ok          : std_logic;
   signal cmp_header_ok       : std_logic;
   signal reg_header_ok       : std_logic;

begin

   -- WARNING: Header analysis is only valid for 128 FL width
   cmp_header_okp: process(DATA)
   begin
      if (DATA(23 downto 16) = X"0C" and DATA(31 downto 24) = X"00") then
         cmp_header_ok <= '1';
      else
         cmp_header_ok <= '0';
      end if;
   end process;

   reg_header_okp: process(CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RX_DST_RDY_N = '0' and TX_SRC_RDY_N = '0') then
            if (SOF_N = '0') then
               if (SOP_N = '0' and EOP_N = '0' and cmp_header_ok = '1') then
                  reg_header_ok <= '1';
               else
                  reg_header_ok <= '0';
               end if;
            end if;
         end if;
      end if;
   end process;

   -- Segment size check is working for all FL sizes
   reg_segment_sizep: process(CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RX_DST_RDY_N = '0' and TX_SRC_RDY_N = '0') then
            if (SOF_N = '0' and SOP_N = '0') then
               reg_segment_size <= DATA(15 downto 0);
            end if;
         end if;
      end if;
   end process;

   cnt_lengthp: process(CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RX_DST_RDY_N = '0' and TX_SRC_RDY_N = '0') then
            if (SOF_N = '0') then
               if (EOP_N = '0') then
                  cnt_length <= conv_std_logic_vector(conv_integer(DREM), cnt_length'length) + 1;
               else
                  cnt_length <= conv_std_logic_vector(FL_WIDTH/8, cnt_length'length);
               end if;
            else
               if (EOP_N = '0' and DREM /= "1111") then
                  cnt_length <= (cnt_length + conv_integer(DREM)) + 1;
               else
                  cnt_length <= cnt_length + FL_WIDTH/8;
               end if;
            end if;
         end if;
      end if;
   end process;

   reg_eofp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg_eof <= '0';
         else
            reg_eof <= not EOF_N and not TX_SRC_RDY_N and not RX_DST_RDY_N;
         end if;
      end if;
   end process;

   FRAME_OK <= cmp_len_ok and reg_header_ok;
   FRAME_OK_VLD <= reg_eof;

   cmp_len_okp: process(cnt_length, reg_segment_size)
   begin
      if (cnt_length = reg_segment_size) then
         cmp_len_ok <= '1';
      else
         cmp_len_ok <= '0';
      end if;
   end process;

end architecture FL_NICPROBE_ARCH;
