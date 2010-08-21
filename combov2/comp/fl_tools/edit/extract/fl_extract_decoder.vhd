-- fl_extract_decoder.vhd: FrameLink Extract decoder subcomponent.
-- Copyright (C) 2007 CESNET
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
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FL_EXTRACT_DECODER is
   generic(
    DECODER_WIDTH  :INTEGER:=4;
    POSITION_WIDTH :INTEGER:=4
   );
   port(
     CLK          : in std_logic;
     RESET        : in std_logic;

  -- Input interface
     SRC_RDY_N : in  std_logic;
     DST_RDY_N : in  std_logic;
     EOP_N     : in  std_logic;
     EOF_N     : in  std_logic;

  -- Output interface
     HEAD_EN   : out std_logic_vector(2**DECODER_WIDTH-1 downto 0);
     POSITION  : out std_logic_vector(POSITION_WIDTH-1 downto 0)
   );
end entity FL_EXTRACT_DECODER;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture FL_EXTRACT_DECODER_ARCH of FL_EXTRACT_DECODER is
signal packet_count: std_logic_vector(DECODER_WIDTH-1 downto 0);
signal part_count: std_logic_vector(POSITION_WIDTH-1 downto 0);
signal packet_ce: std_logic;
signal part_ce: std_logic;
signal packet_reset: std_logic;
signal part_reset: std_logic;

begin
  -- packet counter
process (clk, packet_reset) 
  begin
   if clk='1' and clk'event then
     if packet_reset='1' then  
        packet_count <= (others => '0');
     elsif packet_ce='1' then
          packet_count <= packet_count + 1;
     end if;
   end if;
end process;

--part of packet counter
process (clk, part_reset) 
  begin
   if clk='1' and clk'event then 
     if part_reset='1' then
        part_count <= (others => '0');
     elsif part_ce='1' then
          part_count <= part_count + 1;
     end if;
   end if;
end process;

-- 1-to-n decoder
process(packet_count)
  begin
    HEAD_EN <= (others => '0');
    for i in 0 to 2**DECODER_WIDTH-1 loop
      if (conv_std_logic_vector(i, DECODER_WIDTH) = packet_count) then
        HEAD_EN(i) <= '1';
      end if;
    end loop;
end process;

-- control logic
packet_reset <= ((not EOF_N) and part_ce) or RESET;
packet_ce <= (not EOP_N) and part_ce;
part_reset <= ((not EOP_N) and part_ce) or RESET;
part_ce <=  not SRC_RDY_N and not DST_RDY_N;

POSITION<=part_count;
end architecture FL_EXTRACT_DECODER_ARCH;
