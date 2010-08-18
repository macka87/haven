
-- sof_eof_generator.vhd: This componet generates Frame link SOF and EOF 
--    signals according to IS_HEADER and IS_FOOTER generic and incoming 
--    SOP and EOP signals. 
--
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity SOF_EOF_generator is
   generic (
      RX_IS_HEADER      : boolean := true;
      RX_IS_FOOTER      : boolean := true
   );   
   port (
      -- Common Input
      RESET          : in std_logic;      -- Design reset
      CLK            : in std_logic;      -- Standart clock input
      EN             : in std_logic;      -- Enable input

      -- RX SOP/EOP signals
      RX_SOP_N       : in std_logic;
      RX_EOP_N       : in std_logic;

      -- Generated EX SOF/EOF signals
      RX_SOF_N       : out std_logic;
      RX_EOF_N       : out std_logic
   );
end SOF_EOF_generator;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of SOF_EOF_generator is
   signal hdr_i : std_logic_vector(1 downto 0);
   signal ftr_i : std_logic_vector(1 downto 0);
   signal hf_st : std_logic_vector(1 downto 0);

   -- Packet counter
   signal cnt_pckt : std_logic_vector(1 downto 0);
   signal cnt_pckt_load : std_logic;
   signal cnt_pckt_ce : std_logic;

   signal cnt_ovf : std_logic;
   signal cnt_zero : std_logic;

begin

-- Expand generics
is_header_gener: if (RX_IS_HEADER = true) generate
   hdr_i <= "01";
end generate;
isn_header_gener: if (RX_IS_HEADER = false) generate
   hdr_i <= "00";
end generate;

is_footer_gener: if (RX_IS_FOOTER = true) generate
   ftr_i <= "01";
end generate;
isn_footer_gener: if (RX_IS_FOOTER = false) generate
   ftr_i <= "00";
end generate;

-- SOF/EOF logic
hf_st <= hdr_i + ftr_i + not cnt_pckt_ce;  -- SOP and EOP can be asserted in the same clock!

process(RESET, CLK)
begin
   if (RESET = '1') then
      cnt_pckt <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (cnt_pckt_load = '1') then
         cnt_pckt <= "00";
      elsif (cnt_pckt_ce='1') then
         cnt_pckt <= cnt_pckt + 1;
      end if;
   end if;
end process;

cnt_pckt_ce <= (not RX_SOP_N) and EN;
cnt_ovf <= '1' when cnt_pckt = hf_st else
           '0';
cnt_zero <= '1' when cnt_pckt = "00" else
            '0';
cnt_pckt_load <= (cnt_ovf and (not RX_EOP_N)) and EN;

RX_SOF_N <= (not cnt_zero) or RX_SOP_N;
RX_EOF_N <= not cnt_ovf or RX_EOP_N;
end behavioral;


