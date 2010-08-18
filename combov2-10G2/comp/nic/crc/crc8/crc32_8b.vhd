
--
-- CRC32.vhd: 32-bit CRC coder with 8 bits at a time
-- Copyright (C) 2004 CESNET
-- Author(s): Bidlo Michal <bidlom@fit.vutbr.cz>
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
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity crc32_8b is
   port(
      DI: in std_logic_vector(7 downto 0);
      CLK: in std_logic;
      RESET: in std_logic;
      DI_DV: in std_logic;
      EOP: in std_logic;

      RDY: out std_logic;
      CRC: out std_logic_vector(31 downto 0);
      DO_DV: out std_logic
   );
end entity crc32_8b;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture CRC32_arch of crc32_8b is

   -- register signals
   signal reg_crc0 : std_logic_vector(7 downto 0);
   signal reg_crc1 : std_logic_vector(7 downto 0);
   signal reg_crc2 : std_logic_vector(7 downto 0);
   signal reg_crc3 : std_logic_vector(7 downto 0);
   -- XORed signals
   signal xor0_output: std_logic_vector(7 downto 0);
   signal xor1_output: std_logic_vector(7 downto 0);
   signal xor2_output: std_logic_vector(7 downto 0);
   signal xor3_output: std_logic_vector(7 downto 0);
   -- internal controling outputs of FSM
   signal DI_CTL: std_logic;
   signal TVAL_CTL: std_logic;
   signal DV_CTL: std_logic;
   signal FSM_DV: std_logic;
   -- CRC table output value
   signal TVAL: std_logic_vector(31 downto 0);

   component crc32_8b_tab is
      port(
         DI: in std_logic_vector(7 downto 0);
         CRC: out std_logic_vector(31 downto 0)
      );
   end component;

   component crc32_8b_fsm is
      port(
         CLK: in std_logic;
         RESET: in std_logic;
         DI_DV: in std_logic;
         EOP: in std_logic;

         DI_CTL: out std_logic;
         TVAL_CTL: out std_logic;
         DO_DV: out std_logic;
         DV_CTL : out std_logic;
	 FSM_DV : out std_logic
      );
   end component;

begin

reg_crc_proc: process(RESET, CLK)
begin
   if RESET = '1' then
      reg_crc0 <= (others => '0');
      reg_crc1 <= (others => '0');
      reg_crc2 <= (others => '0');
      reg_crc3 <= (others => '0');
   elsif CLK'event AND CLK = '1' then
      if DV_CTL = '1' OR FSM_DV = '1' then
         reg_crc0 <= xor0_output;
         reg_crc1 <= xor1_output;
         reg_crc2 <= xor2_output;
         reg_crc3 <= xor3_output;
      end if;
   end if;
end process;

-- input logic for reg_crc part3
xor3_output <= DI XOR TVAL(31 downto 24) when DI_CTL = '0' AND TVAL_CTL = '0' else
               NOT DI when DI_CTL = '0' AND TVAL_CTL = '1' else
			   TVAL(31 downto 24) when DI_CTL = '1' AND TVAL_CTL = '0' else
			   "11111111";

-- input logic for reg_crc part2
xor2_output <= reg_crc3 XOR TVAL(23 downto 16) when TVAL_CTL = '0' else
               reg_crc3;

-- input logic for reg_crc part1
xor1_output <= reg_crc2 XOR TVAL(15 downto 8) when TVAL_CTL = '0' else
               reg_crc2;

-- input logic for reg_crc part0
xor0_output <= reg_crc1 XOR TVAL(7 downto 0) when TVAL_CTL = '0' else
               reg_crc1;

CRC32_table_8b_instance: crc32_8b_tab
port map(
   DI => reg_crc0,
   CRC => TVAL
);

FSM_CRC32_instance: crc32_8b_fsm
port map(
   CLK => CLK,
   RESET => RESET,
   DI_DV => DI_DV,
   EOP => EOP,

   DI_CTL => DI_CTL,
   TVAL_CTL => TVAL_CTL,
   DO_DV => DO_DV,
   DV_CTL => DV_CTL,
   FSM_DV => FSM_DV
);

-- final output modifications
CRC <= NOT (reg_crc0 & reg_crc1 & reg_crc2 & reg_crc3);
RDY <= NOT (FSM_DV);

end architecture CRC32_arch;


