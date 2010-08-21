
--
-- crc32_32b.vhd: 32-bit CRC coder with 16 bits at a time
-- Copyright (C) 2005 CESNET
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
entity crc32_32b is
   port(
      DI: in std_logic_vector(31 downto 0);
      CLK: in std_logic;
      RESET: in std_logic;
      DI_DV: in std_logic;
      DI_MASK: in std_logic_vector(1 downto 0);
      EOP: in std_logic;

      RDY: out std_logic;
      CRC: out std_logic_vector(31 downto 0);
      DO_DV: out std_logic
   );
end entity crc32_32b;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture crc32_32b_arch of crc32_32b is

   -- register signals
   signal reg_crc : std_logic_vector(31 downto 0);
   signal reg_input: std_logic_vector(31 downto 0);
   -- internal controling outputs of FSM
   signal DI_CTL: std_logic;
   signal TVAL_CTL: std_logic;
   signal MASK: std_logic;
   signal FSM_DV: std_logic;
   -- CRC tables output values
   signal TVAL: std_logic_vector(31 downto 0);
   signal TVAL2: std_logic_vector(31 downto 0);
   component crc32_32b_tab is
      port(
	     DI: in std_logic_vector(31 downto 0);
		 CRC: out std_logic_vector(31 downto 0)
	  );
   end component;

   component crc32_8b_tab is
      port(
	     DI: in std_logic_vector(7 downto 0);
		 CRC: out std_logic_vector(31 downto 0)
	  );
   end component;

   component crc32_32b_fsm is
      port(
         CLK: in std_logic;
         RESET: in std_logic;
         DI_DV: in std_logic;
         DI_MASK: in std_logic_vector(1 downto 0);
         EOP: in std_logic;

         DI_CTL: out std_logic;
         TVAL_CTL: out std_logic;
         MASK: out std_logic;
         DO_DV: out std_logic;
		 FSM_DV: out std_logic
      );
   end component;

begin

-- CRC register ------------------------------------------------------
reg_crc_proc: process(RESET, CLK)
begin
   if RESET = '1' then
      reg_crc <= (others => '0');
   elsif CLK'event AND CLK = '1' then
      if DI_DV = '1' OR FSM_DV = '1' then
         reg_crc <= reg_input;
      end if;
   end if;
end process;

-- input logic for reg_crc
reg_input <= TVAL2(31 downto 24) &
                (reg_crc(31 downto 8) XOR TVAL2(23 downto 0)) when MASK='1' else
             DI XOR TVAL when DI_CTL = '0' AND TVAL_CTL = '0' else
			 NOT DI when DI_CTL = '0' AND TVAL_CTL = '1' else
			 TVAL when DI_CTL = '1' AND TVAL_CTL = '0' else
			 (others => '1');

crc32_32b_tab_instance: crc32_32b_tab
port map(
   DI => reg_crc,
   CRC => TVAL
);

crc32_8b_tab_instance: crc32_8b_tab
port map(
   DI => reg_crc(7 downto 0),
   CRC => TVAL2
);

crc32_32b_fsm_instance: crc32_32b_fsm
port map(
   CLK => CLK,
   RESET => RESET,
   DI_DV => DI_DV,
   DI_MASK => DI_MASK,
   EOP => EOP,

   DI_CTL => DI_CTL,
   TVAL_CTL => TVAL_CTL,
   MASK => MASK,
   DO_DV => DO_DV,
   FSM_DV => FSM_DV
);

-- final CRC modifications
CRC <= NOT (reg_crc(7 downto 0) & reg_crc(15 downto 8) &
   reg_crc(23 downto 16) & reg_crc(31 downto 24));
RDY <= NOT FSM_DV;

end architecture crc32_32b_arch;

