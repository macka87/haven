--
-- dp_regflags.vhd: Dual Ported Register of Flags
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas martinek@liberouter.org
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
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity dp_regflags is
   generic(
      EXADDR   : integer := 5
   );
	port(
      RESET    : in  std_logic;

      -- SET part
      CLK_SET  : in  std_logic;
      SET      : in  std_logic;
      ADDR_SET : in  std_logic_vector(EXADDR-1 downto 0);
      DO_SET   : out std_logic;

      -- CLR part
      CLK_CLR  : in  std_logic;
      CLR      : in  std_logic;
      ADDR_CLR : in  std_logic_vector(EXADDR-1 downto 0);
      DO_CLR   : out std_logic;

      DO_ALL   : out std_logic_vector((2**EXADDR)-1 downto 0)
	);
end entity dp_regflags;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of dp_regflags is
   constant REGS_NUM    : integer := 2**EXADDR;

   signal clr_int       : std_logic_vector(REGS_NUM-1 downto 0);
   signal set_int       : std_logic_vector(REGS_NUM-1 downto 0);
   signal clr_int_sig   : std_logic_vector(REGS_NUM-1 downto 0);
   signal reg_flags     : std_logic_vector(REGS_NUM-1 downto 0);

begin

-- ---------------------- Input Demultiplexors ----------------------
-- CLR demultiplexor
process(RESET, CLK_CLR)
begin
   if (RESET = '1') then
      clr_int <= (others => '0');
   elsif (CLK_CLR'event AND CLK_CLR = '1') then
      -- loop generetion
      clr_int <= (others => '0');
      for i in 0 to (REGS_NUM-1) loop
         if (conv_std_logic_vector(i, EXADDR) = ADDR_CLR) then
            clr_int(i) <= CLR;
         end if;
      end loop;
   end if;
end process;

-- SET demultiplexor
process(RESET, CLK_SET)
begin
   if (RESET = '1') then
      set_int <= (others => '0');
   elsif (CLK_SET'event AND CLK_SET = '1') then
      set_int <= (others => '0');
      -- loop generetion
      for i in 0 to (REGS_NUM-1) loop
         if (conv_std_logic_vector(i, EXADDR) = ADDR_SET) then
            set_int(i) <= SET;
         end if;
      end loop;
   end if;
end process;

-- ------------------------ Latch instantion ------------------------
-- Flags Latch Register Generation
REG_FLAGS_X: for i in 0 to REGS_NUM-1 generate

-- latch register instantion
clr_int_sig(i) <= clr_int(i) or RESET;
process(clr_int_sig(i), set_int(i))
begin
   if (clr_int_sig(i) = '1') then
      reg_flags(i) <= '0';
   elsif (set_int(i) = '1') then
      reg_flags(i) <= '1';
   end if;
end process;

end generate;

-- ----------------------- Output Multiplexors ----------------------
-- CLR part output multiplexor
process(RESET, CLK_CLR)
begin
   if (RESET = '1') then
      DO_CLR <= '0';
   elsif (CLK_CLR'event AND CLK_CLR = '1') then
      DO_CLR <= '0';
       -- loop generetion
      for i in 0 to (REGS_NUM-1) loop
         if (conv_std_logic_vector(i, EXADDR) = ADDR_CLR) then
            DO_CLR <= reg_flags(i);
         end if;
      end loop;
   end if;
end process;

-- SET part output multiplexor
process(RESET, CLK_SET)
begin
   if (RESET = '1') then
      DO_SET <= '0';
   elsif (CLK_SET'event AND CLK_SET = '1') then
      DO_SET <= '0';
       -- loop generetion
      for i in 0 to (REGS_NUM-1) loop
         if (conv_std_logic_vector(i, EXADDR) = ADDR_SET) then
            DO_SET <= reg_flags(i);
         end if;
      end loop;
   end if;
end process;

-- All registers output
DO_ALL <= reg_flags;

end architecture behavioral;

