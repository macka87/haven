--
-- crc32_64b.vhd: 32-bit CRC module processing 64 bits in parallel
-- Copyright (C) 2006 CESNET
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

entity crc32_64b is
    port(
        DI: in std_logic_vector(63 downto 0);
        DI_DV: in std_logic;
        EOP: in std_logic;
        MASK: in std_logic_vector(2 downto 0);
        CLK: in std_logic;
        RESET: in std_logic;
        
        CRC: out std_logic_vector(31 downto 0);
        DO_DV: out std_logic
   );
end entity crc32_64b;

architecture crc32_64b_arch of crc32_64b is

   signal crc_reg: std_logic_vector(63 downto 0);
   signal dctl, tctl, tval, deop : std_logic;
   signal reg_low, reg_low_data, crctab_do : std_logic_vector(31 downto 0);
   signal mx_di : std_logic_vector(31 downto 0);

   signal reg_mask : std_logic_vector(2 downto 0);
   signal reg_di : std_logic_vector(63 downto 0);
   signal reg_eop_in : std_logic;
   signal reg_mask_in : std_logic_vector(2 downto 0);
   signal reg_di_dv : std_logic;
    
begin

crc32_64b_tab_instance: entity work.crc32_64b_tab
port map(
   DI => crc_reg,
   MASK => reg_mask,
   DO => crctab_do
);

crc32_64b_fsm_instance: entity work.crc32_64b_fsm
port map(
    CLK => CLK,
    RESET => RESET,
    DI_DV => reg_di_dv,
    EOP => reg_eop_in,
    
    DCTL => dctl,
    TCTL => tctl,
    TVAL => tval
);



   -- register reg_di -------------------------------------------------
   reg_dip: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_di <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         reg_di <= DI(63 downto 32) & mx_di;
      end if;
   end process;


   -- register reg_di_dv -------------------------------------------------
   reg_di_dvp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_di_dv <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_di_dv <= DI_DV;
      end if;
   end process;



   -- register reg_eop_in -------------------------------------------------
   reg_eop_inp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_eop_in <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_eop_in <= EOP;
      end if;
   end process;


   -- register reg_mask_in -------------------------------------------------
   reg_mask_inp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_mask_in <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
        reg_mask_in <= MASK;
      end if;
   end process;


crc_reg_proc: process(CLK, RESET)
begin
    if RESET = '1' then
        crc_reg <= (others => '0');
    elsif CLK'event AND clk = '1' then
        if reg_di_dv = '1' OR tval = '1' then
            crc_reg <= reg_di(63 downto 32) & reg_low;
        end if;
    end if;
end process;

process(CLK, RESET)
begin
    if RESET = '1' then
       deop <= '0';
    elsif CLK = '1' AND CLK'event then
       deop <= reg_eop_in;
    end if;
end process;
    
process(CLK, RESET)
begin
    if RESET = '1' then
       DO_DV <= '0';
    elsif CLK = '1' AND CLK'event then
       DO_DV <= deop;
    end if;
end process;


-- register reg_mask -------------------------------------------------
reg_maskp: process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_mask <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      reg_mask <= reg_mask_in;
   end if;
end process;


-- mx_di multiplexor - handles special situation when MASK > 4
mx_dip: process(MASK, DI, EOP)
begin
   mx_di <= DI(31 downto 0);

   if (EOP = '1') then
      case MASK is
         when "101"  => mx_di <=     X"00" & DI(23 downto 0);
         when "110"  => mx_di <=   X"0000" & DI(15 downto 0);
         when "111"  => mx_di <= X"000000" & DI(7 downto 0);
         when others => null;
      end case;
   end if;
end process;

reg_low_data <= crctab_do XOR reg_di(31 downto 0) when (tctl = '0') else
                NOT reg_di(31 downto 0);

reg_low <= reg_low_data when (dctl = '0') else
           crctab_do;
             
CRC <= NOT (crc_reg(7 downto 0) & crc_reg(15 downto 8) & crc_reg(23 downto 16)
            & crc_reg(31 downto 24));

end architecture crc32_64b_arch;
