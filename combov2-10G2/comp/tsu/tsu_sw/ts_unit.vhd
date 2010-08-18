-- ts_unit.vhd: architecture of timestamp unit
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03 at stud.fit.vutbr.cz>
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
-- TODO:
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of ts_unit is
   -- Signals in architecture
   signal reg_realtime		: std_logic_vector(95 downto 0) := X"000000000000000000000000";
   signal incr_value		: std_logic_vector(39 downto 0) := X"0000000000";
   signal correlation           : std_logic;
   signal sel_reg_rtr_low	: std_logic;
   signal sel_reg_rtr_high	: std_logic;
   signal sel_reg_incr_val_low	: std_logic;
   signal sel_reg_incr_val_high	: std_logic;
   signal reg_rtr_low_we	: std_logic;
   signal reg_rtr_high_we	: std_logic;
   signal reg_incr_val_low_we	: std_logic;
   signal reg_incr_val_high_we	: std_logic;
   signal reg_rtr_low_re	: std_logic;

begin
-- -------------------------------------------------------
TS <= reg_realtime(95 downto 32);
TS_DV <= '1'; -- this unit will provide timestamp every count

ARDY <= '1'; -- ARDY constantly set

-- -------------------------------------------------------
-- RTR (real-time register)
reg_rtr : process(CLK)
begin
   if (CLK'event and CLK = '1') then
      if (reg_rtr_low_we = '1') then
	 if (BE(0) = '1') then reg_realtime(39 downto 32) <= DWR(7 downto 0); end if;
	 if (BE(1) = '1') then reg_realtime(47 downto 40) <= DWR(15 downto 8); end if;
	 if (BE(2) = '1') then reg_realtime(55 downto 48) <= DWR(23 downto 16); end if;
	 if (BE(3) = '1') then reg_realtime(63 downto 56) <= DWR(31 downto 24); end if;
      elsif (reg_rtr_high_we = '1') then
	 if (BE(0) = '1') then reg_realtime(71 downto 64) <= DWR(7 downto 0); end if;
	 if (BE(1) = '1') then reg_realtime(79 downto 72) <= DWR(15 downto 8); end if;
	 if (BE(2) = '1') then reg_realtime(87 downto 80) <= DWR(23 downto 16); end if;
	 if (BE(3) = '1') then reg_realtime(95 downto 88) <= DWR(31 downto 24); end if;
      elsif (correlation = '1') then
         reg_realtime <= reg_realtime + incr_value + incr_value;
      else
         reg_realtime <= reg_realtime + incr_value;
      end if;
   end if;
end process reg_rtr;

-- --------------------------------------------------------------------------------
-- Incremental value register
reg_incr_value : process(CLK)
begin
   if (CLK'event and CLK = '1') then
      if (reg_incr_val_low_we = '1') then
	 if (BE(0) = '1') then incr_value(7 downto 0) <= DWR(7 downto 0); end if;
	 if (BE(1) = '1') then incr_value(15 downto 8) <= DWR(15 downto 8); end if;
	 if (BE(2) = '1') then incr_value(23 downto 16) <= DWR(23 downto 16); end if;
	 if (BE(3) = '1') then incr_value(31 downto 24) <= DWR(31 downto 24); end if;
      elsif (reg_incr_val_high_we = '1') then
         if (BE(0) = '1') then incr_value(39 downto 32) <= DWR(7 downto 0); end if;
      end if;
   end if;
end process reg_incr_value;

-- --------------------------------------------------------------------------------
-- Correlation register. When there is an RTR update, there is no incr_value added for
-- one count. Therefore correlation is set and in next count is 2*incr_value added into RTR
reg_correlation : process(CLK)
begin
   if (CLK'event and CLK = '1') then
      correlation <= reg_rtr_low_we or reg_rtr_high_we;
   end if;
end process reg_correlation;

-- --------------------------------------------------------------------------------
-- Register MI32.DRDY (output data ready)
reg_mi32_drdy : process(CLK, RESET)
begin
   if (RESET = '1') then
      DRDY <= '0';      
   elsif (CLK'event and CLK = '1') then
      DRDY <= RD;
   end if;
end process reg_mi32_drdy;

-- --------------------------------------------------------------------------------
-- Register MI32.DRD (data output)
reg_mi32_drd : process(CLK)
begin
   if (CLK'event and CLK = '1') then
      if (reg_rtr_low_re = '1') then
          DRD <= reg_realtime(63 downto 32);
      else
          DRD <= reg_realtime(95 downto 64);
      end if;
   end if;
end process reg_mi32_drd;

-- --------------------------------------------------------------------------------
-- Choose register by address in MI32.ADDR
select_register : process(ADDR)
begin
   -- Implicit values of select
   sel_reg_rtr_low <= '0';
   sel_reg_rtr_high <= '0';
   sel_reg_incr_val_low <= '0';
   sel_reg_incr_val_high <= '0';

   case (ADDR(31 downto 0)) is
      when X"00000000" => sel_reg_rtr_low <= '1';   	-- Lower part of input register for timestamp from SW (RTR)
      when X"00000004" => sel_reg_rtr_high <= '1';   	-- Higher part of input register for timestamp from SW (RTR)
      when X"00000008" => sel_reg_incr_val_low <= '1';	-- Lower part of incremental value register
      when X"0000000C" => sel_reg_incr_val_high <= '1';	-- Higher part of incremental value register
      when others => null;
   end case;

end process select_register;

-- --------------------------------------------------------------------------------
-- Set write enable into register
reg_rtr_low_we <= sel_reg_rtr_low and WR;
reg_rtr_high_we <= sel_reg_rtr_high and WR;
reg_incr_val_low_we <= sel_reg_incr_val_low and WR;
reg_incr_val_high_we <= sel_reg_incr_val_high and WR;

-- --------------------------------------------------------------------------------
-- Set read enable from register
reg_rtr_low_re <= sel_reg_rtr_low and RD;

end architecture behavioral;
