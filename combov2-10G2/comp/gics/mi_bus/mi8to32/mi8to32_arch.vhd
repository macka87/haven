-- mi8to32_arch.vhd: MI8 to MI32 transformer
-- Copyright (C) 2009 CESNET
-- Author(s): Vaclav Bartos <washek@liberouter.org>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--                          ARCHITECTURE DECLARATION                         --
-- ---------------------------------------------------------------------------- 

architecture behavioral of MI8TO32 is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
   
   signal byte_sel      : std_logic_vector(1 downto 0);
   signal byte_sel_reg  : std_logic_vector(1 downto 0);
   signal byte_sel_dec  : std_logic_vector(3 downto 0);
   signal dwr_reg       : std_logic_vector(23 downto 0);
   signal in_ardy_wr    : std_logic;
   signal reading_reg   : std_logic;
   signal can_read      : std_logic;
   signal read_byte_sel : std_logic_vector(1 downto 0);
   
begin
   
   -- Asserts -----------------------------------------------------------------
   assert ADDR_WIDTH >= 2
      report "ADDR_WIDTH must be at least 2."
      severity error;
   
   assert ADDR_WIDTH <= 32
      report "ADDR_WIDTH is not expected to be greater than 32."
      severity warning;
   
   -- -------------------------------------------------------------------------
   --                        MI8 to MI32 Transformer                         --
   -- -------------------------------------------------------------------------
   
   byte_sel <= IN_ADDR(1 downto 0);
   
   byte_sel_decp: process(byte_sel)
   begin
      case (byte_sel) is
         when "00"   => byte_sel_dec <= "0001";
         when "01"   => byte_sel_dec <= "0010";
         when "10"   => byte_sel_dec <= "0100";
         when "11"   => byte_sel_dec <= "1000";
         when others => byte_sel_dec <= "XXXX";
      end case;
   end process;
   
   
   -- write -------------------------------------------------------------------
   
   BE_SUP: if (BE_SUPPORTED = true) generate
      OUT_DWR(7 downto 0)   <= IN_DWR;
      OUT_DWR(15 downto 8)  <= IN_DWR;
      OUT_DWR(23 downto 16) <= IN_DWR;
      OUT_DWR(31 downto 24) <= IN_DWR;
      
      OUT_ADDR   <= IN_ADDR(ADDR_WIDTH-1 downto 2) & "00";
      OUT_BE     <= byte_sel_dec;
      OUT_WR     <= IN_WR;
      in_ardy_wr <= OUT_ARDY;
   end generate;
   
   BE_NOT_SUP: if (BE_SUPPORTED = false) generate
      -- Register to accumulate all 32bits of data before sending
      dwr_regp: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (IN_WR = '1' and byte_sel_dec(0) = '1') then
               dwr_reg( 7 downto  0) <= IN_DWR;
            end if;
            if (IN_WR = '1' and byte_sel_dec(1) = '1') then
               dwr_reg(15 downto  8) <= IN_DWR;
            end if;
            if (IN_WR = '1' and byte_sel_dec(2) = '1') then
               dwr_reg(23 downto 16) <= IN_DWR;
            end if;
         end if;
      end process;
      
      OUT_DWR(23 downto  0) <= dwr_reg;
      OUT_DWR(31 downto 24) <= IN_DWR;
   
      OUT_ADDR   <= IN_ADDR(ADDR_WIDTH-1 downto 2) & "00";
      OUT_BE     <= "1111";
      OUT_WR     <= IN_WR and byte_sel_dec(3);
      in_ardy_wr <= not byte_sel_dec(3) or OUT_ARDY;
   end generate;
   
   
   -- read --------------------------------------------------------------------
   reading_regp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reading_reg <= '0';
         elsif (IN_RD = '1' and OUT_ARDY = '1') then
            reading_reg <= '1';
         end if;
         if (OUT_DRDY = '1') then
            reading_reg <= '0';
         end if;
      end if;
   end process;
   
   can_read <= not reading_reg;
   
   OUT_RD  <= IN_RD    and can_read;
   IN_ARDY <= (OUT_ARDY and can_read) or in_ardy_wr;
   
   byte_sel_regp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (can_read = '1') then
            byte_sel_reg <= byte_sel;
         end if;
      end if;
   end process;
   
   with reading_reg select read_byte_sel <= byte_sel     when '0',
                                            byte_sel_reg when others;
   
   with read_byte_sel select IN_DRD <= OUT_DRD(7 downto 0)   when "00",
                                       OUT_DRD(15 downto 8)  when "01",
                                       OUT_DRD(23 downto 16) when "10",
                                       OUT_DRD(31 downto 24) when others;
   
   IN_DRDY <= OUT_DRDY;
   
end behavioral;
