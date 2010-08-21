--
-- epi2mi_converter_arch.vhd: Endpoint Interface to MI Converter
-- Copyright (C) 2008 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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

architecture epi2mi_converter_arch of EPI2MI_CONVERTER is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal cnt        : std_logic_vector(3 downto 0);
   signal cnt_up     : std_logic;
   signal cnt_down   : std_logic;
   signal full       : std_logic;
   signal empty      : std_logic;
   
begin
   
   -- Asserts -----------------------------------------------------------------
   assert DATA_WIDTH > 0 and ADDR_WIDTH > 0
      report "DATA_WIDTH and ADDR_WIDTH must be positive values."
      severity error;
   
   assert DATA_WIDTH =  8 or DATA_WIDTH = 16 or DATA_WIDTH = 32 or
          DATA_WIDTH = 64 or DATA_WIDTH = 128
      report "DATA_WIDTH is expected to be one of {8,16,32,64,128}."
      severity warning;
   
   assert ADDR_WIDTH <= 32
      report "ADDR_WIDTH is not expected to be greater than 32."
      severity warning;
   
   -- -------------------------------------------------------------------------
   --                           EPI2MI_CONVERTER                             --
   -- -------------------------------------------------------------------------
   
   MI_DWR      <= WR_DATA;
   MI_RD       <= RD_REQ and not full;
   MI_WR       <= WR_REQ;
   
   with WR_REQ select MI_ADDR <= WR_ADDR when '1',
                                 RD_ADDR when others;
   with WR_REQ select MI_BE   <= WR_BE when '1',
                                 RD_BE when others;
   
   WR_RDY         <= MI_ARDY;
   RD_ARDY_ACCEPT <= MI_ARDY and not full;
   RD_SRC_RDY     <= not empty;
   
   with cnt select full <= '1' when "1111",
                           '0' when others;
   
   FIFO : entity work.SH_FIFO
   generic map (
      FIFO_WIDTH    => DATA_WIDTH,
      FIFO_DEPTH    => 16,
      USE_INREG     => false,
      USE_OUTREG    => false
   )
   port map (
      CLK      => CLK,
      RESET    => RESET,
      
      DIN      => MI_DRD,
      WE       => MI_DRDY,
      
      DOUT     => RD_DATA,
      RE       => RD_DST_RDY,
      EMPTY    => empty
      
   );
   
   cnt_up   <= RD_REQ and MI_ARDY and not full;
   cnt_down <= RD_DST_RDY and not empty; 
   
   cntp: process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt <= "0000";
         else
            if (cnt_up = '1' and cnt_down = '1') then
               cnt <= cnt;
            elsif (cnt_up = '1') then
               cnt <= cnt + 1;
            elsif (cnt_down = '1') then
               cnt <= cnt - 1;
            end if;
         end if;
      end if;
   end process;
   
   
end epi2mi_converter_arch;


