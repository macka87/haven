-- fl_stat_arch.vhd: Architecture of Frame link stat unit
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 and min functions
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture full of FL_STAT is

type fl_cnt_array is array(IFCS - 1 downto 0) of std_logic_vector(31 downto 0); -- max 255 ifcs

-- ----------------------------------------------------------------------------
--                          Signals in architecture
-- ----------------------------------------------------------------------------
-- counters and registers signals
signal state            : std_logic_vector( 2 downto 0);
signal state_reg        : std_logic_vector(31 downto 0);
signal clk_cnt          : std_logic_vector(31 downto 0);
signal src_cnt          : fl_cnt_array;
signal dst_cnt          : fl_cnt_array;
signal both_cnt         : fl_cnt_array;

-- mux signals
signal data_out         : std_logic_vector(31 downto 0);

-- select signals
signal sel_state        : std_logic;

-- write enable signals
signal state_we         : std_logic;

-- read enable signals
signal state_re         : std_logic;

begin

ARDY <= '1';

   -- -------------------------------------------------------
   -- state register - 32 bits
   --           -----------------------------------------
   -- bit index | 31 | 30 | 29 | 28 | 27 | 26 | 25 | 24 |
   --           -----------------------------------------
   -- function  |    |    |    |    |    |    |    |    |
   --           -----------------------------------------
   -- bit index | 23 | 22 | 21 | 20 | 19 | 18 | 17 | 16 |
   --           -----------------------------------------
   -- function  |    |    |    |    |    |    |    |    |
   --           -----------------------------------------
   -- bit index | 15 | 14 | 13 | 12 | 11 | 10 |  9 |  8 |
   --           -----------------------------------------
   -- function  |     Number of watched interfaces      |
   --           -----------------------------------------
   -- bit index |  7 |  6 |  5 |  4 |  3 |  2 |  1 |  0 |
   --           -----------------------------------------
   -- function  |    |    |    |    |    | CO | RC | CE |
   --           -----------------------------------------
   --
   -- Meaning of abbreviations:
   --    CE = count enable
   --    RC = reset counters
   --    CO = clock cycles counter owerflow
   --  Empty cells are reserved for future purposes
   state_reg <= X"0000" & conv_std_logic_vector(IFCS, 8) & "00000" & state; -- bits 32 downto 3 are constant or reserved for future purposes

   reg_state : process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1' or state(1) = '1') then
            state <= "000";
         elsif (clk_cnt = X"11111111") then -- what if there is write request into state_reg?
            state(2) <= '1';
         elsif (state_we = '1' and BE(0) = '1') then
            state(1 downto 0) <= DWR(1 downto 0);
         end if;
      end if;
   end process reg_state;

   -- -------------------------------------------------------
   -- counter of clock cycles
   clk_cycle_cnt : process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1' or state(1) = '1') then
            clk_cnt <= (others => '0');
         elsif (state(0) = '1') then
            clk_cnt <= clk_cnt + 1;
         end if;
      end if;
   end process clk_cycle_cnt;


   ifc_counters_gen : for i in 0 to IFCS - 1 generate
      -- -------------------------------------------------------
      -- counter when src is ready and dst is not
      src_active_cnt : process(RESET, CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1' or state(1) = '1') then
               src_cnt(i) <= (others => '0');
	    elsif (state(0) = '1' and SRC_RDY_N(i) = '0' and DST_RDY_N(i) = '1') then
               src_cnt(i) <= src_cnt(i) + 1;
	    end if;
         end if;
      end process src_active_cnt;

      -- -------------------------------------------------------
      -- counter when dst is ready and src is not
      dst_active_cnt : process(RESET, CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1' or state(1) = '1') then
               dst_cnt(i) <= (others => '0');
	    elsif (state(0) = '1' and SRC_RDY_N(i) = '1' and DST_RDY_N(i) = '0') then
               dst_cnt(i) <= dst_cnt(i) + 1;
	    end if;
         end if;
      end process dst_active_cnt;

      -- -------------------------------------------------------
      -- counter when both are ready
      both_active_cnt : process(RESET, CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1' or state(1) = '1') then
               both_cnt(i) <= (others => '0');
	    elsif (state(0) = '1' and SRC_RDY_N(i) = '0' and DST_RDY_N(i) = '0') then
               both_cnt(i) <= both_cnt(i) + 1;
	    end if;
         end if;
      end process both_active_cnt;
   end generate;


   -- -------------------------------------------------------
   -- Register MI32.DRDY (output data ready)
   reg_mi32_drdy : process(CLK, RESET)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            DRDY <= '0';
         else
            DRDY <= RD;
         end if;
      end if;
   end process reg_mi32_drdy;

   -- -------------------------------------------------------
   -- Register MI32.DRD (data output)
   reg_mi32_drd : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            DRD <= (others => '0');
         elsif (state_re = '1') then
            DRD <= state_reg;
         else
            DRD <= data_out;
         end if;
      end if;
   end process reg_mi32_drd;

   -- -------------------------------------------------------
   -- Choose register by address in MI32.ADDR
   select_register : process(ADDR, clk_cnt, src_cnt, dst_cnt, both_cnt)
   begin
      -- Implicit values of select
      sel_state    <= '0';
      data_out     <= (others => '0');

      case (ADDR(11 downto 0)) is
         when X"000" => sel_state     <= '1';       -- state register
         when X"004" => data_out <= clk_cnt;
         when others => null;
      end case;

      for i in 0 to IFCS - 1 loop                        -- interfaces loop
         if (conv_integer(ADDR(11 downto 4)) = i+1) then -- particular interface match
            case (ADDR(3 downto 0)) is                   -- select particular counter of particular interface
               when X"0" => data_out <= src_cnt(i);
               when X"4" => data_out <= dst_cnt(i);
               when X"8" => data_out <= both_cnt(i);
               when others => null;
            end case;
         end if;
      end loop;

   end process select_register;

   -- -------------------------------------------------------
   -- Set write enable into register
   state_we <= sel_state and WR;

   -- -------------------------------------------------------
   -- Set read enable from register
   state_re <= sel_state and RD;

end architecture full;
