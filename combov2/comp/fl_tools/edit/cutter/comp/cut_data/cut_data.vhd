-- cut_data.vhd: FrameLink cutter: cut data logic
-- (extract and optionally remove data on defined offset in defined frame part)
-- Copyright (C) 2008 CESNET
-- Author(s): Bronislav Pribyl <xpriby12@stud.fit.vutbr.cz>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of cut_data is

   -- ============================== SIGNALS ===================================
   signal ls_byte        : std_logic_vector(log2(MAX_PART_SIZE/DATA_BYTES)+log2(DATA_BYTES)-1 downto 0);
   signal cut_data_en : std_logic_vector(SIZE - 1 downto 0);
   
   
begin

   ls_byte <= WORD_NUM & conv_std_logic_vector(0, log2(DATA_BYTES));

   Cut_data_reg_array:for i in 0 to SIZE - 1 generate

      -- cut data enable MUX
      process(ls_byte, PART_NUM, TRANSMIT_PROGRESS)
      begin
         if (
            conv_std_logic_vector((OFFSET + i), ls_byte'length) >= ls_byte
               and
            conv_std_logic_vector(PART, PART_NUM'length) = PART_NUM
               and
            TRANSMIT_PROGRESS = '1'
         ) then
            cut_data_en(i) <= '1';
         else
            cut_data_en(i) <= '0';
         end if;
      end process;

      -- cut data registers
      process(CLK) -- no need for RESET
      begin
         if (CLK'event and CLK = '1') then
            if (cut_data_en(i) = '1') then
               CUT_DATA(8 * (i+1) - 1 downto 8 * i)
                  <= DATA(
                        (((OFFSET+i) mod DATA_BYTES) + 1) * 8 - 1
                           downto
                        ((OFFSET+i) mod DATA_BYTES) * 8
                     );
            end if;
         end if;
      end process;

   end generate;

end architecture full;
