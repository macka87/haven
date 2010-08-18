--
-- conv.vhd: Data width convertor for dist fifos
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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

-- library containing log2 function
--use work.math_pack.all;

--use work.cnt_types.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity conv is
   generic(
      WORD_WIDTH : integer := 8;
      DI_WORDS   : integer := 2;
      DO_WORDS   : integer := 1
   );
   port(
      RESET   : in  std_logic;
      CLK     : in  std_logic;

      -- Input interface
      DI        : in  std_logic_vector(DI_WORDS*WORD_WIDTH-1 downto 0);
      DI_DV     : in  std_logic_vector(DI_WORDS-1 downto 0);
      DI_RD     : out std_logic;
      DI_EMPTY  : in  std_logic;

      -- Output interface
      DO        : out std_logic_vector(DO_WORDS*WORD_WIDTH-1 downto 0);
      DO_DV     : out std_logic_vector(DO_WORDS-1 downto 0);
      DO_REQ    : in  std_logic
   );
end entity conv;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of conv is
      
   signal reg_di : std_logic_vector((DI_WORDS+DO_WORDS)*WORD_WIDTH-1 downto 0);
   signal reg_dv : std_logic_vector(DI_WORDS+DO_WORDS-1 downto 0);

   signal store  : std_logic;
   signal last_word : std_logic;

begin

   gen_di_gt_do: if (DI_WORDS>DO_WORDS) generate
      
      last_word <= '1' when (conv_integer(reg_dv(DO_WORDS*2-1 downto DO_WORDS))=0) else '0';
      -- ----------------------------------------------------------------------
      store <= (not DI_EMPTY) and last_word and DO_REQ;

      -- ----------------------------------------------------------------------
      gen_reg_di : for i in 0 to (DI_WORDS/DO_WORDS)-1 generate
         
         reg_di_and_reg_dv_p : process(CLK, RESET)
         begin
            if (RESET='1') then
               reg_di((i+1)*DO_WORDS*WORD_WIDTH-1 downto i*DO_WORDS*WORD_WIDTH) <= (others=>'0');
               reg_dv((i+1)*DO_WORDS-1 downto i*DO_WORDS) <= (others=>'0');
            elsif (CLK='1' and CLK'event) then
               if (store='1') then                  
                  reg_di((i+1)*DO_WORDS*WORD_WIDTH-1 downto i*DO_WORDS*WORD_WIDTH) <=
                     DI((i+1)*DO_WORDS*WORD_WIDTH-1 downto i*DO_WORDS*WORD_WIDTH);
                  reg_dv((i+1)*DO_WORDS-1 downto i*DO_WORDS) <=
                     DI_DV((i+1)*DO_WORDS-1 downto i*DO_WORDS);
               else
                  reg_di((i+1)*DO_WORDS*WORD_WIDTH-1 downto i*DO_WORDS*WORD_WIDTH) <=
                     reg_di((i+2)*DO_WORDS*WORD_WIDTH-1 downto (i+1)*DO_WORDS*WORD_WIDTH);
                  reg_dv((i+1)*DO_WORDS-1 downto i*DO_WORDS) <=
                     reg_dv((i+2)*DO_WORDS-1 downto (i+1)*DO_WORDS);
               end if;
            end if;
         end process;
         
      end generate;

      reg_di((DI_WORDS+DO_WORDS)*WORD_WIDTH-1 downto DI_WORDS*WORD_WIDTH) <= (others=>'0');
      reg_dv((DI_WORDS+DO_WORDS)-1 downto DI_WORDS) <= (others=>'0');

      DO_DV <= reg_dv(DO_WORDS-1 downto 0);
      DO    <= reg_di(DO_WORDS*WORD_WIDTH-1 downto 0);
      DI_RD <= store;


   end generate;

end architecture full;

