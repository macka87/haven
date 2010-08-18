-- decompress_any.vhd: Frame Link protocol signals decompressor 
-- (Any number of parts)
-- Copyright (C) 2007 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

entity fl_decompress_any is
   generic(
      WIRES : integer := 1;-- 1, 2, or 4
      PARTS : integer      -- No default value - user must provide value
   );
   port(
      -- Common interface
      CLK            : in  std_logic;
      RESET          : in  std_logic;
      
      -- Transmit interface
      TX_SRC_RDY_N   : in  std_logic;
      TX_DST_RDY_N   : in  std_logic; -- Is input, because this comp does not
                                      -- perform flow control.
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      
      FL_JUICE       : in  std_logic_vector(WIRES-1 downto 0); 
         -- Compressed FL control signals
         
      DISCARD        : in  std_logic  -- Next item is SOF & SOP
   );
end entity fl_decompress_any;

architecture full of FL_DECOMPRESS_ANY is

signal cnt_parts     : std_logic_vector(log2(PARTS) downto 0);
   -- Counter of passed parts

signal reg_sop_n  : std_logic;   -- Registering EOP gives us SOP
signal reg_sof_n  : std_logic;   -- Registering EOF gives us SOF
signal sig_eof_n  : std_logic;   -- Computed value of control signal


begin

-- This counter counts the number of current frame parts
cnt_parts_p : process(CLK, RESET)
begin
   if(CLK'event and CLK = '1') then
      if RESET = '1' then
         cnt_parts <= (others => '0');
      else
         if TX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' and FL_JUICE(0) = '0'
            and cnt_parts = PARTS-1 then
            cnt_parts <= (others => '0');
         elsif TX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' and 
            FL_JUICE(0) = '0' then
            cnt_parts <= cnt_parts + 1;
         end if;
      end if;
   end if;
end process;

-- Registering EOP_N (with respect to RDY signals) gives SOP_N
reg_sop_n_p: process(CLK, RESET)
begin
   if(CLK'event and CLK = '1') then
      if(RESET='1' or DISCARD='1') then
         reg_sop_n <= '0';
      else
         if(TX_DST_RDY_N = '0' and TX_SRC_RDY_N = '0') then
            reg_sop_n <= FL_JUICE(0);
         end if;
      end if;
   end if;
end process;

-- Registering EOF_N (with respect to RDY signals) gives SOF_N
reg_sof_n_p: process(CLK, RESET)
begin
   if(CLK'event and CLK = '1') then
      if(RESET='1' or DISCARD='1') then
         reg_sof_n <= '0';
      else
         if(TX_DST_RDY_N = '0' and TX_SRC_RDY_N = '0') then
            reg_sof_n <= sig_eof_n;
         end if;
      end if;
   end if;
end process;

-- Output mapping
TX_EOP_N <= FL_JUICE(0);
TX_EOF_N <= sig_eof_n;

wire1n_cond : if(WIRES > 1) generate
   sig_eof_n <= FL_JUICE(1);
end generate;

wire1_cond : if(WIRES = 1) generate
   sig_eof_n <= '0' when (FL_JUICE(0) = '0' and cnt_parts = PARTS-1)
                    else
                '1';
end generate;

wire4n_cond : if(WIRES < 4) generate
   TX_SOP_N <= reg_sop_n;
   TX_SOF_N <= reg_sof_n;
end generate;

wire4_cond : if(WIRES = 4) generate
   TX_SOP_N <= FL_JUICE(2);
   TX_SOF_N <= FL_JUICE(3);
end generate;

end architecture full;


