-- arbiter.vhd : Unit for selecting address of next '1' item from vector
-- Copyright (C) 2006 CESNET
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
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity arbiter is
   generic(
      VECTOR_WIDTH : integer := 16  -- Must be X**2
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      -- Vector to search in
      VECTOR   : in  std_logic_vector(VECTOR_WIDTH-1 downto 0);
      -- Write actual nearest '1' address to output
      STEP     : in  std_logic;

      -- Output with nearest '1' found
      ADDR     : out std_logic_vector(LOG2(VECTOR_WIDTH)-1 downto 0);
      -- Is '1' if any bit of VECTOR is '1'
      VLD      : out std_logic
   );
end entity arbiter;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture arbiter_arch of arbiter is

signal cnt_search    : std_logic_vector(LOG2(VECTOR_WIDTH)-1 downto 0);
signal best_search   : std_logic_vector(LOG2(VECTOR_WIDTH)-1 downto 0);
signal current       : std_logic_vector(LOG2(VECTOR_WIDTH)-1 downto 0);
signal mux_out       : std_logic_vector(0 downto 0);
signal sig_vld       : std_logic_vector(0 downto 0);
signal reg_vld       : std_logic;

begin

-- This register stores current arbiter output.
current_p : process(CLK, RESET)
begin
   if RESET = '1' then
      current <= (others => '0');
   elsif CLK'event and CLK = '1' then
      if STEP = '1' then
         current <= best_search;
      end if;
   end if;
end process;

-- This multiplexer selects one bit from VECTOR. Address is cnt_search value
search_mux : entity work.GEN_MUX
generic map(
   DATA_WIDTH  => 1,
   MUX_WIDTH   => 16
)
port map(
   DATA_IN     => VECTOR,
   SEL         => cnt_search,
   DATA_OUT    => mux_out
);

-- This multiplexer performs check when STEP is performed
vld_mux : entity work.GEN_MUX
generic map(
   DATA_WIDTH  => 1,
   MUX_WIDTH   => 16
)
port map(
   DATA_IN     => VECTOR,
   SEL         => best_search,
   DATA_OUT    => sig_vld
);

-- This register stores nearest '1' found from current position in the vector.
best_search_p : process(CLK, RESET)
begin
   if RESET = '1' then
      best_search <= (others => '0');
   elsif CLK'event and CLK = '1' then
      if mux_out = "1" and cnt_search /= current then
         best_search <= cnt_search;
      end if;
   end if;
end process;

-- This counter goes up and searches for first '1'. Then it goes back to
-- current position and makes next search.
cnt_search_p : process(CLK, RESET)
begin
   if RESET = '1' then
      cnt_search <= (others => '0');
   elsif CLK'event and CLK = '1' then
      if mux_out = "1" and cnt_search /= current then
         cnt_search <= current;  -- Found '1'
      else
         cnt_search <= cnt_search + 1; -- Continue searching
      end if;
   end if;
end process;

reg_vld_p : process(CLK, RESET)
begin
   if RESET = '1' then
      reg_vld <= '0';
   elsif CLK'event and CLK = '1' then
      if STEP = '1' then
         reg_vld <= sig_vld(0);
      end if;
   end if;
end process;

ADDR <= current;
VLD  <= reg_vld;

end architecture arbiter_arch;
