--
-- cnt.vhd: Fast counter with generic width and direction
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

use WORK.cnt_types.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cnt is
   generic (
      WIDTH : integer := 32;
      DIR   : TCNT := up;
      CLEAR : boolean := false
   );
   port(
      RESET     : in  std_logic;
      CLK       : in  std_logic;
      CE        : in  std_logic;
      CLR       : in  std_logic;
      DO        : out std_logic_vector(WIDTH-1 downto 0)
   );
end entity cnt;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of cnt is

signal cnt_i   : std_logic_vector(WIDTH-1 downto 0);
signal reg_cnt : std_logic_vector(WIDTH-1 downto 0);
signal xo      : std_logic_vector(WIDTH-1 downto 0);
signal s       : std_logic_vector(WIDTH-1 downto 0);
signal cin     : std_logic_vector(WIDTH-1   downto 0);
signal muxin   : std_logic;

component MUXCY_L
  port( DI : in std_logic;
        CI : in std_logic;
        S  : in std_logic;
        LO : out std_logic);
end component;

component XORCY
  port( LI : in std_logic;
        CI : in std_logic;
        O : out std_logic);
end component;

component LUT1_L
   generic(
      INIT : bit_vector
   );
   port(
      I0 : in std_logic;
      LO : out std_logic
   );
end component;

begin
   -- generate only register with negated output...
   gen_width_1_clear: if (WIDTH=1 and CLEAR=true) generate
      cnt_p: process(RESET, CLK)
      begin
         if (RESET='1') then
            reg_cnt <= (others=>'0');
         elsif (CLK'event and CLK='1') then
            if (CLR='1') then
               reg_cnt <= (others=>'0');
            elsif (CE='1') then
               reg_cnt <= not reg_cnt;
            end if;
         end if;
      end process;
   end generate;

   -- generate only register with negated output...
   gen_width_1: if (WIDTH=1 and CLEAR=false) generate
      cnt_p: process(RESET, CLK)
      begin
         if (RESET='1') then
            reg_cnt <= (others=>'0');
         elsif (CLK'event and CLK='1') then
            if (CE='1') then
               reg_cnt <= not reg_cnt;
            end if;
         end if;
      end process;
   end generate;

   
   gen_width_gt1: if (WIDTH>1) generate         

      -- generate cin(0) and muxin for up counter
      gen_cin0_up: if (DIR=up) generate
         cin(0) <= '1';
         muxin  <= '0';
      end generate;

      -- generate cin(0) and muxin for down counter
      gen_cin0_down: if (DIR=down) generate
         cin(0) <= '0';
         muxin  <= '1';
      end generate;

      -- generate cnt_i for counter without clear
      gen_cnt_i: if (CLEAR=false) generate
         cnt_i <= xo;
      end generate;

      -- generate cnt_i for counter with clear
      gen_cnt_i_clear: if (CLEAR=true) generate
         gen_cnt_i_clear_loop: for i in 0 to WIDTH-1 generate
            cnt_i(i) <= xo(i) and not CLR;
         end generate;
      end generate;

      gen_muxcy_l:
      for i in 0 to WIDTH-2 generate
         MUXCY_L_U: MUXCY_L
         port map(
            DI => muxin,
            CI => cin(i),
            S  => s(i),
            LO => cin(i+1)
         );
      end generate;

      gen_lut1_l:
      for i in 0 to WIDTH-1 generate
         -- generate lut for up counter
         gen_init_const_up: if (DIR=up) generate
            LUT1_L_U: LUT1_L
            generic map(
               INIT => X"2" -- sets identity
            )
            port map(
               I0 => reg_cnt(i),
               LO => s(i)
            );
         end generate;

         -- generate lut for down counter
         gen_init_const_down: if (DIR=down) generate
            LUT1_L_U: LUT1_L
            generic map(
               INIT => X"1" -- sets negation
            )
            port map(
               I0 => reg_cnt(i),
               LO => s(i)
            );
         end generate;
      end generate;

      gen_xorcy:
      for i in 0 to WIDTH-1 generate
         XORCY_U: XORCY
         port map(
            LI => s(i),
            CI => cin(i),
            O  => xo(i)
         );
      end generate;

      reg_cnt_p: process (RESET, CLK)
      begin
         if (RESET='1') then
            reg_cnt <= (others=>'0');
         elsif (CLK='1' and CLK'event) then
            if (CE='1' or CLR='1') then
               reg_cnt <= cnt_i;
            end if;
         end if;
      end process;
   
   end generate;

   DO <= reg_cnt;

end architecture full;

