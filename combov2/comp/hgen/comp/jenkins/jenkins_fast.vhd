-- jenkins_fast.vhd: Jenkins hash function module with 
-- Copyright (C) 2008 CESNET
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
use IEEE.std_logic_unsigned.all;
use IEEE.numeric_std.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity jenkins is
   generic(
      INTERFACES : integer := 4;
      UH_SIZE    : integer := 64
   );
   port(
      CLK               : in  std_logic;
      RESET             : in  std_logic;

      DATA_IN           : in  std_logic_vector(95 downto 0);
      STATE             : in  std_logic_vector(95 downto 0);
      DATA_IN_VLD       : in  std_logic;
      DATA_IN_NEXT      : out std_logic;
      CONTEXT_IN_VLD    : in  std_logic;
      CONTEXT_IN_NEXT   : out std_logic;
      CONTEXT_IN        : in  std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
      INPUT_TYPE        : in  std_logic;

      SEED              : in  std_logic_vector(31 downto 0);

      DATA_OUT          : out std_logic_vector(95 downto 0);
      CONTEXT_OUT       : out std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
      DATA_OUT_RDY      : out std_logic;
      DATA_OUT_NEXT     : in  std_logic;
      CONTEXT_OUT_RDY   : out std_logic;
      CONTEXT_OUT_NEXT  : in  std_logic
   );
end entity jenkins;


-- ----------------------------------------------------------------------------
--                        Architecture description
-- ----------------------------------------------------------------------------
architecture full of jenkins is

   -- magic constant for jenkins hash
   constant magic : std_logic_vector(31 downto 0) := X"9e3779b9";
   signal zeros   : std_logic_vector(31 downto 0);

   -- Stage 0 signals
   signal a0      : std_logic_vector(31 downto 0);
   signal b0      : std_logic_vector(31 downto 0);
   signal c0      : std_logic_vector(31 downto 0);
   signal context0: std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal s0rdy   : std_logic;
   signal s0next  : std_logic;
   signal s0en    : std_logic;
   signal cont_s0rdy : std_logic;
   signal cont_s0next: std_logic;
   signal cont_s0en  : std_logic;

   -- Stage 1 signals
   signal a1      : std_logic_vector(31 downto 0);
   signal b1      : std_logic_vector(31 downto 0);
   signal c1      : std_logic_vector(31 downto 0);
   signal context1: std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal s1rdy   : std_logic;
   signal s1next  : std_logic;
   signal s1en    : std_logic;

   -- Stage 2 signals
   signal a2      : std_logic_vector(31 downto 0);
   signal b2      : std_logic_vector(31 downto 0);
   signal c2      : std_logic_vector(31 downto 0);
   signal context2: std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal s2rdy   : std_logic;
   signal s2next  : std_logic;
   signal s2en    : std_logic;

   -- Stage 3 signals
   signal a3      : std_logic_vector(31 downto 0);
   signal b3      : std_logic_vector(31 downto 0);
   signal c3      : std_logic_vector(31 downto 0);
   signal context3: std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal s3rdy   : std_logic;
   signal s3next  : std_logic;
   signal s3en    : std_logic;
   signal cont_s3rdy : std_logic;
   signal cont_s3next: std_logic;
   signal cont_s3en  : std_logic;

   -- Stage 4 signals
   signal a4      : std_logic_vector(31 downto 0);
   signal b4      : std_logic_vector(31 downto 0);
   signal c4      : std_logic_vector(31 downto 0);
   signal context4: std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal s4rdy   : std_logic;
   signal s4next  : std_logic;
   signal s4en    : std_logic;

   -- Stage 5 signals
   signal a5      : std_logic_vector(31 downto 0);
   signal b5      : std_logic_vector(31 downto 0);
   signal c5      : std_logic_vector(31 downto 0);
   signal context5: std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal s5rdy   : std_logic;
   signal s5next  : std_logic;
   signal s5en    : std_logic;

   -- Stage 6 signals
   signal a6      : std_logic_vector(31 downto 0);
   signal b6      : std_logic_vector(31 downto 0);
   signal c6      : std_logic_vector(31 downto 0);
   signal context6: std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal s6rdy   : std_logic;
   signal s6next  : std_logic;
   signal s6en    : std_logic;

   -- Stage 7 signals
   signal a7      : std_logic_vector(31 downto 0);
   signal b7      : std_logic_vector(31 downto 0);
   signal c7      : std_logic_vector(31 downto 0);
   signal context7: std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal s7rdy   : std_logic;
   signal s7next  : std_logic;
   signal s7en    : std_logic;
   signal cont_s7rdy : std_logic;
   signal cont_s7next: std_logic;
   signal cont_s7en  : std_logic;

   -- Stage 8 signals
   signal a8      : std_logic_vector(31 downto 0);
   signal b8      : std_logic_vector(31 downto 0);
   signal c8      : std_logic_vector(31 downto 0);
   signal context8: std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal s8rdy   : std_logic;
   signal s8next  : std_logic;
   signal s8en    : std_logic;

   -- Stage 9 signals
   signal a9      : std_logic_vector(31 downto 0);
   signal b9      : std_logic_vector(31 downto 0);
   signal c9      : std_logic_vector(31 downto 0);
   signal context9: std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal s9rdy   : std_logic;
   signal s9next  : std_logic;
   signal s9en    : std_logic;

   -- Stage 10 signals
   signal a10     : std_logic_vector(31 downto 0);
   signal b10     : std_logic_vector(31 downto 0);
   signal c10     : std_logic_vector(31 downto 0);
   signal context10:std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal s10rdy  : std_logic;
   signal s10next : std_logic;
   signal s10en   : std_logic;
   signal cont_s10rdy : std_logic;
   signal cont_s10next: std_logic;
   signal cont_s10en  : std_logic;
   
   signal a_0     : std_logic_vector(31 downto 0);
   signal b_0     : std_logic_vector(31 downto 0);
   signal c_0     : std_logic_vector(31 downto 0);

   signal a_1     : std_logic_vector(31 downto 0);
   signal b_1     : std_logic_vector(31 downto 0);
   signal c_1     : std_logic_vector(31 downto 0);
   
   signal a_2     : std_logic_vector(31 downto 0);
   signal b_2     : std_logic_vector(31 downto 0);
   signal c_2     : std_logic_vector(31 downto 0);
   
   signal context_1  :std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   
   signal data_in_1  : std_logic_vector(95 downto 0);
begin

zeros <= X"00000000";

-- ----------------------------------------------------------------------------
--                        Stage 0 : Adding
--
-- a = b =  0x9e3779b9;
-- c += ((uint32_t)wideword[8]<<8);
-- b +=((uint32_t)wideword[7]<<24);
-- b +=((uint32_t)wideword[6]<<16);
-- b +=((uint32_t)wideword[5]<<8);
-- b +=wideword[4];
-- a +=((uint32_t)wideword[3]<<24);
-- a +=((uint32_t)wideword[2]<<16);
-- a +=((uint32_t)wideword[1]<<8);
-- a +=wideword[0];
-- ----------------------------------------------------------------------------
   
   -- Select seed
   seed_sel_p : process(INPUT_TYPE, SEED, STATE)
   begin
      case INPUT_TYPE is
         when '0'    => a_0 <= magic;
                        b_0 <= magic;
                        c_0 <= SEED;
         when '1'    => a_0 <= STATE(95 downto 64);
                        b_0 <= STATE(63 downto 32);
                        c_0 <= STATE(31 downto 0);
         when others => null;
      end case;
   end process;
   
   -- Select last word
   lw_sel_p : process(CONTEXT_IN(log2(INTERFACES) + 1), c_0)
   begin
      case CONTEXT_IN(log2(INTERFACES) + 1) is
         when '0'    => c_1 <= c_0;
         when '1'    => c_1 <= c_0 + conv_std_logic_vector(UH_SIZE, 32);
         when others => null;
      end case;
   end process;

   context_1 <= CONTEXT_IN;
   a_1 <= a_0;
   b_1 <= b_0;
   
   pipe_cont_en_u0 : entity work.pipe_en
   generic map(
      RESET_STATE => '0'
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,
      IN_RDY   => CONTEXT_IN_VLD,
      IN_NEXT  => CONTEXT_IN_NEXT,
      OUT_RDY  => cont_s0rdy,
      OUT_NEXT => cont_s0next,
      EN       => cont_s0en
   );
   
   pipe_en_u0 : entity work.pipe_en
   port map(
      CLK      => CLK,
      RESET    => RESET,
      IN_RDY   => DATA_IN_VLD,
      IN_NEXT  => DATA_IN_NEXT,
      OUT_RDY  => s0rdy,
      OUT_NEXT => s0next,
      EN       => s0en
   );

   stage0_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (RESET = '1') then
            context0 <= conv_std_logic_vector(3, log2(INTERFACES) + 2);
         else
            if cont_s0en = '1' then
               context0 <= context_1;
            end if;
            if s0en = '1' then
               a_2 <= a_1;
               b_2 <= b_1;
               c_2 <= c_1;
               data_in_1 <= DATA_IN;
            end if;
         end if;
      end if;
   end process;
   
   
   a0 <= a_2 + data_in_1(31 downto 0);
   b0 <= b_2 + data_in_1(63 downto 32);
   c0 <= c_2 + data_in_1(95 downto 64);

-- ----------------------------------------------------------------------------
--                        Stage 1
-- a -= b;
-- ----------------------------------------------------------------------------
   a1 <= a0 - b0;
   b1 <= b0;
   c1 <= c0;
   context1 <= context0;

-- ----------------------------------------------------------------------------
--                        Stage 2
-- a -= c; a ^= (c>>13);
-- b -= c;
-- ----------------------------------------------------------------------------

   a2 <= (a1 - c1) xor (zeros(12 downto 0) & c1(31 downto 13));
   b2 <= b1 - c1;
   c2 <= c1;
   context2 <= context1;

-- ----------------------------------------------------------------------------
--                        Stage 3
-- b -= a; b ^= (a<<8);
-- c -= a;
-- ----------------------------------------------------------------------------
   pipe_cont_en_u3 : entity work.pipe_en
   generic map(
      RESET_STATE => '0'
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,
      IN_RDY   => cont_s0rdy,
      IN_NEXT  => cont_s0next,
      OUT_RDY  => cont_s3rdy,
      OUT_NEXT => cont_s3next,
      EN       => cont_s3en
   );

   pipe_en_u3 : entity work.pipe_en
   port map(
      CLK      => CLK,
      RESET    => RESET,
      IN_RDY   => s0rdy,
      IN_NEXT  => s0next,
      OUT_RDY  => s3rdy,
      OUT_NEXT => s3next,
      EN       => s3en
   );

   stage3_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (RESET = '1') then
            context3 <= conv_std_logic_vector(2, log2(INTERFACES) + 2);
         else
            if cont_s3en = '1' then
               context3 <= context2;
            end if;
            if s3en = '1' then
               a3 <= a2;
               b3 <= (b2 - a2) xor (a2(23 downto 0) & zeros(7 downto 0));
               c3 <= c2 - a2;
            end if;
         end if;
      end if;
   end process;

-- ----------------------------------------------------------------------------
--                        Stage 4
-- c -= b; c ^= (b>>13);
-- a -= b;
-- ----------------------------------------------------------------------------

   a4 <= a3 - b3;
   b4 <= b3;
   c4 <= (c3 - b3) xor (zeros(12 downto 0) & b3(31 downto 13));
   context4 <= context3;

-- ----------------------------------------------------------------------------
--                        Stage 5
-- a -= c; a ^= (c>>12); 
-- b -= c;
-- ----------------------------------------------------------------------------
   a5 <= (a4 - c4) xor (zeros(11 downto 0) & c4(31 downto 12));
   b5 <= b4 - c4;
   c5 <= c4;
   context5 <= context4;

-- ----------------------------------------------------------------------------
--                        Stage 6
-- b -= a; b ^= (a<<16);
-- c -= a;
-- ----------------------------------------------------------------------------

   a6 <= a5;
   b6 <= (b5 - a5) xor (a5(15 downto 0) & zeros(31 downto 16));
   c6 <= c5 - a5;
   context6 <= context5;


-- ----------------------------------------------------------------------------
--                        Stage 7
-- c -= b; c ^= (b>>5);
-- a -= b;
-- ----------------------------------------------------------------------------
   pipe_cont_en_u7 : entity work.pipe_en
   generic map(
      RESET_STATE => '0'
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,
      IN_RDY   => cont_s3rdy,
      IN_NEXT  => cont_s3next,
      OUT_RDY  => cont_s7rdy,
      OUT_NEXT => cont_s7next,
      EN       => cont_s7en
   );
   
   pipe_en_u7 : entity work.pipe_en
   port map(
      CLK      => CLK,
      RESET    => RESET,
      IN_RDY   => s3rdy,
      IN_NEXT  => s3next,
      OUT_RDY  => s7rdy,
      OUT_NEXT => s7next,
      EN       => s7en
   );

   stage7_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (RESET = '1') then
            context7 <= conv_std_logic_vector(1, log2(INTERFACES) + 2);
         else
            if cont_s7en = '1' then
               context7 <= context6;
            end if;
            if s7en = '1' then
               a7 <= a6 - b6;
               b7 <= b6;
               c7 <= (c6 - b6) xor (zeros(4 downto 0) & b6(31 downto 5));
            end if;
         end if;
      end if;
   end process;

-- ----------------------------------------------------------------------------
--                        Stage 8
-- a -= c; a ^= (c>>3); 
-- b -= c;
-- ----------------------------------------------------------------------------

   a8 <= (a7 - c7) xor (zeros(2 downto 0) & c7(31 downto 3));
   b8 <= b7 - c7;
   c8 <= c7;
   context8 <= context7;

-- ----------------------------------------------------------------------------
--                        Stage 9
-- b -= a; b ^= (a<<10);
-- c -= a;
-- ----------------------------------------------------------------------------
   a9 <= a8;
   b9 <= (b8 - a8) xor (a8(21 downto 0) & zeros(31 downto 22));
   c9 <= c8 - a8;
   context9 <= context8;

-- ----------------------------------------------------------------------------
--                        Stage 10
-- c -= b; c ^= (b>>15);
-- ----------------------------------------------------------------------------
   pipe_cont_en_u10 : entity work.pipe_en
   generic map(
      RESET_STATE => '0'
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,
      IN_RDY   => cont_s7rdy,
      IN_NEXT  => cont_s7next,
      OUT_RDY  => CONTEXT_OUT_RDY,
      OUT_NEXT => CONTEXT_OUT_NEXT,
      EN       => cont_s10en
   );

   pipe_en_u10 : entity work.pipe_en
   port map(
      CLK      => CLK,
      RESET    => RESET,
      IN_RDY   => s7rdy,
      IN_NEXT  => s7next,
      OUT_RDY  => DATA_OUT_RDY,
      OUT_NEXT => DATA_OUT_NEXT,
      EN       => s10en
   );

   stage10_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if (RESET = '1') then
            context10 <= conv_std_logic_vector(0, log2(INTERFACES) + 2);
         else
            if cont_s10en = '1' then
               context10 <= context9;
            end if;
            if s10en = '1' then
               a10 <= a9;
               b10 <= b9;
               c10 <= (c9 - b9) xor (zeros(14 downto 0) & b9(31 downto 15));
            end if;
         end if;
      end if;
   end process;

-- Output signal mapping
DATA_OUT <= a10 & b10 & c10;
CONTEXT_OUT <= context10;

end architecture full;
