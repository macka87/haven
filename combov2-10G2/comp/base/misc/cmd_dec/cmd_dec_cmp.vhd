--
-- cmd_dec_cmp.vhd: Comparator
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas <martinek@liberouter.org>
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
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cmd_dec_cmp is
   generic(
      CMP_VAL  : std_logic_vector(7 downto 0) := X"d5"
   );
   port(
      DIN      : in std_logic_vector(7 downto 0);
      RESULT   : out std_logic
   );
end entity cmd_dec_cmp;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of cmd_dec_cmp is

--    signal lut_l_out  : std_logic;
--    signal lut_h_out  : std_logic;
--    signal vcc        : std_logic;
--    signal lut_l_init : bit_vector(15 downto 0);
--    signal lut_h_init : bit_vector(15 downto 0);

-- component LUT4
--    generic (
--       INIT : bit_vector(15 downto 0)
--    );
--    port (
--       I0 : in std_logic;
--       I1 : in std_logic;
--       I2 : in std_logic;
--       I3 : in std_logic;
--       O : out std_logic
--    );
-- end component;

-- component MUXCY_L
--    port (
--       DI:  in std_logic;
--       CI:  in std_logic;
--       S:   in std_logic;
--       LO: out std_logic);
-- end component;

begin
-- 
-- vcc <= '1';

-- genl_u : for i in 0 to 15 generate
--    lut_l_init(i) <= '1' when (i = conv_integer(CMP_VAL(3 downto 0))) else '0';
-- end generate;

-- LUT_L : LUT4
-- generic map(
--    INIT => lut_l_init
-- )
-- port map(
--    I0 => DIN(0),
--    I1 => DIN(1),
--    I2 => DIN(2),
--    I3 => DIN(3),
--    O  => lut_l_out
-- );

-- 
-- genh_u : for i in 0 to 15 generate
--    lut_h_init(i) <= '1' when (i = conv_integer(CMP_VAL(7 downto 4))) else '0';
-- end generate;

-- LUT_H : LUT4
-- generic map(
--    INIT => lut_h_init
-- )
-- port map(
--    I0 => DIN(4),
--    I1 => DIN(5),
--    I2 => DIN(6),
--    I3 => DIN(7),
--    O  => lut_h_out
-- );

-- MUX_U : MUXCY_L
-- port map(
--    DI => vcc,
--    CI => lut_l_out,
--    S  => lut_h_out,
--    LO => RESULT
-- );

   RESULT <= '1' when (DIN = CMP_VAL) else '0';

end architecture behavioral;

