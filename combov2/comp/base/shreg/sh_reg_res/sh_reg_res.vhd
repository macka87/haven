--
-- sh_reg_res.vhd: Shift Register With Reset
-- Copyright (C) 2006 CESNET
-- Author(s): Michal Spacek <xspace14@stud.fit.vutbr.cz>
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
entity sh_reg_res is
   generic(
      NUM_BITS    : integer := 16;
      INIT        : std_logic_vector(15 downto 0) := X"0000";
      INIT_EXT00  : std_logic_vector(63 downto 0) := X"0000000000000000"      
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;
      DIN      : in  std_logic;
      CE       : in  std_logic;
      DOUT     : out std_logic
   );
end entity sh_reg_res;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of sh_reg_res is

-- ------------------ Signals declaration -------------------------------------
   signal r_din : std_logic;
   signal r_ce  : std_logic;

begin

    r_ce <= RESET or CE;

    r_din <= DIN when RESET='0' else
                   '0' when RESET='1';

SH_REG_U : entity work.sh_reg
      generic map(
         NUM_BITS  => NUM_BITS,
         INIT => INIT,
         INIT_EXT00 => INIT_EXT00
      )
      port map(
         CLK      => CLK,
         DIN      => r_din,
         CE       => r_ce,
         DOUT     => DOUT
      );


end architecture behavioral;

