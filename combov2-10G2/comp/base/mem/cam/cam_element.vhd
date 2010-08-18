--
-- cam_element.vhd: Basic memory element of CAM.
-- Copyright (C) 2005 CESNET
-- Author(s): Martin kosek <xkosek00@stud.fit.vutbr.cz>
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

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cam_element is
   port(
      DATA_FILL      : in std_logic;
      DATA_IN        : in std_logic_vector(3 downto 0);
      WRITE_ENABLE   : in std_logic;
      MATCH_ENABLE   : in std_logic;
      RESET          : in std_logic; -- not used
      CLK            : in std_logic;
      MATCH          : out std_logic
   );
end entity cam_element;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_element_arch of cam_element is

-- ---------------- Distributed Shift Register Component Declaration ----------
   component SRL16E is
      generic (
         INIT : bit_vector := X"0000"
      );
      port    (
         d   : in  std_logic;
         ce  : in  std_logic;
         clk : in  std_logic;
         a0  : in  std_logic;
         a1  : in  std_logic;
         a2  : in  std_logic;
         a3  : in  std_logic;
         q   : out std_logic
      ); 
   end component;

-- ------------------ Signals declaration ------------------------------------- 
   signal muxcy      : std_logic;
   signal muxcy_sel  : std_logic;
   signal gnd        : std_logic;    -- Ground

begin
   gnd <= '0';
   MATCH <= muxcy;

-- shift register SRL16E ------------------------------------------------------
   LUT : SRL16E
   -- synthesis translate_off
   generic map (INIT => X"0000")
   -- synthesis translate_on
   port map (
      d => DATA_FILL,
      ce => WRITE_ENABLE,
      clk => CLK,
      a0 => DATA_IN(0),
      a1 => DATA_IN(1),
      a2 => DATA_IN(2),
      a3 => DATA_IN(3),
      q => muxcy_sel
   );

-- multiplexor muxcy ----------------------------------------------------------
muxcyp: process(muxcy_sel, MATCH_ENABLE, gnd)
begin
   case muxcy_sel is
      when '0' => muxcy <= gnd;
      when '1' => muxcy <= MATCH_ENABLE;
      when others => muxcy <= 'X';
   end case;
end process;

end architecture cam_element_arch;
