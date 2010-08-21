--
-- flasm_mem.vhd: Simul flash memory S29GL
-- Copyright (C) 2008  CESNET
-- Author: Milan Malich <malich@mail.muni.cz>
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

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

entity flash_mem is
    Port (  FA              : in  STD_LOGIC_VECTOR (25 downto 0);
            FD              : out  STD_LOGIC_VECTOR (15 downto 0);
            FWE_N           : in std_logic;
            FCSFLASH_N      : in std_logic;
            FOE_N           : in std_logic;
            FBYTE_N         : in std_logic;
            FRY             : out std_logic
    );
end flash_mem;

architecture Behavioral of flash_mem is
  -- Timing parameter
  constant T_ACC : time := 110 ns;
  constant T_PACC : time := 40 ns;
  constant T_DF : time := 20 ns;

  type CELL_MATRIX is array (7 downto 0) of std_logic_vector (15 downto 0);
  constant flash_mem : CELL_MATRIX :=(X"AA00",X"5501",X"AA02",X"5503",
                                      X"AA04",X"5505",X"AA06",X"5507");  

  signal adress : std_logic_vector( 25 downto 0 ) := (others=>'0');
  signal prv_adress : std_logic_vector( 25 downto 0 ) := (others=>'0');
  
begin

  adress <= FA;

  process( adress, FCSFLASH_N, FOE_N )
  begin
    if( FCSFLASH_N = '0' )then
      if( FOE_N = '0' )then
        if( adress'event )then
          prv_adress <= adress;
          -- Test page mode
          if( prv_adress( 25 downto 3 ) = adress( 25 downto 3 ) )then
            FD <= flash_mem(CONV_INTEGER(adress( 2 downto 0))) after T_PACC; -- Page mode
          else
            FD <= flash_mem(CONV_INTEGER(adress( 2 downto 0))) after T_ACC;  -- Normal mode
          end if;
        end if;
      else
        FD <= (others=>'Z') after T_DF;
      end if;      
    else
      FD <= (others=>'Z') after T_DF;
    end if;
  end process;

  FRY <= '1';


end Behavioral;

