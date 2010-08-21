--
-- addr_const_mx.vhd : Address Constants - implemented with using MX&CNT
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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

library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

use work.math_pack.all; 

-- ----------------------------------------------------------------------------
--                    ENTITY DECLARATION -- Address Constants                -- 
-- ----------------------------------------------------------------------------

entity ADDR_CONST is 
   generic(
      ADDR      : std_logic_vector(31 downto 0) := X"00000000"; -- address constant
      WIDTH     : integer := 16                                 -- output width
   ); 
   port (
      -- Common interface ---------------------------------
      CLK       : in std_logic;
      RESET     : in std_logic;
   
      -- Input interface ----------------------------------
      NEXT_PART : in std_logic;
      
      -- Output interface ---------------------------------
      CONST     : out std_logic_vector(WIDTH-1 downto 0)
   );
end ADDR_CONST;

-- ----------------------------------------------------------------------------
--               ARCHITECTURE DECLARATION  --  Address Constants             --
-- ----------------------------------------------------------------------------

architecture addr_const_arch of ADDR_CONST is

   -- -------------------------------------------------------------------------
   --                           Function declaration                         --
   -- -------------------------------------------------------------------------

   function sel_width(width : integer) return integer is
      variable aux : integer;
   begin
      if (width < 32) then
         aux := log2(32/width);
      else
         aux := 1;
      end if;
      
      return aux;
   end function; 
   
   -- -------------------------------------------------------------------------
   --                            Signal declaration                          --
   -- -------------------------------------------------------------------------

   signal cnt_sel : std_logic_vector(sel_width(WIDTH)-1 downto 0);

begin

   -- -------------------------------------------------------------------------
   --                           CONSTANT WIDTH < 32                          --
   -- ------------------------------------------------------------------------- 
   CONST1_GEN: if (WIDTH < 32) generate

      U_gen_mux: entity work.GEN_MUX   
      generic map (
         DATA_WIDTH => WIDTH,
         MUX_WIDTH  => 32/WIDTH
      )
      port map (
         DATA_IN    => ADDR,
         SEL        => cnt_sel,
         DATA_OUT   => CONST   
      ); 

      cnt_selp: process (CLK, RESET) 
      begin
         if (CLK = '1' and CLK'event) then
            if (RESET = '1') then 
               cnt_sel <= (others => '0');         
            elsif (NEXT_PART = '1') then
               cnt_sel <= cnt_sel + 1;
            end if;
         end if;
      end process;
      
   end generate; 
   -- -------------------------------------------------------------------------
   --                           CONSTANT WIDTH = 32                          --
   -- -------------------------------------------------------------------------
   CONST2_GEN: if (WIDTH = 32) generate
      
      CONST <= ADDR;

   end generate;
   
end addr_const_arch;



