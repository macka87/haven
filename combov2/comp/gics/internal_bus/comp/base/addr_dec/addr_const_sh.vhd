--
-- addr_const_sh.vhd : Address Constants - composed of shift registers
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

-- ----------------------------------------------------------------------------
--                    ENTITY DECLARATION -- Address Constants                -- 
-- ----------------------------------------------------------------------------

entity ADDR_CONST_SH is 
   generic(
      ADDR      : std_logic_vector(31 downto 0) := X"00000000"; -- address constant
      WIDTH     : integer := 16                                 -- output width
   ); 
   port (
      -- Common interface ---------------------------------
      CLK       : in std_logic; 
   
      -- Input interface ----------------------------------
      NEXT_PART : in std_logic;
      
      -- Output interface ---------------------------------
      CONST     : out std_logic_vector(WIDTH-1 downto 0)
   );
end ADDR_CONST_SH;

-- ----------------------------------------------------------------------------
--               ARCHITECTURE DECLARATION  --  Address Constants             --
-- ----------------------------------------------------------------------------

architecture addr_const_sh_arch of ADDR_CONST_SH is

   -- -------------------------------------------------------------------------
   --                            Signal declaration                          --
   -- -------------------------------------------------------------------------

   constant NUM_BITS  : integer := 32/WIDTH;
   constant NUM_ELEMS : integer := (NUM_BITS+15)/16;

   type t_vector4 is array (0 to NUM_ELEMS-1) of std_logic_vector(3 downto 0);
   type t_vector_dw is array (0 to NUM_ELEMS) of std_logic_vector(WIDTH-1 downto 0);
   type t_const_array is array (0 to WIDTH-1) of std_logic_vector(31 downto 0);
   
   signal regsh_do    : t_vector_dw;
   signal regsh_addr  : t_vector4; 

   -- -------------------------------------------------------------------------
   --                   Const Vector Array initialization                    --
   -- -------------------------------------------------------------------------

   function init_array return t_const_array is
      variable aux : t_const_array;
   begin
      for j in 0 to NUM_BITS-1 loop
         for i in 0 to WIDTH-1 loop
            aux(i)(NUM_BITS-1-j) := ADDR(j*WIDTH + i);
         end loop;
      end loop;
      
      return aux;
   end function; 
   
   constant const_array : t_const_array := init_array; 

begin

   -- -------------------------------------------------------------------------
   --                    SHIFT ELEMENTS INSTANTIATION                        --
   -- ------------------------------------------------------------------------- 

   regsh_do(0) <= regsh_do(NUM_ELEMS);

   SH_REG_XU : for i in 0 to NUM_ELEMS-1 generate
      -- addr generation
      regsh_addr(i) <= "1111" when (i < NUM_ELEMS-1) else
                       conv_std_logic_vector((NUM_BITS mod 16)+15, 4);

      -- data width generation
      SH_DATA_WIDTH : for j in 0 to WIDTH-1 generate

         SH_REG_U : entity work.sh_reg_elem
         generic map(
            SH_INIT  => const_array(j)( ((i+1)*16)-1 downto (i*16) )
         )
         port map(
            CLK      => CLK,
            DIN      => regsh_do(i)(j),
            CE       => NEXT_PART,
            ADDR     => regsh_addr(i),
            DOUT     => regsh_do(i+1)(j)
         );
            
      end generate;
   end generate;

   CONST <= regsh_do(NUM_ELEMS); 
   
end addr_const_sh_arch;



