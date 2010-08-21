-- fls_max_select.vhd: Max selection unit architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FLS_MAX_SELECT is
   generic(
      DATA_WIDTH     : integer;
      VECTOR_COUNT   : integer
   );
   port(
      -- input vectors
      DI             : in  std_logic_vector((VECTOR_COUNT*DATA_WIDTH)-1 
                                                                  downto 0);
      -- max bus ('1' -> this vector is the greatest)
      MAX            : out std_logic_vector(VECTOR_COUNT-1 downto 0)
   );
end entity FLS_MAX_SELECT;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FLS_MAX_SELECT is
  
   -- ------------------ Signals declaration ----------------------------------
   signal cmp_bus          : std_logic_vector(VECTOR_COUNT*VECTOR_COUNT-1
                                                                     downto 0);
   signal and_bus          : std_logic_vector(VECTOR_COUNT*VECTOR_COUNT-1
                                                                     downto 0);
begin

   -- generate necessary comparators ------------------------------------------
   GEN_CMP_BUS: for i in 0 to VECTOR_COUNT-1 generate
      GEN_COMPARATORS: for j in 0 to VECTOR_COUNT-1 generate
         
         GEN_COMPARATOR: if j /= i generate
            -- ------------------ Comparator ----------------------------------
            cmp_bus(i*VECTOR_COUNT+j) <= '1' 
               when (DI((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)
                  >= DI((j+1)*DATA_WIDTH-1 downto j*DATA_WIDTH)) else '0';
         end generate;
         
         GEN_ONE: if j = i generate
            cmp_bus(i*VECTOR_COUNT+j) <= '1';
         end generate;
         
      end generate;
   end generate;

   -- generate AND bus --------------------------------------------------------
   GEN_AND_BUS: for i in 0 to VECTOR_COUNT-1 generate
      GEN_ANDS: for j in 0 to VECTOR_COUNT-1 generate
         
         GEN_AND: if j /= 0 generate
            -- ------------------ AND -----------------------------------------
            and_bus(i*VECTOR_COUNT+j) <= 
               and_bus(i*VECTOR_COUNT+j-1) and cmp_bus(i*VECTOR_COUNT+j);
               
         end generate;
         
         GEN_ONE: if j = 0 generate
            and_bus(i*VECTOR_COUNT+j) <= cmp_bus(i*VECTOR_COUNT+j);
         end generate;
         
      end generate;
   end generate;

   -- generate output ---------------------------------------------------------
   GEN_OUT: for i in 0 to VECTOR_COUNT-1 generate
      MAX(i) <= and_bus(i*VECTOR_COUNT+VECTOR_COUNT-1);
   end generate;

end architecture full;
