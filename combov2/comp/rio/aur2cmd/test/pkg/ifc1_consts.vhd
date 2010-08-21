--
-- constants.vhd: constants definition for low level DDR SDRAM scheduler
-- Copyright (C) 2003 CESNET
-- Author(s): Marek Tomas marekt@feld.cvut.cz, Ludek Crha crha@liberouter.org
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
library IEEE;
use IEEE.std_logic_1164.all; 

package ifc_constants is

   -- ============================================================== --
   -- ============================================================== --
   --                           XFP                                  --
   -- ============================================================== --
   -- ============================================================== --
 
   -- XFPpro test
   constant ID_XFP_TEST      : std_logic_vector( 15 downto 0) := X"78C0";
   constant ID_XFP_TEST_TEXT : std_logic_vector(255 downto 0) :=
        X"5846505F74657374696e675F64657369676e0000000000000000000000000000"; 
      --  X F P _ t e s t i n g _ d e s i g n

   -- Address & data width of SSRAM 0-1 on XFP cards
   constant XFP_SSRAM_DATA_WIDTH : integer := 36;
   constant XFP_SSRAM_ADDR_WIDTH : integer := 19;
   
end ifc_constants;


package body ifc_constants is

end ifc_constants;
