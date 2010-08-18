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

package c6x_constants is

   -- Design ID constants

   -- Combo6 test
   constant ID_C6_TEST       : std_logic_vector( 15 downto 0) := X"7100";
   constant ID_C6_TEST_TEXT  : std_logic_vector(255 downto 0) :=
        X"50617A646572615F43365F74657374696e675F64657369676e00000000000000"; 
     --   P a z d e r a _ C 6 _ t e s t i n g _ d e s i g n
 
   -- Combo6X test
   constant ID_C6X_TEST      : std_logic_vector( 15 downto 0) := X"7200";
   constant ID_C6X_TEST_TEXT : std_logic_vector(255 downto 0) :=
        X"50617A646572615F4336585F74657374696e675F64657369676e000000000000"; 
     --   P a z d e r a _ C 6 X _ t e s t i n g _ d e s i g n
   
   -- ======================================================================
   -- Address & data width of SSRAM 0-2 on Combo6 cards
   constant C6_SSRAM0_DATA_WIDTH  : integer := 36;
   constant C6_SSRAM0_ADDR_WIDTH  : integer := 19;

   constant C6_SSRAM1_DATA_WIDTH  : integer := 32;
   constant C6_SSRAM1_ADDR_WIDTH  : integer := 19;

   constant C6_SSRAM2_DATA_WIDTH  : integer := 32;
   constant C6_SSRAM2_ADDR_WIDTH  : integer := 19;

   -- ======================================================================
   -- Address & data width of SSRAM 0-2 on Combo6X cards
   constant C6X_SSRAM0_DATA_WIDTH : integer := 36;
   constant C6X_SSRAM0_ADDR_WIDTH : integer := 20;

   constant C6X_SSRAM1_DATA_WIDTH : integer := 32;
   constant C6X_SSRAM1_ADDR_WIDTH : integer := 20;

   constant C6X_SSRAM2_DATA_WIDTH : integer := 32;
   constant C6X_SSRAM2_ADDR_WIDTH : integer := 20;

   -- ======================================================================
   -- Address & data width of DDR SDRAM on Combo6X cards
   constant C6X_SDRAM0_DATA_WIDTH : integer := 144;
   constant C6X_SDRAM0_ADDR_WIDTH : integer := 26;

end c6x_constants;


package body c6x_constants is

end c6x_constants;
