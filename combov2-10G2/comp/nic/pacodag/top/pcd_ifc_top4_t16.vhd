-- pacodag_top4_t16.vhd: PACODAG for NIC project, data width 16b, 4 instances
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jiri Tobola <tobola@liberouter.org>
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
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

use work.math_pack.ALL;
use work.ibuf_general_pkg.ALL;

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity pacodag_top4_t16 is
   generic (
      HEADER_EN : boolean := true; -- Generate headers
      FOOTER_EN : boolean := false -- Generate footers
   );
   port (
      -- Common interface
      RESET    : in std_logic;
      -- IBUF interface
      PCD0     : inout t_pacodag16;
      PCD1     : inout t_pacodag16;
      PCD2     : inout t_pacodag16;
      PCD3     : inout t_pacodag16
   );
end pacodag_top4_t16;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of pacodag_top4_t16 is
begin

   PACODAG0_I: entity work.pacodag_t16
   generic map(
      IFC_ID      => "0001",
      HEADER_EN   => HEADER_EN,
      FOOTER_EN   => FOOTER_EN
   )
   port map(
      -- Common interface
      RESET    => RESET,
      -- IBUF interface
      PCD      => PCD0
   ); 

   PACODAG1_I: entity work.pacodag_t16
   generic map(
      IFC_ID      => "0010",
      HEADER_EN   => HEADER_EN,
      FOOTER_EN   => FOOTER_EN
   )
   port map(
      -- Common interface
      RESET    => RESET,
      -- IBUF interface
      PCD      => PCD1
   ); 

   PACODAG2_I: entity work.pacodag_t16
   generic map(
      IFC_ID      => "0100",
      HEADER_EN   => HEADER_EN,
      FOOTER_EN   => FOOTER_EN
   )
   port map(
      -- Common interface
      RESET    => RESET,
      -- IBUF interface
      PCD      => PCD2
   ); 

   PACODAG3_I: entity work.pacodag_t16
   generic map(
      IFC_ID      => "1000",
      HEADER_EN   => HEADER_EN,
      FOOTER_EN   => FOOTER_EN
   )
   port map(
      -- Common interface
      RESET    => RESET,
      -- IBUF interface
      PCD      => PCD3
   ); 

end behavioral;

