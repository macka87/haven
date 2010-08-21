-- addr_space.vhd: Combo6 & Combo6X - address space for testing designs 
-- Copyright (C) 2004 CESNET
-- Author(s): Pecenka Tomas <pecenka AT liberouter.org>
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

package c6x_addr_space is
   -- constant declaration
   constant ID_BASE_ADDR       : integer := 16#0000000#; --
   --       ID_ADDR_WIDTH      : integer := 8;        -- range 00000..03fff
   constant SDRAM_BASE_ADDR    : integer := 16#0004000#; --
   constant SDRAM_ADDR_WIDTH   : integer := 13;        -- range 04000..07fff
   constant SSRAM0_BASE_ADDR   : integer := 16#0008000#; --
   constant SSRAM0_ADDR_WIDTH  : integer := 14;       -- range 08000..0bfff
   constant SSRAM1_BASE_ADDR   : integer := 16#000C000#; --
   constant SSRAM1_ADDR_WIDTH  : integer := 14;       -- range 0C000..0ffff
   constant SSRAM2_BASE_ADDR   : integer := 16#0010000#; --
   constant SSRAM2_ADDR_WIDTH  : integer := 14;       -- range 10000..13fff
   constant TCAM_BASE_ADDR     : integer := 16#0014000#; --
   constant TCAM_ADDR_WIDTH    : integer := 14;       -- range 14000..17fff
   constant SPD_BASE_ADDR      : integer := 16#0018000#; --
   constant SPD_ADDR_WIDTH     : integer := 2;        -- range 18000..19fff

   constant SDRAM_CTRL_BASE_ADDR :integer:= 16#001A000#; --
   constant SDRAM_CTRL_ADDR_WIDTH:integer:= 10;        -- range 1A000..1bfff

   constant LB_TEST_BASE_ADDR  : integer := 16#001C000#; --
   --       LB_TEST_ADDR_WIDTH : integer := 10;       -- range 1C000..1efff
end c6x_addr_space;

package body c6x_addr_space is
end c6x_addr_space;

