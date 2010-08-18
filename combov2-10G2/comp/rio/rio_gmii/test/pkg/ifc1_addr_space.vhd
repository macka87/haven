-- addr_space.vhd: Address Space Constants
-- Copyright (C) 2004 CESNET
-- Author(s): Pecenka Tomas <pecenka AT liberouter.org>
--            Filip Tomas <flipflop AT liberouter.org>
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

package ifc_addr_space is
   -- constant declaration
   constant PHYTER_I2C_BASE_ADDR : integer := 16#0001000#; --
   constant ID_BASE_ADDR         : integer := 16#0100000#; --
   --       ID_ADDR_WIDTH        : integer := 8;        -- range 00000..03fff
   constant LB_SDRAM_BASE_ADDR   : integer := 16#0104000#; --
   constant LB_SDRAM_ADDR_WIDTH  : integer := 8;        -- range 04000..07fff
   constant LB_SSRAM0_BASE_ADDR  : integer := 16#0108000#; --
   constant LB_SSRAM0_ADDR_WIDTH : integer := 13;       -- range 08000..0bfff
   constant LB_SSRAM1_BASE_ADDR  : integer := 16#010C000#; --
   constant LB_SSRAM1_ADDR_WIDTH : integer := 13;       -- range 0C000..0ffff
   constant LB_SSRAM2_BASE_ADDR  : integer := 16#0110000#; --
   constant LB_SSRAM2_ADDR_WIDTH : integer := 13;       -- range 10000..13fff
   constant LB_TCAM_BASE_ADDR    : integer := 16#0114000#; --
   constant LB_TCAM_ADDR_WIDTH   : integer := 12;       -- range 14000..17fff
   constant SPD_BASE_ADDR        : integer := 16#0118000#; --
   constant SPD_ADDR_WIDTH       : integer := 2;        -- range 18000..1bfff
   constant LB_TEST_BASE_ADDR    : integer := 16#011C000#; --
   --       LB_TEST_ADDR_WIDTH   : integer := 10;       -- range 1C000..1efff
   constant IFC_TEST0_BASE_ADDR  : integer := 16#0120000#; --
   constant IFC_TEST0_ADDR_WIDTH : integer := 13;       -- range 10c000..10ffff
   constant IFC_TEST1_BASE_ADDR  : integer := 16#0124000#; --
   constant IFC_TEST1_ADDR_WIDTH : integer := 13;       -- range 10c000..10ffff
end ifc_addr_space;

package body ifc_addr_space is
end ifc_addr_space;

