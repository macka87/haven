-- ics_core_pkg.vhd: ICS core pkg - BASE and LIMIT constants
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas martinek@liberouter.org
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the OpenIPCore Hardware General Public
-- License as published by the OpenIPCore Organization; either version
-- 0.20-15092000 of the License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- OpenIPCore Hardware General Public License for more details.
--
-- You should have received a copy of the OpenIPCore Hardware Public
-- License along with this program; if not, download it from
-- OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use work.ib_pkg.all;
use work.lb_pkg.all;

package ics_core_pkg is
-- ----------------------------------------------------------------------------
--                        Switch Address Spaces
-- ----------------------------------------------------------------------------
   -- SWITCH0 ADDR_SPACE
   constant IB_SWITCH0_BASE  : std_logic_vector(31 downto 0) := X"00000000";
   constant IB_SWITCH0_LIMIT : std_logic_vector(31 downto 0) := X"009FFFFF";

   -- SWITCH1 ADDR_SPACE
   constant IB_SWITCH1_BASE  : std_logic_vector(31 downto 0) := X"00200000";
   constant IB_SWITCH1_LIMIT : std_logic_vector(31 downto 0) := X"007FFFFF";

   -- SWITCH2 ADDR_SPACE
   constant IB_SWITCH2_BASE  : std_logic_vector(31 downto 0) := X"00400000";
   constant IB_SWITCH2_LIMIT : std_logic_vector(31 downto 0) := X"005FFFFF";

   -- SWITCH3 ADDR_SPACE
   constant IB_SWITCH3_BASE  : std_logic_vector(31 downto 0) := X"00600000";
   constant IB_SWITCH3_LIMIT : std_logic_vector(31 downto 0) := X"003FFFFF";

-- ----------------------------------------------------------------------------
--       Internal Bus Component Address Spaces (including LB_ROOT)
-- ----------------------------------------------------------------------------
   -- ADDR RANGE: 0x00000000 - 0x001FFFFF
   -- ADDR SPACE: 2 097 152 B
   constant LOCALBUS_BASE    : std_logic_vector(31 downto 0) := X"00000000";
   constant LOCALBUS_LIMIT   : std_logic_vector(31 downto 0) := X"00200000"; -- 21 bits user address

   -- ADDR RANGE: 0x00200000 - 0x003FFFFF
   -- ADDR SPACE: 2 097 152 B
   constant IB_USER0_BASE    : std_logic_vector(31 downto 0) := X"00200000";
   constant IB_USER0_LIMIT   : std_logic_vector(31 downto 0) := X"00200000"; -- 21 bits user address
   
   -- ADDR RANGE: 0x00400000 - 0x005FFFFF
   -- ADDR SPACE: 2 097 152 B
   constant IB_USER1_BASE    : std_logic_vector(31 downto 0) := X"00400000";
   constant IB_USER1_LIMIT   : std_logic_vector(31 downto 0) := X"00200000"; -- 21 bits user address
   
   -- ADDR RANGE: 0x00600000 - 0x007FFFFF
   -- ADDR SPACE: 2 097 152 B
   constant IB_USER2_BASE    : std_logic_vector(31 downto 0) := X"00600000";
   constant IB_USER2_LIMIT   : std_logic_vector(31 downto 0) := X"00200000"; -- 21 bits user address
   
   -- ADDR RANGE: 0x00800000 - 0x009FFFFF
   -- ADDR SPACE: 536 870 912 B
   constant IB_USER3_BASE    : std_logic_vector(31 downto 0) := X"00800000";
   constant IB_USER3_LIMIT   : std_logic_vector(31 downto 0) := X"00200000"; -- 21 bits user address


-- ----------------------------------------------------------------------------
--                   Local Bus Component Address Spaces
-- ----------------------------------------------------------------------------
   -- ADDR RANGE: 0x00000000 - 0x0003FFFF
   -- ADDR SPACE: 262 144 B
   constant LB_USER0_BASE    : std_logic_vector(31 downto 0) := X"00000000";
   constant LB_USER0_LIMIT   : std_logic_vector(31 downto 0) := X"00040000"; -- 18 bits user address
   constant LB_USER0_FREQ    : integer                       := LOCAL_BUS_FREQUENCY;
   constant LB_USER0_BUFFER  : boolean                       := false;

   -- ADDR RANGE: 0x00040000 - 0x0007FFFF
   -- ADDR SPACE: 262 144 B
   constant LB_USER1_BASE    : std_logic_vector(31 downto 0) := X"00040000";
   constant LB_USER1_LIMIT   : std_logic_vector(31 downto 0) := X"00040000"; -- 18 bits user address
   constant LB_USER1_FREQ    : integer                       := LOCAL_BUS_FREQUENCY;
   constant LB_USER1_BUFFER  : boolean                       := false;

   -- ADDR RANGE: 0x00080000 - 0x000BFFFF
   -- ADDR SPACE: 262 144 B
   constant LB_USER2_BASE    : std_logic_vector(31 downto 0) := X"00080000";
   constant LB_USER2_LIMIT   : std_logic_vector(31 downto 0) := X"00040000"; -- 18 bits user address
   constant LB_USER2_FREQ    : integer                       := LOCAL_BUS_FREQUENCY;
   constant LB_USER2_BUFFER  : boolean                       := false;

   -- ADDR RANGE: 0x000C0000 - 0x000FFFFF
   -- ADDR SPACE: 262 144 B
   constant LB_USER3_BASE    : std_logic_vector(31 downto 0) := X"000C0000";
   constant LB_USER3_LIMIT   : std_logic_vector(31 downto 0) := X"00040000"; -- 18 bits user address
   constant LB_USER3_FREQ    : integer                       := LOCAL_BUS_FREQUENCY;
   constant LB_USER3_BUFFER  : boolean                       := false;

   -- ADDR RANGE: 0x00100000 - 0x0013FFFF
   -- ADDR SPACE: 262 144 B
   constant LB_USER4_BASE    : std_logic_vector(31 downto 0) := X"00100000";
   constant LB_USER4_LIMIT   : std_logic_vector(31 downto 0) := X"00040000"; -- 18 bits user address
   constant LB_USER4_FREQ    : integer                       := LOCAL_BUS_FREQUENCY;
   constant LB_USER4_BUFFER  : boolean                       := false;

   -- ADDR RANGE: 0x00140000 - 0x0017FFFF
   -- ADDR SPACE: 262 144 B
   constant LB_USER5_BASE    : std_logic_vector(31 downto 0) := X"00140000";
   constant LB_USER5_LIMIT   : std_logic_vector(31 downto 0) := X"00040000"; -- 18 bits user address
   constant LB_USER5_FREQ    : integer                       := LOCAL_BUS_FREQUENCY;
   constant LB_USER5_BUFFER  : boolean                       := false;

   -- ADDR RANGE: 0x00180000 - 0x001BFFFF
   -- ADDR SPACE: 262 144 B
   constant LB_USER6_BASE    : std_logic_vector(31 downto 0) := X"00180000";
   constant LB_USER6_LIMIT   : std_logic_vector(31 downto 0) := X"00040000"; -- 18 bits user address
   constant LB_USER6_FREQ    : integer                       := LOCAL_BUS_FREQUENCY;
   constant LB_USER6_BUFFER  : boolean                       := false;

   -- ADDR RANGE: 0x001C0000 - 0x001FFFFF (Not USED)
   -- ADDR SPACE: 262 144 B
   constant LB_USER7_BASE    : std_logic_vector(31 downto 0) := X"001C0000";
   constant LB_USER7_LIMIT   : std_logic_vector(31 downto 0) := X"00040000"; -- 18 bits user address
   constant LB_USER7_FREQ    : integer                       := LOCAL_BUS_FREQUENCY;
   constant LB_USER7_BUFFER  : boolean                       := false;

end ics_core_pkg;


package body ics_core_pkg is
end ics_core_pkg;

