-- ics_test_app_pkg.vhd: ICS Test Application Package - Constants for memories
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobierský
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

package ics_test_app_pkg is

-- ----------------------------------------------------------------------------
--       Internal Bus Component Parameters
-- ----------------------------------------------------------------------------
   constant IB_USER0_MEM_SIZE : integer:= 1024; -- Size of memory in bytes
   constant IB_USER0_MEM_TYPE : integer:= 0;    -- 0 = BRAM / 1 = DISTMEM

   constant IB_USER1_MEM_SIZE : integer:= 1024; -- Size of memory in bytes
   constant IB_USER1_MEM_TYPE : integer:= 0;    -- 0 = BRAM / 1 = DISTMEM

   constant IB_USER2_MEM_SIZE : integer:= 1024; -- Size of memory in bytes
   constant IB_USER2_MEM_TYPE : integer:= 0;    -- 0 = BRAM / 1 = DISTMEM

   constant IB_USER3_MEM_SIZE : integer:= 1024; -- Size of memory in bytes
   constant IB_USER3_MEM_TYPE : integer:= 0;    -- 0 = BRAM / 1 = DISTMEM

  
-- ----------------------------------------------------------------------------
--       Local Bus Component Parameters
-- ----------------------------------------------------------------------------
   constant LB_USER0_MEM_SIZE : integer:= 256;  -- Size of memory in bytes
   constant LB_USER0_MEM_TYPE : integer:= 1;    -- 0 = BRAM / 1 = DISTMEM

   constant LB_USER1_MEM_SIZE : integer:= 256;  -- Size of memory in bytes
   constant LB_USER1_MEM_TYPE : integer:= 1;    -- 0 = BRAM / 1 = DISTMEM

   constant LB_USER2_MEM_SIZE : integer:= 256;  -- Size of memory in bytes
   constant LB_USER2_MEM_TYPE : integer:= 1;    -- 0 = BRAM / 1 = DISTMEM

   constant LB_USER3_MEM_SIZE : integer:= 256;  -- Size of memory in bytes
   constant LB_USER3_MEM_TYPE : integer:= 1;    -- 0 = BRAM / 1 = DISTMEM

   constant LB_USER4_MEM_SIZE : integer:= 256;  -- Size of memory in bytes
   constant LB_USER4_MEM_TYPE : integer:= 1;    -- 0 = BRAM / 1 = DISTMEM

   constant LB_USER5_MEM_SIZE : integer:= 256;  -- Size of memory in bytes
   constant LB_USER5_MEM_TYPE : integer:= 1;    -- 0 = BRAM / 1 = DISTMEM

   constant LB_USER6_MEM_SIZE : integer:= 256;  -- Size of memory in bytes
   constant LB_USER6_MEM_TYPE : integer:= 1;    -- 0 = BRAM / 1 = DISTMEM

end ics_test_app_pkg;


package body ics_test_app_pkg is
end ics_test_app_pkg;

