# Modules.tcl: Local include tcl script
# Copyright (C) 2005 CESNET
# Author: Martin Mikusek <martin.mikusek@liberouter.org>
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the OpenIPCore Hardware General Public
# License as published by the OpenIPCore Organization; either version
# 0.20-15092000 of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# OpenIPCore Hardware General Public License for more details.
#
# You should have received a copy of the OpenIPCore Hardware Public
# License along with this program; if not, download it from
# OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
# 
# $Id$
# 

# Base directories
set COMP_BASE           "$ENTITY_BASE/../../.."
set PKG_BASE            "$COMP_BASE/base/pkg"
set AURORA_CORES_BASE   "$ENTITY_BASE"
set 2BYTES_1LANE_BASE   "$AURORA_CORES_BASE/2bytes_1lane"
set 4BYTES_1LANE_BASE   "$AURORA_CORES_BASE/4bytes_1lane"
set 4BYTES_2LANES_BASE  "$AURORA_CORES_BASE/4bytes_2lanes"
set 8BYTES_2LANES_BASE  "$AURORA_CORES_BASE/8bytes_2lanes"

# List of packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd \
              "

# Source files for implemented component
if { $ARCHGRP == "FULL" } {

   # List of components
   set COMPONENTS [list \
           [list "AURORA_2BYTES_1LANE"      $2BYTES_1LANE_BASE  "FULL"] \
           [list "AURORA_4BYTES_1LANE"      $4BYTES_1LANE_BASE  "FULL"] \
           [list "AURORA_4BYTES_2LANES"     $4BYTES_2LANES_BASE "FULL"] \
           [list "AURORA_8BYTES_2LANES"     $8BYTES_2LANES_BASE "FULL"] \
 	     ]

   set MOD "$MOD $ENTITY_BASE/rio_aurora_module_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/rio_aurora_module.vhd"
}

if { $ARCHGRP == "2BYTE" } {

   # List of components
   set COMPONENTS [list \
           [list "AURORA_2BYTES_1LANE"      $2BYTES_1LANE_BASE  "FULL"] \
 	     ]

   set MOD "$MOD $ENTITY_BASE/rio_aurora_module_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/rio_aurora_module.vhd"
}

if { $ARCHGRP == "4BYTE1LANE" } {

   # List of components
   set COMPONENTS [list \
           [list "AURORA_4BYTES_1LANE"      $4BYTES_1LANE_BASE  "FULL"] \
 	     ]

   set MOD "$MOD $ENTITY_BASE/rio_aurora_module_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/rio_aurora_module.vhd"
}

if { $ARCHGRP == "4BYTE2LANE" } {

   # List of components
   set COMPONENTS [list \
           [list "AURORA_4BYTES_2LANES"     $4BYTES_2LANES_BASE "FULL"] \
 	     ]

   set MOD "$MOD $ENTITY_BASE/rio_aurora_module_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/rio_aurora_module.vhd"
}

if { $ARCHGRP == "8BYTE" } {

   # List of components
   set COMPONENTS [list \
           [list "AURORA_8BYTES_2LANES"     $8BYTES_2LANES_BASE "FULL"] \
 	     ]

   set MOD "$MOD $ENTITY_BASE/rio_aurora_module_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/rio_aurora_module.vhd"
}

# Source file for empty component - empty architecture 
if { $ARCHGRP  == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/rio_aurora_module_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/rio_aurora_module_empty.vhd"
}

