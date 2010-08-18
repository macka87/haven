#
# Modules.tcl: Local include tcl script
# Copyright (C) 2008 CESNET
# Author(s): Tomas Malek <tomalek@liberouter.org>
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in
#    the documentation and/or other materials provided with the
#    distribution.
# 3. Neither the name of the Company nor the names of its contributors
#    may be used to endorse or promote products derived from this
#    software without specific prior written permission.
#
# This software is provided ``as is'', and any express or implied
# warranties, including, but not limited to, the implied warranties of
# merchantability and fitness for a particular purpose are disclaimed.
# In no event shall the company or contributors be liable for any
# direct, indirect, incidental, special, exemplary, or consequential
# damages (including, but not limited to, procurement of substitute
# goods or services; loss of use, data, or profits; or business
# interruption) however caused and on any theory of liability, whether
# in contract, strict liability, or tort (including negligence or
# otherwise) arising in any way out of the use of this software, even
# if advised of the possibility of such damage.
#
# $Id$
#

# -----------------------------------------------------------------------------

if { $ARCHGRP == "FULL" } {

  set COMP_BASE        "$ENTITY_BASE/../../../../../.."
   
  set UNPACKER_BASE    "$ENTITY_BASE/../../../base/unpacker"   
  set BE_GEN_BASE      "$ENTITY_BASE/../../../base/be_gen"  
  set MATH_BASE        "$ENTITY_BASE/../../../../../../base/pkg"     
  set SH_FIFO_BASE     "$COMP_BASE/base/fifo/sh_fifo"
  set BUFFER_SH_BASE   "$ENTITY_BASE/../../../base/buffer_sh"
  set SHIFTER_BASE     "$COMP_BASE/base/logic/barrel_shifter"
 
  set COMPONENTS [list \
     [list "UNPACKER"    $UNPACKER_BASE     "FULL"] \
     [list "BE_GEN"      $BE_GEN_BASE       "FULL"] \
     [list "MATH_PACK"   $MATH_BASE         "MATH"] \
     [list "SH_FIFO"     $SH_FIFO_BASE      "FULL"] \
     [list "BUFFER_SH"   $BUFFER_SH_BASE    "FULL"] \
     [list "BARREL_SHIFTER" $SHIFTER_BASE     "FULL"] \
  ]
  
  set MOD "$MOD $ENTITY_BASE/../../../../pkg/ib_fmt_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/../../../../pkg/ib_ifc_pkg.vhd"  
  set MOD "$MOD $ENTITY_BASE/../../pkg/endpoint_pkg.vhd"

  set MOD "$MOD $ENTITY_BASE/align_unit_fake.vhd"
  set MOD "$MOD $ENTITY_BASE/align_unit.vhd" 
  set MOD "$MOD $ENTITY_BASE/unpck_hbuf.vhd"      
  set MOD "$MOD $ENTITY_BASE/pck_hbuf.vhd"      
  set MOD "$MOD $ENTITY_BASE/cpl_buf.vhd"        
  set MOD "$MOD $ENTITY_BASE/read_fsm.vhd"    
  set MOD "$MOD $ENTITY_BASE/cpl_fsm.vhd"     
  set MOD "$MOD $ENTITY_BASE/fetch_marker.vhd"    
  set MOD "$MOD $ENTITY_BASE/read_ctrl.vhd"      
  set MOD "$MOD $ENTITY_BASE/read_ctrl_arch.vhd"    
}

# -----------------------------------------------------------------------------

if { $ARCHGRP == "EMPTY" } {

}



