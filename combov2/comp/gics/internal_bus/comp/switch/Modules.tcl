#
# Modules.tcl: Components include script
# Copyright (C) 2008 CESNET
# Author: Tomas Malek <tomalek@liberouter.org>
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
   
  set IB_SWITCH_INPUT_BASE  "$ENTITY_BASE/comp/input"
  set IB_SWITCH_BUFFER_BASE "$ENTITY_BASE/comp/buffer"
  set IB_SWITCH_OUTPUT_BASE "$ENTITY_BASE/comp/output"
  set IB_PIPE_BASE          "$ENTITY_BASE/../base/pipe"

  set COMPONENTS [list \
      [list "IB_SWITCH_INPUT"    $IB_SWITCH_INPUT_BASE     "FULL"] \
      [list "IB_SWITCH_BUFFER"   $IB_SWITCH_BUFFER_BASE    "FULL"] \
      [list "IB_SWITCH_OUTPUT"   $IB_SWITCH_OUTPUT_BASE    "FULL"] \
      [list "IB_PIPE"            $IB_PIPE_BASE             "FULL"] \
  ]             

  set MOD "$MOD $ENTITY_BASE/../../pkg/ib_fmt_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/../../pkg/ib_ifc_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/pkg/switch_pkg.vhd"

  set MOD "$MOD $ENTITY_BASE/switch_slave.vhd"
  set MOD "$MOD $ENTITY_BASE/switch_slave_arch.vhd"

  set MOD "$MOD $ENTITY_BASE/switch_master.vhd"
  set MOD "$MOD $ENTITY_BASE/switch_master_arch.vhd"

#  set MOD "$MOD $ENTITY_BASE/top/switch_slave_64.vhd"
#  set MOD "$MOD $ENTITY_BASE/top/switch_master_64.vhd"

#  set MOD "$MOD $ENTITY_BASE/top/switch_slave_32.vhd"
#  set MOD "$MOD $ENTITY_BASE/top/switch_master_32.vhd"

#  set MOD "$MOD $ENTITY_BASE/top/switch_slave_16.vhd"
#  set MOD "$MOD $ENTITY_BASE/top/switch_master_16.vhd"

#  set MOD "$MOD $ENTITY_BASE/top/switch_slave_8.vhd"
#  set MOD "$MOD $ENTITY_BASE/top/switch_master_8.vhd"
}

# -----------------------------------------------------------------------------

if { $ARCHGRP == "EMPTY" } {

}



