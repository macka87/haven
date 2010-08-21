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
   
  set IB_ENDPOINT_BM_UNIT_BASE    "$ENTITY_BASE/comp/bm_unit"
  set IB_ENDPOINT_DOWN_BUF_BASE   "$ENTITY_BASE/comp/down_buf"
  set IB_ENDPOINT_UP_BUF_BASE     "$ENTITY_BASE/comp/up_buf"  
  set IB_ENDPOINT_READ_CTRL_BASE  "$ENTITY_BASE/comp/read_ctrl"
  set IB_ENDPOINT_WRITE_CTRL_BASE "$ENTITY_BASE/comp/write_ctrl"
  set EPI2MI_CONVERTER_BASE       "$ENTITY_BASE/../../../mi_bus/epi2mi_converter"

  set COMPONENTS [list \
      [list "IB_ENDPOINT_BM_UNIT   " $IB_ENDPOINT_BM_UNIT_BASE    "FULL"] \
      [list "IB_ENDPOINT_DOWN_BUF  " $IB_ENDPOINT_DOWN_BUF_BASE   "FULL"] \
      [list "IB_ENDPOINT_UP_BUF    " $IB_ENDPOINT_UP_BUF_BASE     "FULL"] \
      [list "IB_ENDPOINT_READ_CTRL " $IB_ENDPOINT_READ_CTRL_BASE  "FULL"] \
      [list "IB_ENDPOINT_WRITE_CTRL" $IB_ENDPOINT_WRITE_CTRL_BASE "FULL"] \
      [list "EPI2MI_CONVERTER      " $EPI2MI_CONVERTER_BASE       "FULL"] \
  ]
  
  set MOD "$MOD $ENTITY_BASE/comp/strict_unit.vhd"
  
  set MOD "$MOD $ENTITY_BASE/../../pkg/ib_fmt_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/../../pkg/ib_ifc_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/pkg/endpoint_pkg.vhd"

  set MOD "$MOD $ENTITY_BASE/endpoint.vhd"
  set MOD "$MOD $ENTITY_BASE/endpoint_arch.vhd"

#  set MOD "$MOD $ENTITY_BASE/top/endpoint_slave_64.vhd"
#  set MOD "$MOD $ENTITY_BASE/top/endpoint_master_64.vhd"

#  set MOD "$MOD $ENTITY_BASE/top/endpoint_slave_32.vhd"
#  set MOD "$MOD $ENTITY_BASE/top/endpoint_master_32.vhd"

#  set MOD "$MOD $ENTITY_BASE/top/endpoint_slave_16.vhd"
#  set MOD "$MOD $ENTITY_BASE/top/endpoint_master_16.vhd"

#  set MOD "$MOD $ENTITY_BASE/top/endpoint_slave_8.vhd"
#  set MOD "$MOD $ENTITY_BASE/top/endpoint_master_8.vhd"

  set MOD "$MOD $ENTITY_BASE/top/endpoint_mi.vhd"
}

# -----------------------------------------------------------------------------

if { $ARCHGRP == "EMPTY" } {

}



