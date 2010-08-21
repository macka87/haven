# Modules.tcl: Local include tcl script
# Copyright (C) 2005 CESNET
# Author: Stepan Friedl <friedl@liberouter.org>
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

# Base directories
set BASE_BASE     "$ENTITY_BASE/../../../base"
set ASFIFO_BASE   "$BASE_BASE/fifo/asfifo"

# Source files for implemented component
if { $GMII_REP == "FULL" } {
   # List of components
   set COMPONENTS [list [list "ASFIFO"       $ASFIFO_BASE     "FULL"] \
                  ]
   set MOD "$MOD $GMII_REP_BASE/comp/rx_fsm.vhd"
   set MOD "$MOD $GMII_REP_BASE/comp/tx_fsm.vhd"
   set MOD "$MOD $GMII_REP_BASE/pckt_fwd.vhd"
   set MOD "$MOD $GMII_REP_BASE/rep_2port.vhd"
}

# Source file for empty component - empty architecture
if { $GMII_REP == "EMPTY" } {
}
