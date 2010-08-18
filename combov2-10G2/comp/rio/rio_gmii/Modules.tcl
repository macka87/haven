# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
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

set COMP_BASE     $ENTITY_BASE/../..
set PCS_BASE      $COMP_BASE/nic/pcs
set LB_BASE       $COMP_BASE/lb

set LB      	   "FULL"
set LB_INST       [list [list "LOCAL_BUS_U"           "FULL"]]

# FULL rio_gmii
if { $ARCHGRP == "FULL" } { 
   set MOD "$MOD $ENTITY_BASE/rio_gmii.vhd"

   set COMPONENTS [list \
                     [list "PCS"       $PCS_BASE      "FULL"               ] \
                  ]
}

# rio_gmii for CV2
if { $ARCHGRP == "CV2" } { 
   set MOD "$MOD $ENTITY_BASE/rio_gmii_cv2.vhd"

   set COMPONENTS [list \
                     [list "PCS"       $PCS_BASE      "FULL"               ] \
                  ]
}

# FULL rio_gmii with debug support
if { $ARCHGRP == "DEBUG" } { 
   set MOD "$MOD $ENTITY_BASE/rio_gmii.vhd"
   set MOD "$MOD $ENTITY_BASE/rio_gmii_debug.vhd"

   set COMPONENTS [list \
                     [list "PCS"       $PCS_BASE      "FULL"               ] \
                     [list "LB"      	$LB_BASE      	$LB      	$LB_INST ] \
                  ]
}

