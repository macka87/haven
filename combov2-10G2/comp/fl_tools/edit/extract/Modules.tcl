# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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

set COMP_BASE   "$ENTITY_BASE/../../.."
set PKG_BASE    "$COMP_BASE/base/pkg"


# Entities
set MOD "$MOD $ENTITY_BASE/fl_extract_top.vhd"

# Global FrameLink package
set MOD "$MOD $ENTITY_BASE/../../pkg/fl_pkg.vhd"
      
# Wrappers for FL_EXTRACT
set MOD "$MOD $ENTITY_BASE/fl_extract_fl16.vhd"
set MOD "$MOD $ENTITY_BASE/fl_extract_fl32.vhd"
set MOD "$MOD $ENTITY_BASE/fl_extract_fl64.vhd"
set MOD "$MOD $ENTITY_BASE/fl_extract_fl128.vhd"

# Decoder subcomponent
set MOD "$MOD $ENTITY_BASE/fl_extract_decoder.vhd"

if { $ARCHGRP == "FULL" } {
      
      # Full architecture
      set MOD "$MOD $ENTITY_BASE/fl_extract_full.vhd"

   }

if { $ARCHGRP == "EMPTY" } {
      # Empty architectures
      set MOD "$MOD $ENTITY_BASE/fl_extract_empty.vhd"
   }

# components
set COMPONENTS [list [list "PKG_MATH"        $PKG_BASE       "MATH"]]
