# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2010 CESNET
# Author: Karel Koranda <xkoran01@stud.fit.vutbr.cz>
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

# Paths
set COMP_BASE     "$ENTITY_BASE/../../.."

   set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_gen.vhd"
   set MOD "$MOD $ENTITY_BASE/top/ver/sw_rxbuf_gen_ver.vhd"

   # components
   set COMPONENTS [list \
      [ list "PKG_MATH"       $COMP_BASE/base/pkg              "MATH"] \
      [ list "DEC1FN_ENABLE"  $COMP_BASE/base/logic/dec1fn     "FULL"] \
      [ list "GEN_DEMUX"      $COMP_BASE/base/logic/demux      "FULL"] \
      [ list "GEN_MUX"        $COMP_BASE/base/logic/mux        "FULL"] \
      [ list "MFIFO2MEM"      $COMP_BASE/base/buffers/top      "FULL"] \
      [ list "FL_MULTIPLEXER" $COMP_BASE/fl_tools/flow/multiplexer "FULL"] \
   ]
