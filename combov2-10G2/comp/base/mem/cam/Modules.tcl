# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
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

set COMP_BASE     "$ENTITY_BASE/../../.."

# Source files for the component
if { $ENTITY == "CAM" } {
   if { $ARCHGRP == "CAM" } {
      #just CAM, without localbus support
      
      set MOD "$MOD $ENTITY_BASE/cam_dec1fn.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_element.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_fill_element.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_filling_part.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_row.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_data_array.vhd"
      set MOD "$MOD $ENTITY_BASE/cam.vhd"
      
      set PKG_BASE "$COMP_BASE/base/pkg"
      set COMPONENTS [list \
                        [ list "PKG"        $PKG_BASE          "MATH"] \
                     ]

   } elseif { $ARCHGRP == "FULL" } {
      #CAM with top_level with localbus support

      set MOD "$MOD $ENTITY_BASE/cam_dec1fn.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_element.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_fill_element.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_filling_part.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_row.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_data_array.vhd"
      set MOD "$MOD $ENTITY_BASE/cam.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_lb_bridge.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_top_level.vhd"
      
      set PKG_BASE "$COMP_BASE/base/pkg"
      set COMPONENTS [list \
                        [ list "PKG"        $PKG_BASE          "MATH"] \
                     ]
   } elseif { $ARCHGRP == "ADC" } {
      #CAM with top_level with localbus support; adc ifc only 
      #(without lb_connmem)

      set MOD "$MOD $ENTITY_BASE/cam_dec1fn.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_element.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_fill_element.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_filling_part.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_row.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_data_array.vhd"
      set MOD "$MOD $ENTITY_BASE/cam.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_lb_bridge.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_top_level_adc.vhd"
      
      set PKG_BASE "$COMP_BASE/base/pkg"
      set COMPONENTS [list \
                        [ list "PKG"        $PKG_BASE          "MATH"] \
                     ]
   } elseif { $ARCHGRP == "LIGHT" } {  
      #lightweight version of CAM made of registers

      set MOD "$MOD $ENTITY_BASE/cam_dec1fn.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_light_2port.vhd"
      set MOD "$MOD $ENTITY_BASE/cam_light.vhd"
      
      set PKG_BASE "$COMP_BASE/base/pkg"
      set COMPONENTS [list \
                        [ list "PKG"        $PKG_BASE          "MATH"] \
                     ]
   }
}
