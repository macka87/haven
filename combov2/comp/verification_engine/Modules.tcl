# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/.."
set FL_BASE                "$COMP_BASE/fl_tools"

set FL_ADDER_BASE          "$FL_BASE/edit/netcope_adder"
set VER_CORE_BASE          "$COMP_BASE/verification_core"
set FL_ADAPTER_BASE        "$COMP_BASE/hw_ver/fl_adapter"
set MT_BASE                "$COMP_BASE/hw_ver/random_generator/mersenne_twister_gen_n"

# Source files
set MOD "$MOD $ENTITY_BASE/verification_engine_ent.vhd"

# Components
set COMPONENTS [list \
   [ list "FL_ADDER"           $FL_ADDER_BASE         "FULL"] \
]

##############################################################################
# The CORE architecture contains:
#
#   * driver
#   * verification core
#   * monitor
#   * assertion checker at the output interface
#   * signal observer
##############################################################################
if { $ARCHGRP == "CORE" } {
  set MOD "$MOD $ENTITY_BASE/verification_engine_core.vhd"

   set COMPONENTS [concat $COMPONENTS [list \
     [ list "VER_CORE"           $VER_CORE_BASE         "FULL"] \
   ]]
}


##############################################################################
# The HW_GEN architecture contains:
#
#   * random number generator
#   * FrameLink adapter
##############################################################################
if { $ARCHGRP == "HW_GEN" } {
  set MOD "$MOD $ENTITY_BASE/verification_engine_hw_gen.vhd"

   set COMPONENTS [concat $COMPONENTS [list \
     [ list "FL_ADAPTER"           $FL_ADAPTER_BASE         "FULL"] \
     [ list "MT"                   $MT_BASE                 "FULL"] \
   ]]
}
