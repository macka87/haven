# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/.."
set FIRMWARE_BASE          "$COMP_BASE/.."
set FL_BASE                "$COMP_BASE/fl_tools"

set FL_ADDER_BASE          "$FL_BASE/edit/netcope_adder"
set VER_CORE_BASE          "$COMP_BASE/verification_core_codix"

# Source files
set MOD "$MOD $ENTITY_BASE/verification_engine_ent.vhd"

# Components
set COMPONENTS [list \
   [ list "FL_ADDER"           $FL_ADDER_BASE         "FULL"] \
]

##############################################################################
# The CORE architecture contains:
#
#   * drivers
#   * DUT
#   * monitors
#   * fl binder
#   * fl adder
##############################################################################
if { $ARCHGRP == "CORE" } {
  set MOD "$MOD $ENTITY_BASE/verification_engine_core.vhd"

   set COMPONENTS [concat $COMPONENTS [list \
     [ list "VER_CORE"           $VER_CORE_BASE         "FULL"] \
   ]]
}

##############################################################################
# The HW_SW_CODASIP architecture contains:
#
#   * program driver
#   * DUT (Codix)
#   * memory monitor
#   * halt monitor
#   * portout monitor
#   * fl binder
##############################################################################
if { $ARCHGRP == "HW_SW_CODASIP" } {

  # Source the HAVEN package
  set PACKAGES "$PACKAGES $FIRMWARE_BASE/pkg/haven_const.vhd"

  set MOD "$MOD $ENTITY_BASE/verification_engine_core.vhd"

   set COMPONENTS [concat $COMPONENTS [list \
     [ list "PROGRAM_DRIVER"       $PROGRAM_DRIVER_BASE  "FULL"] \
     [ list "MEMORY_MONITOR"       $MEMORY_MONITOR_BASE  "FULL"] \
     [ list "HALT_MONITOR_BASE"    $HALT_MONITOR_BASE    "FULL"] \
     [ list "PORTOUT_MONITOR_BASE" $PORTOUT_MONITOR_BASE "FULL"] \
     [ list "FL_ADDER_BASE"        $FL_ADDER_BASE        "FULL"] \

   ]]
}

##############################################################################
# The HW_GEN architecture contains:
#
#   * random number generator
#   * FrameLink adapter
##############################################################################
if { $ARCHGRP == "HW_GEN" } {
  # Source the HAVEN package
  set PACKAGES "$PACKAGES $FIRMWARE_BASE/pkg/haven_const.vhd"

  set MOD "$MOD $ENTITY_BASE/verification_engine_hw_gen.vhd"

   set COMPONENTS [concat $COMPONENTS [list \
     [ list "FL_RAND_GEN"      $FL_RAND_GEN_BASE    "FULL"] \
   ]]
}

##############################################################################
# The HW_GEN_CORE architecture contains CORE and HW_GEN, namely:
#
#   * random number generator
#   * FrameLink adapter
#   * FrameLink command unit
#   * driver
#   * DUT
#   * monitor
#   * assertion checker at the output interface
#   * signal observer
##############################################################################
if { $ARCHGRP == "HW_GEN_CORE" } {
  # Source the HAVEN package
  set PACKAGES "$PACKAGES $FIRMWARE_BASE/pkg/haven_const.vhd"

  set MOD "$MOD $ENTITY_BASE/verification_engine_hw_gen_core.vhd"

   set COMPONENTS [concat $COMPONENTS [list \
     [ list "VER_CORE"           $VER_CORE_BASE         "FULL"] \
     [ list "FL_RAND_GEN"        $FL_RAND_GEN_BASE      "FULL"] \
     [ list "FL_COM_UNIT"        $FL_COM_UNIT_BASE      "FULL"] \
   ]]
}

##############################################################################
# The HW_FULL architecture contains 2 COREs, HW_GEN, and SCOREBOARD, namely:
#
#   * random number generator
#   * FrameLink adapter
#   * FrameLink command unit
#   * 2 verification cores, in each:
#     * driver
#     * DUT
#     * monitor
#     * assertion checker at the output interface
#     * signal observer
#     * FrameLink filter
#   * Scoreboard
##############################################################################
if { $ARCHGRP == "HW_FULL" } {
  # Source the HAVEN package
  set PACKAGES "$PACKAGES $FIRMWARE_BASE/pkg/haven_const.vhd"

  set MOD "$MOD $ENTITY_BASE/verification_engine_hw_full.vhd"

   set COMPONENTS [concat $COMPONENTS [list \
     [ list "VER_CORE"           $VER_CORE_BASE         "FULL"] \
     [ list "FL_RAND_GEN"        $FL_RAND_GEN_BASE      "FULL"] \
     [ list "FL_COM_UNIT"        $FL_COM_UNIT_BASE      "FULL"] \
     [ list "FL_SCOREBOARD"      $FL_SCOREBOARD_BASE    "FULL"] \
     [ list "FL_FILTER"          $FL_FILTER_BASE        "FULL"] \
     [ list "FL_WATCH"           $FL_WATCH_BASE         "FULL"] \
   ]]
}
