# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/.."
set FIRMWARE_BASE          "$COMP_BASE/.."
set FL_BASE                "$COMP_BASE/fl_tools"

set FL_ASFIFO_BASE         "$FL_BASE/storage/asfifo"
set FL_ADDER_BASE          "$FL_BASE/edit/netcope_adder"
set CLOCK_GATE_BASE        "$COMP_BASE/clock_gate"
set FL_HW_DRIVER_BASE      "$COMP_BASE/hw_ver/fl_hw_driver"
set FL_HW_MONITOR_BASE     "$COMP_BASE/hw_ver/fl_hw_monitor"
set FL_VAL_CHECKER_BASE    "$COMP_BASE/hw_ver/fl_val_checker"
set FL_OBSERVER_BASE       "$COMP_BASE/hw_ver/fl_observer"
set RESET_GEN_BASE         "$COMP_BASE/hw_ver/reset_gen"
set FL_BINDER_BASE         "$FL_BASE/flow/binder"
set FL_COV_UNIT_BASE       "$COMP_BASE/hw_ver/fl_cov_unit"

# HW_SW_CODASIP
#set PROGRAM_DRIVER_BASE    "$COMP_BASE/hw_ver/program_driver"
#set HALT_MONITOR_BASE      "$COMP_BASE/hw_ver/halt_monitor"
#set MEMORY_MONITOR_BASE    "$COMP_BASE/hw_ver/memory_monitor"
#set PORTOUT_MONITOR_BASE   "$COMP_BASE/hw_ver/portout_monitor"


set FL_FIFO_BASE           "$FL_BASE/storage/fifo"
set HGEN_BASE              "$COMP_BASE/hgen"
set ERRONEOUS_FL_FIFO_BASE "$COMP_BASE/erroneous_fl_fifo"

# Source the HAVEN package
set PACKAGES "$PACKAGES $FIRMWARE_BASE/pkg/haven_const.vhd"

# Source files
set MOD "$MOD $ENTITY_BASE/verification_core_ent.vhd"
set MOD "$MOD $ENTITY_BASE/verification_core.vhd"

# Componentss
set COMPONENTS [list \
   [ list "FL_FIFO"            $FL_FIFO_BASE             "FULL"] \
   [ list "FL_BINDER"          $FL_BINDER_BASE           "FULL"] \
   [ list "FL_ASFIFO"          $FL_ASFIFO_BASE           "FULL"] \
   [ list "CLOCK_GATE"         $CLOCK_GATE_BASE          "FULL"] \
   [ list "FL_HW_DRIVER"       $FL_HW_DRIVER_BASE        "FULL"] \
   [ list "FL_HW_MONITOR"      $FL_HW_MONITOR_BASE       "FULL"] \
   [ list "RESET_GEN"          $RESET_GEN_BASE           "FULL"] \
   [ list "HGEN"               $HGEN_BASE                "FULL"] \
   [ list "ERRONEOUS_FL_FIFO"  $ERRONEOUS_FL_FIFO_BASE   "FULL"] \
   [ list "FL_VAL_CHECKER"     $FL_VAL_CHECKER_BASE      "FULL"] \
   [ list "FL_OBSERVER"        $FL_OBSERVER_BASE         "FULL"] \
   [ list "FL_COV_UNIT"        $FL_COV_UNIT_BASE         "FULL"] \

#   [ list "PROGRAM_DRIVER"     $PROGRAM_DRIVER_BASE      "FULL"] \
#   [ list "MEMORY_MONITOR"     $MEMORY_MONITOR_BASE      "FULL"] \
#   [ list "HALT_MONITOR"       $HALT_MONITOR_BASE        "FULL"] \
#   [ list "PORTOUT_MONITOR"    $PORTOUT_MONITOR_BASE     "FULL"] \
#   [ list "FL_ADDER"           $FL_ADDER_BASE            "FULL"] \

]
