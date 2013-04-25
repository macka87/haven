# Modules.tcl: Local include Modules tcl script

# Set paths
set COMP_BASE              "$ENTITY_BASE/.."
set FIRMWARE_BASE          "$COMP_BASE/.."
set FL_BASE                "$COMP_BASE/fl_tools"

# HW_SW_CODASIP verification environment architecture
set HALT_MONITOR_BASE      "$COMP_BASE/hw_ver/halt_monitor"
set PORTOUT_MONITOR_BASE   "$COMP_BASE/hw_ver/portout_monitor"
set REGISTER_MONITOR_BASE  "$COMP_BASE/hw_ver/register_monitor"
set MEMORY_MONITOR_BASE    "$COMP_BASE/hw_ver/memory_monitor"
set FL_BINDER_BASE         "$COMP_BASE/hw_ver/fl_binder"

# Source the HAVEN package
set PACKAGES "$PACKAGES $FIRMWARE_BASE/pkg/haven_const.vhd"

# Source files
set MOD "$MOD $ENTITY_BASE/verification_core_ent.vhd"
set MOD "$MOD $ENTITY_BASE/verification_core.vhd"

# Componentss
set COMPONENTS [list \
   [ list "HALT_MONITOR"       $HALT_MONITOR_BASE        "FULL"] \
   [ list "PORTOUT_MONITOR"    $PORTOUT_MONITOR_BASE     "FULL"] \
   [ list "REGISTER_MONITOR"   $REGISTER_MONITOR_BASE    "FULL"] \
   [ list "MEMORY_MONITOR"     $MEMORY_MONITOR_BASE      "FULL"] \
   [ list "FL_BINDER"          $FL_BINDER_BASE           "FULL"] \

]
