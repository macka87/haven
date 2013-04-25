# Modules.tcl: Local include Modules tcl script

# Set paths
set FIRMWARE_BASE          "../../../"
set COMP_BASE              "$FIRMWARE_BASE/comp"
set FL_BASE                "$COMP_BASE/fl_tools"

# HW_SW_CODASIP verification environment architecture
set PROGRAM_DRIVER_BASE    "$COMP_BASE/hw_ver/program_driver"

# DUT - codix
set CODIX_BASE             "../../../../codix/vhdl"

# Source the HAVEN package
set PACKAGES "$PACKAGES $FIRMWARE_BASE/pkg/haven_const.vhd"

# Source files
set MOD "$MOD $ENTITY_BASE/verification_core_ent.vhd"
set MOD "$MOD $ENTITY_BASE/verification_core.vhd"

# Componentss
set COMPONENTS [list \
   [ list "PROGRAM_DRIVER"     $PROGRAM_DRIVER_BASE      "FULL"] \
   [ list "codix_ca_t"         $CODIX_BASE               "FULL"] \
]
