# Source files for all components

set COMP_BASE          "$ENTITY_BASE/../../combov2/comp"
set MULT_BASE          "$ENTITY_BASE/../mult/"

# Base directories
set PKG_BASE    "$COMP_BASE/base/pkg"
set MOD         "$MOD $MULT_BASE/mult.vhd"
set MOD         "$MOD $ENTITY_BASE/alu.vhd"

# components
set COMPONENTS [list \
  [ list "PKG_MATH"        $PKG_BASE         "MATH"] \
]
