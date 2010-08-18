global VHDL_BASE

# Modules variable
#set COMMON     "TESTS"
set CLKGEN     "FULL"
set LB         "FULL"


#Controllers

#Components
set ID   "LB"
set I2C  "FULL"

# Base Directories
set UNIT_BASE        "$VHDL_BASE/units"
set SFPRO_BASE       "$VHDL_BASE/sfpro/tests/"
set TEST_BASE        "$VHDL_BASE/tests/comp"

#set COMMON_BASE      "$UNIT_BASE/common"
set CLKGEN_BASE      "$TEST_BASE/clk_gen"
set LB_BASE          "$UNIT_BASE/lb"
set I2C_BASE         "$UNIT_BASE/i2c/"

set ID_BASE          "$UNIT_BASE/common/id"

# List of packages

#List of instances
set CLKGEN_INST     [list [list "CLKGEN_U"     "FULL"]]
set LB_INST         [list [list "LB_U"         "FULL"]]
set I2C_INST        [list [list "I2C_U"        "FULL"]]
set ID_INST         [list [list "ID_COMP_LB_U" "FULL"]]

# [list "COMMON"     $COMMON_BASE       $COMMON] \

#           

set COMPONENTS [list   \
      [list "I2C"        $I2C_BASE          $I2C        $I2C_INST ]\
      [list "LB"         $LB_BASE           $LB         $LB_INST    ]\
      [list "CLKGEN"     $CLKGEN_BASE       $CLKGEN     $CLKGEN_INST]\
      [list "ID"         $ID_BASE           $ID         $ID_INST    ]\
      ]

