# 
# XST.tcl: XST tcl script to compile specified module
# Author: Stepan Friedl, friedl@liberouter.org
# Copyright (C) 2007 INVEA-TECH
#

# specify vhdl_design directory
set BASE       "../../../../../../.."
set FIRMWARE_BASE  $BASE

# synthesis variables
set SYNTH_FLAGS(MODULE) "ml555"
set SYNTH_FLAGS(OUTPUT) "ml555_arch"
set SYNTH_FLAGS(FPGA)   "xc5vlx50t"

# hierarchy setting
set PACKAGES   ""
set COMPONENTS ""
set MOD        ""

# list of sub-components
source Modules.tcl

set HIERARCHY(COMPONENTS)  $COMPONENTS
set HIERARCHY(PACKAGES)    $PACKAGES
set HIERARCHY(MOD)         $MOD
set HIERARCHY(TOP_LEVEL)   "ml555.vhd \
                            ml555_arch.vhd"

proc SetTopAttribConstr { } {
   set CONSTR [list \
                  "BEGIN MODEL \"ml555\"" \
                  "NET \"SYS_CLK\" PERIOD = 100MHz HIGH 50%;" \
                  "END;"\
   ]
   return $CONSTR
}

# Run global precision tcl script to include general functions
source $BASE/build/XST.inc.tcl

# In fact, XST tcl script only generates XST script named XST.xst.
SynthesizeProject SYNTH_FLAGS HIERARCHY

# Now Makefile will call 'xst -ifn XST.xst' to perform the synthesis.
