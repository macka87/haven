# Leonardo.inc.tcl: Leonardo global include tcl script to compille all design
# Copyright (C) 2003 CESNET
# Authors: Tomas Martinek <martinek@liberouter.org>
#          Viktor Pus     <pus@liberouter.org>
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

source $FIRMWARE_BASE/build/Shared.tcl

# ---------------------------------------------------------------------
#                     Procedures and Functions
# ---------------------------------------------------------------------

# procedure EvalInstance evaluates given instance at INST_PATH and can include
# Precision.tcl file specified in COMP_PATH
proc EvalInstance { COMP_PATH ENTITY ARCHITECTURE INST_PATH PARAMS} {
   puts "Instance $INST_PATH detected"
   upvar 1 $PARAMS param_array

   if { [file exist "$COMP_PATH/Leonardo.tcl" ] } {
      source $COMP_PATH/Leonardo.tcl
      if { [info procs "SetAttribConstr"] == "SetAttribConstr" } {
         puts "Attributes and Constrains applied to $INST_PATH"
         SetAttribConstr $ENTITY $ARCHITECTURE $INST_PATH param_array
      }
   }
}

# If $FILE is two-item list, we will use only the second item
proc EvalFile { FILE } {
   if { [llength $FILE] == 2 } {
      set FNAME [lindex $FILE 1]
   } else {
      set FNAME $FILE
   }

   analyze $FNAME
}

# ---------------------------------------------------------------------
#                        Configuration part
# ---------------------------------------------------------------------
clean_all

# Parameters for local Leonardo.tcl files
if { [info exist FPGA] } {
   set PARAMS(FPGA) $FPGA
}

if { [info exist CARD] } {
   set PARAMS(CARD) $CARD
} else {
   set PARAMS(CARD) "Combo6"
}

if { [info exist MODULE] } {
   set PARAMS(MODULE) $MODULE
} else {
   set PARAMS(MODULE) "Generic"
}

# verification setting
if { $OUTPUT == "top_level.v" } {
   set extract_ram FALSE
   set tristate_map TRUE
}

# technology library setting
if { [info exist FPGA] } {
   if { $FPGA == "xc2v1000" } {
      set TARGET "xcv2"
      set part 2V1000fg456
      set process 4
      set wire_table xcv2-1000-4_wc
      load_library xcv2
   } elseif { $FPGA == "xc2v2000" } {
      set TARGET "xcv2"
      set part 2V2000fg676
      set process 4
      set wire_table xcv2-2000-4_wc
      load_library xcv2
   } elseif { $FPGA == "xc2v3000" } {
      set TARGET "xcv2"
      set part 2V3000bf957
      set process 4
      set wire_table xcv2-3000-4_wc
      load_library xcv2
   } elseif { $FPGA == "xc2vp20" } {
      set TARGET "xcv2p"
      set part 2VP20ff896
      set process 6
      set wire_table xcv2p-20-5_wc
      load_library xcv2p
   } elseif { $FPGA == "xc2vp30" } {
      set TARGET "xcv2p"
      set part 2VP30ff896
      set process 7
      set wire_table xcv2p-30-5_wc
      load_library xcv2p
   } elseif { $FPGA == "xc2vp50" } {
      set TARGET "xcv2p"
      set part 2VP50ff1517
      set process 5
      set wire_table xcv2p-2-7_wc
      load_library xcv2p
   } elseif { $FPGA == "xc3s200" } {
      set TARGET "xis3"
      set part xc3s200pq208
      set process 4
      set wire_table xc3s200-4_wc
      load_library xis3
   } else {
      puts "ERROR : Unknown FPGA variable."
      exit 1
   }
# xc2v3000 is default
} else {
   set part 2V3000bf957
   set process 4
   set wire_table xcv2-3000-4_wc
   load_library xcv2
}


# ---------------------------------------------------------------------
#                         Compilation
# ---------------------------------------------------------------------

set FILES [list ]

# Saves MOD variable - Components have to be compiled first
if { [info exist MOD] } {
   set MOD_SAVE $MOD
}

# Saves MOD variable - Components have to be compiled first
if { [info exist IOB] } {
   set IOB_SAVE $IOB
}

# Compile PACKAGES - if they was defined
if { [info exist PACKAGES] } {
   PrintLabel "Packages Compilation"
   ApplyToMods $PACKAGES EvalFile FILES
}

# Compile components
if { [info exist COMPONENTS] } {
   ApplyToComponents $COMPONENTS EvalFile FILES
}

# Compile MODs - if they was defined
if { [info exist MOD_SAVE] } {
   PrintLabel "MODs Compilation"
   puts $MOD_SAVE
   ApplyToMods $MOD_SAVE EvalFile FILES
}

# Read top level vhdl files
if { [info exist TOP_LEVEL] } {
   PrintLabel "Top Level"
   ApplyToMods $TOP_LEVEL EvalFile FILES
}

PrintLabel "Elaborate"
elaborate $ELABORATE


PrintLabel "Attributes and Constrains Setting"

# Attributes and constrains setting for all instances
if { [info exists COMPONENTS] } {
   ApplyToInstances $COMPONENTS "EvalInstance" PARAMS
}

# Attributes and constrains setting for top_level
if { [info procs "SetTopAttribConstr"] == "SetTopAttribConstr" } {
   SetTopAttribConstr 
}

# ---------------------------------------------------------------------
#                        Synthesize part
# ---------------------------------------------------------------------
# Default hierarchy setting
if { ! [info exist HIERARCHY] } {
   set HIERARCHY "auto"
}

# Default pre-optimize flags setting
if { ! [info exist PREOPTIMIZE_FLAGS] } {
   set PREOPTIMIZE_FLAGS "-common_logic -unused_logic -boundary -xor_comparator_optimize -extract"
}

# Default optimize flags setting
if { ! [info exist OPTIMIZE_FLAGS] } {
   set OPTIMIZE_FLAGS "-target $TARGET -hierarchy $HIERARCHY"
}

# Default write flags setting
if { ! [info exist WRITE_FLAGS] } {
   set WRITE_FLAGS "-format edif"
}

# Pre-optimize
PrintLabel "Pre-optimize"
eval "pre_optimize $PREOPTIMIZE_FLAGS"

# Optimize
PrintLabel "Optimize"
eval "optimize $OPTIMIZE_FLAGS"

# Write
PrintLabel "Write"
set_xilinx_eqn
eval "write $WRITE_FLAGS $OUTPUT"

# ---------------------------------------------------------------------
# Remove used variables
RemoveVars "FPGA MOD MOD_SAVE IOB IOB_SAVE COMPONENTS TOP_LEVEL \
            PACKAGES NOOPT_COMPS ELABORATE OUTPUT"

