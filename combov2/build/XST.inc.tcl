# XST.inc.tcl:tcl include script to generate files needed for synthesis with XST
# Copyright (C) 2006 CESNET
# Author: Viktor Pus     <pus@liberouter.org>
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
#                     Procedures and functions
# ---------------------------------------------------------------------

# procedure EvalInstance evaluates given instance at INST_PATH and can include
# XST.tcl file specified in COMP_PATH
proc EvalInstance { COMP_PATH ENTITY ARCHITECTURE INST_PATH PARAMS} {
   puts "Instance $INST_PATH detected"
   upvar 1 $PARAMS param_array

   if { [file exist "$COMP_PATH/XST.tcl" ] } {
      source $COMP_PATH/XST.tcl
      if { [info procs "SetAttribConstr"] == "SetAttribConstr" } {
         set CONSTR [SetAttribConstr $ENTITY $ARCHITECTURE $INST_PATH param_array]

         if { $CONSTR != "" } {
            puts "Attributes and Constrains applied to $INST_PATH"

            # Add constraints to xcf file
            set filedesc [open "XST.xcf" "a"]
            puts $filedesc "# Constraints from entity $ENTITY:"
            foreach i $CONSTR {
               puts $filedesc $i
            }
            close $filedesc
         }
      }
   }
}

# Add one file to XST.prj
proc EvalFile { FILE } {
   set filedesc [open "XST.prj" "a"]

   if { [llength $FILE] == 2 } {
      set LIB [lindex $FILE 0]
      set FNAME [lindex $FILE 1]
   } else {
      set LIB "work"
      set FNAME $FILE
   }

   if { [regexp {^.*\.v$} $FNAME] } {
      set LANG "verilog"
   } else {
      set LANG "vhdl"
   }

   puts $filedesc "$LANG $LIB $FNAME"

   close $filedesc
   puts "file $FILE added"
}

# ---------------------------------------------------------------------
# Procedure SetupDesign - creates a new fpga.xst project file. 
# If the file already exists, it is removed. 
# Next this procedure sets the type of FPGA chip, name and type of output.
# 
proc SetupDesign { SYNTH_FLAGS } {

   # Open file for writing (delete if exists)
   set filedesc [open "XST.xst" "w"]

   upvar 1 $SYNTH_FLAGS synth
   set FPGA    $synth(FPGA)
   set MODULE  $synth(MODULE)
   set OUTPUT  $synth(OUTPUT)
   if { [info exists synth(SETUP_FLAGS)] } {
      set SETUP_FLAGS $synth(SETUP_FLAGS)
   } else {
      set SETUP_FLAGS ""
   }

   # Write several lines which does not change
   # Directories setting
   puts $filedesc "set -tmpdir \"./xst/projnav.tmp\""
   puts $filedesc "set -xsthdpdir \"./xst\""
   # run command, followig is a long list of pairs -parameter value
   puts $filedesc "run"
   puts $filedesc "-ifn XST.prj"
   puts $filedesc "-ofn $OUTPUT"
   puts $filedesc "-ofmt NGC"
   puts $filedesc "-rtlview YES"
   puts $filedesc "-top $MODULE"
   puts $filedesc "-uc XST.xcf"
   puts $filedesc "-hdl_compilation_order user"

   # Gather toplevel generics from USER_GENERICS list
   set XST_GENERICS ""
   if { [info exists synth(USER_GENERICS)] } {
      set USER_GENERICS $synth(USER_GENERICS)
      foreach i $USER_GENERICS {
         set GENERIC [format "%s=%s" [lindex $i 0] [lindex $i 1]]
         lappend XST_GENERICS $GENERIC
      }
   }

   # Get unix time and UID and set them as a generics
   set TIME [format "BUILD_TIME=%d" [clock seconds]]
   set UID [format "BUILD_UID=%d" [exec id -u]]
   puts $filedesc "-generics {$XST_GENERICS $TIME $UID}"


   # technology library setting
   if { $FPGA == "xc2v1000" } {
      puts $filedesc "-p xc2v1000-4-fg456"
   } elseif { $FPGA == "xc2v2000" } {
      puts $filedesc "-p xc2v2000-4-fg676"
   } elseif { $FPGA == "xc2v3000" } {
      puts $filedesc "-p xc2v3000-4-bf957"
   } elseif { $FPGA == "xc2vp20" } {
      puts $filedesc "-p xc2vp20-6-ff896"
   } elseif { $FPGA == "xc2vp30" } {
      puts $filedesc "-p xc2vp30-7-ff896"
   } elseif { $FPGA == "xc2vp50" } {
      puts $filedesc "-p xc2vp50-5-ff1517"
   } elseif { $FPGA == "xc3s200" } {
      puts $filedesc "-p xc3s200-4-pq208"
   } elseif { $FPGA == "xc5vlx110t" } {
      puts $filedesc "-p xc5vlx110t-1-ff1136"
   } elseif { $FPGA == "xc5vlx110t-2" } {
      puts $filedesc "-p xc5vlx110t-2-ff1136"
   } elseif { $FPGA == "xc5vlx155t" } {
      puts $filedesc "-p xc5vlx155t-1-ff1136"
   } elseif { $FPGA == "xc5vlx155t-2" } {
      puts $filedesc "-p xc5vlx155t-2-ff1136"
   } elseif { $FPGA == "xc5vfx100t" } {
      puts $filedesc "-p xc5vfx100t-2-ff1136"
   } elseif { $FPGA == "xc5vlx50t" } {
      puts $filedesc "-p xc5vlx50t-1-ff1136"
   } elseif { $FPGA == "xc5vtx150t" } {
      puts $filedesc "-p xc5vtx150t-2-ff1156"
   } elseif { $FPGA == "xc5vlx50t-ff665" } {
      puts $filedesc "-p xc5vlx50t-1-ff665"
   } else {
      puts "ERROR : Unknown FPGA variable $FPGA."
      exit 1
   }

   # Define set of default parameters of run command. 
   # These may be extended or modified by SETUP_FLAGS
   set default_params [list \
                         [list "-opt_mode" "Speed"] \
                         [list "-opt_level" "2"] \
                         [list "-iobuf" "Yes"] \
                         [list "-iob" "auto"] \
                         [list "-bus_delimiter" "()"] \
                      ]

   # apply user settings (if any)
   # Each default parameter is added to SETUP_FLAGS if that parameter
   # is not already there.
   if { $SETUP_FLAGS != "" } {
      foreach i $default_params {
         set match 0
         foreach j $SETUP_FLAGS {
            if { [lindex $i 0] == [lindex $j 0] } {
               set match 1
            }
         }
         if { $match == 0 } {
            set SETUP_FLAGS [linsert $SETUP_FLAGS 0 $i]
         }
      }
   } else {
      set SETUP_FLAGS $default_params
   }

   # Write each parameter from resulting SETUP_FLAGS to fpga.xst
   foreach i $SETUP_FLAGS {
      puts $filedesc [concat [lindex $i 0] [lindex $i 1]]
   }

   close $filedesc

   PrintLabel "Project run script generated to file XST.xst."
}

# ---------------------------------------------------------------------
# Procedure AddInputFiles - recursively goes through the components hierarchy
# and adds all design files to .prj file. Procedure
# parameters define the design hierarchy
# 
proc AddInputFiles { HIERARCHY } {
   upvar 1 $HIERARCHY hier
   set FILES [list ]
   set SV_LIBS [list ]

   set filedesc [open "XST.prj" "w"]
   close $filedesc

   PrintLabel "Generating list of source files..."

   # Compile PACKAGES - if they was defined
   if { [info exists hier(PACKAGES)] } {
      PrintLabel "Packages"
      ApplyToMods $hier(PACKAGES) "EvalFile" FILES
   }
   
   # Compile components
   if { [info exists hier(COMPONENTS)] } {
      ApplyToComponents $hier(COMPONENTS) "EvalFile" FILES SV_LIBS
   }
   
   # Compile MODs - if they was defined
   if { [info exists hier(MOD)] } {
      PrintLabel "MODs Compilation"
      ApplyToMods $hier(MOD) "EvalFile" FILES
   }
   
   # Compile Top Level
   if { [info exists hier(TOP_LEVEL)] } {
      PrintLabel "Top Level Compilation"
      ApplyToMods $hier(TOP_LEVEL) "EvalFile" FILES
   }

   PrintLabel "List of source files generated to file XST.prj."
}

# ---------------------------------------------------------------------
# Procedure AttribConstrDesign - recursively goes throught the design hierarchy
# and calls the function SetAttribConstr to all instances.  SetAttribConstr
# is localy defined in component's XST.tcl file.
# 
proc AttribConstrDesign { SYNTH_FLAGS HIERARCHY } { 
   upvar 1 $HIERARCHY hier_array
   upvar 1 $SYNTH_FLAGS synth_array

   if { [info exist synth_array(FPGA)] } {
      set PARAMS(FPGA) $synth_array(FPGA)
   }

   if { [info exist synth_array(CARD)] } {
      set PARAMS(CARD) $synth_array(CARD)
   } else {
      set PARAMS(CARD) "Combo6"
   }

   if { [info exist hier_array(MODULE)] } {
      set PARAMS(MODULE) $hier_array(MODULE)
   }

   set filedesc [open "XST.xcf" "w"]
      puts $filedesc "# This file was generated by translation system."
   close $filedesc

   # Attributes and constrains setting for all instances
   if { [info exists hier_array(COMPONENTS)] } {
      ApplyToInstances $hier_array(COMPONENTS) "EvalInstance" PARAMS
   }

   # Attributes and constrains setting for top_level
   if { [info procs "SetTopAttribConstr"] == "SetTopAttribConstr" } {
      set CONSTR [SetTopAttribConstr]
      if { $CONSTR != "" } {
         set filedesc [open "XST.xcf" "a"]
         puts $filedesc "# Toplevel constraints"
         foreach i $CONSTR {
            puts $filedesc $i
         }
      }
   }

   PrintLabel "Constraints generated to file XST.xcf"
}


# ---------------------------------------------------------------------
# Procedure SynthesizeProject - automaticly performs all previosly defined
# procedures. Alternatively to this function, an user can manualy call
# previously defined procedures and use addition commands to customize
# synthesis process
#
proc SynthesizeProject { SYNTH_FLAGS HIERARCHY } {
   upvar 1 $SYNTH_FLAGS synth_array
   upvar 1 $HIERARCHY hier_array

   # synthesis setting
   SetupDesign synth_array

   # add input files
   AddInputFiles hier_array

   # attributes and constrains setting
   AttribConstrDesign synth_array hier_array
}

