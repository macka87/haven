# Precision.inc.tcl: Precision global include tcl script to compile all design
# Copyright (C) 2003 CESNET
# Author: Tomas Marek    <marekt@liberouter.org>
#         Tomas Martinek <martinek@liberouter.org>
#         Viktor Pus     <pus@liberouter.org>
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
# Precision.tcl file specified in COMP_PATH
proc EvalInstance { COMP_PATH ENTITY ARCHITECTURE INST_PATH PARAMS} {
   puts "Instance $INST_PATH detected"
   upvar 1 $PARAMS param_array

   if { [file exist "$COMP_PATH/Precision.tcl" ] } {
      source $COMP_PATH/Precision.tcl
      if { [info procs "SetAttribConstr"] == "SetAttribConstr" } {
         puts "Attributes and Constrains applied to $INST_PATH"
         SetAttribConstr $ENTITY $ARCHITECTURE $INST_PATH param_array
      }
   }
}

# If $FILE is two-item list, we will compile to another library than work
proc EvalFile { FILE } {
   if { [llength $FILE] == 2 } {
      set FNAME [lindex $FILE 1]
      set LIB [lindex $FILE 0]
   } else {
      set FNAME $FILE
      set LIB "work"
   }

   add_input_file -work $LIB $FNAME
}

# ---------------------------------------------------------------------
# Procedure SetupDesign - creates a new project with the name defined in MODULE
# parameter. If the project already exists, it removes the project including
# all its implementations. It sets the type of FPGA chip, for the synthesis is
# performed and finaly it sets the name of the output edif file defined in
# OUTPUT parameter.
# 
proc SetupDesign { SYNTH_FLAGS } {
   # Resets Precision to the clean state where no project is open and no 
   # results directory is set.
   reset_all
   upvar 1 $SYNTH_FLAGS synth
   set FPGA    $synth(FPGA)
   set MODULE  $synth(MODULE)
   set OUTPUT  $synth(OUTPUT)
   if { [info exists synth(SETUP_FLAGS)] } {
      set SETUP_FLAGS $synth(SETUP_FLAGS)
   } else {
      set SETUP_FLAGS ""
   }

   # store start directory, precision change directory to project directory
   # during execution. I have stored, where I begin. 
   set start_dir [pwd]

   # technology library setting
   if { $FPGA == "xc2v1000" } {
      set ipart 2V1000fg456
      set fpga_type "VIRTEX-II"
      set speed 4
   } elseif { $FPGA == "xc2v2000" } {
      set ipart 2V2000fg676
      set fpga_type "VIRTEX-II"
      set speed 4
   } elseif { $FPGA == "xc2v3000" } {
      set ipart 2V3000bf957
      set fpga_type "VIRTEX-II"
      set speed 4
   } elseif { $FPGA == "xc2vp20" } {
      set ipart 2VP20ff896
      set fpga_type "VIRTEX-II Pro"
      set speed 6
   } elseif { $FPGA == "xc2vp30" } {
      set ipart 2VP30ff896
      set fpga_type "VIRTEX-II Pro"
      set speed 7
   } elseif { $FPGA == "xc2vp50" } {
      set ipart 2VP50ff1517
      set fpga_type "VIRTEX-II Pro"
      set speed 5
   } elseif { $FPGA == "xc3s200" } {
      set ipart 3s200pq208
      set fpga_type "SPARTAN3"
      set speed 4
   } elseif { $FPGA == "xc5vlx110t" } {
      set ipart 5VLX110Tff1136
      set fpga_type "VIRTEX-5"
      set speed 1
   } elseif { $FPGA == "xc5vlx110t-2" } {
      set ipart 5VLX110Tff1136
      set fpga_type "VIRTEX-5"
      set speed 2
   } elseif { $FPGA == "xc5vlx155t" } {
      set ipart 5VLX155Tff1136
      set fpga_type "VIRTEX-5"
      set speed 1
   } elseif { $FPGA == "xc5vlx155t-2" } {
      set ipart 5VLX155Tff1136
      set fpga_type "VIRTEX-5"
      set speed 2
   } elseif { $FPGA == "xc5vfx100t" } {
      set ipart 5VFX100Tff1136
      set fpga_type "VIRTEX-5"
      set speed 2
   } elseif { $FPGA == "xc5vlx50t" } {
      set ipart 5VLX50Tff1136
      set fpga_type "VIRTEX-5"
      set speed 1
  } elseif { $FPGA == "Virtex5-sg1" } {
      set ipart None
      set fpga_type "VIRTEX-5"
      set speed 1
  } elseif { $FPGA == "Virtex5-sg2" } {
      set ipart None
      set fpga_type "VIRTEX-5"
      set speed 2

   } else {
      puts "ERROR : Unknown FPGA variable $FPGA."
      exit 1
   }

   # If exists old project, remove it 
   if [file exists "$MODULE.prec/$MODULE.psp"] {
      delete_project -file "$MODULE.prec/$MODULE.psp" 
   }

   # Create and open a new project with name specified by variable MODULE and
   # directory $MODULE.prec
   new_project -name $MODULE -folder "./$MODULE.prec" -force
   
   # Configure the logfile name and location (move log file to log file named
   # $MODULE.log)
   logfile -move -name $MODULE.log
   
   # Create and activate a new implementation in the current project with
   # name $MODULE_impl. Discard changes in current implementation.
   # -force argument shall be added if it is used in new project command
   new_impl -name [format "%s_impl" $MODULE] -discard
   
   # set part and manufacturer
   setup_design -manufacturer Xilinx -family "$fpga_type" -part "$ipart" \
      -speed "$speed"

   # disable tri-state conversion
   setup_design -transform_tristates  none

   # apply user settings (if any)
   if { $SETUP_FLAGS != "" } {
      foreach i $SETUP_FLAGS {
         setup_design $i
      }
   }

   # specify begin of output file names
   setup_design -basename $OUTPUT
   set_input_dir $start_dir
   cd $start_dir
}

# ---------------------------------------------------------------------
# Procedure AddInputFiles - recursively goes through the components hierarchy
# and adds all design files using Precision command "add_input_file". Procedure
# parameters define the design hierarchy</p>
# 
proc AddInputFiles { SYNTH_FLAGS HIERARCHY } {
   upvar 1 $HIERARCHY hier
   upvar 1 $SYNTH_FLAGS synth_array
   set FILES [list ]
   set SV_LIBS [list ]

   # Compile PACKAGES - if they was defined
   if { [info exists hier(PACKAGES)] } {
      PrintLabel "Packages Compilation"
      ApplyToMods $hier(PACKAGES) EvalFile FILES
   }
   
   # Compile components
   if { [info exists hier(COMPONENTS)] } {
      ApplyToComponents $hier(COMPONENTS) EvalFile FILES SV_LIBS
   }
   
   # Compile MODs - if they was defined
   if { [info exists hier(MOD)] } {
      PrintLabel "MODs Compilation"
      ApplyToMods $hier(MOD) EvalFile FILES
   }
   
   # Compile Top Level
   if { [info exists hier(TOP_LEVEL)] } {
      PrintLabel "Top Level Compilation"
      ApplyToMods $hier(TOP_LEVEL) EvalFile FILES
   }

   if { [info exists synth_array(MODULE)] } {
      setup_design -design $synth_array(MODULE)
   }
}

# ---------------------------------------------------------------------
# Procedure CompileDesign - compiles design using Precision "compile" commnad.
# 
proc CompileDesign { } {
   PrintLabel "Compile"
   compile 
}

# ---------------------------------------------------------------------
# Procedure AttribConstrDesign - recursively goes throught the design hierarchy
# and applies the function SetAttribConstr to all instances.  SetAttribConstr
# is localy defined in component's Precision.tcl file.
# 
proc AttribConstrDesign { SYNTH_FLAGS HIERARCHY } { 
   upvar 1 $HIERARCHY hier_array
   upvar 1 $SYNTH_FLAGS synth_array
   PrintLabel "Attributes and Constrains Setting"

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

   # Attributes and constrains setting for all instances
   if { [info exists hier_array(COMPONENTS)] } {
      ApplyToInstances $hier_array(COMPONENTS) "EvalInstance" PARAMS
   }

   # Attributes and constrains setting for top_level
   if { [info procs "SetTopAttribConstr"] == "SetTopAttribConstr" } {
      SetTopAttribConstr 
   }
}

# ---------------------------------------------------------------------
# Procedure SynthesizeDesign - synthesises design using Precision "synthesize"
# command.
# 
proc SynthesizeDesign { } {
   PrintLabel "Synthesize"
   synthesize
   PrintLabel "Report Constraints"
   report_constraints -hierarchy
   PrintLabel "Report Critical Path"
   report_timing
   PrintLabel "Report Clock Frequency"
   report_timing -clock_frequency
   PrintLabel "Report Area"
   report_area
}

# ---------------------------------------------------------------------
# Procedure SaveDesign - saves current project implementation. It copies the
# output edif file to root project directory, where the Makefile expects this
# output edif file. OUTPUT parameter specifies the name of output edif file.
# Finally it closes the project.
# 
proc SaveDesign { SYNTH_FLAGS } {

   PrintLabel "Save & Close"
   upvar 1 $SYNTH_FLAGS synth
   set OUTPUT  $synth(OUTPUT)

   save_impl
   # Set full path to generated edif file
   set edif_file [format "%s%s.edf" [get_results_dir] $OUTPUT]

   # If edif file was correctly generated, copy it in base directory, where
   # Makefile reads it.
   if [file exists $edif_file] {
      file copy -force $edif_file [pwd]
   } else {
      puts "Error: $OUTPUT.edf don't found"
   }

   # Close project
   close_project
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
   AddInputFiles synth_array hier_array

   # design compilation
   CompileDesign

   # attributes and constrains setting
   AttribConstrDesign synth_array hier_array

   # design synthesis
   SynthesizeDesign

   # design saving
   SaveDesign synth_array
}

