# Synplify.inc.tcl: Synplify global include tcl script to compile all design
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
# Synplify.tcl file specified in COMP_PATH
proc EvalInstance { COMP_PATH ENTITY ARCHITECTURE INST_PATH PARAMS} {
   puts "Instance $INST_PATH detected"
   upvar 1 $PARAMS param_array

   if { [file exist "$COMP_PATH/Synplify.tcl" ] } {
      source $COMP_PATH/Synplify.tcl
      if { [info procs "SetAttribConstr"] == "SetAttribConstr" } {
         set CONSTR [SetAttribConstr $ENTITY $ARCHITECTURE $INST_PATH param_array]
         
         if { $CONSTR != "" } {
            puts "Attributes and Constrains applied to $INST_PATH"
            
            # Open temporary file with constraints
            set filedesc [open "Synplify.sdc" "a"]
            puts $filedesc "# Constraints from entity $ENTITY:"
            foreach i $CONSTR {
               puts $filedesc $i
            }
            close $filedesc
         }
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

   project -addfile $FNAME
}

# ---------------------------------------------------------------------
# Procedure SetupDesign - creates a new project with the name defined in MODULE
# parameter. If the project already exists, it removes the project including
# all its implementations. It sets the type of FPGA chip, for the synthesis is
# performed and finaly it sets the name of the output edif file defined in
# OUTPUT parameter.
# 
proc SetupDesign { SYNTH_FLAGS } {
   upvar 1 $SYNTH_FLAGS synth
   set FPGA    $synth(FPGA)
   set MODULE  $synth(MODULE)
   set OUTPUT  $synth(OUTPUT)
   if { [info exists synth(SETUP_FLAGS)] } {
      set SETUP_FLAGS $synth(SETUP_FLAGS)
   } else {
      set SETUP_FLAGS ""
   }

   # store start directory, synplify change directory to project directory
   # during execution. I have stored, where I begin. 
   set start_dir [pwd]

   # technology library setting
   if { $FPGA == "xc2v1000" } {
      set ipart XC2V1000
      set ipackage FG456
      set fpga_type VIRTEX2
      set speed -4
   } elseif { $FPGA == "xc2v2000" } {
      set ipart XC2V2000
      set ipackage FG676
      set fpga_type "VIRTEX2"
      set speed -4
   } elseif { $FPGA == "xc2v3000" } {
      set ipart XC2V3000
      set ipackage BF957
      set fpga_type VIRTEX2
      set speed -4
   } elseif { $FPGA == "xc2vp20" } {
      set ipart XC2VP20
      set ipackage FF896
      set fpga_type VIRTEX2P
      set speed -6
   } elseif { $FPGA == "xc2vp30" } {
      set ipart XC2VP30
      set ipackage FF896
      set fpga_type VIRTEX2P
      set speed -7
   } elseif { $FPGA == "xc2vp50" } {
      set ipart XC2VP50
      set ipackage FF1517
      set fpga_type VIRTEX2P
      set speed -5
   } elseif { $FPGA == "xc3s200" } {
      set ipart XC3S200
      set ipackage PQ208
      set fpga_type SPARTAN3
      set speed -4
   } else {
      puts "ERROR : Unknown FPGA variable."
      exit 1
   }

   # Create and open a new project with name specified by variable MODULE and
   # directory $MODULE
   project -new $MODULE

   project -log_file $MODULE.log
   
   # Create and activate a new implementation in the current project with
	# name $MODULE.synp.
	set impl_name [format "%s.synp" $MODULE]
	impl -add $impl_name

 	# set part and manufacturer
	set_option -technology $fpga_type
	set_option -part $ipart
	set_option -package $ipackage
	set_option -speed_grade $speed  
   
   # disable tri-state conversion
   #setup_design -transform_tristates  none

   # apply user settings (if any)
   if { $SETUP_FLAGS != "" } {
      foreach i $SETUP_FLAGS {
         set_option $i
      }
   }

   # specify begin of output file names
   project -result_file $OUTPUT
   #set_input_dir $start_dir
   #cd $start_dir
}

# ---------------------------------------------------------------------
# Procedure AddInputFiles - recursively goes through the components hierarchy
# and adds all design files using Precision command "add_input_file". Procedure
# parameters define the design hierarchy</p>
# 
proc AddInputFiles { HIERARCHY } {
   upvar 1 $HIERARCHY hier
   set FILES [list ]

   # Compile PACKAGES - if they was defined
   if { [info exists hier(PACKAGES)] } {
      PrintLabel "Packages Compilation"
      ApplyToMods $hier(PACKAGES) EvalFile FILES
   }
   
   # Compile components
   if { [info exists hier(COMPONENTS)] } {
      ApplyToComponents $hier(COMPONENTS) EvalFile FILES
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
}

# ---------------------------------------------------------------------
# Procedure CompileDesign - compiles design using Precision "compile" commnad.
# 
proc CompileDesign { } {
   PrintLabel "Compile"
   project -run compile 
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

   # Create temporary file with constraints
   set filedesc [open "Synplify.sdc" "w"]
   close $filedesc
   
   # Attributes and constrains setting for all instances
   if { [info exists hier_array(COMPONENTS)] } {
      ApplyToInstances $hier_array(COMPONENTS) "EvalInstance" PARAMS
   }

   # Attributes and constraints for toplevel
   if { [info procs "SetTopAttribConstr"] == "SetTopAttribConstr" } {
      set CONSTR [SetTopAttribConstr]
      if { $CONSTR != "" } {
         # Open temporary file with constraints
         set filedesc [open "Synplify.sdc" "a"]
         puts $filedesc "# Toplevel constraints"
         foreach i $CONSTR {
            puts $filedesc $i
         }
         close $filedesc
      }
   }

   # Include the final file with constraints
   add_file -constraint Synplify.sdc
   
}

# ---------------------------------------------------------------------
# Procedure SynthesizeDesign - synthesises design using Precision "synthesize"
# command.
# 
proc SynthesizeDesign { } {
   PrintLabel "Synthesize"
   project -run synthesis
}

# ---------------------------------------------------------------------
# Procedure SaveDesign - saves current project implementation. It copies the
# output edif file to root project directory, where the Makefile expects this
# output edif file. OUTPUT parameter specifies the name of output edif file.
# Finally it closes the project.
# 
proc SaveDesign { SYNTH_FLAGS } {
   upvar 1 $SYNTH_FLAGS synth
   set OUTPUT  $synth(OUTPUT)
   set MODULE  $synth(MODULE)

   project -save
   # Set full path to generated edif file
   set edif_file [format "%s%s.synp/%s.edf" [project -dir] $MODULE $OUTPUT]

   # If edif file was correctly generated, copy it in base directory, where
   # Makefile reads it.
   if [file exists $edif_file] {
      file copy -force $edif_file [pwd]
   } else {
      puts "Error: $edif_file not found"
   }

   # Close project
   project -close
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

   # design compilation
   CompileDesign

   # attributes and constrains setting
   AttribConstrDesign synth_array hier_array

   # design synthesis
   SynthesizeDesign

   # design saving
   SaveDesign synth_array
}

