# SVDoxy.inc.tcl: Tcl script to store SystemVerilog files to list
# Copyright (C) 2009 CESNET
# Author: Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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

# Identify SystemVerilog files and store them to list
proc StoreSVFiles {MODULE} {
  
  if { [llength $MODULE] == 2 } {
      set FNAME [lindex $MODULE 1]
  } else {
      set FNAME $MODULE
  }

  # store SV files to list
  if { [regexp {^.*\.sv$} $FNAME] } {
      set filedesc [open "SVfiles.txt" "a"]
      puts $filedesc $FNAME
      close $filedesc
  }
}

# ---------------------------------------------------------------------
#                         Compilation
# ---------------------------------------------------------------------

set FILES [list ]
set SV_LIBS [list ]

# Open file for writing (delete if exists)
   set filedesc [open "SVfiles.txt" "w"]
   close $filedesc

# Saves MOD variable - Components have to be compiled first
if { [info exist MOD] } {
   set MOD_SAVE $MOD
}

# Compile PACKAGES - if they was defined
if { [info exist PACKAGES] } {
   PrintLabel "Packages Compilation - sv"
   ApplyToMods $PACKAGES "StoreSVFiles" FILES
}

# Compile components
if { [info exist COMPONENTS] } {
   PrintLabel "Comp Compilation - sv"
   ApplyToComponents $COMPONENTS "StoreSVFiles" FILES SV_LIBS
}

# Compile MODs - if they were defined
if { [info exist MOD_SAVE] } {
   PrintLabel "MODs Compilation - sv"
   puts $MOD_SAVE
   ApplyToMods $MOD_SAVE "StoreSVFiles" FILES
}

# Read top level vhdl files
if { [info exist TOP_LEVEL] } {
   PrintLabel "Top Level - sv"
   ApplyToMods $TOP_LEVEL "StoreSVFiles" FILES
}

# Read testbench files
if { [info exist TB_FILE] } {
   PrintLabel "Testbench - sv"
   ApplyToMods $TB_FILE "StoreSVFiles" FILES
}