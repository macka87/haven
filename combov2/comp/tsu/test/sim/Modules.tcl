# Modules.tcl: Modules.tcl script to compille all design
# Copyright (C) 2003 CESNET
# Author: Tomas Martinek <martinek@liberouter.org>
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
global VHDL_BASE

# Base directories
set C6X_BASE        "../combo6x"
set SFPRO_BASE      "../sfpro"
set PTM_BASE        "../../../../ptm/projects/time_stamp"

# List of components
set COMPONENTS [list [list "COMBO6X"    $C6X_BASE   "FULL"]  \
                     [list "SFPRO"      $SFPRO_BASE "FULL"]  \
                     [list "PTM"        $PTM_BASE   "FULL"]  \
               ]

