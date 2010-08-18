# Makefile: Makefile just for simulation
# Copyright (C) 2004 Masaryk University
# Author: Jiri Novotny <novotny@ics.muni.cz>
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
# $Id: Makefile 14 2007-07-31 06:44:05Z kosek $
#

# Top level entity
#

SRC = tsu2pci.vhd
TOP =
FPGAUCF = fpga.ucf
NGDBUILDFLAGS = -aul
MOD =
BASE = ../../..

SYNTHFLAGS = -file=Leonardo.tcl

# Simulation specification
SIMF = sim/simf.do
SIMT =

all: $(SRC:.vhd=.mcs)
	@echo "$(SRC:.vhd=.mcs) has been successfully built"

# Translation specification
include $(BASE)/base/Makefile.fpga.inc

