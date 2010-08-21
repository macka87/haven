# Makefile: Makefile to compile CRC module as a module
# Copyright (C) 2007 CESNET
# Author: Lukas Solanka <solanka@liberouter.org>
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
# $Id: Makefile 6150 2008-10-29 10:31:47Z solanka $
#

# Synthesis tool: precision or XST
SYNTHESIS ?= precision
#SYNTHESIS ?= xst

# Base directory
FIRMWARE_BASE = ../../../..

# Architecture + entity
SRC = crc32_64b.vhd
TOP = crc32_64b.vhd

ifeq ($(SYNTHESIS),xst)
	# Precision Synthesizer
	SYNTH = xst
	SYNTHFLAGS = -ifn
	SYNTHFILES = XST.xst
else
	# XST Synthesizer
	SYNTH = precision2007a
	SYNTHFLAGS = -shell -file
	SYNTHFILES = Precision.tcl
endif


all: $(SRC:.vhd=.edf)

# Translation specification
include $(FIRMWARE_BASE)/build/Makefile.fpga.inc

