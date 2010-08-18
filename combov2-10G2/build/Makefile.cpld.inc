#
# Makefile.cpld.inc: Include Makefile for compilation CPLD toolchain
# Copyright (C) 2003 CESNET
# Author: Rudolf Cejka <cejkar@fit.vutbr.cz>
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

# Makefile example:
#
# # Formal verification
# DESIGN = main
# TO_OPTIMIZE = .work.src.main_vhd
# # V2SMVFLAGS = -async
#
# # TOP = cpld.vhd
# SRC = src.vhd
# MOD = mod1.vhd mod2.vhd ...
# SIM = src-tb.vhd
# SIMF = simf.do
# SIMT = simt.do
# BASE = ..
#
# all: $(SRC:.vhd=.jed)
#
# include $(BASE)/../base/Makefile.cpld.inc

# Documentation:
#
# merlot.ics.muni.cz:/usr/local/fpga/Exemplar/doc/leospec_ref.pdf
# merlot.ics.muni.cz:/usr/local/xilinx/doc/usenglish/docs/dev/dev.pdf
# merlot.ics.muni.cz:/usr/local/fpga/Modeltech/docs/pdf/se_cmds.pdf

ZIP ?= zip
RM ?= rm -f
PRINTF ?= printf
GREP ?= egrep
TEST ?= test

EXEMPLARBIN ?= /usr/local/fpga/Exemplar/bin
XILINXBIN ?= /usr/local/xilinx/bin/sol
LOCALBIN ?= /usr/local/bin
MODELTECHBIN ?= /usr/local/fpga/Modeltech/bin
VERIFBIN ?= /usr/local/verif/bin

CPLDPART ?= xcr3256xl
CPLDPROCESS ?= 7
CPLDPACKAGE ?= ft256
CPLDTECH ?= xcr
CPLDUCF ?= $(BASE)/chips/cpld.ucf

TOP ?= $(BASE)/chips/cpld.vhd

LIB ?= $(SRC:.vhd=.lib)
SIMSRC ?= $(SRC:.vhd=.sim.vhd)
SIMSDF ?= $(SRC:.vhd=.sim.sdf)

SYNTH = $(EXEMPLARBIN)/spectrum
SYNTHFLAGS ?= -source=$(CPLDTECH).syn -target=$(CPLDTECH).syn \
    -delay -select_modgen=fastest -noxlx_fast_slew -effort=standard \
    -report_full -encoding=Binary -wire_tree=Worst \
    -nocontrol -vhdl_93 -chip \
    -part $(CPLDPART)$(CPLDPACKAGE) -process $(CPLDPROCESS)

NGDBUILD = $(XILINXBIN)/ngdbuild
NGDBUILDFLAGS ?=

CPLDFIT = $(XILINXBIN)/cpldfit
CPLDFITFLAGS ?= -p $(CPLDPART)-$(CPLDPROCESS)-$(CPLDPACKAGE)

HPREP6 = $(XILINXBIN)/hprep6
HPREP6FLAGS ?=

IMPACT = $(XILINXBIN)/impact
IMPACTFLAGS ?=

SVF2XSVF = $(LOCALBIN)/svf2xsvf
SVF2XSVFFLAGS ?= -nc

TAENGINE = $(XILINXBIN)/taengine
TAENGINEFLAGS ?=

TSIM = $(XILINXBIN)/tsim
TSIMFLAGS ?=

NGD2VHDL = $(XILINXBIN)/ngd2vhdl
NGD2VHDLFLAGS ?= -w

VLIB = $(MODELTECHBIN)/vlib
VLIBFLAGS ?=

VCOM = $(MODELTECHBIN)/vcom
VCOMFLAGS ?= -93

VSIM = $(MODELTECHBIN)/vsim
VSIMFLAGS ?=

VHD2V = $(VERIFBIN)/vhd2v

V2SMV = $(VERIFBIN)/v2smv
V2SMVFLAGS ?=

ifdef SIMF
SIMFFLAGS ?= -do $(SIMF)
endif

ifdef SIMT
SIMTFLAGS ?= -do $(SIMT)
endif

.SUFFIXES: .ucf .vhd .edf .ngd .vm6 .tim .nga .jed .jed.zip .svf .xsvf \
    .pcf .map.ncd .par.ncd .bit .map.ngm .sdf .v .smv

.PRECIOUS: $(SRC:.vhd=.edf) $(SRC:.vhd=.ngd) $(SRC:.vhd=.vm6) \
    $(SRC:.vhd=.jed) $(SRC:.vhd=.svf) \
    $(SRC:.vhd=.v) $(SRC:.vhd=.smv)

all:

# Grep errors and warning from *.log into *.err.

%.edf: %.vhd $(TOP) $(MOD)
	@$(RM) $(<:.vhd=.err)
	$(SYNTH) $(SYNTHFLAGS) -vhdl_file="$(TOP) $(MOD)" $< $@ ; \
	    SAVE=$$? ; \
	    $(TEST) -f $(<:.vhd=.log) && \
	      $(GREP) "(Warning|Error)" $(<:.vhd=.log) >> $(<:.vhd=.err) ; \
	    exit $$SAVE

%.ngd: %.edf $(CPLDUCF)
	$(NGDBUILD) $(NGDBUILDFLAGS) -uc $(CPLDUCF) $< $@

%.vm6 %.gyd: %.ngd
	$(CPLDFIT) $(CPLDFITFLAGS) $<

%.jed: %.vm6
	$(HPREP6) -i $* $(HPREP6FLAGS)

%.jed.zip: %.jed
	$(ZIP) $@ $<

%.svf: %.jed
	$(PRINTF) "%s\n%s\n%s\n%s\n%s\n" \
	    "setmode -bsfile" \
	    "setcable -port svf -file $@" \
	    "addDevice -position 1 -file $<" \
	    "program -e -v -p 1" \
	    "quit" \
	    | $(IMPACT) $(IMPACTFLAGS) -batch

%.xsvf: %.svf
	$(SVF2XSVF) $(SVF2XSVFFLAGS) -i $< -o $@

%.tim: %.vm6 $(SRC:.vhd=.gyd)
	$(TAENGINE) $(TAENGINEFLAGS) -l $@ -f $<

%.nga: %.vm6
	$(TSIM) $(TSIMFLAGS) $< $@

$(SIMSRC) $(SIMSDF): $(SRC:.vhd=.nga)
	$(NGD2VHDL) $(NGD2VHDLFLAGS) $(SRC:.vhd=.nga) $(SIMSRC)

# Functional simulation, dependency list

simf-d: $(TOP) $(SRC) $(MOD) $(SIM)

# Functional simulation, vsim execution

simf: simf-d
	TOP="$(TOP)" SRC="$(SRC)" MOD="$(MOD)" SIM="$(SIM)" LIB="$(LIB)" \
	    VCOMFLAGS="$(VCOMFLAGS)" VSIMFLAGS="$(VSIMFLAGS)" \
	    $(VSIM) $(VSIMFLAGS) $(SIMFFLAGS)

# Timing simulation, dependency list

simt-d: $(SIMSRC) $(SIMSDF)

# Timing simulation, vsim execution

simt: simt-d
	SIMSRC="$(SIMSRC)" SIMSDF="$(SIMSDF)" LIB="$(LIB)" \
	    VCOMFLAGS="$(VCOMFLAGS)" VSIMFLAGS="$(VSIMFLAGS)" \
	    $(VSIM) $(VSIMFLAGS) $(SIMTFLAGS)

%.v: %.vhd $(MOD)
	$(VHD2V) $(DESIGN) $(TO_OPTIMIZE) $(MOD) $(SRC)

%.smv: %.v
	$(V2SMV) $(V2SMVFLAGS) $<

clean:
	-@$(RM) *.xdb *.sum *.log *.err *.edf *.ncf \
	    *.ngo *.nav *.ngd *.bld *.lst \
	    *.rpt *.xml *.vm6 *.pnx *.mfd *.gyd *.cxt *.pad *_pad.csv \
	    *.tim *.mod *.data \
	    *.wlf transcript \
	    *.err *.nga \
	    *.sim.sdf *.sim.vhd \
	    *.jed *.jed.zip \
	    *.svf *.xsvf _impact.cmd \
	    *.v *.smv

	-@$(RM) -r $(LIB)

info:
	@for M in * ; do $(GREP) $$M: $$M | sed -e 's/^ *[-#*]* *//' ; done

