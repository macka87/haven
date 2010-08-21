#
# Makefile.fpga.inc: Include Makefile for compilation FPGA toolchain
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

ZIP ?= zip
RM ?= rm -f
TCLSH ?= tclsh
PRINTF ?= printf
GREP ?= egrep
TEST ?= test
LN ?= ln
TOUCH ?= touch

EXEMPLARBIN ?= /usr/local/fpga/Exemplar/bin
XILINXBIN ?= /usr/local/xilinx/bin/sol
MODELTECHBIN ?= /usr/local/fpga/Modeltech/bin
VERIFBIN ?= $(LIBEROUTER_PATH)/ver/scripts

# Liberouter CVS local root
LIBEROUTER_PATH ?= $(BASE)/../..

FPGAPART ?= 2v3000
FPGAPROCESS ?= 4
FPGAPACKAGE ?= bf957
FPGATECH ?= xcv2
FPGAUCF ?= $(BASE)/chips/fpga.ucf
FULLUCF ?= $(SRC:.vhd=.gen.ucf)

TOP ?= $(BASE)/chips/fpga.vhd

MOD ?= $(shell export SECOND_PASS=1 && tclsh XST.tcl > /dev/null && cat XST.prj | cut -d" " -f3)

CLEANALL_DEPENDS ?=

LIB ?= $(SRC:.vhd=.lib)
SIMSRC ?= $(SRC:.vhd=.sim.vhd)
SIMSDF ?= $(SRC:.vhd=.sim.sdf)
SIMMAPSRC ?= $(SRC:.vhd=.simmap.vhd)
SIMMAPSDF ?= $(SRC:.vhd=.simmap.sdf)

FIRSTTEEFLAG ?= | tee translation.log
TEEFLAG ?= | tee -a translation.log

SYNTH ?= $(EXEMPLARBIN)/spectrum
SYNTHFLAGS ?= -source=$(FPGATECH).syn -target=$(FPGATECH).syn \
    -select_modgen=fastest -effort=quick \
    -report_full -wire_tree=Worst -nocontrol -vhdl_93 -chip \
    -part $(FPGAPART)$(FPGAPACKAGE) -process $(FPGAPROCESS)
SYNTHFILES ?= -vhdl_file="$(TOP) $(MOD)" $< $@

PRE_XST_SYNTH?=sleep 0

NGDBUILD ?= $(XILINXBIN)/ngdbuild
NGDBUILDFLAGS ?=

TOP_BASE ?= ..

MAP ?= $(XILINXBIN)/map
MAPFLAGS ?=

PAR ?= $(XILINXBIN)/par
PARFLAGS ?= -w -ol std

BITGEN ?= $(XILINXBIN)/bitgen
BITGENFLAGS ?= -w -g UnusedPin:PullNone -g DriveDone:Yes

PROMGEN ?= $(XILINXBIN)/promgen
PROMGENFLAGS ?= -w -u 0

TRCE ?= $(XILINXBIN)/trce
TRCEFLAGS ?= -v 3

NETGEN ?= $(XILINXBIN)/netgen
NETGENFLAGS ?= -ofmt vhdl -sim -w

VLIB ?= $(MODELTECHBIN)/vlib
VLIBFLAGS ?=

VCOM ?= $(MODELTECHBIN)/vcom
VCOMFLAGS ?= -93

VSIM ?= $(MODELTECHBIN)/vsim
VSIMFLAGS ?=

VHD2V ?= $(VERIFBIN)/vhd2v

V2SMV ?= $(VERIFBIN)/v2smv.pl
V2SMVFLAGS ?=

VHDOCL ?= vhdocl

ifdef SIMF
SIMFFLAGS ?= -do $(SIMF)
endif

ifdef SIMT
SIMTFLAGS ?= -do $(SIMT)
endif

.SUFFIXES: .ucf .vhd .edf .ngd .pcf .map.ncd .par.ncd .bit .mcs \
    .mcs.zip .twr .map.ngm .sdf .v .smv

.PRECIOUS: *.edf \
    *.ngc *.ngd \
    *.ncd *.pcf \
    *.ngo\
    *.bit *.mcs *.ngm *.v *.smv

.SECONDARY:

.PHONY: vhdocl

$(FULLUCF): $(FPGAUCF) $(ADDUCF)
	cat $(FPGAUCF) $(ADDUCF) > $@

##################
# Common targets #
##################
all:


ifneq ($(DISABLE_SYNTH),1)
%.ngc: $(MOD) XST.tcl
	@echo
	@echo '*****************************************************************************'
	@echo '* SYNTHESIZE (VHDL -> NGC)                                                  *'
	@echo '*****************************************************************************'
	export TOP_LEVEL_ENT=$(@:.ngc=) ; $(TCLSH) XST.tcl
	$(RM) -r xst/
	$(RM) $@
	mkdir xst
	mkdir xst/projnav.tmp
	$(PRE_XST_SYNTH) ; $(SYNTH) -ifn XST.xst $(FIRSTTEEFLAG)
	@ls $@

%.edf: $(MOD) $(SYNTHFILES)
	@echo
	@echo '*****************************************************************************'
	@echo '* SYNTHESIZE (VHDL -> EDIF)                                                 *'
	@echo '*****************************************************************************'
	export TOP_LEVEL_ENT=$(@:.edf=) ; $(SYNTH) $(SYNTHFLAGS) $(SYNTHFILES) $(FIRSTTEEFLAG)
endif

%.v: %.vhd $(TOP) $(MOD)
	@echo
	@echo '*****************************************************************************'
	@echo '* SYNTHESIZE (VHDL -> Verilog)                                              *'
	@echo '*****************************************************************************'
	@$(RM) $(<:.vhd=.err)
	$(SYNTH) $(VERSYNTHFLAGS) -vhdl_file="$(TOP) $(MOD)" $< $@ ; \
	    SAVE=$$? ; \
	    $(TEST) -f $(<:.vhd=.log) && \
	      $(GREP) "(Warning|Error)" $(<:.vhd=.log) \
	      | $(GREP) -v "^(Warning, port .* is connected to a disabled tristate, possibly unconnected port in design|\".*$(TOP)\",line [0-9]+: Warning, inout .* is (never used or assigned a value|used as (input|output) only)|\".*\",line [0-9]+: Warning, signal empty_sig is never used)\.$$" > $(<:.vhd=.err) ; \
	    exit $$SAVE

ifeq ($(SYNTH),xst)
%.ngd: %.ngc $(FULLUCF) $(NGDBUILD_DEPENDS)
	@echo
	@echo '*****************************************************************************'
	@echo '* NGDBUILD (NGC -> NGD)                                                     *'
	@echo '*      NGD ... Native Generic Database                                      *'
	@echo '*****************************************************************************'
	$(RM) $@
	$(NGDBUILD) $(NGDBUILDFLAGS) -uc $(FULLUCF) $< $@ $(TEEFLAG)
else
%.ngd: %.edf $(FULLUCF) $(NGDBUILD_DEPENDS)
	@echo
	@echo '*****************************************************************************'
	@echo '* NGDBUILD (EDIF -> NGD)                                                    *'
	@echo '*      NGD ... Native Generic Database                                      *'
	@echo '*****************************************************************************'
	$(RM) $@
	$(NGDBUILD) $(NGDBUILDFLAGS) -uc $(FULLUCF) $< $@ $(TEEFLAG)
endif

%.map.ncd %.map.ngm %.pcf: %.ngd
	@echo
	@echo '*****************************************************************************'
	@echo '* MAP (NGD -> MAP.NCD, MAP.NGM, PCF)                                        *'
	@echo '*      NCD ... Native Circuit Description                                   *'
	@echo '*      NGM ... Structure, naming, hierarchy                                 *'
	@echo '*      PCF ... Physical Constraints File                                    *'
	@echo '*****************************************************************************'
	$(RM) $@
	$(MAP) $(MAPFLAGS) -o $*.map.ncd $< $*.pcf $(TEEFLAG)

%.par.ncd: %.map.ncd %.pcf
	@echo
	@echo '*****************************************************************************'
	@echo '* PLACE & ROUTE (MAP.NCD, PCF -> PAR.NCD)                                   *'
	@echo '*****************************************************************************'
	$(RM) $@
	$(PAR) $(PARFLAGS) $< $@ $*.pcf $(TEEFLAG)

%.bit: %.par.ncd %.pcf
	@echo
	@echo '*****************************************************************************'
	@echo '* BITGEN (PAR.NCD, PCF -> BIT)                                              *'
	@echo '*****************************************************************************'
	$(RM) $@
	$(BITGEN) $(BITGENFLAGS) $< $@ $*.pcf $(TEEFLAG)

%.mcs: %.bit
	@echo
	@echo '*****************************************************************************'
	@echo '* PROMGEN (BIT -> MCS)                                                      *'
	@echo '*****************************************************************************'
	$(RM) $@
	$(PROMGEN) -o $@ $(PROMGENFLAGS) $< $(TEEFLAG)

%.mcs.zip: %.mcs
	$(ZIP) $@ $<

%.twr: %.par.ncd $(SRC:.vhd=.pcf)
	@echo
	@echo '*****************************************************************************'
	@echo '* TRACE (PAR.NCD, PCF -> TWR)                                               *'
	@echo '*      TWR ... Timing Report And Circuit Evaluate                           *'
	@echo '*****************************************************************************'
	$(TRCE) $(TRCEFLAGS) -o $@ $< $(SRC:.vhd=.pcf)

$(SIMSRC) $(SIMSDF): $(SRC:.vhd=.par.ncd) $(SRC:.vhd=.pcf) $(SRC:.vhd=.map.ngm)
	@echo
	@echo '*****************************************************************************'
	@echo '* NETGEN (PAR.NCD, PCF, MAP.NGM -> SIM.SDF, SIM.VHD)                        *'
	@echo '*      SDF ... Standard Delay Format                                        *'
	@echo '*****************************************************************************'
	$(LN) $(SRC:.vhd=.map.ngm) $(SRC:.vhd=.ngm)
	$(NETGEN) $(NETGENFLAGS) -pcf $(SRC:.vhd=.pcf) \
	    $(SRC:.vhd=.par.ncd) $(SIMSRC)
	$(RM) $(SRC:.vhd=.ngm)

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

# Timing (post-par) simulation, no vsim executed

simpar: simt-d

# Post-map simulation

simmap: $(SIMMAPSRC) $(SIMMAPSDF)

$(SIMMAPSRC) $(SIMMAPSDF): $(SRC:.vhd=.map.ncd) $(SRC:.vhd=.pcf) $(SRC:.vhd=.map.ngm)
	@echo
	@echo '*****************************************************************************'
	@echo '* NETGEN (MAP.NCD, PCF, MAP.NGM -> SIM.SDF, SIM.VHD)                        *'
	@echo '*      SDF ... Standard Delay Format                                        *'
	@echo '*****************************************************************************'
	$(LN) $(SRC:.vhd=.map.ngm) $(SRC:.vhd=.ngm)
	$(NETGEN) $(NETGENFLAGS) -pcf $(SRC:.vhd=.pcf) \
	    $(SRC:.vhd=.map.ncd) $(SIMMAPSRC)
	$(RM) $(SRC:.vhd=.ngm)


# Simulation after synthesis and ngdbuild

simsynt: $(SRC:.vhd=.simsynt.vhd)

%.simsynt.vhd: %.ngd
	@echo '**********************************************************************'
	@echo '* POST SYNTHESIS SIMULATION MODEL (NGD -> SIMSYNTH.VHD)               '
	@echo '**********************************************************************'
	$(NETGEN) -ofmt vhdl -w -sim $< $@

%.smv: %.v
	@echo
	@echo '*****************************************************************************'
	@echo '* TRANSLATION (Verilog -> Cadence SMV)                                      *'
	@echo '*****************************************************************************'
	$(V2SMV) $(V2SMVFLAGS) $<

clean_build:
	-@$(RM) *.xdb *.sum *.log *.err *.edf $(FULLUCF) \
	    *.ngo *.nav *.ngd *.bld *.lst \
	    *.pcf *.map.ngm *.map.ncd *.map.mrp *.map.map \
	    *.par.xpi *.par.pad *.par.ncd *.par.dly *.par.par \
	    *.par_pad.csv *.par_pad.txt \
	    *.drc *.bit *.bgn *.prm \
	    *.wlf exemplar.his transcript \
	    *.nlf *.ncf *.ngm \
	    *.sim.sdf *.sim.vhd *.simsynt.vhd \
	    *.mcs *.mcs.zip *.twr *.cfi \
	    *.v *.smv \
	    *.prj *.prd *.sdc \
       *.par.unroutes *_usage.xml \
       *.gen.ucf STD_OUTPUT \
       *.ngc *.lso *.srp *.xcf XST.xst *.ngr *.ndf \
       *.xrpt *.ise *.psr *.ptwx *summary.xml *.twx
	-@$(RM) -r $(LIB)
	-@$(RM) -r *.prec
	-@$(RM) -r *.synp
	-@$(RM) -r xst
	-@$(RM) -r *_xdb
	-@$(RM) -r _xmsgs
	-@$(RM) -r vhdocl.doc vhdocl.conf

clean: clean_build $(CLEAN_DEPENDS)
	-@$(RM) *.edf *.ngc

warn: warn_synth
	@echo "Constraint compliance:"
	@cat *.par.par | egrep "All constraints were met" || echo "!!! Some constraints were not met !!!"

warn_synth:
	@echo "Extremely suspicious warnings by XST:"
	@#Add suspicious warinngs into the string, separated by |
	@#PCRE are used (see grep --help)
	@cat XST.srp | grep -P "WARNING:Xst:(653|737|1610|2170)|INFO:Xst:(1799|2679)" || echo "None found"

cleanall: $(CLEANALL_DEPENDS) clean
	-@$(RM) *.ncd .psr

simclean:
	-@$(RM) -r sim/work
	-@$(RM) sim/transcript sim/vsim.wlf sim/Makefile

info:
	@for M in * ; do $(GREP) $$M: $$M | sed -e 's/^ *[-#*]* *//' ; done

XST.prj: XST.tcl
	$(TCLSH) XST.tcl

vhdocl: XST.prj
	echo "outputdir=vhdocl.doc" > vhdocl.conf
	cat XST.prj | sed 's/^vhdl\ .*\ /input\ /' >> vhdocl.conf
	$(VHDOCL) -f vhdocl.conf

# Targets to synthesise components
xst_comp :
		tclsh XST.tcl
		rm -f -fr xst/
		mkdir xst
		mkdir xst/projnav.tmp
		xst -ifn XST.xst

precision_comp :
		precision -shell -file Precision.tcl
