# Makefile: Makefile to synthesize single component
# Copyright (C) 2010 CESNET
# Author: Viktor Pus <pus@liberouter.org>
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
# $Id: Makefile 12951 2010-02-25 09:27:57Z pus $
#
.NOTPARALLEL:

MODULE1=fl_transformer_128to64
MODULE2=fl_transformer_64to128

.PHONY: all doc xst precision clean

MAIN=Makefile.main

# Default: XST
xst: $(MODULE1).ngc $(MODULE2).ngc

precision: $(MODULE1).edf $(MODULE2).edf

%.ngc: FORCE
	$(MAKE) -f $(MAIN) $@ SYNTH=xst

%.edf: FORCE
	$(MAKE) -f $(MAIN) $@ SYNTH=precision SYNTHFLAGS="-shell -file" SYNTHFILES=Precision.tcl

FORCE:

clean:
	$(MAKE) -f $(MAIN) $@

doc:
	$(MAKE) -f $(MAIN) vhdocl
