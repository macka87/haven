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
# $Id: Makefile 13303 2010-03-19 10:28:40Z pus $
#

TRASH=xst XST.prj XST.srp XST.xcf XST.xst *.lso *.ngc STD_OUTPUT *.ngr *.xrpt
TRASH2=*.prec *.edf 

MODULE1=fl_watch_4
MODULE2=fl_watch_2
MODULE3=fl_watch_2_hdr
MODULE4=fl_watch_4_hdr

.PHONY: precision, xst

all : xst
	
xst : XST.tcl $(MODULE1).ngc $(MODULE2).ngc $(MODULE3).ngc $(MODULE4).ngc

%.ngc:
	export TOP_LEVEL_ENT=$(@:.ngc=) && tclsh XST.tcl
	rm -f -fr xst/
	mkdir xst
	mkdir xst/projnav.tmp
	xst -ifn XST.xst
 
precision : Precision.tcl $(MODULE1).edf $(MODULE2).edf $(MODULE3).edf $(MODULE4).edf

%.edf:
	export TOP_LEVEL_ENT=$(@:.edf=) && precision -shell -file Precision.tcl


clean :
		rm -f -fr $(TRASH) 
		rm -f -fr $(TRASH2)
