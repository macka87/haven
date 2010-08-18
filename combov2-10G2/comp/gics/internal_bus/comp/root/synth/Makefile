# Makefile: Makefile to compile PCIE bridge module
# Copyright (C) 2010 CESNET
# Author: Pavol Korcek <korcek@liberouter.org>
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
# $Id: Makefile 13105 2010-03-06 10:38:14Z korcek $
#


# makefile to synthesize component

TRASH=xst XST.prj XST.srp XST.xcf XST.xst *.lso *.ngc *.prec *.edf *.ngr *.xrpt *.ise *_xdb *.prj

all : xst

MODULE=pcie2ib_bridge
        
xst : XST.tcl $(MODULE).ngc

$(MODULE).ngc:
	tclsh XST.tcl
	rm -f -fr xst/
	mkdir xst
	mkdir xst/projnav.tmp
	xst -ifn XST.xst
 
precision : Precision.tcl $(MODULE).edf

$(MODULE).edf:
	precision -shell -file Precision.tcl    

clean :
	rm -f -fr $(TRASH) 
