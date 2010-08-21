# Makefile: Makefile to generate CHIPSCOPE core (ila72)
# Copyright (C) 2009 CESNET
# Author: Jan Vozenilek <xvozen00@stud.fit.vutbr.cz>
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
# $Id: Makefile 13673 2010-05-04 15:34:49Z pus $
#

PREFIX=ila72

SOURCE_FILE=$(PREFIX).xco
RESULT_FILE=../$(PREFIX).ngc

COREGEN=coregen

all: $(RESULT_FILE)

$(RESULT_FILE): $(SOURCE_FILE)
	rm -f coregen.cgc
	cp $(SOURCE_FILE) $(SOURCE_FILE).bak
	$(COREGEN) -b $(SOURCE_FILE)
	mv $(SOURCE_FILE).bak $(SOURCE_FILE)
	mv $(PREFIX).ngc ../

clean:
	rm -f $(RESULT_FILE)
	rm -rf home tmp $(PREFIX) xlnx_auto_0_xdb
	rm -f coregen.log xlnx_auto_0.ise
	rm -f $(PREFIX).cdc $(PREFIX).ncf $(PREFIX).vhd $(PREFIX).vho $(PREFIX)_flist.txt $(PREFIX)_readme.txt $(PREFIX)_xmdf.tcl
