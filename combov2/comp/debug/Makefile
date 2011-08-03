# Makefile: Makefile to generate debug cores
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
# $Id: Makefile 8625 2009-06-03 07:49:14Z xvozen00 $
#

TARGET0=icon3
TARGET1=ila144
TARGET2=ila72
TARGET2=ila73

COREGEN=coregen

all: $(TARGET0).ngc $(TARGET1).ngc $(TARGET2).ngc

$(TARGET0).ngc: $(TARGET0)/$(TARGET0).xco
	cd $(TARGET0); make

$(TARGET1).ngc: $(TARGET1)/$(TARGET1).xco
	cd $(TARGET1); make

$(TARGET2).ngc: $(TARGET2)/$(TARGET2).xco
	cd $(TARGET2); make

$(TARGET3).ngc: $(TARGET3)/$(TARGET3).xco
	cd $(TARGET3); make

clean:
	cd $(TARGET0); make clean && cd ..; \
  cd $(TARGET1); make clean && cd ..; \
  cd $(TARGET2); make clean && cd ..; \
  cd $(TARGET3); make clean
