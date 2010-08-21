#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# cut_packet.py: Cut(extract) one part from FL_SIM(FL_BFM) file
# Copyright (C) 2010 CESNET
# Author: Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
# $Id: cut_packet.py 13103 2010-03-05 19:59:45Z xkosar02 $
#

import sys
import re

if len(sys.argv) != 4:
  print("Cut 1 part from multipart FL_SIM(FL_BFM) file.")
  print("Usage:")
  print("cut_packet in.sim out.sim PART")
  print("PART - part with packet, start with 0")
  exit()

fin = open(sys.argv[1], "rb")
fout = open(sys.argv[2], "wb")

blob = fin.read()

parts = re.split("#\n",blob)

t = str()

for i in range(0, len(parts)):
  if len(parts[i]) > 0:
    in_parts = re.split("\$\n",parts[i])
    
    for j in range(0, len(in_parts)):
      if (len(in_parts[j]) > 0):
	if j == int(sys.argv[3]):
	  t = t + in_parts[j] + "#\n"
          
fout.write(t)

fout.close()
fin.close()