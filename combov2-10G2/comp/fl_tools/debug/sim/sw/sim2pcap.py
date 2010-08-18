#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# sim2pcap.py: Convert FL_SIM(FL_BFM) file to PCAP file
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
# $Id: sim2pcap.py 13103 2010-03-05 19:59:45Z xkosar02 $
#

import sys
import re
import struct

if len(sys.argv) != 3:
  print("Convert FL_SIM(FL_BFM) file to PCAP file.")
  print("Usage:")
  print("sim2pcap.py file.sim file.pcap")
  print("NOTE: FL_SIM files with only 1 part are supported. Use cut_packet.py to extract packets from multipart FL_SIM file.")
  exit()

fsim = open(sys.argv[1], "rb")
fpcap = open(sys.argv[2], "wb")
blob = fsim.read()
fpcap.write(struct.pack("IHHIIII", 0xa1b2c3d4L, 2, 4, 0, 0, 1600, 1))
parts = re.split("#\n",blob)
for i in range(0, len(parts)):
  if len(parts[i]) > 0:
    s = str()
    words = re.split("\n", parts[i])
    for j in range(0, len(words)):
      if (len(words[j])>0):
	if (len(words[j]) == 2):
	  s += words[j][0] + words[j][1]
	if (len(words[j]) == 4):
	  s += words[j][2] + words[j][3] + words[j][0] + words[j][1]
	if (len(words[j]) == 6):
	  s += words[j][4] + words[j][5] + words[j][2] + words[j][3] + words[j][0] + words[j][1]
	if (len(words[j]) == 8):
	  s += words[j][6] + words[j][7] + words[j][4] + words[j][5] + words[j][2] + words[j][3] + words[j][0] + words[j][1]
    d = str()
    j = 0
    while j < len(s):
      b = s[j] + s[j+1]
      j = j + 2
      d += chr(int(b,16))
    length = len(d)
    seconds = 0
    useconds = 0
    captureLength = length
    wireLength = length
    fpcap.write(struct.pack("IIII", seconds, useconds, captureLength, wireLength))
    fpcap.write(d)
fsim.close()
fpcap.close()
    