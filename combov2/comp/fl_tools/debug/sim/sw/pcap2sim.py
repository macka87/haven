#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# pcap2sim.py: Convert PCAP file to FL_SIM(FL_BFM) file
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
# $Id: pcap2sim.py 13103 2010-03-05 19:59:45Z xkosar02 $
#

import sys
import struct

if len(sys.argv) != 3:
  print("Convert PCAP file to FL_SIM(FL_BFM) file.")
  print("Usage:")
  print("pcap2sim.py file.pcap file.sim")
  print("NOTE: FL_SIM file is generated with 1 part.")
  exit()

#pcap = pcapy.open_offline(sys.argv[1])
fpcap = open(sys.argv[1],"rb")
fsim = open(sys.argv[2], "wb")
code = fpcap.read(4)

if code == "\xa1\xb2\xc3\xd4":
    endianity = ">"
elif code == "\xd4\xc3\xb2\xa1":
    endianity = "<"

stopFlag = 0

pcapHeader = fpcap.read(20)

packetHeader = fpcap.read(16)
if len(packetHeader) < 16:
  stopFlag = 1
else:
  seconds,useconds,captureLength,wireLength = struct.unpack(endianity + "IIII", packetHeader)
  packet = fpcap.read(captureLength)

#pkt = pcap.next()
g = str()
while (stopFlag == 0):
  s = str()
  for i in range(0,len(packet)):
    b = hex(ord(packet[i]))
    if len(b) == 3:
      s = s + "0" + b[2]
    else:
      s = s + b[2] + b[3]
    #print(b)

  t = str()
  i = 0
  while i < len(s):
    l = str()
    if len(s) - i < 8:
      p = i
      if len(s) - p == 2:
        l = s[i] + s[i+1]
        i = i + 2
      if len(s) - p == 4:
        l = s[i+2] + s[i+3] + s[i] + s[i+1]
        i = i + 4
      if len(s) - p == 6:
        l = s[i+4] + s[i+5] + s[i+2] + s[i+3] + s[i] + s[i+1]
        i = i + 6
    else:
      l = s[i+6] + s[i+7] + s[i+4] + s[i+5] + s[i+2] + s[i+3] + s[i] + s[i+1] 
      i = i + 8
    t = t + l + "\n"
  t = t + "#"
  #print(t)
  g = g + t + "\n"

  packetHeader = fpcap.read(16)
  if len(packetHeader) < 16:
    stopFlag = 1
  else:
    seconds,useconds,captureLength,wireLength = struct.unpack(endianity + "IIII", packetHeader)
    packet = fpcap.read(captureLength)

fpcap.close()
fsim.write(g)
fsim.close()