# Precison.tcl: ComboV2 Precision synthesis tcl script
# Copyright (C) 2008 CESNET
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
# $Id$
#
# glogal procedures
proc NetCopeAttribConstr { } {
   #set_false_path -design gatelevel -to *regasync*
   
   #create_clock -design rtl -name IB_CLK -period 8 -waveform {0 4} -domain main PCI_SYSTEM.PCIE_BLK_PLUS_I.TRN_CLK
   #create_clock -design rtl -name IB_CLK -period 8 -waveform {0 4} -domain main PCI_SYSTEM.IB_CLK

   set_attribute -design rtl -name NOBUFF -value TRUE -net ICS_CLK
   set_attribute -design rtl -name BUFFER_SIG -value {""} -net ICS_CLK
   set_attribute -design rtl -name NOBUFF -value TRUE -net PCI_SYSTEM.BRIDGE_CLK
   set_attribute -design rtl -name BUFFER_SIG -value {""} -net PCI_SYSTEM.BRIDGE_CLK
}
