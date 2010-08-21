# Leonardo.tcl: Local include Leonardo tcl script
# Copyright (C) 2004 CESNET
# Author: Pecenka  Tomas <pecenka  AT liberouter.org>
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

# List of packages
set PACKAGES      "$ENTITY_BASE/../pkg/rio_codes.vhd \
                   $ENTITY_BASE/../../../projects/liberouter/pkg/commands.vhd \
                   $ENTITY_BASE/../../common/pkg/math_pack.vhd" 		
 
# Source files for implemented component
   set MOD "$MOD $ENTITY_BASE/comp/rio4.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/rio_ctrl.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/cmd_encoder.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/cmd_decoder.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/align_comma_32.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/transmitter.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/recv_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/receiver.vhd"
   set MOD "$MOD $ENTITY_BASE/rio2cmd_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/rio2cmd.vhd"
