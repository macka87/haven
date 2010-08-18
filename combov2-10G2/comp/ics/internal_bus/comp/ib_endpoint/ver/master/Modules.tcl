# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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

# Source files for all components


if { $ARCHGRP == "FULL" } {
  set MOD "$MOD $ENTITY_BASE/tbench/ib_ifc.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/endpoint_ifc.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/ib_endpoint_master_ifc.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/ib_endpoint_master.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/bm_transaction_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/bm_generator_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/bm_driver_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/ib_transaction_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/ib_driver_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/ib_generator_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/ib_monitor_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/ib_memory_trans.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/ib_memory.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/scoreboard_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
}

