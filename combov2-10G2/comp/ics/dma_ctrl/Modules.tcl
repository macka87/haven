# Modules.tcl: Modules.tcl script
# Copyright (C) 2007 CESNET
# Author: Petr Kastovsky <kastovsky@liberouter.org>
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
#
# README: Set DMA_IFC_COUNT to 0 to disable handelc compilation
#
#

proc __compile_dma_ctrls { ENTITY_BASE ENTITY_MODFILE } {
    # Recompile controllers with the DMA width globally defined
    global DMA_IFC_COUNT
    if { [info exists DMA_IFC_COUNT] } {
        if { $DMA_IFC_COUNT != 0 } {
            
            # export environment variable for Makefile
            # This variable will set proper -D parameter for handelc compiler
            global env
            set env(DMA_DATA_WIDTH) [expr 64/(2*$DMA_IFC_COUNT)]

            # Save PWD and after make, restore it back
            set cwd [eval pwd]
            cd $ENTITY_BASE

            puts -nonewline "$ENTITY_MODFILE: compiling handelc sources for rx/tx_dma_ctrl..."
            flush stdout
            exec make
            puts "done."

            # Restore CWD for proper script continuation
            cd $cwd
        } else {
            puts "**** $ENTITY_MODFILE: DMA_IFC_COUNT == 0. Not running handelC compiler."
        }
    } else {
        error "$ENTITY_MODFILE: DMA_IFC_COUNT variable not set. See this file on how to set this variable." 
    }
}

# optimalized and nonoptimalized DMAs (with/without desc_manager)
if {$ARCHGRP == "FULL"} {

    set COMP_BASE        "$ENTITY_BASE/../.."
    set ARCH_BASE        "$ENTITY_BASE/arch"

    set MOD  "$MOD [list [list "dk" $COMP_BASE/base/pkg/dk.vhd]]"
#    set MOD  "$MOD [list [list "agility" $COMP_BASE/base/pkg/agility.vhd]]"
    set MOD  "$MOD $COMP_BASE/ics/internal_bus/pkg/ib_pkg.vhd"

    set MOD  "$MOD $ENTITY_BASE/comp/bm2mem_ifc.vhd"
    set MOD  "$MOD $ENTITY_BASE/comp/dma2bm.vhd"

#    set MOD  "$MOD $ENTITY_BASE/rx_dma_ctrl_opt_arch.vhd"
    set MOD  "$MOD $ARCH_BASE/rx_dma_ctrl_opt_arch_1b.vhd"
    set MOD  "$MOD $ARCH_BASE/rx_dma_ctrl_opt_arch_2b.vhd"
    set MOD  "$MOD $ARCH_BASE/rx_dma_ctrl_opt_arch_4b.vhd"
    set MOD  "$MOD $ARCH_BASE/rx_dma_ctrl_opt_arch_8b.vhd"
    set MOD  "$MOD $ARCH_BASE/rx_dma_ctrl_opt_arch_16b.vhd"
    set MOD  "$MOD $ARCH_BASE/rx_dma_ctrl_opt_arch_32b.vhd"
    set MOD  "$MOD $ARCH_BASE/rx_dma_ctrl_opt_arch_64b.vhd"
    set MOD  "$MOD $ENTITY_BASE/rx_dma_ctrl_opt.vhd"

#    set MOD  "$MOD $ENTITY_BASE/tx_dma_ctrl_opt_arch.vhd"
    set MOD  "$MOD $ARCH_BASE/tx_dma_ctrl_opt_arch_1b.vhd"
    set MOD  "$MOD $ARCH_BASE/tx_dma_ctrl_opt_arch_2b.vhd"
    set MOD  "$MOD $ARCH_BASE/tx_dma_ctrl_opt_arch_4b.vhd"
    set MOD  "$MOD $ARCH_BASE/tx_dma_ctrl_opt_arch_8b.vhd"
    set MOD  "$MOD $ARCH_BASE/tx_dma_ctrl_opt_arch_16b.vhd"
    set MOD  "$MOD $ARCH_BASE/tx_dma_ctrl_opt_arch_32b.vhd"
    set MOD  "$MOD $ARCH_BASE/tx_dma_ctrl_opt_arch_64b.vhd"
    set MOD  "$MOD $ENTITY_BASE/tx_dma_ctrl_opt.vhd"
    
    set MOD  "$MOD $ENTITY_BASE/comp/dma_status_reg.vhd"
    
    set MOD  "$MOD $ENTITY_BASE/comp/dma2data.vhd"
    set MOD  "$MOD $ENTITY_BASE/comp/data2bm.vhd" 
    set MOD  "$MOD $ENTITY_BASE/top/dma_ctrl_array_opt.vhd"
    set MOD  "$MOD $ENTITY_BASE/top/dma_ctrl_array_rx_opt.vhd"

    # components
    set COMPONENTS [list \
       [ list "PKG_MATH"       $COMP_BASE/base/pkg                                "MATH"] \
       [ list "DESC_MANAGER"   $COMP_BASE/ics/dma_ctrl/comp/desc_manager          "FULL"] \
       [ list "MI_SPLITTER"    $COMP_BASE/gics/mi_bus/mi_splitter                 "FULL"] \
    ]

    # Recompile DMA modules
# commented out because DMA controllers' VHDL source files are commited to SVN
#    __compile_dma_ctrls $ENTITY_BASE $ENTITY_MODFILE

} else {
    error "$ENTITY_MODFILE: Unsupported ARCHGRP: $ARCHGRP" "" "1"
}
