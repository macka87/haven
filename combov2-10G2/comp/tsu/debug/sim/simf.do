# Behavioral simulation
# Author: Jiri Novotny <novotny@ics.muni.cz>
# $Id: simf.do 14 2007-07-31 06:44:05Z kosek $

proc PCI_write { PCI_ADR PCI_DAT } {
global CLK_PCI0
force LHOLD 1
run $CLK_PCI0
force ADS 0
force LAD $PCI_ADR
force LWR 1
run $CLK_PCI0
force ADS 1
force LAD  $PCI_DAT
force BLAST 0
run $CLK_PCI0
force LWR 1
force BLAST 1
noforce LAD
run $CLK_PCI0
force LHOLD 0
run $CLK_PCI0
}

proc PCI_read { PCI_ADR }  {
global CLK_PCI0
force LHOLD 1
run $CLK_PCI0
force ADS 0
force LAD $PCI_ADR
force LWR 0
run $CLK_PCI0
noforce LAD
force ADS 1
force BLAST 0
run $CLK_PCI0
run $CLK_PCI0
run $CLK_PCI0
run $CLK_PCI0
run $CLK_PCI0
noforce LAD
force LWR 1
force BLAST 1
run $CLK_PCI0
force LHOLD 0

run $CLK_PCI0
}

# PCI waves

proc add_wave_PCI {} {
# PCI side
add wave LCLKF
add wave LRESET
add wave LAD
add wave ADS
add wave BLAST
add wave LHOLD
add wave LHOLDA
add wave LWR
add wave READY
add wave USERO
#add_wave_lbus
add_wave_lbconn
}

# Local bus waves
proc add_wave_lbus {} {
add wave lbclk
add wave lbframe
add wave lbholda
add wave lbad
add wave lbas
add wave lbrw
add wave lbrdy
add wave lblast
}

# Local bus connect waves
proc add_wave_lbconn {} {
add wave data_from_lb
add wave data_to_lb
add wave pci_adr
add wave pci_en
add wave pci_rw
add wave lb_connect0/sel
add wave lb_connect0/drdy
add wave lb_connect0/ardy
}

# TSU waves
proc add_wave_TSU {} {
add wave pci_write
add wave ts_en_add
add wave ts_request
add wave ts_short_add
add wave ts_short
add wave tsu_add_test/reset
add wave tsu_add_test/clk_add
add wave tsu_add_test/refclk
add wave tsu_add_test/ts_request_syn

}

# TSU core waves
proc add_wave_TSU_core {} {
add wave tsu_add_test/present_state
add wave tsu_add_test/reg_time_s
add wave tsu_add_test/ts_i
}


# Compilation
vlib work
vcom -93 ../../../combo6/chips/fpga.vhd \
	 ../../../units/common/asrq2sync/asrq2sync.vhd\
         ../../../units/tsu/tsu_add.vhd \
	 ../../../units/lb/local_bus.vhd \
	 ../../../units/lb/lbconn_mem.vhd \
	 tsu2pci.vhd


# Simulator start
vsim -t ps fpga

set DefaultRadix hex
set UserTimeUnit ns

view wave
restart -force
delete wave *

view wave

# Waves
add_wave_PCI
add_wave_TSU
add_wave_TSU_core

# Clock definition
set CLK_RUN 10
# REFLCK
set CLK0 8
set CLK1 4

set CLK_PCI0 20
set CLK_PCI1 10


# Signal initialization
noforce refclk
noforce ppfts

force REFCLK  1,0 $CLK1 -repeat $CLK0
force LCLKF  1,0 $CLK_PCI1 -repeat $CLK_PCI0

force LRESET 0

force USERO 0

force ads 1
force lwr 1
force BLAST 1
force lhold 0

# Wait for DCM delayed reset
run [expr $CLK_RUN * 30]
force LRESET 1

# Wait for DCM is up
run [expr $CLK_RUN * 100]

# Tests

PCI_write 10 80

run 100



