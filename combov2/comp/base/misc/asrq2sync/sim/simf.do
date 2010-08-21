# Behavioral simulation
# Author: Jiri Novotny <novotny@ics.muni.cz>
# $Id: simf.do 21 2007-07-31 10:26:03Z kosek $

# Compilation
vlib work
vcom -93 asrq2sync.vhd

# Simulator start
vsim -t ps asrq2sync

set DefaultRadix hex
set UserTimeUnit ns

view wave
restart -force
delete wave *

view wave


# Waves
add wave RESET
add wave ASY_PE
add wave ASY_CLK
add wave SYNC_CLK
add wave SYNC_PULS

# Clock definition
set CLK0 10
set CLK1 5

# Signal initialization
force SYNC_CLK  1,0 $CLK1 -repeat $CLK0

force RESET 1
force ASY_PE 0
force ASY_CLK 0
run $CLK0

force RESET 0

run 1
force ASY_PE 1
force ASY_CLK 1

run $CLK0
run $CLK0
force ASY_CLK 0

run $CLK0

force ASY_CLK 1
run 5

force ASY_CLK 0
run 5

force ASY_CLK 1
run 5

force ASY_CLK 0

force ASY_PE 0
run $CLK0
run $CLK0
run $CLK0

force ASY_CLK 1
run 5
force ASY_CLK 0

run 20




