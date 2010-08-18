clean_all

# --------------------------------------------------------------------------
# technology library setting
set part 2V1000fg456
set process 4
set wire_table xcv2-1000-4_wc
load_library xcv2

# --------------------------------------------------------------------------
# read input files
read ../crc8s.vhd
read top_level.vhd

# --------------------------------------------------------------------------
# pre-optimize
pre_optimize -common_logic -unused_logic -boundary -xor_comparator_optimize \
-extract

optimize -chip -target xcv2

set_xilinx_eqn
eval "write -format edif top_level.edf"

