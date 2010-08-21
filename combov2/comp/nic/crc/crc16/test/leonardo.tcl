clean_all

# --------------------------------------------------------------------------
# technology library setting
set part 2V1000fg456
set process 4
set wire_table xcv2-1000-4_wc
load_library xcv2

# --------------------------------------------------------------------------
# read input files
read ../fsm_crc32_16b.vhd
read ../crc32_table_8b.vhd
read ../crc32_table_16b.vhd
read ../crc32_16b.vhd
read top_level.vhd

# --------------------------------------------------------------------------
# pre-optimize
pre_optimize -common_logic -unused_logic -boundary -xor_comparator_optimize \
-extract

optimize -chip -target xcv2

report_area

set_xilinx_eqn
eval "write -format edif top_level.edf"

