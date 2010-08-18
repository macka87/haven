clean_all

# --------------------------------------------------------------------------
# technology library setting
set part 2V3000bf957
set process 6
set wire_table xcv2-3000-6_wc
load_library xcv2

# --------------------------------------------------------------------------
# read input files
read ../crc8s.vhd

# --------------------------------------------------------------------------
# pre-optimize
pre_optimize -common_logic -unused_logic -boundary -xor_comparator_optimize \
-extract

optimize -macro -target xcv2

