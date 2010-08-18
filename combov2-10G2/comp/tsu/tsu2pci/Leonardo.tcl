clean_all

# --------------------------------------------------------------------------
# technology library setting
set part 2V3000bf957
set process 4
set wire_table xcv2-3000-4_wc
load_library xcv2

# --------------------------------------------------------------------------
# set working directories
set SRCPATH "."
set_working_dir $SRCPATH

# Base directories
set VHDL_BASE        "../../.."
set UNIT_BASE        "$VHDL_BASE/units"
set SCAMPI_BASE      "$VHDL_BASE/projects/scampi_ph2"
set COMMON_BASE      "$VHDL_BASE/units/common"
set MODELS_BASE      "$VHDL_BASE/models"
set PTM_BASE         "$VHDL_BASE/ptm"
set TSU_BASE         "$PTM_BASE/projects/time_stamp"
set TSUADD_BASE      "$UNIT_BASE/tsu"

# --------------------------------------------------------------------------
# read input files
#Common components
analyze "$COMMON_BASE/asrq2sync/asrq2sync.vhd"
analyze "$COMMON_BASE/ad2sd/ad2sd.vhd"

#CLK_GEN component
analyze "$SCAMPI_BASE/comp/clk_gen/clk2x.vhd"
analyze "$SCAMPI_BASE/comp/clk_gen/clk4x.vhd"
analyze "$SCAMPI_BASE/comp/clk_gen/clk_gen.vhd"

#Local bus
analyze "$UNIT_BASE/lb/lbconn_mem.vhd"
analyze "$UNIT_BASE/lb/lbconn_mem.vhd"
analyze "$UNIT_BASE/lb/local_bus.vhd"

#TSU Components
analyze "$TSUADD_BASE/tsu_add_fsm.vhd"
analyze "$TSUADD_BASE/tsu_add.vhd"

#top_level entity
analyze "$VHDL_BASE/combo6/chips/fpga.vhd"
#analyze "$TSUADD_BASE/fpga.vhd"

#architecture of top_level for TSU debuging
analyze "$TSUADD_BASE/tsu2pci/tsu2pci.vhd"

elaborate fpga
set_attribute u_tsu_add.reg_regiob_tsdv -instance -name IOB -value TRUE
set_attribute u_tsu_add.reg_regiob_ppfts -instance -name IOB -value TRUE
set_attribute u_tsu_add.reg_regiob_ts(*) -instance -name IOB -value TRUE
set_attribute u_tsu_add.reg_regiob_tsinit -instance -name IOB -value TRUE
set_attribute u_tsu_add.reg_regiob_tsshort -instance -name IOB -value TRUE

# --------------------------------------------------------------------------
# pre-optimize
pre_optimize -common_logic -unused_logic -boundary -xor_comparator_optimize \
-extract

optimize -target xcv2

# -hierarchy preserve

set_xilinx_eqn
write -format edif tsu2pci.edf

