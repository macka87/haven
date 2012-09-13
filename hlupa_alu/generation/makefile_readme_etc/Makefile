
OVM_HOME ?= $(QUESTA_HOME)/verilog_src/ovm-2.1
OVM_CONTAINER ?= ../../../ovm_container

all: work build run

tarball: clean tar

work:
	vlib work

build:
	vlog -cover sbce +incdir+$(OVM_HOME)/src $(OVM_CONTAINER)/ovm_container.sv
	vlog -cover sbce ../common/dut_if.sv
	vlog -cover sbce ../common/dut.sv
	vlog -cover sbce +incdir+$(OVM_HOME)/src ../common/my_pkg.sv
	vlog -cover sbce +incdir+$(OVM_HOME)/src ../sequence_library/my_seq_library.sv
	vlog -cover sbce +incdir+$(OVM_HOME)/src ../tests/my_test_library.sv
	vlog -cover sbce ../common/top.sv
	#DUT compilation
	vcom -93 -explicit -work work ../src/alu.vhd

run:
	#-c je ze iba pre command line
	vsim -c -do "run -all" top
	#vsim -do "run -all" top

clean:
	rm -rf work transcript *~ vsim.wlf *.log
	
tar:
	@(cd ../.. ;\
	tar -cf generation/makefile_readme_etc/hlupa_alu.tar\
	generation/common\
	generation/sequence_library\
	generation/tests\
	generation/makefile_readme_etc/Makefile\
	generation/makefile_readme_etc/README.txt;\
	cd generation/makefile_readme_etc)
	@gzip -f hlupa_alu.tar