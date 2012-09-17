# *****************************************************************************
#  Project Name: HAVEN
#  File Name:    Makefile
#  Description:  Compiles And Runs Verification
#  Authors:      Michaela Belesova <xbeles00@stud.fit.vutbr.cz>,
#                Marcela Simkova <isimkova@fit.vutbr.cz> 
#  Date:         17.9.2012
#  ************************************************************************** */

OVM_HOME ?= $(QUESTA_HOME)/verilog_src/ovm-2.1
OVM_BASIC ?= ../../combov2/comp/sw_ver/ovm_basic_components

all: work build run

work:
	vlib work

build:
	vlog -cover sbce +incdir+$(OVM_HOME)/src +incdir+$(OVM_BASIC) $(OVM_BASIC)/sv_basic_comp_pkg.sv
	vlog -cover sbce alu_general_settings.sv
	vlog -cover sbce dut_if.sv
	vlog -cover sbce dut.sv
	vlog -cover sbce +incdir+$(OVM_HOME)/src alu_transaction_result.sv
	vlog -cover sbce +incdir+$(OVM_HOME)/src alu_transaction.sv
	vlog -cover sbce +incdir+$(OVM_HOME)/src alu_subscriber.sv
	vlog -cover sbce +incdir+$(OVM_HOME)/src alu_subscriber.sv  
	vlog -cover sbce +incdir+$(OVM_HOME)/src alu_sequence.sv
	#vlog -cover sbce +incdir+$(OVM_HOME)/src alu_transaction_table.sv  
	#vlog -cover sbce +incdir+$(OVM_HOME)/src alu_scoreboard.sv
	vlog -cover sbce +incdir+$(OVM_HOME)/src alu_sequencer.sv
	vlog -cover sbce +incdir+$(OVM_HOME)/src alu_monitor.sv
	vlog -cover sbce +incdir+$(OVM_HOME)/src alu_dut_if_wrapper.sv 
	vlog -cover sbce +incdir+$(OVM_HOME)/src alu_driver.sv
	vlog -cover sbce +incdir+$(OVM_HOME)/src alu_agent.sv
	vlog -cover sbce +incdir+$(OVM_HOME)/src alu_env.sv  
	vlog -cover sbce +incdir+$(OVM_HOME)/src alu_test.sv
	vlog -cover sbce alu_top.sv
	#DUT compilation
	vcom -93 -explicit -work work ../alu/alu.vhd

run:
	#-c je ze iba pre command line
	vsim -c -do "run -all" AluTop
	#vsim -do "run -all" AluTop

clean:
	rm -rf work transcript *~ vsim.wlf *.log