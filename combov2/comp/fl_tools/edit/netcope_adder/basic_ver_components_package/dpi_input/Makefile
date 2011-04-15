# Makefile for SystemVerilog DPI Library

# DLL to compile
INPUT_WRAPPER_DLL  = dpi_input_wrapper_pkg

# sze2 paths
SZE2_INCLUDE       = /usr/local/liberouter/include
SZE2_LIB_PATH      = /usr/local/liberouter/lib

CC=g++
LL=ld
INCLUDE=/usr/local/fpga/modeltechdir/Modeltech66a/include
LIBS=-lm -lsze2
FLAGS=-c -fPIC
DLL_FLAGS=-shared -Bsymbolic -E --allow-shlib-undefined


all: $(INPUT_WRAPPER_DLL).so

clean:
	rm -fR *.o *.$(DLL_SUFFIX) $(INPUT_WRAPPER_DLL).h

#
# Rules for compiling DPI library
#
$(INPUT_WRAPPER_DLL).h: $(INPUT_WRAPPER_DLL).sv
	vlib work
	echo "import $(INPUT_WRAPPER_DLL)::*; module top; endmodule" > top.sv
	vlog -sv $(INPUT_WRAPPER_DLL).sv
	vlog -sv -dpiheader $(INPUT_WRAPPER_DLL).h top.sv
	rm -fR top.sv work

%.so: %.o 
	$(LL) $(DLL_FLAGS) -o $@ $^ -L$(SZE2_LIB_PATH) $(LIBS)

$(INPUT_WRAPPER_DLL).o: $(INPUT_WRAPPER_DLL).h $(INPUT_WRAPPER_DLL).c 
	$(CC) $(FLAGS) -I$(INCLUDE) -I$(SZE2_INCLUDE) $(INPUT_WRAPPER_DLL).c -o $@
