# Makefile for SystemVerilog DPI Library

# DLL to compile
OUTPUT_WRAPPER_DLL  = dpi_output_wrapper_pkg

# sze2 paths
SZE2_INCLUDE       = /usr/local/liberouter/include
SZE2_LIB_PATH      = /usr/local/liberouter/lib

CC=g++
LL=ld
INCLUDE=/usr/local/fpga/modeltechdir/Modeltech66a/include
LIBS=-lm -lsze2
FLAGS=-c -fPIC
DLL_FLAGS=-shared -Bsymbolic -E --allow-shlib-undefined


all: $(OUTPUT_WRAPPER_DLL).so

clean:
	rm -fR *.o *.$(DLL_SUFFIX) $(OUTPUT_WRAPPER_DLL).h

#
# Rules for compiling DPI library
#
$(OUTPUT_WRAPPER_DLL).h: $(OUTPUT_WRAPPER_DLL).sv
	vlib work
	echo "import $(OUTPUT_WRAPPER_DLL)::*; module top; endmodule" > top.sv
	vlog -sv $(OUTPUT_WRAPPER_DLL).sv
	vlog -sv -dpiheader $(OUTPUT_WRAPPER_DLL).h top.sv
	rm -fR top.sv work

%.so: %.o 
	$(LL) $(DLL_FLAGS) -o $@ $^ -L$(SZE2_LIB_PATH) $(LIBS)

$(OUTPUT_WRAPPER_DLL).o: $(OUTPUT_WRAPPER_DLL).h $(OUTPUT_WRAPPER_DLL).c 
	$(CC) $(FLAGS) -I$(INCLUDE) -I$(SZE2_INCLUDE) $(OUTPUT_WRAPPER_DLL).c -o $@
