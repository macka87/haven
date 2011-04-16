# Makefile for SystemVerilog DPI Library

# DLL to compile
WRAPPER_DLL  = dpi_wrapper_pkg

# sze2 paths
SZE2_INCLUDE       = /usr/local/liberouter/include
SZE2_LIB_PATH      = /usr/local/liberouter/lib

CC=gcc
LL=ld
INCLUDE=/usr/local/fpga/modeltechdir/Modeltech66a/include
LIBS=-lm -lsze2
FLAGS=-c -fPIC
DLL_FLAGS=-shared -Bsymbolic --allow-shlib-undefined


all: $(WRAPPER_DLL).so

clean:
	rm -fR *.o *.$(DLL_SUFFIX) $(WRAPPER_DLL).h

#
# Rules for compiling DPI library
#
$(WRAPPER_DLL).h: $(WRAPPER_DLL).sv
	vlib work
	echo "import $(WRAPPER_DLL)::*; module top; endmodule" > top.sv
	vlog -sv $(WRAPPER_DLL).sv
	vlog -sv -dpiheader $(WRAPPER_DLL).h top.sv
	rm -fR top.sv work

%.so: %.o 
	$(LL) $(DLL_FLAGS) -L$(SZE2_LIB_PATH) $(LIBS) -o $@ $^

$(WRAPPER_DLL).o: $(WRAPPER_DLL).h $(WRAPPER_DLL).c 
	$(CC) $(FLAGS) -I$(INCLUDE) -I$(SZE2_INCLUDE) $(WRAPPER_DLL).c -o $@
