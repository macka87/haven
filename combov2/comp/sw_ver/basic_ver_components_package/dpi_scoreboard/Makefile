# Makefile for SystemVerilog DPI Library

# DLL to compile
TR_TABLE_DLL  = dpi_tr_table_pkg

# sze2 paths
SZE2_INCLUDE       = /usr/local/liberouter/include
SZE2_LIB_PATH      = /usr/local/liberouter/lib

CC=gcc
LL=ld
INCLUDE=/opt/modelsim10.0c/modeltech/include
LIBS=-lm -lsze2
FLAGS=-c -fPIC
DLL_FLAGS=-shared -Bsymbolic --allow-shlib-undefined


all: $(TR_TABLE_DLL).so

clean:
	rm -fR *.o *.$(DLL_SUFFIX) $(TR_TABLE_DLL).h

#
# Rules for compiling DPI library
#
$(TR_TABLE_DLL).h: $(TR_TABLE_DLL).sv
	vlib work
	echo "import $(TR_TABLE_DLL)::*; module top; endmodule" > top.sv
	vlog -sv $(TR_TABLE_DLL).sv
	vlog -sv -dpiheader $(TR_TABLE_DLL).h top.sv
	rm -fR top.sv work

%.so: %.o 
	$(LL) $(DLL_FLAGS) -L$(SZE2_LIB_PATH) $(LIBS) -o $@ $^

$(TR_TABLE_DLL).o: $(TR_TABLE_DLL).h $(TR_TABLE_DLL).c 
	$(CC) $(FLAGS) -I$(INCLUDE) -I$(SZE2_INCLUDE) $(TR_TABLE_DLL).c -o $@
