# Makefile for SystemVerilog DPI Library

# DLL to compile
WRAPPER_DLL  = dpi_mi32_wrapper_pkg

CC=gcc
LL=ld
INCLUDE=/opt/modelsim10.0c/modeltech/include
LIBS=-lm -lsze2 -lcombo
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
	$(CC) $(FLAGS) -I$(INCLUDE) $(WRAPPER_DLL).c -o $@
