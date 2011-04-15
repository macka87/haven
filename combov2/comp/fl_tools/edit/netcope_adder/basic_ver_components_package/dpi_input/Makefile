# Makefile for SystemVerilog DPI Library

# DLL to compile
INPUT_WRAPPER_DLL  = dpi_input_wrapper_pkg

ifeq ($(OS), Windows_NT)
  CC=g++ 
  LL=g++
  INCLUDE=C:\Modeltech\include
  LIB=C:\Modeltech\win32
  LIBS=-lmtipli -lm
  FLAGS=-c
  DLL_FLAGS=-shared -Bsymbolic
  DLL_SUFFIX=dll
  ifeq ($(TERM),cygwin)
    CC=$(WIN_GPLUSPLUS)
    LL=$(WIN_GPLUSPLUS)
	QUOTE="
  else
  	QUOTE=
  endif

else # Linux
  PLATFORM=`uname`
  CC=g++
  LL=ld
  INCLUDE=/usr/local/fpga/modeltechdir/Modeltech65c/include
  LIB=
  LIBS=-lm
  FLAGS=-c -fPIC
  DLL_FLAGS=-shared -Bsymbolic -E --allow-shlib-undefined
  DLL_SUFFIX=so
  QUOTE="
endif


all: $(INPUT_WRAPPER_DLL).$(DLL_SUFFIX)

clean:
	rm -fR *.o *.$(DLL_SUFFIX) $(INPUT_WRAPPER_DLL).h

#
# Rules for compiling DPI library
#
$(INPUT_WRAPPER_DLL).h: $(INPUT_WRAPPER_DLL).sv
	vlib work
	echo $(QUOTE)import $(INPUT_WRAPPER_DLL)::*; module top; endmodule$(QUOTE) > top.sv
	vlog -sv $(INPUT_WRAPPER_DLL).sv
	vlog -sv -dpiheader $(INPUT_WRAPPER_DLL).h top.sv
	rm -fR top.sv work

$(INPUT_WRAPPER_DLL).$(DLL_SUFFIX): $(INPUT_WRAPPER_DLL).o 
	$(LL) $(DLL_FLAGS) -o $@ $^ -L$(LIB) $(LIBS)

$(INPUT_WRAPPER_DLL).o: $(INPUT_WRAPPER_DLL).h $(INPUT_WRAPPER_DLL).c 
	$(CC) $(FLAGS) -I$(INCLUDE) $(INPUT_WRAPPER_DLL).c
