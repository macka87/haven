# Makefile for SystemVerilog DPI Library

# DLL to compile
CMATH_DLL = cmath

# Compiling in Windows (only mingw) not working for cygwin compiler
# export WIN_GPLUSPLUS=/cygdrive/c/DevCpp/bin/g++.exe in .bashrc
# solve the problem

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
  INCLUDE=/usr/local/fpga/modeltechdir/Modeltech62g/include
  LIB=
  LIBS=-lm
  FLAGS=-c -fPIC
  DLL_FLAGS=-shared -Bsymbolic -E --allow-shlib-undefined
  DLL_SUFFIX=so
  QUOTE="
endif


all: $(CMATH_DLL).$(DLL_SUFFIX)
	
clean:
	echo $(CYGWIN)
	rm -fR *.h *.o *.$(DLL_SUFFIX)

#
# Rules for compiling cmath DPI library
#
$(CMATH_DLL).h: $(CMATH_DLL).sv
	vlib work
	echo $(QUOTE)import $(CMATH_DLL)::*; module top; endmodule$(QUOTE) > top.sv
	vlog -sv $(CMATH_DLL).sv
	vlog -sv -dpiheader $(CMATH_DLL).h top.sv
	rm -fR top.sv work

$(CMATH_DLL).$(DLL_SUFFIX): $(CMATH_DLL).o
	$(LL) $(DLL_FLAGS) -o $@ $^ -L$(LIB) $(LIBS)

$(CMATH_DLL).o: $(CMATH_DLL).h $(CMATH_DLL).c 
	$(CC) $(FLAGS) -I$(INCLUDE) $(CMATH_DLL).c


