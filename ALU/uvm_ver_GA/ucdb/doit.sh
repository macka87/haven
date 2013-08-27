#!/bin/sh
#
# Copyright 2011 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
# PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
# LICENSE TERMS.
#
# UCDB API User Guide Example - Simulation shell script
#
# Usage:     Help/usage ..................... doit.sh
#            Run example .................... doit.sh run
#            Clean directory ................ doit.sh clean
#
SRC="../env_lib/alu_in_coverage_monitor.svh"
APP=create_ucdb
UCDBDUMP="../../../ucdbdump/ucdbdump"

export MTI_HOME="/opt/modelsim10.0c/modeltech/"

if [ "$1" = "clean" ] ; then
    rm -f transcript *.wlf core* *.log workingExclude.cov
    rm -f *.dll *.exp *.lib *.obj *.sl *.o *.so *.ucdb $APP
    rm -f vsim_stacktrace.vstf
    rm -rf work
	rm -rf *.dump
    exit 0
fi

if [ "$1" != "run" ] ; then
    echo ""
    echo "### Help/Usage ..................... doit.sh"
    echo "### Run example .................... doit.sh run"
    echo "### Clean directory ................ doit.sh clean"
    echo ""
fi

# The rest of the script is "run"
rm -rf work
vlib work
if [ $? -ne 0 ]; then
    echo "ERROR: Couldn't run vlib. Make sure \$PATH is set correctly."
    exit 0
fi
if [ -z "$MTI_HOME" ] ; then
    echo "ERROR: Environment variable MTI_HOME is not set"
    exit 0
fi
`vsim -version | grep "64 vsim" > /dev/null`
if [ $? -eq 0 ]; then
    MTI_VCO_MODE=64
else
    MTI_VCO_MODE=32
fi
export MTI_VCO_MODE
platform="linux_x86_64"
rm -f *.o *.dll *.so

LIBPATH=

case `uname` in
Linux)
    gccversion=`gcc -dumpversion | awk -F. '{print $1}'`
    machine=`uname -m`
    if [ "$gccversion" = "2" -o "$machine" = "ia64" ] ; then
        CC="gcc -g -c  -Wall -ansi -I. -I$MTI_HOME/include"
        LD="gcc -lm -Wl,-export-dynamic -o "
    elif [ "$MTI_VCO_MODE" = "64" ] ; then
        CC="gcc -g -c -m64 -Wall -ansi -I. -I$MTI_HOME/include"
        LD="gcc -lm -m64 -Wl,-export-dynamic -o "
    else
        CC="gcc -g -c -m32 -Wall -ansi -I. -I$MTI_HOME/include"
        LD="gcc -lm -m32 -Wl,-export-dynamic -o "
    fi
    LDLIB="$APP.o $MTI_HOME/$platform/libucdb.a"
    ;;
SunOS)
    if [ "$gccversion" = "2" ] ; then
        CC="gcc -g -c -I. -I$MTI_HOME/include"
        LD="gcc -ldl -lm -o "
    elif [ "$MTI_VCO_MODE" = "64" ] ; then
        CC="gcc -g -m64 -c -I. -I$MTI_HOME/include"
        LD="gcc -ldl -lm -m64 -o "
    else
        CC="gcc -g -m32 -c -I. -I$MTI_HOME/include"
        LD="gcc -ldl -lm -m32 -o "
    fi
    LDLIB="$APP.o $MTI_HOME/$platform/libucdb.a"
    ;;
Win*|CYGWIN_NT*)
    CC="cl -c -Ox -Oy /MD -DWIN32 -I`cygpath -m $MTI_HOME/include` "
    LD="link "
    LIBPATH=/LIBPATH:`regtool get '\\HKLM\\SOFTWARE\\Microsoft\\Microsoft SDKs\\Windows\\CurrentInstallFolder'`\\Lib
    LDLIB="`cygpath -d $MTI_HOME/$platform/libucdb.lib`"
    ;;
*)
    echo "Script not configured for `uname`, see User's manual."
    exit 0
    ;;
esac

echo ""
echo "### NOTE: Running UCDB API User Guide Example ..."
echo ""


# preklad alu_in_coverage_monitor.svh
#vlog -cover bcestf $FLAGS $SRC
#vsim -c -coverage top -do "run -all; coverage save test.ucdb; quit"


$CC $APP.c
if [ "$LIBPATH" = "" ] ; then
    $LD $APP $LDLIB
else
    $LD $APP "$LDLIB" "$LIBPATH"
fi
echo "APP=$APP"
./$APP
if [ -x $UCDBDUMP ]
then
	$UCDBDUMP test.ucdb > test.dump
	$UCDBDUMP test_API.ucdb > test_API.dump
	diff test.dump test_API.dump
fi
exit 0
