# makefile to synthesize component

TRASH=xst XST.prj XST.srp XST.xcf XST.xst *.lso *.ngc STD_OUTPUT *.ngr *_xst.xrpt xlnx_auto_0.ise xlnx_auto_0_xdb
TRASH2=*.prec *.edf 

all : xst
	
xst : XST.tcl
		tclsh XST.tcl
		rm -f -fr xst/
		mkdir xst
		mkdir xst/projnav.tmp
		xst -ifn XST.xst
 
precision : Precision.tcl
		precision -shell -file Precision.tcl 	

clean :
		rm -f -fr $(TRASH) 

cleanprec :
		rm -f -fr $(TRASH2)
