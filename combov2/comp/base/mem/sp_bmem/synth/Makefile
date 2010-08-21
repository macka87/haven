# makefile to synthesize component

TRASH=xst XST.prj XST.srp XST.xcf XST.xst *.lso *.ngc 
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

cleanprec : $(TRASH2)
		rm -f -fr $(TRASH2)
