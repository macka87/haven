# Makefile to synthesize component
# $Id: Makefile 6607 2008-12-27 09:47:30Z xlenga00 $
#

TRASH=xst XST.prj XST.srp XST.xcf XST.xst *.lso *.ngc *.ngr
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
