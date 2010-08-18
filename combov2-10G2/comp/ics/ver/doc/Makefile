#make
# $Id: Makefile 10347 2009-08-13 09:07:51Z xivanc01 $
#-----------------------------------------------------------------------------
#    This program is free software: you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation, either version 3 of the License, or
#    (at your option) any later version.
#
#    This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with this program.  If not, see <http://www.gnu.org/licenses/>.
#
#-----------------------------------------------------------------------------
# Title:        Doxygen Generating Makefile for Test SV Files
# Description:  This makefile generates the doxygen documentation for the 
#               source in 3 steps.  1) generate the SV template from the base
#               and SV delta file 2) generate the project doxyfile from the
#               SV template and the project delta file 3) generate docs
#               with doxygen and generated doxyfile.
#
# Usage:        make docs -- make the documentation
#               make clean -- cleanup - delete all generated files
#
#               To run from trunk:
#               make docs TRUNK=1
#               To run from tagged release area:
#               make docs
#
# Original Author: Sean O'Boyle
# Contact:         seanoboyle@intelligentdv.com
# Company:         Intelligent Design Verification
# Company URL:     http://intelligentdv.com
#
# Download the most recent version here:
#                  http://intelligentdv.com/downloads
#
# File Bugs Here:  http://bugs.intelligentdv.com
#        Project:  DoxygenFilterSV
#
# File: Makefile
# $LastChangedBy: xivanc01 $
# $LastChangedDate: 2009-08-13 11:07:51 +0200 (Thu, 13 Aug 2009) $
# $LastChangedRevision: 10347 $
#
#-----------------------------------------------------------------------------

PATH_DOXYSCR = /opt/doxygen

SV_FILES = SVfiles.txt
SV = $(shell cat $(SV_FILES))
PATH_HOME = $(HOME)
PATH_PRJ = ../tbench $(SV)
DOXYGEN = doxygen
DOXYFILE_BASE = $(PATH_DOXYSCR)/doxyfile/Doxyfile.template
DOXYFILE_SVDELT = $(PATH_DOXYSCR)/doxyfile/idv_doxyfile_sv.delta
DOXYFILE_TMPLCONV = $(PATH_DOXYSCR)/scripts/idv_doxyfile_tmplconv.pl 
DOXYFILE_TMPL = ./Doxyfile_sv.template
DOXYFILE_DELT = ./Doxyfile.delta
DOXYFILE_OUT = ./Doxyfile.output
DOC_PATH = doxygen_doc

DOC = $(DOC_PATH)/index.html

all: docs

SVfiles.txt:
	$(shell tcl ../doc_level.fdo)
	
# Create the Template SystemVerilog Doxyfile
$(DOXYFILE_TMPL): $(DOXYFILE_TMPLCONV) $(DOXYFILE_BASE) $(DOXYFILE_SVDELT)
	$(DOXYFILE_TMPLCONV) --path_home "$(PATH_HOME)" --path_doxyscr "$(PATH_DOXYSCR)" --path_prj "$(PATH_PRJ)" --template $(DOXYFILE_BASE) --delta $(DOXYFILE_SVDELT) --output $(DOXYFILE_TMPL)

# Create the project Doxyfile from the template SystemVerilog Doxyfile
$(DOXYFILE_OUT): $(DOXYFILE_TMPLCONV) $(DOXYFILE_TMPL) $(DOXYFILE_DELT) $(SV_FILES)
	echo $(PATH_PRJ)
	$(DOXYFILE_TMPLCONV) --path_home "$(PATH_HOME)" --path_doxyscr "$(PATH_DOXYSCR)" --path_prj "$(PATH_PRJ)" --template $(DOXYFILE_TMPL) --delta $(DOXYFILE_DELT) --output $(DOXYFILE_OUT)

doxyfile : $(DOXYFILE_OUT)

# Build the Documentation
docs: $(DOXYFILE_OUT)
	$(DOXYGEN) $(DOXYFILE_OUT)
.PHONY :	docs clean doxyfile

# Clean the documentation
clean:
	rm -rf $(DOC_PATH)
	rm -rf $(DOXYFILE_TMPL) $(DOXYFILE_OUT)
	rm -rf $(SV_FILES)	
