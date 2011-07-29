# the name of the output
CO=acc_ver

# names of files other than sources the change of which should recompile the
# source
#CHANGED_FILES_OTHER=literature.bib

# The output format for figures
FIG_OUT_FMT=pdf

# The conversion program for .fig files
FIG=fig2dev

# Flags for Fig2Dev
FIG_FLAGS=-L $(FIG_OUT_FMT)

# The image conversion to PDF program name
IMG_TO_PDF=epstopdf

# The image conversion program output file option
IMG_TO_PDF_OUT=--outfile

# The image PDF file extension
PDF_EXT=pdf

# List of TeX files
TEX_FILES=$(wildcard *.tex)

# List of figures
FIG_FILES=$(patsubst %.fig,%.$(FIG_OUT_FMT), $(wildcard fig/*.fig))

# List of graphs
DOT_FILES=$(patsubst %.dot,%.$(FIG_OUT_FMT), $(wildcard fig/*.dot))

# List of gnuplot files
GNUPLOT_FILES=$(patsubst %.gpi,%.$(FIG_OUT_FMT), $(wildcard fig/*.gpi))

# The .dot conversion program
DOT=dot

# The GNUPlot executable
GNUPLOT=gnuplot

###############################################################################
#                                 Rules                                       #
###############################################################################

.PHONY: all images clean pack love

all: $(CO).pdf

$(CO).pdf: $(CHANGED_FILES_OTHER) $(TEX_FILES) $(FIG_FILES) $(DOT_FILES) $(GNUPLOT_FILES)
#	pdflatex $(CO)
#	bibtex $(CO)
	pdflatex $(CO)
	pdflatex $(CO)


%.$(FIG_OUT_FMT): %.fig
	$(FIG) $(FIG_FLAGS) $< $@

%.$(FIG_OUT_FMT): %.dot
	$(DOT) -T$(FIG_OUT_FMT) -o$(patsubst %.dot,%.$(FIG_OUT_FMT), $<) $<

%.$(FIG_OUT_FMT): %.gpi
	$(GNUPLOT) $<

clean:
	rm -f *.dvi *.log $(CO).blg $(CO).bbl $(CO).toc *.aux $(CO).out $(CO).lof
	rm -f $(CO).pdf
	rm -f $(FIG_FILES)
	rm -f $(patsubst %.pdf,%.fig.bak, $(FIG_FILES))
	rm -f $(DOT_FILES)
	rm -f $(GNUPLOT_FILES)
	rm -f *~

love: $(CO).pdf
	xpdf $(CO).pdf
