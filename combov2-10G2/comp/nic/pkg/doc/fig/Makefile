# Makefile to create figure

all: png

png: time_diagram_drawtiming.txt
	drawtiming --output diagram.png  time_diagram_drawtiming.txt

clean:
	rm -f diagram.png
