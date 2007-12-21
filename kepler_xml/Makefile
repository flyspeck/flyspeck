
all : version2007.pdf


%.dvi : %.tex
	latex --src-specials "\scrollmode\input" $<

%.ps : %.dvi 
	dvips $< -o

%.pdf : %.ps 
	ps2pdf $<
