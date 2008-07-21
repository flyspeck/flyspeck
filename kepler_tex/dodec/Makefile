
all : proofdodec.pdf

proofdodec.pdf : *.tex

#all : flypaper.pdf


%.dvi : %.tex
	latex --src-specials "\scrollmode\input" $<

%.ps : %.dvi 
	dvips $< -o

%.pdf : %.tex
	pdflatex $<
