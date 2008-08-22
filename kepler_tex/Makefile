# http://hsrl.rutgers.edu/ug/make_help.html (Make help)

all : flypaper.pdf

clean: 
	rm *.*~  *.aux *.log *.dvi 


%.dvi : %.tex
	latex --src-specials "\scrollmode\input" $<

%.ps : %.dvi 
	dvips $< -o

%.pdf : %.tex
	pdflatex $<

%.ind : %.idx
	makeindex $<

index : index/*.ind

tarskis.js : array_tarski.js  # remove chars: _ \ $
	tr -d "_\\$$" < array_tarski.js > tarskis.js
