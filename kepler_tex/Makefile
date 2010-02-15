# http://hsrl.rutgers.edu/ug/make_help.html (Make help)

all : flypaper.pdf

clean: 
	rm *.*~  *.aux *.log *.dvi 


%.dvi : %.tex
	latex --src-specials "\scrollmode\input" $<

%.ps : %.dvi 
	dvips $< -o

%.pdf : %.tex
	pdflatex --src-specials "\scrollmode\input" $<

%.ind : %.idx
	makeindex $<

index : index/*.ind

tarskis.js : array_tarski.js  # remove chars: _ \ $
	tr -d "_\\$$" < array_tarski.js > tarskis.js

fig : # take all figpy/*.py convert to fig/*.pdf

svninfo.txt : *.tex
	svn info | grep "^Revision" > svninfo.txt