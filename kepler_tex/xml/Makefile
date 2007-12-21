TARGET = version2007
PDF = $(TARGET:%=%.pdf)
DVI = $(TARGET:%=%.dvi)
PS = $(TARGET:%=%.ps)
TEX.XML = $(TARGET:%=%.tex.xml)
XHTML = $(TARGET:%=%.xhtml)

LTXDIR 		= $(HOME)/arxmliv/trunk/sty

LTX.blib.dir    	 = $(HOME)/stex/LaTeXML/blib
LTX.bin.dir       = $(LTX.blib.dir)/script
PKGDIR		= $(LTX.blib.dir)/lib/LaTeXML/Package

LATEXML		= $(LTX.bin.dir)/latexml --path=$(PKGDIR) --path=$(LTXDIR)  --inputencoding=iso-8859-1 
LATEXMLPOST	= $(LTX.bin.dir)/latexmlpost --format=xhtml --pmml --cmml --novalid 

all : $(pdf)
tex.xml: $(TEX.XML)

%.dvi : %.tex
	latex --src-specials "\scrollmode\input" $<

%.ps : %.dvi 
	dvips $< -o

%.pdf : %.ps 
	ps2pdf $<


$(TEX.XML): %.tex.xml: %.tex $(LTXML.dep) $(MAKEFILES)
		$(LATEXML)  --output=$@ $(firstword $<) # 2> stderr.log >stdout.log

$(XHTML): %.xhtml: %.tex.xml $(MAKEFILES)
		$(LATEXMLPOST)  --destination=$@ $(firstword $<) #  2> post.stderr.log > post.stdout.log
