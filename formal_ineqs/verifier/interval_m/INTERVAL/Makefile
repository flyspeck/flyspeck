OCAMLDIR:= "$(shell ocamlc -where)"
CSLC = ocamlc
CSLOPT = ocamlopt
NORM_OBJS= fpu.cmo fpu_rename_all.cmo fpu_rename.cmo interval.cmo 
OPT_OBJS=  $(NORM_OBJS:.cmo=.cmx)
CC = gcc

all : interval.cma interval.cmxa libinterval.a doc/index.html ocamlfpu

interval.cma: $(NORM_OBJS)
	$(CSLC) -a -custom -o interval.cma $(NORM_OBJS)


interval.cmxa: $(OPT_OBJS)
	$(CSLOPT) -a -o interval.cmxa  $(OPT_OBJS)

libinterval.a: chcw.o
	rm -f $@
	ar rc $@  chcw.o
	ranlib $@

ocamlfpu: interval.cma libinterval.a
	ocamlmktop -o ocamlfpu chcw.o fpu.cmo interval.cma libinterval.a nums.cma str.cma unix.cma


.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo :
	$(CSLC) -c $<
.mli.cmi :
	$(CSLC) -c $<
.ml.cmx :
	$(CSLOPT) -c $<
.c.o :
	$(CC) -W -Wall -O5 -I $(OCAMLDIR)/caml -c  $<

clean:
	\rm -f *.cmo *.cmi *.cmx *.o *~ *.cma *.cmxa *.a a.out ocamlfpu ocamlfpu.exe

doc/index.html: *.mli
	ocamldoc -d doc -html *.mli

depend:
	ocamldep *.mli *.ml > .depend

include .depend
