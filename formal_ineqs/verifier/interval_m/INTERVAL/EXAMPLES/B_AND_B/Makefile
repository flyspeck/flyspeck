CSLC = ocamlc
CSLOPT = ocamlopt
CSLDEP = ocamldep
INCLUDES= -I ../..
CSLFLAGS=$(INCLUDES)
CSLOPTFLAGS=$(INCLUDES)

TESTNORM_OBJS= pqueue.cmo b_and_b.cmo main.cmo
TESTOPT_OBJS=  $(TESTNORM_OBJS:.cmo=.cmx)

all: testnorm testopt

testopt : $(TESTOPT_OBJS)
	$(CSLOPT) $(CSLOPTFLAGS) -o $@ ../../interval.cmxa $(TESTOPT_OBJS) ../../libinterval.a

testnorm : $(TESTNORM_OBJS)
	$(CSLC) $(CSLFLAGS)  -o $@ ../../interval.cma $(TESTNORM_OBJS) ../../libinterval.a  


.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo :
	$(CSLC) $(CSLFLAGS) -c $<
.mli.cmi :
	$(CSLC) $(CSLFLAGS) -c $<
.ml.cmx :
	$(CSLOPT) $(CSLOPTFLAGS) -c $<

clean:
	\rm -f *.cmo *.cmi *.cmx *.o *.a *.cma *.cmxa testnorm testopt *~

depend:
	$(CSLDEP) $(INCLUDES) *.mli *.ml >.depend

include .depend

