OCAMLDIR:=$(shell ocamlc -where)
CSLOPT = ocamlopt


tests: tests.ml
	$(CSLOPT) -I .. -o tests ../interval.cmxa unix.cmxa tests.ml ../libinterval.a


clean:
	\rm -f *.cmo *.cmi *.cmx *.o *~  tests

