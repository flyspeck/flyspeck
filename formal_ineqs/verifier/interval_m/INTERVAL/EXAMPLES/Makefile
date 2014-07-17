all: norm opt

norm: example.norm precision.norm

opt: example.opt precision.opt

example.opt: example.ml
	ocamlopt ../interval.cmxa -I .. example.ml ../libinterval.a -o example.opt

example.norm: example.ml
	ocamlc ../interval.cma -I .. example.ml ../libinterval.a -o example.norm

precision.opt: precision.ml
	ocamlopt ../interval.cmxa -I .. precision.ml ../libinterval.a -o precision.opt

precision.norm: precision.ml
	ocamlc ../interval.cma -I .. precision.ml ../libinterval.a -o precision.norm

clean:
	\rm -f *.norm *.opt *.o *.cmx *.cmo *.cmi *~ 
