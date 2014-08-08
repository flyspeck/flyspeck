HOL_NAT=hol-light-nat
INEQ_NAT=formal_ineqs-nat
FLYSPECK_NAT=flyspeck-nat

CAMLP5=camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I $(HOL_NAT) pa_j.cmo

OPT_ML=ocamlopt -c -pp "$(CAMLP5)"
OPT_MLI=$(OPT_ML)
OPT_HL=ocamlopt -c -pp "$(CAMLP5) -impl"

DIRS=	$(HOL_NAT) \
	$(HOL_NAT)/Library \
	$(HOL_NAT)/Multivariate \
	$(INEQ_NAT) \
	$(INEQ_NAT)/lib/ssreflect \
	$(INEQ_NAT)/lib \
	$(INEQ_NAT)/misc \
	$(INEQ_NAT)/arith \
	$(INEQ_NAT)/taylor/theory \
	$(INEQ_NAT)/taylor \
	$(INEQ_NAT)/jordan \
	$(INEQ_NAT)/list \
	$(INEQ_NAT)/informal \
	$(INEQ_NAT)/trig \
	$(INEQ_NAT)/verifier \
	$(INEQ_NAT)/verifier/interval_m \
	$(FLYSPECK_NAT)

INCLUDE=$(addprefix -I ,$(DIRS))

HOL_CORE_SRC0=system.ml \
	lib.ml \
	fusion.ml \
	basics.ml \
	nets.ml \
	printer.ml \
	preterm.ml \
	parser.ml \
	equal.ml \
	bool.ml \
	drule.ml \
	tactics.ml \
	itab.ml \
	simp.ml \
	theorems.ml \
	ind_defs.ml \
	class.ml \
	trivia.ml \
	canon.ml \
	meson.ml \
	quot.ml \
	impconv.ml \
	pair.ml \
	nums.ml \
	recursion.ml \
	arith.ml \
	wf.ml \
	calc_num.ml \
	normalizer.ml \
	grobner.ml \
	ind_types.ml \
	lists.ml \
	realax.ml \
	calc_int.ml \
	realarith.ml \
	real.ml \
	calc_rat.ml \
	int.ml \
	sets.ml \
	iterate.ml \
	cart.ml \
	define.ml \
	hol_core.ml

HOL_LIB_SRC0=Library/binomial.ml \
	Library/wo.ml \
	Library/card.ml \
	Library/permutations.ml \
	Library/products.ml \
	Library/floor.ml \
	Library/iter.ml \
	Multivariate/misc.ml \
	Multivariate/vector1.ml \
	Multivariate/vector2.ml \
	Multivariate/vector3.ml \
	Multivariate/vector4.ml \
	Multivariate/vectors.ml \
	Multivariate/determinants.ml \
	Multivariate/topology1.ml \
	Multivariate/topology2.ml \
	Multivariate/topology3.ml \
	Multivariate/topology4.ml \
	Multivariate/topology5.ml \
	Multivariate/topology.ml \
	Multivariate/convex1.ml \
	Multivariate/convex2.ml \
	Multivariate/convex.ml \
	Multivariate/paths1.ml \
	Multivariate/paths2.ml \
	Multivariate/paths3.ml \
	Multivariate/paths4.ml \
	Multivariate/paths.ml \
	Multivariate/polytope1.ml \
	Multivariate/polytope.ml \
	Multivariate/dimension1.ml \
	Multivariate/dimension.ml \
	Multivariate/derivatives.ml \
	Multivariate/integration1.ml \
	Multivariate/integration2.ml \
	Multivariate/integration3.ml \
	Multivariate/integration4.ml \
	Multivariate/integration.ml \
	Multivariate/measure1.ml \
	Multivariate/measure2.ml \
	Multivariate/measure3.ml \
	Multivariate/measure.ml \
	Multivariate/complexes.ml \
	Multivariate/canal.ml \
	Multivariate/transcendentals1.ml \
	Multivariate/transcendentals2.ml \
	Multivariate/transcendentals.ml \
	Multivariate/realanalysis1.ml \
	Multivariate/realanalysis2.ml \
	Multivariate/realanalysis3.ml \
	Multivariate/realanalysis.ml

INEQ_SRC0= misc/misc_vars.hl \
	misc/misc_functions.hl \
	misc/report.hl \
	arith/interval_arith.hl \
	arith_options.hl \
	verifier_options.hl \
	arith/arith_num.mli \
	arith/arith_num.hl \
	arith/arith_cache.hl \
	arith/arith_nat.hl \
	arith/num_exp_theory.hl \
	arith/float_theory.hl \
	arith/arith_float.mli \
	arith/arith_float.hl \
	arith/more_float.hl \
	lib/ssreflect/sections.hl \
	lib/ssreflect/ssreflect.hl \
	lib/ssrfun.hl \
	lib/ssrbool.hl \
	lib/ssrnat.hl \
	jordan/parse_ext_override_interface.hl \
	jordan/refinement.hl \
	jordan/real_ext.hl \
	jordan/taylor_atn.hl \
	list/more_list.hl \
	list/list_conversions.mli \
	list/list_conversions.hl \
	list/list_float.mli \
	list/list_float.hl \
	trig/poly.hl \
	trig/poly_eval.hl \
	trig/series.hl \
	trig/sin_cos.hl \
	trig/matan.hl \
	arith/float_atn.mli \
	arith/float_atn.hl \
	trig/cos_bounds_eval.mli \
	trig/cos_bounds_eval.hl \
	trig/cos_eval.mli \
	trig/cos_eval.hl \
	trig/sin_eval.mli \
	trig/sin_eval.hl \
	trig/matan_eval.mli \
	trig/matan_eval.hl \
	arith/eval_interval.hl \
	taylor/theory/taylor_interval1.hl \
	taylor/theory/taylor_interval.hl \
	taylor/theory/multivariate_taylor1.hl \
	taylor/theory/multivariate_taylor2.hl \
	taylor/theory/multivariate_taylor.hl \
	taylor/m_taylor.hl \
	taylor/m_taylor_arith.hl \
	taylor/m_taylor_arith2.hl \
	verifier/certificate.hl \
	informal/informal_nat.mli \
	informal/informal_nat.hl \
	informal/informal_float.mli \
	informal/informal_float.hl \
	informal/informal_interval.mli \
	informal/informal_interval.hl \
	informal/informal_poly.mli \
	informal/informal_poly.hl \
	informal/informal_atn.mli \
	informal/informal_atn.hl \
	informal/informal_sin_cos.mli \
	informal/informal_sin_cos.hl \
	informal/informal_matan.mli \
	informal/informal_matan.hl \
	informal/informal_eval_interval.hl \
	informal/informal_taylor.hl \
	informal/informal_search.hl \
	informal/informal_verifier.hl \
	verifier/m_verifier_build.hl \
	verifier/m_verifier.hl \
	verifier/m_verifier_main.hl

FLYSPECK_SRC0=prove_by_refinement.hl \
	definitions.hl \
	serialization.hl \
	break_case.hl \
	hminus.hl \
	ineq_data.hl

HOL_CORE_SRC=$(addprefix $(HOL_NAT)/,$(HOL_CORE_SRC0))
HOL_LIB_SRC=$(addprefix $(HOL_NAT)/,$(HOL_LIB_SRC0))
INEQ_SRC=$(addprefix $(INEQ_NAT)/,$(INEQ_SRC0))
FLYSPECK_SRC=$(addprefix $(FLYSPECK_NAT)/,$(FLYSPECK_SRC0))

HOL_CORE_OBJ=$(HOL_CORE_SRC:.ml=.cmx)
HOL_LIB_OBJ=$(HOL_LIB_SRC:.ml=.cmx)

TMP_INEQ_OBJ=$(INEQ_SRC:.hl=.cmx)
INEQ_OBJ=$(TMP_INEQ_OBJ:.mli=.cmi)
BUILD_INEQ_OBJ=$(filter-out %.cmi, $(INEQ_OBJ))

FLYSPECK_OBJ=$(FLYSPECK_SRC:.hl=.cmx)


parser:
	ocamlc -c -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo" -I +camlp5 $(HOL_NAT)/pa_j.ml

hol-core: $(HOL_CORE_OBJ)
	@echo "HOL Light core compiled"

hol-lib: $(HOL_LIB_OBJ)
	@echo "HOL Light library compiled"

ineq: $(INEQ_OBJ)
	@echo "Formal Verification Tool compiled"

flyspeck: $(FLYSPECK_OBJ)
	@echo "Flyspeck inequalities compiled"

build:
	$(OPT_ML) config.ml
	$(OPT_HL) $(INCLUDE) -impl main_verifier.hl
	ocamlopt -linkall -o verifier unix.cmxa nums.cmxa str.cmxa config.cmx $(INCLUDE) \
		$(HOL_CORE_OBJ) $(HOL_LIB_OBJ) $(BUILD_INEQ_OBJ) $(FLYSPECK_OBJ) \
		main_verifier.cmx

sharp:
	$(OPT_HL) $(INCLUDE) -impl $(FLYSPECK_NAT)/sharp_theorems.hl
	$(OPT_HL) $(INCLUDE) -impl $(FLYSPECK_NAT)/sharp_ineqs.hl
	ocamlopt -linkall -o sharp_verifier unix.cmxa nums.cmxa str.cmxa $(INCLUDE) \
		$(HOL_CORE_OBJ) $(HOL_LIB_OBJ) $(BUILD_INEQ_OBJ) $(FLYSPECK_OBJ) \
		sharp_theorems.cmx sharp_ineqs.cmx


test_flyspeck:
	$(OPT_HL) $(INCLUDE) -impl test_flyspeck.hl
	ocamlopt -linkall -o test_flyspeck $(INCLUDE) unix.cmxa nums.cmxa \
		$(HOL_CORE_OBJ) $(HOL_LIB_OBJ) $(BUILD_INEQ_OBJ) test_flyspeck.cmx

%.cmi : %.mli
	$(OPT_MLI) $(INCLUDE) $^

%.cmx : %.hl
	$(OPT_HL) $(INCLUDE) -impl $^

%.cmx : %.ml
	$(OPT_ML) $(INCLUDE) $^

clean-hol:
	find $(HOL_NAT) -name "*.cmi" -delete \
			-o -name "*.cmx" -delete \
			-o -name "*.o" -delete

clean-ineq:
	find $(INEQ_NAT) -name "*.cmi" -delete \
			-o -name "*.cmx" -delete \
			-o -name "*.o" -delete

clean-flyspeck:
	find $(FLYSPECK_NAT) -name "*.cmi" -delete \
				-o -name "*.cmx" -delete \
				-o -name "*.o" -delete

clean: clean-hol clean-ineq clean-flyspeck
	rm -f *.cmi *.cmx *.o test_flyspeck

