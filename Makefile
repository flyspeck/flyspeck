HOL_NATIVE_DIR=/Users/monad/Work/git/forks/hol-light-my
FORMALIZATION_DIR=text_formalization

CAMLP5_PATH=
CAMLP5=camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I $(HOL_NATIVE_DIR) pa_j.cmo

OPT_ML=ocamlopt -c -pp "$(CAMLP5_PATH)$(CAMLP5)"
OPT_MLI=$(OPT_ML)
OPT_HL=ocamlopt -c -pp "$(CAMLP5_PATH)$(CAMLP5) -impl"
WARNINGS=-w +33
#+44+45
OPTIONS=

DIRS=\
	$(HOL_NATIVE_DIR) \
	$(HOL_NATIVE_DIR)/Rqe \
	$(HOL_NATIVE_DIR)/Library \
	$(HOL_NATIVE_DIR)/Multivariate \
	$(FORMALIZATION_DIR)/build \
	$(FORMALIZATION_DIR)/general \
	$(FORMALIZATION_DIR)/leg \
	$(FORMALIZATION_DIR)/jordan \
	$(FORMALIZATION_DIR)/trigonometry \
	$(FORMALIZATION_DIR)/nonlinear \
	$(FORMALIZATION_DIR)/volume \
	$(FORMALIZATION_DIR)/hypermap \
	$(FORMALIZATION_DIR)/fan \
	$(FORMALIZATION_DIR)/packing \
	$(FORMALIZATION_DIR)/local \
	$(FORMALIZATION_DIR)/tame \
	jHOLLight/caml \
	jHOLLight/Examples \
	$(FORMALIZATION_DIR)/tame/ssreflect \
	formal_lp/hypermap/ssreflect \
	formal_lp/hypermap/ineqs \
	formal_lp/hypermap/computations \
	formal_lp/ineqs

INCLUDE=$(addprefix -I ,$(DIRS))

HOL_SRC0=\
	system.ml \
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
	firstorder.ml \
	metis.ml \
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
	hol_core.ml \
	Library/wo.ml \
	Library/card.ml \
	Library/floor.ml \
	Multivariate/misc.ml \
	Multivariate/vectors.ml \
	Library/products.ml \
	Library/permutations.ml \
	Multivariate/determinants.ml \
	Library/iter.ml \
	Multivariate/metric.ml \
	Multivariate/topology.ml \
	Multivariate/convex.ml \
	Library/frag.ml \
	Library/grouptheory.ml \
	Multivariate/homology.ml \
	Multivariate/paths.ml \
	Multivariate/polytope.ml \
	Multivariate/degree.ml \
	Multivariate/derivatives.ml \
	Multivariate/integration.ml \
	Multivariate/measure.ml \
	Multivariate/complexes.ml \
	Multivariate/canal.ml \
	Multivariate/transcendentals.ml \
	Library/binomial.ml \
	Multivariate/realanalysis.ml \
	Multivariate/geom.ml \
	Multivariate/cross.ml \
	Multivariate/flyspeck.ml

EXTRA_HOL_SRC0=\
	Library/rstc.ml \
	Rqe/num_calc_simp.ml

FLYSPECK_SRC0=\
	general/state_manager.hl \
	general/prove_by_refinement.hl \
	build/native_strictbuild.mli \
	build/native_strictbuild.hl \
	general/hol_library.hl \
	general/print_types.hl \
	general/flyspeck_lib.hl \
	general/sphere.hl \
	general/hales_tactic.hl \
	general/truong_tactic.hl \
	leg/leg_basics.hl \
	leg/geomdetail.hl \
	leg/aff_sgn_tac.hl \
	leg/affprops.hl \
	leg/cayleyr.hl \
	leg/mur.hl \
	leg/enclosed.hl \
	leg/collect_geom.hl \
	leg/collect_geom2.hl \
	jordan/refinement.hl \
	jordan/lib_ext.hl \
	jordan/hash_term.hl \
	jordan/parse_ext_override_interface.hl \
	jordan/goal_printer.hl \
	jordan/real_ext.hl \
	jordan/tactics_jordan.hl \
	jordan/num_ext_nabs.hl \
	jordan/taylor_atn.hl \
	jordan/float.hl \
	jordan/flyspeck_constants.hl \
	jordan/misc_defs_and_lemmas.hl \
	general/gen_tactics.hl \
	general/vukhacky_tactics.hl \
	trigonometry/trigonometry1.hl \
	trigonometry/trigonometry2.hl \
	trigonometry/delta_x.hl \
	trigonometry/euler_complement.hl \
	trigonometry/euler_multivariate.hl \
	trigonometry/euler_main_theorem.hl \
	trigonometry/trigonometry.hl \
	trigonometry/hvihvec.hl \
	nonlinear/calc_derivative.hl \
	nonlinear/ineqdata3q1h.hl \
	nonlinear/types.hl \
	nonlinear/nonlin_def.hl \
	nonlinear/ineq.hl \
	nonlinear/main_estimate_ineq.hl \
	nonlinear/nonlinear_lemma.hl \
	nonlinear/functional_equation.hl \
	nonlinear/optimize.hl \
	nonlinear/function_list.hl \
	nonlinear/merge_ineq.hl \
	volume/vol1.hl \
	hypermap/hypermap.hl \
	fan/fan_defs.hl \
	fan/fan.hl \
	fan/gmlwkpk.hl \
	fan/fan_topology.hl \
	fan/fan_misc.hl \
	fan/planarity.hl \
	fan/hypermap_and_fan.hl \
	fan/conforming.hl \
	fan/polyhedron.hl \
	packing/pack1.hl \
	packing/pack2.hl \
	packing/pack_defs.hl \
	packing/pack_concl.hl \
	packing/packing3.hl \
	packing/rogers.hl \
	packing/tarjjuw.hl \
	packing/marchal_cells.hl \
	packing/upfzbzm_support_lemmas.hl \
	packing/emnwuus.hl \
	packing/marchal_cells_2_new.hl \
	packing/sltstlo.hl \
	packing/lepjbdj.hl \
	packing/urrphbz1.hl \
	packing/urrphbz2.hl \
	packing/hdtfnfz.hl \
	packing/urrphbz3.hl \
	packing/rvfxzbu.hl \
	local/wrgcvdr_cizmrrh.hl \
	local/lvducxu.hl \
	local/ldurdpn.hl \
	local/local_lemmas.hl \
	tame/tame_inequalities.hl \
	packing/ynhyjit.hl \
	packing/njiutiu.hl \
	packing/tezffsk.hl \
	packing/qzksykg.hl \
	packing/ddzuphj.hl \
	packing/ajripqn.hl \
	packing/qzyzmjc.hl \
	packing/marchal_cells_3.hl \
	packing/grutoti.hl \
	packing/kizhltl.hl \
	packing/bump.hl \
	packing/sum_gammax_lmfun_estimate.hl \
	packing/upfzbzm.hl \
	packing/rdwkarc.hl \
	local/local_lemmas1.hl \
	local/nkezbfc_local.hl \
	tame/arc_properties.hl \
	fan/cfyxfty.hl \
	packing/ysskqoy.hl  \
	packing/counting_spheres.hl \
	packing/reuhady.hl \
	packing/tskajxy_lemmas.hl \
	packing/tskajxy_034.hl \
	packing/oxl_def.hl \
	packing/oxl_2012.hl \
	packing/leaf_cell.hl \
	packing/tskajxy.hl \
	packing/oxlzlez.hl \
	local/dih2k_hypermap.hl \
	local/wjscpro.hl \
	local/tecoxbm.hl \
	local/vpwshto.hl \
	local/lfjcixp.hl \
	local/localization.hl \
	local/polar_fan.hl  \
	local/hdplygy.hl \
	local/gbycpxs.hl \
	local/mtuwlun.hl \
	local/pcrttid.hl \
	local/xivphks.hl \
	tame/tame_defs.hl \
	../jHOLLight/caml/ssreflect.hl \
	../jHOLLight/caml/sections.hl \
	../jHOLLight/Examples/ssrfun.hl \
	../jHOLLight/Examples/ssrbool.hl \
	../jHOLLight/Examples/ssrnat.hl \
	fan/hypermap_iso.hl \
	tame/ckqowsa_3_points.hl \
	tame/ckqowsa_4_points.hl \
	tame/ckqowsa.hl \
	tame/tame_general.hl \
	tame/jgtdebu.hl \
	tame/tame_opposite.hl \
	tame/fatugpd.hl \
	tame/crttxat_tame.hl \
	tame/hrxefdm_tame.hl \
	../jHOLLight/Examples/seq.hl \
	tame/ssreflect/seq2.hl \
	tame/ssreflect/seq_sort.hl \
	tame/ssreflect/fnjlbxs.hl \
	../formal_lp/hypermap/ssreflect/add_triangle.hl \
	tame/ssreflect/tame_lemmas.hl \
	tame/cdtetat_tame.hl \
	local/appendix.hl \
	local/terminal.hl \
	local/pent_hex.hl \
	local/lp_details.hl \
	local/zithlqn.hl \
	local/xwitccn.hl \
	local/ayqjtmd.hl \
	local/jkqewgv.hl \
	local/uxckfpe.hl \
	local/sgtrnaf.hl \
	local/qknvmlb.hl \
	local/yxionxl.hl \
	local/hxhytij.hl \
	local/uaghhbm.hl \
	local/lkgrqui.hl \
	local/deformation.hl \
	local/odxlstc.hl \
	local/lunar_deform.hl \
	local/ocbicby.hl \
	local/yxionxl2.hl \
	local/eyypqdw.hl \
	local/imjxphr.hl \
	local/zlzthic.hl \
	local/pqcsxwg.hl \
	local/nuxcoea.hl \
	local/fektyiy.hl \
	local/aursipd.hl \
	local/ppbtydq.hl \
	local/axjrpnc.hl \
	local/cuxvzoz.hl \
	local/rrcwnsj.hl \
	local/jcyfmrp.hl \
	local/tfitskc.hl \
	local/cqaoqlr.hl \
	local/jlxfdmj.hl \
	local/yrtafyh.hl \
	local/wkeidft.hl \
	local/hexagons.hl \
	local/iunbuig.hl \
	local/otmtotj.hl \
	local/hijqaha.hl \
	local/cnicgsf.hl \
	local/bkossge.hl \
	local/jotswix.hl \
	local/ardbzye.hl \
	local/aueaheh.hl \
	local/vasyyau.hl \
	local/miqmcsn.hl \
	local/jejtvgb.hl \
	../formal_lp/hypermap/ssreflect/list_hypermap.hl \
	../formal_lp/hypermap/ineqs/lp_gen_theory.hl \
	../formal_lp/hypermap/ssreflect/list_hypermap_iso.hl \
	../formal_lp/hypermap/computations/more_list_hypermap.hl \
	local/rnsyjxm.hl \
	tame/tame_defs2.hl \
	tame/tame_list.hl \
	tame/import_tame_classification.hl \
	tame/more_tame_concl.hl \
	tame/oxaxucs.hl \
	tame/asfutbf.hl \
	tame/elllnyz.hl \
	tame/wmlnymd.hl \
	tame/dpzgbyf.hl \
	tame/auqtzyz.hl \
	tame/auqtzyz_list.hl \
	tame/rxokskc.hl \
	tame/dangeyj.hl \
	tame/jcajydu.hl \
	tame/pwssrat.hl \
	tame/ohcgkfu.hl \
	tame/pplhulj.hl \
	tame/ncvibwu.hl \
	tame/qcdvkea.hl \
	tame/pbflhet.hl \
	tame/pnxvwfs.hl \
	tame/diowaas.hl \
	tame/ryiuuvk.hl \
	tame/kbwpbhq.hl \
	tame/meeixjo.hl \
	tame/obdatyb.hl \
	tame/lebhirj.hl \
	tame/hojodcm.hl \
	tame/aq1.hl \
	tame/aq23.hl \
	tame/aq4.hl \
	tame/aq56.hl \
	tame/aq7.hl \
	tame/aq8.hl \
	tame/aq9.hl \
	tame/aq10.hl \
	tame/aq11.hl \
	tame/aq12.hl \
	tame/aq13.hl \
	tame/reduction1.hl \
	tame/reduction2.hl \
	tame/more_lemma1.hl \
	tame/reduction3.hl \
	tame/more_lemma2.hl \
	tame/reduction4.hl \
	tame/betwn_corek_z_x.hl \
	tame/betwn_core0_z_y.hl \
	tame/reduction5.hl \
	../formal_lp/hypermap/ineqs/lp_ineqs_defs.hl \
	../formal_lp/ineqs/constants_approx.hl \
	../formal_lp/hypermap/ineqs/lp_ineqs_proofs.hl \
	../formal_lp/hypermap/ineqs/lp_main_estimate.hl \
	../formal_lp/hypermap/ineqs/lp_ineqs_quads.hl \
	tame/ssreflect/kcblrqc.hl \
	tame/ssreflect/mqmsmab.hl \
	packing/flyspeck_devol.hl \
	general/kepler_spec.hl \
	general/the_main_statement.hl \
	general/audit_formal_proof.hl

#	general/the_kepler_conjecture.hl







HOL_SRC=$(addprefix $(HOL_NATIVE_DIR)/,$(HOL_SRC0))
EXTRA_HOL_SRC=$(addprefix $(HOL_NATIVE_DIR)/,$(EXTRA_HOL_SRC0))
FLYSPECK_SRC=$(addprefix $(FORMALIZATION_DIR)/,$(FLYSPECK_SRC0))

HOL_OBJ=$(HOL_SRC:.ml=.cmx)
EXTRA_HOL_OBJ=$(EXTRA_HOL_SRC:.ml=.cmx)

FLYSPECK_OBJ0=$(FLYSPECK_SRC:.hl=.cmx)
FLYSPECK_OBJ=$(FLYSPECK_OBJ0:.mli=.cmi)
BUILD_FLYSPECK_OBJ=$(filter-out %.cmi, $(FLYSPECK_OBJ))

%.cmi : %.mli
	$(OPT_MLI) $(OPTIONS) $(WARNINGS) $(INCLUDE) $^

%.cmx : %.hl
	$(OPT_HL) $(OPTIONS) $(WARNINGS) $(INCLUDE) -impl $^

%.cmx : %.ml
	$(OPT_ML) $(OPTIONS) $(WARNINGS) $(INCLUDE) $^

.PHONY: clean all flyspeck-compile

all: flyspeck

flyspeck-compile: $(EXTRA_HOL_OBJ) $(FLYSPECK_OBJ)
	@echo "Flyspeck compiled"

flyspeck: flyspeck-compile
	ocamlopt -linkall -o flyspeck unix.cmxa nums.cmxa str.cmxa $(OPTIONS) \
		 $(INCLUDE) $(HOL_OBJ) $(EXTRA_HOL_OBJ) $(BUILD_FLYSPECK_OBJ)

clean:
	find $(FORMALIZATION_DIR) -name "*.cmi" -delete \
		-o -name "*.cmx" -delete \
		-o -name "*.o" -delete