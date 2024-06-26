package edu.pitt.math.jhol;

import java.lang.reflect.Array;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

public class Database {
	public static final String[] HOL_COMMANDS_STRING = {"++",
			 "||",
			 ">>",
			 "|=>",
			 "--",
			 "|->",
			 "a",
			 "ABBREV_TAC",
			 "ABS",
			 "ABS_CONV",
			 "ABS_TAC",
			 "AC",
			 "ACCEPT_TAC",
			 "aconv",
			 "ADD_ASSUM",
			 "allpairs",
			 "ALL_CONV",
			 "ALL_TAC",
			 "ALL_THEN",
			 "alpha",
			 "ALPHA_CONV",
			 "ALPHA",
			 "ANTE_RES_THEN",
			 "ANTS_TAC",
			 "apply",
			 "applyd",
			 "apply_prover",
			 "AP_TERM",
			 "AP_TERM_TAC",
			 "AP_THM",
			 "AP_THM_TAC",
			 "ARITH_RULE",
			 "ARITH_TAC",
			 "ASM",
			 "ASM_ARITH_TAC",
			 "ASM_CASES_TAC",
			 "ASM_FOL_TAC",
			 "ASM_INT_ARITH_TAC",
			 "ASM_MESON_TAC",
			 "ASM_REAL_ARITH_TAC",
			 "ASM_REWRITE_RULE",
			 "ASM_REWRITE_TAC",
			 "ASM_SIMP_TAC",
			 "assoc",
			 "assocd",
			 "ASSOC_CONV",
			 "ASSUME",
			 "ASSUME_TAC",
			 "ASSUM_LIST",
			 "atleast",
			 "aty",
			 "augment",
			 "AUGMENT_SIMPSET",
			 "axioms",
			 "b",
			 "basic_congs",
			 "basic_convs",
			 "basic_net",
			 "basic_prover",
			 "basic_rectype_net",
			 "basic_rewrites",
			 "basic_ss",
			 "BETA",
			 "BETAS_CONV",
			 "BETA_CONV",
			 "BETA_RULE",
			 "BETA_TAC",
			 "binders",
			 "BINDER_CONV",
			 "binops",
			 "BINOP_CONV",
			 "BINOP_TAC",
			 "bndvar",
			 "body",
			 "BOOL_CASES_TAC",
			 "bool_ty",
			 "bty",
			 "butlast",
			 "by",
			 "C",
			 "CACHE_CONV",
			 "can",
			 "cases",
			 "CCONTR",
			 "CHANGED_CONV",
			 "CHANGED_TAC",
			 "CHEAT_TAC",
			 "check",
			 "checkpoint",
			 "choose",
			 "CHOOSE_TAC",
			 "CHOOSE_THEN",
			 "CHOOSE",
			 "chop_list",
			 "CNF_CONV",
			 "COMB2_CONV",
			 "combine",
			 "COMB_CONV",
			 "comment_token",
			 "compose_insts",
			 "concl",
			 "CONDS_CELIM_CONV",
			 "CONDS_ELIM_CONV",
			 "COND_CASES_TAC",
			 "COND_ELIM_CONV",
			 "CONJ",
			 "CONJUNCT1",
			 "CONJUNCT2",
			 "conjuncts",
			 "CONJUNCTS_THEN",
			 "CONJUNCTS_THEN2",
			 "CONJUNCTS",
			 "CONJ_ACI_RULE",
			 "CONJ_CANON_CONV",
			 "CONJ_PAIR",
			 "CONJ_TAC",
			 "constants",
			 "CONTR",
			 "CONTRAPOS_CONV",
			 "CONTR_TAC",
			 "CONV_RULE",
			 "CONV_TAC",
			 "current_goalstack",
			 "curry",
			 "decreasing",
			 "DEDUCT_ANTISYM_RULE",
			 "deep_alpha",
			 "define",
			 "defined",
			 "define_finite_type",
			 "define_quotient_type",
			 "define_type",
			 "define_type_raw",
			 "definitions",
			 "delete_parser",
			 "delete_user_printer",
			 "denominator",
			 "DENUMERAL",
			 "DEPTH_BINOP_CONV",
			 "DEPTH_CONV",
			 "DEPTH_SQCONV",
			 "derive_nonschematic_inductive_relations",
			 "derive_strong_induction",
			 "dest_abs",
			 "dest_binary",
			 "dest_binder",
			 "dest_binop",
			 "dest_comb",
			 "dest_cond",
			 "dest_conj",
			 "dest_cons",
			 "dest_const",
			 "dest_disj",
			 "dest_eq",
			 "dest_exists",
			 "dest_forall",
			 "dest_fun_ty",
			 "dest_gabs",
			 "dest_iff",
			 "dest_imp",
			 "dest_intconst",
			 "dest_let",
			 "dest_list",
			 "dest_neg",
			 "dest_numeral",
			 "dest_pair",
			 "dest_realintconst",
			 "dest_select",
			 "dest_setenum",
			 "dest_small_numeral",
			 "dest_thm",
			 "dest_type",
			 "dest_uexists",
			 "dest_var",
			 "dest_vartype",
			 "DISCH",
			 "DISCH_ALL",
			 "DISCH_TAC",
			 "DISCH_THEN",
			 "DISJ1",
			 "DISJ1_TAC",
			 "DISJ2",
			 "DISJ2_TAC",
			 "disjuncts",
			 "DISJ_ACI_RULE",
			 "DISJ_CANON_CONV",
			 "DISJ_CASES",
			 "DISJ_CASES_TAC",
			 "DISJ_CASES_THEN",
			 "DISJ_CASES_THEN2",
			 "distinctness",
			 "distinctness_store",
			 "DNF_CONV",
			 "dom",
			 "do_list",
			 "dpty",
			 "e",
			 "el",
			 "elistof",
			 "empty_net",
			 "empty_ss",
			 "end_itlist",
			 "enter",
			 "EQF_ELIM",
			 "EQF_INTRO",
			 "EQT_ELIM",
			 "EQT_INTRO",
			 "equals_goal",
			 "equals_thm",
			 "EQ_IMP_RULE",
			 "EQ_MP",
			 "EQ_TAC",
			 "ETA_CONV",
			 "EVERY",
			 "EVERY_ASSUM",
			 "EVERY_CONV",
			 "EVERY_TCL",
			 "exactly",
			 "EXISTENCE",
			 "exists",
			 "EXISTS_EQUATION",
			 "EXISTS_TAC",
			 "EXISTS",
			 "EXPAND_CASES_CONV",
			 "EXPAND_TAC",
			 "explode",
			 "extend_basic_congs",
			 "extend_basic_convs",
			 "extend_basic_rewrites",
			 "extend_rectype_net",
			 "fail",
			 "FAIL_TAC",
			 "file_of_string",
			 "file_on_path",
			 "filter",
			 "find",
			 "FIND_ASSUM",
			 "find_path",
			 "find_term",
			 "find_terms",
			 "finished",
			 "FIRST",
			 "FIRST_ASSUM",
			 "FIRST_CONV",
			 "FIRST_TCL",
			 "FIRST_X_ASSUM",
			 "fix",
			 "flat",
			 "flush_goalstack",
			 "foldl",
			 "foldr",
			 "follow_path",
			 "forall",
			 "forall2",
			 "FORALL_UNWIND_CONV",
			 "frees",
			 "freesin",
			 "freesl",
			 "FREEZE_THEN",
			 "free_in",
			 "funpow",
			 "F_F",
			 "f_f_",
			 "g",
			 "GABS_CONV",
			 "gcd",
			 "gcd_num",
			 "GEN",
			 "GENERAL_REWRITE_CONV",
			 "GENL",
			 "genvar",
			 "GEN_ALL",
			 "GEN_ALPHA_CONV",
			 "GEN_BETA_CONV",
			 "GEN_MESON_TAC",
			 "GEN_NNF_CONV",
			 "GEN_PART_MATCH",
			 "GEN_REAL_ARITH",
			 "GEN_REWRITE_CONV",
			 "GEN_REWRITE_RULE",
			 "GEN_REWRITE_TAC",
			 "GEN_SIMPLIFY_CONV",
			 "GEN_TAC",
			 "get_const_type",
			 "get_infix_status",
			 "get_type_arity",
			 "graph",
			 "GSYM",
			 "HAS_SIZE_CONV",
			 "hd",
			 "help",
			 "help_path",
			 "hide_constant",
			 "HIGHER_REWRITE_CONV",
			 "hol_dir",
			 "hol_expand_directory",
			 "hol_version",
			 "hyp",
			 "I",
			 "ideal_cofactors",
			 "ignore_constant_varstruct",
			 "implode",
			 "IMP_ANTISYM_RULE",
			 "IMP_RES_THEN",
			 "IMP_REWR_CONV",
			 "IMP_TRANS",
			 "increasing",
			 "index",
			 "inductive_type_store",
			 "INDUCT_TAC",
			 "infixes",
			 "injectivity",
			 "injectivity_store",
			 "insert",
			 "insert'",
			 "inst",
			 "installed_parsers",
			 "install_parser",
			 "install_user_printer",
			 "instantiate",
			 "INSTANTIATE_ALL",
			 "instantiate_casewise_recursion",
			 "INSTANTIATE",
			 "inst_goal",
			 "INST_TYPE",
			 "INST",
			 "INTEGER_RULE",
			 "INTEGER_TAC",
			 "intersect",
			 "INT_ABS_CONV",
			 "INT_ADD_CONV",
			 "INT_ARITH",
			 "INT_ARITH_TAC",
			 "INT_EQ_CONV",
			 "INT_GE_CONV",
			 "INT_GT_CONV",
			 "int_ideal_cofactors",
			 "INT_LE_CONV",
			 "INT_LT_CONV",
			 "INT_MAX_CONV",
			 "INT_MIN_CONV",
			 "INT_MUL_CONV",
			 "INT_NEG_CONV",
			 "INT_OF_REAL_THM",
			 "INT_POLY_CONV",
			 "INT_POW_CONV",
			 "INT_REDUCE_CONV",
			 "INT_RED_CONV",
			 "INT_RING",
			 "INT_SUB_CONV",
			 "isalnum",
			 "isalpha",
			 "isbra",
			 "isnum",
			 "ISPEC",
			 "ISPECL",
			 "issep",
			 "isspace",
			 "issymb",
			 "is_abs",
			 "is_binary",
			 "is_binder",
			 "is_binop",
			 "is_comb",
			 "is_cond",
			 "is_conj",
			 "is_cons",
			 "is_const",
			 "is_disj",
			 "is_eq",
			 "is_exists",
			 "is_forall",
			 "is_gabs",
			 "is_hidden",
			 "is_iff",
			 "is_imp",
			 "is_intconst",
			 "is_let",
			 "is_list",
			 "is_neg",
			 "is_numeral",
			 "is_pair",
			 "is_prefix",
			 "is_ratconst",
			 "is_realintconst",
			 "is_reserved_word",
			 "is_select",
			 "is_setenum",
			 "is_type",
			 "is_uexists",
			 "is_undefined",
			 "is_var",
			 "is_vartype",
			 "it",
			 "ITAUT",
			 "ITAUT_TAC",
			 "itlist",
			 "itlist2",
			 "K",
			 "LABEL_TAC",
			 "LAMBDA_ELIM_CONV",
			 "LAND_CONV",
			 "last",
			 "lcm_num",
			 "leftbin",
			 "length",
			 "let_CONV",
			 "LET_TAC",
			 "lex",
			 "LE_IMP",
			 "lhand",
			 "lhs",
			 "lift_function",
			 "lift_theorem",
			 "listof",
			 "LIST_CONV",
			 "LIST_INDUCT_TAC",
			 "list_mk_abs",
			 "list_mk_binop",
			 "list_mk_comb",
			 "list_mk_conj",
			 "list_mk_disj",
			 "list_mk_exists",
			 "list_mk_forall",
			 "list_mk_gabs",
			 "list_mk_icomb",
			 "loaded_files",
			 "loads",
			 "loadt",
			 "load_on_path",
			 "load_path",
			 "lookup",
			 "make_args",
			 "make_overloadable",
			 "many",
			 "map",
			 "map2",
			 "mapf",
			 "mapfilter",
			 "MAP_EVERY",
			 "MAP_FIRST",
			 "MATCH_ACCEPT_TAC",
			 "MATCH_CONV",
			 "MATCH_MP",
			 "MATCH_MP_TAC",
			 "mem",
			 "mem'",
			 "merge",
			 "mergesort",
			 "merge_nets",
			 "MESON",
			 "meson_brand",
			 "meson_chatty",
			 "meson_dcutin",
			 "meson_depth",
			 "meson_prefine",
			 "meson_skew",
			 "meson_split_limit",
			 "MESON_TAC",
			 "META_EXISTS_TAC",
			 "META_SPEC_TAC",
			 "mk_abs",
			 "mk_binary",
			 "mk_binder",
			 "mk_binop",
			 "MK_BINOP",
			 "mk_comb",
			 "MK_COMB_TAC",
			 "MK_COMB",
			 "mk_cond",
			 "mk_conj",
			 "MK_CONJ",
			 "mk_cons",
			 "mk_const",
			 "mk_disj",
			 "MK_DISJ",
			 "mk_eq",
			 "mk_exists",
			 "MK_EXISTS",
			 "mk_flist",
			 "mk_forall",
			 "MK_FORALL",
			 "mk_fset",
			 "mk_fthm",
			 "mk_fun_ty",
			 "mk_gabs",
			 "mk_goalstate",
			 "mk_icomb",
			 "mk_iff",
			 "mk_imp",
			 "mk_intconst",
			 "mk_let",
			 "mk_list",
			 "mk_mconst",
			 "mk_neg",
			 "mk_numeral",
			 "mk_pair",
			 "mk_primed_var",
			 "mk_prover",
			 "mk_realintconst",
			 "mk_rewrites",
			 "mk_select",
			 "mk_setenum",
			 "mk_small_numeral",
			 "mk_thm",
			 "mk_type",
			 "mk_uexists",
			 "mk_var",
			 "mk_vartype",
			 "monotonicity_theorems",
			 "MONO_TAC",
			 "MP",
			 "MP_CONV",
			 "MP_TAC",
			 "name",
			 "name_of",
			 "needs",
			 "net_of_cong",
			 "net_of_conv",
			 "net_of_thm",
			 "new_axiom",
			 "new_basic_definition",
			 "new_basic_type_definition",
			 "new_constant",
			 "new_definition",
			 "new_inductive_definition",
			 "new_recursive_definition",
			 "new_specification",
			 "new_type",
			 "new_type_abbrev",
			 "new_type_definition",
			 "NNFC_CONV",
			 "NNF_CONV",
			 "nothing",
			 "NOT_ELIM",
			 "NOT_INTRO",
			 "NO_CONV",
			 "NO_TAC",
			 "NO_THEN",
			 "nsplit",
			 "null_inst",
			 "null_meta",
			 "NUMBER_RULE",
			 "NUMBER_TAC",
			 "numdom",
			 "numerator",
			 "NUMSEG_CONV",
			 "num_0",
			 "num_1",
			 "num_10",
			 "num_2",
			 "NUM_ADD_CONV",
			 "NUM_CANCEL_CONV",
			 "num_CONV",
			 "NUM_DIV_CONV",
			 "NUM_EQ_CONV",
			 "NUM_EVEN_CONV",
			 "NUM_EXP_CONV",
			 "NUM_FACT_CONV",
			 "NUM_GE_CONV",
			 "NUM_GT_CONV",
			 "NUM_LE_CONV",
			 "NUM_LT_CONV",
			 "NUM_MAX_CONV",
			 "NUM_MIN_CONV",
			 "NUM_MOD_CONV",
			 "NUM_MULT_CONV",
			 "NUM_NORMALIZE_CONV",
			 "NUM_ODD_CONV",
			 "num_of_string",
			 "NUM_PRE_CONV",
			 "NUM_REDUCE_CONV",
			 "NUM_REDUCE_TAC",
			 "NUM_RED_CONV",
			 "NUM_REL_CONV",
			 "NUM_RING",
			 "NUM_SIMPLIFY_CONV",
			 "NUM_SUB_CONV",
			 "NUM_SUC_CONV",
			 "NUM_TO_INT_CONV",
			 "o",
			 "occurs_in",
			 "omit",
			 "ONCE_ASM_REWRITE_RULE",
			 "ONCE_ASM_REWRITE_TAC",
			 "ONCE_ASM_SIMP_TAC",
			 "ONCE_DEPTH_CONV",
			 "ONCE_DEPTH_SQCONV",
			 "ONCE_REWRITE_CONV",
			 "ONCE_REWRITE_RULE",
			 "ONCE_REWRITE_TAC",
			 "ONCE_SIMPLIFY_CONV",
			 "ONCE_SIMP_CONV",
			 "ONCE_SIMP_RULE",
			 "ONCE_SIMP_TAC",
			 "ORDERED_IMP_REWR_CONV",
			 "ORDERED_REWR_CONV",
			 "ORELSE",
			 "ORELSEC",
			 "orelsec_",
			 "orelse_",
			 "ORELSE_TCL",
			 "orelse_tcl_",
			 "overload_interface",
			 "override_interface",
			 "p",
			 "parses_as_binder",
			 "parse_as_binder",
			 "parse_as_infix",
			 "parse_as_prefix",
			 "parse_inductive_type_specification",
			 "parse_preterm",
			 "parse_pretype",
			 "parse_term",
			 "parse_type",
			 "partition",
			 "PART_MATCH",
			 "PATH_CONV",
			 "PAT_CONV",
			 "PINST",
			 "POP_ASSUM",
			 "POP_ASSUM_LIST",
			 "possibly",
			 "pow10",
			 "pow2",
			 "pp_print_qterm",
			 "pp_print_qtype",
			 "pp_print_term",
			 "pp_print_thm",
			 "pp_print_type",
			 "prebroken_binops",
			 "prefixes",
			 "PRENEX_CONV",
			 "PRESIMP_CONV",
			 "preterm_of_term",
			 "pretype_of_type",
			 "print_all_thm",
			 "print_fpf",
			 "print_goal",
			 "print_goalstack",
			 "print_num",
			 "print_qterm",
			 "print_qtype",
			 "print_term",
			 "print_thm",
			 "print_to_string",
			 "print_type",
			 "print_unambiguous_comprehensions",
			 "prioritize_int",
			 "prioritize_num",
			 "prioritize_overload",
			 "prioritize_real",
			 "PROP_ATOM_CONV",
			 "prove",
			 "prove_cases_thm",
			 "prove_constructors_distinct",
			 "prove_constructors_injective",
			 "prove_general_recursive_function_exists",
			 "PROVE_HYP",
			 "prove_inductive_relations_exist",
			 "prove_monotonicity_hyps",
			 "prove_recursive_functions_exist",
			 "PURE_ASM_REWRITE_RULE",
			 "PURE_ASM_REWRITE_TAC",
			 "PURE_ASM_SIMP_TAC",
			 "PURE_ONCE_ASM_REWRITE_RULE",
			 "PURE_ONCE_ASM_REWRITE_TAC",
			 "PURE_ONCE_REWRITE_CONV",
			 "PURE_ONCE_REWRITE_RULE",
			 "PURE_ONCE_REWRITE_TAC",
			 "pure_prove_recursive_function_exists",
			 "PURE_REWRITE_CONV",
			 "PURE_REWRITE_RULE",
			 "PURE_REWRITE_TAC",
			 "PURE_SIMP_CONV",
			 "PURE_SIMP_RULE",
			 "PURE_SIMP_TAC",
			 "qmap",
			 "quotexpander",
			 "r",
			 "ran",
			 "rand",
			 "RAND_CONV",
			 "rator",
			 "RATOR_CONV",
			 "rat_of_term",
			 "REAL_ARITH",
			 "REAL_ARITH_TAC",
			 "REAL_FIELD",
			 "real_ideal_cofactors",
			 "REAL_IDEAL_CONV",
			 "REAL_INT_ABS_CONV",
			 "REAL_INT_ADD_CONV",
			 "REAL_INT_EQ_CONV",
			 "REAL_INT_GE_CONV",
			 "REAL_INT_GT_CONV",
			 "REAL_INT_LE_CONV",
			 "REAL_INT_LT_CONV",
			 "REAL_INT_MUL_CONV",
			 "REAL_INT_NEG_CONV",
			 "REAL_INT_POW_CONV",
			 "REAL_INT_RAT_CONV",
			 "REAL_INT_REDUCE_CONV",
			 "REAL_INT_RED_CONV",
			 "REAL_INT_SUB_CONV",
			 "REAL_LET_IMP",
			 "REAL_LE_IMP",
			 "REAL_LINEAR_PROVER",
			 "REAL_POLY_ADD_CONV",
			 "REAL_POLY_CONV",
			 "REAL_POLY_MUL_CONV",
			 "REAL_POLY_NEG_CONV",
			 "REAL_POLY_POW_CONV",
			 "REAL_POLY_SUB_CONV",
			 "REAL_RAT_ABS_CONV",
			 "REAL_RAT_ADD_CONV",
			 "REAL_RAT_DIV_CONV",
			 "REAL_RAT_EQ_CONV",
			 "REAL_RAT_GE_CONV",
			 "REAL_RAT_GT_CONV",
			 "REAL_RAT_INV_CONV",
			 "REAL_RAT_LE_CONV",
			 "REAL_RAT_LT_CONV",
			 "REAL_RAT_MAX_CONV",
			 "REAL_RAT_MIN_CONV",
			 "REAL_RAT_MUL_CONV",
			 "REAL_RAT_NEG_CONV",
			 "REAL_RAT_POW_CONV",
			 "REAL_RAT_REDUCE_CONV",
			 "REAL_RAT_RED_CONV",
			 "REAL_RAT_SUB_CONV",
			 "REAL_RING",
			 "RECALL_ACCEPT_TAC",
			 "REDEPTH_CONV",
			 "REDEPTH_SQCONV",
			 "reduce_interface",
			 "refine",
			 "REFL",
			 "REFL_TAC",
			 "REFUTE_THEN",
			 "remark",
			 "remove",
			 "remove_interface",
			 "REMOVE_THEN",
			 "remove_type_abbrev",
			 "repeat",
			 "REPEATC",
			 "REPEAT_GTCL",
			 "REPEAT_TCL",
			 "REPEAT",
			 "replicate",
			 "REPLICATE_TAC",
			 "report",
			 "report_timing",
			 "reserved_words",
			 "reserve_words",
			 "retypecheck",
			 "rev",
			 "reverse_interface_mapping",
			 "rev_assoc",
			 "rev_assocd",
			 "rev_itlist",
			 "rev_itlist2",
			 "rev_splitlist",
			 "REWRITES_CONV",
			 "REWRITE_CONV",
			 "REWRITE_RULE",
			 "REWRITE_TAC",
			 "REWR_CONV",
			 "rhs",
			 "rightbin",
			 "RIGHT_BETAS",
			 "RING",
			 "RING_AND_IDEAL_CONV",
			 "rotate",
			 "RULE_ASSUM_TAC",
			 "search",
			 "SELECT_CONV",
			 "SELECT_ELIM_TAC",
			 "SELECT_RULE",
			 "self_destruct",
			 "SEMIRING_NORMALIZERS_CONV",
			 "setify",
			 "set_basic_congs",
			 "set_basic_convs",
			 "set_basic_rewrites",
			 "set_eq",
			 "set_goal",
			 "SET_RULE",
			 "SET_TAC",
			 "shareout",
			 "SIMPLE_CHOOSE",
			 "SIMPLE_DISJ_CASES",
			 "SIMPLE_EXISTS",
			 "SIMPLIFY_CONV",
			 "SIMP_CONV",
			 "SIMP_RULE",
			 "SIMP_TAC",
			 "SKOLEM_CONV",
			 "some",
			 "sort",
			 "SPEC",
			 "SPECL",
			 "SPEC_ALL",
			 "SPEC_TAC",
			 "SPEC_VAR",
			 "splitlist",
			 "ss_of_congs",
			 "ss_of_conv",
			 "ss_of_maker",
			 "ss_of_prover",
			 "ss_of_provers",
			 "ss_of_thms",
			 "startup_banner",
			 "strings_of_file",
			 "string_of_file",
			 "string_of_term",
			 "string_of_thm",
			 "string_of_type",
			 "striplist",
			 "strip_abs",
			 "STRIP_ASSUME_TAC",
			 "strip_comb",
			 "strip_exists",
			 "strip_forall",
			 "strip_gabs",
			 "STRIP_GOAL_THEN",
			 "strip_ncomb",
			 "STRIP_TAC",
			 "STRIP_THM_THEN",
			 "STRUCT_CASES_TAC",
			 "SUBGOAL_TAC",
			 "SUBGOAL_THEN",
			 "SUBS",
			 "subset",
			 "subst",
			 "SUBST1_TAC",
			 "SUBST_ALL_TAC",
			 "SUBST_VAR_TAC",
			 "SUBS_CONV",
			 "subtract",
			 "subtract'",
			 "SUB_CONV",
			 "SYM",
			 "SYM_CONV",
			 "TAC_PROOF",
			 "TAUT",
			 "temp_path",
			 "term_match",
			 "term_of_preterm",
			 "term_of_rat",
			 "term_order",
			 "term_unify",
			 "term_union",
			 "THEN",
			 "THENC",
			 "thenc_",
			 "THENL",
			 "thenl_",
			 "then_",
			 "THEN_TCL",
			 "then_tcl_",
			 "theorems",
			 "the_definitions",
			 "the_inductive_definitions",
			 "the_inductive_types",
			 "the_interface",
			 "the_overload_skeletons",
			 "the_specifications",
			 "the_type_definitions",
			 "thm_frees",
			 "time",
			 "tl",
			 "TOP_DEPTH_CONV",
			 "TOP_DEPTH_SQCONV",
			 "top_goal",
			 "top_realgoal",
			 "TOP_SWEEP_CONV",
			 "TOP_SWEEP_SQCONV",
			 "top_thm",
			 "TRANS",
			 "TRY",
			 "tryapplyd",
			 "tryfind",
			 "TRY_CONV",
			 "try_user_parser",
			 "try_user_printer",
			 "types",
			 "type_abbrevs",
			 "type_invention_warning",
			 "type_match",
			 "type_of",
			 "type_of_pretype",
			 "type_subst",
			 "type_vars_in_term",
			 "typify_universal_set",
			 "tysubst",
			 "tyvars",
			 "uncurry",
			 "undefine",
			 "undefined",
			 "UNDISCH",
			 "UNDISCH_ALL",
			 "UNDISCH_TAC",
			 "UNDISCH_THEN",
			 "unhide_constant",
			 "UNIFY_ACCEPT_TAC",
			 "union",
			 "unions",
			 "unions'",
			 "union'",
			 "uniq",
			 "unparse_as_binder",
			 "unparse_as_infix",
			 "unparse_as_prefix",
			 "unreserve_words",
			 "unspaced_binops",
			 "UNWIND_CONV",
			 "unzip",
			 "use_file",
			 "USE_THEN",
			 "VALID",
			 "variables",
			 "variant",
			 "variants",
			 "verbose",
			 "vfree_in",
			 "vsubst",
			 "W",
			 "warn",
			 "WEAK_CNF_CONV",
			 "WEAK_DNF_CONV",
			 "WF_INDUCT_TAC",
			 "X_CHOOSE_TAC",
			 "X_CHOOSE_THEN",
			 "X_GEN_TAC",
			 "X_META_EXISTS_TAC",
			 "zip"};

	
	public static final List<String> HOL_COMMANDS;
	public static final Set<String> basicLogicTheorems;
	public static final Set<String> constructTheorems; 
	
	public static final Set<String> pairTheorems ;
	public static final Set<String> wellfoundednessTheorems ;
	public static final Set<String> naturalNumberTheorems ;
	public static final Set<String> listTheorems ;
	public static final Set<String> realNumberTheorems;
	public static final Set<String> integerTheorems ;
	public static final Set<String> setAndFunctionTheorems ;
	public static final Set<String> iteratedOperationTheorems ;
	public static final Set<String> cartesianPowerTheorems ;
	public static final int NUM_HOL_COMMANDS;
	static{
		
		 NUM_HOL_COMMANDS = Array.getLength(HOL_COMMANDS_STRING);
		HOL_COMMANDS = new LinkedList<String>();
		for (int i = 0; i < NUM_HOL_COMMANDS; i++){
		   HOL_COMMANDS.add(HOL_COMMANDS_STRING[i]);
			}

		 pairTheorems = new TreeSet<String>();
		 wellfoundednessTheorems = new TreeSet<String>();
		 naturalNumberTheorems = new TreeSet<String>();
		 listTheorems = new TreeSet<String>();
		 realNumberTheorems = new TreeSet<String>();
		 integerTheorems = new TreeSet<String>();
		 setAndFunctionTheorems = new TreeSet<String>();
		 iteratedOperationTheorems = new TreeSet<String>();
		 cartesianPowerTheorems = new TreeSet<String>();

		
		 basicLogicTheorems = new TreeSet<String>();
		basicLogicTheorems.add("ABS_SIMP");
		basicLogicTheorems.add("AND_CLAUSES");
		basicLogicTheorems.add("AND_DEF");
		basicLogicTheorems.add("AND_FORALL_THM");
		basicLogicTheorems.add("BETA_THM");
		basicLogicTheorems.add("BOOL_CASES_AX");
		basicLogicTheorems.add("COND_ABS");
		basicLogicTheorems.add("COND_CLAUSES");
		basicLogicTheorems.add("COND_DEF");
		basicLogicTheorems.add("COND_ELIM_THM");
		basicLogicTheorems.add("COND_EXPAND");
		basicLogicTheorems.add("COND_ID");
		basicLogicTheorems.add("COND_RAND");
		basicLogicTheorems.add("COND_RATOR");
		basicLogicTheorems.add("CONJ_ACI");
		basicLogicTheorems.add("CONJ_ASSOC");
		basicLogicTheorems.add("CONJ_SYM");
		basicLogicTheorems.add("CONTRAPOS_THM");
		basicLogicTheorems.add("DE_MORGAN_THM");
		basicLogicTheorems.add("DISJ_ACI");
		basicLogicTheorems.add("DISJ_ASSOC");
		basicLogicTheorems.add("DISJ_SYM");
		basicLogicTheorems.add("EQ_CLAUSES");
		basicLogicTheorems.add("EQ_EXT");
		basicLogicTheorems.add("EQ_IMP");
		basicLogicTheorems.add("EQ_REFL");
		basicLogicTheorems.add("EQ_REFL_T");
		basicLogicTheorems.add("EQ_SYM");
		basicLogicTheorems.add("EQ_SYM_EQ");
		basicLogicTheorems.add("EQ_TRANS");
		basicLogicTheorems.add("ETA_AX");
		basicLogicTheorems.add("EXCLUDED_MIDDLE");
		basicLogicTheorems.add("EXISITS_BOOL_THM");
		basicLogicTheorems.add("EXISTS_DEF");
		basicLogicTheorems.add("EXISTS_NOT_THM");
		basicLogicTheorems.add("EXISTS_OR_THM");
		basicLogicTheorems.add("EXISTS_REFL");
		basicLogicTheorems.add("EXISTS_SIMP");
		basicLogicTheorems.add("EXISTS_THM");
		basicLogicTheorems.add("EXISTS_UNIQUE");
		basicLogicTheorems.add("EXISTS_UNIQUE_ALT");
		basicLogicTheorems.add("EXISTS_UNIQUE_DEF");
		basicLogicTheorems.add("EXISTS_UNIQUE_REFL");
		basicLogicTheorems.add("EXISTS_UNIQUE_THM");
		basicLogicTheorems.add("FORALL_AND_THM");
		basicLogicTheorems.add("FORALL_BOOL_THM");
		basicLogicTheorems.add("FORALL_DEF");
		basicLogicTheorems.add("FORALL_NOT_THM");
		basicLogicTheorems.add("FORALL_SIMP");
		basicLogicTheorems.add("FUN_EQ_THM");
		basicLogicTheorems.add("F_DEF");
		basicLogicTheorems.add("IMP_CLAUSES");
		basicLogicTheorems.add("IMP_CONJ");
		basicLogicTheorems.add("IMP_DEF");
		basicLogicTheorems.add("IMP_IMP");
		basicLogicTheorems.add("LEFT_AND_EXISTS_THM");
		basicLogicTheorems.add("LEFT_AND_FORALL_THM");
		basicLogicTheorems.add("LEFT_EXISTS_AND_THM");
		basicLogicTheorems.add("LEFT_EXISTS_IMP_THM");
		basicLogicTheorems.add("LEFT_FORALL_IMP_THM");
		basicLogicTheorems.add("LEFT_FORALL_OR_THM");
		basicLogicTheorems.add("LEFT_IMP_EXISTS_THM");
		basicLogicTheorems.add("LEFT_IMP_FORALL_THM");
		basicLogicTheorems.add("LEFT_OR_DISTRIB");
		basicLogicTheorems.add("LEFT_OR_EXISTS_THM");
		basicLogicTheorems.add("LEFT_OR_FORALL_THM");
		basicLogicTheorems.add("MONO_AND");
		basicLogicTheorems.add("MONO_COND");
		basicLogicTheorems.add("MONO_EXISTS");
		basicLogicTheorems.add("MONO_FORALL");
		basicLogicTheorems.add("MONO_IMP");
		basicLogicTheorems.add("MONO_NOT");
		basicLogicTheorems.add("MONO_OR");
		basicLogicTheorems.add("NOT_CLAUSES");
		basicLogicTheorems.add("NOT_CLAUSES_WEAK");
		basicLogicTheorems.add("NOT_DEF");
		basicLogicTheorems.add("NOT_EXISTS_THM");
		basicLogicTheorems.add("NOT_FORALL_THM");
		basicLogicTheorems.add("NOT_IMP");
		basicLogicTheorems.add("OR_CLAUSES");
		basicLogicTheorems.add("OR_DEF");
		basicLogicTheorems.add("OR_EXISTS_THM");
		basicLogicTheorems.add("REFL_CLAUSE");
		basicLogicTheorems.add("RIGHT_AND_EXISTS_THM");
		basicLogicTheorems.add("RIGHT_AND_FORALL_THM");
		basicLogicTheorems.add("RIGHT_EXISTS_AND_THM");
		basicLogicTheorems.add("RIGHT_EXISTS_IMP_THM");
		basicLogicTheorems.add("RIGHT_FORALL_IMP_THM");
		basicLogicTheorems.add("RIGHT_FORALL_OR_THM");
		basicLogicTheorems.add("RIGHT_IMP_EXISTS_THM");
		basicLogicTheorems.add("RIGHT_IMP_FORALL_THM");
		basicLogicTheorems.add("RIGHT_OR_DISTRIB");
		basicLogicTheorems.add("RIGHT_OR_EXISTS_THM");
		basicLogicTheorems.add("RIGHT_OR_FORALL_THM");
		basicLogicTheorems.add("SELECT_AX");
		basicLogicTheorems.add("SELECT_REFL");
		basicLogicTheorems.add("SELECT_UNIQUE");
		basicLogicTheorems.add("SKOLEM_THM");
		basicLogicTheorems.add("SWAP_EXISTS_THM");
		basicLogicTheorems.add("SWAP_FORALL_THM");
		basicLogicTheorems.add("TRIV_AND_EXISTS_THM");
		basicLogicTheorems.add("TRIV_EXISTS_AND_THM");
		basicLogicTheorems.add("TRIV_EXISTS_IMP_THM");
		basicLogicTheorems.add("TRIV_FORALL_IMP_THM");
		basicLogicTheorems.add("TRIV_FORALL_OR_THM");
		basicLogicTheorems.add("TRUTH");
		basicLogicTheorems.add("T_DEF");
		basicLogicTheorems.add("UNIQUE_SKOLEM_ALT");
		basicLogicTheorems.add("UNIQUE_SKOLEM_THM");
		basicLogicTheorems.add("UNWIND_THM1");
		basicLogicTheorems.add("UNWIND_THM2");
		basicLogicTheorems.add("bool_INDUCT");
		basicLogicTheorems.add("bool_RECURSION");
		 constructTheorems = new TreeSet<String>();

		constructTheorems.add("EXISTS_ONE_REP ".trim());
		constructTheorems.add("I_DEF ".trim());
		constructTheorems.add("I_O_ID ".trim());
		constructTheorems.add("I_THM ".trim());
		constructTheorems.add("OUTL".trim());
		constructTheorems.add("OUTR".trim());
		constructTheorems.add("o_ASSOC".trim());
		constructTheorems.add("o_DEF ".trim());
		constructTheorems.add("o_THM ".trim());
		constructTheorems.add("one".trim());
		constructTheorems.add("one_Axiom".trim());
		constructTheorems.add("one_DEF ".trim());
		constructTheorems.add("one_INDUCT ".trim());
		constructTheorems.add("one_RECURSION ".trim());
		constructTheorems.add("one_axiom ".trim());
		constructTheorems.add("one_tydef ".trim());
		constructTheorems.add("option_INDUCT ".trim());
		constructTheorems.add("option_RECURSION".trim());
		constructTheorems.add("sum_INDUCT ".trim());
		constructTheorems.add("sum_RECURSION ".trim());

		

		pairTheorems.add("COMMA_DEF ".trim());
		pairTheorems.add("CURRY_DEF ".trim());
		pairTheorems.add("EXISTS_PAIR_THM ".trim());
		pairTheorems.add("FORALL_PAIR_THM ".trim());
		pairTheorems.add("FST".trim());
		pairTheorems.add("FST_DEF ".trim());
		pairTheorems.add("PAIR".trim());
		pairTheorems.add("PAIR_EQ".trim());
		pairTheorems.add("PAIR_EXISTS_THM ".trim());
		pairTheorems.add("PAIR_SURJECTIVE ".trim());
		pairTheorems.add("PASSOC_DEF ".trim());
		pairTheorems.add("REP_ABS_PAIR".trim());
		pairTheorems.add("SND".trim());
		pairTheorems.add("SND_DEF".trim());
		pairTheorems.add("UNCURRY_DEF".trim());
		pairTheorems.add("mk_pair_def".trim());
		pairTheorems.add("pair_INDUCT ".trim());
		pairTheorems.add("pair_RECURSION ".trim());
		pairTheorems.add("prod_tybij".trim());

		
		wellfoundednessTheorems.add("MEASURE_LE ".trim());
		wellfoundednessTheorems.add("WF".trim());
		wellfoundednessTheorems.add("WF_DCHAIN ".trim());
		wellfoundednessTheorems.add("WF_EQ ".trim());
		wellfoundednessTheorems.add("WF_EREC ".trim());
		wellfoundednessTheorems.add("WF_FALSE".trim());
		wellfoundednessTheorems.add("WF_IND ".trim());
		wellfoundednessTheorems.add("WF_LEX ".trim());
		wellfoundednessTheorems.add("WF_LEX_DEPENDENT".trim());
		wellfoundednessTheorems.add("WF_MEASURE ".trim());
		wellfoundednessTheorems.add("WF_MEASURE_GEN ".trim());
		wellfoundednessTheorems.add("WF_POINTWISE ".trim());
		wellfoundednessTheorems.add("WF_REC ".trim());
		wellfoundednessTheorems.add("WF_REC_INVARIANT ".trim());
		wellfoundednessTheorems.add("WF_REC_TAIL ".trim());
		wellfoundednessTheorems.add("WF_REC_TAIL_GENERAL".trim());
		wellfoundednessTheorems.add("WF_REC_WF ".trim());
		wellfoundednessTheorems.add("WF_REC_num ".trim());
		wellfoundednessTheorems.add("WF_REFL ".trim());
		wellfoundednessTheorems.add("WF_SUBSET ".trim());
		wellfoundednessTheorems.add("WF_UREC_WF".trim());
		wellfoundednessTheorems.add("WF_num ".trim());
		wellfoundednessTheorems.add("measure ".trim());

		
		naturalNumberTheorems.add("ADD".trim());
		naturalNumberTheorems.add("ADD1".trim());
		naturalNumberTheorems.add("ADD_0 ".trim());
		naturalNumberTheorems.add("ADD_AC ".trim());
		naturalNumberTheorems.add("ADD_ASSOC ".trim());
		naturalNumberTheorems.add("ADD_CLAUSES ".trim());
		naturalNumberTheorems.add("ADD_EQ_0".trim());
		naturalNumberTheorems.add("ADD_SUB".trim());
		naturalNumberTheorems.add("ADD_SUB2".trim());
		naturalNumberTheorems.add("ADD_SUBR".trim());
		naturalNumberTheorems.add("ADD_SUBR2".trim());
		naturalNumberTheorems.add("ADD_SUC".trim());
		naturalNumberTheorems.add("ADD_SYM".trim());
		naturalNumberTheorems.add("BIT0".trim());
		naturalNumberTheorems.add("BIT0_THM ".trim());
		naturalNumberTheorems.add("BIT1".trim());
		naturalNumberTheorems.add("BIT1_THM ".trim());
		naturalNumberTheorems.add("DIST_ADD2 ".trim());
		naturalNumberTheorems.add("DIST_ADD2_REV ".trim());
		naturalNumberTheorems.add("DIST_ADDBOUND ".trim());
		naturalNumberTheorems.add("DIST_ELIM_THM ".trim());
		naturalNumberTheorems.add("DIST_EQ_0".trim());
		naturalNumberTheorems.add("DIST_LADD ".trim());
		naturalNumberTheorems.add("DIST_LADD_0 ".trim());
		naturalNumberTheorems.add("DIST_LE_CASES ".trim());
		naturalNumberTheorems.add("DIST_LMUL ".trim());
		naturalNumberTheorems.add("DIST_LZERO ".trim());
		naturalNumberTheorems.add("DIST_RADD ".trim());
		naturalNumberTheorems.add("DIST_RADD_0 ".trim());
		naturalNumberTheorems.add("DIST_REFL ".trim());
		naturalNumberTheorems.add("DIST_RMUL ".trim());
		naturalNumberTheorems.add("DIST_RZERO ".trim());
		naturalNumberTheorems.add("DIST_SYM ".trim());
		naturalNumberTheorems.add("DIST_TRIANGLE ".trim());
		naturalNumberTheorems.add("DIST_TRIANGLES_LE ".trim());
		naturalNumberTheorems.add("DIST_TRIANGLE_LE ".trim());
		naturalNumberTheorems.add("DIVISION ".trim());
		naturalNumberTheorems.add("DIVISION_0 ".trim());
		naturalNumberTheorems.add("DIVMOD_ELIM_THM ".trim());
		naturalNumberTheorems.add("DIVMOD_ELIM_THM’".trim());
		naturalNumberTheorems.add("DIVMOD_EXIST ".trim());
		naturalNumberTheorems.add("DIVMOD_EXIST_0 ".trim());
		naturalNumberTheorems.add("DIVMOD_UNIQ ".trim());
		naturalNumberTheorems.add("DIVMOD_UNIQ_LEMMA ".trim());
		naturalNumberTheorems.add("DIV_0 ".trim());
		naturalNumberTheorems.add("DIV_1 ".trim());
		naturalNumberTheorems.add("DIV_ADD_MOD ".trim());
		naturalNumberTheorems.add("DIV_DIV ".trim());
		naturalNumberTheorems.add("DIV_EQ_0 ".trim());
		naturalNumberTheorems.add("DIV_EQ_EXCLUSION ".trim());
		naturalNumberTheorems.add("DIV_LE ".trim());
		naturalNumberTheorems.add("DIV_LE_EXCLUSION ".trim());
		naturalNumberTheorems.add("DIV_LT ".trim());
		naturalNumberTheorems.add("DIV_MOD ".trim());
		naturalNumberTheorems.add("DIV_MONO ".trim());
		naturalNumberTheorems.add("DIV_MONO2 ".trim());
		naturalNumberTheorems.add("DIV_MONO_LT ".trim());
		naturalNumberTheorems.add("DIV_MULT ".trim());
		naturalNumberTheorems.add("DIV_MULT2 ".trim());
		naturalNumberTheorems.add("DIV_MUL_LE ".trim());
		naturalNumberTheorems.add("DIV_REFL ".trim());
		naturalNumberTheorems.add("DIV_UNIQ ".trim());
		naturalNumberTheorems.add("EQ_ADD_LCANCEL".trim());
		naturalNumberTheorems.add("EQ_ADD_LCANCEL_0 ".trim());
		naturalNumberTheorems.add("EQ_ADD_RCANCEL ".trim());
		naturalNumberTheorems.add("EQ_ADD_RCANCEL_0 ".trim());
		naturalNumberTheorems.add("EQ_IMP_LE ".trim());
		naturalNumberTheorems.add("EQ_MULT_LCANCEL ".trim());
		naturalNumberTheorems.add("EQ_MULT_RCANCEL ".trim());
		naturalNumberTheorems.add("EQ_SUC ".trim());
		naturalNumberTheorems.add("EVEN".trim());
		naturalNumberTheorems.add("EVEN_ADD ".trim());
		naturalNumberTheorems.add("EVEN_AND_ODD ".trim());
		naturalNumberTheorems.add("EVEN_DOUBLE ".trim());
		naturalNumberTheorems.add("EVEN_EXISTS ".trim());
		naturalNumberTheorems.add("EVEN_EXISTS_LEMMA ".trim());
		naturalNumberTheorems.add("EVEN_EXP ".trim());
		naturalNumberTheorems.add("EVEN_MOD ".trim());
		naturalNumberTheorems.add("EVEN_MULT ".trim());
		naturalNumberTheorems.add("EVEN_ODD_DECOMPOSITION ".trim());
		naturalNumberTheorems.add("EVEN_OR_ODD ".trim());
		naturalNumberTheorems.add("EVEN_SUB ".trim());
		naturalNumberTheorems.add("EXP".trim());
		naturalNumberTheorems.add("EXP_1 ".trim());
		naturalNumberTheorems.add("EXP_2 ".trim());
		naturalNumberTheorems.add("EXP_ADD ".trim());
		naturalNumberTheorems.add("EXP_EQ_0 ".trim());
		naturalNumberTheorems.add("EXP_LT_0".trim());
		naturalNumberTheorems.add("EXP_MULT ".trim());
		naturalNumberTheorems.add("EXP_ONE ".trim());
		naturalNumberTheorems.add("FACT".trim());
		naturalNumberTheorems.add("FACT_LE ".trim());
		naturalNumberTheorems.add("FACT_LT ".trim());
		naturalNumberTheorems.add("FACT_MONO ".trim());
		naturalNumberTheorems.add("GE".trim());
		naturalNumberTheorems.add("GT".trim());
		naturalNumberTheorems.add("LE".trim());
		naturalNumberTheorems.add("LEFT_ADD_DISTRIB".trim());
		naturalNumberTheorems.add("LEFT_SUB_DISTRIB ".trim());
		naturalNumberTheorems.add("LET_ADD2 ".trim());
		naturalNumberTheorems.add("LET_ANTISYM ".trim());
		naturalNumberTheorems.add("LET_CASES ".trim());
		naturalNumberTheorems.add("LET_TRANS ".trim());
		naturalNumberTheorems.add("LE_0".trim());
		naturalNumberTheorems.add("LE_ADD ".trim());
		naturalNumberTheorems.add("LE_ADD2 ".trim());
		naturalNumberTheorems.add("LE_ADDR ".trim());
		naturalNumberTheorems.add("LE_ADD_LCANCEL ".trim());
		naturalNumberTheorems.add("LE_ADD_RCANCEL ".trim());
		naturalNumberTheorems.add("LE_ANTISYM ".trim());
		naturalNumberTheorems.add("LE_CASES ".trim());
		naturalNumberTheorems.add("LE_EXISTS ".trim());
		naturalNumberTheorems.add("LE_EXP ".trim());
		naturalNumberTheorems.add("LE_LDIV ".trim());
		naturalNumberTheorems.add("LE_LDIV_EQ ".trim());
		naturalNumberTheorems.add("LE_LT ".trim());
		naturalNumberTheorems.add("LE_MULT2 ".trim());
		naturalNumberTheorems.add("LE_MULT_LCANCEL ".trim());
		naturalNumberTheorems.add("LE_MULT_RCANCEL ".trim());
		naturalNumberTheorems.add("LE_RDIV_EQ ".trim());
		naturalNumberTheorems.add("LE_REFL ".trim());
		naturalNumberTheorems.add("LE_SQUARE_REFL ".trim());
		naturalNumberTheorems.add("LE_SUC ".trim());
		naturalNumberTheorems.add("LE_SUC_LT ".trim());
		naturalNumberTheorems.add("LE_TRANS ".trim());
		naturalNumberTheorems.add("LT".trim());
		naturalNumberTheorems.add("LTE_ADD2 ".trim());
		naturalNumberTheorems.add("LTE_ANTISYM ".trim());
		naturalNumberTheorems.add("LTE_CASES ".trim());
		naturalNumberTheorems.add("LTE_TRANS |- !m n p. m < n".trim());
		naturalNumberTheorems.add("LT_0".trim());
		naturalNumberTheorems.add("LT_ADD ".trim());
		naturalNumberTheorems.add("LT_ADD2 ".trim());
		naturalNumberTheorems.add("LT_ADDR ".trim());
		naturalNumberTheorems.add("LT_ADD_LCANCEL ".trim());
		naturalNumberTheorems.add("LT_ADD_RCANCEL ".trim());
		naturalNumberTheorems.add("LT_ANTISYM ".trim());
		naturalNumberTheorems.add("LT_CASES ".trim());
		naturalNumberTheorems.add("LT_EXISTS ".trim());
		naturalNumberTheorems.add("LT_EXP ".trim());
		naturalNumberTheorems.add("LT_IMP_LE ".trim());
		naturalNumberTheorems.add("LT_LE ".trim());
		naturalNumberTheorems.add("LT_LMULT ".trim());
		naturalNumberTheorems.add("LT_MULT ".trim());
		naturalNumberTheorems.add("LT_MULT2 ".trim());
		naturalNumberTheorems.add("LT_MULT_LCANCEL ".trim());
		naturalNumberTheorems.add("LT_MULT_RCANCEL ".trim());
		naturalNumberTheorems.add("LT_NZ ".trim());
		naturalNumberTheorems.add("LT_REFL ".trim());
		naturalNumberTheorems.add("LT_SUC ".trim());
		naturalNumberTheorems.add("LT_SUC_LE ".trim());
		naturalNumberTheorems.add("LT_TRANS ".trim());
		naturalNumberTheorems.add("MINIMAL ".trim());
		naturalNumberTheorems.add("MOD_0 ".trim());
		naturalNumberTheorems.add("MOD_1 ".trim());
		naturalNumberTheorems.add("MOD_ADD_MOD ".trim());
		naturalNumberTheorems.add("MOD_EQ ".trim());
		naturalNumberTheorems.add("MOD_EQ_0 ".trim());
		naturalNumberTheorems.add("MOD_EXISTS ".trim());
		naturalNumberTheorems.add("MOD_EXP_MOD ".trim());
		naturalNumberTheorems.add("MOD_LE ".trim());
		naturalNumberTheorems.add("MOD_LT ".trim());
		naturalNumberTheorems.add("MOD_MOD ".trim());
		naturalNumberTheorems.add("MOD_MOD_REFL ".trim());
		naturalNumberTheorems.add("MOD_MULT ".trim());
		naturalNumberTheorems.add("MOD_MULT2 ".trim());
		naturalNumberTheorems.add("MOD_MULT_ADD ".trim());
		naturalNumberTheorems.add("MOD_MULT_LMOD ".trim());
		naturalNumberTheorems.add("MOD_MULT_MOD2 ".trim());
		naturalNumberTheorems.add("MOD_MULT_RMOD ".trim());
		naturalNumberTheorems.add("MOD_UNIQ ".trim());
		naturalNumberTheorems.add("MULT".trim());
		naturalNumberTheorems.add("MULT_0 ".trim());
		naturalNumberTheorems.add("MULT_2 ".trim());
		naturalNumberTheorems.add("MULT_AC ".trim());
		naturalNumberTheorems.add("MULT_ASSOC ".trim());
		naturalNumberTheorems.add("MULT_CLAUSES ".trim());
		naturalNumberTheorems.add("MULT_EQ_0 ".trim());
		naturalNumberTheorems.add("MULT_EQ_1 ".trim());
		naturalNumberTheorems.add("MULT_EXP ".trim());
		naturalNumberTheorems.add("MULT_SUC ".trim());
		naturalNumberTheorems.add("MULT_SYM ".trim());
		naturalNumberTheorems.add("NOT_EVEN ".trim());
		naturalNumberTheorems.add("NOT_LE ".trim());
		naturalNumberTheorems.add("NOT_LT ".trim());
		naturalNumberTheorems.add("NOT_ODD ".trim());
		naturalNumberTheorems.add("NOT_SUC ".trim());
		naturalNumberTheorems.add("NUMERAL ".trim());
		naturalNumberTheorems.add("ODD".trim());
		naturalNumberTheorems.add("ODD_ADD ".trim());
		naturalNumberTheorems.add("ODD_DOUBLE ".trim());
		naturalNumberTheorems.add("ODD_EXISTS ".trim());
		naturalNumberTheorems.add("ODD_EXP ".trim());
		naturalNumberTheorems.add("ODD_MOD ".trim());
		naturalNumberTheorems.add("ODD_MULT ".trim());
		naturalNumberTheorems.add("ODD_SUB ".trim());
		naturalNumberTheorems.add("ONE".trim());
		naturalNumberTheorems.add("PRE".trim());
		naturalNumberTheorems.add("PRE_ELIM_THM ".trim());
		naturalNumberTheorems.add("PRE_ELIM_THM’ ".trim());
		naturalNumberTheorems.add("RIGHT_ADD_DISTRIB ".trim());
		naturalNumberTheorems.add("RIGHT_SUB_DISTRIB ".trim());
		naturalNumberTheorems.add("SUB".trim());
		naturalNumberTheorems.add("SUB_0 ".trim());
		naturalNumberTheorems.add("SUB_ADD ".trim());
		naturalNumberTheorems.add("SUB_ADD_LCANCEL".trim());
		naturalNumberTheorems.add("SUB_ADD_RCANCEL".trim());
		naturalNumberTheorems.add("SUB_ELIM_THM ".trim());
		naturalNumberTheorems.add("SUB_ELIM_THM’ ".trim());
		naturalNumberTheorems.add("SUB_EQ_0 ".trim());
		naturalNumberTheorems.add("SUB_PRESUC ".trim());
		naturalNumberTheorems.add("SUB_REFL ".trim());
		naturalNumberTheorems.add("SUB_SUC ".trim());
		naturalNumberTheorems.add("SUC_INJ ".trim());
		naturalNumberTheorems.add("SUC_SUB1 ".trim());
		naturalNumberTheorems.add("TWO".trim());
		naturalNumberTheorems.add("WLOG_LE ".trim());
		naturalNumberTheorems.add("WLOG_LT ".trim());
		naturalNumberTheorems.add("dist".trim());
		naturalNumberTheorems.add("minimal ".trim());
		naturalNumberTheorems.add("num_Axiom ".trim());
		naturalNumberTheorems.add("num_CASES ".trim());
		naturalNumberTheorems.add("num_INDUCTION ".trim());
		naturalNumberTheorems.add("num_MAX ".trim());
		naturalNumberTheorems.add("num_RECURSION ".trim());
		naturalNumberTheorems.add("num_WF ".trim());
		naturalNumberTheorems.add("num_WOP ".trim());

		

		listTheorems.add("ALL".trim());
		listTheorems.add("ALL2".trim());
		listTheorems.add("ALL2_ALL ".trim());
		listTheorems.add("ALL2_AND_RIGHT ".trim());
		listTheorems.add("ALL2_DEF ".trim());
		listTheorems.add("ALL2_MAP ".trim());
		listTheorems.add("ALL2_MAP2 ".trim());
		listTheorems.add("ALL_APPEND ".trim());
		listTheorems.add("ALL_IMP ".trim());
		listTheorems.add("ALL_MAP ".trim());
		listTheorems.add("ALL_MEM ".trim());
		listTheorems.add("ALL_MP ".trim());
		listTheorems.add("ALL_T ".trim());
		listTheorems.add("AND_ALL ".trim());
		listTheorems.add("AND_ALL2 ".trim());
		listTheorems.add("APPEND ".trim());
		listTheorems.add("APPEND_ASSOC ".trim());
		listTheorems.add("APPEND_EQ_NIL ".trim());
		listTheorems.add("APPEND_NIL ".trim());
		listTheorems.add("ASSOC ".trim());
		listTheorems.add("CONS_11 ".trim());
		listTheorems.add("EL".trim());
		listTheorems.add("EX".trim());
		listTheorems.add("EXISTS_EX ".trim());
		listTheorems.add("EX_IMP ".trim());
		listTheorems.add("EX_MAP ".trim());
		listTheorems.add("EX_MEM ".trim());
		listTheorems.add("FILTER ".trim());
		listTheorems.add("FILTER_APPEND ".trim());
		listTheorems.add("FILTER_MAP ".trim());
		listTheorems.add("FORALL_ALL ".trim());
		listTheorems.add("HD".trim());
		listTheorems.add("ITLIST ".trim());
		listTheorems.add("ITLIST2 ".trim());
		listTheorems.add("ITLIST2_DEF ".trim());
		listTheorems.add("ITLIST_APPEND ".trim());
		listTheorems.add("ITLIST_EXTRA ".trim());
		listTheorems.add("LAST".trim());
		listTheorems.add("LAST_CLAUSES ".trim());
		listTheorems.add("LENGTH ".trim());
		listTheorems.add("LENGTH_APPEND ".trim());
		listTheorems.add("LENGTH_EQ_CONS ".trim());
		listTheorems.add("LENGTH_EQ_NIL ".trim());
		listTheorems.add("LENGTH_MAP ".trim());
		listTheorems.add("LENGTH_MAP2 ".trim());
		listTheorems.add("LENGTH_REPLICATE ".trim());
		listTheorems.add("MAP".trim());
		listTheorems.add("MAP2".trim());
		listTheorems.add("MAP2_DEF ".trim());
		listTheorems.add("MAP_APPEND ".trim());
		listTheorems.add("MAP_EQ ".trim());
		listTheorems.add("MAP_EQ_ALL2 ".trim());
		listTheorems.add("MAP_EQ_DEGEN ".trim());
		listTheorems.add("MAP_FST_ZIP ".trim());
		listTheorems.add("MAP_SND_ZIP ".trim());
		listTheorems.add("MAP_o ".trim());
		listTheorems.add("MEM".trim());
		listTheorems.add("MEM_APPEND ".trim());
		listTheorems.add("MEM_ASSOC ".trim());
		listTheorems.add("MEM_EL ".trim());
		listTheorems.add("MEM_FILTER ".trim());
		listTheorems.add("MEM_MAP ".trim());
		listTheorems.add("MONO_ALL ".trim());
		listTheorems.add("MONO_ALL2 ".trim());
		listTheorems.add("NOT_ALL ".trim());
		listTheorems.add("NOT_CONS_NIL ".trim());
		listTheorems.add("NOT_EX ".trim());
		listTheorems.add("NULL".trim());
		listTheorems.add("REPLICATE ".trim());
		listTheorems.add("REVERSE ".trim());
		listTheorems.add("REVERSE_APPEND ".trim());
		listTheorems.add("REVERSE_REVERSE ".trim());
		listTheorems.add("TL".trim());
		listTheorems.add("ZIP".trim());
		listTheorems.add("ZIP_DEF ".trim());
		listTheorems.add("list_CASES ".trim());
		listTheorems.add("list_INDUCT ".trim());
		listTheorems.add("list_RECURSION ".trim());

		

		realNumberTheorems.add("REAL_ADD_ASSOC ".trim());
		realNumberTheorems.add("REAL_ADD_LDISTRIB ".trim());
		realNumberTheorems.add("REAL_ADD_LID ".trim());
		realNumberTheorems.add("REAL_ADD_LINV ".trim());
		realNumberTheorems.add("REAL_ADD_SYM ".trim());
		realNumberTheorems.add("REAL_INV_0 ".trim());
		realNumberTheorems.add("REAL_LE_ANTISYM ".trim());
		realNumberTheorems.add("REAL_LE_LADD_IMP ".trim());
		realNumberTheorems.add("REAL_LE_MUL ".trim());
		realNumberTheorems.add("REAL_LE_REFL ".trim());
		realNumberTheorems.add("REAL_LE_TOTAL ".trim());
		realNumberTheorems.add("REAL_LE_TRANS ".trim());
		realNumberTheorems.add("REAL_MUL_ASSOC".trim());
		realNumberTheorems.add("REAL_MUL_LID ".trim());
		realNumberTheorems.add("REAL_MUL_LINV ".trim());
		realNumberTheorems.add("REAL_MUL_SYM ".trim());
		realNumberTheorems.add("REAL_OF_NUM_ADD ".trim());
		realNumberTheorems.add("REAL_OF_NUM_EQ".trim());
		realNumberTheorems.add("REAL_OF_NUM_LE ".trim());
		realNumberTheorems.add("REAL_OF_NUM_MUL ".trim());
		realNumberTheorems.add("REAL_ABS_0 ".trim());
		realNumberTheorems.add("REAL_ABS_1 ".trim());
		realNumberTheorems.add("REAL_ABS_ABS ".trim());
		realNumberTheorems.add("REAL_ABS_BETWEEN ".trim());
		realNumberTheorems.add("REAL_ABS_BETWEEN1 ".trim());
		realNumberTheorems.add("REAL_ABS_BETWEEN2 ".trim());
		realNumberTheorems.add("REAL_ABS_BOUND ".trim());
		realNumberTheorems.add("REAL_ABS_BOUNDS ".trim());
		realNumberTheorems.add("REAL_ABS_CASES ".trim());
		realNumberTheorems.add("REAL_ABS_CIRCLE ".trim());
		realNumberTheorems.add("REAL_ABS_DIV ".trim());
		realNumberTheorems.add("REAL_ABS_INV ".trim());
		realNumberTheorems.add("REAL_ABS_LE ".trim());
		realNumberTheorems.add("REAL_ABS_MUL ".trim());
		realNumberTheorems.add("REAL_ABS_NEG ".trim());
		realNumberTheorems.add("REAL_ABS_NUM ".trim());
		realNumberTheorems.add("REAL_ABS_NZ ".trim());
		realNumberTheorems.add("REAL_ABS_POS ".trim());
		realNumberTheorems.add("REAL_ABS_POW ".trim());
		realNumberTheorems.add("REAL_ABS_REFL ".trim());
		realNumberTheorems.add("REAL_ABS_SIGN ".trim());
		realNumberTheorems.add("REAL_ABS_SIGN2 ".trim());
		realNumberTheorems.add("REAL_ABS_STILLNZ ".trim());
		realNumberTheorems.add("REAL_ABS_SUB ".trim());
		realNumberTheorems.add("REAL_ABS_SUB_ABS ".trim());
		realNumberTheorems.add("REAL_ABS_TRIANGLE ".trim());
		realNumberTheorems.add("REAL_ABS_TRIANGLE_LE ".trim());
		realNumberTheorems.add("REAL_ABS_TRIANGLE_LT ".trim());
		realNumberTheorems.add("REAL_ABS_ZERO ".trim());
		realNumberTheorems.add("REAL_ADD2_SUB2 ".trim());
		realNumberTheorems.add("REAL_ADD_AC ".trim());
		realNumberTheorems.add("REAL_ADD_RDISTRIB ".trim());
		realNumberTheorems.add("REAL_ADD_RID ".trim());
		realNumberTheorems.add("REAL_ADD_RINV ".trim());
		realNumberTheorems.add("REAL_ADD_SUB ".trim());
		realNumberTheorems.add("REAL_ADD_SUB2 ".trim());
		realNumberTheorems.add("REAL_COMPLETE ".trim());
		realNumberTheorems.add("REAL_DIFFSQ ".trim());
		realNumberTheorems.add("REAL_DIV_1 ".trim());
		realNumberTheorems.add("REAL_DIV_LMUL ".trim());
		realNumberTheorems.add("REAL_DIV_POW2 ".trim());
		realNumberTheorems.add("REAL_DIV_POW2_ALT ".trim());
		realNumberTheorems.add("REAL_DIV_REFL ".trim());
		realNumberTheorems.add("REAL_DIV_RMUL ".trim());
		realNumberTheorems.add("REAL_DOWN ".trim());
		realNumberTheorems.add("REAL_DOWN2 ".trim());
		realNumberTheorems.add("REAL_ENTIRE ".trim());
		realNumberTheorems.add("REAL_EQ_ADD_LCANCEL ".trim());
		realNumberTheorems.add("REAL_EQ_ADD_LCANCEL_0 ".trim());
		realNumberTheorems.add("REAL_EQ_ADD_RCANCEL ".trim());
		realNumberTheorems.add("REAL_EQ_ADD_RCANCEL_0 ".trim());
		realNumberTheorems.add("REAL_EQ_IMP_LE ".trim());
		realNumberTheorems.add("REAL_EQ_LCANCEL_IMP ".trim());
		realNumberTheorems.add("REAL_EQ_LDIV_EQ ".trim());
		realNumberTheorems.add("REAL_EQ_MUL_LCANCEL ".trim());
		realNumberTheorems.add("REAL_EQ_MUL_RCANCEL ".trim());
		realNumberTheorems.add("REAL_EQ_NEG2 ".trim());
		realNumberTheorems.add("REAL_EQ_RCANCEL_IMP ".trim());
		realNumberTheorems.add("REAL_EQ_RDIV_EQ ".trim());
		realNumberTheorems.add("REAL_EQ_SUB_LADD ".trim());
		realNumberTheorems.add("REAL_EQ_SUB_RADD ".trim());
		realNumberTheorems.add("REAL_INV_1 ".trim());
		realNumberTheorems.add("REAL_INV_1_LE ".trim());
		realNumberTheorems.add("REAL_INV_DIV ".trim());
		realNumberTheorems.add("REAL_INV_EQ_0 ".trim());
		realNumberTheorems.add("REAL_INV_INV ".trim());
		realNumberTheorems.add("REAL_INV_LE_1 ".trim());
		realNumberTheorems.add("REAL_INV_MUL ".trim());
		realNumberTheorems.add("REAL_INV_NEG ".trim());
		realNumberTheorems.add("REAL_LET_ADD ".trim());
		realNumberTheorems.add("REAL_LET_ADD2 ".trim());
		realNumberTheorems.add("REAL_LET_ANTISYM ".trim());
		realNumberTheorems.add("REAL_LET_TOTAL ".trim());
		realNumberTheorems.add("REAL_LET_TRANS ".trim());
		realNumberTheorems.add("REAL_LE_01 ".trim());
		realNumberTheorems.add("REAL_LE_ADD ".trim());
		realNumberTheorems.add("REAL_LE_ADD2 ".trim());
		realNumberTheorems.add("REAL_LE_ADDL ".trim());
		realNumberTheorems.add("REAL_LE_ADDR ".trim());
		realNumberTheorems.add("REAL_LE_DIV ".trim());
		realNumberTheorems.add("REAL_LE_DIV2_EQ".trim());
		realNumberTheorems.add("REAL_LE_DOUBLE".trim());
		realNumberTheorems.add("REAL_LE_INV ".trim());
		realNumberTheorems.add("REAL_LE_INV2 ".trim());
		realNumberTheorems.add("REAL_LE_INV_EQ ".trim());
		realNumberTheorems.add("REAL_LE_LADD ".trim());
		realNumberTheorems.add("REAL_LE_LCANCEL_IMP ".trim());
		realNumberTheorems.add("REAL_LE_LDIV_EQ ".trim());
		realNumberTheorems.add("REAL_LE_LMUL ".trim());
		realNumberTheorems.add("REAL_LE_LMUL_EQ ".trim());
		realNumberTheorems.add("REAL_LE_LNEG ".trim());
		realNumberTheorems.add("REAL_LE_LT ".trim());
		realNumberTheorems.add("REAL_LE_MAX ".trim());
		realNumberTheorems.add("REAL_LE_MIN ".trim());
		realNumberTheorems.add("REAL_LE_MUL2 ".trim());
		realNumberTheorems.add("REAL_LE_NEG ".trim());
		realNumberTheorems.add("REAL_LE_NEG2 ".trim());
		realNumberTheorems.add("REAL_LE_NEGL ".trim());
		realNumberTheorems.add("REAL_LE_NEGR ".trim());
		realNumberTheorems.add("REAL_LE_NEGTOTAL ".trim());
		realNumberTheorems.add("REAL_LE_POW2 ".trim());
		realNumberTheorems.add("REAL_LE_RADD ".trim());
		realNumberTheorems.add("REAL_LE_RCANCEL_IMP ".trim());
		realNumberTheorems.add("REAL_LE_RDIV_EQ ".trim());
		realNumberTheorems.add("REAL_LE_RMUL ".trim());
		realNumberTheorems.add("REAL_LE_RMUL_EQ ".trim());
		realNumberTheorems.add("REAL_LE_RNEG ".trim());
		realNumberTheorems.add("REAL_LE_SQUARE ".trim());
		realNumberTheorems.add("REAL_LE_SQUARE_ABS ".trim());
		realNumberTheorems.add("REAL_LE_SUB_LADD ".trim());
		realNumberTheorems.add("REAL_LE_SUB_RADD ".trim());
		realNumberTheorems.add("REAL_LNEG_UNIQ ".trim());
		realNumberTheorems.add("REAL_LTE_ADD ".trim());
		realNumberTheorems.add("REAL_LTE_ADD2 ".trim());
		realNumberTheorems.add("REAL_LTE_ANTISYM ".trim());
		realNumberTheorems.add("REAL_LTE_TOTAL ".trim());
		realNumberTheorems.add("REAL_LTE_TRANS ".trim());
		realNumberTheorems.add("REAL_LT_01 ".trim());
		realNumberTheorems.add("REAL_LT_ADD ".trim());
		realNumberTheorems.add("REAL_LT_ADD1 ".trim());
		realNumberTheorems.add("REAL_LT_ADD2 ".trim());
		realNumberTheorems.add("REAL_LT_ADDL ".trim());
		realNumberTheorems.add("REAL_LT_ADDNEG ".trim());
		realNumberTheorems.add("REAL_LT_ADDNEG2 ".trim());
		realNumberTheorems.add("REAL_LT_ADDR ".trim());
		realNumberTheorems.add("REAL_LT_ADD_SUB ".trim());
		realNumberTheorems.add("REAL_LT_ANTISYM ".trim());
		realNumberTheorems.add("REAL_LT_DIV ".trim());
		realNumberTheorems.add("REAL_LT_DIV2_EQ".trim());
		realNumberTheorems.add("REAL_LT_GT ".trim());
		realNumberTheorems.add("REAL_LT_IMP_LE ".trim());
		realNumberTheorems.add("REAL_LT_IMP_NE ".trim());
		realNumberTheorems.add("REAL_LT_IMP_NZ ".trim());
		realNumberTheorems.add("REAL_LT_INV ".trim());
		realNumberTheorems.add("REAL_LT_INV2 ".trim());
		realNumberTheorems.add("REAL_LT_INV_EQ ".trim());
		realNumberTheorems.add("REAL_LT_LADD".trim());
		realNumberTheorems.add("REAL_LT_LADD_IMP ".trim());
		realNumberTheorems.add("REAL_LT_LCANCEL_IMP ".trim());
		realNumberTheorems.add("REAL_LT_LDIV_EQ ".trim());
		realNumberTheorems.add("REAL_LT_LE ".trim());
		realNumberTheorems.add("REAL_LT_LMUL ".trim());
		realNumberTheorems.add("REAL_LT_LMUL_EQ ".trim());
		realNumberTheorems.add("REAL_LT_LNEG ".trim());
		realNumberTheorems.add("REAL_LT_MAX ".trim());
		realNumberTheorems.add("REAL_LT_MIN ".trim());
		realNumberTheorems.add("REAL_LT_MUL ".trim());
		realNumberTheorems.add("REAL_LT_MUL2 ".trim());
		realNumberTheorems.add("REAL_LT_NEG ".trim());
		realNumberTheorems.add("REAL_LT_NEG2 ".trim());
		realNumberTheorems.add("REAL_LT_NEGTOTAL ".trim());
		realNumberTheorems.add("REAL_LT_POW2 ".trim());
		realNumberTheorems.add("REAL_LT_RADD ".trim());
		realNumberTheorems.add("REAL_LT_RCANCEL_IMP ".trim());
		realNumberTheorems.add("REAL_LT_RDIV_EQ ".trim());
		realNumberTheorems.add("REAL_LT_REFL ".trim());
		realNumberTheorems.add("REAL_LT_RMUL ".trim());
		realNumberTheorems.add("REAL_LT_RMUL_EQ ".trim());
		realNumberTheorems.add("REAL_LT_RNEG ".trim());
		realNumberTheorems.add("REAL_LT_SQUARE ".trim());
		realNumberTheorems.add("REAL_LT_SUB_LADD ".trim());
		realNumberTheorems.add("REAL_LT_SUB_RADD ".trim());
		realNumberTheorems.add("REAL_LT_TOTAL ".trim());
		realNumberTheorems.add("REAL_LT_TRANS ".trim());
		realNumberTheorems.add("REAL_MAX_ACI ".trim());
		realNumberTheorems.add("REAL_MAX_ASSOC ".trim());
		realNumberTheorems.add("REAL_MAX_LE ".trim());
		realNumberTheorems.add("REAL_MAX_LT ".trim());
		realNumberTheorems.add("REAL_MAX_MAX".trim());
		realNumberTheorems.add("REAL_MAX_MIN".trim());
		realNumberTheorems.add("REAL_MAX_SYM ".trim());
		realNumberTheorems.add("REAL_MIN_ACI ".trim());
		realNumberTheorems.add("REAL_MIN_ASSOC ".trim());
		realNumberTheorems.add("REAL_MIN_LE ".trim());
		realNumberTheorems.add("REAL_MIN_LT ".trim());
		realNumberTheorems.add("REAL_MIN_MAX ".trim());
		realNumberTheorems.add("REAL_MIN_MIN ".trim());
		realNumberTheorems.add("REAL_MIN_SYM ".trim());
		realNumberTheorems.add("REAL_MUL_2 ".trim());
		realNumberTheorems.add("REAL_MUL_AC ".trim());
		realNumberTheorems.add("REAL_MUL_LINV_UNIQ ".trim());
		realNumberTheorems.add("REAL_MUL_LNEG ".trim());
		realNumberTheorems.add("REAL_MUL_LZERO ".trim());
		realNumberTheorems.add("REAL_MUL_RID ".trim());
		realNumberTheorems.add("REAL_MUL_RINV ".trim());
		realNumberTheorems.add("REAL_MUL_RINV_UNIQ ".trim());
		realNumberTheorems.add("REAL_MUL_RNEG ".trim());
		realNumberTheorems.add("REAL_MUL_RZERO ".trim());
		realNumberTheorems.add("REAL_NEGNEG ".trim());
		realNumberTheorems.add("REAL_NEG_0 ".trim());
		realNumberTheorems.add("REAL_NEG_ADD ".trim());
		realNumberTheorems.add("REAL_NEG_EQ ".trim());
		realNumberTheorems.add("REAL_NEG_EQ_0 ".trim());
		realNumberTheorems.add("REAL_NEG_GE0 ".trim());
		realNumberTheorems.add("REAL_NEG_GT0 ".trim());
		realNumberTheorems.add("REAL_NEG_LE0 ".trim());
		realNumberTheorems.add("REAL_NEG_LMUL ".trim());
		realNumberTheorems.add("REAL_NEG_LT0 ".trim());
		realNumberTheorems.add("REAL_NEG_MINUS1 ".trim());
		realNumberTheorems.add("REAL_NEG_MUL2 ".trim());
		realNumberTheorems.add("REAL_NEG_NEG ".trim());
		realNumberTheorems.add("REAL_NEG_RMUL ".trim());
		realNumberTheorems.add("REAL_NEG_SUB ".trim());
		realNumberTheorems.add("REAL_NOT_EQ ".trim());
		realNumberTheorems.add("REAL_NOT_LE ".trim());
		realNumberTheorems.add("REAL_NOT_LT".trim());
		realNumberTheorems.add("REAL_OF_NUM_GE ".trim());
		realNumberTheorems.add("REAL_OF_NUM_GT ".trim());
		realNumberTheorems.add("REAL_OF_NUM_LT ".trim());
		realNumberTheorems.add("REAL_OF_NUM_POW ".trim());
		realNumberTheorems.add("REAL_OF_NUM_SUB ".trim());
		realNumberTheorems.add("REAL_OF_NUM_SUC ".trim());
		realNumberTheorems.add("REAL_POS ".trim());
		realNumberTheorems.add("REAL_POS_NZ ".trim());
		realNumberTheorems.add("REAL_POW2_ABS".trim());
		realNumberTheorems.add("REAL_POW_1 ".trim());
		realNumberTheorems.add("REAL_POW_1_LE ".trim());
		realNumberTheorems.add("REAL_POW_2 ".trim());
		realNumberTheorems.add("REAL_POW_ADD ".trim());
		realNumberTheorems.add("REAL_POW_DIV ".trim());
		realNumberTheorems.add("REAL_POW_EQ_0 ".trim());
		realNumberTheorems.add("REAL_POW_INV".trim());
		realNumberTheorems.add("REAL_POW_LE".trim());
		realNumberTheorems.add("REAL_POW_LE2".trim());
		realNumberTheorems.add("REAL_POW_LE_1".trim());
		realNumberTheorems.add("REAL_POW_LT ".trim());
		realNumberTheorems.add("REAL_POW_LT2 ".trim());
		realNumberTheorems.add("REAL_POW_MONO ".trim());
		realNumberTheorems.add("REAL_POW_MONO_LT ".trim());
		realNumberTheorems.add("REAL_POW_MUL ".trim());
		realNumberTheorems.add("REAL_POW_NEG ".trim());
		realNumberTheorems.add("REAL_POW_NZ ".trim());
		realNumberTheorems.add("REAL_POW_ONE ".trim());
		realNumberTheorems.add("REAL_POW_POW ".trim());
		realNumberTheorems.add("REAL_POW_SUB ".trim());
		realNumberTheorems.add("REAL_RNEG_UNIQ ".trim());
		realNumberTheorems.add("REAL_SOS_EQ_0 ".trim());
		realNumberTheorems.add("REAL_SUB_0 ".trim());
		realNumberTheorems.add("REAL_SUB_ABS ".trim());
		realNumberTheorems.add("REAL_SUB_ADD ".trim());
		realNumberTheorems.add("REAL_SUB_ADD2 ".trim());
		realNumberTheorems.add("REAL_SUB_INV ".trim());
		realNumberTheorems.add("REAL_SUB_LDISTRIB ".trim());
		realNumberTheorems.add("REAL_SUB_LE ".trim());
		realNumberTheorems.add("REAL_SUB_LNEG ".trim());
		realNumberTheorems.add("REAL_SUB_LT ".trim());
		realNumberTheorems.add("REAL_SUB_LZERO ".trim());
		realNumberTheorems.add("REAL_SUB_NEG2".trim());
		realNumberTheorems.add("REAL_SUB_RDISTRIB".trim());
		realNumberTheorems.add("REAL_SUB_REFL ".trim());
		realNumberTheorems.add("REAL_SUB_RNEG ".trim());
		realNumberTheorems.add("REAL_SUB_RZERO ".trim());
		realNumberTheorems.add("REAL_SUB_SUB ".trim());
		realNumberTheorems.add("REAL_SUB_SUB2 ".trim());
		realNumberTheorems.add("REAL_SUB_TRIANGLE ".trim());
		realNumberTheorems.add("REAL_WLOG_LE ".trim());
		realNumberTheorems.add("REAL_WLOG_LT ".trim());
		realNumberTheorems.add("real_abs ".trim());
		realNumberTheorems.add("real_div ".trim());
		realNumberTheorems.add("real_ge ".trim());
		realNumberTheorems.add("real_gt ".trim());
		realNumberTheorems.add("real_lt ".trim());
		realNumberTheorems.add("real_max ".trim());
		realNumberTheorems.add("real_min ".trim());
		realNumberTheorems.add("real_pow ".trim());
		realNumberTheorems.add("real_sub ".trim());

		

		integerTheorems.add("INT_ABS ".trim());
		integerTheorems.add("INT_ABS_0 ".trim());
		integerTheorems.add("INT_ABS_1 ".trim());
		integerTheorems.add("INT_ABS_ABS ".trim());
		integerTheorems.add("INT_ABS_BETWEEN ".trim());
		integerTheorems.add("INT_ABS_BETWEEN1 ".trim());
		integerTheorems.add("INT_ABS_BETWEEN2 ".trim());
		integerTheorems.add("INT_ABS_BOUND ".trim());
		integerTheorems.add("INT_ABS_CASES ".trim());
		integerTheorems.add("INT_ABS_CIRCLE ".trim());
		integerTheorems.add("INT_ABS_LE ".trim());
		integerTheorems.add("INT_ABS_MUL ".trim());
		integerTheorems.add("INT_ABS_MUL_1 ".trim());
		integerTheorems.add("INT_ABS_NEG ".trim());
		integerTheorems.add("INT_ABS_NUM ".trim());
		integerTheorems.add("INT_ABS_NZ ".trim());
		integerTheorems.add("INT_ABS_POS ".trim());
		integerTheorems.add("INT_ABS_POW ".trim());
		integerTheorems.add("INT_ABS_REFL ".trim());
		integerTheorems.add("INT_ABS_SIGN ".trim());
		integerTheorems.add("INT_ABS_SIGN2 ".trim());
		integerTheorems.add("INT_ABS_STILLNZ ".trim());
		integerTheorems.add("INT_ABS_SUB ".trim());
		integerTheorems.add("INT_ABS_SUB_ABS ".trim());
		integerTheorems.add("INT_ABS_TRIANGLE ".trim());
		integerTheorems.add("INT_ABS_ZERO ".trim());
		integerTheorems.add("INT_ADD2_SUB2 ".trim());
		integerTheorems.add("INT_ADD_AC ".trim());
		integerTheorems.add("INT_ADD_ASSOC ".trim());
		integerTheorems.add("INT_ADD_LDISTRIB ".trim());
		integerTheorems.add("INT_ADD_LID ".trim());
		integerTheorems.add("INT_ADD_LINV ".trim());
		integerTheorems.add("INT_ADD_RDISTRIB ".trim());
		integerTheorems.add("INT_ADD_RID ".trim());
		integerTheorems.add("INT_ADD_RINV ".trim());
		integerTheorems.add("INT_ADD_SUB ".trim());
		integerTheorems.add("INT_ADD_SUB2 ".trim());
		integerTheorems.add("INT_ADD_SYM ".trim());
		integerTheorems.add("INT_ARCH ".trim());
		integerTheorems.add("INT_DIFFSQ ".trim());
		integerTheorems.add("INT_ENTIRE ".trim());
		integerTheorems.add("INT_EQ_ADD_LCANCEL ".trim());
		integerTheorems.add("INT_EQ_ADD_LCANCEL_0 ".trim());
		integerTheorems.add("INT_EQ_ADD_RCANCEL ".trim());
		integerTheorems.add("INT_EQ_ADD_RCANCEL_0 ".trim());
		integerTheorems.add("INT_EQ_IMP_LE ".trim());
		integerTheorems.add("INT_EQ_MUL_LCANCEL ".trim());
		integerTheorems.add("INT_EQ_MUL_RCANCEL ".trim());
		integerTheorems.add("INT_EQ_NEG2 ".trim());
		integerTheorems.add("INT_EQ_SUB_LADD ".trim());
		integerTheorems.add("INT_EQ_SUB_RADD ".trim());
		integerTheorems.add("INT_FORALL_POS ".trim());
		integerTheorems.add("INT_GE ".trim());
		integerTheorems.add("INT_GT ".trim());
		integerTheorems.add("INT_GT_DISCRETE ".trim());
		integerTheorems.add("INT_IMAGE ".trim());
		integerTheorems.add("INT_LET_ADD ".trim());
		integerTheorems.add("INT_LET_ADD2 ".trim());
		integerTheorems.add("INT_LET_ANTISYM ".trim());
		integerTheorems.add("INT_LET_TOTAL ".trim());
		integerTheorems.add("INT_LET_TRANS ".trim());
		integerTheorems.add("INT_LE_01 ".trim());
		integerTheorems.add("INT_LE_ADD ".trim());
		integerTheorems.add("INT_LE_ADD2 ".trim());
		integerTheorems.add("INT_LE_ADDL ".trim());
		integerTheorems.add("INT_LE_ADDR ".trim());
		integerTheorems.add("INT_LE_ANTISYM ".trim());
		integerTheorems.add("INT_LE_DOUBLE ".trim());
		integerTheorems.add("INT_LE_LADD ".trim());
		integerTheorems.add("INT_LE_LADD_IMP ".trim());
		integerTheorems.add("INT_LE_LMUL ".trim());
		integerTheorems.add("INT_LE_LNEG ".trim());
		integerTheorems.add("INT_LE_LT ".trim());
		integerTheorems.add("INT_LE_MAX ".trim());
		integerTheorems.add("INT_LE_MIN ".trim());
		integerTheorems.add("INT_LE_MUL".trim());
		integerTheorems.add("INT_LE_NEG ".trim());
		integerTheorems.add("INT_LE_NEG2 ".trim());
		integerTheorems.add("INT_LE_NEGL".trim());
		integerTheorems.add("INT_LE_NEGR".trim());
		integerTheorems.add("INT_LE_NEGTOTAL".trim());
		integerTheorems.add("INT_LE_POW2 ".trim());
		integerTheorems.add("INT_LE_RADD ".trim());
		integerTheorems.add("INT_LE_REFL".trim());
		integerTheorems.add("INT_LE_RNEG ".trim());
		integerTheorems.add("INT_LE_SQUARE ".trim());
		integerTheorems.add("INT_LE_SUB_LADD ".trim());
		integerTheorems.add("INT_LE_SUB_RADD ".trim());
		integerTheorems.add("INT_LE_TOTAL ".trim());
		integerTheorems.add("INT_LE_TRANS".trim());
		integerTheorems.add("INT_LNEG_UNIQ ".trim());
		integerTheorems.add("INT_LT ".trim());
		integerTheorems.add("INT_LTE_ADD ".trim());
		integerTheorems.add("INT_LTE_ADD2 ".trim());
		integerTheorems.add("INT_LTE_ANTISYM ".trim());
		integerTheorems.add("INT_LTE_TOTAL ".trim());
		integerTheorems.add("INT_LTE_TRANS ".trim());
		integerTheorems.add("INT_LT_01 ".trim());
		integerTheorems.add("INT_LT_ADD ".trim());
		integerTheorems.add("INT_LT_ADD1 ".trim());
		integerTheorems.add("INT_LT_ADD2 ".trim());
		integerTheorems.add("INT_LT_ADDL ".trim());
		integerTheorems.add("INT_LT_ADDNEG ".trim());
		integerTheorems.add("INT_LT_ADDNEG2 ".trim());
		integerTheorems.add("INT_LT_ADDR ".trim());
		integerTheorems.add("INT_LT_ADD_SUB ".trim());
		integerTheorems.add("INT_LT_ANTISYM ".trim());
		integerTheorems.add("INT_LT_DISCRETE ".trim());
		integerTheorems.add("INT_LT_GT ".trim());
		integerTheorems.add("INT_LT_IMP_LE ".trim());
		integerTheorems.add("INT_LT_IMP_NE ".trim());
		integerTheorems.add("INT_LT_LADD ".trim());
		integerTheorems.add("INT_LT_LE ".trim());
		integerTheorems.add("INT_LT_LMUL_EQ ".trim());
		integerTheorems.add("INT_LT_MAX ".trim());
		integerTheorems.add("INT_LT_MIN ".trim());
		integerTheorems.add("INT_LT_MUL ".trim());
		integerTheorems.add("INT_LT_NEG ".trim());
		integerTheorems.add("INT_LT_NEG2 ".trim());
		integerTheorems.add("INT_LT_NEGTOTAL ".trim());
		integerTheorems.add("INT_LT_POW2 ".trim());
		integerTheorems.add("INT_LT_RADD ".trim());
		integerTheorems.add("INT_LT_REFL ".trim());
		integerTheorems.add("INT_LT_RMUL_EQ ".trim());
		integerTheorems.add("INT_LT_SUB_LADD ".trim());
		integerTheorems.add("INT_LT_SUB_RADD ".trim());
		integerTheorems.add("INT_LT_TOTAL ".trim());
		integerTheorems.add("INT_LT_TRANS ".trim());
		integerTheorems.add("INT_MAX_ACI ".trim());
		integerTheorems.add("INT_MAX_ASSOC ".trim());
		integerTheorems.add("INT_MAX_LE ".trim());
		integerTheorems.add("INT_MAX_LT ".trim());
		integerTheorems.add("INT_MAX_MAX ".trim());
		integerTheorems.add("INT_MAX_MIN ".trim());
		integerTheorems.add("INT_MAX_SYM ".trim());
		integerTheorems.add("INT_MIN_ACI ".trim());
		integerTheorems.add("INT_MIN_ASSOC ".trim());
		integerTheorems.add("INT_MIN_LE ".trim());
		integerTheorems.add("INT_MIN_LT ".trim());
		integerTheorems.add("INT_MIN_MAX ".trim());
		integerTheorems.add("INT_MIN_MIN".trim());
		integerTheorems.add("INT_MIN_SYM ".trim());
		integerTheorems.add("INT_MUL_AC ".trim());
		integerTheorems.add("INT_MUL_ASSOC ".trim());
		integerTheorems.add("INT_MUL_LID ".trim());
		integerTheorems.add("INT_MUL_LNEG ".trim());
		integerTheorems.add("INT_MUL_LZERO ".trim());
		integerTheorems.add("INT_MUL_RID ".trim());
		integerTheorems.add("INT_MUL_RNEG ".trim());
		integerTheorems.add("INT_MUL_RZERO ".trim());
		integerTheorems.add("INT_MUL_SYM ".trim());
		integerTheorems.add("INT_NEGNEG".trim());
		integerTheorems.add("INT_NEG_0 ".trim());
		integerTheorems.add("INT_NEG_ADD ".trim());
		integerTheorems.add("INT_NEG_EQ ".trim());
		integerTheorems.add("INT_NEG_EQ_0 ".trim());
		integerTheorems.add("INT_NEG_GE0 ".trim());
		integerTheorems.add("INT_NEG_GT0 ".trim());
		integerTheorems.add("INT_NEG_LE0 ".trim());
		integerTheorems.add("INT_NEG_LMUL ".trim());
		integerTheorems.add("INT_NEG_LT0 ".trim());
		integerTheorems.add("INT_NEG_MINUS1 ".trim());
		integerTheorems.add("INT_NEG_MUL2 ".trim());
		integerTheorems.add("INT_NEG_NEG ".trim());
		integerTheorems.add("INT_NEG_RMUL ".trim());
		integerTheorems.add("INT_NEG_SUB ".trim());
		integerTheorems.add("INT_NOT_EQ ".trim());
		integerTheorems.add("INT_NOT_LE ".trim());
		integerTheorems.add("INT_NOT_LT ".trim());
		integerTheorems.add("INT_OF_NUM_ADD ".trim());
		integerTheorems.add("INT_OF_NUM_EQ ".trim());
		integerTheorems.add("INT_OF_NUM_GE ".trim());
		integerTheorems.add("INT_OF_NUM_GT ".trim());
		integerTheorems.add("INT_OF_NUM_LE ".trim());
		integerTheorems.add("INT_OF_NUM_LT ".trim());
		integerTheorems.add("INT_OF_NUM_MUL ".trim());
		integerTheorems.add("INT_OF_NUM_OF_INT ".trim());
		integerTheorems.add("INT_OF_NUM_POW ".trim());
		integerTheorems.add("INT_OF_NUM_SUB ".trim());
		integerTheorems.add("INT_OF_NUM_SUC ".trim());
		integerTheorems.add("INT_POS ".trim());
		integerTheorems.add("INT_POS_NZ ".trim());
		integerTheorems.add("INT_POW ".trim());
		integerTheorems.add("INT_POW2_ABS ".trim());
		integerTheorems.add("INT_POW_1 ".trim());
		integerTheorems.add("INT_POW_1_LE ".trim());
		integerTheorems.add("INT_POW_2 ".trim());
		integerTheorems.add("INT_POW_ADD ".trim());
		integerTheorems.add("INT_POW_EQ_0 ".trim());
		integerTheorems.add("INT_POW_LE ".trim());
		integerTheorems.add("INT_POW_LE2 ".trim());
		integerTheorems.add("INT_POW_LE_1 ".trim());
		integerTheorems.add("INT_POW_LT ".trim());
		integerTheorems.add("INT_POW_LT2 ".trim());
		integerTheorems.add("INT_POW_MONO ".trim());
		integerTheorems.add("INT_POW_MONO_LT ".trim());
		integerTheorems.add("INT_POW_MUL ".trim());
		integerTheorems.add("INT_POW_NEG ".trim());
		integerTheorems.add("INT_POW_NZ ".trim());
		integerTheorems.add("INT_POW_ONE ".trim());
		integerTheorems.add("INT_POW_POW ".trim());
		integerTheorems.add("INT_RNEG_UNIQ ".trim());
		integerTheorems.add("INT_SUB ".trim());
		integerTheorems.add("INT_SUB_0 ".trim());
		integerTheorems.add("INT_SUB_ABS ".trim());
		integerTheorems.add("INT_SUB_ADD ".trim());
		integerTheorems.add("INT_SUB_ADD2 ".trim());
		integerTheorems.add("INT_SUB_LDISTRIB ".trim());
		integerTheorems.add("INT_SUB_LE ".trim());
		integerTheorems.add("INT_SUB_LNEG ".trim());
		integerTheorems.add("INT_SUB_LT ".trim());
		integerTheorems.add("INT_SUB_LZERO ".trim());
		integerTheorems.add("INT_SUB_NEG2 ".trim());
		integerTheorems.add("INT_SUB_REFL ".trim());
		integerTheorems.add("INT_SUB_RNEG ".trim());
		integerTheorems.add("INT_SUB_RZERO ".trim());
		integerTheorems.add("INT_SUB_SUB ".trim());
		integerTheorems.add("INT_SUB_SUB2 ".trim());
		integerTheorems.add("INT_SUB_TRIANGLE ".trim());
		integerTheorems.add("NUM_GCD ".trim());
		integerTheorems.add("NUM_OF_INT ".trim());
		integerTheorems.add("NUM_OF_INT_OF_NUM ".trim());
		integerTheorems.add("int_congruent ".trim());
		integerTheorems.add("int_coprime ".trim());
		integerTheorems.add("int_divides ".trim());
		integerTheorems.add("int_gcd ".trim());
		integerTheorems.add("int_mod ".trim());
		integerTheorems.add("num_congruent ".trim());
		integerTheorems.add("num_coprime ".trim());
		integerTheorems.add("num_divides".trim());
		integerTheorems.add("num_gcd".trim());
		integerTheorems.add("num_mod".trim());

		

		setAndFunctionTheorems.add("ABSORPTION ".trim());
		setAndFunctionTheorems.add("BIJ".trim());
		setAndFunctionTheorems.add("BIJECTIONS_CARD_EQ ".trim());
		setAndFunctionTheorems.add("BIJECTIONS_HAS_SIZE ".trim());
		setAndFunctionTheorems.add("BIJECTIONS_HAS_SIZE_EQ ".trim());
		setAndFunctionTheorems.add("CARD".trim());
		setAndFunctionTheorems.add("CARD_CLAUSES ".trim());
		setAndFunctionTheorems.add("CARD_CROSS ".trim());
		setAndFunctionTheorems.add("CARD_DELETE ".trim());
		setAndFunctionTheorems.add("CARD_EQ ".trim());
		setAndFunctionTheorems.add("CARD_EQ_0 ".trim());
		setAndFunctionTheorems.add("CARD_EQ_BIJECTION ".trim());
		setAndFunctionTheorems.add("CARD_EQ_BIJECTIONS ".trim());
		setAndFunctionTheorems.add("CARD_FUNSPACE ".trim());
		setAndFunctionTheorems.add("CARD_GE ".trim());
		setAndFunctionTheorems.add("CARD_GE_REFL ".trim());
		setAndFunctionTheorems.add("CARD_GE_TRANS ".trim());
		setAndFunctionTheorems.add("CARD_GT ".trim());
		setAndFunctionTheorems.add("CARD_IMAGE_INJ ".trim());
		setAndFunctionTheorems.add("CARD_IMAGE_INJ_EQ ".trim());
		setAndFunctionTheorems.add("CARD_IMAGE_LE ".trim());
		setAndFunctionTheorems.add("CARD_LE ".trim());
		setAndFunctionTheorems.add("CARD_LE_INJ ".trim());
		setAndFunctionTheorems.add("CARD_LT ".trim());
		setAndFunctionTheorems.add("CARD_NUMSEG ".trim());
		setAndFunctionTheorems.add("CARD_NUMSEG_1 ".trim());
		setAndFunctionTheorems.add("CARD_NUMSEG_LE ".trim());
		setAndFunctionTheorems.add("CARD_NUMSEG_LEMMA ".trim());
		setAndFunctionTheorems.add("CARD_NUMSEG_LT ".trim());
		setAndFunctionTheorems.add("CARD_POWERSET ".trim());
		setAndFunctionTheorems.add("CARD_PRODUCT ".trim());
		setAndFunctionTheorems.add("CARD_PSUBSET ".trim());
		setAndFunctionTheorems.add("CARD_SUBSET ".trim());
		setAndFunctionTheorems.add("CARD_SUBSET_EQ ".trim());
		setAndFunctionTheorems.add("CARD_SUBSET_LE ".trim());
		setAndFunctionTheorems.add("CARD_UNION".trim());
		setAndFunctionTheorems.add("CARD_UNIONS_LE ".trim());
		setAndFunctionTheorems.add("CARD_UNION_EQ ".trim());
		setAndFunctionTheorems.add("CARD_UNION_LE ".trim());
		setAndFunctionTheorems.add("CHOICE ".trim());
		setAndFunctionTheorems.add("CHOICE_DEF ".trim());
		setAndFunctionTheorems.add("CHOOSE_SUBSET ".trim());
		setAndFunctionTheorems.add("COMPONENT ".trim());
		setAndFunctionTheorems.add("COUNTABLE ".trim());
		setAndFunctionTheorems.add("CROSS ".trim());
		setAndFunctionTheorems.add("DECOMPOSITION ".trim());
		setAndFunctionTheorems.add("DELETE ".trim());
		setAndFunctionTheorems.add("DELETE_COMM ".trim());
		setAndFunctionTheorems.add("DELETE_DELETE ".trim());
		setAndFunctionTheorems.add("DELETE_INSERT ".trim());
		setAndFunctionTheorems.add("DELETE_INTER ".trim());
		setAndFunctionTheorems.add("DELETE_NON_ELEMENT ".trim());
		setAndFunctionTheorems.add("DELETE_SUBSET ".trim());
		setAndFunctionTheorems.add("DIFF".trim());
		setAndFunctionTheorems.add("DIFF_DIFF ".trim());
		setAndFunctionTheorems.add("DIFF_EMPTY ".trim());
		setAndFunctionTheorems.add("DIFF_EQ_EMPTY ".trim());
		setAndFunctionTheorems.add("DIFF_INSERT ".trim());
		setAndFunctionTheorems.add("DIFF_UNIV ".trim());
		setAndFunctionTheorems.add("DISJOINT ".trim());
		setAndFunctionTheorems.add("DISJOINT_DELETE_SYM ".trim());
		setAndFunctionTheorems.add("DISJOINT_EMPTY ".trim());
		setAndFunctionTheorems.add("DISJOINT_EMPTY_REFL ".trim());
		setAndFunctionTheorems.add("DISJOINT_INSERT ".trim());
		setAndFunctionTheorems.add("DISJOINT_NUMSEG ".trim());
		setAndFunctionTheorems.add("DISJOINT_SYM ".trim());
		setAndFunctionTheorems.add("DISJOINT_UNION ".trim());
		setAndFunctionTheorems.add("EMPTY ".trim());
		setAndFunctionTheorems.add("EMPTY_DELETE ".trim());
		setAndFunctionTheorems.add("EMPTY_DIFF ".trim());
		setAndFunctionTheorems.add("EMPTY_GSPEC ".trim());
		setAndFunctionTheorems.add("EMPTY_NOT_UNIV ".trim());
		setAndFunctionTheorems.add("EMPTY_SUBSET ".trim());
		setAndFunctionTheorems.add("EMPTY_UNION ".trim());
		setAndFunctionTheorems.add("EMPTY_UNIONS ".trim());
		setAndFunctionTheorems.add("EQ_UNIV ".trim());
		setAndFunctionTheorems.add("EXISTS_IN_CLAUSES ".trim());
		setAndFunctionTheorems.add("EXISTS_IN_IMAGE ".trim());
		setAndFunctionTheorems.add("EXTENSION ".trim());
		setAndFunctionTheorems.add("FINITE_CASES ".trim());
		setAndFunctionTheorems.add("FINITE_CROSS ".trim());
		setAndFunctionTheorems.add("FINITE_DELETE ".trim());
		setAndFunctionTheorems.add("FINITE_DELETE_IMP ".trim());
		setAndFunctionTheorems.add("FINITE_DIFF ".trim());
		setAndFunctionTheorems.add("FINITE_FUNSPACE ".trim());
		setAndFunctionTheorems.add("FINITE_HAS_SIZE_LEMMA ".trim());
		setAndFunctionTheorems.add("FINITE_IMAGE ".trim());
		setAndFunctionTheorems.add("FINITE_IMAGE_EXPAND ".trim());
		setAndFunctionTheorems.add("FINITE_IMAGE_INJ ".trim());
		setAndFunctionTheorems.add("FINITE_IMAGE_INJ_EQ ".trim());
		setAndFunctionTheorems.add("FINITE_IMAGE_INJ_GENERAL ".trim());
		setAndFunctionTheorems.add("FINITE_INDEX_NUMBERS ".trim());
		setAndFunctionTheorems.add("FINITE_INDEX_NUMSEG ".trim());
		setAndFunctionTheorems.add("FINITE_INDUCT ".trim());
		setAndFunctionTheorems.add("FINITE_INDUCT_DELETE ".trim());
		setAndFunctionTheorems.add("FINITE_INDUCT_STRONG ".trim());
		setAndFunctionTheorems.add("FINITE_INSERT ".trim());
		setAndFunctionTheorems.add("FINITE_INTER ".trim());
		setAndFunctionTheorems.add("FINITE_NUMSEG ".trim());
		setAndFunctionTheorems.add("FINITE_NUMSEG_LE ".trim());
		setAndFunctionTheorems.add("FINITE_NUMSEG_LT ".trim());
		setAndFunctionTheorems.add("FINITE_POWERSET ".trim());
		setAndFunctionTheorems.add("FINITE_PRODUCT ".trim());
		setAndFunctionTheorems.add("FINITE_PRODUCT_DEPENDENT ".trim());
		setAndFunctionTheorems.add("FINITE_RECURSION ".trim());
		setAndFunctionTheorems.add("FINITE_RECURSION_DELETE ".trim());
		setAndFunctionTheorems.add("FINITE_RESTRICT ".trim());
		setAndFunctionTheorems.add("FINITE_RULES ".trim());
		setAndFunctionTheorems.add("FINITE_SET_OF_LIST ".trim());
		setAndFunctionTheorems.add("FINITE_SUBSET ".trim());
		setAndFunctionTheorems.add("FINITE_SUBSETS ".trim());
		setAndFunctionTheorems.add("FINITE_SUBSET_IMAGE ".trim());
		setAndFunctionTheorems.add("FINITE_SUBSET_IMAGE_IMP ".trim());
		setAndFunctionTheorems.add("FINITE_UNION ".trim());
		setAndFunctionTheorems.add("FINITE_UNIONS ".trim());
		setAndFunctionTheorems.add("FINITE_UNION_IMP ".trim());
		setAndFunctionTheorems.add("FINREC ".trim());
		setAndFunctionTheorems.add("FINREC_1_LEMMA ".trim());
		setAndFunctionTheorems.add("FINREC_EXISTS_LEMMA ".trim());
		setAndFunctionTheorems.add("FINREC_FUN ".trim());
		setAndFunctionTheorems.add("FINREC_FUN_LEMMA ".trim());
		setAndFunctionTheorems.add("FINREC_SUC_LEMMA ".trim());
		setAndFunctionTheorems.add("FINREC_UNIQUE_LEMMA ".trim());
		setAndFunctionTheorems.add("FORALL_IN_CLAUSES ".trim());
		setAndFunctionTheorems.add("FORALL_IN_IMAGE ".trim());
		setAndFunctionTheorems.add("FORALL_IN_UNIONS ".trim());
		setAndFunctionTheorems.add("FUNCTION_FACTORS_LEFT ".trim());
		setAndFunctionTheorems.add("FUNCTION_FACTORS_RIGHT ".trim());
		setAndFunctionTheorems.add("GSPEC ".trim());
		setAndFunctionTheorems.add("HAS_SIZE ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_0 ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_CARD ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_CLAUSES ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_CROSS ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_FUNSPACE ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_IMAGE_INJ ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_INDEX ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_NUMSEG ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_NUMSEG_1 ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_NUMSEG_LE ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_NUMSEG_LT ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_POWERSET ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_PRODUCT ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_PRODUCT_DEPENDENT ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_SUC ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_UNION ".trim());
		setAndFunctionTheorems.add("HAS_SIZE_UNIONS ".trim());
		setAndFunctionTheorems.add("IMAGE ".trim());
		setAndFunctionTheorems.add("IMAGE_CLAUSES ".trim());
		setAndFunctionTheorems.add("IMAGE_CONST ".trim());
		setAndFunctionTheorems.add("IMAGE_DELETE_INJ ".trim());
		setAndFunctionTheorems.add("IMAGE_DIFF_INJ ".trim());
		setAndFunctionTheorems.add("IMAGE_EQ_EMPTY ".trim());
		setAndFunctionTheorems.add("IMAGE_IMP_INJECTIVE ".trim());
		setAndFunctionTheorems.add("IMAGE_IMP_INJECTIVE_GEN ".trim());
		setAndFunctionTheorems.add("IMAGE_SUBSET ".trim());
		setAndFunctionTheorems.add("IMAGE_UNION ".trim());
		setAndFunctionTheorems.add("IMAGE_o ".trim());
		setAndFunctionTheorems.add("IN".trim());
		setAndFunctionTheorems.add("INFINITE ".trim());
		setAndFunctionTheorems.add("INFINITE_DIFF_FINITE ".trim());
		setAndFunctionTheorems.add("INFINITE_IMAGE_INJ ".trim());
		setAndFunctionTheorems.add("INFINITE_NONEMPTY ".trim());
		setAndFunctionTheorems.add("INJ".trim());
		setAndFunctionTheorems.add("INJECTIVE_LEFT_INVERSE ".trim());
		setAndFunctionTheorems.add("INJECTIVE_ON_LEFT_INVERSE ".trim());
		setAndFunctionTheorems.add("INSERT ".trim());
		setAndFunctionTheorems.add("INSERT_AC ".trim());
		setAndFunctionTheorems.add("INSERT_COMM ".trim());
		setAndFunctionTheorems.add("INSERT_DEF ".trim());
		setAndFunctionTheorems.add("INSERT_DELETE ".trim());
		setAndFunctionTheorems.add("INSERT_DIFF ".trim());
		setAndFunctionTheorems.add("INSERT_INSERT ".trim());
		setAndFunctionTheorems.add("INSERT_INTER ".trim());
		setAndFunctionTheorems.add("INSERT_SUBSET ".trim());
		setAndFunctionTheorems.add("INSERT_UNION ".trim());
		setAndFunctionTheorems.add("INSERT_UNION_EQ ".trim());
		setAndFunctionTheorems.add("INSERT_UNIV ".trim());
		setAndFunctionTheorems.add("INTER ".trim());
		setAndFunctionTheorems.add("INTERS ".trim());
		setAndFunctionTheorems.add("INTERS_0 ".trim());
		setAndFunctionTheorems.add("INTERS_1 ".trim());
		setAndFunctionTheorems.add("INTERS_2 ".trim());
		setAndFunctionTheorems.add("INTERS_INSERT ".trim());
		setAndFunctionTheorems.add("INTER_ACI ".trim());
		setAndFunctionTheorems.add("INTER_ASSOC ".trim());
		setAndFunctionTheorems.add("INTER_COMM ".trim());
		setAndFunctionTheorems.add("INTER_EMPTY ".trim());
		setAndFunctionTheorems.add("INTER_IDEMPOT ".trim());
		setAndFunctionTheorems.add("INTER_OVER_UNION ".trim());
		setAndFunctionTheorems.add("INTER_SUBSET ".trim());
		setAndFunctionTheorems.add("INTER_UNIV ".trim());
		setAndFunctionTheorems.add("IN_CROSS ".trim());
		setAndFunctionTheorems.add("IN_DELETE ".trim());
		setAndFunctionTheorems.add("IN_DELETE_EQ ".trim());
		setAndFunctionTheorems.add("IN_DIFF ".trim());
		setAndFunctionTheorems.add("IN_DISJOINT ".trim());
		setAndFunctionTheorems.add("IN_ELIM_PAIR_THM ".trim());
		setAndFunctionTheorems.add("IN_ELIM_THM ".trim());
		setAndFunctionTheorems.add("IN_IMAGE ".trim());
		setAndFunctionTheorems.add("IN_INSERT ".trim());
		setAndFunctionTheorems.add("IN_INTER ".trim());
		setAndFunctionTheorems.add("IN_INTERS ".trim());
		setAndFunctionTheorems.add("IN_NUMSEG ".trim());
		setAndFunctionTheorems.add("IN_REST ".trim());
		setAndFunctionTheorems.add("IN_SET_OF_LIST ".trim());
		setAndFunctionTheorems.add("IN_SING ".trim());
		setAndFunctionTheorems.add("IN_UNION ".trim());
		setAndFunctionTheorems.add("IN_UNIONS ".trim());
		setAndFunctionTheorems.add("IN_UNIV ".trim());
		setAndFunctionTheorems.add("ITSET ".trim());
		setAndFunctionTheorems.add("ITSET_EQ ".trim());
		setAndFunctionTheorems.add("LENGTH_LIST_OF_SET ".trim());
		setAndFunctionTheorems.add("LIST_OF_SET_PROPERTIES ".trim());
		setAndFunctionTheorems.add("MEMBER_NOT_EMPTY ".trim());
		setAndFunctionTheorems.add("MEM_LIST_OF_SET ".trim());
		setAndFunctionTheorems.add("NOT_EMPTY_INSERT ".trim());
		setAndFunctionTheorems.add("NOT_EQUAL_SETS ".trim());
		setAndFunctionTheorems.add("NOT_INSERT_EMPTY ".trim());
		setAndFunctionTheorems.add("NOT_IN_EMPTY ".trim());
		setAndFunctionTheorems.add("NOT_PSUBSET_EMPTY ".trim());
		setAndFunctionTheorems.add("NOT_UNIV_PSUBSET ".trim());
		setAndFunctionTheorems.add("NUMSEG_ADD_SPLIT ".trim());
		setAndFunctionTheorems.add("NUMSEG_CLAUSES ".trim());
		setAndFunctionTheorems.add("NUMSEG_COMBINE_L ".trim());
		setAndFunctionTheorems.add("NUMSEG_COMBINE_R ".trim());
		setAndFunctionTheorems.add("NUMSEG_EMPTY ".trim());
		setAndFunctionTheorems.add("NUMSEG_LREC ".trim());
		setAndFunctionTheorems.add("NUMSEG_OFFSET_IMAGE ".trim());
		setAndFunctionTheorems.add("NUMSEG_REC ".trim());
		setAndFunctionTheorems.add("NUMSEG_RREC ".trim());
		setAndFunctionTheorems.add("NUMSEG_SING ".trim());
		setAndFunctionTheorems.add("PAIRWISE ".trim());
		setAndFunctionTheorems.add("PSUBSET ".trim());
		setAndFunctionTheorems.add("PSUBSET_INSERT_SUBSET ".trim());
		setAndFunctionTheorems.add("PSUBSET_IRREFL ".trim());
		setAndFunctionTheorems.add("PSUBSET_MEMBER ".trim());
		setAndFunctionTheorems.add("PSUBSET_SUBSET_TRANS ".trim());
		setAndFunctionTheorems.add("PSUBSET_TRANS ".trim());
		setAndFunctionTheorems.add("PSUBSET_UNIV ".trim());
		setAndFunctionTheorems.add("REST".trim());
		setAndFunctionTheorems.add("SETSPEC ".trim());
		setAndFunctionTheorems.add("SET_CASES ".trim());
		setAndFunctionTheorems.add("SET_OF_LIST_APPEND ".trim());
		setAndFunctionTheorems.add("SET_OF_LIST_OF_SET ".trim());
		setAndFunctionTheorems.add("SET_RECURSION_LEMMA ".trim());
		setAndFunctionTheorems.add("SIMPLE_IMAGE ".trim());
		setAndFunctionTheorems.add("SING".trim());
		setAndFunctionTheorems.add("SUBSET ".trim());
		setAndFunctionTheorems.add("SUBSET_ANTISYM ".trim());
		setAndFunctionTheorems.add("SUBSET_DELETE ".trim());
		setAndFunctionTheorems.add("SUBSET_DIFF ".trim());
		setAndFunctionTheorems.add("SUBSET_EMPTY ".trim());
		setAndFunctionTheorems.add("SUBSET_IMAGE ".trim());
		setAndFunctionTheorems.add("SUBSET_INSERT ".trim());
		setAndFunctionTheorems.add("SUBSET_INSERT_DELETE ".trim());
		setAndFunctionTheorems.add("SUBSET_INTER_ABSORPTION ".trim());
		setAndFunctionTheorems.add("SUBSET_NUMSEG ".trim());
		setAndFunctionTheorems.add("SUBSET_PSUBSET_TRANS ".trim());
		setAndFunctionTheorems.add("SUBSET_REFL ".trim());
		setAndFunctionTheorems.add("SUBSET_RESTRICT ".trim());
		setAndFunctionTheorems.add("SUBSET_TRANS ".trim());
		setAndFunctionTheorems.add("SUBSET_UNION ".trim());
		setAndFunctionTheorems.add("SUBSET_UNION_ABSORPTION ".trim());
		setAndFunctionTheorems.add("SUBSET_UNIV ".trim());
		setAndFunctionTheorems.add("SURJ".trim());
		setAndFunctionTheorems.add("SURJECTIVE_IFF_INJECTIVE ".trim());
		setAndFunctionTheorems.add("SURJECTIVE_IFF_INJECTIVE_GEN ".trim());
		setAndFunctionTheorems.add("SURJECTIVE_ON_RIGHT_INVERSE ".trim());
		setAndFunctionTheorems.add("SURJECTIVE_RIGHT_INVERSE ".trim());
		setAndFunctionTheorems.add("UNION ".trim());
		setAndFunctionTheorems.add("UNIONS ".trim());
		setAndFunctionTheorems.add("UNIONS_0 ".trim());
		setAndFunctionTheorems.add("UNIONS_1 ".trim());
		setAndFunctionTheorems.add("UNIONS_2 ".trim());
		setAndFunctionTheorems.add("UNIONS_INSERT ".trim());
		setAndFunctionTheorems.add("UNION_ACI ".trim());
		setAndFunctionTheorems.add("UNION_ASSOC ".trim());
		setAndFunctionTheorems.add("UNION_COMM ".trim());
		setAndFunctionTheorems.add("UNION_EMPTY ".trim());
		setAndFunctionTheorems.add("UNION_IDEMPOT ".trim());
		setAndFunctionTheorems.add("UNION_OVER_INTER ".trim());
		setAndFunctionTheorems.add("UNION_SUBSET ".trim());
		setAndFunctionTheorems.add("UNION_UNIV ".trim());
		setAndFunctionTheorems.add("UNIV".trim());
		setAndFunctionTheorems.add("UNIV_NOT_EMPTY ".trim());
		setAndFunctionTheorems.add("UNIV_SUBSET ".trim());
		setAndFunctionTheorems.add("list_of_set ".trim());
		setAndFunctionTheorems.add("num_FINITE ".trim());
		setAndFunctionTheorems.add("num_FINITE_AVOID ".trim());
		setAndFunctionTheorems.add("num_INFINITE ".trim());
		setAndFunctionTheorems.add("numseg ".trim());
		setAndFunctionTheorems.add("pairwise ".trim());
		setAndFunctionTheorems.add("set_of_list ".trim());

		

		iteratedOperationTheorems.add("CARD_EQ_NSUM ".trim());
		iteratedOperationTheorems.add("CARD_EQ_SUM ".trim());
		iteratedOperationTheorems.add("FINITE_SUPPORT ".trim());
		iteratedOperationTheorems.add("FINITE_SUPPORT_DELTA ".trim());
		iteratedOperationTheorems.add("IN_SUPPORT ".trim());
		iteratedOperationTheorems.add("ITERATE_BIJECTION ".trim());
		iteratedOperationTheorems.add("ITERATE_CASES ".trim());
		iteratedOperationTheorems.add("ITERATE_CLAUSES ".trim());
		iteratedOperationTheorems.add("ITERATE_CLAUSES_GEN ".trim());
		iteratedOperationTheorems.add("ITERATE_CLOSED ".trim());
		iteratedOperationTheorems.add("ITERATE_CLOSED_GEN ".trim());
		iteratedOperationTheorems.add("ITERATE_DELETE ".trim());
		iteratedOperationTheorems.add("ITERATE_DELTA ".trim());
		iteratedOperationTheorems.add("ITERATE_DIFF ".trim());
		iteratedOperationTheorems.add("ITERATE_DIFF_GEN".trim());
		iteratedOperationTheorems.add("ITERATE_EQ ".trim());
		iteratedOperationTheorems.add("ITERATE_EQ_GENERAL ".trim());
		iteratedOperationTheorems.add("ITERATE_EQ_GENERAL_INVERSES ".trim());
		iteratedOperationTheorems.add("ITERATE_EQ_NEUTRAL ".trim());
		iteratedOperationTheorems.add("ITERATE_IMAGE ".trim());
		iteratedOperationTheorems.add("ITERATE_INJECTION ".trim());
		iteratedOperationTheorems.add("ITERATE_ITERATE_PRODUCT ".trim());
		iteratedOperationTheorems.add("ITERATE_RELATED ".trim());
		iteratedOperationTheorems.add("ITERATE_SING ".trim());
		iteratedOperationTheorems.add("ITERATE_SUPPORT ".trim());
		iteratedOperationTheorems.add("ITERATE_UNION ".trim());
		iteratedOperationTheorems.add("ITERATE_UNION_GEN ".trim());
		iteratedOperationTheorems.add("MONOIDAL_ADD ".trim());
		iteratedOperationTheorems.add("MONOIDAL_MUL ".trim());
		iteratedOperationTheorems.add("MONOIDAL_REAL_ADD ".trim());
		iteratedOperationTheorems.add("MONOIDAL_REAL_MUL ".trim());
		iteratedOperationTheorems.add("NEUTRAL_ADD ".trim());
		iteratedOperationTheorems.add("NEUTRAL_MUL ".trim());
		iteratedOperationTheorems.add("NEUTRAL_REAL_ADD ".trim());
		iteratedOperationTheorems.add("NEUTRAL_REAL_MUL ".trim());
		iteratedOperationTheorems.add("NSUM_0 ".trim());
		iteratedOperationTheorems.add("NSUM_ADD ".trim());
		iteratedOperationTheorems.add("NSUM_ADD_NUMSEG ".trim());
		iteratedOperationTheorems.add("NSUM_ADD_SPLIT ".trim());
		iteratedOperationTheorems.add("NSUM_BIJECTION ".trim());
		iteratedOperationTheorems.add("NSUM_BOUND ".trim());
		iteratedOperationTheorems.add("NSUM_BOUND_GEN ".trim());
		iteratedOperationTheorems.add("NSUM_BOUND_LT ".trim());
		iteratedOperationTheorems.add("NSUM_BOUND_LT_ALL ".trim());
		iteratedOperationTheorems.add("NSUM_BOUND_LT_GEN ".trim());
		iteratedOperationTheorems.add("NSUM_CLAUSES ".trim());
		iteratedOperationTheorems.add("NSUM_CLAUSES_LEFT ".trim());
		iteratedOperationTheorems.add("NSUM_CLAUSES_NUMSEG ".trim());
		iteratedOperationTheorems.add("NSUM_CLAUSES_RIGHT ".trim());
		iteratedOperationTheorems.add("NSUM_CONST ".trim());
		iteratedOperationTheorems.add("NSUM_CONST_NUMSEG ".trim());
		iteratedOperationTheorems.add("NSUM_DELETE ".trim());
		iteratedOperationTheorems.add("NSUM_DELTA ".trim());
		iteratedOperationTheorems.add("NSUM_DIFF ".trim());
		iteratedOperationTheorems.add("NSUM_EQ ".trim());
		iteratedOperationTheorems.add("NSUM_EQ_0 ".trim());
		iteratedOperationTheorems.add("NSUM_EQ_0_IFF ".trim());
		iteratedOperationTheorems.add("NSUM_EQ_0_IFF_NUMSEG ".trim());
		iteratedOperationTheorems.add("NSUM_EQ_0_NUMSEG ".trim());
		iteratedOperationTheorems.add("NSUM_EQ_GENERAL ".trim());
		iteratedOperationTheorems.add("NSUM_EQ_GENERAL_INVERSES ".trim());
		iteratedOperationTheorems.add("NSUM_EQ_NUMSEG ".trim());
		iteratedOperationTheorems.add("NSUM_EQ_SUPERSET ".trim());
		iteratedOperationTheorems.add("NSUM_IMAGE ".trim());
		iteratedOperationTheorems.add("NSUM_IMAGE_GEN ".trim());
		iteratedOperationTheorems.add("NSUM_INJECTION ".trim());
		iteratedOperationTheorems.add("NSUM_LE ".trim());
		iteratedOperationTheorems.add("NSUM_LE_NUMSEG ".trim());
		iteratedOperationTheorems.add("NSUM_LMUL ".trim());
		iteratedOperationTheorems.add("NSUM_LT ".trim());
		iteratedOperationTheorems.add("NSUM_LT_ALL ".trim());
		iteratedOperationTheorems.add("NSUM_MULTICOUNT ".trim());
		iteratedOperationTheorems.add("NSUM_MULTICOUNT_GEN ".trim());
		iteratedOperationTheorems.add("NSUM_NSUM_PRODUCT ".trim());
		iteratedOperationTheorems.add("NSUM_NSUM_RESTRICT ".trim());
		iteratedOperationTheorems.add("NSUM_OFFSET ".trim());
		iteratedOperationTheorems.add("NSUM_OFFSET_0 ".trim());
		iteratedOperationTheorems.add("NSUM_POS_BOUND ".trim());
		iteratedOperationTheorems.add("NSUM_RESTRICT ".trim());
		iteratedOperationTheorems.add("NSUM_RESTRICT_SET ".trim());
		iteratedOperationTheorems.add("NSUM_RMUL ".trim());
		iteratedOperationTheorems.add("NSUM_SING ".trim());
		iteratedOperationTheorems.add("NSUM_SING_NUMSEG ".trim());
		iteratedOperationTheorems.add("NSUM_SUBSET ".trim());
		iteratedOperationTheorems.add("NSUM_SUBSET_SIMPLE ".trim());
		iteratedOperationTheorems.add("NSUM_SUPERSET ".trim());
		iteratedOperationTheorems.add("NSUM_SUPPORT ".trim());
		iteratedOperationTheorems.add("NSUM_SWAP ".trim());
		iteratedOperationTheorems.add("NSUM_SWAP_NUMSEG ".trim());
		iteratedOperationTheorems.add("NSUM_TRIV_NUMSEG ".trim());
		iteratedOperationTheorems.add("NSUM_UNION ".trim());
		iteratedOperationTheorems.add("NSUM_UNION_EQ ".trim());
		iteratedOperationTheorems.add("NSUM_UNION_LZERO ".trim());
		iteratedOperationTheorems.add("NSUM_UNION_RZERO ".trim());
		iteratedOperationTheorems.add("REAL_OF_NUM_SUM ".trim());
		iteratedOperationTheorems.add("REAL_OF_NUM_SUM_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_0 ".trim());
		iteratedOperationTheorems.add("SUM_ABS ".trim());
		iteratedOperationTheorems.add("SUM_ABS_BOUND ".trim());
		iteratedOperationTheorems.add("SUM_ABS_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_ADD ".trim());
		iteratedOperationTheorems.add("SUM_ADD_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_ADD_SPLIT ".trim());
		iteratedOperationTheorems.add("SUM_BIJECTION ".trim());
		iteratedOperationTheorems.add("SUM_BOUND ".trim());
		iteratedOperationTheorems.add("SUM_BOUND_GEN ".trim());
		iteratedOperationTheorems.add("SUM_BOUND_LT ".trim());
		iteratedOperationTheorems.add("SUM_BOUND_LT_ALL ".trim());
		iteratedOperationTheorems.add("SUM_BOUND_LT_GEN ".trim());
		iteratedOperationTheorems.add("SUM_CLAUSES ".trim());
		iteratedOperationTheorems.add("SUM_CLAUSES_LEFT ".trim());
		iteratedOperationTheorems.add("SUM_CLAUSES_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_CLAUSES_RIGHT ".trim());
		iteratedOperationTheorems.add("SUM_CONST ".trim());
		iteratedOperationTheorems.add("SUM_CONST_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_DELETE ".trim());
		iteratedOperationTheorems.add("SUM_DELTA ".trim());
		iteratedOperationTheorems.add("SUM_DIFF ".trim());
		iteratedOperationTheorems.add("SUM_EQ ".trim());
		iteratedOperationTheorems.add("SUM_EQ_0 ".trim());
		iteratedOperationTheorems.add("SUM_EQ_0_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_EQ_GENERAL ".trim());
		iteratedOperationTheorems.add("SUM_EQ_GENERAL_INVERSES ".trim());
		iteratedOperationTheorems.add("SUM_EQ_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_EQ_SUPERSET".trim());
		iteratedOperationTheorems.add("SUM_IMAGE ".trim());
		iteratedOperationTheorems.add("SUM_IMAGE_GEN ".trim());
		iteratedOperationTheorems.add("SUM_INJECTION ".trim());
		iteratedOperationTheorems.add("SUM_LE ".trim());
		iteratedOperationTheorems.add("SUM_LE_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_LMUL ".trim());
		iteratedOperationTheorems.add("SUM_LT ".trim());
		iteratedOperationTheorems.add("SUM_LT_ALL ".trim());
		iteratedOperationTheorems.add("SUM_MULTICOUNT ".trim());
		iteratedOperationTheorems.add("SUM_MULTICOUNT_GEN ".trim());
		iteratedOperationTheorems.add("SUM_NEG ".trim());
		iteratedOperationTheorems.add("SUM_OFFSET ".trim());
		iteratedOperationTheorems.add("SUM_OFFSET_0 ".trim());
		iteratedOperationTheorems.add("SUM_POS_BOUND ".trim());
		iteratedOperationTheorems.add("SUM_POS_EQ_0 ".trim());
		iteratedOperationTheorems.add("SUM_POS_EQ_0_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_POS_LE ".trim());
		iteratedOperationTheorems.add("SUM_POS_LE_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_RESTRICT ".trim());
		iteratedOperationTheorems.add("SUM_RESTRICT_SET ".trim());
		iteratedOperationTheorems.add("SUM_RMUL".trim());
		iteratedOperationTheorems.add("SUM_SING".trim());
		iteratedOperationTheorems.add("SUM_SING_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_SUB ".trim());
		iteratedOperationTheorems.add("SUM_SUBSET ".trim());
		iteratedOperationTheorems.add("SUM_SUBSET_SIMPLE ".trim());
		iteratedOperationTheorems.add("SUM_SUB_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_SUM_PRODUCT ".trim());
		iteratedOperationTheorems.add("SUM_SUM_RESTRICT ".trim());
		iteratedOperationTheorems.add("SUM_SUPERSET ".trim());
		iteratedOperationTheorems.add("SUM_SUPPORT ".trim());
		iteratedOperationTheorems.add("SUM_SWAP ".trim());
		iteratedOperationTheorems.add("SUM_SWAP_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_TRIV_NUMSEG ".trim());
		iteratedOperationTheorems.add("SUM_UNION ".trim());
		iteratedOperationTheorems.add("SUM_UNION_EQ ".trim());
		iteratedOperationTheorems.add("SUM_UNION_LZERO ".trim());
		iteratedOperationTheorems.add("SUM_UNION_RZERO ".trim());
		iteratedOperationTheorems.add("SUPPORT_CLAUSES ".trim());
		iteratedOperationTheorems.add("SUPPORT_DELTA".trim());
		iteratedOperationTheorems.add("SUPPORT_EMPTY ".trim());
		iteratedOperationTheorems.add("SUPPORT_SUBSET ".trim());
		iteratedOperationTheorems.add("SUPPORT_SUPPORT ".trim());
		iteratedOperationTheorems.add("iterate ".trim());
		iteratedOperationTheorems.add("monoidal ".trim());
		iteratedOperationTheorems.add("neutral ".trim());
		iteratedOperationTheorems.add("nsum".trim());
		iteratedOperationTheorems.add("sum".trim());
		iteratedOperationTheorems.add("support ".trim());

		
		cartesianPowerTheorems.add("CARD_FINITE_IMAGE ".trim());
		cartesianPowerTheorems.add("CART_EQ ".trim());
		cartesianPowerTheorems.add("DIMINDEX_1 ".trim());
		cartesianPowerTheorems.add("DIMINDEX_2 ".trim());
		cartesianPowerTheorems.add("DIMINDEX_3 ".trim());
		cartesianPowerTheorems.add("DIMINDEX_FINITE_IMAGE ".trim());
		cartesianPowerTheorems.add("DIMINDEX_FINITE_SUM ".trim());
		cartesianPowerTheorems.add("DIMINDEX_GE_1 ".trim());
		cartesianPowerTheorems.add("DIMINDEX_HAS_SIZE_FINITE_SUM ".trim());
		cartesianPowerTheorems.add("DIMINDEX_NONZERO ".trim());
		cartesianPowerTheorems.add("DIMINDEX_UNIQUE ".trim());
		cartesianPowerTheorems.add("DIMINDEX_UNIV ".trim());
		cartesianPowerTheorems.add("EXISTS_PASTECART ".trim());
		cartesianPowerTheorems.add("FINITE_FINITE_IMAGE ".trim());
		cartesianPowerTheorems.add("FINITE_IMAGE_IMAGE ".trim());
		cartesianPowerTheorems.add("FINITE_INDEX_INJ ".trim());
		cartesianPowerTheorems.add("FINITE_INDEX_WORKS ".trim());
		cartesianPowerTheorems.add("FINITE_SUM_IMAGE ".trim());
		cartesianPowerTheorems.add("FORALL_FINITE_INDEX ".trim());
		cartesianPowerTheorems.add("FORALL_PASTECART ".trim());
		cartesianPowerTheorems.add("FSTCART_PASTECART ".trim());
		cartesianPowerTheorems.add("HAS_SIZE_1 ".trim());
		cartesianPowerTheorems.add("HAS_SIZE_2 ".trim());
		cartesianPowerTheorems.add("HAS_SIZE_3 ".trim());
		cartesianPowerTheorems.add("HAS_SIZE_FINITE_IMAGE ".trim());
		cartesianPowerTheorems.add("LAMBDA_BETA ".trim());
		cartesianPowerTheorems.add("LAMBDA_ETA ".trim());
		cartesianPowerTheorems.add("LAMBDA_UNIQUE ".trim());
		cartesianPowerTheorems.add("PASTECART_EQ ".trim());
		cartesianPowerTheorems.add("PASTECART_FST_SND ".trim());
		cartesianPowerTheorems.add("SNDCART_PASTECART ".trim());
		cartesianPowerTheorems.add("cart_tybij ".trim());
		cartesianPowerTheorems.add("dimindex ".trim());
		cartesianPowerTheorems.add("finite_image_tybij ".trim());
		cartesianPowerTheorems.add("finite_index ".trim());
		cartesianPowerTheorems.add("finite_sum_tybij ".trim());
		cartesianPowerTheorems.add("fstcart ".trim());
		cartesianPowerTheorems.add("lambda ".trim());
		cartesianPowerTheorems.add("pastecart ".trim());
		cartesianPowerTheorems.add("sndcart".trim()); 
		//end of theorem labels

	}

}
