open Hol_core
open Num
	val arith_base : int
    val num_def : thm
    val NUM_THM : thm
    val num_const : term
    val const_array : term array
    val def_array: thm array
    val def_thm_array: thm array
    val mk_numeral_hash : num -> term
    val mk_numeral_array : num -> term
    val mk_small_numeral_array : int -> term
    val raw_dest_hash : term -> num
    val dest_numeral_hash : term -> num
    val NUMERAL_TO_NUM_CONV : term -> thm
    val NUM_TO_NUMERAL_CONV : term -> thm
	(* SUC *)
    val raw_suc_conv_hash : term -> thm
    val NUM_SUC_HASH_CONV : term -> thm
	(* eq0 *)
    val raw_eq0_hash_conv : term -> thm
    val NUM_EQ0_HASH_CONV : term -> thm
	(* PRE *)
    val raw_pre_hash_conv : term -> thm
    val NUM_PRE_HASH_CONV : term -> thm
	(* gt0 *)
    val raw_gt0_hash_conv : term -> thm
    val NUM_GT0_HASH_CONV : term -> thm
	(* eq *)
	val raw_eq_hash_conv : term -> thm
	val NUM_EQ_HASH_CONV : term -> thm
	(* lt, le *)
    val raw_lt_hash_conv : term -> thm
    val raw_le_hash_conv : term -> thm
    val NUM_LT_HASH_CONV : term -> thm
    val NUM_LE_HASH_CONV : term -> thm
	(* add *)
    val raw_add_conv_hash : term -> thm
    val NUM_ADD_HASH_CONV : term -> thm
	(* sub *)
    val raw_sub_hash_conv : term -> thm
    val raw_sub_and_le_hash_conv : term -> term -> thm * thm
    val NUM_SUB_HASH_CONV : term -> thm
	(* mul *)
    val raw_mul_conv_hash : term -> thm
    val NUM_MULT_HASH_CONV : term -> thm
	(* DIV *)
    val raw_div_hash_conv : term -> thm
    val NUM_DIV_HASH_CONV : term -> thm
	(* EVEN, ODD *)
    val raw_even_hash_conv : term -> thm
    val raw_odd_hash_conv : term -> thm
    val NUM_EVEN_HASH_CONV : term -> thm
    val NUM_ODD_HASH_CONV : term -> thm
