open Hol_core
open Num
    val mk_num_exp : term -> term -> term
    val dest_num_exp : term -> (term * term)
    val dest_float : term -> (string * term * term)
    val float_lt0 : term -> thm
    val float_gt0 : term -> thm
    val float_lt : term -> term -> thm
    val float_le0 : term -> thm
    val float_ge0 : term -> thm
    val float_le : term -> term -> thm
    val float_min : term -> term -> thm
    val float_max : term -> term -> thm
    val float_min_max : term -> term -> (thm * thm)
    val float_mul_eq : term -> term -> thm
    val float_mul_lo : int -> term -> term -> thm
    val float_mul_hi : int -> term -> term -> thm
    val float_div_lo : int -> term -> term -> thm
    val float_div_hi : int -> term -> term -> thm
    val float_add_lo : int -> term -> term -> thm
    val float_add_hi : int -> term -> term -> thm
    val float_sub_lo : int -> term -> term -> thm
    val float_sub_hi : int -> term -> term -> thm
    val float_sqrt_lo : int -> term -> thm
    val float_sqrt_hi : int -> term -> thm

    val float_prove_le : term -> term -> bool * thm
    val float_prove_lt : term -> term -> bool * thm
    val float_prove_le_interval : term -> thm -> bool * thm
    val float_prove_ge_interval : term -> thm -> bool * thm
    val float_prove_lt_interval : term -> thm -> bool * thm
    val float_prove_gt_interval : term -> thm -> bool * thm
    val float_compare_interval : term -> thm -> int * thm

    val reset_stat : unit -> unit
    val reset_cache : unit -> unit
    val print_stat : unit -> unit

    val dest_float_interval : term -> term * term * term
    val mk_float_interval_small_num : int -> thm
    val mk_float_interval_num : num -> thm

    val float_lo : int -> term -> thm
    val float_hi : int -> term -> thm

    val float_interval_round : int -> thm -> thm

    val float_interval_neg : thm -> thm
    val float_interval_mul : int -> thm -> thm -> thm
    val float_interval_div : int -> thm -> thm -> thm
    val float_interval_add : int -> thm -> thm -> thm
    val float_interval_sub : int -> thm -> thm -> thm
    val float_interval_sqrt : int -> thm -> thm

    val float_abs : term -> thm
	
    val FLOAT_TO_NUM_CONV : term -> thm
