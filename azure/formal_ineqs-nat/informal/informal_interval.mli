open Hol_core
open Num
    type interval
    val print_interval_fmt : Format.formatter -> interval -> unit
    val print_interval : interval -> unit
    val zero_interval : interval
    val one_interval : interval
    val two_interval : interval
    val mk_interval : Informal_float.ifloat * Informal_float.ifloat -> interval
    val mk_num_interval : num -> interval
    val mk_small_num_interval : int -> interval
    val dest_interval : interval -> Informal_float.ifloat * Informal_float.ifloat
    val round_interval : int -> interval -> interval
    val neg_interval : interval -> interval
    val mul_interval : int -> interval -> interval -> interval
    val div_interval : int -> interval -> interval -> interval
    val add_interval : int -> interval -> interval -> interval
    val sub_interval : int -> interval -> interval -> interval
    val sqrt_interval : int -> interval -> interval
    val inv_interval : int -> interval -> interval
    val pow_interval : int -> int -> interval -> interval
      (* Computes max(-lo, hi) *)
    val abs_interval : interval -> Informal_float.ifloat
      (* Compares a floating-point value and an interval *)
    val le_interval : Informal_float.ifloat -> interval -> bool
    val ge_interval : Informal_float.ifloat -> interval -> bool
    val compare_interval : Informal_float.ifloat -> interval -> int
