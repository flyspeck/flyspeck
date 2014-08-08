open Hol_core
open Num
    type ifloat
    val min_exp : int
    val print_ifloat_fmt : Format.formatter -> ifloat -> unit
    val print_ifloat : ifloat -> unit
    val mk_float : Num.num -> int -> ifloat
    val mk_num_float : Num.num -> ifloat
    val mk_small_num_float : int -> ifloat
    val dest_float : ifloat -> bool * Num.num * int
    val num_of_ifloat : ifloat -> Num.num
    val float_of_ifloat : ifloat -> float
    val sign_float : ifloat -> bool
      (* Compares representations, not numbers themselves *)
    val eq_float : ifloat -> ifloat -> bool
    val lo_float : int -> ifloat -> ifloat
    val hi_float : int -> ifloat -> ifloat
    val neg_float : ifloat -> ifloat
    val abs_float : ifloat -> ifloat
    val lt0_float : ifloat -> bool
    val gt0_float : ifloat -> bool
    val le0_float : ifloat -> bool
    val ge0_float : ifloat -> bool
    val lt_float : ifloat -> ifloat -> bool
    val le_float : ifloat -> ifloat -> bool
    val min_float : ifloat -> ifloat -> ifloat
    val max_float : ifloat -> ifloat -> ifloat
    val mul_float_eq : ifloat -> ifloat -> ifloat
    val mul_float_lo : int -> ifloat -> ifloat -> ifloat
    val mul_float_hi : int -> ifloat -> ifloat -> ifloat
    val div_float_lo : int -> ifloat -> ifloat -> ifloat
    val div_float_hi : int -> ifloat -> ifloat -> ifloat
    val add_float_lo : int -> ifloat -> ifloat -> ifloat
    val add_float_hi : int -> ifloat -> ifloat -> ifloat
    val sub_float_lo : int -> ifloat -> ifloat -> ifloat
    val sub_float_hi : int -> ifloat -> ifloat -> ifloat
    val sqrt_float_lo : int -> ifloat -> ifloat
    val sqrt_float_hi : int -> ifloat -> ifloat
