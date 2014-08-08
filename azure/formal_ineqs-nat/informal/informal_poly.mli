open Hol_core
open Num
    val eval_interval_poly_f : int -> Informal_interval.interval list -> Informal_interval.interval -> Informal_interval.interval
    val eval_high_poly_f_pos_pos : int -> Informal_interval.interval list -> Informal_float.ifloat -> Informal_float.ifloat
    val eval_low_poly_f_pos_pos : int -> Informal_interval.interval list -> Informal_float.ifloat -> Informal_float.ifloat
    val eval_pow2_high : int -> Informal_float.ifloat -> Informal_float.ifloat
    val eval_pow2_low : int -> Informal_float.ifloat -> Informal_float.ifloat
    val eval_pow4_high : int -> Informal_float.ifloat -> Informal_float.ifloat
    val eval_pow4_low : int -> Informal_float.ifloat -> Informal_float.ifloat
    val eval_pow2_pow4_high : int -> Informal_float.ifloat -> Informal_float.ifloat * Informal_float.ifloat
    val eval_pow2_pow4_low : int -> Informal_float.ifloat -> Informal_float.ifloat * Informal_float.ifloat
