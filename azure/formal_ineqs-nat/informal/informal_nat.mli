open Hol_core
open Num
    type nat
    val arith_base : int
    val mk_nat : num -> nat
    val mk_small_nat : int -> nat
    val dest_nat : nat -> num
    val eq_nat : nat -> nat -> bool
    val suc_nat : nat -> nat
    val pre_nat : nat -> nat
    val eq0_nat : nat -> bool
    val gt0_nat : nat -> bool
    val lt_nat : nat -> nat -> bool
    val le_nat : nat -> nat -> bool
    val add_nat : nat -> nat -> nat
    val sub_nat : nat -> nat -> nat
    (* If sub_and_le_nat m n = (m - n, true) if n <= m; (n - m, false) if m < n *)
    val sub_and_le_nat : nat -> nat -> nat * bool
    val mul_nat : nat -> nat -> nat
    val div_nat : nat -> nat -> nat
    val even_nat : nat -> bool
    val odd_nat : nat -> bool

    (* normalize_nat m = (n, e) s.t. m = n * base^e, e >= 0 *)
    val normalize_nat : nat -> nat * int
    val denormalize_nat : nat * int -> nat
    (* hi_nat p m = (n, e) s.t. m <= n * base^e and n contains at most p "digits" *)
    val hi_nat : int -> nat -> nat * int
    val hi_lt_nat : int -> nat -> nat * int
    (* lo_nat p m = (n, e) s.t. n * base^e <= m and n contains at most p "digits" *)
    val lo_nat : int -> nat -> nat * int
