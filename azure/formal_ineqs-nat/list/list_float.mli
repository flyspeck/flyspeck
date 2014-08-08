open Hol_core
open Num
  val list_sum : thm
  val list_sum2 : thm
  val error_mul_f2 : thm
  val error_mul_f1 : thm
  val list_sum_conv : (term -> thm) -> term -> thm
  val list_sum2_le_conv : int -> (int -> term -> term -> thm) -> term -> thm
  val error_mul_f2_le_conv : int -> term -> term -> thm
  val error_mul_f2_le_conv2 : int -> term -> term -> thm
  val error_mul_f1_le_conv : term -> int -> term -> term -> thm
