open Native_strictbuild

val my_mk_realintconst : num -> term
val my_dest_realintconst : term -> num
val my_real_int_neg_conv : term -> thm
val my_real_int_add_conv : term -> thm
val my_real_int_sub_conv : term -> thm
val my_real_int_mul_conv : term -> thm
