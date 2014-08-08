(* ========================================================================= *)
(* Real vectors in Euclidean space, and elementary linear algebra.           *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

open Hol_core
include Misc

(* ------------------------------------------------------------------------- *)
(* Some common special cases.                                                *)
(* ------------------------------------------------------------------------- *)

let FORALL_1 = prove
 (`(!i. 1 <= i /\ i <= 1 ==> P i) <=> P 1`,
  MESON_TAC[LE_ANTISYM]);;

let FORALL_2 = prove
 (`!P. (!i. 1 <= i /\ i <= 2 ==> P i) <=> P 1 /\ P 2`,
  MESON_TAC[ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`]);;

let FORALL_3 = prove
 (`!P. (!i. 1 <= i /\ i <= 3 ==> P i) <=> P 1 /\ P 2 /\ P 3`,
  MESON_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`]);;

let FORALL_4 = prove
 (`!P. (!i. 1 <= i /\ i <= 4 ==> P i) <=> P 1 /\ P 2 /\ P 3 /\ P 4`,
  MESON_TAC[ARITH_RULE `1 <= i /\ i <= 4 <=>
    i = 1 \/ i = 2 \/ i = 3 \/ i = 4`]);;

let SUM_1 = prove
 (`sum(1..1) f = f(1)`,
  REWRITE_TAC[SUM_SING_NUMSEG]);;

let SUM_2 = prove
 (`!t. sum(1..2) t = t(1) + t(2)`,
  REWRITE_TAC[num_CONV `2`; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[SUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

let SUM_3 = prove
 (`!t. sum(1..3) t = t(1) + t(2) + t(3)`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[SUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

let SUM_4 = prove
 (`!t. sum(1..4) t = t(1) + t(2) + t(3) + t(4)`,
  SIMP_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[SUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Basic componentwise operations on vectors.                                *)
(* ------------------------------------------------------------------------- *)

let vector_add = new_definition
  `(vector_add:real^N->real^N->real^N) x y = lambda i. x$i + y$i`;;

let vector_sub = new_definition
  `(vector_sub:real^N->real^N->real^N) x y = lambda i. x$i - y$i`;;

let vector_neg = new_definition
  `(vector_neg:real^N->real^N) x = lambda i. --(x$i)`;;

overload_interface ("+",`(vector_add):real^N->real^N->real^N`);;
overload_interface ("-",`(vector_sub):real^N->real^N->real^N`);;
overload_interface ("--",`(vector_neg):real^N->real^N`);;

prioritize_real();;

let prioritize_vector = let ty = `:real^N` in
  fun () -> prioritize_overload ty;;

(* ------------------------------------------------------------------------- *)
(* Also the scalar-vector multiplication.                                    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("%",(21,"right"));;

let vector_mul = new_definition
  `((%):real->real^N->real^N) c x = lambda i. c * x$i`;;

(* ------------------------------------------------------------------------- *)
(* Vectors corresponding to small naturals. Perhaps should overload "&"?     *)
(* ------------------------------------------------------------------------- *)

let vec = new_definition
  `(vec:num->real^N) n = lambda i. &n`;;

(* ------------------------------------------------------------------------- *)
(* Dot products.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("dot",(20,"right"));;

let dot = new_definition
  `(x:real^N) dot (y:real^N) = sum(1..dimindex(:N)) (\i. x$i * y$i)`;;

let DOT_1 = prove
 (`(x:real^1) dot (y:real^1) = x$1 * y$1`,
  REWRITE_TAC[dot; DIMINDEX_1; SUM_1]);;

let DOT_2 = prove
 (`(x:real^2) dot (y:real^2) = x$1 * y$1 + x$2 * y$2`,
  REWRITE_TAC[dot; DIMINDEX_2; SUM_2]);;

let DOT_3 = prove
 (`(x:real^3) dot (y:real^3) = x$1 * y$1 + x$2 * y$2 + x$3 * y$3`,
  REWRITE_TAC[dot; DIMINDEX_3; SUM_3]);;

let DOT_4 = prove
 (`(x:real^4) dot (y:real^4) = x$1 * y$1 + x$2 * y$2 + x$3 * y$3 + x$4 * y$4`,
  REWRITE_TAC[dot; DIMINDEX_4; SUM_4]);;

(* ------------------------------------------------------------------------- *)
(* A naive proof procedure to lift really trivial arithmetic stuff from R.   *)
(* ------------------------------------------------------------------------- *)

let VECTOR_ARITH_TAC =
  let RENAMED_LAMBDA_BETA th =
    if fst(dest_fun_ty(type_of(funpow 3 rand (concl th)))) = aty
    then INST_TYPE [aty,bty; bty,aty] LAMBDA_BETA else LAMBDA_BETA in
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT(GEN_TAC ORELSE CONJ_TAC ORELSE DISCH_TAC ORELSE EQ_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[dot; GSYM SUM_ADD_NUMSEG; GSYM SUM_SUB_NUMSEG;
              GSYM SUM_LMUL; GSYM SUM_RMUL; GSYM SUM_NEG] THEN
  (MATCH_MP_TAC SUM_EQ_NUMSEG ORELSE MATCH_MP_TAC SUM_EQ_0_NUMSEG ORELSE
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [CART_EQ]) THEN
  REWRITE_TAC[AND_FORALL_THM] THEN TRY EQ_TAC THEN
  TRY(MATCH_MP_TAC MONO_FORALL) THEN GEN_TAC THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`;
              TAUT `(a ==> b) \/ (a ==> c) <=> a ==> b \/ c`] THEN
  TRY(MATCH_MP_TAC(TAUT `(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)`)) THEN
  REWRITE_TAC[vector_add; vector_sub; vector_neg; vector_mul; vec] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP(RENAMED_LAMBDA_BETA th) th]) THEN
  REAL_ARITH_TAC;;

let VECTOR_ARITH tm = prove(tm,VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Obvious "component-pushing".                                              *)
(* ------------------------------------------------------------------------- *)

let VEC_COMPONENT = prove
 (`!k i. (vec k :real^N)$i = &k`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    ASM_SIMP_TAC[vec; CART_EQ; LAMBDA_BETA]]);;

let VECTOR_ADD_COMPONENT = prove
 (`!x:real^N y i. (x + y)$i = x$i + y$i`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    ASM_SIMP_TAC[vector_add; CART_EQ; LAMBDA_BETA]]);;

let VECTOR_SUB_COMPONENT = prove
 (`!x:real^N y i. (x - y)$i = x$i - y$i`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    ASM_SIMP_TAC[vector_sub; CART_EQ; LAMBDA_BETA]]);;

let VECTOR_NEG_COMPONENT = prove
 (`!x:real^N i. (--x)$i = --(x$i)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    ASM_SIMP_TAC[vector_neg; CART_EQ; LAMBDA_BETA]]);;

let VECTOR_MUL_COMPONENT = prove
 (`!c x:real^N i. (c % x)$i = c * x$i`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    ASM_SIMP_TAC[vector_mul; CART_EQ; LAMBDA_BETA]]);;

let COND_COMPONENT = prove
 (`(if b then x else y)$i = if b then x$i else y$i`,
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some frequently useful arithmetic lemmas over vectors.                    *)
(* ------------------------------------------------------------------------- *)

let VECTOR_ADD_SYM = VECTOR_ARITH `!x y:real^N. x + y = y + x`;;

let VECTOR_ADD_LID = VECTOR_ARITH `!x. vec 0 + x = x`;;

let VECTOR_ADD_RID = VECTOR_ARITH `!x. x + vec 0 = x`;;

let VECTOR_SUB_REFL = VECTOR_ARITH `!x. x - x = vec 0`;;

let VECTOR_ADD_LINV = VECTOR_ARITH `!x. --x + x = vec 0`;;

let VECTOR_ADD_RINV = VECTOR_ARITH `!x. x + --x = vec 0`;;

let VECTOR_SUB_RADD = VECTOR_ARITH `!x y. x - (x + y) = --y:real^N`;;

let VECTOR_NEG_SUB = VECTOR_ARITH `!x:real^N y. --(x - y) = y - x`;;

let VECTOR_SUB_EQ = VECTOR_ARITH `!x y. (x - y = vec 0) <=> (x = y)`;;

let VECTOR_MUL_ASSOC = VECTOR_ARITH `!a b x. a % (b % x) = (a * b) % x`;;

let VECTOR_MUL_LID = VECTOR_ARITH `!x. &1 % x = x`;;

let VECTOR_MUL_LZERO = VECTOR_ARITH `!x. &0 % x = vec 0`;;

let VECTOR_SUB_ADD = VECTOR_ARITH `(x - y) + y = x:real^N`;;

let VECTOR_SUB_ADD2 = VECTOR_ARITH `y + (x - y) = x:real^N`;;

let VECTOR_ADD_LDISTRIB = VECTOR_ARITH `c % (x + y) = c % x + c % y`;;

let VECTOR_SUB_LDISTRIB = VECTOR_ARITH `c % (x - y) = c % x - c % y`;;

let VECTOR_ADD_RDISTRIB = VECTOR_ARITH `(a + b) % x = a % x + b % x`;;

let VECTOR_SUB_RDISTRIB = VECTOR_ARITH `(a - b) % x = a % x - b % x`;;

let VECTOR_ADD_SUB = VECTOR_ARITH `(x + y:real^N) - x = y`;;

let VECTOR_EQ_ADDR = VECTOR_ARITH `(x + y = x) <=> (y = vec 0)`;;

let VECTOR_SUB = VECTOR_ARITH `x - y = x + --(y:real^N)`;;

let VECTOR_SUB_RZERO = VECTOR_ARITH `x - vec 0 = x`;;

let VECTOR_MUL_RZERO = VECTOR_ARITH `c % vec 0 = vec 0`;;

let VECTOR_NEG_MINUS1 = VECTOR_ARITH `--x = (--(&1)) % x`;;

let VECTOR_ADD_ASSOC = VECTOR_ARITH `(x:real^N) + y + z = (x + y) + z`;;

let VECTOR_SUB_LZERO = VECTOR_ARITH `vec 0 - x = --x`;;

let VECTOR_NEG_NEG = VECTOR_ARITH `--(--(x:real^N)) = x`;;

let VECTOR_MUL_LNEG = VECTOR_ARITH `--c % x = --(c % x)`;;

let VECTOR_MUL_RNEG = VECTOR_ARITH `c % --x = --(c % x)`;;

let VECTOR_NEG_0 = VECTOR_ARITH `--(vec 0) = vec 0`;;

let VECTOR_NEG_EQ_0 = VECTOR_ARITH `--x = vec 0 <=> x = vec 0`;;

let VECTOR_EQ_NEG2 = VECTOR_ARITH `!x y:real^N. --x = --y <=> x = y`;;

let VECTOR_ADD_AC = VECTOR_ARITH
  `(m + n = n + m:real^N) /\
   ((m + n) + p = m + n + p) /\
   (m + n + p = n + m + p)`;;

let VEC_EQ = prove
 (`!m n. (vec m = vec n) <=> (m = n)`,
  SIMP_TAC[CART_EQ; VEC_COMPONENT; REAL_OF_NUM_EQ] THEN
  MESON_TAC[LE_REFL; DIMINDEX_GE_1]);;

(* ------------------------------------------------------------------------- *)
(* Analogous theorems for set-sums.                                          *)
(* ------------------------------------------------------------------------- *)

let SUMS_SYM = prove
 (`!s t:real^N->bool.
        {x + y | x IN s /\ y IN t} = {y + x | y IN t /\ x IN s}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[VECTOR_ADD_SYM]);;

let SUMS_ASSOC = prove
 (`!s t u:real^N->bool.
        {w + z | w IN {x + y | x IN s /\ y IN t} /\ z IN u} =
        {x + v | x IN s /\ v IN {y + z | y IN t /\ z IN u}}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[VECTOR_ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Infinitude of Euclidean space.                                            *)
(* ------------------------------------------------------------------------- *)

let EUCLIDEAN_SPACE_INFINITE = prove
 (`INFINITE(:real^N)`,
  REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPEC `vec:num->real^N` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] FINITE_IMAGE_INJ)) THEN
  REWRITE_TAC[VEC_EQ; SET_RULE `{x | f x IN UNIV} = UNIV`] THEN
  REWRITE_TAC[GSYM INFINITE; num_INFINITE]);;

(* ------------------------------------------------------------------------- *)
(* Properties of the dot product.                                            *)
(* ------------------------------------------------------------------------- *)

let DOT_SYM = VECTOR_ARITH `!x y. x dot y = y dot x`;;

let DOT_LADD = VECTOR_ARITH `!x y z. (x + y) dot z = (x dot z) + (y dot z)`;;

let DOT_RADD = VECTOR_ARITH `!x y z. x dot (y + z) = (x dot y) + (x dot z)`;;

let DOT_LSUB = VECTOR_ARITH `!x y z. (x - y) dot z = (x dot z) - (y dot z)`;;

let DOT_RSUB = VECTOR_ARITH `!x y z. x dot (y - z) = (x dot y) - (x dot z)`;;

let DOT_LMUL = VECTOR_ARITH `!c x y. (c % x) dot y = c * (x dot y)`;;

let DOT_RMUL = VECTOR_ARITH `!c x y. x dot (c % y) = c * (x dot y)`;;

let DOT_LNEG = VECTOR_ARITH `!x y. (--x) dot y = --(x dot y)`;;

let DOT_RNEG = VECTOR_ARITH `!x y. x dot (--y) = --(x dot y)`;;

let DOT_LZERO = VECTOR_ARITH `!x. (vec 0) dot x = &0`;;

let DOT_RZERO = VECTOR_ARITH `!x. x dot (vec 0) = &0`;;

let DOT_POS_LE = prove
 (`!x. &0 <= x dot x`,
  SIMP_TAC[dot; SUM_POS_LE_NUMSEG; REAL_LE_SQUARE]);;

let DOT_EQ_0 = prove
 (`!x:real^N. ((x dot x = &0) <=> (x = vec 0))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[DOT_LZERO]] THEN
  SIMP_TAC[dot; CART_EQ; vec; LAMBDA_BETA] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[REAL_ENTIRE] `x * x = &0`)] THEN
  MATCH_MP_TAC SUM_POS_EQ_0_NUMSEG THEN ASM_REWRITE_TAC[REAL_LE_SQUARE]);;

let DOT_POS_LT = prove
 (`!x. (&0 < x dot x) <=> ~(x = vec 0)`,
  REWRITE_TAC[REAL_LT_LE; DOT_POS_LE] THEN MESON_TAC[DOT_EQ_0]);;

let FORALL_DOT_EQ_0 = prove
 (`(!y. (!x. x dot y = &0) <=> y = vec 0) /\
   (!x. (!y. x dot y = &0) <=> x = vec 0)`,
  MESON_TAC[DOT_LZERO; DOT_RZERO; DOT_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Introduce norms, but defer many properties till we get square roots.      *)
(* ------------------------------------------------------------------------- *)

make_overloadable "norm" `:A->real`;;
overload_interface("norm",`vector_norm:real^N->real`);;

let vector_norm = new_definition
  `norm x = sqrt(x dot x)`;;

(* ------------------------------------------------------------------------- *)
(* Useful for the special cases of 1 dimension.                              *)
(* ------------------------------------------------------------------------- *)

let FORALL_DIMINDEX_1 = prove
 (`(!i. 1 <= i /\ i <= dimindex(:1) ==> P i) <=> P 1`,
  MESON_TAC[DIMINDEX_1; LE_ANTISYM]);;

(* ------------------------------------------------------------------------- *)
(* The collapse of the general concepts to the real line R^1.                *)
(* ------------------------------------------------------------------------- *)

let VECTOR_ONE = prove
 (`!x:real^1. x = lambda i. x$1`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN MESON_TAC[DIMINDEX_1; LE_ANTISYM]);;

let FORALL_REAL_ONE = prove
 (`(!x:real^1. P x) <=> (!x. P(lambda i. x))`,
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x:real^1)$1`) THEN
  REWRITE_TAC[GSYM VECTOR_ONE]);;

let NORM_REAL = prove
 (`!x:real^1. norm(x) = abs(x$1)`,
  REWRITE_TAC[vector_norm; dot; DIMINDEX_1; SUM_SING_NUMSEG;
              GSYM REAL_POW_2; POW_2_SQRT_ABS]);;

(* ------------------------------------------------------------------------- *)
(* Metric function.                                                          *)
(* ------------------------------------------------------------------------- *)

override_interface("dist",`distance:real^N#real^N->real`);;

let dist = new_definition
  `dist(x,y) = norm(x - y)`;;

let DIST_REAL = prove
 (`!x:real^1 y. dist(x,y) = abs(x$1 - y$1)`,
  SIMP_TAC[dist; NORM_REAL; vector_sub; LAMBDA_BETA; LE_REFL; DIMINDEX_1]);;

(* ------------------------------------------------------------------------- *)
(* A connectedness or intermediate value lemma with several applications.    *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_REAL_LEMMA = prove
 (`!f:real->real^N a b e1 e2.
        a <= b /\ f(a) IN e1 /\ f(b) IN e2 /\
        (!e x. a <= x /\ x <= b /\ &0 < e
               ==> ?d. &0 < d /\
                       !y. abs(y - x) < d ==> dist(f(y),f(x)) < e) /\
        (!y. y IN e1 ==> ?e. &0 < e /\ !y'. dist(y',y) < e ==> y' IN e1) /\
        (!y. y IN e2 ==> ?e. &0 < e /\ !y'. dist(y',y) < e ==> y' IN e2) /\
        ~(?x. a <= x /\ x <= b /\ f(x) IN e1 /\ f(x) IN e2)
        ==> ?x. a <= x /\ x <= b /\ ~(f(x) IN e1) /\ ~(f(x) IN e2)`,
  let tac = ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TOTAL; REAL_LE_ANTISYM] in
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\c. !x. a <= x /\ x <= c ==> (f(x):real^N) IN e1`
              REAL_COMPLETE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [tac; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `a <= x /\ x <= b` STRIP_ASSUME_TAC THENL [tac; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!z. a <= z /\ z < x ==> (f(z):real^N) IN e1` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_NOT_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN
     `?d. &0 < d /\ !y. abs(y - x) < d ==> (f(y):real^N) IN e1`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[REAL_ARITH `z <= x + e /\ e < d ==> z < x \/ abs(z - x) < d`;
                  REAL_ARITH `&0 < e ==> ~(x + e <= x)`; REAL_DOWN];
    SUBGOAL_THEN
     `?d. &0 < d /\ !y. abs(y - x) < d ==> (f(y):real^N) IN e2`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`x - a`; `d:real`] REAL_DOWN2) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[REAL_LT_LE; REAL_SUB_LT]; ALL_TAC] THEN
    ASM_MESON_TAC[REAL_ARITH `e < x - a ==> a <= x - e`;
                  REAL_ARITH `&0 < e /\ x <= b ==> x - e <= b`;
      REAL_ARITH `&0 < e /\ e < d ==> x - e < x /\ abs((x - e) - x) < d`]]);;

(* ------------------------------------------------------------------------- *)
(* One immediately useful corollary is the existence of square roots!        *)
(* ------------------------------------------------------------------------- *)

let SQUARE_BOUND_LEMMA = prove
 (`!x. x < (&1 + x) * (&1 + x)`,
  GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t REAL_LE_SQUARE)) [`x:real`; `&1 + x`] THEN
  REAL_ARITH_TAC);;

let SQUARE_CONTINUOUS = prove
 (`!x e. &0 < e
         ==> ?d. &0 < d /\ !y. abs(y - x) < d ==> abs(y * y - x * x) < e`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    EXISTS_TAC `inv(&1 + inv(e))` THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_LT_ADD; REAL_LT_01] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC  REAL_LTE_TRANS THEN
    EXISTS_TAC `inv(&1 + inv(e)) * inv(&1 + inv(e))` THEN
    ASM_SIMP_TAC[REAL_ABS_MUL; REAL_LT_MUL2; REAL_ABS_POS] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SQUARE_BOUND_LEMMA; REAL_LT_INV_EQ];
    MP_TAC(SPECL [`abs(x)`; `e / (&3 * abs(x))`] REAL_DOWN2)THEN
    ASM_SIMP_TAC[GSYM REAL_ABS_NZ; REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT;
                 ARITH; REAL_LT_RDIV_EQ] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN
    REWRITE_TAC[REAL_ARITH `x * x - y * y = (x - y) * (x + y)`] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `d * &3 * abs(x)` THEN ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE] THEN
    MAP_EVERY UNDISCH_TAC [`abs (y - x) < d`; `d < abs(x)`] THEN
    REAL_ARITH_TAC]);;

let SQRT_WORKS_GEN = prove
 (`!x. real_sgn(sqrt x) = real_sgn x /\ sqrt(x) pow 2 = abs x`,
  GEN_TAC THEN REWRITE_TAC[sqrt] THEN CONV_TAC SELECT_CONV THEN
  SUBGOAL_THEN `!x. &0 < x ==> ?y. &0 < y /\ y pow 2 = x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(\u. lambda i. u):real->real^1`; `&0`; `&1 + x`;
            `{u:real^1 | u$1 * u$1 < x}`; `{u:real^1 | u$1 * u$1 > x}`]
         CONNECTED_REAL_LEMMA) THEN
    SIMP_TAC[LAMBDA_BETA; LE_REFL; DIMINDEX_1; DIST_REAL; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH `~(x < y) /\ ~(x > y) <=> x = y`] THEN
    ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LT_LE; REAL_ENTIRE]] THEN
    ASM_REWRITE_TAC[real_gt; SQUARE_BOUND_LEMMA; REAL_MUL_LZERO] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_LT_ANTISYM]] THEN
    MESON_TAC[SQUARE_CONTINUOUS; REAL_SUB_LT;
              REAL_ARITH `abs(z2 - x2) < y - x2 ==> z2 < y`;
              REAL_ARITH `abs(z2 - x2) < x2 - y ==> y < z2`];
    ASM_CASES_TAC `x = &0` THEN
    ASM_REWRITE_TAC[REAL_SGN_0; REAL_SGN_EQ; UNWIND_THM2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `abs x`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `real_sgn x * y` THEN
    ASM_REWRITE_TAC[REAL_POW_MUL; GSYM REAL_SGN_POW; REAL_SGN_POW_2] THEN
    REWRITE_TAC[REAL_SGN_MUL; REAL_SGN_REAL_SGN] THEN
    ASM_SIMP_TAC[real_sgn; REAL_ARITH `&0 < abs x <=> ~(x = &0)`] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID]]);;

let SQRT_UNIQUE_GEN = prove
 (`!x y. real_sgn y = real_sgn x /\ y pow 2 = abs x ==> sqrt x = y`,
  REPEAT GEN_TAC THEN
  MP_TAC(GSYM(SPEC `x:real` SQRT_WORKS_GEN)) THEN
  SIMP_TAC[REAL_RING `x pow 2 = y pow 2 <=> x:real = y \/ x = --y`] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[IMP_CONJ_ALT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_SGN_NEG] THEN
  SIMP_TAC[REAL_ARITH `--x = x <=> x = &0`; REAL_SGN_EQ; REAL_NEG_0; SQRT_0]);;

let SQRT_NEG = prove
 (`!x. sqrt(--x) = --sqrt(x)`,
  GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
  REWRITE_TAC[REAL_SGN_NEG; REAL_POW_NEG; REAL_ABS_NEG; ARITH] THEN
  REWRITE_TAC[SQRT_WORKS_GEN]);;

let REAL_SGN_SQRT = prove
 (`!x. real_sgn(sqrt x) = real_sgn x`,
  REWRITE_TAC[SQRT_WORKS_GEN]);;

let SQRT_WORKS = prove
 (`!x. &0 <= x ==> &0 <= sqrt(x) /\ sqrt(x) pow 2 = x`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `x:real` SQRT_WORKS_GEN) THEN
  REWRITE_TAC[real_sgn] THEN ASM_REAL_ARITH_TAC);;

let SQRT_POS_LE = prove
 (`!x. &0 <= x ==> &0 <= sqrt(x)`,
  MESON_TAC[SQRT_WORKS]);;

let SQRT_POW_2 = prove
 (`!x. &0 <= x ==> sqrt(x) pow 2 = x`,
  MESON_TAC[SQRT_WORKS]);;

let SQRT_POW2 = prove
 (`!x. sqrt(x) pow 2 = x <=> &0 <= x`,
  MESON_TAC[REAL_POW_2; REAL_LE_SQUARE; SQRT_POW_2]);;

let SQRT_MUL = prove
 (`!x y. sqrt(x * y) = sqrt x * sqrt y`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
  REWRITE_TAC[REAL_SGN_MUL; REAL_POW_MUL; SQRT_WORKS_GEN; REAL_ABS_MUL]);;

let SQRT_INV = prove
 (`!x. sqrt (inv x) = inv(sqrt x)`,
  GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
  REWRITE_TAC[REAL_SGN_INV; REAL_POW_INV; REAL_ABS_INV; SQRT_WORKS_GEN]);;

let SQRT_DIV = prove
 (`!x y. sqrt (x / y) = sqrt x / sqrt y`,
  REWRITE_TAC[real_div; SQRT_MUL; SQRT_INV]);;

let SQRT_LT_0 = prove
 (`!x. &0 < sqrt x <=> &0 < x`,
  REWRITE_TAC[GSYM real_gt; GSYM REAL_SGN_EQ; REAL_SGN_SQRT]);;

let SQRT_EQ_0 = prove
 (`!x. sqrt x = &0 <=> x = &0`,
  ONCE_REWRITE_TAC[GSYM REAL_SGN_EQ] THEN REWRITE_TAC[REAL_SGN_SQRT]);;

let SQRT_LE_0 = prove
 (`!x. &0 <= sqrt x <=> &0 <= x`,
  REWRITE_TAC[REAL_ARITH `&0 <= x <=> &0 < x \/ x = &0`] THEN
  REWRITE_TAC[SQRT_LT_0; SQRT_EQ_0]);;

let SQRT_MONO_LT = prove
 (`!x y. x < y ==> sqrt(x) < sqrt(y)`,
  SUBGOAL_THEN `!x y. &0 <= x /\ x < y ==> sqrt x < sqrt y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN
    EXISTS_TAC `2` THEN ASM_REWRITE_TAC[SQRT_WORKS_GEN; SQRT_LE_0] THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= x` THEN ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `&0 <= y` THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[GSYM REAL_NOT_LE; SQRT_LE_0];
      FIRST_X_ASSUM(MP_TAC o SPECL [`--y:real`; `--x:real`]) THEN
      REWRITE_TAC[SQRT_NEG] THEN ASM_REAL_ARITH_TAC]]);;

let SQRT_MONO_LE = prove
 (`!x y. x <= y ==> sqrt(x) <= sqrt(y)`,
  MESON_TAC[REAL_LE_LT; SQRT_MONO_LT]);;

let SQRT_MONO_LT_EQ = prove
 (`!x y. sqrt(x) < sqrt(y) <=> x < y`,
  MESON_TAC[REAL_NOT_LT; SQRT_MONO_LT; SQRT_MONO_LE]);;

let SQRT_MONO_LE_EQ = prove
 (`!x y. sqrt(x) <= sqrt(y) <=> x <= y`,
  MESON_TAC[REAL_NOT_LT; SQRT_MONO_LT; SQRT_MONO_LE]);;

let SQRT_INJ = prove
 (`!x y. sqrt(x) = sqrt(y) <=> x = y`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; SQRT_MONO_LE_EQ]);;

let SQRT_POS_LT = prove
 (`!x. &0 < x ==> &0 < sqrt(x)`,
  MESON_TAC[REAL_LT_LE; SQRT_POS_LE; SQRT_EQ_0]);;

let REAL_LE_LSQRT = prove
 (`!x y. &0 <= y /\ x <= y pow 2 ==> sqrt(x) <= y`,
  MESON_TAC[SQRT_MONO_LE; REAL_POW_LE; POW_2_SQRT]);;

let REAL_LE_RSQRT = prove
 (`!x y. x pow 2 <= y ==> x <= sqrt(y)`,
  MESON_TAC[REAL_LE_TOTAL; SQRT_MONO_LE; SQRT_POS_LE; REAL_POW_2;
            REAL_LE_SQUARE; REAL_LE_TRANS; POW_2_SQRT]);;

let REAL_LT_LSQRT = prove
 (`!x y. &0 <= y /\ x < y pow 2 ==> sqrt x < y`,
  MESON_TAC[SQRT_MONO_LT; REAL_POW_LE; POW_2_SQRT]);;

let REAL_LT_RSQRT = prove
 (`!x y. x pow 2 < y ==> x < sqrt(y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `abs x < a ==> x < a`) THEN
  REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN MATCH_MP_TAC SQRT_MONO_LT THEN
  ASM_REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]);;

let SQRT_EVEN_POW2 = prove
 (`!n. EVEN n ==> (sqrt(&2 pow n) = &2 pow (n DIV 2))`,
  SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM; DIV_MULT; ARITH_EQ] THEN
  MESON_TAC[SQRT_UNIQUE; REAL_POW_POW; MULT_SYM; REAL_POW_LE; REAL_POS]);;

let REAL_DIV_SQRT = prove
 (`!x. &0 <= x ==> x / sqrt(x) = sqrt(x)`,
  REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SQRT_0; real_div; REAL_MUL_LZERO]] THEN
  ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; SQRT_POS_LT; GSYM REAL_POW_2] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]);;

let REAL_RSQRT_LE = prove
 (`!x y. &0 <= x /\ &0 <= y /\ x <= sqrt y ==> x pow 2 <= y`,
  MESON_TAC[REAL_POW_LE2; SQRT_POW_2]);;

let REAL_LSQRT_LE = prove
 (`!x y. &0 <= x /\ sqrt x <= y ==> x <= y pow 2`,
  MESON_TAC[REAL_POW_LE2; SQRT_POS_LE; REAL_LE_TRANS; SQRT_POW_2]);;

let REAL_SQRT_POW_2 = prove
 (`!x. sqrt x pow 2 = abs x`,
  REWRITE_TAC[SQRT_WORKS_GEN]);;

(* ------------------------------------------------------------------------- *)
(* Hence derive more interesting properties of the norm.                     *)
(* ------------------------------------------------------------------------- *)

let NORM_0 = prove
 (`norm(vec 0) = &0`,
  REWRITE_TAC[vector_norm; DOT_LZERO; SQRT_0]);;

let NORM_POS_LE = prove
 (`!x. &0 <= norm x`,
  GEN_TAC THEN SIMP_TAC[DOT_POS_LE; vector_norm; SQRT_POS_LE]);;

let NORM_NEG = prove
 (`!x. norm(--x) = norm x`,
  REWRITE_TAC[vector_norm; DOT_LNEG; DOT_RNEG; REAL_NEG_NEG]);;

let NORM_SUB = prove
 (`!x y. norm(x - y) = norm(y - x)`,
  MESON_TAC[NORM_NEG; VECTOR_NEG_SUB]);;

let NORM_MUL = prove
 (`!a x. norm(a % x) = abs(a) * norm x`,
  REWRITE_TAC[vector_norm; DOT_LMUL; DOT_RMUL; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[SQRT_MUL; GSYM REAL_POW_2; REAL_SQRT_POW_2]);;

let NORM_EQ_0_DOT = prove
 (`!x. (norm x = &0) <=> (x dot x = &0)`,
  SIMP_TAC[vector_norm; SQRT_EQ_0; DOT_POS_LE]);;

let NORM_EQ_0 = prove
 (`!x. (norm x = &0) <=> (x = vec 0)`,
  SIMP_TAC[vector_norm; DOT_EQ_0; SQRT_EQ_0; DOT_POS_LE]);;

let NORM_POS_LT = prove
 (`!x. &0 < norm x <=> ~(x = vec 0)`,
  MESON_TAC[REAL_LT_LE; NORM_POS_LE; NORM_EQ_0]);;

let NORM_POW_2 = prove
 (`!x. norm(x) pow 2 = x dot x`,
  SIMP_TAC[vector_norm; SQRT_POW_2; DOT_POS_LE]);;

let NORM_EQ_0_IMP = prove
 (`!x. (norm x = &0) ==> (x = vec 0)`,
  MESON_TAC[NORM_EQ_0]);;

let NORM_LE_0 = prove
 (`!x. norm x <= &0 <=> (x = vec 0)`,
  MESON_TAC[REAL_LE_ANTISYM; NORM_EQ_0; NORM_POS_LE]);;

let VECTOR_MUL_EQ_0 = prove
 (`!a x. (a % x = vec 0) <=> (a = &0) \/ (x = vec 0)`,
  REWRITE_TAC[GSYM NORM_EQ_0; NORM_MUL; REAL_ABS_ZERO; REAL_ENTIRE]);;

let VECTOR_MUL_LCANCEL = prove
 (`!a x y. (a % x = a % y) <=> (a = &0) \/ (x = y)`,
  MESON_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_LDISTRIB; VECTOR_SUB_EQ]);;

let VECTOR_MUL_RCANCEL = prove
 (`!a b x. (a % x = b % x) <=> (a = b) \/ (x = vec 0)`,
  MESON_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_RDISTRIB; REAL_SUB_0; VECTOR_SUB_EQ]);;

let VECTOR_MUL_LCANCEL_IMP = prove
 (`!a x y. ~(a = &0) /\ (a % x = a % y) ==> (x = y)`,
  MESON_TAC[VECTOR_MUL_LCANCEL]);;

let VECTOR_MUL_RCANCEL_IMP = prove
 (`!a b x. ~(x = vec 0) /\ (a % x = b % x) ==> (a = b)`,
  MESON_TAC[VECTOR_MUL_RCANCEL]);;

let NORM_CAUCHY_SCHWARZ = prove
 (`!(x:real^N) y. x dot y <= norm(x) * norm(y)`,
  REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`norm(x:real^N) = &0`; `norm(y:real^N) = &0`] THEN
  ASM_SIMP_TAC[NORM_EQ_0_IMP; DOT_LZERO; DOT_RZERO;
               REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  MP_TAC(ISPEC `norm(y:real^N) % x - norm(x:real^N) % y` DOT_POS_LE) THEN
  REWRITE_TAC[DOT_RSUB; DOT_LSUB; DOT_LMUL; DOT_RMUL; GSYM NORM_POW_2;
              REAL_POW_2; REAL_LE_REFL] THEN
  REWRITE_TAC[DOT_SYM; REAL_ARITH
   `&0 <= y * (y * x * x - x * d) - x * (y * d - x * y * y) <=>
    x * y * d <= x * y * x * y`] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_LE; NORM_POS_LE]);;

let NORM_CAUCHY_SCHWARZ_ABS = prove
 (`!x:real^N y. abs(x dot y) <= norm(x) * norm(y)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `x:real^N` NORM_CAUCHY_SCHWARZ) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `y:real^N` th) THEN
        MP_TAC(SPEC `--(y:real^N)` th)) THEN
  REWRITE_TAC[DOT_RNEG; NORM_NEG] THEN REAL_ARITH_TAC);;

let REAL_ABS_NORM = prove
 (`!x. abs(norm x) = norm x`,
  REWRITE_TAC[NORM_POS_LE; REAL_ABS_REFL]);;

let NORM_CAUCHY_SCHWARZ_DIV = prove
 (`!x:real^N y. abs((x dot y) / (norm x * norm y)) <= &1`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`x:real^N = vec 0`; `y:real^N = vec 0`] THEN
  ASM_REWRITE_TAC[NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO; real_div;
             REAL_INV_1; DOT_LZERO; DOT_RZERO; REAL_ABS_NUM; REAL_POS] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_ABS_DIV; REAL_LE_LDIV_EQ; REAL_LT_MUL;
     REAL_ABS_INV; NORM_POS_LT; REAL_ABS_MUL; REAL_ABS_NORM] THEN
  REWRITE_TAC[REAL_MUL_LID; NORM_CAUCHY_SCHWARZ_ABS]);;

let NORM_TRIANGLE = prove
 (`!x y. norm(x + y) <= norm(x) + norm(y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vector_norm] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN
  SIMP_TAC[GSYM vector_norm; DOT_POS_LE; NORM_POS_LE; REAL_LE_ADD] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; REAL_POW_2; GSYM NORM_POW_2] THEN
  SIMP_TAC[NORM_CAUCHY_SCHWARZ; DOT_SYM; REAL_ARITH
   `d <= x * y ==> (x * x + d) + (d + y * y) <= (x + y) * (x + y)`]);;

let NORM_TRIANGLE_SUB = prove
 (`!x y:real^N. norm(x) <= norm(y) + norm(x - y)`,
  MESON_TAC[NORM_TRIANGLE; VECTOR_SUB_ADD2]);;

let NORM_TRIANGLE_LE = prove
 (`!x y. norm(x) + norm(y) <= e ==> norm(x + y) <= e`,
  MESON_TAC[REAL_LE_TRANS; NORM_TRIANGLE]);;

let NORM_TRIANGLE_LT = prove
 (`!x y. norm(x) + norm(y) < e ==> norm(x + y) < e`,
  MESON_TAC[REAL_LET_TRANS; NORM_TRIANGLE]);;

let COMPONENT_LE_NORM = prove
 (`!x:real^N i. abs(x$i) <= norm x`,
  REPEAT GEN_TAC THEN SUBGOAL_THEN
  `?k. 1 <= k /\ k <= dimindex(:N) /\ !x:real^N. x$i = x$k`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[vector_norm] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[GSYM REAL_ABS_POW] THEN
  REWRITE_TAC[real_abs; REAL_POW_2; REAL_LE_SQUARE] THEN
  SUBGOAL_THEN
   `x$k * (x:real^N)$k =
     sum(1..dimindex(:N)) (\i. if i = k then x$k * x$k else &0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_DELTA] THEN ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LE_SQUARE]);;

let NORM_BOUND_COMPONENT_LE = prove
 (`!x:real^N e. norm(x) <= e
                ==> !i. 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) <= e`,
  MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]);;

let NORM_BOUND_COMPONENT_LT = prove
 (`!x:real^N e. norm(x) < e
                ==> !i. 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) < e`,
  MESON_TAC[COMPONENT_LE_NORM; REAL_LET_TRANS]);;

let NORM_LE_L1 = prove
 (`!x:real^N. norm x <= sum(1..dimindex(:N)) (\i. abs(x$i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vector_norm; dot] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
  SIMP_TAC[SUM_POS_LE; FINITE_NUMSEG; REAL_LE_SQUARE; REAL_ABS_POS] THEN
  SPEC_TAC(`dimindex(:N)`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THEN
  SIMP_TAC[REAL_MUL_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a2 <= a * a /\ &0 <= a * b /\ b2 <= b * b
    ==> a2 + b2 <= (a + b) * (a + b)`) THEN
  ASM_SIMP_TAC[SUM_POS_LE; REAL_LE_MUL; REAL_ABS_POS; FINITE_NUMSEG] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC);;

let REAL_ABS_SUB_NORM = prove
 (`abs(norm(x) - norm(y)) <= norm(x - y)`,
  REWRITE_TAC[REAL_ARITH `abs(x - y) <= a <=> x <= y + a /\ y <= x + a`] THEN
  MESON_TAC[NORM_TRIANGLE_SUB; NORM_SUB]);;

let NORM_LE = prove
 (`!x y. norm(x) <= norm(y) <=> x dot x <= y dot y`,
  REWRITE_TAC[vector_norm] THEN MESON_TAC[SQRT_MONO_LE_EQ; DOT_POS_LE]);;

let NORM_LT = prove
 (`!x y. norm(x) < norm(y) <=> x dot x < y dot y`,
  REWRITE_TAC[vector_norm] THEN MESON_TAC[SQRT_MONO_LT_EQ; DOT_POS_LE]);;

let NORM_EQ = prove
 (`!x y. (norm x = norm y) <=> (x dot x = y dot y)`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; NORM_LE]);;

let NORM_EQ_1 = prove
 (`!x. norm(x) = &1 <=> x dot x = &1`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM SQRT_1] THEN
  SIMP_TAC[vector_norm; SQRT_INJ; DOT_POS_LE; REAL_POS]);;

let NORM_LE_COMPONENTWISE = prove
 (`!x:real^N y:real^N.
        (!i. 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) <= abs(y$i))
        ==> norm(x) <= norm(y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_LE; dot] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; GSYM REAL_LE_SQUARE_ABS]);;

let L1_LE_NORM = prove
 (`!x:real^N.
    sum(1..dimindex(:N)) (\i. abs(x$i)) <= sqrt(&(dimindex(:N))) * norm x`,
  let lemma = prove
   (`!x n. &n * sum(1..n) (\i. x i pow 2) - (sum(1..n) x) pow 2 =
           sum(1..n) (\i. sum(i+1..n) (\j. (x i - x j) pow 2))`,
    GEN_TAC THEN CONV_TAC(BINDER_CONV SYM_CONV) THEN INDUCT_TAC THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; ARITH_RULE `1 <= SUC n`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[ARITH_RULE `i <= n ==> i + 1 <= SUC n`; SUM_TRIV_NUMSEG;
             ARITH_RULE `~(n + 1 <= n)`; ARITH_RULE `n < SUC n + 1`] THEN
    ASM_REWRITE_TAC[SUM_ADD_NUMSEG; REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_ARITH
     `(x - y) pow 2 = (x pow 2 + y pow 2) - &2 * x * y`] THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_LMUL; SUM_RMUL;
                GSYM REAL_OF_NUM_SUC; SUM_CONST_NUMSEG; ADD_SUB] THEN
    REAL_ARITH_TAC) in
  GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ abs x <= abs y ==> x <= y`) THEN
  SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; SQRT_POS_LE; REAL_POS] THEN
  REWRITE_TAC[REAL_LE_SQUARE_ABS; REAL_POW_MUL] THEN
  SIMP_TAC[SQRT_POW_2; REAL_POS; NORM_POW_2; dot] THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_POW2_ABS] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN REWRITE_TAC[lemma] THEN
  SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_LE_POW_2]);;

(* ------------------------------------------------------------------------- *)
(* Squaring equations and inequalities involving norms.                      *)
(* ------------------------------------------------------------------------- *)

let DOT_SQUARE_NORM = prove
 (`!x. x dot x = norm(x) pow 2`,
  SIMP_TAC[vector_norm; SQRT_POW_2; DOT_POS_LE]);;

let NORM_EQ_SQUARE = prove
 (`!x:real^N. norm(x) = a <=> &0 <= a /\ x dot x = a pow 2`,
  REWRITE_TAC[DOT_SQUARE_NORM] THEN
  ONCE_REWRITE_TAC[REAL_RING `x pow 2 = a pow 2 <=> x = a \/ x + a = &0`] THEN
  GEN_TAC THEN MP_TAC(ISPEC `x:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC);;

let NORM_LE_SQUARE = prove
 (`!x:real^N. norm(x) <= a <=> &0 <= a /\ x dot x <= a pow 2`,
  REWRITE_TAC[DOT_SQUARE_NORM; GSYM REAL_LE_SQUARE_ABS] THEN
  GEN_TAC THEN MP_TAC(ISPEC `x:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC);;

let NORM_GE_SQUARE = prove
 (`!x:real^N. norm(x) >= a <=> a <= &0 \/ x dot x >= a pow 2`,
  REWRITE_TAC[real_ge; DOT_SQUARE_NORM; GSYM REAL_LE_SQUARE_ABS] THEN
  GEN_TAC THEN MP_TAC(ISPEC `x:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC);;

let NORM_LT_SQUARE = prove
 (`!x:real^N. norm(x) < a <=> &0 < a /\ x dot x < a pow 2`,
  REWRITE_TAC[REAL_ARITH `x < a <=> ~(x >= a)`; NORM_GE_SQUARE] THEN
  REAL_ARITH_TAC);;

let NORM_GT_SQUARE = prove
 (`!x:real^N. norm(x) > a <=> a < &0 \/ x dot x > a pow 2`,
  REWRITE_TAC[REAL_ARITH `x > a <=> ~(x <= a)`; NORM_LE_SQUARE] THEN
  REAL_ARITH_TAC);;

let NORM_LT_SQUARE_ALT = prove
 (`!x:real^N. norm(x) < a <=> &0 <= a /\ x dot x < a pow 2`,
  REWRITE_TAC[REAL_ARITH `x < a <=> ~(x >= a)`; NORM_GE_SQUARE] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = &0` THENL
   [ASM_REWRITE_TAC[real_ge] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[DOT_POS_LE];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* General linear decision procedure for normed spaces.                      *)
(* ------------------------------------------------------------------------- *)

let NORM_ARITH =
  let find_normedterms =
    let augment_norm b tm acc =
      match tm with
        Comb(Const("vector_norm",_),v) -> insert (b,v) acc
      | _ -> acc in
    let rec find_normedterms tm acc =
      match tm with
        Comb(Comb(Const("real_add",_),l),r) ->
            find_normedterms l (find_normedterms r acc)
      | Comb(Comb(Const("real_mul",_),c),n) ->
            if not (is_ratconst c) then acc else
            augment_norm (rat_of_term c >=/ Int 0) n acc
      | _ -> augment_norm true tm acc in
    find_normedterms in
  let lincomb_neg t = mapf minus_num t in
  let lincomb_cmul c t = if c =/ Int 0 then undefined else mapf (( */ ) c) t in
  let lincomb_add l r = combine (+/) (fun x -> x =/ Int 0) l r in
  let lincomb_sub l r = lincomb_add l (lincomb_neg r) in
  let lincomb_eq l r = lincomb_sub l r = undefined in
  let rec vector_lincomb tm =
    match tm with
        Comb(Comb(Const("vector_add",_),l),r) ->
          lincomb_add (vector_lincomb l) (vector_lincomb r)
      | Comb(Comb(Const("vector_sub",_),l),r) ->
          lincomb_sub (vector_lincomb l) (vector_lincomb r)
      | Comb(Comb(Const("%",_),l),r) ->
          lincomb_cmul (rat_of_term l) (vector_lincomb r)
      | Comb(Const("vector_neg",_),t) ->
          lincomb_neg (vector_lincomb t)
      | Comb(Const("vec",_),n) when is_numeral n & dest_numeral n =/ Int 0 ->
          undefined
      | _ -> (tm |=> Int 1) in
  let vector_lincombs tms =
    itlist (fun t fns ->
                  if can (assoc t) fns then fns else
                  let f = vector_lincomb t in
                  try let _,f' = find (fun (_,f') -> lincomb_eq f f') fns in
                      (t,f')::fns
                  with Failure _ -> (t,f)::fns) tms [] in
  let rec replacenegnorms fn tm =
    match tm with
      Comb(Comb(Const("real_add",_),l),r) ->
          BINOP_CONV (replacenegnorms fn) tm
    | Comb(Comb(Const("real_mul",_),c),n) when rat_of_term c </ Int 0 ->
          RAND_CONV fn tm
    | _ -> REFL tm in
  let flip v eq =
    if defined eq v then (v |-> minus_num(apply eq v)) eq else eq in
  let rec allsubsets s =
    match s with
      [] -> [[]]
    | (a::t) -> let res = allsubsets t in
                map (fun b -> a::b) res @ res in
  let evaluate env lin =
    foldr (fun x c s -> s +/ c */ apply env x) lin (Int 0) in
  let rec solve (vs,eqs) =
    match (vs,eqs) with
      [],[] -> (0 |=> Int 1)
    | _,eq::oeqs ->
          let v = hd(intersect vs (dom eq)) in
          let c = apply eq v in
          let vdef = lincomb_cmul (Int(-1) // c) eq in
          let eliminate eqn =
            if not(defined eqn v) then eqn else
            lincomb_add (lincomb_cmul (apply eqn v) vdef) eqn in
          let soln = solve (subtract vs [v],map eliminate oeqs) in
          (v |-> evaluate soln (undefine v vdef)) soln in
  let rec combinations k l =
    if k = 0 then [[]] else
    match l with
      [] -> []
    | h::t -> map (fun c -> h::c) (combinations (k - 1) t) @
              combinations k t in
  let vertices vs eqs =
    let vertex cmb =
      let soln = solve(vs,cmb) in
      map (fun v -> tryapplyd soln v (Int 0)) vs in
    let rawvs = mapfilter vertex (combinations (length vs) eqs) in
    let unset = filter (forall (fun c -> c >=/ Int 0)) rawvs in
    itlist (insert' (forall2 (=/))) unset [] in
  let subsumes l m = forall2 (fun x y -> abs_num x <=/ abs_num y) l m in
  let rec subsume todo dun =
    match todo with
      [] -> dun
    | v::ovs -> let dun' = if exists (fun w -> subsumes w v) dun then dun
                           else v::(filter (fun w -> not(subsumes v w)) dun) in
                subsume ovs dun' in
  let NORM_CMUL_RULE =
    let MATCH_pth = (MATCH_MP o prove)
     (`!b x. b >= norm(x) ==> !c. abs(c) * b >= norm(c % x)`,
      SIMP_TAC[NORM_MUL; real_ge; REAL_LE_LMUL; REAL_ABS_POS]) in
    fun c th -> ISPEC(term_of_rat c) (MATCH_pth th) in
  let NORM_ADD_RULE =
    let MATCH_pth = (MATCH_MP o prove)
     (`!b1 b2 x1 x2. b1 >= norm(x1) /\ b2 >= norm(x2)
                     ==> b1 + b2 >= norm(x1 + x2)`,
      REWRITE_TAC[real_ge] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC NORM_TRIANGLE_LE THEN ASM_SIMP_TAC[REAL_LE_ADD2]) in
    fun th1 th2 -> MATCH_pth (CONJ th1 th2) in
  let INEQUALITY_CANON_RULE =
    CONV_RULE(LAND_CONV REAL_POLY_CONV) o
    CONV_RULE(LAND_CONV REAL_RAT_REDUCE_CONV) o
    GEN_REWRITE_RULE I [REAL_ARITH `s >= t <=> s - t >= &0`] in
  let NORM_CANON_CONV =
    let APPLY_pth1 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `x:real^N = &1 % x`]
    and APPLY_pth2 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `x - y:real^N = x + --y`]
    and APPLY_pth3 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `--x:real^N = -- &1 % x`]
    and APPLY_pth4 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `&0 % x:real^N = vec 0`;
      VECTOR_ARITH `c % vec 0:real^N = vec 0`]
    and APPLY_pth5 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `c % (d % x) = (c * d) % x`]
    and APPLY_pth6 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `c % (x + y) = c % x + c % y`]
    and APPLY_pth7 = GEN_REWRITE_CONV I
     [VECTOR_ARITH `vec 0 + x = x`;
      VECTOR_ARITH `x + vec 0 = x`]
    and APPLY_pth8 =
     GEN_REWRITE_CONV I [VECTOR_ARITH `c % x + d % x = (c + d) % x`] THENC
     LAND_CONV REAL_RAT_ADD_CONV THENC
     GEN_REWRITE_CONV TRY_CONV [VECTOR_ARITH `&0 % x = vec 0`]
    and APPLY_pth9 =
     GEN_REWRITE_CONV I
      [VECTOR_ARITH `(c % x + z) + d % x = (c + d) % x + z`;
       VECTOR_ARITH `c % x + (d % x + z) = (c + d) % x + z`;
       VECTOR_ARITH `(c % x + w) + (d % x + z) = (c + d) % x + (w + z)`] THENC
     LAND_CONV(LAND_CONV REAL_RAT_ADD_CONV)
    and APPLY_ptha =
     GEN_REWRITE_CONV I [VECTOR_ARITH `&0 % x + y = y`]
    and APPLY_pthb =
     GEN_REWRITE_CONV I
      [VECTOR_ARITH `c % x + d % y = c % x + d % y`;
       VECTOR_ARITH `(c % x + z) + d % y = c % x + (z + d % y)`;
       VECTOR_ARITH `c % x + (d % y + z) = c % x + (d % y + z)`;
       VECTOR_ARITH `(c % x + w) + (d % y + z) = c % x + (w + (d % y + z))`]
    and APPLY_pthc =
     GEN_REWRITE_CONV I
      [VECTOR_ARITH `c % x + d % y = d % y + c % x`;
       VECTOR_ARITH `(c % x + z) + d % y = d % y + (c % x + z)`;
       VECTOR_ARITH `c % x + (d % y + z) = d % y + (c % x + z)`;
       VECTOR_ARITH `(c % x + w) + (d % y + z) = d % y + ((c % x + w) + z)`]
    and APPLY_pthd =
     GEN_REWRITE_CONV TRY_CONV
      [VECTOR_ARITH `x + vec 0 = x`] in
    let headvector tm =
      match tm with
        Comb(Comb(Const("vector_add",_),Comb(Comb(Const("%",_),l),v)),r) -> v
      | Comb(Comb(Const("%",_),l),v) -> v
      | _ -> failwith "headvector: non-canonical term" in
    let rec VECTOR_CMUL_CONV tm =
     ((APPLY_pth5 THENC LAND_CONV REAL_RAT_MUL_CONV) ORELSEC
      (APPLY_pth6 THENC BINOP_CONV VECTOR_CMUL_CONV)) tm
    and VECTOR_ADD_CONV tm =
      try APPLY_pth7 tm with Failure _ ->
      try APPLY_pth8 tm with Failure _ ->
      match tm with
        Comb(Comb(Const("vector_add",_),lt),rt) ->
          let l = headvector lt and r = headvector rt in
          if l < r then (APPLY_pthb THENC
                         RAND_CONV VECTOR_ADD_CONV THENC
                         APPLY_pthd) tm
          else if r < l then (APPLY_pthc THENC
                              RAND_CONV VECTOR_ADD_CONV THENC
                              APPLY_pthd) tm else
          (APPLY_pth9 THENC
            ((APPLY_ptha THENC VECTOR_ADD_CONV) ORELSEC
             RAND_CONV VECTOR_ADD_CONV THENC
             APPLY_pthd)) tm
      | _ -> REFL tm in
    let rec VECTOR_CANON_CONV tm =
      match tm with
        Comb(Comb(Const("vector_add",_),l),r) ->
          let lth = VECTOR_CANON_CONV l and rth = VECTOR_CANON_CONV r in
          let th = MK_COMB(AP_TERM (rator(rator tm)) lth,rth) in
          CONV_RULE (RAND_CONV VECTOR_ADD_CONV) th
      | Comb(Comb(Const("%",_),l),r) ->
          let rth = AP_TERM (rator tm) (VECTOR_CANON_CONV r) in
          CONV_RULE (RAND_CONV(APPLY_pth4 ORELSEC VECTOR_CMUL_CONV)) rth
      | Comb(Comb(Const("vector_sub",_),l),r) ->
          (APPLY_pth2 THENC VECTOR_CANON_CONV) tm
      | Comb(Const("vector_neg",_),t) ->
          (APPLY_pth3 THENC VECTOR_CANON_CONV) tm
      | Comb(Const("vec",_),n) when is_numeral n & dest_numeral n =/ Int 0 ->
          REFL tm
      | _ -> APPLY_pth1 tm in
    fun tm ->
      match tm with
       Comb(Const("vector_norm",_),e) -> RAND_CONV VECTOR_CANON_CONV tm
      | _ -> failwith "NORM_CANON_CONV" in
  let REAL_VECTOR_COMBO_PROVER =
    let pth_zero = prove(`norm(vec 0:real^N) = &0`,REWRITE_TAC[NORM_0])
    and tv_n = mk_vartype "N" in
    fun translator (nubs,ges,gts) ->
      let sources = map (rand o rand o concl) nubs
      and rawdests = itlist (find_normedterms o lhand o concl) (ges @ gts) [] in
      if not (forall fst rawdests) then failwith "Sanity check" else
      let dests = setify (map snd rawdests) in
      let srcfuns = map vector_lincomb sources
      and destfuns = map vector_lincomb dests in
      let vvs = itlist (union o dom) (srcfuns @ destfuns) [] in
      let n = length srcfuns in
      let nvs = 1--n in
      let srccombs = zip srcfuns nvs in
      let consider d =
        let coefficients x =
            let inp = if defined d x then 0 |=> minus_num(apply d x)
                      else undefined in
          itlist (fun (f,v) g -> if defined f x then (v |-> apply f x) g else g)
                 srccombs inp in
        let equations = map coefficients vvs
        and inequalities = map (fun n -> (n |=> Int 1)) nvs in
        let plausiblevertices f =
          let flippedequations = map (itlist flip f) equations in
          let constraints = flippedequations @ inequalities in
          let rawverts = vertices nvs constraints in
          let check_solution v =
            let f = itlist2 (|->) nvs v (0 |=> Int 1) in
            forall (fun e -> evaluate f e =/ Int 0) flippedequations in
          let goodverts = filter check_solution rawverts in
          let signfixups = map (fun n -> if mem n f then -1 else 1) nvs in
          map (map2 (fun s c -> Int s */ c) signfixups) goodverts in
        let allverts = itlist (@) (map plausiblevertices (allsubsets nvs)) [] in
        subsume allverts [] in
      let compute_ineq v =
        let ths = mapfilter (fun (v,t) -> if v =/ Int 0 then fail()
                                          else  NORM_CMUL_RULE v t)
                            (zip v nubs) in
        INEQUALITY_CANON_RULE (end_itlist NORM_ADD_RULE ths) in
      let ges' = mapfilter compute_ineq (itlist ((@) o consider) destfuns []) @
                 map INEQUALITY_CANON_RULE nubs @ ges in
      let zerodests = filter
        (fun t -> dom(vector_lincomb t) = []) (map snd rawdests) in
      REAL_LINEAR_PROVER translator
       (map (fun t -> INST_TYPE [last(snd(dest_type(type_of t))),tv_n] pth_zero)
            zerodests,
        map (CONV_RULE(ONCE_DEPTH_CONV NORM_CANON_CONV THENC
                       LAND_CONV REAL_POLY_CONV)) ges',
        map (CONV_RULE(ONCE_DEPTH_CONV NORM_CANON_CONV THENC
                       LAND_CONV REAL_POLY_CONV)) gts) in
  let REAL_VECTOR_INEQ_PROVER =
    let pth = prove
     (`norm(x) = n ==> norm(x) >= &0 /\ n >= norm(x)`,
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC[real_ge; NORM_POS_LE] THEN REAL_ARITH_TAC) in
    let NORM_MP = MATCH_MP pth in
    fun translator (ges,gts) ->
    let ntms = itlist find_normedterms (map (lhand o concl) (ges @ gts)) [] in
    let lctab = vector_lincombs (map snd (filter (not o fst) ntms)) in
    let asl = map (fun (t,_) ->
       ASSUME(mk_eq(mk_icomb(mk_const("vector_norm",[]),t),
                    genvar `:real`))) lctab in
    let replace_conv = GEN_REWRITE_CONV TRY_CONV asl in
    let replace_rule = CONV_RULE (LAND_CONV (replacenegnorms replace_conv)) in
    let ges' =
       itlist (fun th ths -> CONJUNCT1(NORM_MP th)::ths)
              asl (map replace_rule ges)
    and gts' = map replace_rule gts
    and nubs = map (CONJUNCT2 o NORM_MP) asl in
    let th1 = REAL_VECTOR_COMBO_PROVER translator (nubs,ges',gts') in
    let th2 = INST
     (map (fun th -> let l,r = dest_eq(concl th) in (l,r)) asl) th1 in
    itlist PROVE_HYP (map (REFL o lhand o concl) asl) th2 in
  let REAL_VECTOR_PROVER =
    let rawrule =
      GEN_REWRITE_RULE I [REAL_ARITH `x = &0 <=> x >= &0 /\ --x >= &0`] in
    let splitequation th acc =
      let th1,th2 = CONJ_PAIR(rawrule th) in
      th1::CONV_RULE(LAND_CONV REAL_POLY_NEG_CONV) th2::acc in
    fun translator (eqs,ges,gts) ->
      REAL_VECTOR_INEQ_PROVER translator
         (itlist splitequation eqs ges,gts) in
  let pth = prove
   (`(!x y:real^N. x = y <=> norm(x - y) <= &0) /\
     (!x y:real^N. ~(x = y) <=> ~(norm(x - y) <= &0))`,
    REWRITE_TAC[NORM_LE_0; VECTOR_SUB_EQ]) in
  let conv1 = GEN_REWRITE_CONV TRY_CONV [pth] in
  let conv2 tm = (conv1 tm,conv1(mk_neg tm)) in
  let init = GEN_REWRITE_CONV ONCE_DEPTH_CONV [DECIMAL] THENC
             REAL_RAT_REDUCE_CONV THENC
             GEN_REWRITE_CONV ONCE_DEPTH_CONV [dist] THENC
             GEN_NNF_CONV true (conv1,conv2)
  and pure = GEN_REAL_ARITH REAL_VECTOR_PROVER in
  fun tm -> let th = init tm in EQ_MP (SYM th) (pure(rand(concl th)));;

let NORM_ARITH_TAC = CONV_TAC NORM_ARITH;;

let ASM_NORM_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_forall o concl))) THEN
  NORM_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Dot product in terms of the norm rather than conversely.                  *)
(* ------------------------------------------------------------------------- *)

let DOT_NORM = prove
 (`!x y. x dot y = (norm(x + y) pow 2 - norm(x) pow 2 - norm(y) pow 2) / &2`,
  REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_SYM] THEN REAL_ARITH_TAC);;

let DOT_NORM_NEG = prove
 (`!x y. x dot y = ((norm(x) pow 2 + norm(y) pow 2) - norm(x - y) pow 2) / &2`,
  REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  REAL_ARITH_TAC);;

let DOT_NORM_SUB = prove
 (`!x y. x dot y = ((norm(x) pow 2 + norm(y) pow 2) - norm(x - y) pow 2) / &2`,
  REWRITE_TAC[NORM_POW_2; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Equality of vectors in terms of dot products.                             *)
(* ------------------------------------------------------------------------- *)

let VECTOR_EQ = prove
 (`!x y. (x = y) <=> (x dot x = x dot y) /\ (y dot y = x dot x)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM DOT_EQ_0] THEN
  SIMP_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence more metric properties.                                             *)
(* ------------------------------------------------------------------------- *)

let DIST_REFL = prove
 (`!x. dist(x,x) = &0`,
  NORM_ARITH_TAC);;

let DIST_SYM = prove
 (`!x y. dist(x,y) = dist(y,x)`,
  NORM_ARITH_TAC);;

let DIST_POS_LE = prove
 (`!x y. &0 <= dist(x,y)`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE = prove
 (`!x:real^N y z. dist(x,z) <= dist(x,y) + dist(y,z)`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE_ALT = prove
 (`!x y z. dist(y,z) <= dist(x,y) + dist(x,z)`,
  NORM_ARITH_TAC);;

let DIST_EQ_0 = prove
 (`!x y. (dist(x,y) = &0) <=> (x = y)`,
  NORM_ARITH_TAC);;

let DIST_POS_LT = prove
 (`!x y. ~(x = y) ==> &0 < dist(x,y)`,
  NORM_ARITH_TAC);;

let DIST_NZ = prove
 (`!x y. ~(x = y) <=> &0 < dist(x,y)`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE_LE = prove
 (`!x y z e. dist(x,z) + dist(y,z) <= e ==> dist(x,y) <= e`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE_LT = prove
 (`!x y z e. dist(x,z) + dist(y,z) < e ==> dist(x,y) < e`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE_HALF_L = prove
 (`!x1 x2 y. dist(x1,y) < e / &2 /\ dist(x2,y) < e / &2 ==> dist(x1,x2) < e`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE_HALF_R = prove
 (`!x1 x2 y. dist(y,x1) < e / &2 /\ dist(y,x2) < e / &2 ==> dist(x1,x2) < e`,
  NORM_ARITH_TAC);;

let DIST_TRIANGLE_ADD = prove
 (`!x x' y y'. dist(x + y,x' + y') <= dist(x,x') + dist(y,y')`,
  NORM_ARITH_TAC);;

let DIST_MUL = prove
 (`!x y c. dist(c % x,c % y) = abs(c) * dist(x,y)`,
  REWRITE_TAC[dist; GSYM VECTOR_SUB_LDISTRIB; NORM_MUL]);;

let DIST_TRIANGLE_ADD_HALF = prove
 (`!x x' y y':real^N.
    dist(x,x') < e / &2 /\ dist(y,y') < e / &2 ==> dist(x + y,x' + y') < e`,
  NORM_ARITH_TAC);;

let DIST_LE_0 = prove
 (`!x y. dist(x,y) <= &0 <=> x = y`,
  NORM_ARITH_TAC);;

let DIST_EQ = prove
 (`!w x y z. dist(w,x) = dist(y,z) <=> dist(w,x) pow 2 = dist(y,z) pow 2`,
  REWRITE_TAC[dist; NORM_POW_2; NORM_EQ]);;

let DIST_0 = prove
 (`!x. dist(x,vec 0) = norm(x) /\ dist(vec 0,x) = norm(x)`,
  NORM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Sums of vectors.                                                          *)
(* ------------------------------------------------------------------------- *)

let NEUTRAL_VECTOR_ADD = prove
 (`neutral(+) = vec 0:real^N`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[VECTOR_ARITH `x + y = y <=> x = vec 0`;
              VECTOR_ARITH `x + y = x <=> y = vec 0`]);;

let MONOIDAL_VECTOR_ADD = prove
 (`monoidal((+):real^N->real^N->real^N)`,
  REWRITE_TAC[monoidal; NEUTRAL_VECTOR_ADD] THEN
  REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC);;

let vsum = new_definition
  `(vsum:(A->bool)->(A->real^N)->real^N) s f = lambda i. sum s (\x. f(x)$i)`;;

let VSUM_CLAUSES = prove
 (`(!f. vsum {} f = vec 0) /\
   (!x f s. FINITE s
            ==> (vsum (x INSERT s) f =
                 if x IN s then vsum s f else f(x) + vsum s f))`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT; SUM_CLAUSES] THEN
  SIMP_TAC[VEC_COMPONENT] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT]);;

let VSUM = prove
 (`!f s. FINITE s ==> vsum s f = iterate (+) s f`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; ITERATE_CLAUSES; MONOIDAL_VECTOR_ADD] THEN
  REWRITE_TAC[NEUTRAL_VECTOR_ADD]);;

let VSUM_EQ_0 = prove
 (`!f s. (!x:A. x IN s ==> (f(x) = vec 0)) ==> (vsum s f = vec 0)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; vec; SUM_EQ_0]);;

let VSUM_0 = prove
 (`vsum s (\x. vec 0) = vec 0`,
  SIMP_TAC[VSUM_EQ_0]);;

let VSUM_LMUL = prove
 (`!f c s.  vsum s (\x. c % f(x)) = c % vsum s f`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_MUL_COMPONENT; SUM_LMUL]);;

let VSUM_RMUL = prove
 (`!c s v. vsum s (\x. c x % v) = (sum s c) % v`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_MUL_COMPONENT; SUM_RMUL]);;

let VSUM_ADD = prove
 (`!f g s. FINITE s ==> (vsum s (\x. f x + g x) = vsum s f + vsum s g)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT; SUM_ADD]);;

let VSUM_SUB = prove
 (`!f g s. FINITE s ==> (vsum s (\x. f x - g x) = vsum s f - vsum s g)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_SUB_COMPONENT; SUM_SUB]);;

let VSUM_CONST = prove
 (`!c s. FINITE s ==> (vsum s (\n. c) = &(CARD s) % c)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_CONST; VECTOR_MUL_COMPONENT]);;

let VSUM_COMPONENT = prove
 (`!s f i. 1 <= i /\ i <= dimindex(:N)
           ==> ((vsum s (f:A->real^N))$i = sum s (\x. f(x)$i))`,
  SIMP_TAC[vsum; LAMBDA_BETA]);;

let VSUM_IMAGE = prove
 (`!f g s. FINITE s /\ (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (vsum (IMAGE f s) g = vsum s (g o f))`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o lhs o snd) THEN
  ASM_REWRITE_TAC[o_DEF]);;

let VSUM_UNION = prove
 (`!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (vsum (s UNION t) f = vsum s f + vsum t f)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_UNION; VECTOR_ADD_COMPONENT]);;

let VSUM_DIFF = prove
 (`!f s t. FINITE s /\ t SUBSET s
           ==> (vsum (s DIFF t) f = vsum s f - vsum t f)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_DIFF; VECTOR_SUB_COMPONENT]);;

let VSUM_DELETE = prove
 (`!f s a. FINITE s /\ a IN s
           ==> vsum (s DELETE a) f = vsum s f - f a`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_DELETE; VECTOR_SUB_COMPONENT]);;

let VSUM_INCL_EXCL = prove
 (`!s t (f:A->real^N).
        FINITE s /\ FINITE t
        ==> vsum s f + vsum t f = vsum (s UNION t) f + vsum (s INTER t) f`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT] THEN
  SIMP_TAC[SUM_INCL_EXCL]);;

let VSUM_NEG = prove
 (`!f s. vsum s (\x. --f x) = --vsum s f`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_NEG; VECTOR_NEG_COMPONENT]);;

let VSUM_EQ = prove
 (`!f g s. (!x. x IN s ==> (f x = g x)) ==> (vsum s f = vsum s g)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]);;

let VSUM_SUPERSET = prove
 (`!f:A->real^N u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = vec 0))
        ==> (vsum v f = vsum u f)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VEC_COMPONENT; SUM_SUPERSET]);;

let VSUM_SUPPORT = prove
 (`!f:A->real^N s. vsum {x | x IN s /\ ~(f x = vec 0)} f = vsum s f`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
  SET_TAC[]);;

let VSUM_EQ_SUPERSET = prove
 (`!f s t:A->bool.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> f(x) = vec 0)
        ==> vsum s f = vsum t g`,
  MESON_TAC[VSUM_SUPERSET; VSUM_EQ]);;

let VSUM_UNION_RZERO = prove
 (`!f:A->real^N u v.
        (!x. x IN v /\ ~(x IN u) ==> (f(x) = vec 0))
        ==> (vsum (u UNION v) f = vsum u f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_SUPERSET THEN ASM SET_TAC[]);;

let VSUM_UNION_LZERO = prove
 (`!f:A->real^N u v.
        (!x. x IN u /\ ~(x IN v) ==> (f(x) = vec 0))
        ==> (vsum (u UNION v) f = vsum v f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_SUPERSET THEN ASM SET_TAC[]);;

let VSUM_RESTRICT = prove
 (`!f s. vsum s (\x. if x IN s then f(x) else vec 0) = vsum s f`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[]);;

let VSUM_RESTRICT_SET = prove
 (`!P s f. vsum {x | x IN s /\ P x} f =
           vsum s (\x. if P x then f x else vec 0)`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VEC_COMPONENT; SUM_RESTRICT_SET;
           COND_COMPONENT]);;

let VSUM_CASES = prove
 (`!s P f g. FINITE s
             ==> vsum s (\x:A. if P x then (f x):real^N else g x) =
                 vsum {x | x IN s /\ P x} f + vsum {x | x IN s /\ ~P x} g`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT; SUM_CASES;
           COND_COMPONENT]);;

let VSUM_SING = prove
 (`!f x. vsum {x} f = f(x)`,
  SIMP_TAC[VSUM_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; VECTOR_ADD_RID]);;

let VSUM_NORM = prove
 (`!f s. FINITE s ==> norm(vsum s f) <= sum s (\x. norm(f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; NORM_0; REAL_LE_REFL] THEN
  NORM_ARITH_TAC);;

let VSUM_NORM_LE = prove
 (`!s f:A->real^N g.
        FINITE s /\ (!x. x IN s ==> norm(f x) <= g(x))
        ==> norm(vsum s f) <= sum s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\x:A. norm(f x :real^N))` THEN
  ASM_SIMP_TAC[VSUM_NORM; SUM_LE]);;

let VSUM_NORM_TRIANGLE = prove
 (`!s f b. FINITE s /\ sum s (\a. norm(f a)) <= b ==> norm(vsum s f) <= b`,
  MESON_TAC[VSUM_NORM; REAL_LE_TRANS]);;

let VSUM_NORM_BOUND = prove
 (`!s f b. FINITE s /\ (!x:A. x IN s ==> norm(f(x)) <= b)
           ==> norm(vsum s f) <= &(CARD s) * b`,
  SIMP_TAC[GSYM SUM_CONST; VSUM_NORM_LE]);;

let VSUM_CLAUSES_NUMSEG = prove
 (`(!m. vsum(m..0) f = if m = 0 then f(0) else vec 0) /\
   (!m n. vsum(m..SUC n) f = if m <= SUC n then vsum(m..n) f + f(SUC n)
                             else vsum(m..n) f)`,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[VSUM_SING; VSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; VECTOR_ADD_AC]);;

let VSUM_CLAUSES_RIGHT = prove
 (`!f m n. 0 < n /\ m <= n ==> vsum(m..n) f = vsum(m..n-1) f + (f n):real^N`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[LT_REFL; VSUM_CLAUSES_NUMSEG; SUC_SUB1]);;

let VSUM_CMUL_NUMSEG = prove
 (`!f c m n. vsum (m..n) (\x. c % f x) = c % vsum (m..n) f`,
  SIMP_TAC[VSUM_LMUL; FINITE_NUMSEG]);;

let VSUM_EQ_NUMSEG = prove
 (`!f g m n.
         (!x. m <= x /\ x <= n ==> (f x = g x))
         ==> (vsum(m .. n) f = vsum(m .. n) g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG]);;

let VSUM_IMAGE_GEN = prove
 (`!f:A->B g s.
        FINITE s
        ==> (vsum s g =
             vsum (IMAGE f s) (\y. vsum {x | x IN s /\ (f(x) = y)} g))`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_IMAGE_GEN]);;

let VSUM_GROUP = prove
 (`!f:A->B g s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> vsum t (\y. vsum {x | x IN s /\ f(x) = y} g) = vsum s g`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; SUM_GROUP]);;

let VSUM_VMUL = prove
 (`!f v s. (sum s f) % v = vsum s (\x. f(x) % v)`,
  REWRITE_TAC[VSUM_RMUL]);;

let VSUM_DELTA = prove
 (`!s a. vsum s (\x. if x = a then b else vec 0) =
         if a IN s then b else vec 0`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VSUM_COMPONENT; COND_COMPONENT] THEN
  SIMP_TAC[VEC_COMPONENT; SUM_DELTA]);;

let VSUM_ADD_NUMSEG = prove
 (`!f g m n. vsum(m..n) (\i. f i + g i) = vsum(m..n) f + vsum(m..n) g`,
  SIMP_TAC[VSUM_ADD; FINITE_NUMSEG]);;

let VSUM_SUB_NUMSEG = prove
 (`!f g m n. vsum(m..n) (\i. f i - g i) = vsum(m..n) f - vsum(m..n) g`,
  SIMP_TAC[VSUM_SUB; FINITE_NUMSEG]);;

let VSUM_ADD_SPLIT = prove
 (`!f m n p.
       m <= n + 1 ==> vsum(m..n + p) f = vsum(m..n) f + vsum(n + 1..n + p) f`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VSUM_COMPONENT; VECTOR_ADD_COMPONENT;
           SUM_ADD_SPLIT]);;

let VSUM_VSUM_PRODUCT = prove
 (`!s:A->bool t:A->B->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> vsum s (\i. vsum (t i) (x i)) =
            vsum {i,j | i IN s /\ j IN t i} (\(i,j). x i j)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VSUM_COMPONENT; COND_COMPONENT] THEN
  SIMP_TAC[SUM_SUM_PRODUCT] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let VSUM_IMAGE_NONZERO = prove
 (`!d:B->real^N i:A->B s.
    FINITE s /\
    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ i x = i y ==> d(i x) = vec 0)
    ==> vsum (IMAGE i s) d = vsum s (d o i)`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IMAGE_CLAUSES; VSUM_CLAUSES; FINITE_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `vsum s ((d:B->real^N) o (i:A->B)) = vsum (IMAGE i s) d`
  SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
  REWRITE_TAC[VECTOR_ARITH `a = x + a <=> x = vec 0`] THEN
  ASM_MESON_TAC[IN_IMAGE]);;

let VSUM_UNION_NONZERO = prove
 (`!f s t. FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> f(x) = vec 0)
           ==> vsum (s UNION t) f = vsum s f + vsum t f`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT] THEN
  SIMP_TAC[VEC_COMPONENT; SUM_UNION_NONZERO]);;

let VSUM_UNIONS_NONZERO = prove
 (`!f s. FINITE s /\ (!t:A->bool. t IN s ==> FINITE t) /\
         (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                    ==> f x = vec 0)
         ==> vsum (UNIONS s) f = vsum s (\t. vsum t f)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; VSUM_CLAUSES; IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`t:A->bool`; `s:(A->bool)->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN ASM_SIMP_TAC[VSUM_CLAUSES] THEN
  ANTS_TAC THENL  [ASM_MESON_TAC[]; DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
  STRIP_TAC THEN MATCH_MP_TAC VSUM_UNION_NONZERO THEN
  ASM_SIMP_TAC[FINITE_UNIONS; IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[]);;

let VSUM_CLAUSES_LEFT = prove
 (`!f m n. m <= n ==> vsum(m..n) f = f m + vsum(m + 1..n) f`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT] THEN
  SIMP_TAC[VEC_COMPONENT; SUM_CLAUSES_LEFT]);;

let VSUM_DIFFS = prove
 (`!m n. vsum(m..n) (\k. f(k) - f(k + 1)) =
          if m <= n then f(m) - f(n + 1) else vec 0`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[VSUM_CLAUSES_NUMSEG; LE] THEN
  ASM_CASES_TAC `m = SUC n` THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; VECTOR_ADD_LID] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD1] THEN VECTOR_ARITH_TAC);;

let VSUM_DIFFS_ALT = prove
 (`!m n. vsum(m..n) (\k. f(k + 1) - f(k)) =
          if m <= n then f(n + 1) - f(m) else vec 0`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_NEG_SUB] THEN
  SIMP_TAC[VSUM_NEG; VSUM_DIFFS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_NEG_SUB; VECTOR_NEG_0]);;

let VSUM_DELETE_CASES = prove
 (`!x f s.
        FINITE(s:A->bool)
        ==> vsum(s DELETE x) f = if x IN s then vsum s f - f x else vsum s f`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SET_RULE `~(x IN s) ==> s DELETE x = s`] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [MATCH_MP (SET_RULE `x IN s ==> s = x INSERT (s DELETE x)`) th]) THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; FINITE_DELETE; IN_DELETE] THEN VECTOR_ARITH_TAC);;

let VSUM_EQ_GENERAL = prove
  (`!s:A->bool t:B->bool (f:A->real^N) g h.
        (!y. y IN t ==> ?!x. x IN s /\ h x = y) /\
        (!x. x IN s ==> h x IN t /\ g(h x) = f x)
        ==> vsum s f = vsum t g`,
   SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL THEN
   EXISTS_TAC `h:A->B` THEN ASM_MESON_TAC[]);;

let VSUM_EQ_GENERAL_INVERSES = prove
 (`!s t (f:A->real^N) (g:B->real^N) h k.
        (!y. y IN t ==> k y IN s /\ h (k y) = y) /\
        (!x. x IN s ==> h x IN t /\ k (h x) = x /\ g (h x) = f x)
        ==> vsum s f = vsum t g`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC [`h:A->B`; `k:B->A`] THEN ASM_MESON_TAC[]);;

let VSUM_NORM_ALLSUBSETS_BOUND = prove
 (`!f:A->real^N p e.
        FINITE p /\
        (!q. q SUBSET p ==> norm(vsum q f) <= e)
        ==> sum p (\x. norm(f x)) <= &2 * &(dimindex(:N)) * e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum p (\x:A. sum (1..dimindex(:N)) (\i. abs((f x:real^N)$i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[NORM_LE_L1]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&2 * &n * e = &n * &2 * e`] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
   [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {x:A | x IN p /\ &0 <= (f x:real^N)$k} (\x. abs((f x)$k)) +
              sum {x | x IN p /\ (f x)$k < &0} (\x. abs((f x)$k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= a`) THEN
    MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_SIMP_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN p` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= e /\ y <= e ==> x + y <= &2 * e`) THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_ABS_NEG] THEN
  CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `!g. sum s g = sum s f /\ sum s g <= e ==> sum s f <= e`)
  THENL
   [EXISTS_TAC `\x. ((f:A->real^N) x)$k`;
    EXISTS_TAC `\x. --(((f:A->real^N) x)$k)`] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPONENT; SUM_NEG; FINITE_RESTRICT] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) <= e ==> x <= e`) THEN
  REWRITE_TAC[REAL_ABS_NEG] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs((vsum q f)$k) <= norm(vsum q f) /\
    norm(vsum q f) <= e
    ==> abs((vsum q f)$k) <= e`) THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC[]);;

let DOT_LSUM = prove
 (`!s f y. FINITE s ==> (vsum s f) dot y = sum s (\x. f(x) dot y)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; SUM_CLAUSES; DOT_LZERO; DOT_LADD]);;

let DOT_RSUM = prove
 (`!s f x. FINITE s ==> x dot (vsum s f) = sum s (\y. x dot f(y))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; SUM_CLAUSES; DOT_RZERO; DOT_RADD]);;

let VSUM_OFFSET = prove
 (`!p f m n. vsum(m + p..n + p) f = vsum(m..n) (\i. f (i + p))`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VEC_COMPONENT; SUM_OFFSET]);;

let VSUM_OFFSET_0 = prove
 (`!f m n. m <= n ==> vsum(m..n) f = vsum(0..n - m) (\i. f (i + m))`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VEC_COMPONENT; SUM_OFFSET_0]);;

let VSUM_TRIV_NUMSEG = prove
 (`!f m n. n < m ==> vsum(m..n) f = vec 0`,
  SIMP_TAC[GSYM NUMSEG_EMPTY; VSUM_CLAUSES]);;

let VSUM_CONST_NUMSEG = prove
 (`!c m n. vsum(m..n) (\n. c) = &((n + 1) - m) % c`,
  SIMP_TAC[VSUM_CONST; FINITE_NUMSEG; CARD_NUMSEG]);;

let VSUM_SUC = prove
 (`!f m n. vsum (SUC n..SUC m) f = vsum (n..m) (f o SUC)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `SUC n..SUC m = IMAGE SUC (n..m)` SUBST1_TAC THENL
   [REWRITE_TAC [ADD1; NUMSEG_OFFSET_IMAGE] THEN
    REWRITE_TAC [ONE; ADD_SUC; ADD_0; ETA_AX];
    SIMP_TAC [VSUM_IMAGE; FINITE_NUMSEG; SUC_INJ]]);;

let VSUM_BIJECTION = prove
 (`!f:A->real^N p s:A->bool.
                (!x. x IN s ==> p(x) IN s) /\
                (!y. y IN s ==> ?!x. x IN s /\ p(x) = y)
                ==> vsum s f = vsum s (f o p)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC VSUM_EQ_GENERAL THEN EXISTS_TAC `p:A->A` THEN
  ASM_REWRITE_TAC[o_THM]);;

let VSUM_PARTIAL_SUC = prove
 (`!f g:num->real^N m n.
        vsum (m..n) (\k. f(k) % (g(k + 1) - g(k))) =
            if m <= n then f(n + 1) % g(n + 1) - f(m) % g(m) -
                           vsum (m..n) (\k. (f(k + 1) - f(k)) % g(k + 1))
            else vec 0`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[VSUM_TRIV_NUMSEG; GSYM NOT_LE] THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG] THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[ARITH] THENL
     [VECTOR_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE]) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[GSYM NOT_LT; VSUM_TRIV_NUMSEG; ARITH_RULE `n < SUC n`] THEN
  ASM_SIMP_TAC[GSYM ADD1; ADD_CLAUSES] THEN VECTOR_ARITH_TAC);;

let VSUM_PARTIAL_PRE = prove
 (`!f g:num->real^N m n.
        vsum (m..n) (\k. f(k) % (g(k) - g(k - 1))) =
            if m <= n then f(n + 1) % g(n) - f(m) % g(m - 1) -
                           vsum (m..n) (\k. (f(k + 1) - f(k)) % g(k))
            else vec 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `\k. (g:num->real^N)(k - 1)`;
                 `m:num`; `n:num`] VSUM_PARTIAL_SUC) THEN
  REWRITE_TAC[ADD_SUB] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let VSUM_COMBINE_L = prove
 (`!f m n p.
        0 < n /\ m <= n /\ n <= p + 1
        ==> vsum(m..n - 1) f + vsum(n..p) f = vsum(m..p) f`,
  SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VSUM_COMPONENT; SUM_COMBINE_L]);;

let VSUM_COMBINE_R = prove
 (`!f m n p.
        m <= n + 1 /\ n <= p
        ==> vsum(m..n) f + vsum(n + 1..p) f = vsum(m..p) f`,
  SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VSUM_COMPONENT; SUM_COMBINE_R]);;

let VSUM_INJECTION = prove
 (`!f p s.
         FINITE s /\
         (!x. x IN s ==> p x IN s) /\
         (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
         ==> vsum s (f o p) = vsum s f`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SUM_INJECTION) THEN
  SIMP_TAC[CART_EQ; VSUM_COMPONENT; o_DEF]);;

let VSUM_SWAP = prove
 (`!f s t.
         FINITE s /\ FINITE t
         ==> vsum s (\i. vsum t (f i)) = vsum t (\j. vsum s (\i. f i j))`,
   SIMP_TAC[CART_EQ; VSUM_COMPONENT] THEN REPEAT STRIP_TAC THEN
   W(MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o lhs o snd) THEN
   ASM_REWRITE_TAC[]);;

let VSUM_SWAP_NUMSEG = prove
  (`!a b c d f.
         vsum (a..b) (\i. vsum (c..d) (f i)) =
         vsum (c..d) (\j. vsum (a..b) (\i. f i j))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_SWAP THEN REWRITE_TAC[FINITE_NUMSEG]);;

let VSUM_ADD_GEN = prove
 (`!f g s.
       FINITE {x | x IN s /\ ~(f x = vec 0)} /\
       FINITE {x | x IN s /\ ~(g x = vec 0)}
       ==> vsum s (\x. f x + g x) = vsum s f + vsum s g`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC[CART_EQ; vsum; LAMBDA_BETA; VECTOR_ADD_COMPONENT] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_ADD_GEN THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_AND THEN
  CONJ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[VEC_COMPONENT]);;

let VSUM_CASES_1 = prove
 (`!s a. FINITE s /\ a IN s
         ==> vsum s (\x. if x = a then y else f(x)) = vsum s f + (y - f a)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VSUM_CASES] THEN
  ASM_SIMP_TAC[GSYM DELETE; VSUM_DELETE] THEN
  ASM_SIMP_TAC[SET_RULE `a IN s ==> {x | x IN s /\ x = a} = {a}`] THEN
  REWRITE_TAC[VSUM_SING] THEN VECTOR_ARITH_TAC);;

let VSUM_SING_NUMSEG = prove
 (`vsum(n..n) f = f n`,
  REWRITE_TAC[NUMSEG_SING; VSUM_SING]);;

let VSUM_1 = prove
 (`vsum(1..1) f = f(1)`,
  REWRITE_TAC[VSUM_SING_NUMSEG]);;

let VSUM_2 = prove
 (`!t. vsum(1..2) t = t(1) + t(2)`,
  REWRITE_TAC[num_CONV `2`; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

let VSUM_3 = prove
 (`!t. vsum(1..3) t = t(1) + t(2) + t(3)`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_4 = prove
 (`!t. vsum(1..4) t = t(1) + t(2) + t(3) + t(4)`,
  SIMP_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_PAIR = prove
 (`!f:num->real^N m n.
        vsum(2*m..2*n+1) f = vsum(m..n) (\i. f(2*i) + f(2*i+1))`,
  SIMP_TAC[CART_EQ; VSUM_COMPONENT; VECTOR_ADD_COMPONENT; SUM_PAIR]);;

let VSUM_PAIR_0 = prove
 (`!f:num->real^N n. vsum(0..2*n+1) f = vsum(0..n) (\i. f(2*i) + f(2*i+1))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->real^N`; `0`; `n:num`] VSUM_PAIR) THEN
  ASM_REWRITE_TAC[ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Add useful congruences to the simplifier.                                 *)
(* ------------------------------------------------------------------------- *)

let th = prove
 (`(!f g s.   (!x. x IN s ==> f(x) = g(x))
              ==> vsum s (\i. f(i)) = vsum s g) /\
   (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
              ==> vsum(a..b) (\i. f(i)) = vsum(a..b) g) /\
   (!f g p.   (!x. p x ==> f x = g x)
              ==> vsum {y | p y} (\i. f(i)) = vsum {y | p y} g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  ASM_SIMP_TAC[IN_ELIM_THM; IN_NUMSEG]) in
  extend_basic_congs (map SPEC_ALL (CONJUNCTS th));;

(* ------------------------------------------------------------------------- *)
(* A conversion for evaluation of `vsum(m..n) f` for numerals m and n.       *)
(* ------------------------------------------------------------------------- *)

let EXPAND_VSUM_CONV =
  let [pth_0; pth_1; pth_2] = (CONJUNCTS o prove)
   (`(n < m ==> vsum(m..n) (f:num->real^N) = vec 0) /\
     vsum(m..m) (f:num->real^N) = f m /\
     (m <= n ==> vsum (m..n) (f:num->real^N) = f m + vsum (m + 1..n) f)`,
    REWRITE_TAC[VSUM_CLAUSES_LEFT; VSUM_SING_NUMSEG; VSUM_TRIV_NUMSEG])
  and ns_tm = `..` and f_tm = `f:num->real^N`
  and m_tm = `m:num` and n_tm = `n:num`
  and n_ty = `:N` in
  let rec conv tm =
    let smn,ftm = dest_comb tm in
    let s,mn = dest_comb smn in
    if not(is_const s & fst(dest_const s) = "vsum")
    then failwith "EXPAND_VSUM_CONV" else
    let mtm,ntm = dest_binop ns_tm mn in
    let m = dest_numeral mtm and n = dest_numeral ntm in
    let nty = hd(tl(snd(dest_type(snd(dest_fun_ty(type_of ftm)))))) in
    let ilist = [nty,n_ty] in
    let ifn = inst ilist and tfn = INST_TYPE ilist in
    if n < m then
      let th1 = INST [ftm,ifn f_tm; mtm,m_tm; ntm,n_tm] (tfn pth_0) in
      MP th1 (EQT_ELIM(NUM_LT_CONV(lhand(concl th1))))
    else if n = m then CONV_RULE (RAND_CONV(TRY_CONV BETA_CONV))
                                 (INST [ftm,ifn f_tm; mtm,m_tm] (tfn pth_1))
    else
      let th1 = INST [ftm,ifn f_tm; mtm,m_tm; ntm,n_tm] (tfn pth_2) in
      let th2 = MP th1 (EQT_ELIM(NUM_LE_CONV(lhand(concl th1)))) in
      CONV_RULE (RAND_CONV(COMB2_CONV (RAND_CONV(TRY_CONV BETA_CONV))
       (LAND_CONV(LAND_CONV NUM_ADD_CONV) THENC conv))) th2 in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Basis vectors in coordinate directions.                                   *)
(* ------------------------------------------------------------------------- *)

let basis = new_definition
  `basis k = lambda i. if i = k then &1 else &0`;;

let NORM_BASIS = prove
 (`!k. 1 <= k /\ k <= dimindex(:N)
       ==> (norm(basis k :real^N) = &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[basis; dot; vector_norm] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum (1..dimindex(:N)) (\i. if i = k then &1 else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    ASM_SIMP_TAC[LAMBDA_BETA; IN_NUMSEG; EQ_SYM_EQ] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG]]);;

let NORM_BASIS_1 = prove
 (`norm(basis 1) = &1`,
  SIMP_TAC[NORM_BASIS; ARITH_EQ; ARITH_RULE `1 <= k <=> ~(k = 0)`;
           DIMINDEX_NONZERO]);;

let VECTOR_CHOOSE_SIZE = prove
 (`!c. &0 <= c ==> ?x:real^N. norm(x) = c`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `c % basis 1 :real^N` THEN
  ASM_REWRITE_TAC[NORM_MUL; real_abs; NORM_BASIS_1; REAL_MUL_RID]);;

let VECTOR_CHOOSE_DIST = prove
 (`!x e. &0 <= e ==> ?y:real^N. dist(x,y) = e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?c:real^N. norm(c) = e` CHOOSE_TAC THENL
   [ASM_SIMP_TAC[VECTOR_CHOOSE_SIZE]; ALL_TAC] THEN
  EXISTS_TAC `x - c:real^N` THEN REWRITE_TAC[dist] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `x - (x - c) = c:real^N`]);;

let BASIS_INJ = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N) /\
         (basis i :real^N = basis j)
         ==> (i = j)`,
  SIMP_TAC[basis; CART_EQ; LAMBDA_BETA] THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; ARITH_EQ]);;

let BASIS_INJ_EQ = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
         ==> (basis i:real^N = basis j <=> i = j)`,
  MESON_TAC[BASIS_INJ]);;

let BASIS_NE = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N) /\
         ~(i = j)
         ==> ~(basis i :real^N = basis j)`,
  MESON_TAC[BASIS_INJ]);;

let BASIS_COMPONENT = prove
 (`!k i. 1 <= i /\ i <= dimindex(:N)
         ==> ((basis k :real^N)$i = if i = k then &1 else &0)`,
  SIMP_TAC[basis; LAMBDA_BETA] THEN MESON_TAC[]);;

let BASIS_EXPANSION = prove
 (`!x:real^N. vsum(1..dimindex(:N)) (\i. x$i % basis i) = x`,
  SIMP_TAC[CART_EQ; VSUM_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG; REAL_MUL_RID]);;

let BASIS_EXPANSION_UNIQUE = prove
 (`!f x:real^N. (vsum(1..dimindex(:N)) (\i. f(i) % basis i) = x) <=>
                (!i. 1 <= i /\ i <= dimindex(:N) ==> f(i) = x$i)`,
  SIMP_TAC[CART_EQ; VSUM_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[COND_RAND; REAL_MUL_RZERO; REAL_MUL_RID] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o RAND_CONV o LAND_CONV o
                   ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  SIMP_TAC[SUM_DELTA; IN_NUMSEG]);;

let DOT_BASIS = prove
 (`!x:real^N i.
        1 <= i /\ i <= dimindex(:N)
        ==> ((basis i) dot x = x$i) /\ (x dot (basis i) = x$i)`,
  SIMP_TAC[dot; basis; LAMBDA_BETA] THEN
  REWRITE_TAC[COND_RATOR; COND_RAND] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  SIMP_TAC[SUM_DELTA; IN_NUMSEG; REAL_MUL_LID; REAL_MUL_RID]);;

let DOT_BASIS_BASIS = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N)
         ==> (basis i:real^N) dot (basis j) = if i = j then &1 else &0`,
  SIMP_TAC[DOT_BASIS; BASIS_COMPONENT]);;

let DOT_BASIS_BASIS_UNEQUAL = prove
 (`!i j. ~(i = j) ==> (basis i) dot (basis j) = &0`,
  SIMP_TAC[basis; dot; LAMBDA_BETA] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[SUM_0; REAL_MUL_RZERO; REAL_MUL_LZERO; COND_ID]);;

let BASIS_EQ_0 = prove
 (`!i. (basis i :real^N = vec 0) <=> ~(i IN 1..dimindex(:N))`,
  SIMP_TAC[CART_EQ; BASIS_COMPONENT; VEC_COMPONENT; IN_NUMSEG] THEN
  MESON_TAC[REAL_ARITH `~(&1 = &0)`]);;

let BASIS_NONZERO = prove
 (`!k. 1 <= k /\ k <= dimindex(:N)
       ==> ~(basis k :real^N = vec 0)`,
  REWRITE_TAC[BASIS_EQ_0; IN_NUMSEG]);;

let VECTOR_EQ_LDOT = prove
 (`!y z. (!x. x dot y = x dot z) <=> y = z`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[CART_EQ] THEN MESON_TAC[DOT_BASIS]);;

let VECTOR_EQ_RDOT = prove
 (`!x y. (!z. x dot z = y dot z) <=> x = y`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[CART_EQ] THEN MESON_TAC[DOT_BASIS]);;

