open Hol_core
include Vector1

(* ------------------------------------------------------------------------- *)
(* Orthogonality.                                                            *)
(* ------------------------------------------------------------------------- *)

let orthogonal = new_definition
  `orthogonal x y <=> (x dot y = &0)`;;

let ORTHOGONAL_0 = prove
 (`!x. orthogonal (vec 0) x /\ orthogonal x (vec 0)`,
  REWRITE_TAC[orthogonal; DOT_LZERO; DOT_RZERO]);;

let ORTHOGONAL_REFL = prove
 (`!x. orthogonal x x <=> x = vec 0`,
  REWRITE_TAC[orthogonal; DOT_EQ_0]);;

let ORTHOGONAL_SYM = prove
 (`!x y. orthogonal x y <=> orthogonal y x`,
  REWRITE_TAC[orthogonal; DOT_SYM]);;

let ORTHOGONAL_LNEG = prove
 (`!x y. orthogonal (--x) y <=> orthogonal x y`,
  REWRITE_TAC[orthogonal; DOT_LNEG; REAL_NEG_EQ_0]);;

let ORTHOGONAL_RNEG = prove
 (`!x y. orthogonal x (--y) <=> orthogonal x y`,
  REWRITE_TAC[orthogonal; DOT_RNEG; REAL_NEG_EQ_0]);;

let ORTHOGONAL_MUL = prove
 (`(!a x y:real^N. orthogonal (a % x) y <=> a = &0 \/ orthogonal x y) /\
   (!a x y:real^N. orthogonal x (a % y) <=> a = &0 \/ orthogonal x y)`,
  REWRITE_TAC[orthogonal; DOT_LMUL; DOT_RMUL; REAL_ENTIRE]);;

let ORTHOGONAL_BASIS = prove
 (`!x:real^N i. 1 <= i /\ i <= dimindex(:N)
                ==> (orthogonal (basis i) x <=> (x$i = &0))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[orthogonal; dot; basis; LAMBDA_BETA] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG; REAL_MUL_LID]);;

let ORTHOGONAL_BASIS_BASIS = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N)
         ==> (orthogonal (basis i :real^N) (basis j) <=> ~(i = j))`,
  ASM_SIMP_TAC[ORTHOGONAL_BASIS] THEN ASM_SIMP_TAC[BASIS_COMPONENT] THEN
  MESON_TAC[REAL_ARITH `~(&1 = &0)`]);;

let ORTHOGONAL_CLAUSES = prove
 (`(!a. orthogonal a (vec 0)) /\
   (!a x c. orthogonal a x ==> orthogonal a (c % x)) /\
   (!a x. orthogonal a x ==> orthogonal a (--x)) /\
   (!a x y. orthogonal a x /\ orthogonal a y ==> orthogonal a (x + y)) /\
   (!a x y. orthogonal a x /\ orthogonal a y ==> orthogonal a (x - y)) /\
   (!a. orthogonal (vec 0) a) /\
   (!a x c. orthogonal x a ==> orthogonal (c % x) a) /\
   (!a x. orthogonal x a ==> orthogonal (--x) a) /\
   (!a x y. orthogonal x a /\ orthogonal y a ==> orthogonal (x + y) a) /\
   (!a x y. orthogonal x a /\ orthogonal y a ==> orthogonal (x - y) a)`,
  REWRITE_TAC[orthogonal; DOT_RNEG; DOT_RMUL; DOT_RADD; DOT_RSUB;
    DOT_LZERO; DOT_RZERO; DOT_LNEG; DOT_LMUL; DOT_LADD; DOT_LSUB] THEN
  SIMP_TAC[] THEN REAL_ARITH_TAC);;

let ORTHOGONAL_RVSUM = prove
 (`!f:A->real^N s x.
        FINITE s /\
        (!y. y IN s ==> orthogonal x (f y))
        ==> orthogonal x (vsum s f)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT; ORTHOGONAL_CLAUSES; VSUM_CLAUSES]);;

let ORTHOGONAL_LVSUM = prove
 (`!f:A->real^N s y.
        FINITE s /\
        (!x. x IN s ==> orthogonal (f x) y)
        ==> orthogonal (vsum s f) y`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT; ORTHOGONAL_CLAUSES; VSUM_CLAUSES]);;

let NORM_ADD_PYTHAGOREAN = prove
 (`!a b:real^N.
        orthogonal a b
        ==> norm(a + b) pow 2 = norm(a) pow 2 + norm(b) pow 2`,
  SIMP_TAC[NORM_POW_2; orthogonal; DOT_LADD; DOT_RADD; DOT_SYM] THEN
  REAL_ARITH_TAC);;

let NORM_VSUM_PYTHAGOREAN = prove
 (`!k u:A->real^N.
        FINITE k /\ pairwise (\i j. orthogonal (u i) (u j)) k
        ==> norm(vsum k u) pow 2 = sum k (\i. norm(u i) pow 2)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN SIMP_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; SUM_CLAUSES; NORM_0] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[PAIRWISE_INSERT] THEN
  REWRITE_TAC[pairwise] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NORM_ADD_PYTHAGOREAN THEN MATCH_MP_TAC ORTHOGONAL_RVSUM THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Explicit vector construction from lists.                                  *)
(* ------------------------------------------------------------------------- *)

let VECTOR_1 = prove
 (`(vector[x]:A^1)$1 = x`,
  SIMP_TAC[vector; LAMBDA_BETA; DIMINDEX_1; ARITH; LENGTH; EL; HD; TL]);;

let VECTOR_2 = prove
 (`(vector[x;y]:A^2)$1 = x /\
   (vector[x;y]:A^2)$2 = y`,
  SIMP_TAC[vector; LAMBDA_BETA; DIMINDEX_2; ARITH; LENGTH; EL] THEN
  REWRITE_TAC[num_CONV `1`; HD; TL; EL]);;

let VECTOR_3 = prove
 (`(vector[x;y;z]:A^3)$1 = x /\
   (vector[x;y;z]:A^3)$2 = y /\
   (vector[x;y;z]:A^3)$3 = z`,
  SIMP_TAC[vector; LAMBDA_BETA; DIMINDEX_3; ARITH; LENGTH; EL] THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; HD; TL; EL]);;

let VECTOR_4 = prove
 (`(vector[w;x;y;z]:A^4)$1 = w /\
   (vector[w;x;y;z]:A^4)$2 = x /\
   (vector[w;x;y;z]:A^4)$3 = y /\
   (vector[w;x;y;z]:A^4)$4 = z`,
  SIMP_TAC[vector; LAMBDA_BETA; DIMINDEX_4; ARITH; LENGTH; EL] THEN
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; HD; TL; EL]);;

let FORALL_VECTOR_1 = prove
 (`(!v:A^1. P v) <=> !x. P(vector[x])`,
  EQ_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(v:A^1)$1`) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[CART_EQ; FORALL_1; VECTOR_1; DIMINDEX_1]);;

let FORALL_VECTOR_2 = prove
 (`(!v:A^2. P v) <=> !x y. P(vector[x;y])`,
  EQ_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(v:A^2)$1`; `(v:A^2)$2`]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[CART_EQ; FORALL_2; VECTOR_2; DIMINDEX_2]);;

let FORALL_VECTOR_3 = prove
 (`(!v:A^3. P v) <=> !x y z. P(vector[x;y;z])`,
  EQ_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`(v:A^3)$1`; `(v:A^3)$2`; `(v:A^3)$3`]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[CART_EQ; FORALL_3; VECTOR_3; DIMINDEX_3]);;

let FORALL_VECTOR_4 = prove
 (`(!v:A^4. P v) <=> !w x y z. P(vector[w;x;y;z])`,
  EQ_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`(v:A^4)$1`; `(v:A^4)$2`; `(v:A^4)$3`; `(v:A^4)$4`]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[CART_EQ; FORALL_4; VECTOR_4; DIMINDEX_4]);;

let EXISTS_VECTOR_1 = prove
 (`(?v:A^1. P v) <=> ?x. P(vector[x])`,
  REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_VECTOR_1]);;

let EXISTS_VECTOR_2 = prove
 (`(?v:A^2. P v) <=> ?x y. P(vector[x;y])`,
  REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_VECTOR_2]);;

let EXISTS_VECTOR_3 = prove
 (`(?v:A^3. P v) <=> ?x y z. P(vector[x;y;z])`,
  REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_VECTOR_3]);;

let EXISTS_VECTOR_4 = prove
 (`(?v:A^4. P v) <=> ?w x y z. P(vector[w;x;y;z])`,
  REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_VECTOR_4]);;

let VECTOR_EXPAND_1 = prove
 (`!x:real^1. x = vector[x$1]`,
  SIMP_TAC[CART_EQ; DIMINDEX_1; FORALL_1; VECTOR_1]);;

let VECTOR_EXPAND_2 = prove
 (`!x:real^2. x = vector[x$1;x$2]`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

let VECTOR_EXPAND_3 = prove
 (`!x:real^3. x = vector[x$1;x$2;x$3]`,
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3]);;

let VECTOR_EXPAND_4 = prove
 (`!x:real^4. x = vector[x$1;x$2;x$3;x$4]`,
  SIMP_TAC[CART_EQ; DIMINDEX_4; FORALL_4; VECTOR_4]);;

(* ------------------------------------------------------------------------- *)
(* Linear functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let linear = new_definition
  `linear (f:real^M->real^N) <=>
        (!x y. f(x + y) = f(x) + f(y)) /\
        (!c x. f(c % x) = c % f(x))`;;

let LINEAR_COMPOSE_CMUL = prove
 (`!f c. linear f ==> linear (\x. c % f(x))`,
  SIMP_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let LINEAR_COMPOSE_NEG = prove
 (`!f. linear f ==> linear (\x. --(f(x)))`,
  SIMP_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let LINEAR_COMPOSE_ADD = prove
 (`!f g. linear f /\ linear g ==> linear (\x. f(x) + g(x))`,
  SIMP_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let LINEAR_COMPOSE_SUB = prove
 (`!f g. linear f /\ linear g ==> linear (\x. f(x) - g(x))`,
  SIMP_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let LINEAR_COMPOSE = prove
 (`!f g. linear f /\ linear g ==> linear (g o f)`,
  SIMP_TAC[linear; o_THM]);;

let LINEAR_ID = prove
 (`linear (\x. x)`,
  REWRITE_TAC[linear]);;

let LINEAR_I = prove
 (`linear I`,
  REWRITE_TAC[I_DEF; LINEAR_ID]);;

let LINEAR_ZERO = prove
 (`linear (\x. vec 0)`,
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let LINEAR_NEGATION = prove
 (`linear(--)`,
  REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC);;

let LINEAR_COMPOSE_VSUM = prove
 (`!f s. FINITE s /\ (!a. a IN s ==> linear(f a))
         ==> linear(\x. vsum s (\a. f a x))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; LINEAR_ZERO] THEN
  ASM_SIMP_TAC[ETA_AX; IN_INSERT; LINEAR_COMPOSE_ADD]);;

let LINEAR_VMUL_COMPONENT = prove
 (`!f:real^M->real^N v k.
     linear f /\ 1 <= k /\ k <= dimindex(:N)
     ==> linear (\x. f(x)$k % v)`,
  SIMP_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let LINEAR_0 = prove
 (`!f. linear f ==> (f(vec 0) = vec 0)`,
  MESON_TAC[VECTOR_MUL_LZERO; linear]);;

let LINEAR_CMUL = prove
 (`!f c x. linear f ==> (f(c % x) = c % f(x))`,
  SIMP_TAC[linear]);;

let LINEAR_NEG = prove
 (`!f x. linear f ==> (f(--x) = --(f x))`,
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN SIMP_TAC[LINEAR_CMUL]);;

let LINEAR_ADD = prove
 (`!f x y. linear f ==> (f(x + y) = f(x) + f(y))`,
  SIMP_TAC[linear]);;

let LINEAR_SUB = prove
 (`!f x y. linear f ==> (f(x - y) = f(x) - f(y))`,
  SIMP_TAC[VECTOR_SUB; LINEAR_ADD; LINEAR_NEG]);;

let LINEAR_VSUM = prove
 (`!f g s. linear f /\ FINITE s ==> (f(vsum s g) = vsum s (f o g))`,
  GEN_TAC THEN GEN_TAC THEN SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES] THEN FIRST_ASSUM(fun th ->
    SIMP_TAC[MATCH_MP LINEAR_0 th; MATCH_MP LINEAR_ADD th; o_THM]));;

let LINEAR_VSUM_MUL = prove
 (`!f s c v.
        linear f /\ FINITE s
        ==> f(vsum s (\i. c i % v i)) = vsum s (\i. c(i) % f(v i))`,
  SIMP_TAC[LINEAR_VSUM; o_DEF; LINEAR_CMUL]);;

let LINEAR_INJECTIVE_0 = prove
 (`!f. linear f
       ==> ((!x y. (f(x) = f(y)) ==> (x = y)) <=>
            (!x. (f(x) = vec 0) ==> (x = vec 0)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM VECTOR_SUB_EQ] THEN
  ASM_SIMP_TAC[GSYM LINEAR_SUB] THEN MESON_TAC[VECTOR_SUB_RZERO]);;

let LINEAR_BOUNDED = prove
 (`!f:real^M->real^N. linear f ==> ?B. !x. norm(f x) <= B * norm(x)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC
   `sum(1..dimindex(:M)) (\i. norm((f:real^M->real^N)(basis i)))` THEN
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; IN_NUMSEG] THEN
  ASM_SIMP_TAC[o_DEF; NORM_MUL; LINEAR_CMUL] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL; NORM_POS_LE; COMPONENT_LE_NORM]);;

let LINEAR_BOUNDED_POS = prove
 (`!f:real^M->real^N. linear f ==> ?B. &0 < B /\ !x. norm(f x) <= B * norm(x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B:real` o MATCH_MP LINEAR_BOUNDED) THEN
  EXISTS_TAC `abs(B) + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  REAL_ARITH_TAC);;

let SYMMETRIC_LINEAR_IMAGE = prove
 (`!f s. (!x. x IN s ==> --x IN s) /\ linear f
          ==> !x. x IN (IMAGE f s) ==> --x IN (IMAGE f s)`,
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  SIMP_TAC[GSYM LINEAR_NEG] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Bilinear functions.                                                       *)
(* ------------------------------------------------------------------------- *)

let bilinear = new_definition
  `bilinear f <=> (!x. linear(\y. f x y)) /\ (!y. linear(\x. f x y))`;;

let BILINEAR_LADD = prove
 (`!h x y z. bilinear h ==> h (x + y) z = (h x z) + (h y z)`,
  SIMP_TAC[bilinear; linear]);;

let BILINEAR_RADD = prove
 (`!h x y z. bilinear h ==> h x (y + z) = (h x y) + (h x z)`,
  SIMP_TAC[bilinear; linear]);;

let BILINEAR_LMUL = prove
 (`!h c x y. bilinear h ==> h (c % x) y = c % (h x y)`,
  SIMP_TAC[bilinear; linear]);;

let BILINEAR_RMUL = prove
 (`!h c x y. bilinear h ==> h x (c % y) = c % (h x y)`,
  SIMP_TAC[bilinear; linear]);;

let BILINEAR_LNEG = prove
 (`!h x y. bilinear h ==> h (--x) y = --(h x y)`,
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN SIMP_TAC[BILINEAR_LMUL]);;

let BILINEAR_RNEG = prove
 (`!h x y. bilinear h ==> h x (--y) = --(h x y)`,
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN SIMP_TAC[BILINEAR_RMUL]);;

let BILINEAR_LZERO = prove
 (`!h x. bilinear h ==> h (vec 0) x = vec 0`,
  ONCE_REWRITE_TAC[VECTOR_ARITH `x = vec 0 <=> x + x = x`] THEN
  SIMP_TAC[GSYM BILINEAR_LADD; VECTOR_ADD_LID]);;

let BILINEAR_RZERO = prove
 (`!h x. bilinear h ==> h x (vec 0) = vec 0`,
  ONCE_REWRITE_TAC[VECTOR_ARITH `x = vec 0 <=> x + x = x`] THEN
  SIMP_TAC[GSYM BILINEAR_RADD; VECTOR_ADD_LID]);;

let BILINEAR_LSUB = prove
 (`!h x y z. bilinear h ==> h (x - y) z = (h x z) - (h y z)`,
  SIMP_TAC[VECTOR_SUB; BILINEAR_LNEG; BILINEAR_LADD]);;

let BILINEAR_RSUB = prove
 (`!h x y z. bilinear h ==> h x (y - z) = (h x y) - (h x z)`,
  SIMP_TAC[VECTOR_SUB; BILINEAR_RNEG; BILINEAR_RADD]);;

let BILINEAR_VSUM = prove
 (`!h:real^M->real^N->real^P.
       bilinear h /\ FINITE s /\ FINITE t
       ==> h (vsum s f) (vsum t g) = vsum (s CROSS t) (\(i,j). h (f i) (g j))`,
  REPEAT GEN_TAC THEN SIMP_TAC[bilinear; ETA_AX] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> (a /\ d) /\ (b /\ c)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[LEFT_AND_FORALL_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_ALL o MATCH_MP LINEAR_VSUM o SPEC_ALL) THEN
  SIMP_TAC[] THEN ASM_SIMP_TAC[LINEAR_VSUM; o_DEF; VSUM_VSUM_PRODUCT] THEN
  REWRITE_TAC[GSYM CROSS]);;

let BILINEAR_BOUNDED = prove
 (`!h:real^M->real^N->real^P.
        bilinear h ==> ?B. !x y. norm(h x y) <= B * norm(x) * norm(y)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `sum ((1..dimindex(:M)) CROSS (1..dimindex(:N)))
                  (\(i,j). norm((h:real^M->real^N->real^P)
                                (basis i) (basis j)))` THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC
   (LAND_CONV o RAND_CONV o BINOP_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[BILINEAR_VSUM; FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BILINEAR_LMUL; NORM_MUL] THEN
  ASM_SIMP_TAC[BILINEAR_RMUL; NORM_MUL; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM; REAL_ABS_POS; REAL_LE_MUL2]);;

let BILINEAR_BOUNDED_POS = prove
 (`!h. bilinear h
       ==> ?B. &0 < B /\ !x y. norm(h x y) <= B * norm(x) * norm(y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B:real` o MATCH_MP BILINEAR_BOUNDED) THEN
  EXISTS_TAC `abs(B) + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_RMUL THEN
         SIMP_TAC[NORM_POS_LE; REAL_LE_MUL]) THEN
  REAL_ARITH_TAC);;

let BILINEAR_VSUM_PARTIAL_SUC = prove
 (`!f g h:real^M->real^N->real^P m n.
        bilinear h
        ==> vsum (m..n) (\k. h (f k) (g(k + 1) - g(k))) =
                if m <= n then h (f(n + 1)) (g(n + 1)) - h (f m) (g m) -
                               vsum (m..n) (\k. h (f(k + 1) - f(k)) (g(k + 1)))
                else vec 0`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN INDUCT_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[VSUM_TRIV_NUMSEG; GSYM NOT_LE] THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG] THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[ARITH] THENL
     [ASM_SIMP_TAC[BILINEAR_RSUB; BILINEAR_LSUB] THEN VECTOR_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE]) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[GSYM NOT_LT; VSUM_TRIV_NUMSEG; ARITH_RULE `n < SUC n`] THEN
  ASM_SIMP_TAC[GSYM ADD1; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[BILINEAR_RSUB; BILINEAR_LSUB] THEN VECTOR_ARITH_TAC);;

let BILINEAR_VSUM_PARTIAL_PRE = prove
 (`!f g h:real^M->real^N->real^P m n.
        bilinear h
        ==> vsum (m..n) (\k. h (f k) (g(k) - g(k - 1))) =
                if m <= n then h (f(n + 1)) (g(n)) - h (f m) (g(m - 1)) -
                               vsum (m..n) (\k. h (f(k + 1) - f(k)) (g(k)))
                else vec 0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPECL [`f:num->real^M`; `\k. (g:num->real^N)(k - 1)`;
                 `m:num`; `n:num`] o MATCH_MP BILINEAR_VSUM_PARTIAL_SUC) THEN
   REWRITE_TAC[ADD_SUB] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Adjoints.                                                                 *)
(* ------------------------------------------------------------------------- *)

let adjoint = new_definition
 `adjoint(f:real^M->real^N) = @f'. !x y. f(x) dot y = x dot f'(y)`;;

let ADJOINT_WORKS = prove
 (`!f:real^M->real^N. linear f ==> !x y. f(x) dot y = x dot (adjoint f)(y)`,
  GEN_TAC THEN DISCH_TAC THEN SIMP_TAC[adjoint] THEN CONV_TAC SELECT_CONV THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN ONCE_REWRITE_TAC[GSYM SKOLEM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  EXISTS_TAC `(lambda i. (f:real^M->real^N) (basis i) dot y):real^M` THEN
  X_GEN_TAC `x:real^M` THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG] THEN
  SIMP_TAC[dot; LAMBDA_BETA; VSUM_COMPONENT; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  ASM_SIMP_TAC[o_THM; VECTOR_MUL_COMPONENT; LINEAR_CMUL; REAL_MUL_ASSOC]);;

let ADJOINT_LINEAR = prove
 (`!f:real^M->real^N. linear f ==> linear(adjoint f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[linear; GSYM VECTOR_EQ_LDOT] THEN
  ASM_SIMP_TAC[DOT_RMUL; DOT_RADD; GSYM ADJOINT_WORKS]);;

let ADJOINT_CLAUSES = prove
 (`!f:real^M->real^N.
     linear f ==> (!x y. x dot (adjoint f)(y) = f(x) dot y) /\
                  (!x y. (adjoint f)(y) dot x = y dot f(x))`,
  MESON_TAC[ADJOINT_WORKS; DOT_SYM]);;

let ADJOINT_ADJOINT = prove
 (`!f:real^M->real^N. linear f ==> adjoint(adjoint f) = f`,
  SIMP_TAC[FUN_EQ_THM; GSYM VECTOR_EQ_LDOT; ADJOINT_CLAUSES; ADJOINT_LINEAR]);;

let ADJOINT_UNIQUE = prove
 (`!f f'. linear f /\ (!x y. f'(x) dot y = x dot f(y))
          ==> f' = adjoint f`,
  SIMP_TAC[FUN_EQ_THM; GSYM VECTOR_EQ_RDOT; ADJOINT_CLAUSES]);;

let ADJOINT_COMPOSE = prove
 (`!f g:real^N->real^N.
        linear f /\ linear g ==> adjoint(f o g) = adjoint g o adjoint f`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC ADJOINT_UNIQUE THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE; o_THM; ADJOINT_CLAUSES]);;

let SELF_ADJOINT_COMPOSE = prove
 (`!f g:real^N->real^N.
        linear f /\ linear g /\ adjoint f = f /\ adjoint g = g
        ==> (adjoint(f o g) = f o g <=> f o g = g o f)`,
  SIMP_TAC[ADJOINT_COMPOSE] THEN MESON_TAC[]);;

let SELF_ADJOINT_ORTHOGONAL_EIGENVECTORS = prove
 (`!f:real^N->real^N v w a b.
        linear f /\ adjoint f = f /\ f v = a % v /\ f w = b % w /\ ~(a = b)
        ==> orthogonal v w`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPECL [`v:real^N`; `w:real^N`] o
        MATCH_MP ADJOINT_WORKS) THEN
  ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL; orthogonal; REAL_EQ_MUL_RCANCEL]);;

(* ------------------------------------------------------------------------- *)
(* Matrix notation. NB: an MxN matrix is of type real^N^M, not real^M^N.     *)
(* We could define a special type if we're going to use them a lot.          *)
(* ------------------------------------------------------------------------- *)

overload_interface ("--",`(matrix_neg):real^N^M->real^N^M`);;
overload_interface ("+",`(matrix_add):real^N^M->real^N^M->real^N^M`);;
overload_interface ("-",`(matrix_sub):real^N^M->real^N^M->real^N^M`);;

make_overloadable "**" `:A->B->C`;;

overload_interface ("**",`(matrix_mul):real^N^M->real^P^N->real^P^M`);;
overload_interface ("**",`(matrix_vector_mul):real^N^M->real^N->real^M`);;
overload_interface ("**",`(vector_matrix_mul):real^M->real^N^M->real^N`);;

parse_as_infix("%%",(21,"right"));;

prioritize_real();;

let matrix_cmul = new_definition
  `((%%):real->real^N^M->real^N^M) c A = lambda i j. c * A$i$j`;;

let matrix_neg = new_definition
  `!A:real^N^M. --A = lambda i j. --(A$i$j)`;;

let matrix_add = new_definition
  `!A:real^N^M B:real^N^M. A + B = lambda i j. A$i$j + B$i$j`;;

let matrix_sub = new_definition
  `!A:real^N^M B:real^N^M. A - B = lambda i j. A$i$j - B$i$j`;;

let matrix_mul = new_definition
  `!A:real^N^M B:real^P^N.
        A ** B =
          lambda i j. sum(1..dimindex(:N)) (\k. A$i$k * B$k$j)`;;

let matrix_vector_mul = new_definition
  `!A:real^N^M x:real^N.
        A ** x = lambda i. sum(1..dimindex(:N)) (\j. A$i$j * x$j)`;;

let vector_matrix_mul = new_definition
  `!A:real^N^M x:real^M.
        x ** A = lambda j. sum(1..dimindex(:M)) (\i. A$i$j * x$i)`;;

let mat = new_definition
  `(mat:num->real^N^M) k = lambda i j. if i = j then &k else &0`;;

let transp = new_definition
  `(transp:real^N^M->real^M^N) A = lambda i j. A$j$i`;;

let row = new_definition
 `(row:num->real^N^M->real^N) i A = lambda j. A$i$j`;;

let column = new_definition
 `(column:num->real^N^M->real^M) j A = lambda i. A$i$j`;;

let rows = new_definition
 `rows(A:real^N^M) = { row i A | 1 <= i /\ i <= dimindex(:M)}`;;

let columns = new_definition
 `columns(A:real^N^M) = { column i A | 1 <= i /\ i <= dimindex(:N)}`;;

let MATRIX_CMUL_COMPONENT = prove
 (`!c A:real^N^M i. (c %% A)$i$j = c * A$i$j`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[matrix_cmul; CART_EQ; LAMBDA_BETA]);;

let MATRIX_ADD_COMPONENT = prove
 (`!A B:real^N^M i j. (A + B)$i$j = A$i$j + B$i$j`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[matrix_add; LAMBDA_BETA]);;

let MATRIX_SUB_COMPONENT = prove
 (`!A B:real^N^M i j. (A - B)$i$j = A$i$j - B$i$j`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[matrix_sub; LAMBDA_BETA]);;

let MATRIX_NEG_COMPONENT = prove
 (`!A:real^N^M i j. (--A)$i$j = --(A$i$j)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[matrix_neg; LAMBDA_BETA]);;

let TRANSP_COMPONENT = prove
 (`!A:real^N^M i j. (transp A)$i$j = A$j$i`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\
                    (!A:real^M^N. A$i = A$k) /\ (!z:real^N. z$i = z$k)`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:M) /\
                    (!A:real^N^M. A$j = A$l) /\ (!z:real^M. z$j = z$l)`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[transp; LAMBDA_BETA]);;

let MAT_COMPONENT = prove
 (`!n i j.
        1 <= i /\ i <= dimindex(:M) /\
        1 <= j /\ j <= dimindex(:N)
        ==> (mat n:real^N^M)$i$j = if i = j then &n else &0`,
  SIMP_TAC[mat; LAMBDA_BETA]);;

let MAT_0_COMPONENT = prove
 (`!i j. (mat 0:real^N^M)$i$j = &0`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[mat; COND_ID; LAMBDA_BETA]);;

let MATRIX_CMUL_ASSOC = prove
 (`!a b X:real^M^N. a %% (b %% X) = (a * b) %% X`,
  SIMP_TAC[CART_EQ; matrix_cmul; LAMBDA_BETA; REAL_MUL_ASSOC]);;

let MATRIX_CMUL_LID = prove
 (`!X:real^M^N. &1 %% X = X`,
  SIMP_TAC[CART_EQ; matrix_cmul; LAMBDA_BETA; REAL_MUL_LID]);;

let MATRIX_ADD_SYM = prove
 (`!A:real^N^M B. A + B = B + A`,
  SIMP_TAC[matrix_add; CART_EQ; LAMBDA_BETA; REAL_ADD_AC]);;

let MATRIX_ADD_ASSOC = prove
 (`!A:real^N^M B C. A + (B + C) = (A + B) + C`,
  SIMP_TAC[matrix_add; CART_EQ; LAMBDA_BETA; REAL_ADD_AC]);;

let MATRIX_ADD_LID = prove
 (`!A. mat 0 + A = A`,
  SIMP_TAC[matrix_add; mat; COND_ID; CART_EQ; LAMBDA_BETA; REAL_ADD_LID]);;

let MATRIX_ADD_RID = prove
 (`!A. A + mat 0 = A`,
  SIMP_TAC[matrix_add; mat; COND_ID; CART_EQ; LAMBDA_BETA; REAL_ADD_RID]);;

let MATRIX_ADD_LNEG = prove
 (`!A. --A + A = mat 0`,
  SIMP_TAC[matrix_neg; matrix_add; mat; COND_ID;
           CART_EQ; LAMBDA_BETA; REAL_ADD_LINV]);;

let MATRIX_ADD_RNEG = prove
 (`!A. A + --A = mat 0`,
  SIMP_TAC[matrix_neg; matrix_add; mat; COND_ID;
           CART_EQ; LAMBDA_BETA; REAL_ADD_RINV]);;

let MATRIX_SUB = prove
 (`!A:real^N^M B. A - B = A + --B`,
  SIMP_TAC[matrix_neg; matrix_add; matrix_sub; CART_EQ; LAMBDA_BETA;
           real_sub]);;

let MATRIX_SUB_REFL = prove
 (`!A. A - A = mat 0`,
  REWRITE_TAC[MATRIX_SUB; MATRIX_ADD_RNEG]);;

let MATRIX_ADD_LDISTRIB = prove
 (`!A:real^N^M B:real^P^N C. A ** (B + C) = A ** B + A ** C`,
  SIMP_TAC[matrix_mul; matrix_add; CART_EQ; LAMBDA_BETA;
           GSYM SUM_ADD_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  ASM_SIMP_TAC[LAMBDA_BETA; REAL_ADD_LDISTRIB]);;

let MATRIX_MUL_LID = prove
 (`!A:real^N^M. mat 1 ** A = A`,
  REWRITE_TAC[matrix_mul;
   GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ]
    (SPEC_ALL mat)] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REWRITE_TAC[COND_RATOR; COND_RAND] THEN
  SIMP_TAC[SUM_DELTA; REAL_MUL_LZERO; IN_NUMSEG; REAL_MUL_LID]);;

let MATRIX_MUL_RID = prove
 (`!A:real^N^M. A ** mat 1 = A`,
  REWRITE_TAC[matrix_mul; mat] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REWRITE_TAC[COND_RATOR; COND_RAND] THEN
  SIMP_TAC[SUM_DELTA; REAL_MUL_RZERO; IN_NUMSEG; REAL_MUL_RID]);;

let MATRIX_MUL_ASSOC = prove
 (`!A:real^N^M B:real^P^N C:real^Q^P. A ** B ** C = (A ** B) ** C`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[matrix_mul; CART_EQ; LAMBDA_BETA; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let MATRIX_MUL_LZERO = prove
 (`!A. (mat 0:real^N^M) ** (A:real^P^N) = mat 0`,
  SIMP_TAC[matrix_mul; mat; CART_EQ; LAMBDA_BETA; COND_ID; REAL_MUL_LZERO] THEN
  REWRITE_TAC[SUM_0]);;

let MATRIX_MUL_RZERO = prove
 (`!A. (A:real^N^M) ** (mat 0:real^P^N) = mat 0`,
  SIMP_TAC[matrix_mul; mat; CART_EQ; LAMBDA_BETA; COND_ID; REAL_MUL_RZERO] THEN
  REWRITE_TAC[SUM_0]);;

let MATRIX_ADD_RDISTRIB = prove
 (`!A:real^N^M B C:real^P^N. (A + B) ** C = A ** C + B ** C`,
  SIMP_TAC[matrix_mul; matrix_add; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG]);;

let MATRIX_SUB_LDISTRIB = prove
 (`!A:real^N^M B C:real^P^N. A ** (B - C) = A ** B - A ** C`,
  SIMP_TAC[matrix_mul; matrix_sub; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; SUM_SUB_NUMSEG]);;

let MATRIX_SUB_RDISTRIB = prove
 (`!A:real^N^M B C:real^P^N. (A - B) ** C = A ** C - B ** C`,
  SIMP_TAC[matrix_mul; matrix_sub; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG]);;

let MATRIX_MUL_LMUL = prove
 (`!A:real^N^M B:real^P^N c. (c %% A) ** B = c %% (A ** B)`,
  SIMP_TAC[matrix_mul; matrix_cmul; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL]);;

let MATRIX_MUL_RMUL = prove
 (`!A:real^N^M B:real^P^N c. A ** (c %% B) = c %% (A ** B)`,
  SIMP_TAC[matrix_mul; matrix_cmul; CART_EQ; LAMBDA_BETA] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `A * c * B:real = c * A * B`] THEN
  REWRITE_TAC[SUM_LMUL]);;

let MATRIX_CMUL_ADD_LDISTRIB = prove
 (`!A:real^N^M B c. c %% (A + B) = c %% A + c %% B`,
  SIMP_TAC[matrix_cmul; matrix_add; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB]);;

let MATRIX_CMUL_SUB_LDISTRIB = prove
 (`!A:real^N^M B c. c %% (A - B) = c %% A - c %% B`,
  SIMP_TAC[matrix_cmul; matrix_sub; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB]);;

let MATRIX_CMUL_ADD_RDISTRIB = prove
 (`!A:real^N^M b c. (b + c) %% A = b %% A + c %% A`,
  SIMP_TAC[matrix_cmul; matrix_add; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB]);;

let MATRIX_CMUL_SUB_RDISTRIB = prove
 (`!A:real^N^M b c. (b - c) %% A = b %% A - c %% A`,
  SIMP_TAC[matrix_cmul; matrix_sub; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB]);;

let MATRIX_CMUL_RZERO = prove
 (`!c. c %% mat 0 = mat 0`,
  SIMP_TAC[matrix_cmul; mat; CART_EQ; LAMBDA_BETA; COND_ID; REAL_MUL_RZERO]);;

let MATRIX_CMUL_LZERO = prove
 (`!A. &0 %% A = mat 0`,
  SIMP_TAC[matrix_cmul; mat; CART_EQ; LAMBDA_BETA; COND_ID; REAL_MUL_LZERO]);;

let MATRIX_NEG_MINUS1 = prove
 (`!A:real^N^M. --A = --(&1) %% A`,
  REWRITE_TAC[matrix_cmul; matrix_neg; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM REAL_NEG_MINUS1]);;

let MATRIX_ADD_AC = prove
 (`(A:real^N^M) + B = B + A /\
   (A + B) + C = A + (B + C) /\
   A + (B + C) = B + (A + C)`,
  MESON_TAC[MATRIX_ADD_ASSOC; MATRIX_ADD_SYM]);;

let MATRIX_NEG_ADD = prove
 (`!A B:real^N^M. --(A + B) = --A + --B`,
  SIMP_TAC[matrix_neg; matrix_add; CART_EQ; LAMBDA_BETA; REAL_NEG_ADD]);;

let MATRIX_NEG_SUB = prove
 (`!A B:real^N^M. --(A - B) = B - A`,
  SIMP_TAC[matrix_neg; matrix_sub; CART_EQ; LAMBDA_BETA; REAL_NEG_SUB]);;

let MATRIX_NEG_0 = prove
 (`--(mat 0) = mat 0`,
  SIMP_TAC[CART_EQ; mat; matrix_neg; LAMBDA_BETA; REAL_NEG_0; COND_ID]);;

let MATRIX_SUB_RZERO = prove
 (`!A:real^N^M. A - mat 0 = A`,
  SIMP_TAC[CART_EQ; mat; matrix_sub; LAMBDA_BETA; REAL_SUB_RZERO; COND_ID]);;

let MATRIX_SUB_LZERO = prove
 (`!A:real^N^M. mat 0 - A = --A`,
  SIMP_TAC[CART_EQ; mat; matrix_sub; matrix_neg;
           LAMBDA_BETA; REAL_SUB_LZERO; COND_ID]);;

let MATRIX_NEG_EQ_0 = prove
 (`!A:real^N^M. --A = mat 0 <=> A = mat 0`,
  SIMP_TAC[CART_EQ; matrix_neg; mat; LAMBDA_BETA; REAL_NEG_EQ_0; COND_ID]);;

let MATRIX_VECTOR_MUL_ASSOC = prove
 (`!A:real^N^M B:real^P^N x:real^P. A ** B ** x = (A ** B) ** x`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[matrix_mul; matrix_vector_mul;
           CART_EQ; LAMBDA_BETA; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let MATRIX_VECTOR_MUL_LID = prove
 (`!x:real^N. mat 1 ** x = x`,
  REWRITE_TAC[matrix_vector_mul;
   GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ]
    (SPEC_ALL mat)] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REWRITE_TAC[COND_RATOR; COND_RAND] THEN
  SIMP_TAC[SUM_DELTA; REAL_MUL_LZERO; IN_NUMSEG; REAL_MUL_LID]);;

let MATRIX_VECTOR_MUL_LZERO = prove
 (`!x:real^N. mat 0 ** x = vec 0`,
  SIMP_TAC[mat; matrix_vector_mul; CART_EQ; VEC_COMPONENT; LAMBDA_BETA;
           COND_ID; REAL_MUL_LZERO; SUM_0]);;

let MATRIX_VECTOR_MUL_RZERO = prove
 (`!A:real^M^N. A ** vec 0 = vec 0`,
  SIMP_TAC[mat; matrix_vector_mul; CART_EQ; VEC_COMPONENT; LAMBDA_BETA;
           COND_ID; REAL_MUL_RZERO; SUM_0]);;

let MATRIX_VECTOR_MUL_ADD_LDISTRIB = prove
 (`!A:real^M^N x:real^M y. A ** (x + y) = A ** x + A ** y`,
  SIMP_TAC[CART_EQ; matrix_vector_mul; VECTOR_ADD_COMPONENT; LAMBDA_BETA;
           SUM_ADD_NUMSEG; REAL_ADD_LDISTRIB]);;

let MATRIX_VECTOR_MUL_SUB_LDISTRIB = prove
 (`!A:real^M^N x:real^M y. A ** (x - y) = A ** x - A ** y`,
  SIMP_TAC[CART_EQ; matrix_vector_mul; VECTOR_SUB_COMPONENT; LAMBDA_BETA;
           SUM_SUB_NUMSEG; REAL_SUB_LDISTRIB]);;

let MATRIX_VECTOR_MUL_ADD_RDISTRIB = prove
 (`!A:real^M^N B x. (A + B) ** x = (A ** x) + (B ** x)`,
  SIMP_TAC[CART_EQ; matrix_vector_mul; matrix_add; LAMBDA_BETA;
           VECTOR_ADD_COMPONENT; REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG]);;

let MATRIX_VECTOR_MUL_SUB_RDISTRIB = prove
 (`!A:real^M^N B x. (A - B) ** x = (A ** x) - (B ** x)`,
  SIMP_TAC[CART_EQ; matrix_vector_mul; matrix_sub; LAMBDA_BETA;
           VECTOR_SUB_COMPONENT; REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG]);;

let MATRIX_VECTOR_MUL_RMUL = prove
 (`!A:real^M^N x:real^M c. A ** (c % x) = c % (A ** x)`,
  SIMP_TAC[CART_EQ; VECTOR_MUL_COMPONENT; matrix_vector_mul; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN REWRITE_TAC[REAL_MUL_AC]);;

let MATRIX_MUL_LNEG = prove
 (`!A:real^N^M B:real^P^N. (--A) ** B = --(A ** B)`,
  REWRITE_TAC[MATRIX_NEG_MINUS1; MATRIX_MUL_LMUL]);;

let MATRIX_MUL_RNEG = prove
 (`!A:real^N^M B:real^P^N. A ** --B = --(A ** B)`,
  REWRITE_TAC[MATRIX_NEG_MINUS1; MATRIX_MUL_RMUL]);;

let MATRIX_NEG_NEG = prove
 (`!A:real^N^N. --(--A) = A`,
  SIMP_TAC[CART_EQ; MATRIX_NEG_COMPONENT; REAL_NEG_NEG]);;

let MATRIX_TRANSP_MUL = prove
 (`!A B. transp(A ** B) = transp(B) ** transp(A)`,
  SIMP_TAC[matrix_mul; transp; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let SYMMETRIC_MATRIX_MUL = prove
 (`!A B:real^N^N.
        transp(A) = A /\ transp(B) = B
        ==> (transp(A ** B) = A ** B <=> A ** B = B ** A)`,
  SIMP_TAC[MATRIX_TRANSP_MUL] THEN MESON_TAC[]);;

let MATRIX_EQ = prove
 (`!A:real^N^M B. (A = B) = !x:real^N. A ** x = B ** x`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN `i:num` o SPEC `(basis i):real^N`) THEN
  SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA; basis] THEN
  SIMP_TAC[SUM_DELTA; COND_RAND; REAL_MUL_RZERO] THEN
  REWRITE_TAC[TAUT `(if p then b else T) <=> p ==> b`] THEN
  SIMP_TAC[REAL_MUL_RID; IN_NUMSEG]);;

let MATRIX_VECTOR_MUL_COMPONENT = prove
 (`!A:real^N^M x k.
    1 <= k /\ k <= dimindex(:M) ==> ((A ** x)$k = (A$k) dot x)`,
  SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; dot]);;

let DOT_LMUL_MATRIX = prove
 (`!A:real^N^M x:real^M y:real^N. (x ** A) dot y = x dot (A ** y)`,
  SIMP_TAC[dot; matrix_vector_mul; vector_matrix_mul; dot; LAMBDA_BETA] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[REAL_MUL_AC]);;

let TRANSP_MATRIX_CMUL = prove
 (`!A:real^M^N c. transp(c %% A) = c %% transp A`,
  SIMP_TAC[CART_EQ; transp; MATRIX_CMUL_COMPONENT; LAMBDA_BETA]);;

let TRANSP_MATRIX_ADD = prove
 (`!A B:real^N^M. transp(A + B) = transp A + transp B`,
  SIMP_TAC[CART_EQ; transp; LAMBDA_BETA; matrix_add]);;

let TRANSP_MATRIX_SUB = prove
 (`!A B:real^N^M. transp(A - B) = transp A - transp B`,
  SIMP_TAC[CART_EQ; transp; LAMBDA_BETA; matrix_sub]);;

let TRANSP_MATRIX_NEG = prove
 (`!A:real^N^M. transp(--A) = --(transp A)`,
  SIMP_TAC[CART_EQ; transp; LAMBDA_BETA; matrix_neg]);;

let TRANSP_MAT = prove
 (`!n. transp(mat n) = mat n`,
  SIMP_TAC[transp; mat; LAMBDA_BETA; CART_EQ; EQ_SYM_EQ]);;

let TRANSP_TRANSP = prove
 (`!A:real^N^M. transp(transp A) = A`,
  SIMP_TAC[CART_EQ; transp; LAMBDA_BETA]);;

let SYMMETRIX_MATRIX_CONJUGATE = prove
 (`!A B:real^N^N. transp B = B
                  ==> transp(transp A ** B ** A) = transp A ** B ** A`,
  SIMP_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC]);;

let TRANSP_EQ = prove
 (`!A B:real^M^N. transp A = transp B <=> A = B`,
  MESON_TAC[TRANSP_TRANSP]);;

let ROW_TRANSP = prove
 (`!A:real^N^M i.
        1 <= i /\ i <= dimindex(:N) ==> row i (transp A) = column i A`,
  SIMP_TAC[row; column; transp; CART_EQ; LAMBDA_BETA]);;

let COLUMN_TRANSP = prove
 (`!A:real^N^M i.
        1 <= i /\ i <= dimindex(:M) ==> column i (transp A) = row i A`,
  SIMP_TAC[row; column; transp; CART_EQ; LAMBDA_BETA]);;

let ROWS_TRANSP = prove
 (`!A:real^N^M. rows(transp A) = columns A`,
  REWRITE_TAC[rows; columns; EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[ROW_TRANSP]);;

let COLUMNS_TRANSP = prove
 (`!A:real^N^M. columns(transp A) = rows A`,
  MESON_TAC[TRANSP_TRANSP; ROWS_TRANSP]);;

let VECTOR_MATRIX_MUL_TRANSP = prove
 (`!A:real^M^N x:real^N. x ** A = transp A ** x`,
  REWRITE_TAC[matrix_vector_mul; vector_matrix_mul; transp] THEN
  SIMP_TAC[LAMBDA_BETA; CART_EQ]);;

let MATRIX_VECTOR_MUL_TRANSP = prove
 (`!A:real^M^N x:real^M. A ** x = x ** transp A`,
  REWRITE_TAC[VECTOR_MATRIX_MUL_TRANSP; TRANSP_TRANSP]);;

let FINITE_ROWS = prove
 (`!A:real^N^M. FINITE(rows A)`,
  REWRITE_TAC[rows] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  SIMP_TAC[GSYM numseg; FINITE_IMAGE; FINITE_NUMSEG]);;

let FINITE_COLUMNS = prove
 (`!A:real^N^M. FINITE(columns A)`,
  REWRITE_TAC[columns] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  SIMP_TAC[GSYM numseg; FINITE_IMAGE; FINITE_NUMSEG]);;

let MATRIX_EQUAL_ROWS = prove
 (`!A B:real^N^M.
        A = B <=> !i. 1 <= i /\ i <= dimindex(:M) ==> row i A = row i B`,
  SIMP_TAC[row; CART_EQ; LAMBDA_BETA]);;

let MATRIX_EQUAL_COLUMNS = prove
 (`!A B:real^N^M.
        A = B <=> !i. 1 <= i /\ i <= dimindex(:N) ==> column i A = column i B`,
  SIMP_TAC[column; CART_EQ; LAMBDA_BETA] THEN MESON_TAC[]);;

let MATRIX_CMUL_EQ_0 = prove
 (`!A:real^M^N c. c %% A = mat 0 <=> c = &0 \/ A = mat 0`,
  SIMP_TAC[CART_EQ; MATRIX_CMUL_COMPONENT; MAT_COMPONENT; COND_ID] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = &0` THEN
  ASM_REWRITE_TAC[REAL_ENTIRE]);;

let MAT_EQ = prove
 (`!m n. mat m = mat n <=> m = n`,
  SIMP_TAC[CART_EQ; MAT_COMPONENT] THEN REPEAT STRIP_TAC THEN
  MESON_TAC[REAL_OF_NUM_EQ; DIMINDEX_GE_1; LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Two sometimes fruitful ways of looking at matrix-vector multiplication.   *)
(* ------------------------------------------------------------------------- *)

let MATRIX_MUL_DOT = prove
 (`!A:real^N^M x. A ** x = lambda i. A$i dot x`,
  REWRITE_TAC[matrix_vector_mul; dot] THEN SIMP_TAC[CART_EQ; LAMBDA_BETA]);;

let MATRIX_MUL_VSUM = prove
 (`!A:real^N^M x. A ** x = vsum(1..dimindex(:N)) (\i. x$i % column i A)`,
  SIMP_TAC[matrix_vector_mul; CART_EQ; VSUM_COMPONENT; LAMBDA_BETA;
           VECTOR_MUL_COMPONENT; column; REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Slightly gruesome lemmas: better to define sums over vectors really...    *)
(* ------------------------------------------------------------------------- *)

let VECTOR_COMPONENTWISE = prove
 (`!x:real^N.
    x = lambda j. sum(1..dimindex(:N))
                     (\i. x$i * (basis i :real^N)$j)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; basis] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(m:num = n) <=> (n = m)`] THEN
  SIMP_TAC[COND_RAND; REAL_MUL_RZERO; SUM_DELTA; IN_NUMSEG] THEN
  REWRITE_TAC[REAL_MUL_RID; COND_ID]);;

let LINEAR_COMPONENTWISE_EXPANSION = prove
 (`!f:real^M->real^N.
      linear(f)
      ==> !x j. 1 <= j /\ j <= dimindex(:N)
                ==> (f x $j =
                     sum(1..dimindex(:M)) (\i. x$i * f(basis i)$j))`,
  REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
   [VECTOR_COMPONENTWISE] THEN
  SPEC_TAC(`dimindex(:M)`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THENL
   [REWRITE_TAC[GSYM vec] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
     [GSYM VECTOR_MUL_LZERO] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC[vec; LAMBDA_BETA];
    REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN
    ASSUM_LIST(fun thl -> REWRITE_TAC(map GSYM thl)) THEN
    SIMP_TAC[GSYM VECTOR_MUL_COMPONENT;
             ASSUME `1 <= j`; ASSUME `j <= dimindex(:N)`] THEN
    ASSUM_LIST(fun thl -> REWRITE_TAC(map GSYM thl)) THEN
    SIMP_TAC[GSYM VECTOR_ADD_COMPONENT;
             ASSUME `1 <= j`; ASSUME `j <= dimindex(:N)`] THEN
    ASSUM_LIST(fun thl -> REWRITE_TAC(map GSYM thl)) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT]]);;

(* ------------------------------------------------------------------------- *)
(* Inverse matrices (not necessarily square, but it's vacuous otherwise).    *)
(* ------------------------------------------------------------------------- *)

let invertible = new_definition
  `invertible(A:real^N^M) <=>
        ?A':real^M^N. (A ** A' = mat 1) /\ (A' ** A = mat 1)`;;

let matrix_inv = new_definition
  `matrix_inv(A:real^N^M) =
        @A':real^M^N. (A ** A' = mat 1) /\ (A' ** A = mat 1)`;;

let MATRIX_INV = prove
 (`!A:real^N^M.
    invertible A ==> A ** matrix_inv A = mat 1 /\ matrix_inv A ** A = mat 1`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[matrix_inv; invertible] THEN
  CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[GSYM invertible]);;

let MATRIX_INV_UNIQUE = prove
 (`!A:real^N^M B. A ** B = mat 1 /\ B ** A = mat 1 ==> matrix_inv A = B`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `A:real^N^M` MATRIX_INV) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[invertible]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o
    AP_TERM `(( ** ):real^M^N->real^M^M->real^M^N) B` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[MATRIX_MUL_ASSOC; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let INVERTIBLE_NEG = prove
 (`!A:real^N^M. invertible(--A) <=> invertible A`,
  REWRITE_TAC[invertible] THEN
  MESON_TAC[MATRIX_MUL_LNEG; MATRIX_MUL_RNEG; MATRIX_NEG_NEG]);;

let MATRIX_INV_I = prove
 (`matrix_inv(mat 1:real^N^N) = mat 1`,
  MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
  REWRITE_TAC[MATRIX_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Correspondence between matrices and linear operators.                     *)
(* ------------------------------------------------------------------------- *)

let matrix = new_definition
  `(matrix:(real^M->real^N)->real^M^N) f = lambda i j. f(basis j)$i`;;

let MATRIX_VECTOR_MUL_LINEAR = prove
 (`!A:real^N^M. linear(\x. A ** x)`,
  REWRITE_TAC[linear; matrix_vector_mul] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
    VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG; GSYM SUM_LMUL; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_ADD_AC; REAL_MUL_AC]);;

let MATRIX_WORKS = prove
 (`!f:real^M->real^N. linear f ==> !x. matrix f ** x = f(x)`,
  REWRITE_TAC[matrix; matrix_vector_mul] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM LINEAR_COMPONENTWISE_EXPANSION]);;

let MATRIX_VECTOR_MUL = prove
 (`!f:real^M->real^N. linear f ==> f = \x. matrix f ** x`,
  SIMP_TAC[FUN_EQ_THM; MATRIX_WORKS]);;

let MATRIX_OF_MATRIX_VECTOR_MUL = prove
 (`!A:real^N^M. matrix(\x. A ** x) = A`,
  SIMP_TAC[MATRIX_EQ; MATRIX_VECTOR_MUL_LINEAR; MATRIX_WORKS]);;

let MATRIX_COMPOSE = prove
 (`!f g. linear f /\ linear g ==> (matrix(g o f) = matrix g ** matrix f)`,
  SIMP_TAC[MATRIX_EQ; MATRIX_WORKS; LINEAR_COMPOSE;
           GSYM MATRIX_VECTOR_MUL_ASSOC; o_THM]);;

let MATRIX_VECTOR_COLUMN = prove
 (`!A:real^N^M x.
        A ** x = vsum(1..dimindex(:N)) (\i. x$i % (transp A)$i)`,
  REWRITE_TAC[matrix_vector_mul; transp] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VSUM_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let MATRIX_MUL_COMPONENT = prove
 (`!i. 1 <= i /\ i <= dimindex(:N)
       ==> ((A:real^N^N) ** (B:real^N^N))$i = transp B ** A$i`,
  SIMP_TAC[matrix_mul; LAMBDA_BETA; matrix_vector_mul; vector_matrix_mul;
       transp; CART_EQ] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let ADJOINT_MATRIX = prove
 (`!A:real^N^M. adjoint(\x. A ** x) = (\x. transp A ** x)`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC ADJOINT_UNIQUE THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN REPEAT GEN_TAC THEN
  SIMP_TAC[transp; dot; LAMBDA_BETA; matrix_vector_mul;
           GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[REAL_MUL_AC]);;

let MATRIX_ADJOINT = prove
 (`!f. linear f ==> matrix(adjoint f) = transp(matrix f)`,
  GEN_TAC THEN DISCH_THEN
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV)
                [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
  REWRITE_TAC[ADJOINT_MATRIX; MATRIX_OF_MATRIX_VECTOR_MUL]);;

let MATRIX_ID = prove
 (`matrix(\x. x) = mat 1`,
  SIMP_TAC[MATRIX_EQ; LINEAR_ID; MATRIX_WORKS; MATRIX_VECTOR_MUL_LID]);;

let MATRIX_I = prove
 (`matrix I = mat 1`,
  REWRITE_TAC[I_DEF; MATRIX_ID]);;

let LINEAR_EQ_MATRIX = prove
 (`!f g. linear f /\ linear g /\ matrix f = matrix g ==> f = g`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP MATRIX_VECTOR_MUL)) THEN
  ASM_REWRITE_TAC[]);;

let MATRIX_SELF_ADJOINT = prove
 (`!f. linear f ==> (adjoint f = f <=> transp(matrix f) = matrix f)`,
  SIMP_TAC[GSYM MATRIX_ADJOINT] THEN
  MESON_TAC[LINEAR_EQ_MATRIX; ADJOINT_LINEAR]);;

let LINEAR_MATRIX_EXISTS = prove
 (`!f:real^M->real^N. linear f <=> ?A:real^M^N. f = \x. A ** x`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_LINEAR; LEFT_IMP_EXISTS_THM] THEN
  DISCH_TAC THEN EXISTS_TAC `matrix(f:real^M->real^N)` THEN
  ASM_SIMP_TAC[GSYM MATRIX_VECTOR_MUL]);;

let LINEAR_1 = prove
 (`!f:real^1->real^1. linear f <=> ?c. f = \x. c % x`,
  SIMP_TAC[LINEAR_MATRIX_EXISTS; EXISTS_VECTOR_1] THEN
  SIMP_TAC[FUN_EQ_THM; CART_EQ; FORALL_1; DIMINDEX_1; VECTOR_1;
           matrix_vector_mul; SUM_1; CART_EQ; LAMBDA_BETA;
           VECTOR_MUL_COMPONENT]);;

let SYMMETRIC_MATRIX = prove
 (`!A:real^N^N. transp A = A <=> adjoint(\x. A ** x) = \x. A ** x`,
  SIMP_TAC[MATRIX_SELF_ADJOINT; MATRIX_VECTOR_MUL_LINEAR] THEN
  REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL]);;

let SYMMETRIC_MATRIX_ORTHOGONAL_EIGENVECTORS = prove
 (`!A:real^N^N v w a b.
        transp A = A /\ A ** v = a % v /\ A ** w = b % w /\ ~(a = b)
        ==> orthogonal v w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SYMMETRIC_MATRIX] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        SELF_ADJOINT_ORTHOGONAL_EIGENVECTORS)) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

(* ------------------------------------------------------------------------- *)
(* Operator norm.                                                            *)
(* ------------------------------------------------------------------------- *)

let onorm = new_definition
 `onorm (f:real^M->real^N) = sup { norm(f x) | norm(x) = &1 }`;;

let NORM_BOUND_GENERALIZE = prove
 (`!f:real^M->real^N b.
        linear f
        ==> ((!x. (norm(x) = &1) ==> norm(f x) <= b) <=>
             (!x. norm(f x) <= b * norm(x)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_MUL_RID]] THEN
  X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `x:real^M = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; REAL_MUL_RZERO] THEN
    ASM_MESON_TAC[LINEAR_0; NORM_0; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; NORM_POS_LT; real_div] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(a * b) <= c ==> b * a <= c`) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM; GSYM NORM_MUL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV;
               NORM_EQ_0]);;

let ONORM = prove
 (`!f:real^M->real^N.
        linear f
        ==> (!x. norm(f x) <= onorm f * norm(x)) /\
            (!b. (!x. norm(f x) <= b * norm(x)) ==> onorm f <= b)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `{ norm((f:real^M->real^N) x) | norm(x) = &1 }` SUP) THEN
  SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
  ASM_SIMP_TAC[NORM_BOUND_GENERALIZE; GSYM onorm; GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[VECTOR_CHOOSE_SIZE; LINEAR_BOUNDED; REAL_POS]);;

let ONORM_POS_LE = prove
 (`!f. linear f ==> &0 <= onorm f`,
  MESON_TAC[ONORM; VECTOR_CHOOSE_SIZE; REAL_POS; REAL_MUL_RID; NORM_POS_LE;
            REAL_LE_TRANS]);;

let ONORM_EQ_0 = prove
 (`!f:real^M->real^N. linear f ==> ((onorm f = &0) <=> (!x. f x = vec 0))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `f:real^M->real^N` ONORM) THEN
  ASM_SIMP_TAC[GSYM REAL_LE_ANTISYM; ONORM_POS_LE; NORM_0; REAL_MUL_LZERO;
               NORM_LE_0; REAL_LE_REFL]);;

let ONORM_CONST = prove
 (`!y:real^N. onorm(\x:real^M. y) = norm(y)`,
  GEN_TAC THEN REWRITE_TAC[onorm] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sup {norm(y:real^N)}` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
     `(?x. P x) ==> {f y | x | P x} = {f y}`) THEN
    EXISTS_TAC `basis 1 :real^M` THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL];
    MATCH_MP_TAC REAL_SUP_UNIQUE THEN SET_TAC[REAL_LE_REFL]]);;

let ONORM_POS_LT = prove
 (`!f. linear f ==> (&0 < onorm f <=> ~(!x. f x = vec 0))`,
  SIMP_TAC[GSYM ONORM_EQ_0; ONORM_POS_LE;
           REAL_ARITH `(&0 < x <=> ~(x = &0)) <=> &0 <= x`]);;

let ONORM_COMPOSE = prove
 (`!f g. linear f /\ linear g ==> onorm(f o g) <= onorm f * onorm g`,
  MESON_TAC[ONORM; LINEAR_COMPOSE; o_THM; REAL_MUL_ASSOC; REAL_LE_TRANS; ONORM;
            REAL_LE_LMUL; ONORM_POS_LE]);;

let ONORM_NEG_LEMMA = prove
 (`!f. linear f ==> onorm(\x. --(f x)) <= onorm f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ONORM o
    MATCH_MP LINEAR_COMPOSE_NEG) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[NORM_NEG; ONORM]);;

let ONORM_NEG = prove
 (`!f:real^M->real^N. linear f ==> (onorm(\x. --(f x)) = onorm f)`,
  REPEAT STRIP_TAC THEN  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  ASM_SIMP_TAC[ONORM_NEG_LEMMA] THEN
  SUBGOAL_THEN `f:real^M->real^N = \x. --(--(f x))`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  ASM_SIMP_TAC[ONORM_NEG_LEMMA; LINEAR_COMPOSE_NEG] THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX]);;

let ONORM_TRIANGLE = prove
 (`!f:real^M->real^N g.
        linear f /\ linear g ==> onorm(\x. f x + g x) <= onorm f + onorm g`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o MATCH_MP ONORM o MATCH_MP
              LINEAR_COMPOSE_ADD) THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  ASM_MESON_TAC[REAL_LE_ADD2; REAL_LE_TRANS; NORM_TRIANGLE; ONORM]);;

let ONORM_TRIANGLE_LE = prove
 (`!f g. linear f /\ linear g /\ onorm(f) + onorm(g) <= e
         ==> onorm(\x. f x + g x) <= e`,
  MESON_TAC[REAL_LE_TRANS; ONORM_TRIANGLE]);;

let ONORM_TRIANGLE_LT = prove
 (`!f g. linear f /\ linear g /\ onorm(f) + onorm(g) < e
         ==> onorm(\x. f x + g x) < e`,
  MESON_TAC[REAL_LET_TRANS; ONORM_TRIANGLE]);;

let ONORM_ID = prove
 (`onorm(\x:real^N. x) = &1`,
  REWRITE_TAC[onorm] THEN
  SUBGOAL_THEN `{norm(x:real^N) | norm x = &1} = {&1}`
   (fun th -> REWRITE_TAC[th; SUP_SING]) THEN
  SUBGOAL_THEN `norm(basis 1:real^N) = &1` MP_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL]; SET_TAC[]]);;

let ONORM_I = prove
 (`onorm(I:real^N->real^N) = &1`,
  REWRITE_TAC[I_DEF; ONORM_ID]);;

(* ------------------------------------------------------------------------- *)
(* It's handy to "lift" from R to R^1 and "drop" from R^1 to R.              *)
(* ------------------------------------------------------------------------- *)

let lift = new_definition
 `(lift:real->real^1) x = lambda i. x`;;

let drop = new_definition
 `(drop:real^1->real) x = x$1`;;

let LIFT_COMPONENT = prove
 (`!x. (lift x)$1 = x`,
  SIMP_TAC[lift; LAMBDA_BETA; DIMINDEX_1; LE_ANTISYM]);;

let LIFT_DROP = prove
 (`(!x. lift(drop x) = x) /\ (!x. drop(lift x) = x)`,
  SIMP_TAC[lift; drop; CART_EQ; LAMBDA_BETA; DIMINDEX_1; LE_ANTISYM]);;

let IMAGE_LIFT_DROP = prove
 (`(!s. IMAGE (lift o drop) s = s) /\ (!s. IMAGE (drop o lift) s = s)`,
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN SET_TAC[]);;

let IN_IMAGE_LIFT_DROP = prove
 (`(!x s. x IN IMAGE lift s <=> drop x IN s) /\
   (!x s. x IN IMAGE drop s <=> lift x IN s)`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[LIFT_DROP]);;

let FORALL_LIFT = prove
 (`(!x. P x) = (!x. P(lift x))`,
  MESON_TAC[LIFT_DROP]);;

let EXISTS_LIFT = prove
 (`(?x. P x) = (?x. P(lift x))`,
  MESON_TAC[LIFT_DROP]);;

let FORALL_DROP = prove
 (`(!x. P x) = (!x. P(drop x))`,
  MESON_TAC[LIFT_DROP]);;

let EXISTS_DROP = prove
 (`(?x. P x) = (?x. P(drop x))`,
  MESON_TAC[LIFT_DROP]);;

let FORALL_LIFT_FUN = prove
 (`!P:(A->real^1)->bool. (!f. P f) <=> (!f. P(lift o f))`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `f:A->real^1` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `drop o (f:A->real^1)`) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]);;

let FORALL_DROP_FUN = prove
 (`!P:(A->real)->bool. (!f. P f) <=> (!f. P(drop o f))`,
  REWRITE_TAC[FORALL_LIFT_FUN; o_DEF; LIFT_DROP; ETA_AX]);;

let EXISTS_LIFT_FUN = prove
 (`!P:(A->real^1)->bool. (?f. P f) <=> (?f. P(lift o f))`,
  ONCE_REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_LIFT_FUN]);;

let EXISTS_DROP_FUN = prove
 (`!P:(A->real)->bool. (?f. P f) <=> (?f. P(drop o f))`,
  ONCE_REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[FORALL_DROP_FUN]);;

let LIFT_EQ = prove
 (`!x y. (lift x = lift y) <=> (x = y)`,
  MESON_TAC[LIFT_DROP]);;

let DROP_EQ = prove
 (`!x y. (drop x = drop y) <=> (x = y)`,
  MESON_TAC[LIFT_DROP]);;

let LIFT_IN_IMAGE_LIFT = prove
 (`!x s. (lift x) IN (IMAGE lift s) <=> x IN s`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[LIFT_DROP]);;

let FORALL_LIFT_IMAGE = prove
 (`!P. (!s. P s) <=> (!s. P(IMAGE lift s))`,
  MESON_TAC[IMAGE_LIFT_DROP; IMAGE_o]);;

let EXISTS_LIFT_IMAGE = prove
 (`!P. (?s. P s) <=> (?s. P(IMAGE lift s))`,
  MESON_TAC[IMAGE_LIFT_DROP; IMAGE_o]);;

let SUBSET_LIFT_IMAGE = prove
 (`!s t. IMAGE lift s SUBSET IMAGE lift t <=> s SUBSET t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[IMAGE_SUBSET] THEN
  DISCH_THEN(MP_TAC o ISPEC `drop` o MATCH_MP IMAGE_SUBSET) THEN
  REWRITE_TAC[GSYM IMAGE_o; IMAGE_LIFT_DROP]);;

let FORALL_DROP_IMAGE = prove
 (`!P. (!s. P s) <=> (!s. P(IMAGE drop s))`,
  MESON_TAC[IMAGE_LIFT_DROP; IMAGE_o]);;

let EXISTS_DROP_IMAGE = prove
 (`!P. (?s. P s) <=> (?s. P(IMAGE drop s))`,
  MESON_TAC[IMAGE_LIFT_DROP; IMAGE_o]);;

let SUBSET_DROP_IMAGE = prove
 (`!s t. IMAGE drop s SUBSET IMAGE drop t <=> s SUBSET t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[IMAGE_SUBSET] THEN
  DISCH_THEN(MP_TAC o ISPEC `lift` o MATCH_MP IMAGE_SUBSET) THEN
  REWRITE_TAC[GSYM IMAGE_o; IMAGE_LIFT_DROP]);;

let DROP_IN_IMAGE_DROP = prove
 (`!x s. (drop x) IN (IMAGE drop s) <=> x IN s`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[LIFT_DROP]);;

let LIFT_NUM = prove
 (`!n. lift(&n) = vec n`,
  SIMP_TAC[CART_EQ; lift; vec; LAMBDA_BETA]);;

let LIFT_ADD = prove
 (`!x y. lift(x + y) = lift x + lift y`,
  SIMP_TAC[CART_EQ; lift; LAMBDA_BETA; VECTOR_ADD_COMPONENT]);;

let LIFT_SUB = prove
 (`!x y. lift(x - y) = lift x - lift y`,
  SIMP_TAC[CART_EQ; lift; LAMBDA_BETA; VECTOR_SUB_COMPONENT]);;

let LIFT_CMUL = prove
 (`!x c. lift(c * x) = c % lift(x)`,
  SIMP_TAC[CART_EQ; lift; LAMBDA_BETA; VECTOR_MUL_COMPONENT]);;

let LIFT_NEG = prove
 (`!x. lift(--x) = --(lift x)`,
  SIMP_TAC[CART_EQ; lift; LAMBDA_BETA; VECTOR_NEG_COMPONENT]);;

let LIFT_EQ_CMUL = prove
 (`!x. lift x = x % vec 1`,
  REWRITE_TAC[GSYM LIFT_NUM; GSYM LIFT_CMUL; REAL_MUL_RID]);;

let SUM_VSUM = prove
 (`!f s. sum s f = drop(vsum s(lift o f))`,
  SIMP_TAC[vsum; drop; LAMBDA_BETA; DIMINDEX_1; ARITH] THEN
  REWRITE_TAC[o_THM; GSYM drop; LIFT_DROP; ETA_AX]);;

let VSUM_REAL = prove
 (`!f s. vsum s f = lift(sum s (drop o f))`,
  REWRITE_TAC[o_DEF; SUM_VSUM; LIFT_DROP; ETA_AX]);;

let LIFT_SUM = prove
 (`!k x. lift(sum k x) = vsum k (lift o x)`,
  REWRITE_TAC[SUM_VSUM; LIFT_DROP]);;

let DROP_VSUM = prove
 (`!k x. drop(vsum k x) = sum k (drop o x)`,
  REWRITE_TAC[VSUM_REAL; LIFT_DROP]);;

let DROP_LAMBDA = prove
 (`!x. drop(lambda i. x i) = x 1`,
  SIMP_TAC[drop; LAMBDA_BETA; DIMINDEX_1; LE_REFL]);;

let DROP_VEC = prove
 (`!n. drop(vec n) = &n`,
  MESON_TAC[LIFT_DROP; LIFT_NUM]);;

let DROP_ADD = prove
 (`!x y. drop(x + y) = drop x + drop y`,
  MESON_TAC[LIFT_DROP; LIFT_ADD]);;

let DROP_SUB = prove
 (`!x y. drop(x - y) = drop x - drop y`,
  MESON_TAC[LIFT_DROP; LIFT_SUB]);;

let DROP_CMUL = prove
 (`!x c. drop(c % x) = c * drop(x)`,
  MESON_TAC[LIFT_DROP; LIFT_CMUL]);;

let DROP_NEG = prove
 (`!x. drop(--x) = --(drop x)`,
  MESON_TAC[LIFT_DROP; LIFT_NEG]);;

let NORM_1 = prove
 (`!x. norm x = abs(drop x)`,
  REWRITE_TAC[drop; NORM_REAL]);;

let NORM_1_POS = prove
 (`!x. &0 <= drop x ==> norm x = drop x`,
  SIMP_TAC[NORM_1; real_abs]);;

let NORM_LIFT = prove
 (`!x. norm(lift x) = abs(x)`,
  SIMP_TAC[lift; NORM_REAL; LIFT_COMPONENT]);;

let DIST_LIFT = prove
 (`!x y. dist(lift x,lift y) = abs(x - y)`,
  REWRITE_TAC[DIST_REAL; LIFT_COMPONENT]);;

let ABS_DROP = prove
 (`!x. norm x = abs(drop x)`,
  REWRITE_TAC[FORALL_LIFT; LIFT_DROP; NORM_LIFT]);;

let LINEAR_VMUL_DROP = prove
 (`!f v. linear f ==> linear (\x. drop(f x) % v)`,
  SIMP_TAC[drop; LINEAR_VMUL_COMPONENT; DIMINDEX_1; LE_REFL]);;

let LINEAR_FROM_REALS = prove
 (`!f:real^1->real^N. linear f ==> f = \x. drop x % column 1 (matrix f)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  SIMP_TAC[CART_EQ; matrix_vector_mul; vector_mul; LAMBDA_BETA;
           DIMINDEX_1; SUM_SING_NUMSEG; drop; column] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let LINEAR_TO_REALS = prove
 (`!f:real^N->real^1. linear f ==> f = \x. lift(row 1 (matrix f) dot x)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  SIMP_TAC[CART_EQ; matrix_vector_mul; dot; LAMBDA_BETA;
           DIMINDEX_1; SUM_SING_NUMSEG; lift; row; LE_ANTISYM]);;

let DROP_EQ_0 = prove
 (`!x. drop x = &0 <=> x = vec 0`,
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC]);;

let DROP_WLOG_LE = prove
 (`(!x y. P x y <=> P y x) /\ (!x y. drop x <= drop y ==> P x y)
   ==> (!x y. P x y)`,
  MESON_TAC[REAL_LE_TOTAL]);;

let IMAGE_LIFT_UNIV = prove
 (`IMAGE lift (:real) = (:real^1)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN MESON_TAC[LIFT_DROP]);;

let IMAGE_DROP_UNIV = prove
 (`IMAGE drop (:real^1) = (:real)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN MESON_TAC[LIFT_DROP]);;

let LINEAR_LIFT_DOT = prove
 (`!a. linear(\x. lift(a dot x))`,
  REWRITE_TAC[linear; DOT_RMUL; DOT_RADD; LIFT_ADD; LIFT_CMUL]);;

let LINEAR_LIFT_COMPONENT = prove
 (`!k. linear(\x:real^N. lift(x$k))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?j. 1 <= j /\ j <= dimindex(:N) /\ !z:real^N. z$k = z$j`
  CHOOSE_TAC THENL
   [REWRITE_TAC[FINITE_INDEX_INRANGE];
    MP_TAC(ISPEC `basis j:real^N` LINEAR_LIFT_DOT) THEN
    ASM_SIMP_TAC[DOT_BASIS]]);;

let BILINEAR_DROP_MUL = prove
 (`bilinear (\x y:real^N. drop x % y)`,
  REWRITE_TAC[bilinear; linear] THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC);;

let LINEAR_COMPONENTWISE = prove
 (`!f:real^M->real^N.
        linear f <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> linear(\x. lift(f(x)$i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linear] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CART_EQ] THEN
  SIMP_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pasting vectors.                                                          *)
(* ------------------------------------------------------------------------- *)

let LINEAR_FSTCART = prove
 (`linear fstcart`,
  SIMP_TAC[linear; fstcart; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; DIMINDEX_FINITE_SUM;
           ARITH_RULE `x <= a ==> x <= a + b:num`]);;

let LINEAR_SNDCART = prove
 (`linear sndcart`,
  SIMP_TAC[linear; sndcart; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; DIMINDEX_FINITE_SUM;
           ARITH_RULE `x <= a ==> x <= a + b:num`;
           ARITH_RULE `x <= b ==> x + a <= a + b:num`]);;

let FSTCART_VEC = prove
 (`!n. fstcart(vec n) = vec n`,
  SIMP_TAC[vec; fstcart; LAMBDA_BETA; CART_EQ; DIMINDEX_FINITE_SUM;
           ARITH_RULE `m <= n:num ==> m <= n + p`]);;

let FSTCART_ADD = prove
 (`!x:real^(M,N)finite_sum y. fstcart(x + y) = fstcart(x) + fstcart(y)`,
  REWRITE_TAC[REWRITE_RULE[linear] LINEAR_FSTCART]);;

let FSTCART_CMUL = prove
 (`!x:real^(M,N)finite_sum c. fstcart(c % x) = c % fstcart(x)`,
  REWRITE_TAC[REWRITE_RULE[linear] LINEAR_FSTCART]);;

let FSTCART_NEG = prove
 (`!x:real^(M,N)finite_sum. --(fstcart x) = fstcart(--x)`,
  ONCE_REWRITE_TAC[VECTOR_ARITH `--x = --(&1) % x`] THEN
  REWRITE_TAC[FSTCART_CMUL]);;

let FSTCART_SUB = prove
 (`!x:real^(M,N)finite_sum y. fstcart(x - y) = fstcart(x) - fstcart(y)`,
  REWRITE_TAC[VECTOR_SUB; FSTCART_NEG; FSTCART_ADD]);;

let FSTCART_VSUM = prove
 (`!k x. FINITE k ==> (fstcart(vsum k x) = vsum k (\i. fstcart(x i)))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_RULES; FSTCART_ADD; FSTCART_VEC]);;

let SNDCART_VEC = prove
 (`!n. sndcart(vec n) = vec n`,
  SIMP_TAC[vec; sndcart; LAMBDA_BETA; CART_EQ; DIMINDEX_FINITE_SUM;
           ARITH_RULE `x <= a ==> x <= a + b:num`;
           ARITH_RULE `x <= b ==> x + a <= a + b:num`]);;

let SNDCART_ADD = prove
 (`!x:real^(M,N)finite_sum y. sndcart(x + y) = sndcart(x) + sndcart(y)`,
  REWRITE_TAC[REWRITE_RULE[linear] LINEAR_SNDCART]);;

let SNDCART_CMUL = prove
 (`!x:real^(M,N)finite_sum c. sndcart(c % x) = c % sndcart(x)`,
  REWRITE_TAC[REWRITE_RULE[linear] LINEAR_SNDCART]);;

let SNDCART_NEG = prove
 (`!x:real^(M,N)finite_sum. --(sndcart x) = sndcart(--x)`,
  ONCE_REWRITE_TAC[VECTOR_ARITH `--x = --(&1) % x`] THEN
  REWRITE_TAC[SNDCART_CMUL]);;

let SNDCART_SUB = prove
 (`!x:real^(M,N)finite_sum y. sndcart(x - y) = sndcart(x) - sndcart(y)`,
  REWRITE_TAC[VECTOR_SUB; SNDCART_NEG; SNDCART_ADD]);;

let SNDCART_VSUM = prove
 (`!k x. FINITE k ==> (sndcart(vsum k x) = vsum k (\i. sndcart(x i)))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_RULES; SNDCART_ADD; SNDCART_VEC]);;

let PASTECART_VEC = prove
 (`!n. pastecart (vec n) (vec n) = vec n`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_VEC; SNDCART_VEC;
              FSTCART_PASTECART; SNDCART_PASTECART]);;

let PASTECART_ADD = prove
 (`!x1 y1 x2:real^M y2:real^N.
     pastecart x1 y1 + pastecart x2 y2 = pastecart (x1 + x2) (y1 + y2)`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_ADD; SNDCART_ADD;
              FSTCART_PASTECART; SNDCART_PASTECART]);;

let PASTECART_CMUL = prove
 (`!x1 y1 c. pastecart (c % x1) (c % y1) = c % pastecart x1 y1`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_CMUL; SNDCART_CMUL;
              FSTCART_PASTECART; SNDCART_PASTECART]);;

let PASTECART_NEG = prove
 (`!x:real^M y:real^N. pastecart (--x) (--y) = --(pastecart x y)`,
  ONCE_REWRITE_TAC[VECTOR_ARITH `--x = --(&1) % x`] THEN
  REWRITE_TAC[PASTECART_CMUL]);;

let PASTECART_SUB = prove
 (`!x1 y1 x2:real^M y2:real^N.
     pastecart x1 y1 - pastecart x2 y2 = pastecart (x1 - x2) (y1 - y2)`,
  REWRITE_TAC[VECTOR_SUB; GSYM PASTECART_NEG; PASTECART_ADD]);;

let PASTECART_VSUM = prove
 (`!k x y. FINITE k ==> (pastecart (vsum k x) (vsum k y) =
                         vsum k (\i. pastecart (x i) (y i)))`,
  SIMP_TAC[PASTECART_EQ; FSTCART_VSUM; SNDCART_VSUM;
           FSTCART_PASTECART; SNDCART_PASTECART; ETA_AX]);;

let PASTECART_EQ_VEC = prove
 (`!x y n. pastecart x y = vec n <=> x = vec n /\ y = vec n`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_VEC; SNDCART_VEC;
              FSTCART_PASTECART; SNDCART_PASTECART]);;

let NORM_FSTCART = prove
 (`!x. norm(fstcart x) <= norm x`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM PASTECART_FST_SND] THEN
  SIMP_TAC[SQRT_MONO_LE_EQ; DOT_POS_LE; vector_norm] THEN
  SIMP_TAC[pastecart; dot; DIMINDEX_FINITE_SUM; LAMBDA_BETA; DIMINDEX_NONZERO;
           SUM_ADD_SPLIT; REAL_LE_ADDR; SUM_POS_LE; FINITE_NUMSEG;
           REAL_LE_SQUARE; ARITH_RULE `x <= a ==> x <= a + b:num`;
           ARITH_RULE `~(d = 0) ==> 1 <= d + 1`]);;

let DIST_FSTCART = prove
 (`!x y. dist(fstcart x,fstcart y) <= dist(x,y)`,
  REWRITE_TAC[dist; GSYM FSTCART_SUB; NORM_FSTCART]);;

let NORM_SNDCART = prove
 (`!x. norm(sndcart x) <= norm x`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM PASTECART_FST_SND] THEN
  SIMP_TAC[SQRT_MONO_LE_EQ; DOT_POS_LE; vector_norm] THEN
  SIMP_TAC[pastecart; dot; DIMINDEX_FINITE_SUM; LAMBDA_BETA; DIMINDEX_NONZERO;
           SUM_ADD_SPLIT; ARITH_RULE `x <= a ==> x <= a + b:num`;
           ARITH_RULE `~(d = 0) ==> 1 <= d + 1`] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[NUMSEG_OFFSET_IMAGE] THEN
  SIMP_TAC[SUM_IMAGE; FINITE_NUMSEG; EQ_ADD_RCANCEL; o_DEF; ADD_SUB] THEN
  SIMP_TAC[ARITH_RULE `1 <= x ==> ~(x + a <= a)`; SUM_POS_LE; FINITE_NUMSEG;
           REAL_LE_ADDL; REAL_LE_SQUARE]);;

let DIST_SNDCART = prove
 (`!x y. dist(sndcart x,sndcart y) <= dist(x,y)`,
  REWRITE_TAC[dist; GSYM SNDCART_SUB; NORM_SNDCART]);;

let DOT_PASTECART = prove
 (`!x1 x2 y1 y2. (pastecart x1 x2) dot (pastecart y1 y2) =
                x1 dot y1 + x2 dot y2`,
  SIMP_TAC[pastecart; dot; LAMBDA_BETA; DIMINDEX_FINITE_SUM] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `~(d = 0) ==> 1 <= d + 1`;
           DIMINDEX_NONZERO; REAL_LE_LADD] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[NUMSEG_OFFSET_IMAGE] THEN
  SIMP_TAC[SUM_IMAGE; FINITE_NUMSEG; EQ_ADD_RCANCEL; o_DEF; ADD_SUB] THEN
  SIMP_TAC[ARITH_RULE `1 <= x ==> ~(x + a <= a)`; REAL_LE_REFL]);;

let SQNORM_PASTECART = prove
 (`!x y. norm(pastecart x y) pow 2 = norm(x) pow 2 + norm(y) pow 2`,
  REWRITE_TAC[NORM_POW_2; DOT_PASTECART]);;

let NORM_PASTECART = prove
 (`!x y. norm(pastecart x y) = sqrt(norm(x) pow 2 + norm(y) pow 2)`,
  REWRITE_TAC[NORM_EQ_SQUARE] THEN
  SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_LE_ADD; REAL_LE_POW_2] THEN
  REWRITE_TAC[DOT_PASTECART; NORM_POW_2]);;

let NORM_PASTECART_LE = prove
 (`!x y. norm(pastecart x y) <= norm(x) + norm(y)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC TRIANGLE_LEMMA THEN
  REWRITE_TAC[NORM_POS_LE; NORM_POW_2; DOT_PASTECART; REAL_LE_REFL]);;

let NORM_LE_PASTECART = prove
 (`!x:real^M y:real^N.
    norm(x) <= norm(pastecart x y) /\
    norm(y) <= norm(pastecart x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORM_PASTECART] THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  REWRITE_TAC[REAL_LE_ADDL; REAL_LE_ADDR; REAL_LE_POW_2]);;

let NORM_PASTECART_0 = prove
 (`(!x. norm(pastecart x (vec 0)) = norm x) /\
   (!y. norm(pastecart (vec 0) y) = norm y)`,
  REWRITE_TAC[NORM_EQ_SQUARE; NORM_POW_2; NORM_POS_LE] THEN
  REWRITE_TAC[DOT_PASTECART; DOT_LZERO; REAL_ADD_LID; REAL_ADD_RID]);;

let DIST_PASTECART_CANCEL = prove
 (`(!x x' y. dist(pastecart x y,pastecart x' y) = dist(x,x')) /\
   (!x y y'. dist(pastecart x y,pastecart x y') = dist(y,y'))`,
  REWRITE_TAC[dist; PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART_0]);;

let LINEAR_PASTECART = prove
 (`!f:real^M->real^N g:real^M->real^P.
        linear f /\ linear g ==> linear (\x. pastecart (f x) (g x))`,
  SIMP_TAC[linear; PASTECART_ADD; GSYM PASTECART_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* A bit of linear algebra.                                                  *)
(* ------------------------------------------------------------------------- *)

let subspace = new_definition
 `subspace s <=>
        vec(0) IN s /\
        (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\
        (!c x. x IN s ==> (c % x) IN s)`;;

let span = new_definition
  `span s = subspace hull s`;;

let dependent = new_definition
 `dependent s <=> ?a. a IN s /\ a IN span(s DELETE a)`;;

let independent = new_definition
 `independent s <=> ~(dependent s)`;;

(* ------------------------------------------------------------------------- *)
(* Closure properties of subspaces.                                          *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_UNIV = prove
 (`subspace(UNIV:real^N->bool)`,
  REWRITE_TAC[subspace; IN_UNIV]);;

let SUBSPACE_IMP_NONEMPTY = prove
 (`!s. subspace s ==> ~(s = {})`,
  REWRITE_TAC[subspace] THEN SET_TAC[]);;

let SUBSPACE_0 = prove
 (`subspace s ==> vec(0) IN s`,
  SIMP_TAC[subspace]);;

let SUBSPACE_ADD = prove
 (`!x y s. subspace s /\ x IN s /\ y IN s ==> (x + y) IN s`,
  SIMP_TAC[subspace]);;

let SUBSPACE_MUL = prove
 (`!x c s. subspace s /\ x IN s ==> (c % x) IN s`,
  SIMP_TAC[subspace]);;

let SUBSPACE_NEG = prove
 (`!x s. subspace s /\ x IN s ==> (--x) IN s`,
  SIMP_TAC[VECTOR_ARITH `--x = --(&1) % x`; SUBSPACE_MUL]);;

let SUBSPACE_SUB = prove
 (`!x y s. subspace s /\ x IN s /\ y IN s ==> (x - y) IN s`,
  SIMP_TAC[VECTOR_SUB; SUBSPACE_ADD; SUBSPACE_NEG]);;

let SUBSPACE_VSUM = prove
 (`!s f t. subspace s /\ FINITE t /\ (!x. x IN t ==> f(x) IN s)
           ==> (vsum t f) IN s`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; SUBSPACE_0; IN_INSERT; SUBSPACE_ADD]);;

let SUBSPACE_LINEAR_IMAGE = prove
 (`!f s. linear f /\ subspace s ==> subspace(IMAGE f s)`,
  REWRITE_TAC[subspace; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN
  MESON_TAC[linear; LINEAR_0]);;

let SUBSPACE_LINEAR_PREIMAGE = prove
 (`!f s. linear f /\ subspace s ==> subspace {x | f(x) IN s}`,
  REWRITE_TAC[subspace; IN_ELIM_THM] THEN
  MESON_TAC[linear; LINEAR_0]);;

let SUBSPACE_TRIVIAL = prove
 (`subspace {vec 0}`,
  SIMP_TAC[subspace; IN_SING] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let SUBSPACE_INTER = prove
 (`!s t. subspace s /\ subspace t ==> subspace (s INTER t)`,
  REWRITE_TAC[subspace; IN_INTER] THEN MESON_TAC[]);;

let SUBSPACE_INTERS = prove
 (`!f. (!s. s IN f ==> subspace s) ==> subspace(INTERS f)`,
  SIMP_TAC[subspace; IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_INTERS]);;

let LINEAR_INJECTIVE_0_SUBSPACE = prove
 (`!f:real^M->real^N s.
        linear f /\ subspace s
         ==> ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
              (!x. x IN s /\ f x = vec 0 ==> x = vec 0))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM VECTOR_SUB_EQ] THEN
  ASM_SIMP_TAC[GSYM LINEAR_SUB] THEN
  ASM_MESON_TAC[VECTOR_SUB_RZERO; SUBSPACE_SUB; SUBSPACE_0]);;

let SUBSPACE_UNION_CHAIN = prove
 (`!s t:real^N->bool.
        subspace s /\ subspace t /\ subspace(s UNION t)
         ==> s SUBSET t \/ t SUBSET s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_RULE
   `s SUBSET t \/ t SUBSET s <=>
    ~(?x y. x IN s /\ ~(x IN t) /\ y IN t /\ ~(y IN s))`] THEN
  STRIP_TAC THEN SUBGOAL_THEN `(x + y:real^N) IN s UNION t` MP_TAC THENL
   [MATCH_MP_TAC SUBSPACE_ADD THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN
    ASM_MESON_TAC[SUBSPACE_SUB; VECTOR_ARITH
     `(x + y) - x:real^N = y /\ (x + y) - y = x`]]);;

let SUBSPACE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t ==> subspace(s PCROSS t)`,
  REWRITE_TAC[subspace; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; GSYM PASTECART_CMUL; PASTECART_ADD] THEN
  REWRITE_TAC[GSYM PASTECART_VEC; PASTECART_IN_PCROSS] THEN SIMP_TAC[]);;

let SUBSPACE_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace(s PCROSS t) <=> subspace s /\ subspace t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [ASM_MESON_TAC[PCROSS_EMPTY; SUBSPACE_IMP_NONEMPTY]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_MESON_TAC[PCROSS_EMPTY; SUBSPACE_IMP_NONEMPTY]; ALL_TAC] THEN
  EQ_TAC THEN REWRITE_TAC[SUBSPACE_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
     `(s:real^M->bool) PCROSS (t:real^N->bool)`] SUBSPACE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
     `(s:real^M->bool) PCROSS (t:real^N->bool)`] SUBSPACE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SPAN_SPAN = prove
 (`!s. span(span s) = span s`,
  REWRITE_TAC[span; HULL_HULL]);;

let SPAN_MONO = prove
 (`!s t. s SUBSET t ==> span s SUBSET span t`,
  REWRITE_TAC[span; HULL_MONO]);;

let SUBSPACE_SPAN = prove
 (`!s. subspace(span s)`,
  GEN_TAC THEN REWRITE_TAC[span] THEN MATCH_MP_TAC P_HULL THEN
  SIMP_TAC[subspace; IN_INTERS]);;

let SPAN_CLAUSES = prove
 (`(!a s. a IN s ==> a IN span s) /\
   (vec(0) IN span s) /\
   (!x y s. x IN span s /\ y IN span s ==> (x + y) IN span s) /\
   (!x c s. x IN span s ==> (c % x) IN span s)`,
  MESON_TAC[span; HULL_SUBSET; SUBSET; SUBSPACE_SPAN; subspace]);;

let SPAN_INDUCT = prove
 (`!s h. (!x. x IN s ==> x IN h) /\ subspace h ==> !x. x IN span(s) ==> h(x)`,
  REWRITE_TAC[span] THEN MESON_TAC[SUBSET; HULL_MINIMAL; IN]);;

let SPAN_EMPTY = prove
 (`span {} = {vec 0}`,
  REWRITE_TAC[span] THEN MATCH_MP_TAC HULL_UNIQUE THEN
  SIMP_TAC[subspace; SUBSET; IN_SING; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let INDEPENDENT_EMPTY = prove
 (`independent {}`,
  REWRITE_TAC[independent; dependent; NOT_IN_EMPTY]);;

let INDEPENDENT_NONZERO = prove
 (`!s. independent s ==> ~(vec 0 IN s)`,
  REWRITE_TAC[independent; dependent] THEN MESON_TAC[SPAN_CLAUSES]);;

let INDEPENDENT_MONO = prove
 (`!s t. independent t /\ s SUBSET t ==> independent s`,
  REWRITE_TAC[independent; dependent] THEN
  ASM_MESON_TAC[SPAN_MONO; SUBSET; IN_DELETE]);;

let DEPENDENT_MONO = prove
 (`!s t:real^N->bool. dependent s /\ s SUBSET t ==> dependent t`,
  ONCE_REWRITE_TAC[TAUT `p /\ q ==> r <=> ~r /\ q ==> ~p`] THEN
  REWRITE_TAC[GSYM independent; INDEPENDENT_MONO]);;

let SPAN_SUBSPACE = prove
 (`!b s. b SUBSET s /\ s SUBSET (span b) /\ subspace s ==> (span b = s)`,
  MESON_TAC[SUBSET_ANTISYM; span; HULL_MINIMAL]);;

let SPAN_INDUCT_ALT = prove
 (`!s h. h(vec 0) /\
         (!c x y. x IN s /\ h(y) ==> h(c % x + y))
          ==> !x:real^N. x IN span(s) ==> h(x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o prove_inductive_relations_exist o concl) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^N. x IN span(s) ==> g(x)`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC[subspace; IN_ELIM_THM] THEN
  REWRITE_TAC[IN; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_MESON_TAC[IN; VECTOR_ADD_LID; VECTOR_ADD_ASSOC; VECTOR_ADD_SYM;
                VECTOR_MUL_LID; VECTOR_MUL_RZERO]);;

