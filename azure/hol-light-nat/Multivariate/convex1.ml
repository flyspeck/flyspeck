(* ========================================================================= *)
(* Convex sets, functions and related things.                                *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*                 (c) Copyright, Lars Schewe 2007                           *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

open Hol_core
open Vectors
open Determinants
open Topology


(* ------------------------------------------------------------------------- *)
(* Some miscelleneous things that are convenient to prove here.              *)
(* ------------------------------------------------------------------------- *)

let TRANSLATION_GALOIS = prove
 (`!s t a:real^N. s = IMAGE (\x. a + x) t <=> t = IMAGE (\x. --a + x) s`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[VECTOR_ARITH `--a + a + x:real^N = x`;
              VECTOR_ARITH `a + --a + x:real^N = x`] THEN
  REWRITE_TAC[IMAGE_ID]);;

let TRANSLATION_EQ_IMP = prove
 (`!P:(real^N->bool)->bool.
        (!a s. P(IMAGE (\x. a + x) s) <=> P s) <=>
        (!a s. P s ==> P (IMAGE (\x. a + x) s))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `s:real^N->bool`] THEN
  EQ_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FIRST_X_ASSUM
   (MP_TAC o SPECL [`--a:real^N`; `IMAGE (\x:real^N. a + x) s`]) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID;
                  VECTOR_ARITH `--a + a + x:real^N = x`]);;

let DIM_HYPERPLANE = prove
 (`!a:real^N. ~(a = vec 0) ==> dim {x | a dot x = &0} = dimindex(:N) - 1`,
  GEOM_BASIS_MULTIPLE_TAC 1 `a:real^N` THEN
  SIMP_TAC[VECTOR_MUL_EQ_0; DE_MORGAN_THM; DOT_LMUL; DOT_BASIS;
           DIMINDEX_GE_1; LE_REFL; REAL_ENTIRE; DIM_SPECIAL_HYPERPLANE]);;

let LOWDIM_EQ_HYPERPLANE = prove
 (`!s. dim s = dimindex(:N) - 1
       ==> ?a:real^N. ~(a = vec 0) /\ span s = {x | a dot x = &0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` LOWDIM_SUBSET_HYPERPLANE) THEN
  ASM_SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= a ==> a - 1 < a`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `a:real^N` SUBSPACE_HYPERPLANE) THEN
  ONCE_REWRITE_TAC[GSYM SPAN_EQ_SELF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC DIM_EQ_SPAN THEN
  ASM_SIMP_TAC[DIM_HYPERPLANE; LE_REFL] THEN
  ASM_MESON_TAC[SUBSET_TRANS; SPAN_INC]);;

let DIM_EQ_HYPERPLANE = prove
 (`!s. dim s = dimindex(:N) - 1 <=>
       ?a:real^N. ~(a = vec 0) /\ span s = {x | a dot x = &0}`,
  MESON_TAC[DIM_HYPERPLANE; LOWDIM_EQ_HYPERPLANE; DIM_SPAN]);;

(* ------------------------------------------------------------------------- *)
(* Affine set and affine hull.                                               *)
(* ------------------------------------------------------------------------- *)

let affine = new_definition
  `affine s <=> !x y u v. x IN s /\ y IN s /\ (u + v = &1)
                          ==> (u % x + v % y) IN s`;;

let AFFINE_ALT = prove
 (`affine s <=> !x y u. x IN s /\ y IN s ==> ((&1 - u) % x + u % y) IN s`,
  REWRITE_TAC[affine] THEN
  MESON_TAC[REAL_ARITH `(u + v = &1) <=> (u = &1 - v)`]);;

let AFFINE_SCALING = prove
 (`!s c. affine s ==> affine (IMAGE (\x. c % x) s)`,
  REWRITE_TAC[affine; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `u % c % x + v % c % y = c % (u % x + v % y)`] THEN
  ASM_MESON_TAC[]);;

let AFFINE_SCALING_EQ = prove
 (`!s c. ~(c = &0) ==> (affine (IMAGE (\x. c % x) s) <=> affine s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[AFFINE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c` o MATCH_MP AFFINE_SCALING) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; o_DEF; VECTOR_MUL_ASSOC;
               REAL_MUL_LINV; VECTOR_MUL_LID; IMAGE_ID]);;

let AFFINE_NEGATIONS = prove
 (`!s. affine s ==> affine (IMAGE (--) s)`,
  REWRITE_TAC[affine; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `u % --x + v % --y = --(u % x + v % y)`] THEN
  ASM_MESON_TAC[]);;

let AFFINE_SUMS = prove
 (`!s t. affine s /\ affine t ==> affine {x + y | x IN s /\ y IN t}`,
  REWRITE_TAC[affine; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
    `u % (a + b) + v % (c + d) = (u % a + v % c) + (u % b + v % d)`] THEN
  ASM_MESON_TAC[]);;

let AFFINE_DIFFERENCES = prove
 (`!s t. affine s /\ affine t ==> affine {x - y | x IN s /\ y IN t}`,
  REWRITE_TAC[affine; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
    `u % (a - b) + v % (c - d) = (u % a + v % c) - (u % b + v % d)`] THEN
  ASM_MESON_TAC[]);;

let AFFINE_TRANSLATION_EQ = prove
 (`!a:real^N s. affine (IMAGE (\x. a + x) s) <=> affine s`,
  REWRITE_TAC[AFFINE_ALT; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE; UNWIND_THM1; VECTOR_ARITH
   `(&1 - u) % (a + x) + u % (a + y) = a + z <=> (&1 - u) % x + u % y = z`]);;

add_translation_invariants [AFFINE_TRANSLATION_EQ];;

let AFFINE_TRANSLATION = prove
 (`!s a:real^N. affine s ==> affine (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[AFFINE_TRANSLATION_EQ]);;

let AFFINE_AFFINITY = prove
 (`!s a:real^N c.
        affine s ==> affine (IMAGE (\x. a + c % x) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; AFFINE_TRANSLATION; AFFINE_SCALING]);;

let AFFINE_LINEAR_IMAGE = prove
 (`!f s. affine s /\ linear f ==> affine(IMAGE f s)`,
  REWRITE_TAC[affine; FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IN_IMAGE; linear] THEN MESON_TAC[]);;

let AFFINE_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (affine (IMAGE f s) <=> affine s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE AFFINE_LINEAR_IMAGE));;

add_linear_invariants [AFFINE_LINEAR_IMAGE_EQ];;

let AFFINE_EMPTY = prove
 (`affine {}`,
  REWRITE_TAC[affine; NOT_IN_EMPTY]);;

let AFFINE_SING = prove
 (`!x. affine {x}`,
  SIMP_TAC[AFFINE_ALT; IN_SING] THEN
  REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_SUB_ADD; VECTOR_MUL_LID]);;

let AFFINE_UNIV = prove
 (`affine(UNIV:real^N->bool)`,
  REWRITE_TAC[affine; IN_UNIV]);;

let AFFINE_HYPERPLANE = prove
 (`!a b. affine {x | a dot x = b}`,
  REWRITE_TAC[affine; IN_ELIM_THM; DOT_RADD; DOT_RMUL] THEN
  CONV_TAC REAL_RING);;

let AFFINE_STANDARD_HYPERPLANE = prove
 (`!a b k. affine {x:real^N | x$k = b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `b:real`] AFFINE_HYPERPLANE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let AFFINE_INTERS = prove
 (`(!s. s IN f ==> affine s) ==> affine(INTERS f)`,
  REWRITE_TAC[affine; IN_INTERS] THEN MESON_TAC[]);;

let AFFINE_INTER = prove
 (`!s t. affine s /\ affine t ==> affine(s INTER t)`,
  REWRITE_TAC[affine; IN_INTER] THEN MESON_TAC[]);;

let AFFINE_AFFINE_HULL = prove
 (`!s. affine(affine hull s)`,
  SIMP_TAC[P_HULL; AFFINE_INTERS]);;

let AFFINE_HULL_EQ = prove
 (`!s. (affine hull s = s) <=> affine s`,
  SIMP_TAC[HULL_EQ; AFFINE_INTERS]);;

let IS_AFFINE_HULL = prove
 (`!s. affine s <=> ?t. s = affine hull t`,
  GEN_TAC THEN MATCH_MP_TAC IS_HULL THEN SIMP_TAC[AFFINE_INTERS]);;

let AFFINE_HULL_UNIV = prove
 (`affine hull (:real^N) = (:real^N)`,
  REWRITE_TAC[AFFINE_HULL_EQ; AFFINE_UNIV]);;

let AFFINE_HULLS_EQ = prove
 (`!s t. s SUBSET affine hull t /\ t SUBSET affine hull s
         ==> affine hull s = affine hull t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULLS_EQ THEN
  ASM_SIMP_TAC[AFFINE_INTERS]);;

let AFFINE_HULL_TRANSLATION = prove
 (`!a s. affine hull (IMAGE (\x. a + x) s) =
         IMAGE (\x. a + x) (affine hull s)`,
  REWRITE_TAC[hull] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [AFFINE_HULL_TRANSLATION];;

let AFFINE_HULL_LINEAR_IMAGE = prove
 (`!f s. linear f
         ==> affine hull (IMAGE f s) = IMAGE f (affine hull s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  CONJ_TAC THEN MATCH_MP_TAC HULL_INDUCT THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN SIMP_TAC[FUN_IN_IMAGE; HULL_INC] THEN
  REWRITE_TAC[affine; IN_ELIM_THM] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_ADD th)]) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    MESON_TAC[REWRITE_RULE[affine] AFFINE_AFFINE_HULL];
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
    MESON_TAC[REWRITE_RULE[affine] AFFINE_AFFINE_HULL]]);;

add_linear_invariants [AFFINE_HULL_LINEAR_IMAGE];;

let IN_AFFINE_HULL_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s x.
        linear f /\ x IN affine hull s ==> (f x) IN affine hull (IMAGE f s)`,
  SIMP_TAC[AFFINE_HULL_LINEAR_IMAGE] THEN SET_TAC[]);;

let SAME_DISTANCES_TO_AFFINE_HULL = prove
 (`!s a b:real^N.
        (!x. x IN s ==> dist(x,a) = dist(x,b))
        ==> (!x. x IN affine hull s ==> dist(x,a) = dist(x,b))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HULL_INDUCT THEN
  ASM_REWRITE_TAC[AFFINE_ALT; IN_ELIM_THM] THEN
  REWRITE_TAC[dist; NORM_EQ_SQUARE; NORM_POS_LE; VECTOR_ARITH
   `((&1 - u) % x + u % y) - a:real^N = (&1 - u) % (x - a) + u % (y - a)`] THEN
  REWRITE_TAC[NORM_POW_2; DOT_LMUL; DOT_RMUL; VECTOR_ARITH
   `(x + y) dot (x + y):real^N = (x dot x + y dot y) + &2 * x dot y`] THEN
  SIMP_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Some convenient lemmas about common affine combinations.                  *)
(* ------------------------------------------------------------------------- *)

let IN_AFFINE_ADD_MUL = prove
 (`!s a x:real^N d. affine s /\ a IN s /\ (a + x) IN s ==> (a + d % x) IN s`,
  REWRITE_TAC[affine] THEN REPEAT STRIP_TAC THEN
  SUBST1_TAC(VECTOR_ARITH `a + d % x:real^N = (&1 - d) % a + d % (a + x)`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let IN_AFFINE_ADD_MUL_DIFF = prove
 (`!s a x y z:real^N.
        affine s /\ x IN s /\ y IN s /\ z IN s ==> (x + a % (y - z)) IN s`,
  REWRITE_TAC[affine] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH
   `x + a % (y - z):real^N =
    &1 / &2 % ((&1 - &2 * a) % x + (&2 * a) % y) +
    &1 / &2 % ((&1 + &2 * a) % x + (-- &2 * a) % z)`] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let IN_AFFINE_MUL_DIFF_ADD = prove
 (`!s a x y z:real^N.
        affine s /\ x IN s /\ y IN s /\ z IN s ==> a % (x - y) + z IN s`,
  ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
  SIMP_TAC[IN_AFFINE_ADD_MUL_DIFF]);;

let IN_AFFINE_SUB_MUL_DIFF = prove
 (`!s a x y z:real^N.
        affine s /\ x IN s /\ y IN s /\ z IN s ==> x - a % (y - z) IN s`,
  REWRITE_TAC[VECTOR_ARITH `x - a % (y - z):real^N = x + a % (z - y)`] THEN
  SIMP_TAC[IN_AFFINE_ADD_MUL_DIFF]);;

let AFFINE_DIFFS_SUBSPACE = prove
 (`!s:real^N->bool a.
        affine s /\ a IN s ==> subspace {x - a | x IN s}`,
  REWRITE_TAC[subspace; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[VECTOR_ARITH `vec 0:real^N = x - a <=> x = a`;
              VECTOR_ARITH `x - a + y - a:real^N = z - a <=>
                            z = (a + &1 % (x - a)) + &1 % (y - a)`;
              VECTOR_ARITH `c % (x - a):real^N = y - a <=>
                            y = a + c % (x - a)`] THEN
  MESON_TAC[IN_AFFINE_ADD_MUL_DIFF]);;

(* ------------------------------------------------------------------------- *)
(* Explicit formulations for affine combinations.                            *)
(* ------------------------------------------------------------------------- *)

let AFFINE_VSUM = prove
 (`!s k u x:A->real^N.
        FINITE k /\ affine s /\ sum k u = &1 /\ (!i. i IN k ==> x i IN s)
        ==> vsum k (\i. u i % x i) IN s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
    ASM_CASES_TAC `k:A->bool = {}` THEN ASM_REWRITE_TAC[SUM_CLAUSES] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`] AFFINE_DIFFS_SUBSPACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{x - a:real^N | x IN s}`;
                 `(\i. u i % (x i - a)):A->real^N`;
                 `k:A->bool`] SUBSPACE_VSUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBSPACE_MUL THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_SIMP_TAC[VSUM_SUB; IN_ELIM_THM; VECTOR_SUB_LDISTRIB; VSUM_RMUL] THEN
    REWRITE_TAC[VECTOR_ARITH `x - &1 % a:real^N = y - a <=> x = y`] THEN
    ASM_MESON_TAC[]]);;

let AFFINE_VSUM_STRONG = prove
 (`!s k u x:A->real^N.
        affine s /\
        sum k u = &1 /\
        (!i. i IN k ==> u i = &0 \/ x i IN s)
        ==> vsum k (\i. u i % x i) IN s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum k (\i. u i % (x:A->real^N) i) =
    vsum {i | i IN k /\ ~(u i = &0)} (\i. u i % x i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    SET_TAC[];
    MATCH_MP_TAC AFFINE_VSUM THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUM_DEGENERATE; REAL_ARITH `~(&1 = &0)`];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN ASM SET_TAC[];
      ASM SET_TAC[]]]);;

let AFFINE_INDEXED = prove
 (`!s:real^N->bool.
        affine s <=>
            !k u x. (!i:num. 1 <= i /\ i <= k ==> x(i) IN s) /\
                    (sum (1..k) u = &1)
                    ==> vsum (1..k) (\i. u(i) % x(i)) IN s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC AFFINE_VSUM THEN
    ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG];
    DISCH_TAC THEN REWRITE_TAC[affine] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
    DISCH_THEN(MP_TAC o SPEC `\n. if n = 1 then u else v:real`) THEN
    DISCH_THEN(MP_TAC o SPEC `\n. if n = 1 then x else y:real^N`) THEN
    REWRITE_TAC[num_CONV `2`; SUM_CLAUSES_NUMSEG; VSUM_CLAUSES_NUMSEG;
      NUMSEG_SING; VSUM_SING; SUM_SING] THEN REWRITE_TAC[ARITH] THEN
    ASM_MESON_TAC[]]);;

let AFFINE_HULL_INDEXED = prove
 (`!s. affine hull s =
        {y:real^N | ?k u x. (!i. 1 <= i /\ i <= k ==> x i IN s) /\
                            (sum (1..k) u = &1) /\
                            (vsum (1..k) (\i. u i % x i) = y)}`,
  GEN_TAC THEN MATCH_MP_TAC HULL_UNIQUE THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`1`; `\i:num. &1`; `\i:num. x:real^N`] THEN
    ASM_SIMP_TAC[FINITE_RULES; IN_SING; SUM_SING; VECTOR_MUL_LID; VSUM_SING;
                 REAL_POS; NUMSEG_SING];
    ALL_TAC;
    REWRITE_TAC[AFFINE_INDEXED; SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MESON_TAC[]] THEN
  REWRITE_TAC[affine; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`k1:num`; `u1:num->real`; `x1:num->real^N`;
    `k2:num`; `u2:num->real`; `x2:num->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `k1 + k2:num` THEN
  EXISTS_TAC `\i:num. if i <= k1 then u * u1(i) else v * u2(i - k1):real` THEN
  EXISTS_TAC `\i:num. if i <= k1 then x1(i) else x2(i - k1):real^N` THEN
  ASM_SIMP_TAC[NUMSEG_ADD_SPLIT; ARITH_RULE `1 <= x + 1 /\ x < x + 1`;
   IN_NUMSEG; SUM_UNION; VSUM_UNION; FINITE_NUMSEG; DISJOINT_NUMSEG;
   ARITH_RULE `k1 + 1 <= i ==> ~(i <= k1)`] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] NUMSEG_OFFSET_IMAGE] THEN
  ASM_SIMP_TAC[SUM_IMAGE; VSUM_IMAGE; EQ_ADD_LCANCEL; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[o_DEF; ADD_SUB2; SUM_LMUL; VSUM_LMUL; GSYM VECTOR_MUL_ASSOC;
               FINITE_NUMSEG; REAL_MUL_RID] THEN
  ASM_MESON_TAC[REAL_LE_MUL; ARITH_RULE
    `i <= k1 + k2 /\ ~(i <= k1) ==> 1 <= i - k1 /\ i - k1 <= k2`]);;

let AFFINE = prove
 (`!V:real^N->bool.
     affine V <=>
         !(s:real^N->bool) (u:real^N->real).
             FINITE s /\ ~(s = {}) /\ s SUBSET V /\ sum s u = &1
             ==> vsum s (\x. u x % x) IN V`,
  GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC AFFINE_VSUM THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[affine] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
    STRIP_TAC THEN ASM_CASES_TAC `x:real^N = y` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB;VECTOR_MUL_LID];ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `{x:real^N,y}`) THEN
    DISCH_THEN(MP_TAC o SPEC `\w. if w = x:real^N then u else v:real`) THEN
    ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_RULES; NUMSEG_SING;
                 VSUM_SING; SUM_SING;SUBSET;IN_INSERT;NOT_IN_EMPTY] THEN
    ASM SET_TAC[]]);;

let AFFINE_EXPLICIT = prove
 (`!s:real^N->bool.
        affine s <=>
            !t u. FINITE t /\ t SUBSET s /\ sum t u = &1
                  ==> vsum t (\x. u(x) % x) IN s`,
  GEN_TAC THEN REWRITE_TAC[AFFINE] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SUM_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let AFFINE_HULL_EXPLICIT = prove
 (`!(p:real^N -> bool).
        affine hull p =
         {y | ?s u. FINITE s /\ ~(s = {}) /\ s SUBSET p /\
                    sum s u = &1 /\ vsum s (\v. u v % v) = y}`,
  GEN_TAC THEN MATCH_MP_TAC HULL_UNIQUE THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET;IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`{x:real^N}`;`\v:real^N. &1:real`] THEN
    ASM_SIMP_TAC[FINITE_RULES;IN_SING;SUM_SING;VSUM_SING;VECTOR_MUL_LID] THEN
    SET_TAC[];
    REWRITE_TAC[affine;IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `(s UNION s'):real^N->bool` THEN
    EXISTS_TAC
      `\a:real^N. (\b:real^N.if (b IN s) then (u * (u' b)) else &0) a +
                  (\b:real^N.if (b IN s') then v * (u'' b) else &0) a` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[FINITE_UNION];
      ASM SET_TAC[];
      ASM_REWRITE_TAC[UNION_SUBSET];
      ASM_SIMP_TAC[REWRITE_RULE[REAL_ARITH `a + b = c + d <=> c = a + b - d`]
                   SUM_INCL_EXCL; GSYM SUM_RESTRICT_SET;
                   SET_RULE `{a | a IN (s:A->bool) /\ a IN s'} = s INTER s'`;
                   SUM_ADD;SUM_LMUL;REAL_MUL_RID;
                   FINITE_INTER;INTER_IDEMPOT] THEN
    ASM_REWRITE_TAC[SET_RULE `(a INTER b) INTER a = a INTER b`;
                    SET_RULE `(a INTER b) INTER b = a INTER b`;
                    REAL_ARITH `(a + b) + (c + d) - (e + b) = (a + d) + c - e`;
                    REAL_ARITH `a + b - c = a <=> b = c`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[INTER_COMM];
    ASM_SIMP_TAC[REWRITE_RULE
                  [VECTOR_ARITH `(a:real^N) + b = c + d <=> c = a + b - d`]
                  VSUM_INCL_EXCL;GSYM VSUM_RESTRICT_SET;
                 SET_RULE `{a | a IN (s:A->bool) /\ a IN s'} = s INTER s'`;
                 VSUM_ADD;FINITE_INTER;INTER_IDEMPOT;VECTOR_ADD_RDISTRIB;
                 GSYM VECTOR_MUL_ASSOC;VSUM_LMUL;
                 MESON[] `(if P then a else b) % (x:real^N) =
                          (if P then a % x else b % x)`;
                 VECTOR_MUL_LZERO;GSYM VSUM_RESTRICT_SET] THEN
    ASM_REWRITE_TAC[SET_RULE `(a INTER b) INTER a = a INTER b`;
                    SET_RULE `(a INTER b) INTER b = a INTER b`;
                    VECTOR_ARITH
                     `((a:real^N) + b) + (c + d) - (e + b) = (a + d) + c - e`;
                    VECTOR_ARITH `(a:real^N) + b - c = a <=> b = c`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[INTER_COMM]];
    ASM_CASES_TAC `(p:real^N->bool) = {}` THENL
      [FIRST_X_ASSUM SUBST_ALL_TAC THEN
       REWRITE_TAC[SUBSET_EMPTY;EMPTY_SUBSET] THEN ASM SET_TAC[];
       ALL_TAC] THEN
    REWRITE_TAC[AFFINE; SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    ASM SET_TAC[]]);;

let AFFINE_HULL_EXPLICIT_ALT = prove
 (`!(p:real^N -> bool).
        affine hull p =
         {y | ?s u. FINITE s /\ s SUBSET p /\
                    sum s u = &1 /\ vsum s (\v. u v % v) = y}`,
  GEN_TAC THEN REWRITE_TAC[AFFINE_HULL_EXPLICIT] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  SIMP_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH_EQ]);;

let AFFINE_HULL_FINITE = prove
 (`!s:real^N->bool.
        affine hull s = {y | ?u. sum s u = &1 /\ vsum s (\v. u v % v) = y}`,
  GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[AFFINE_HULL_EXPLICIT; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `f:real^N->real`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `\x:real^N. if x IN t then f x else &0` THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; VECTOR_MUL_LZERO] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET; GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`];
    X_GEN_TAC `f:real^N->real` THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH] THEN STRIP_TAC THEN
    EXISTS_TAC `support (+) (f:real^N->real) s` THEN
    EXISTS_TAC `f:real^N->real` THEN
    MP_TAC(ASSUME `sum s (f:real^N->real) = &1`) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [sum] THEN
    REWRITE_TAC[iterate] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[NEUTRAL_REAL_ADD; REAL_OF_NUM_EQ; ARITH] THEN
    DISCH_THEN(K ALL_TAC) THEN
    UNDISCH_TAC `sum s (f:real^N->real) = &1` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM SUM_SUPPORT] THEN
    ASM_CASES_TAC `support (+) (f:real^N->real) s = {}` THEN
    ASM_SIMP_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH] THEN
    DISCH_TAC THEN REWRITE_TAC[SUPPORT_SUBSET] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[SUPPORT_SUBSET] THEN
    REWRITE_TAC[support; IN_ELIM_THM; NEUTRAL_REAL_ADD] THEN
    MESON_TAC[VECTOR_MUL_LZERO]]);;

(* ------------------------------------------------------------------------- *)
(* Stepping theorems and hence small special cases.                          *)
(* ------------------------------------------------------------------------- *)

let AFFINE_HULL_EMPTY = prove
 (`affine hull {} = {}`,
  MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[SUBSET_REFL; AFFINE_EMPTY; EMPTY_SUBSET]);;

let AFFINE_HULL_EQ_EMPTY = prove
 (`!s. (affine hull s = {}) <=> (s = {})`,
  GEN_TAC THEN EQ_TAC THEN
  MESON_TAC[SUBSET_EMPTY; HULL_SUBSET; AFFINE_HULL_EMPTY]);;

let AFFINE_HULL_FINITE_STEP_GEN = prove
 (`!P:real^N->real->bool.
        ((?u. (!x. x IN {} ==> P x (u x)) /\
              sum {} u = w /\ vsum {} (\x. u(x) % x) = y) <=>
         w = &0 /\ y = vec 0) /\
        (FINITE(s:real^N->bool) /\
         (!y. a IN s /\ P a y ==> P a (y / &2)) /\
         (!x y. a IN s /\ P a x /\ P a y ==> P a (x + y))
         ==> ((?u. (!x. x IN (a INSERT s) ==> P x (u x)) /\
                   sum (a INSERT s) u = w /\
                   vsum (a INSERT s) (\x. u(x) % x) = y) <=>
              ?v u. P a v /\ (!x. x IN s ==> P x (u x)) /\
                    sum s u = w - v /\
                    vsum s (\x. u(x) % x) = y - v % a))`,
  GEN_TAC THEN SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  ASM_CASES_TAC `(a:real^N) IN s` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[SET_RULE `a IN s ==> a INSERT s = s`] THEN EQ_TAC THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
     [X_GEN_TAC `u:real^N->real` THEN STRIP_TAC THEN
      EXISTS_TAC `(u:real^N->real) a / &2` THEN
      EXISTS_TAC `\x:real^N. if x = a then u x / &2 else u x`;
      MAP_EVERY X_GEN_TAC [`v:real`; `u:real^N->real`] THEN
      STRIP_TAC THEN
      EXISTS_TAC `\x:real^N. if x = a then u x + v else u x`] THEN
    ASM_SIMP_TAC[] THEN (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC[VSUM_CASES; SUM_CASES] THEN
    ASM_SIMP_TAC[GSYM DELETE; SUM_DELETE; VSUM_DELETE] THEN
    ASM_SIMP_TAC[SET_RULE `a IN s ==> {x | x IN s /\ x = a} = {a}`] THEN
    REWRITE_TAC[SUM_SING; VSUM_SING] THEN
    (CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]);
    EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
     [X_GEN_TAC `u:real^N->real` THEN STRIP_TAC THEN
      EXISTS_TAC `(u:real^N->real) a` THEN
      EXISTS_TAC `u:real^N->real` THEN ASM_SIMP_TAC[IN_INSERT] THEN
      REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`v:real`; `u:real^N->real`] THEN
      STRIP_TAC THEN
      EXISTS_TAC `\x:real^N. if x = a then v:real else u x` THEN
      ASM_SIMP_TAC[IN_INSERT] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
      ASM_SIMP_TAC[VSUM_CASES; SUM_CASES] THEN
      ASM_SIMP_TAC[GSYM DELETE; SUM_DELETE; VSUM_DELETE] THEN
      ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> {x | x IN s /\ x = a} = {}`] THEN
      ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> s DELETE a = s`] THEN
      REWRITE_TAC[SUM_CLAUSES; VSUM_CLAUSES] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]]]);;

let AFFINE_HULL_FINITE_STEP = prove
 (`((?u. sum {} u = w /\ vsum {} (\x. u(x) % x) = y) <=>
    w = &0 /\ y = vec 0) /\
   (FINITE(s:real^N->bool)
    ==> ((?u. sum (a INSERT s) u = w /\
              vsum (a INSERT s) (\x. u(x) % x) = y) <=>
         ?v u.  sum s u = w - v /\
                vsum s (\x. u(x) % x) = y - v % a))`,
  MATCH_ACCEPT_TAC (REWRITE_RULE[]
   (ISPEC `\x:real^N y:real. T` AFFINE_HULL_FINITE_STEP_GEN)));;

let AFFINE_HULL_2 = prove
 (`!a b. affine hull {a,b} =
         {u % a + v % b | u + v = &1}`,
  SIMP_TAC[AFFINE_HULL_FINITE; FINITE_INSERT; FINITE_RULES] THEN
  SIMP_TAC[AFFINE_HULL_FINITE_STEP; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[REAL_ARITH `x - y = z:real <=> x = y + z`;
              VECTOR_ARITH `x - y = z:real^N <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN SET_TAC[]);;

let AFFINE_HULL_2_ALT = prove
 (`!a b. affine hull {a,b} = {a + u % (b - a) | u IN (:real)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFFINE_HULL_2] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV; ARITH_RULE `u + v = &1 <=> v = &1 - u`;
    FORALL_UNWIND_THM2; UNWIND_THM2] THEN
  CONJ_TAC THEN X_GEN_TAC `u:real` THEN EXISTS_TAC `&1 - u` THEN
  VECTOR_ARITH_TAC);;

let AFFINE_HULL_3 = prove
 (`affine hull {a,b,c} =
    { u % a + v % b + w % c | u + v + w = &1}`,
  SIMP_TAC[AFFINE_HULL_FINITE; FINITE_INSERT; FINITE_RULES] THEN
  SIMP_TAC[AFFINE_HULL_FINITE_STEP; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[REAL_ARITH `x - y = z:real <=> x = y + z`;
              VECTOR_ARITH `x - y = z:real^N <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some relations between affine hull and subspaces.                         *)
(* ------------------------------------------------------------------------- *)

let AFFINE_HULL_INSERT_SUBSET_SPAN = prove
 (`!a:real^N s.
     affine hull (a INSERT s) SUBSET {a + v | v | v IN span {x - a | x IN s}}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [SUBSET] THEN
  REWRITE_TAC[AFFINE_HULL_EXPLICIT; SPAN_EXPLICIT; IN_ELIM_THM] THEN
  REWRITE_TAC[SIMPLE_IMAGE; CONJ_ASSOC; FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[MESON[]
   `(?s u. (?t. P t /\ s = f t) /\ Q s u) <=>
    (?t u. P t /\ Q (f t) u)`] THEN
  REWRITE_TAC[MESON[]
   `(?v. (?s u. P s /\ f s u = v) /\ (x = g a v)) <=>
    (?s u. ~(P s ==> ~(g a (f s u) = x)))`] THEN
  SIMP_TAC[VSUM_IMAGE; VECTOR_ARITH `x - a:real^N = y - a <=> x = y`] THEN
  REWRITE_TAC[o_DEF] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC
   [`t DELETE (a:real^N)`; `\x. (u:real^N->real)(x + a)`] THEN
  ASM_SIMP_TAC[FINITE_DELETE; VECTOR_SUB_ADD; SET_RULE
   `t SUBSET (a INSERT s) ==> t DELETE a SUBSET s`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `a + vsum t (\x. u x % (x - a)):real^N` THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN SET_TAC[];
    ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; FINITE_DELETE; VSUM_SUB] THEN
    ASM_REWRITE_TAC[VSUM_RMUL] THEN
    REWRITE_TAC[VECTOR_ARITH `a + x - &1 % a:real^N = x`]]);;

let AFFINE_HULL_INSERT_SPAN = prove
 (`!a:real^N s.
        ~(a IN s)
        ==> affine hull (a INSERT s) =
            {a + v | v | v IN span {x - a | x IN s}}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[AFFINE_HULL_INSERT_SUBSET_SPAN] THEN REWRITE_TAC[SUBSET] THEN
  REWRITE_TAC[AFFINE_HULL_EXPLICIT; SPAN_EXPLICIT; IN_ELIM_THM] THEN
  REWRITE_TAC[SIMPLE_IMAGE; CONJ_ASSOC; FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[MESON[]
   `(?s u. (?t. P t /\ s = f t) /\ Q s u) <=>
    (?t u. P t /\ Q (f t) u)`] THEN
  REWRITE_TAC[MESON[]
   `(?v. (?s u. P s /\ f s u = v) /\ (x = g a v)) <=>
    (?s u. ~(P s ==> ~(g a (f s u) = x)))`] THEN
  SIMP_TAC[VSUM_IMAGE; VECTOR_ARITH `x - a:real^N = y - a <=> x = y`] THEN
  REWRITE_TAC[o_DEF] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC
   [`(a:real^N) INSERT t`;
    `\x. if x = a then &1 - sum t (\x. u(x - a))
         else (u:real^N->real)(x - a)`] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES] THEN
  ASM_CASES_TAC `(a:real^N) IN t` THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_INSERT; NOT_INSERT_EMPTY;
               SET_RULE `s SUBSET t ==> (a INSERT s) SUBSET (a INSERT t)`] THEN
  SUBGOAL_THEN `!x:real^N. x IN t ==> ~(x = a)` MP_TAC THENL
   [ASM SET_TAC[]; SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC)] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; FINITE_DELETE; VSUM_SUB] THEN
  ASM_REWRITE_TAC[VSUM_RMUL] THEN VECTOR_ARITH_TAC);;

let AFFINE_HULL_SPAN = prove
 (`!a:real^N s.
        a IN s
        ==> (affine hull s =
             {a + v | v | v IN span {x - a | x | x IN (s DELETE a)}})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `s DELETE (a:real^N)`]
    AFFINE_HULL_INSERT_SPAN) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let DIFFS_AFFINE_HULL_SPAN = prove
 (`!a:real^N s.
        a IN s ==> {x - a | x IN affine hull s} = span {x - a | x IN s}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFFINE_HULL_SPAN) THEN
  REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF; VECTOR_ADD_SUB; IMAGE_ID] THEN
  SIMP_TAC[IMAGE_DELETE_INJ;
           VECTOR_ARITH `x - a:real^N = y - a <=> x = y`] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; SPAN_DELETE_0]);;

let AFFINE_HULL_SING = prove
 (`!a. affine hull {a} = {a}`,
  SIMP_TAC[AFFINE_HULL_INSERT_SPAN; NOT_IN_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{f x | x | F} = {}`; SPAN_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{f x | x IN {a}} = {f a}`; VECTOR_ADD_RID]);;

let AFFINE_HULL_EQ_SING = prove
 (`!s a:real^N. affine hull s = {a} <=> s = {a}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[AFFINE_HULL_EMPTY] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[AFFINE_HULL_SING] THEN
  MATCH_MP_TAC(SET_RULE `~(s = {}) /\ s SUBSET {a} ==> s = {a}`) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[HULL_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Convexity.                                                                *)
(* ------------------------------------------------------------------------- *)

let convex = new_definition
  `convex s <=>
        !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
                  ==> (u % x + v % y) IN s`;;

let CONVEX_ALT = prove
 (`convex s <=> !x y u. x IN s /\ y IN s /\ &0 <= u /\ u <= &1
                        ==> ((&1 - u) % x + u % y) IN s`,
  REWRITE_TAC[convex] THEN
  MESON_TAC[REAL_ARITH `&0 <= u /\ &0 <= v /\ (u + v = &1)
                        ==> v <= &1 /\ (u = &1 - v)`;
            REAL_ARITH `u <= &1 ==> &0 <= &1 - u /\ ((&1 - u) + u = &1)`]);;

let IN_CONVEX_SET = prove
 (`!s a b u.
        convex s /\ a IN s /\ b IN s /\ &0 <= u /\ u <= &1
        ==> ((&1 - u) % a + u % b) IN s`,
  MESON_TAC[CONVEX_ALT]);;

let MIDPOINT_IN_CONVEX = prove
 (`!s x y:real^N.
        convex s /\ x IN s /\ y IN s ==> midpoint(x,y) IN s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`; `y:real^N`; `&1 / &2`]
        IN_CONVEX_SET) THEN
  ASM_REWRITE_TAC[midpoint] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC VECTOR_ARITH);;

let CONVEX_CONTAINS_SEGMENT = prove
 (`!s. convex s <=> !a b. a IN s /\ b IN s ==> segment[a,b] SUBSET s`,
  REWRITE_TAC[CONVEX_ALT; segment; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let CONVEX_CONTAINS_OPEN_SEGMENT = prove
 (`!s. convex s <=> !a b. a IN s /\ b IN s ==> segment(a,b) SUBSET s`,
  ONCE_REWRITE_TAC[segment] THEN REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
  SET_TAC[]);;

let CONVEX_CONTAINS_SEGMENT_EQ = prove
 (`!s:real^N->bool.
        convex s <=> !a b. segment[a,b] SUBSET s <=> a IN s /\ b IN s`,
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT; SUBSET] THEN
  MESON_TAC[ENDS_IN_SEGMENT]);;

let CONVEX_CONTAINS_SEGMENT_IMP = prove
 (`!s a b. convex s ==> (segment[a,b] SUBSET s <=> a IN s /\ b IN s)`,
  SIMP_TAC[CONVEX_CONTAINS_SEGMENT_EQ]);;

let CONVEX_EMPTY = prove
 (`convex {}`,
  REWRITE_TAC[convex; NOT_IN_EMPTY]);;

let CONVEX_SING = prove
 (`!a. convex {a}`,
  SIMP_TAC[convex; IN_SING; GSYM VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID]);;

let CONVEX_UNIV = prove
 (`convex(UNIV:real^N->bool)`,
  REWRITE_TAC[convex; IN_UNIV]);;

let CONVEX_INTERS = prove
 (`(!s. s IN f ==> convex s) ==> convex(INTERS f)`,
  REWRITE_TAC[convex; IN_INTERS] THEN MESON_TAC[]);;

let CONVEX_INTER = prove
 (`!s t. convex s /\ convex t ==> convex(s INTER t)`,
  REWRITE_TAC[convex; IN_INTER] THEN MESON_TAC[]);;

let CONVEX_HALFSPACE_LE = prove
 (`!a b. convex {x | a dot x <= b}`,
  REWRITE_TAC[convex; IN_ELIM_THM; DOT_RADD; DOT_RMUL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(u + v) * b` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_ADD_RDISTRIB; REAL_LE_ADD2; REAL_LE_LMUL];
    ASM_MESON_TAC[REAL_MUL_LID; REAL_LE_REFL]]);;

let CONVEX_HALFSPACE_COMPONENT_LE = prove
 (`!a k. convex {x:real^N | x$k <= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CONVEX_HALFSPACE_LE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CONVEX_HALFSPACE_GE = prove
 (`!a b. convex {x:real^N | a dot x >= b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x:real^N | a dot x >= b} = {x | --a dot x <= --b}`
   (fun th -> REWRITE_TAC[th; CONVEX_HALFSPACE_LE]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_LNEG] THEN REAL_ARITH_TAC);;

let CONVEX_HALFSPACE_COMPONENT_GE = prove
 (`!a k. convex {x:real^N | x$k >= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CONVEX_HALFSPACE_GE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CONVEX_HYPERPLANE = prove
 (`!a b. convex {x:real^N | a dot x = b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `{x:real^N | a dot x = b} = {x | a dot x <= b} INTER {x | a dot x >= b}`
   (fun th -> SIMP_TAC[th; CONVEX_INTER;
                       CONVEX_HALFSPACE_LE; CONVEX_HALFSPACE_GE]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CONVEX_STANDARD_HYPERPLANE = prove
 (`!k a. convex {x:real^N | x$k = a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CONVEX_HYPERPLANE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CONVEX_HALFSPACE_LT = prove
 (`!a b. convex {x | a dot x < b}`,
  REWRITE_TAC[convex; IN_ELIM_THM; DOT_RADD; DOT_RMUL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN
  ASM_REWRITE_TAC[]);;

let CONVEX_HALFSPACE_COMPONENT_LT = prove
 (`!a k. convex {x:real^N | x$k < a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CONVEX_HALFSPACE_LT) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CONVEX_HALFSPACE_GT = prove
 (`!a b. convex {x | a dot x > b}`,
  REWRITE_TAC[REAL_ARITH `ax > b <=> --ax < --b`] THEN
  REWRITE_TAC[GSYM DOT_LNEG; CONVEX_HALFSPACE_LT]);;

let CONVEX_HALFSPACE_COMPONENT_GT = prove
 (`!a k. convex {x:real^N | x$k > a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CONVEX_HALFSPACE_GT) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CONVEX_POSITIVE_ORTHANT = prove
 (`convex {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                          ==> &0 <= x$i}`,
  SIMP_TAC[convex; IN_ELIM_THM; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           REAL_LE_MUL; REAL_LE_ADD]);;

let LIMPT_OF_CONVEX = prove
 (`!s x:real^N.
        convex s /\ x IN s ==> (x limit_point_of s <=> ~(s = {x}))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s = {x:real^N}` THEN ASM_REWRITE_TAC[LIMPT_SING] THEN
  SUBGOAL_THEN `?y:real^N. y IN s /\ ~(y = x)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `u = min (&1 / &2) (e / &2 / norm(y - x:real^N))` THEN
  SUBGOAL_THEN `&0 < u /\ u < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  EXISTS_TAC `(&1 - u) % x + u % y:real^N` THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; VECTOR_ARITH
     `(&1 - u) % x + u % y:real^N = x <=> u % (y - x) = vec 0`] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[dist; NORM_MUL; VECTOR_ARITH
     `((&1 - u) % x + u % y) - x:real^N = u % (y - x)`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < u ==> abs u = u`] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= e / &2 /\ &0 < e ==> x < e`) THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

let TRIVIAL_LIMIT_WITHIN_CONVEX = prove
 (`!s x:real^N.
        convex s /\ x IN s ==> (trivial_limit(at x within s) <=> s = {x})`,
  SIMP_TAC[TRIVIAL_LIMIT_WITHIN; LIMPT_OF_CONVEX]);;

(* ------------------------------------------------------------------------- *)
(* Some invariance theorems for convex sets.                                 *)
(* ------------------------------------------------------------------------- *)

let CONVEX_TRANSLATION_EQ = prove
 (`!a:real^N s. convex (IMAGE (\x. a + x) s) <=> convex s`,
  REWRITE_TAC[CONVEX_ALT; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE; UNWIND_THM1; VECTOR_ARITH
   `(&1 - u) % (a + x) + u % (a + y) = a + z <=> (&1 - u) % x + u % y = z`]);;

add_translation_invariants [CONVEX_TRANSLATION_EQ];;

let CONVEX_TRANSLATION = prove
 (`!s a:real^N. convex s ==> convex (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[CONVEX_TRANSLATION_EQ]);;

let CONVEX_LINEAR_IMAGE = prove
 (`!f s. convex s /\ linear f ==> convex(IMAGE f s)`,
  REWRITE_TAC[convex; FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IN_IMAGE; linear] THEN MESON_TAC[]);;

let CONVEX_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (convex (IMAGE f s) <=> convex s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE CONVEX_LINEAR_IMAGE));;

add_linear_invariants [CONVEX_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Explicit expressions for convexity in terms of arbitrary sums.            *)
(* ------------------------------------------------------------------------- *)

let CONVEX_VSUM = prove
 (`!s k u x:A->real^N.
        FINITE k /\ convex s /\ sum k u = &1 /\
        (!i. i IN k ==> &0 <= u i /\ x i IN s)
        ==> vsum k (\i. u i % x i) IN s`,
  GEN_TAC THEN ASM_CASES_TAC `convex(s:real^N->bool)` THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FORALL_IN_INSERT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MAP_EVERY X_GEN_TAC [`i:A`; `k:A->bool`] THEN
  GEN_REWRITE_TAC (BINOP_CONV o DEPTH_CONV) [RIGHT_IMP_FORALL_THM] THEN
  REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:A->real`; `x:A->real^N`] THEN
  ASM_CASES_TAC `(u:A->real) i = &1` THENL
   [ASM_REWRITE_TAC[REAL_ARITH `&1 + a  = &1 <=> a = &0`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `vsum k (\i:A. u i % x(i):real^N) = vec 0`
     (fun th -> ASM_SIMP_TAC[th; VECTOR_ADD_RID; VECTOR_MUL_LID]) THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    REPEAT STRIP_TAC THEN DISJ1_TAC THEN
    ASM_MESON_TAC[SUM_POS_EQ_0];
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\j:A. u(j) / (&1 - u(i))`) THEN
    ASM_REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[SUM_LMUL; VSUM_LMUL; GSYM VECTOR_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    SUBGOAL_THEN `&0 < &1 - u(i:A)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUM_POS_LE; REAL_ADD_SYM; REAL_ARITH
       `&0 <= a /\ &0 <= b /\ b + a = &1 /\ ~(a = &1) ==> &0 < &1 - a`];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_MUL_LID; REAL_EQ_SUB_LADD] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`vsum k (\j. (u j / (&1 - u(i:A))) % x(j) :real^N)`;
      `x(i:A):real^N`; `&1 - u(i:A)`; `u(i:A):real`]) THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM VECTOR_MUL_ASSOC; VSUM_LMUL] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; VSUM_LMUL] THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; REAL_ARITH_TAC] THEN
    ASM_MESON_TAC[REAL_ADD_SYM]]);;

let CONVEX_VSUM_STRONG = prove
 (`!s k u x:A->real^N.
        convex s /\
        sum k u = &1 /\
        (!i. i IN k ==> &0 <= u i /\ (u i = &0 \/ x i IN s))
        ==> vsum k (\i. u i % x i) IN s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum k (\i. u i % (x:A->real^N) i) =
    vsum {i | i IN k /\ ~(u i = &0)} (\i. u i % x i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    SET_TAC[];
    MATCH_MP_TAC CONVEX_VSUM THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUM_DEGENERATE; REAL_ARITH `~(&1 = &0)`];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN ASM SET_TAC[];
      ASM SET_TAC[]]]);;

let CONVEX_INDEXED = prove
 (`!s:real^N->bool.
        convex s <=>
            !k u x. (!i:num. 1 <= i /\ i <= k ==> &0 <= u(i) /\ x(i) IN s) /\
                    (sum (1..k) u = &1)
                    ==> vsum (1..k) (\i. u(i) % x(i)) IN s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_VSUM THEN
    ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG];
    DISCH_TAC THEN REWRITE_TAC[convex] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
    DISCH_THEN(MP_TAC o SPEC `\n. if n = 1 then u else v:real`) THEN
    DISCH_THEN(MP_TAC o SPEC `\n. if n = 1 then x else y:real^N`) THEN
    REWRITE_TAC[num_CONV `2`; SUM_CLAUSES_NUMSEG; VSUM_CLAUSES_NUMSEG;
      NUMSEG_SING; VSUM_SING; SUM_SING] THEN REWRITE_TAC[ARITH] THEN
    ASM_MESON_TAC[]]);;

let CONVEX_EXPLICIT = prove
 (`!s:real^N->bool.
        convex s <=>
        !t u. FINITE t /\ t SUBSET s /\ (!x. x IN t ==> &0 <= u x) /\
              sum t u = &1
              ==> vsum t (\x. u(x) % x) IN s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_VSUM THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN REWRITE_TAC[convex] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
    ASM_CASES_TAC `x:real^N = y` THENL
     [ASM_SIMP_TAC[GSYM VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID]; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `{x:real^N,y}`) THEN
    DISCH_THEN(MP_TAC o SPEC `\z:real^N. if z = x then u else v:real`) THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_RULES; SUM_CLAUSES; VSUM_CLAUSES;
                 NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; REAL_ADD_RID; SUBSET] THEN
    REWRITE_TAC[VECTOR_ADD_RID] THEN ASM_MESON_TAC[]]);;

let CONVEX = prove
 (`!V:real^N->bool.
     convex V <=>
         !(s:real^N->bool) (u:real^N->real).
             FINITE s /\ ~(s = {}) /\ s SUBSET V /\
             (!x. x IN s ==> &0 <= u x) /\ sum s u = &1
             ==> vsum s (\x. u x % x) IN V`,
  GEN_TAC THEN REWRITE_TAC[CONVEX_EXPLICIT] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SUM_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let CONVEX_FINITE = prove
 (`!s:real^N->bool.
        FINITE s
        ==> (convex s <=>
                !u. (!x. x IN s ==> &0 <= u x) /\
                    sum s u = &1
                    ==> vsum s (\x. u(x) % x) IN s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_EXPLICIT] THEN
  EQ_TAC THENL [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\x:real^N. if x IN t then u x else &0`) THEN
  ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  ASM_SIMP_TAC[VECTOR_MUL_LZERO; REAL_LE_REFL; GSYM VSUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[COND_ID; SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`]);;

let AFFINE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        affine s /\ affine t ==> affine(s PCROSS t)`,
  REWRITE_TAC[affine; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC[FORALL_IN_PCROSS; GSYM PASTECART_CMUL; PASTECART_ADD] THEN
  SIMP_TAC[PASTECART_IN_PCROSS]);;

let AFFINE_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        affine(s PCROSS t) <=> s = {} \/ t = {} \/ affine s /\ affine t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; AFFINE_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; AFFINE_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[AFFINE_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`] AFFINE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`] AFFINE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let CONVEX_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        convex s /\ convex t ==> convex(s PCROSS t)`,
  REWRITE_TAC[convex; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC[FORALL_IN_PCROSS; GSYM PASTECART_CMUL; PASTECART_ADD] THEN
  SIMP_TAC[PASTECART_IN_PCROSS]);;

let CONVEX_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        convex(s PCROSS t) <=> s = {} \/ t = {} \/ convex s /\ convex t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CONVEX_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CONVEX_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[CONVEX_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`] CONVEX_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`] CONVEX_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Conic sets and conic hull.                                                *)
(* ------------------------------------------------------------------------- *)

let conic = new_definition
  `conic s <=> !x c. x IN s /\ &0 <= c ==> (c % x) IN s`;;

let SUBSPACE_IMP_CONIC = prove
 (`!s. subspace s ==> conic s`,
  SIMP_TAC[subspace; conic]);;

let CONIC_EMPTY = prove
 (`conic {}`,
  REWRITE_TAC[conic; NOT_IN_EMPTY]);;

let CONIC_UNIV = prove
 (`conic (UNIV:real^N->bool)`,
  REWRITE_TAC[conic; IN_UNIV]);;

let CONIC_INTERS = prove
 (`(!s. s IN f ==> conic s) ==> conic(INTERS f)`,
  REWRITE_TAC[conic; IN_INTERS] THEN MESON_TAC[]);;

let CONIC_LINEAR_IMAGE = prove
 (`!f s. conic s /\ linear f ==> conic(IMAGE f s)`,
  REWRITE_TAC[conic; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[LINEAR_CMUL]);;

let CONIC_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (conic (IMAGE f s) <=> conic s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE CONIC_LINEAR_IMAGE));;

add_linear_invariants [CONIC_LINEAR_IMAGE_EQ];;

let CONIC_CONIC_HULL = prove
 (`!s. conic(conic hull s)`,
  SIMP_TAC[P_HULL; CONIC_INTERS]);;

let CONIC_HULL_EQ = prove
 (`!s. (conic hull s = s) <=> conic s`,
  SIMP_TAC[HULL_EQ; CONIC_INTERS]);;

let CONIC_NEGATIONS = prove
 (`!s. conic s ==> conic (IMAGE (--) s)`,
  REWRITE_TAC[conic; RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE; VECTOR_MUL_RNEG] THEN MESON_TAC[]);;

let CONIC_SPAN = prove
 (`!s. conic(span s)`,
  SIMP_TAC[SUBSPACE_IMP_CONIC; SUBSPACE_SPAN]);;

let CONIC_HULL_EXPLICIT = prove
 (`!s:real^N->bool. conic hull s = {c % x | &0 <= c /\ x IN s}`,
  GEN_TAC THEN MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[conic; SUBSET; RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`&1`; `x:real^N`] THEN
    ASM_SIMP_TAC[REAL_POS; VECTOR_MUL_LID];
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN MESON_TAC[REAL_LE_MUL];
    MESON_TAC[]]);;

let CONIC_HULL_LINEAR_IMAGE = prove
 (`!f s. linear f ==> conic hull (IMAGE f s) = IMAGE f (conic hull s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONIC_HULL_EXPLICIT] THEN
  REWRITE_TAC[SET_RULE `IMAGE f {c % x | P c x} = {f(c % x) | P c x}`] THEN
  REWRITE_TAC[SET_RULE `{c % x | &0 <= c /\ x IN IMAGE f s} =
                        {c % f(x) | &0 <= c /\ x IN s}`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]));;

add_linear_invariants [CONIC_HULL_LINEAR_IMAGE];;

let CONVEX_CONIC_HULL = prove
 (`!s:real^N->bool. convex s ==> convex (conic hull s)`,
  REWRITE_TAC[CONIC_HULL_EXPLICIT] THEN
  REWRITE_TAC[CONVEX_ALT; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_THM; IMP_IMP] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `y:real^N`] THEN STRIP_TAC THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_CASES_TAC `(&1 - u) * c = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
    ASM_MESON_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 - u) * c + u * d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_ADD THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(&1 - u) * c + u * d:real` THEN
  EXISTS_TAC `((&1 - u) * c) / ((&1 - u) * c + u * d) % x +
              (u * d) / ((&1 - u) * c + u * d) % y:real^N` THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_SUB_LE] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `&0 < u + v ==> u / (u + v) = &1 - (v / (u + v))`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_LE_MUL; REAL_MUL_LID; REAL_LE_ADDL;
               REAL_SUB_LE]);;

let CONIC_HALFSPACE_LE = prove
 (`!a. conic {x | a dot x <= &0}`,
  REWRITE_TAC[conic; IN_ELIM_THM; DOT_RMUL] THEN
  REWRITE_TAC[REAL_ARITH `a <= &0 <=> &0 <= --a`] THEN
  SIMP_TAC[GSYM REAL_MUL_RNEG; REAL_LE_MUL]);;

let CONIC_HALFSPACE_GE = prove
 (`!a. conic {x | a dot x >= &0}`,
  SIMP_TAC[conic; IN_ELIM_THM; DOT_RMUL; real_ge; REAL_LE_MUL]);;

let CONIC_HULL_EMPTY = prove
 (`conic hull {} = {}`,
  MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[SUBSET_REFL; CONIC_EMPTY; EMPTY_SUBSET]);;

let CONIC_CONTAINS_0 = prove
 (`!s:real^N->bool. conic s ==> (vec 0 IN s <=> ~(s = {}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [conic]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `&0`]) THEN
  ASM_REWRITE_TAC[REAL_POS; VECTOR_MUL_LZERO]);;

let CONIC_HULL_EQ_EMPTY = prove
 (`!s. (conic hull s = {}) <=> (s = {})`,
  GEN_TAC THEN EQ_TAC THEN
  MESON_TAC[SUBSET_EMPTY; HULL_SUBSET; CONIC_HULL_EMPTY]);;

let CONIC_SUMS = prove
 (`!s t. conic s /\ conic t ==> conic {x + y:real^N | x IN s /\ y IN t}`,
  REWRITE_TAC[conic; IN_ELIM_THM] THEN
  MESON_TAC[VECTOR_ADD_LDISTRIB]);;

let CONIC_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        conic s /\ conic t ==> conic(s PCROSS t)`,
  REWRITE_TAC[conic; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC[FORALL_IN_PCROSS; GSYM PASTECART_CMUL; PASTECART_ADD] THEN
  SIMP_TAC[PASTECART_IN_PCROSS]);;

let CONIC_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        conic(s PCROSS t) <=> s = {} \/ t = {} \/ conic s /\ conic t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CONIC_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CONIC_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[CONIC_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`] CONIC_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`] CONIC_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let CONIC_POSITIVE_ORTHANT = prove
 (`conic {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i}`,
  SIMP_TAC[conic; IN_ELIM_THM; REAL_LE_MUL; VECTOR_MUL_COMPONENT]);;

let SEPARATE_CLOSED_CONES = prove
 (`!c d:real^N->bool.
        conic c /\ closed c /\ conic d /\ closed d /\ c INTER d SUBSET {vec 0}
        ==> ?e. &0 < e /\
                !x y. x IN c /\ y IN d
                      ==> dist(x,y) >= e * max (norm x) (norm y)`,
  SUBGOAL_THEN
   `!c d:real^N->bool.
        conic c /\ closed c /\ conic d /\ closed d /\ c INTER d SUBSET {vec 0}
        ==> ?e. &0 < e /\
                !x y. x IN c /\ y IN d ==> dist(x,y)
                      >= e * norm x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[real_ge] THEN
    MP_TAC(ISPECL [`c INTER sphere(vec 0:real^N,&1)`; `d:real^N->bool`]
      SEPARATE_COMPACT_CLOSED) THEN
    ASM_SIMP_TAC[CLOSED_INTER_COMPACT; COMPACT_SPHERE] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `c INTER d SUBSET {a} ==> ~(a IN s) ==> (c INTER s) INTER d = {}`)) THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
      REWRITE_TAC[IN_INTER; IN_SPHERE_0] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `x:real^N = vec 0` THEN
      ASM_REWRITE_TAC[DIST_POS_LE; REAL_MUL_RZERO; NORM_0] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`inv(norm x) % x:real^N`; `inv(norm(x:real^N)) % y:real^N`]) THEN
      REWRITE_TAC[dist; NORM_MUL; GSYM VECTOR_SUB_LDISTRIB] THEN
      REWRITE_TAC[REAL_ARITH `abs x * a = a * abs x`] THEN
      REWRITE_TAC[REAL_ABS_INV; GSYM real_div; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; NORM_POS_LT] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; NORM_EQ_0] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[conic]) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; NORM_POS_LE]];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`c:real^N->bool`; `d:real^N->bool`] th) THEN
      MP_TAC(SPECL [`d:real^N->bool`; `c:real^N->bool`] th)) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; real_ge] THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    EXISTS_TAC `min d e:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `d * norm(y:real^N)` THEN ONCE_REWRITE_TAC[DIST_SYM];
      EXISTS_TAC `e * norm(x:real^N)`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN NORM_ARITH_TAC]);;

let CONTINUOUS_ON_COMPACT_SURFACE_PROJECTION = prove
 (`!s:real^N->bool v d:real^N->real.
        compact s /\ s SUBSET (v DELETE (vec 0)) /\ conic v /\
        (!x k. x IN v DELETE (vec 0) ==> (&0 < k /\ (k % x) IN s <=> d x = k))
        ==> (\x. d x % x) continuous_on (v DELETE (vec 0))`,
  let lemma = prove
   (`!s:real^N->real^N p srf:real^N->bool pnc.
          compact srf /\ srf SUBSET pnc /\
          IMAGE s pnc SUBSET srf /\ (!x. x IN srf ==> s x = x) /\
          p continuous_on pnc /\
          (!x. x IN pnc ==> s(p x) = s x /\ p(s x) = p x)
          ==> s continuous_on pnc`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `(s:real^N->real^N) o (p:real^N->real^N)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (p:real^N->real^N) pnc = IMAGE p srf` SUBST1_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_INVERSE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]]]) in
  REWRITE_TAC[conic; IN_DELETE; SUBSET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
  MAP_EVERY EXISTS_TAC [`\x:real^N. inv(norm x) % x`; `s:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN SIMP_TAC[o_DEF; CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
    SIMP_TAC[IN_DELETE; NORM_EQ_0; SIMP_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM];
    REWRITE_TAC[IN_UNIV; IN_DELETE]] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `&1`]) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; REAL_LT_01; IN_DELETE] THEN
    ASM_MESON_TAC[VECTOR_MUL_LID; SUBSET; IN_DELETE];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL
     [`inv(norm x) % x:real^N`; `norm x * (d:real^N->real) x`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `(d:real^N->real) x`]) THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; NORM_POS_LE; REAL_LT_MUL; NORM_POS_LT] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; NORM_EQ_0; REAL_FIELD
     `~(n = &0) ==> (n * d) * inv n = d`];
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `(d:real^N->real) x`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[NORM_MUL; VECTOR_MUL_ASSOC; REAL_INV_MUL] THEN
    ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < x ==> (inv(x) * y) * x = y`]]);;

(* ------------------------------------------------------------------------- *)
(* Affine dependence and consequential theorems (from Lars Schewe).          *)
(* ------------------------------------------------------------------------- *)

let affine_dependent = new_definition
 `affine_dependent (s:real^N -> bool) <=>
        ?x. x IN s /\ x IN (affine hull (s DELETE x))`;;

let AFFINE_DEPENDENT_EXPLICIT = prove
 (`!p. affine_dependent (p:real^N -> bool) <=>
            (?s u. FINITE s /\ s SUBSET p /\
                   sum s u = &0 /\
                   (?v. v IN s /\ ~(u v = &0)) /\
                   vsum s (\v. u v % v) = (vec 0):real^N)`,
  X_GEN_TAC `p:real^N->bool` THEN EQ_TAC THENL
   [REWRITE_TAC[affine_dependent;AFFINE_HULL_EXPLICIT;
                IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `(x:real^N) INSERT s` THEN
    EXISTS_TAC `\v:real^N.if v = x then -- &1 else u v` THEN
      ASM_SIMP_TAC[FINITE_INSERT;SUM_CLAUSES;VSUM_CLAUSES;INSERT_SUBSET] THEN
      REPEAT CONJ_TAC THENL
      [ASM SET_TAC[];
       COND_CASES_TAC THENL [ASM SET_TAC[];ALL_TAC] THEN
         ASM_SIMP_TAC[SUM_CASES; SUM_CLAUSES; SET_RULE
          `~((x:real^N) IN s) ==> {v | v IN s /\ v = x} = {} /\
                                  {v | v IN s /\ ~(v = x)} = s`] THEN
         REAL_ARITH_TAC;
       SET_TAC[REAL_ARITH `~(-- &1 = &0)`];
       MP_TAC (SET_RULE `s SUBSET p DELETE (x:real^N) ==> ~(x IN s)`) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_TAC THEN
       ASM_SIMP_TAC[VECTOR_ARITH
        `(-- &1 % (x:real^N)) + a = vec 0 <=> a = x`] THEN
       MATCH_MP_TAC EQ_TRANS THEN
       EXISTS_TAC `vsum s (\v:real^N. u v % v)` THEN
       CONJ_TAC THENL [
       MATCH_MP_TAC VSUM_EQ THEN
         ASM_SIMP_TAC[] THEN
         ASM SET_TAC[];
       ASM_REWRITE_TAC[]]];
       ALL_TAC] THEN
    REWRITE_TAC[affine_dependent;AFFINE_HULL_EXPLICIT;IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `v:real^N` THEN
    CONJ_TAC THENL [ASM SET_TAC[];ALL_TAC] THEN
    EXISTS_TAC `s DELETE (v:real^N)` THEN
    EXISTS_TAC `\x:real^N. -- (&1 / (u v)) * u x` THEN
    ASM_SIMP_TAC[FINITE_DELETE;SUM_DELETE;VSUM_DELETE_CASES] THEN
    ASM_SIMP_TAC[SUM_LMUL;GSYM VECTOR_MUL_ASSOC;VSUM_LMUL;
            VECTOR_MUL_RZERO;VECTOR_ARITH `vec 0 - -- a % x = a % x:real^N`;
            REAL_MUL_RZERO;REAL_ARITH `&0 - -- a * b = a * b`] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(x = &0) ==> &1 / x * x = &1`;
                 VECTOR_MUL_ASSOC;VECTOR_MUL_LID] THEN
    CONJ_TAC THENL [ALL_TAC;ASM SET_TAC[]] THEN
    ASM_SIMP_TAC[SET_RULE `v IN s ==> (s DELETE v = {} <=> s = {v})`] THEN
    ASM_CASES_TAC `s = {v:real^N}` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIND_ASSUM MP_TAC `sum {v:real^N} u = &0` THEN
    REWRITE_TAC[SUM_SING]
    THEN ASM_REWRITE_TAC[]);;

let AFFINE_DEPENDENT_EXPLICIT_FINITE = prove
 (`!s. FINITE(s:real^N -> bool)
       ==> (affine_dependent s <=>
            ?u. sum s u = &0 /\
                (?v. v IN s /\ ~(u v = &0)) /\
                vsum s (\v. u v % v) = vec 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFFINE_DEPENDENT_EXPLICIT] THEN
  EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET_REFL]] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
   (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x:real^N. if x IN t then u(x) else &0` THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; VECTOR_MUL_LZERO] THEN
  ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET; GSYM VSUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`] THEN
  ASM SET_TAC[]);;

let AFFINE_DEPENDENT_TRANSLATION_EQ = prove
 (`!a s. affine_dependent (IMAGE (\x. a + x) s) <=> affine_dependent s`,
  REWRITE_TAC[affine_dependent] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [AFFINE_DEPENDENT_TRANSLATION_EQ];;

let AFFINE_DEPENDENT_TRANSLATION = prove
 (`!s a. affine_dependent s ==> affine_dependent (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[AFFINE_DEPENDENT_TRANSLATION_EQ]);;

let AFFINE_DEPENDENT_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (affine_dependent(IMAGE f s) <=> affine_dependent s)`,
  REWRITE_TAC[affine_dependent] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [AFFINE_DEPENDENT_LINEAR_IMAGE_EQ];;

let AFFINE_DEPENDENT_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        affine_dependent(s)
        ==> affine_dependent(IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[affine_dependent; EXISTS_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^M` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) s DELETE f a = IMAGE f (s DELETE a)`
   (fun t -> ASM_SIMP_TAC[FUN_IN_IMAGE; AFFINE_HULL_LINEAR_IMAGE; t]) THEN
  ASM SET_TAC[]);;

let AFFINE_DEPENDENT_MONO = prove
 (`!s t:real^N->bool. affine_dependent s /\ s SUBSET t ==> affine_dependent t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[affine_dependent] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:real^N` THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HULL_MONO o SPEC `x:real^N` o MATCH_MP
   (SET_RULE `!x. s SUBSET t ==> (s DELETE x) SUBSET (t DELETE x)`)) THEN
  ASM SET_TAC[]);;

let AFFINE_INDEPENDENT_EMPTY = prove
 (`~(affine_dependent {})`,
  REWRITE_TAC[affine_dependent; NOT_IN_EMPTY]);;

let AFFINE_INDEPENDENT_1 = prove
 (`!a:real^N. ~(affine_dependent {a})`,
  REWRITE_TAC[affine_dependent; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{a} DELETE a = {}`; AFFINE_HULL_EMPTY; NOT_IN_EMPTY]);;

let AFFINE_INDEPENDENT_2 = prove
 (`!a b:real^N. ~(affine_dependent {a,b})`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_REWRITE_TAC[INSERT_AC; AFFINE_INDEPENDENT_1];
    REWRITE_TAC[affine_dependent; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC[SET_RULE
     `~(a = b) ==> {a,b} DELETE a = {b} /\ {a,b} DELETE b = {a}`] THEN
    ASM_REWRITE_TAC[AFFINE_HULL_SING; IN_SING]]);;

let AFFINE_INDEPENDENT_SUBSET = prove
 (`!s t. ~affine_dependent t /\ s SUBSET t ==> ~affine_dependent s`,
  REWRITE_TAC[IMP_CONJ_ALT; CONTRAPOS_THM] THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT; AFFINE_DEPENDENT_MONO]);;

let AFFINE_INDEPENDENT_DELETE = prove
 (`!s a. ~affine_dependent s ==> ~affine_dependent(s DELETE a)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_INDEPENDENT_SUBSET) THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Coplanarity, and collinearity in terms of affine hull.                    *)
(* ------------------------------------------------------------------------- *)

let coplanar = new_definition
 `coplanar s <=> ?u v w. s SUBSET affine hull {u,v,w}`;;

let COLLINEAR_AFFINE_HULL = prove
 (`!s:real^N->bool. collinear s <=> ?u v. s SUBSET affine hull {u,v}`,
  GEN_TAC THEN REWRITE_TAC[collinear; AFFINE_HULL_2] THEN EQ_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[REAL_ARITH `u + v = &1 <=> &1 - u = v`; UNWIND_THM1] THENL
   [X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN EXISTS_TAC `x + u:real^N` THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `x - y:real^N = z <=> x = y + z`] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` SUBST1_TAC) THEN
    EXISTS_TAC `&1 + c` THEN VECTOR_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
    EXISTS_TAC `b - a:real^N` THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `y:real^N` th) THEN MP_TAC(SPEC `x:real^N` th)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `r:real` THEN DISCH_THEN SUBST1_TAC THEN
    X_GEN_TAC `s:real` THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `s - r:real` THEN VECTOR_ARITH_TAC]);;

let COLLINEAR_IMP_COPLANAR = prove
 (`!s. collinear s ==> coplanar s`,
  REWRITE_TAC[coplanar; COLLINEAR_AFFINE_HULL] THEN MESON_TAC[INSERT_AC]);;

let COPLANAR_SMALL = prove
 (`!s. FINITE s /\ CARD s <= 3 ==> coplanar s`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `s <= 3 <=> s <= 2 \/ s = 3`] THEN
  REWRITE_TAC[LEFT_OR_DISTRIB; GSYM HAS_SIZE] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
  SIMP_TAC[COLLINEAR_IMP_COPLANAR; COLLINEAR_SMALL] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN REWRITE_TAC[coplanar] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[HULL_INC; SUBSET]);;

let COPLANAR_EMPTY = prove
 (`coplanar {}`,
  SIMP_TAC[COLLINEAR_IMP_COPLANAR; COLLINEAR_EMPTY]);;

let COPLANAR_SING = prove
 (`!a. coplanar {a}`,
  SIMP_TAC[COLLINEAR_IMP_COPLANAR; COLLINEAR_SING]);;

let COPLANAR_2 = prove
 (`!a b. coplanar {a,b}`,
  SIMP_TAC[COLLINEAR_IMP_COPLANAR; COLLINEAR_2]);;

let COPLANAR_3 = prove
 (`!a b c. coplanar {a,b,c}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC COPLANAR_SMALL THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_RULES] THEN ARITH_TAC);;

let COLLINEAR_AFFINE_HULL_COLLINEAR = prove
 (`!s. collinear(affine hull s) <=> collinear s`,
  REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
  MESON_TAC[HULL_HULL; HULL_MONO; HULL_INC; SUBSET]);;

let COPLANAR_AFFINE_HULL_COPLANAR = prove
 (`!s. coplanar(affine hull s) <=> coplanar s`,
  REWRITE_TAC[coplanar] THEN
  MESON_TAC[HULL_HULL; HULL_MONO; HULL_INC; SUBSET]);;

let COPLANAR_TRANSLATION_EQ = prove
 (`!a:real^N s. coplanar(IMAGE (\x. a + x) s) <=> coplanar s`,
  REWRITE_TAC[coplanar] THEN GEOM_TRANSLATE_TAC[]);;

let COPLANAR_TRANSLATION = prove
 (`!a:real^N s. coplanar s ==> coplanar(IMAGE (\x. a + x) s)`,
  REWRITE_TAC[COPLANAR_TRANSLATION_EQ]);;

add_translation_invariants [COPLANAR_TRANSLATION_EQ];;

let COPLANAR_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s. coplanar s /\ linear f ==> coplanar(IMAGE f s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[coplanar; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `c:real^M`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
  [`(f:real^M->real^N) a`; `(f:real^M->real^N) b`; `(f:real^M->real^N) c`] THEN
  REWRITE_TAC[SET_RULE `{f a,f b,f c} = IMAGE f {a,b,c}`] THEN
  ASM_SIMP_TAC[AFFINE_HULL_LINEAR_IMAGE; IMAGE_SUBSET]);;

let COPLANAR_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (coplanar (IMAGE f s) <=> coplanar s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE COPLANAR_LINEAR_IMAGE));;

add_linear_invariants [COPLANAR_LINEAR_IMAGE_EQ];;

let COPLANAR_SUBSET = prove
 (`!s t. coplanar t /\ s SUBSET t ==> coplanar s`,
  REWRITE_TAC[coplanar] THEN SET_TAC[]);;

let AFFINE_HULL_3_IMP_COLLINEAR = prove
 (`!a b c. c IN affine hull {a,b} ==> collinear {a,b,c}`,
  ONCE_REWRITE_TAC[GSYM COLLINEAR_AFFINE_HULL_COLLINEAR] THEN
  SIMP_TAC[HULL_REDUNDANT_EQ; INSERT_AC] THEN
  REWRITE_TAC[COLLINEAR_AFFINE_HULL_COLLINEAR; COLLINEAR_2]);;

let COLLINEAR_3_AFFINE_HULL = prove
 (`!a b c:real^N.
        ~(a = b) ==> (collinear {a,b,c} <=> c IN affine hull {a,b})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[AFFINE_HULL_3_IMP_COLLINEAR] THEN
  REWRITE_TAC[collinear] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPECL [`b:real^N`; `a:real^N`] th) THEN
                        MP_TAC(SPECL [`c:real^N`; `a:real^N`] th)) THEN
  REWRITE_TAC[IN_INSERT; AFFINE_HULL_2; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[VECTOR_ARITH `a - b:real^N = c <=> a = b + c`] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN X_GEN_TAC `y:real` THEN
  ASM_CASES_TAC `y = &0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`&1 - x / y`; `x / y:real`] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL] THEN VECTOR_ARITH_TAC);;

let COLLINEAR_3_EQ_AFFINE_DEPENDENT = prove
 (`!a b c:real^N.
        collinear{a,b,c} <=>
                a = b \/ a = c \/ b = c \/ affine_dependent {a,b,c}`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t ->
    ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC])
   [`a:real^N = b`; `a:real^N = c`; `b:real^N = c`] THEN
  ASM_REWRITE_TAC[affine_dependent] THEN EQ_TAC THENL
   [ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN DISCH_TAC THEN
    EXISTS_TAC `c:real^N` THEN REWRITE_TAC[IN_INSERT];
    REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,c,a}`];
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {c,a,b}`];
      ALL_TAC] THEN
    ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s SUBSET t ==> x IN t`)) THEN
  MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]);;

let AFFINE_DEPENDENT_IMP_COLLINEAR_3 = prove
 (`!a b c:real^N. affine_dependent {a,b,c} ==> collinear{a,b,c}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[affine_dependent] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; RIGHT_OR_DISTRIB] THEN
  REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2; COLLINEAR_AFFINE_HULL] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`b:real^N`; `c:real^N`];
    MAP_EVERY EXISTS_TAC [`a:real^N`; `c:real^N`];
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`]] THEN
  SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; HULL_INC; IN_INSERT] THEN
  POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> a IN s ==> a IN t`) THEN
  MATCH_MP_TAC HULL_MONO THEN SET_TAC[]);;

let COLLINEAR_3_IN_AFFINE_HULL = prove
 (`!v0 v1 x:real^N.
        ~(v1 = v0)
        ==> (collinear {v0,v1,x} <=> x IN affine hull {v0,v1})`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `v0:real^N` THEN
  REWRITE_TAC[COLLINEAR_LEMMA; AFFINE_HULL_2] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; IN_ELIM_THM] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THEN ASM_REWRITE_TAC[] THENL
   [MAP_EVERY EXISTS_TAC [`&1`; `&0`] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    VECTOR_ARITH_TAC;
    MESON_TAC[REAL_ARITH `u + v = &1 <=> u = &1 - v`]]);;

(* ------------------------------------------------------------------------- *)
(* A general lemma.                                                          *)
(* ------------------------------------------------------------------------- *)

let CONVEX_CONNECTED = prove
 (`!s:real^N->bool. convex s ==> connected s`,
  REWRITE_TAC[CONVEX_ALT; connected; SUBSET; EXTENSION; IN_INTER;
              IN_UNION; NOT_IN_EMPTY; NOT_FORALL_THM; NOT_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  MAP_EVERY (K(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) (1--4) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC)
                         (X_CHOOSE_THEN `x2:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`\u. (&1 - u) % x1 + u % (x2:real^N)`;
                 `&0`; `&1`; `e1:real^N->bool`; `e2:real^N->bool`]
         (REWRITE_RULE[GSYM open_def] CONNECTED_REAL_LEMMA)) THEN
  ASM_REWRITE_TAC[NOT_IMP; REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                  REAL_SUB_REFL; VECTOR_ADD_RID; VECTOR_ADD_LID; REAL_POS] THEN
  REPEAT(CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[dist] THEN
  REWRITE_TAC[NORM_MUL; VECTOR_ARITH
   `((&1 - a) % x + a % y) - ((&1 - b) % x + b % y) = (a - b) % (y - x)`] THEN
  MP_TAC(ISPEC `(x2 - x1):real^N` NORM_POS_LE) THEN
  REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_MUL_RZERO; REAL_LT_01]] THEN
  EXISTS_TAC `e / norm((x2 - x1):real^N)` THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_DIV]);;

(* ------------------------------------------------------------------------- *)
(* Various topological facts are queued up here, just because they rely on   *)
(* CONNECTED_UNIV, which is a trivial consequence of CONVEX_UNIV. It would   *)
(* be fairly easy to prove it earlier and move these back to the topology.ml *)
(* file, which is a bit tidier intellectually.                               *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_UNIV = prove
 (`connected (UNIV:real^N->bool)`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_UNIV]);;

let CONNECTED_COMPONENT_UNIV = prove
 (`!x. connected_component(:real^N) x = (:real^N)`,
  MESON_TAC[CONNECTED_CONNECTED_COMPONENT_SET; CONNECTED_UNIV; IN_UNIV]);;

let CONNECTED_COMPONENT_EQ_UNIV = prove
 (`!s x. connected_component s x = (:real^N) <=> s = (:real^N)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[CONNECTED_COMPONENT_UNIV] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s = UNIV ==> t = UNIV`) THEN
  REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]);;

let COMPONENTS_UNIV = prove
 (`components(:real^N) = {(:real^N)}`,
  REWRITE_TAC[COMPONENTS_EQ_SING; CONNECTED_UNIV; UNIV_NOT_EMPTY]);;

let CLOPEN = prove
 (`!s. closed s /\ open s <=> s = {} \/ s = (:real^N)`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY; OPEN_EMPTY; CLOSED_UNIV; OPEN_UNIV] THEN
  MATCH_MP_TAC(REWRITE_RULE[CONNECTED_CLOPEN] CONNECTED_UNIV) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; GSYM CLOSED_IN]);;

let COMPACT_OPEN = prove
 (`!s:real^N->bool. compact s /\ open s <=> s = {}`,
  MESON_TAC[COMPACT_EMPTY; OPEN_EMPTY; COMPACT_IMP_CLOSED; CLOPEN;
            COMPACT_IMP_BOUNDED; NOT_BOUNDED_UNIV]);;

let FRONTIER_NOT_EMPTY = prove
 (`!s. ~(s = {}) /\ ~(s = (:real^N)) ==> ~(frontier s = {})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `s:real^N->bool`] CONNECTED_INTER_FRONTIER) THEN
  REWRITE_TAC[CONNECTED_UNIV] THEN ASM SET_TAC[]);;

let FRONTIER_EQ_EMPTY = prove
 (`!s. frontier s = {} <=> s = {} \/ s = (:real^N)`,
  MESON_TAC[FRONTIER_NOT_EMPTY; FRONTIER_EMPTY; FRONTIER_UNIV]);;

let EQ_INTERVAL = prove
 (`(!a b c d:real^N.
        interval[a,b] = interval[c,d] <=>
        interval[a,b] = {} /\ interval[c,d] = {} \/ a = c /\ b = d) /\
   (!a b c d:real^N.
        interval[a,b] = interval(c,d) <=>
        interval[a,b] = {} /\ interval(c,d) = {}) /\
   (!a b c d:real^N.
        interval(a,b) = interval[c,d] <=>
        interval(a,b) = {} /\ interval[c,d] = {}) /\
   (!a b c d:real^N.
        interval(a,b) = interval(c,d) <=>
        interval(a,b) = {} /\ interval(c,d) = {} \/ a = c /\ b = d)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  (EQ_TAC THENL [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]]) THEN
  MATCH_MP_TAC(MESON[]
   `(p = {} /\ q = {} ==> r) /\ (~(p = {}) /\ ~(q = {}) ==> p = q ==> r)
    ==> p = q ==> r`) THEN
  SIMP_TAC[] THENL
   [REWRITE_TAC[INTERVAL_NE_EMPTY; CART_EQ] THEN
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    SIMP_TAC[SUBSET_INTERVAL; GSYM REAL_LE_ANTISYM];
    STRIP_TAC THEN MATCH_MP_TAC(MESON[CLOPEN]
     `closed s /\ open t /\ ~(s = {}) /\ ~(s = UNIV) ==> ~(s = t)`) THEN
    ASM_REWRITE_TAC[CLOSED_INTERVAL; OPEN_INTERVAL; NOT_INTERVAL_UNIV];
    STRIP_TAC THEN MATCH_MP_TAC(MESON[CLOPEN]
     `closed s /\ open t /\ ~(s = {}) /\ ~(s = UNIV) ==> ~(t = s)`) THEN
    ASM_REWRITE_TAC[CLOSED_INTERVAL; OPEN_INTERVAL; NOT_INTERVAL_UNIV];
    REWRITE_TAC[INTERVAL_NE_EMPTY; CART_EQ] THEN
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    SIMP_TAC[SUBSET_INTERVAL; GSYM REAL_LE_ANTISYM]]);;

let CLOSED_INTERVAL_EQ = prove
 (`(!a b:real^N. closed(interval[a,b])) /\
   (!a b:real^N. closed(interval(a,b)) <=> interval(a,b) = {})`,
  REWRITE_TAC[CLOSED_INTERVAL] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY] THEN
  MP_TAC(ISPEC `interval(a:real^N,b)` CLOPEN) THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL] THEN
  MESON_TAC[BOUNDED_INTERVAL; NOT_BOUNDED_UNIV]);;

let OPEN_INTERVAL_EQ = prove
 (`(!a b:real^N. open(interval[a,b]) <=> interval[a,b] = {}) /\
   (!a b:real^N. open(interval(a,b)))`,
  REWRITE_TAC[OPEN_INTERVAL] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY] THEN
  MP_TAC(ISPEC `interval[a:real^N,b]` CLOPEN) THEN
  ASM_REWRITE_TAC[CLOSED_INTERVAL] THEN
  MESON_TAC[BOUNDED_INTERVAL; NOT_BOUNDED_UNIV]);;

let COMPACT_INTERVAL_EQ = prove
 (`(!a b:real^N. compact(interval[a,b])) /\
   (!a b:real^N. compact(interval(a,b)) <=> interval(a,b) = {})`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_INTERVAL] THEN
  REWRITE_TAC[CLOSED_INTERVAL_EQ]);;

let CONNECTED_CHAIN = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> compact s /\ connected s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> connected(INTERS f)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[INTERS_0; CONNECTED_UNIV] THEN
  ABBREV_TAC `c:real^N->bool = INTERS f` THEN
  SUBGOAL_THEN `compact(c:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC COMPACT_INTERS THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONNECTED_CLOSED_SET; COMPACT_IMP_CLOSED; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `b:real^N->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `b:real^N->bool`] SEPARATION_NORMAL) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?k:real^N->bool. k IN f` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?n:real^N->bool. open n /\ k SUBSET n` MP_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET_BALL; COMPACT_IMP_BOUNDED; OPEN_BALL];
    REWRITE_TAC[UNIONS_SUBSET] THEN STRIP_TAC] THEN
  MP_TAC(ISPEC `k:real^N->bool` COMPACT_IMP_HEINE_BOREL) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC
   `(u UNION v:real^N->bool) INSERT {n DIFF s | s IN f}`) THEN
  REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_INSERT; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[OPEN_UNION; OPEN_DIFF; COMPACT_IMP_CLOSED; NOT_IMP] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_INSERT] THEN REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[IN_UNION] THEN
    ASM_CASES_TAC `(x:real^N) IN c` THENL [ASM SET_TAC[]; DISJ2_TAC] THEN
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM] THEN
    UNDISCH_TAC `~((x:real^N) IN c)` THEN
    SUBST1_TAC(SYM(ASSUME `INTERS f:real^N->bool = c`)) THEN
    REWRITE_TAC[IN_INTERS; NOT_FORALL_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SUBSET_INSERT_DELETE] THEN
  SUBGOAL_THEN `FINITE(g DELETE (u UNION v:real^N->bool))` MP_TAC THENL
   [ASM_REWRITE_TAC[FINITE_DELETE];
    REWRITE_TAC[TAUT `p ==> ~q <=> ~(p /\ q)`]] THEN
  REWRITE_TAC[FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?j:real^N->bool. j IN f /\
                     UNIONS(IMAGE (\s. n DIFF s) f') SUBSET (n DIFF j)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `f':(real^N->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; EMPTY_SUBSET] THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?j:real^N->bool. j IN f' /\
                       UNIONS(IMAGE (\s. n DIFF s) f') SUBSET (n DIFF j)`
    MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET]] THEN
    SUBGOAL_THEN
     `!s t:real^N->bool. s IN f' /\ t IN f' ==> s SUBSET t \/ t SUBSET s`
    MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `~(f':(real^N->bool)->bool = {})` THEN
    UNDISCH_TAC `FINITE(f':(real^N->bool)->bool)` THEN
    SPEC_TAC(`f':(real^N->bool)->bool`,`f':(real^N->bool)->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[] THEN
    REWRITE_TAC[EXISTS_IN_INSERT; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_INSERT] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY X_GEN_TAC [`i:real^N->bool`; `f:(real^N->bool)->bool`] THEN
    ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT; NOT_IN_EMPTY;
                    UNIONS_0; UNION_EMPTY; SUBSET_REFL] THEN
    DISCH_THEN(fun th -> REPEAT DISCH_TAC THEN MP_TAC th) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(n DIFF j) SUBSET (n DIFF i) \/
                  (n DIFF i:real^N->bool) SUBSET (n DIFF j)`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:real^N->bool` o CONJUNCT2) THEN
      ASM SET_TAC[];
      DISJ1_TAC THEN ASM SET_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `j:real^N->bool` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j INTER k:real^N->bool) SUBSET (u UNION v)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `k SUBSET (u UNION v) UNION (n DIFF j)
      ==> (j INTER k) SUBSET (u UNION v)`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS g :real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
     `UNIONS((u UNION v:real^N->bool) INSERT (g DELETE (u UNION v)))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUBSET_UNIONS THEN SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[UNIONS_INSERT] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(j INTER k:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[SET_RULE `s SUBSET t ==> s INTER t = s`; INTER_COMM];
    REWRITE_TAC[connected] THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let CONNECTED_CHAIN_GEN = prove
 (`!f:(real^N->bool)->bool.
       (!s. s IN f ==> closed s /\ connected s) /\
       (?s. s IN f /\ compact s) /\
       (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
       ==> connected(INTERS f)`,
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `INTERS f = INTERS(IMAGE (\t:real^N->bool. s INTER t) f)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; INTERS_IMAGE] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONNECTED_CHAIN THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[COMPACT_INTER_CLOSED] THEN
    CONJ_TAC THENL [X_GEN_TAC `t:real^N->bool`; ASM SET_TAC[]] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `s INTER t:real^N->bool = s \/ s INTER t = t`
     (DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM SET_TAC[]]);;

let CONNECTED_NEST = prove
 (`!s. (!n. compact(s n) /\ connected(s n)) /\
       (!m n. m <= n ==> s n SUBSET s m)
       ==> connected(INTERS {s n | n IN (:num)})`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CONNECTED_CHAIN THEN
  ASM_SIMP_TAC[FORALL_IN_GSPEC; IN_UNIV; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC WLOG_LE THEN ASM_MESON_TAC[]);;

let CONNECTED_NEST_GEN = prove
 (`!s. (!n. closed(s n) /\ connected(s n)) /\ (?n. compact(s n)) /\
       (!m n. m <= n ==> s n SUBSET s m)
       ==> connected(INTERS {s n | n IN (:num)})`,
  GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC CONNECTED_CHAIN_GEN THEN
  ASM_SIMP_TAC[FORALL_IN_GSPEC; IN_UNIV; IMP_CONJ; RIGHT_FORALL_IMP_THM;
               EXISTS_IN_GSPEC] THEN
  MATCH_MP_TAC WLOG_LE THEN ASM_MESON_TAC[]);;

let EQ_BALLS = prove
 (`(!a a':real^N r r'.
      ball(a,r) = ball(a',r') <=> a = a' /\ r = r' \/ r <= &0 /\ r' <= &0) /\
   (!a a':real^N r r'.
      ball(a,r) = cball(a',r') <=> r <= &0 /\ r' < &0) /\
   (!a a':real^N r r'.
      cball(a,r) = ball(a',r') <=> r < &0 /\ r' <= &0) /\
   (!a a':real^N r r'.
      cball(a,r) = cball(a',r') <=> a = a' /\ r = r' \/ r < &0 /\ r' < &0)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT STRIP_TAC THEN
  (EQ_TAC THENL
    [ALL_TAC; REWRITE_TAC[EXTENSION; IN_BALL; IN_CBALL] THEN NORM_ARITH_TAC])
  THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_BALLS] THEN NORM_ARITH_TAC;
    ONCE_REWRITE_TAC[EQ_SYM_EQ];
    ALL_TAC;
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_BALLS] THEN NORM_ARITH_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[CLOPEN; BOUNDED_BALL; NOT_BOUNDED_UNIV]
    `s = t ==> closed s /\ open t /\ bounded t ==> s = {} /\ t = {}`)) THEN
  REWRITE_TAC[OPEN_BALL; CLOSED_CBALL; BOUNDED_BALL;
              BALL_EQ_EMPTY; CBALL_EQ_EMPTY] THEN
  REAL_ARITH_TAC);;

let FINITE_CBALL = prove
 (`!a:real^N r. FINITE(cball(a,r)) <=> r <= &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[CBALL_EMPTY; REAL_LT_IMP_LE; FINITE_EMPTY] THEN
  ASM_CASES_TAC `r = &0` THEN
  ASM_REWRITE_TAC[CBALL_TRIVIAL; FINITE_SING; REAL_LE_REFL] THEN
  EQ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP EMPTY_INTERIOR_FINITE) THEN
  REWRITE_TAC[INTERIOR_CBALL; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC);;

let FINITE_BALL = prove
 (`!a:real^N r. FINITE(ball(a,r)) <=> r <= &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r <= &0` THEN
  ASM_SIMP_TAC[BALL_EMPTY; REAL_LT_IMP_LE; FINITE_EMPTY] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        FINITE_IMP_NOT_OPEN)) THEN
  REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Minimal continua.                                                         *)
(* ------------------------------------------------------------------------- *)

let MINIMAL_CONTINUUM = prove
 (`!t s:real^N->bool.
        t SUBSET s /\ compact s /\ connected s
        ==> ?u. t SUBSET u /\ u SUBSET s /\ compact u /\ connected u /\
                !v. v SUBSET u /\ t SUBSET v /\ compact v /\ connected v
                    ==> v = u`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [EXISTS_TAC `{}:real^N->bool` THEN
    ASM_MESON_TAC[COMPACT_EMPTY; CONNECTED_EMPTY; SUBSET_EMPTY; EMPTY_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real^N->bool. t SUBSET u /\ connected u`;
                 `s:real^N->bool`]
        BROUWER_REDUCTION_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN GEN_TAC THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET_INTERS] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONNECTED_NEST THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SET_RULE `(v SUBSET u /\ p ==> v = u) <=>
                          (v SUBSET u /\ p ==> ~(v PSUBSET u))`] THEN
    GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Convex functions into the reals.                                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("convex_on",(12,"right"));;

let convex_on = new_definition
  `f convex_on s <=>
        !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
                  ==> f(u % x + v % y) <= u * f(x) + v * f(y)`;;

let CONVEX_ON_SUBSET = prove
 (`!f s t. f convex_on t /\ s SUBSET t ==> f convex_on s`,
  REWRITE_TAC[convex_on; SUBSET] THEN MESON_TAC[]);;

let CONVEX_ON_EQ = prove
 (`!f g s. convex s /\ (!x. x IN s ==> f x = g x) /\ f convex_on s
           ==> g convex_on s`,
  REWRITE_TAC[convex_on; convex] THEN MESON_TAC[]);;

let CONVEX_ADD = prove
 (`!s f g. f convex_on s /\ g convex_on s ==> (\x. f(x) + g(x)) convex_on s`,
  REWRITE_TAC[convex_on; AND_FORALL_THM] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL ORELSE GEN_TAC) THEN
  MATCH_MP_TAC(TAUT
    `(b /\ c ==> d) ==> (a ==> b) /\ (a ==> c) ==> a ==> d`) THEN
  REAL_ARITH_TAC);;

let CONVEX_CMUL = prove
 (`!s c f. &0 <= c /\ f convex_on s ==> (\x. c * f(x)) convex_on s`,
  SIMP_TAC[convex_on; REAL_LE_LMUL;
           REAL_ARITH `u * c * fx + v * c * fy = c * (u * fx + v * fy)`]);;

let CONVEX_MAX = prove
 (`!f g s. f convex_on s /\ g convex_on s
           ==> (\x. max (f x) (g x)) convex_on s`,
  REWRITE_TAC[convex_on; REAL_MAX_LE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let CONVEX_LOWER = prove
 (`!f s x y. f convex_on s /\
             x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
             ==> f(u % x + v % y) <= max (f(x)) (f(y))`,
  REWRITE_TAC[convex_on] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  ASM_MESON_TAC[REAL_LE_ADD2; REAL_LE_LMUL; REAL_MAX_MAX]);;

let CONVEX_LOWER_SEGMENT = prove
 (`!f s a b x:real^N.
        f convex_on s /\ a IN s /\ b IN s /\ x IN segment[a,b]
        ==> f(x) <= max (f a) (f b)`,
  REWRITE_TAC[IN_SEGMENT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONVEX_LOWER THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CONVEX_LOCAL_GLOBAL_MINIMUM = prove
 (`!f s t x:real^N.
       f convex_on s /\ x IN t /\ open t /\ t SUBSET s /\
       (!y. y IN t ==> f(x) <= f(y))
       ==> !y. y IN s ==> f(x) <= f(y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < dist(x:real^N,y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIST_POS_LT; REAL_LT_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`&1`; `e / dist(x:real^N,y)`] REAL_DOWN2) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [convex_on]) THEN
  DISCH_THEN(MP_TAC o
    SPECL [`x:real^N`; `y:real^N`; `&1 - u`; `u:real`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_SUB_ADD; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
    ASM_MESON_TAC[CENTRE_IN_BALL; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `(&1 - u) * f(x) + u * f(x:real^N):real` THEN
  ASM_SIMP_TAC[REAL_LT_LADD; REAL_LT_LMUL] THEN
  REWRITE_TAC[REAL_ARITH `(&1 - x) * a + x * a = a`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[IN_BALL; dist] THEN
  REWRITE_TAC[VECTOR_ARITH `x - ((&1 - u) % x + u % y):real^N =
                            u % (x - y)`] THEN
  REWRITE_TAC[NORM_MUL; GSYM dist] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ;
               REAL_ARITH `&0 < x /\ x < b ==> abs x < b`]);;

let CONVEX_DISTANCE = prove
 (`!s a. (\x. dist(a,x)) convex_on s`,
  REWRITE_TAC[convex_on; dist] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
   [GSYM VECTOR_MUL_LID] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_ARITH
   `(u + v) % z - (u % x + v % y) = u % (z - x) + v % (z - y)`] THEN
  ASM_MESON_TAC[NORM_TRIANGLE; NORM_MUL; REAL_ABS_REFL]);;

let CONVEX_NORM = prove
 (`!s:real^N->bool. norm convex_on s`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `vec 0:real^N`] CONVEX_DISTANCE) THEN
  REWRITE_TAC[DIST_0; ETA_AX]);;

let CONVEX_ON_COMPOSE_LINEAR = prove
 (`!f g:real^M->real^N s.
        f convex_on (IMAGE g s) /\ linear g ==> (f o g) convex_on s`,
  REWRITE_TAC[convex_on; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  ASM_SIMP_TAC[]);;

let CONVEX_ON_TRANSLATION = prove
 (`!f a:real^N.
        f convex_on (IMAGE (\x. a + x) s) <=> (\x. f(a + x)) convex_on s`,
  REWRITE_TAC[convex_on; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN
  REWRITE_TAC[VECTOR_ARITH
   `u % (a + x) + v % (a + y):real^N = (u + v) % a + u % x + v % y`] THEN
  SIMP_TAC[VECTOR_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Open and closed balls are convex and hence connected.                     *)
(* ------------------------------------------------------------------------- *)

let CONVEX_BALL = prove
 (`!x:real^N e. convex(ball(x,e))`,
  let lemma = REWRITE_RULE[convex_on; IN_UNIV]
   (ISPEC `(:real^N)` CONVEX_DISTANCE) in
  REWRITE_TAC[convex; IN_BALL] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) lemma o lhand o snd) THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_CONVEX_BOUND_LT]);;

let CONNECTED_BALL = prove
 (`!x:real^N e. connected(ball(x,e))`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_BALL]);;

let CONVEX_CBALL = prove
 (`!x:real^N e. convex(cball(x,e))`,
  REWRITE_TAC[convex; IN_CBALL; dist] THEN MAP_EVERY X_GEN_TAC
   [`x:real^N`; `e:real`; `y:real^N`; `z:real^N`; `u:real`; `v:real`] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[VECTOR_ARITH `a - b = &1 % a - b`] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a + b) % x - (a % y + b % z) = a % (x - y) + b % (x - z)`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(u % (x - y)) + norm(v % (x - z):real^N)` THEN
  REWRITE_TAC[NORM_TRIANGLE; NORM_MUL] THEN
  MATCH_MP_TAC REAL_CONVEX_BOUND_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 <= u /\ &0 <= v /\ (u + v = &1) ==> (abs(u) + abs(v) = &1)`]);;

let CONNECTED_CBALL = prove
 (`!x:real^N e. connected(cball(x,e))`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_CBALL]);;

let CONVEX_INTERMEDIATE_BALL = prove
 (`!a:real^N r t. ball(a,r) SUBSET t /\ t SUBSET cball(a,r) ==> convex t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_CONTAINS_OPEN_SEGMENT] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    SUBSET_TRANS)) THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN GEN_TAC THEN DISCH_THEN
   (MP_TAC o SPEC `a:real^N` o MATCH_MP DIST_DECREASES_OPEN_SEGMENT) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[IN_CBALL] THEN ASM_MESON_TAC[REAL_LTE_TRANS]);;

let FRONTIER_OF_CONNECTED_COMPONENT_SUBSET = prove
 (`!s c x:real^N. frontier(connected_component s x) SUBSET frontier s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frontier; SUBSET; IN_DIFF] THEN
  X_GEN_TAC `y:real^N` THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `y IN s ==> s SUBSET t ==> y IN t`)) THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN REWRITE_TAC[CONNECTED_COMPONENT_SUBSET];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `ball(y:real^N,e) SUBSET connected_component s y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
      ASM_REWRITE_TAC[CONNECTED_BALL; CENTRE_IN_BALL];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSURE_APPROACHABLE]) THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
      ASM_REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] (GSYM IN_BALL)] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
      REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `e:real` THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`; `y:real^N`]
        CONNECTED_COMPONENT_OVERLAP) THEN
      MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[]]]);;

let FRONTIER_OF_COMPONENTS_SUBSET = prove
 (`!s c:real^N->bool.
        c IN components s ==> frontier c SUBSET frontier s`,
  SIMP_TAC[components; FORALL_IN_GSPEC;
           FRONTIER_OF_CONNECTED_COMPONENT_SUBSET]);;

let FRONTIER_OF_COMPONENTS_CLOSED_COMPLEMENT = prove
 (`!s c. closed s /\ c IN components ((:real^N) DIFF s)
         ==> frontier c SUBSET s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FRONTIER_OF_COMPONENTS_SUBSET) THEN
  REWRITE_TAC[FRONTIER_COMPLEMENT] THEN
  ASM_MESON_TAC[FRONTIER_SUBSET_EQ; SUBSET_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* A couple of lemmas about components (see Newman IV, 3.3 and 3.4).         *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_UNION_CLOPEN_IN_COMPLEMENT = prove
 (`!s t u:real^N->bool.
        connected s /\ connected u /\ s SUBSET u /\
        open_in (subtopology euclidean (u DIFF s)) t /\
        closed_in (subtopology euclidean (u DIFF s)) t
        ==> connected (s UNION t)`,
  MAP_EVERY X_GEN_TAC
   [`c:real^N->bool`; `h:real^N->bool`; `s:real^N->bool`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[CONNECTED_CLOSED_IN_EQ; NOT_EXISTS_THM] THEN
  MATCH_MP_TAC(MESON[]
   `!Q. (!x y. P x y <=> P y x) /\
        (!x y. P x y ==> Q x \/ Q y) /\
        (!x y. P x y /\ Q x ==> F)
        ==> (!x y. ~(P x y))`) THEN
  EXISTS_TAC `\x:real^N->bool. c SUBSET x` THEN
  CONJ_TAC THENL [MESON_TAC[INTER_COMM; UNION_COMM]; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THEN
  MAP_EVERY X_GEN_TAC [`h1:real^N->bool`; `h2:real^N->bool`] THENL
   [STRIP_TAC THEN UNDISCH_TAC `connected(c:real^N->bool)` THEN
    REWRITE_TAC[CONNECTED_CLOSED_IN; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o
      SPECL [`c INTER h1:real^N->bool`; `c INTER h2:real^N->bool`]) THEN
    MATCH_MP_TAC(TAUT
     `(p /\ q) /\ (~r ==> s) ==> ~(p /\ q /\ r) ==> s`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN CONJ_TAC THENL
     [UNDISCH_TAC
        `closed_in(subtopology euclidean (c UNION h)) (h1:real^N->bool)`;
      UNDISCH_TAC
        `closed_in(subtopology euclidean (c UNION h)) (h2:real^N->bool)`] THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM SET_TAC[];
    STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
    SUBGOAL_THEN `(h2:real^N->bool) SUBSET h` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `connected(s:real^N->bool)` THEN
    REWRITE_TAC[CONNECTED_CLOPEN] THEN
    DISCH_THEN(MP_TAC o SPEC `h2:real^N->bool`) THEN REWRITE_TAC[NOT_IMP] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    SUBGOAL_THEN `s:real^N->bool = (s DIFF c) UNION (c UNION h)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_UNION THEN
      MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(c UNION h) DIFF h2:real^N->bool = h1`
         (fun th -> ASM_REWRITE_TAC[th]) THEN ASM SET_TAC[];
        DISCH_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS THEN
        EXISTS_TAC `h:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC
         `open_in(subtopology euclidean (c UNION h)) (h2:real^N->bool)` THEN
        REWRITE_TAC[OPEN_IN_OPEN] THEN MATCH_MP_TAC MONO_EXISTS THEN
        ASM SET_TAC[]];
      MATCH_MP_TAC CLOSED_IN_SUBTOPOLOGY_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_IN_TRANS THEN EXISTS_TAC `h:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `closed_in(subtopology euclidean (c UNION h)) (h2:real^N->bool)` THEN
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN MATCH_MP_TAC MONO_EXISTS THEN
      ASM SET_TAC[]]]);;

let COMPONENT_COMPLEMENT_CONNECTED = prove
 (`!s u c:real^N->bool.
        connected s /\ connected u /\ s SUBSET u /\ c IN components (u DIFF s)
        ==> connected(u DIFF c)`,
  MAP_EVERY X_GEN_TAC
   [`a:real^N->bool`; `s:real^N->bool`; `c:real^N->bool`] THEN
  STRIP_TAC THEN UNDISCH_TAC `connected(a:real^N->bool)` THEN
  REWRITE_TAC[CONNECTED_CLOSED_IN_EQ; NOT_EXISTS_THM] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC
   [`h3:real^N->bool`; `h4:real^N->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`a INTER h3:real^N->bool`; `a INTER h4:real^N->bool`]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
  EVERY_ASSUM(fun th -> try
        MP_TAC(CONJUNCT1(GEN_REWRITE_RULE I [closed_in] th))
        with Failure _ -> ALL_TAC) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `closed_in (subtopology euclidean (s DIFF c))
                           (h3:real^N->bool)` THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM SET_TAC[];
    UNDISCH_TAC `closed_in (subtopology euclidean (s DIFF c))
                           (h4:real^N->bool)` THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`s DIFF a:real^N->bool`; `c UNION h3:real^N->bool`;
               `c:real^N->bool`] COMPONENTS_MAXIMAL) THEN
    ASM_REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONNECTED_UNION_CLOPEN_IN_COMPLEMENT THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      ASM SET_TAC[];
      REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `s DIFF c DIFF h3:real^N->bool = h4` SUBST1_TAC THEN
      ASM SET_TAC[]];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`s DIFF a:real^N->bool`; `c UNION h4:real^N->bool`;
               `c:real^N->bool`] COMPONENTS_MAXIMAL) THEN
    ASM_REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONNECTED_UNION_CLOPEN_IN_COMPLEMENT THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      ASM SET_TAC[];
      REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `s DIFF c DIFF h4:real^N->bool = h3` SUBST1_TAC THEN
      ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Condition for an open map's image to contain a ball.                      *)
(* ------------------------------------------------------------------------- *)

let BALL_SUBSET_OPEN_MAP_IMAGE = prove
 (`!f:real^M->real^N s a r.
        bounded s /\ f continuous_on closure s /\ open(IMAGE f (interior s)) /\
        a IN s /\ &0 < r /\ (!z. z IN frontier s ==> r <= norm(f z - f a))
        ==> ball(f(a),r) SUBSET IMAGE f s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ball((f:real^M->real^N) a,r)`;
                 `(:real^N) DIFF IMAGE (f:real^M->real^N) s`]
    CONNECTED_INTER_FRONTIER) THEN
  REWRITE_TAC[CONNECTED_BALL] THEN MATCH_MP_TAC(SET_RULE
   `~(b INTER s = {}) /\ b INTER f = {} ==>
    (~(b INTER (UNIV DIFF s) = {}) /\ ~(b DIFF (UNIV DIFF s) = {})
     ==> ~(b INTER f = {}))
    ==> b SUBSET s`) THEN
  REWRITE_TAC[FRONTIER_COMPLEMENT] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(f:real^M->real^N) a` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM SET_TAC[];
    REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x. x IN t ==> ~(x IN s)`] THEN
    REWRITE_TAC[IN_BALL; REAL_NOT_LT]] THEN
  MP_TAC(ISPECL[`frontier(IMAGE (f:real^M->real^N) s)`; `(f:real^M->real^N) a`]
    DISTANCE_ATTAINS_INF) THEN
  REWRITE_TAC[FRONTIER_CLOSED; FRONTIER_EQ_EMPTY] THEN ANTS_TAC THENL
   [SIMP_TAC[DE_MORGAN_THM] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[NOT_BOUNDED_UNIV] `bounded s ==> ~(s = UNIV)`) THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N) (closure s)` THEN
    SIMP_TAC[IMAGE_SUBSET; CLOSURE_SUBSET] THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[COMPACT_CLOSURE];
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [frontier]) THEN
  REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[CLOSURE_SEQUENTIAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num->real^N`
   (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[IN_IMAGE; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:num->real^M` THEN REWRITE_TAC[FORALL_AND_THM] THEN
  ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM COMPACT_CLOSURE]) THEN
  REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `z:num->real^M`) THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y:real^M`; `r:num->num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(((\n. (f:real^M->real^N)(z n)) o (r:num->num)) --> w) sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC LIM_SUBSEQUENCE THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN REWRITE_TAC[GSYM o_ASSOC]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!n. ((z:num->real^M) o (r:num->num)) n IN s` MP_TAC THENL
   [ASM_REWRITE_TAC[o_THM];
    UNDISCH_THEN `((\n. (f:real^M->real^N) ((z:num->real^M) n)) --> w)
                  sequentially` (K ALL_TAC) THEN
    UNDISCH_THEN `!n. (z:num->real^M) n IN s` (K ALL_TAC)] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`(z:num->real^M) o (r:num->num)`, `z:num->real^M`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `w = (f:real^M->real^N) y` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `(f:real^M->real^N) o (z:num->real^M)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_CLOSURE_SEQUENTIALLY];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(f y - (f:real^M->real^N) a)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC; ASM_MESON_TAC[dist; NORM_SUB]] THEN
  ASM_REWRITE_TAC[frontier; IN_DIFF] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) (interior s)` THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; INTERIOR_SUBSET] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on sets preserve convexity.                         *)
(* ------------------------------------------------------------------------- *)

let CONVEX_SCALING = prove
 (`!s c. convex s ==> convex (IMAGE (\x. c % x) s)`,
  REWRITE_TAC[convex; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `u % c % x + v % c % y = c % (u % x + v % y)`] THEN
  ASM_MESON_TAC[]);;

let CONVEX_SCALING_EQ = prove
 (`!s c. ~(c = &0) ==> (convex (IMAGE (\x. c % x) s) <=> convex s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[CONVEX_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c` o MATCH_MP CONVEX_SCALING) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; o_DEF; VECTOR_MUL_ASSOC;
               REAL_MUL_LINV; VECTOR_MUL_LID; IMAGE_ID]);;

let CONVEX_NEGATIONS = prove
 (`!s. convex s ==> convex (IMAGE (--) s)`,
  REWRITE_TAC[convex; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `u % --x + v % --y = --(u % x + v % y)`] THEN
  ASM_MESON_TAC[]);;

let CONVEX_SUMS = prove
 (`!s t. convex s /\ convex t ==> convex {x + y | x IN s /\ y IN t}`,
  REWRITE_TAC[convex; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
    `u % (a + b) + v % (c + d) = (u % a + v % c) + (u % b + v % d)`] THEN
  ASM_MESON_TAC[]);;

let CONVEX_DIFFERENCES = prove
 (`!s t. convex s /\ convex t ==> convex {x - y | x IN s /\ y IN t}`,
  REWRITE_TAC[convex; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
    `u % (a - b) + v % (c - d) = (u % a + v % c) - (u % b + v % d)`] THEN
  ASM_MESON_TAC[]);;

let CONVEX_AFFINITY = prove
 (`!s a:real^N c.
        convex s ==> convex (IMAGE (\x. a + c % x) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; CONVEX_TRANSLATION; CONVEX_SCALING]);;

let CONVEX_LINEAR_PREIMAGE = prove
 (`!f:real^M->real^N.
     linear f /\ convex s ==> convex {x | f(x) IN s}`,
  REWRITE_TAC[CONVEX_ALT; IN_ELIM_THM] THEN
  SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* Some interesting "cancellation" properties for sum-sets.                  *)
(* ------------------------------------------------------------------------- *)

let SUBSET_SUMS_LCANCEL = prove
 (`!s t u:real^N->bool.
        ~(s = {}) /\ bounded s /\ closed u /\ convex u /\
        {x + y | x IN s /\ y IN t} SUBSET {x + z | x IN s /\ z IN u}
        ==> t SUBSET u`,
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN X_GEN_TAC `b:real^N` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. ?w z:real^N. w IN s /\ z IN u /\ (&n + &1) % (b - z) = w - a`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
      ASM_REWRITE_TAC[REAL_ADD_LID; VECTOR_MUL_LID] THEN
      REWRITE_TAC[VECTOR_ARITH `b - z:real^N = w - a <=> a + b = w + z`] THEN
      MESON_TAC[];
      FIRST_X_ASSUM(X_CHOOSE_THEN `a':real^N` (X_CHOOSE_THEN `c':real^N`
        STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a':real^N`; `b:real^N`]) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`a'':real^N`; `c'':real^N`] THEN STRIP_TAC THEN
      EXISTS_TAC `a'':real^N` THEN EXISTS_TAC
       `(&1 - &1 / (&n + &2)) % c' + &1 / (&n + &2) % c'':real^N` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONVEX_ALT]) THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ;
                     REAL_ARITH `&0 < &n + &2`] THEN
        REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I
         [VECTOR_ARITH `a' + b:real^N = a'' + c <=> a'' = (a' + b) - c`]) THEN
        REWRITE_TAC[VECTOR_ARITH
         `(&n + &1) % (b - c):real^N = (a' + b) - c'' - a <=>
          &n % b - (&n + &1) % c = (a' - c'') - a`] THEN
        SIMP_TAC[GSYM REAL_OF_NUM_SUC; VECTOR_MUL_ASSOC; VECTOR_ADD_LDISTRIB;
                 REAL_ARITH `(n + &1) + &1 = n + &2`] THEN
        REWRITE_TAC[VECTOR_MUL_LID; REAL_FIELD
         `(&n + &2) * (&1 - (&1 / (&n + &2))) = &n + &1 /\
          (&n + &2) * &1 / (&n + &2) = &1`] THEN
        ASM_REWRITE_TAC[VECTOR_ARITH
         `n % b - (n % c + d):real^N = n % (b - c) - d`] THEN
        CONV_TAC VECTOR_ARITH]];
      FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl) THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `s:real^N->bool`] BOUNDED_DIFFS) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[BOUNDED_POS; FORALL_IN_GSPEC] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
      DISCH_TAC THEN FIRST_X_ASSUM(fun th ->
        ONCE_REWRITE_TAC[GSYM(MATCH_MP CLOSED_APPROACHABLE th)]) THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(SPEC `e:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `B:real`) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; X_GEN_TAC `n:num`] THEN
      DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `c:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
      EXISTS_TAC `abs(&n + &1)` THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[dist]] THEN
      ASM_REWRITE_TAC[GSYM NORM_MUL] THEN
      REWRITE_TAC[REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
      ASM_MESON_TAC[REAL_LET_TRANS]]);;

let SUBSET_SUMS_RCANCEL = prove
 (`!s t u:real^N->bool.
        closed t /\ convex t /\ bounded u /\ ~(u = {}) /\
        {x + z | x IN s /\ z IN u} SUBSET {y + z | y IN t /\ z IN u}
        ==> s SUBSET t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_SUMS_LCANCEL THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SUMS_SYM] THEN ASM_REWRITE_TAC[]);;

let EQ_SUMS_LCANCEL = prove
 (`!s t u.
        ~(s = {}) /\ bounded s /\
        closed t /\ convex t /\ closed u /\ convex u /\
        {x + y | x IN s /\ y IN t} = {x + z | x IN s /\ z IN u}
        ==> t = u`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; EMPTY_SUBSET] THEN
  REWRITE_TAC[SUBSET_EMPTY] THEN MESON_TAC[SUBSET_SUMS_LCANCEL]);;

let EQ_SUMS_RCANCEL = prove
 (`!s t u.
        closed s /\ convex s /\ closed t /\ convex t /\
        bounded u /\ ~(u = {}) /\
        {x + z | x IN s /\ z IN u} = {y + z | y IN t /\ z IN u}
        ==> s = t`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; EMPTY_SUBSET] THEN
  REWRITE_TAC[SUBSET_EMPTY] THEN MESON_TAC[SUBSET_SUMS_RCANCEL]);;

(* ------------------------------------------------------------------------- *)
(* Convex hull.                                                              *)
(* ------------------------------------------------------------------------- *)

let CONVEX_CONVEX_HULL = prove
 (`!s. convex(convex hull s)`,
  SIMP_TAC[P_HULL; CONVEX_INTERS]);;

let CONVEX_HULL_EQ = prove
 (`!s. (convex hull s = s) <=> convex s`,
  SIMP_TAC[HULL_EQ; CONVEX_INTERS]);;

let CONVEX_HULLS_EQ = prove
 (`!s t. s SUBSET convex hull t /\ t SUBSET convex hull s
         ==> convex hull s = convex hull t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULLS_EQ THEN
  ASM_SIMP_TAC[CONVEX_INTERS]);;

let IS_CONVEX_HULL = prove
 (`!s. convex s <=> ?t. s = convex hull t`,
  GEN_TAC THEN MATCH_MP_TAC IS_HULL THEN SIMP_TAC[CONVEX_INTERS]);;

let MIDPOINTS_IN_CONVEX_HULL = prove 
 (`!x:real^N s. x IN convex hull s /\ y IN convex hull s
         ==> midpoint(x,y) IN convex hull s`,
  MESON_TAC[MIDPOINT_IN_CONVEX; CONVEX_CONVEX_HULL]);;

let CONVEX_HULL_UNIV = prove
 (`convex hull (:real^N) = (:real^N)`,
  REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_UNIV]);;

let BOUNDED_CONVEX_HULL = prove
 (`!s:real^N->bool. bounded s ==> bounded(convex hull s)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [bounded] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `cball(vec 0:real^N,B)` THEN
  SIMP_TAC[BOUNDED_CBALL; SUBSET_HULL; CONVEX_CBALL] THEN
  ASM_REWRITE_TAC[IN_CBALL; SUBSET; dist; VECTOR_SUB_LZERO; NORM_NEG]);;

let BOUNDED_CONVEX_HULL_EQ = prove
 (`!s. bounded(convex hull s) <=> bounded s`,
  MESON_TAC[BOUNDED_CONVEX_HULL; HULL_SUBSET; BOUNDED_SUBSET]);;

let FINITE_IMP_BOUNDED_CONVEX_HULL = prove
 (`!s. FINITE s ==> bounded(convex hull s)`,
  SIMP_TAC[BOUNDED_CONVEX_HULL; FINITE_IMP_BOUNDED]);;

(* ------------------------------------------------------------------------- *)
(* Stepping theorems for convex hulls of finite sets.                        *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_EMPTY = prove
 (`convex hull {} = {}`,
  MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[SUBSET_REFL; CONVEX_EMPTY; EMPTY_SUBSET]);;

let CONVEX_HULL_EQ_EMPTY = prove
 (`!s. (convex hull s = {}) <=> (s = {})`,
  GEN_TAC THEN EQ_TAC THEN
  MESON_TAC[SUBSET_EMPTY; HULL_SUBSET; CONVEX_HULL_EMPTY]);;

let CONVEX_HULL_SING = prove
 (`!a. convex hull {a} = {a}`,
  REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_SING]);;

let CONVEX_HULL_EQ_SING = prove
 (`!s a:real^N. convex hull s = {a} <=> s = {a}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CONVEX_HULL_EMPTY] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[CONVEX_HULL_SING] THEN
  MATCH_MP_TAC(SET_RULE `~(s = {}) /\ s SUBSET {a} ==> s = {a}`) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[HULL_SUBSET]);;

let CONVEX_HULL_INSERT = prove
 (`!s a. ~(s = {})
         ==> (convex hull (a INSERT s) =
                {x:real^N | ?u v b. &0 <= u /\ &0 <= v /\ (u + v = &1) /\
                                    b IN (convex hull s) /\
                                    (x = u % a + v % b)})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
       [MAP_EVERY EXISTS_TAC [`&1`; `&0`];
        MAP_EVERY EXISTS_TAC [`&0`; `&1`]] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO] THEN
      ASM_REWRITE_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_MESON_TAC[MEMBER_NOT_EMPTY; HULL_SUBSET; SUBSET];
      ALL_TAC];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[convex] CONVEX_CONVEX_HULL) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[HULL_SUBSET; SUBSET; IN_INSERT; HULL_MONO]] THEN
  REWRITE_TAC[convex; IN_ELIM_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`x:real^N`; `y:real^N`; `u:real`; `v:real`; `u1:real`; `v1:real`;
    `b1:real^N`; `u2:real`; `v2:real`; `b2:real^N`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`u * u1 + v * u2`; `u * v1 + v * v2`] THEN
  REWRITE_TAC[VECTOR_ARITH
   `u % (u1 % a + v1 % b1) + v % (u2 % a + v2 % b2) =
    (u * u1 + v * u2) % a + (u * v1) % b1 + (v * v2) % b2`] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID; REAL_ARITH
   `(u * u1 + v * u2) + (u * v1 + v * v2) =
    u * (u1 + v1) + v * (u2 + v2)`] THEN
  ASM_CASES_TAC `u * v1 + v * v2 = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `(a + b = &0) ==> &0 <= a /\ &0 <= b ==> (a = &0) /\ (b = &0)`)) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_ADD_LID; VECTOR_MUL_LZERO;
                 VECTOR_ADD_RID] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(u * v1) / (u * v1 + v * v2) % b1 +
              (v * v2) / (u * v1 + v * v2) % b2 :real^N` THEN
  ASM_SIMP_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; REAL_DIV_LMUL] THEN
  MATCH_MP_TAC(REWRITE_RULE[convex] CONVEX_CONVEX_HULL) THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_LE_ADD] THEN
  ASM_SIMP_TAC[real_div; GSYM REAL_ADD_RDISTRIB; REAL_MUL_RINV]);;

let CONVEX_HULL_INSERT_ALT = prove
 (`!s a:real^N.
      convex hull (a INSERT s) =
      if s = {} then {a}
      else {(&1 - u) % a + u % x | &0 <= u /\ u <= &1 /\ x IN convex hull s}`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CONVEX_HULL_SING] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> b /\ c /\ a /\ d`] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2; REAL_SUB_LE;
              REAL_ARITH `u + v = &1 <=> u = &1 - v`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Explicit expression for convex hull.                                      *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_INDEXED = prove
 (`!s. convex hull s =
        {y:real^N | ?k u x. (!i. 1 <= i /\ i <= k ==> &0 <= u i /\ x i IN s) /\
                            (sum (1..k) u = &1) /\
                            (vsum (1..k) (\i. u i % x i) = y)}`,
  GEN_TAC THEN MATCH_MP_TAC HULL_UNIQUE THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`1`; `\i:num. &1`; `\i:num. x:real^N`] THEN
    ASM_SIMP_TAC[FINITE_RULES; IN_SING; SUM_SING; VECTOR_MUL_LID; VSUM_SING;
                 REAL_POS; NUMSEG_SING];
    ALL_TAC;
    REWRITE_TAC[CONVEX_INDEXED; SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MESON_TAC[]] THEN
  REWRITE_TAC[convex; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`k1:num`; `u1:num->real`; `x1:num->real^N`;
    `k2:num`; `u2:num->real`; `x2:num->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `k1 + k2:num` THEN
  EXISTS_TAC `\i:num. if i <= k1 then u * u1(i) else v * u2(i - k1):real` THEN
  EXISTS_TAC `\i:num. if i <= k1 then x1(i) else x2(i - k1):real^N` THEN
  ASM_SIMP_TAC[NUMSEG_ADD_SPLIT; ARITH_RULE `1 <= x + 1 /\ x < x + 1`;
   IN_NUMSEG; SUM_UNION; VSUM_UNION; FINITE_NUMSEG; DISJOINT_NUMSEG;
   ARITH_RULE `k1 + 1 <= i ==> ~(i <= k1)`] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] NUMSEG_OFFSET_IMAGE] THEN
  ASM_SIMP_TAC[SUM_IMAGE; VSUM_IMAGE; EQ_ADD_LCANCEL; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[o_DEF; ADD_SUB2; SUM_LMUL; VSUM_LMUL; GSYM VECTOR_MUL_ASSOC;
               FINITE_NUMSEG; REAL_MUL_RID] THEN
  ASM_MESON_TAC[REAL_LE_MUL; ARITH_RULE
    `i <= k1 + k2 /\ ~(i <= k1) ==> 1 <= i - k1 /\ i - k1 <= k2`]);;

(* ------------------------------------------------------------------------- *)
(* Another formulation from Lars Schewe.                                     *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_EXPLICIT = prove
  (`!p. convex hull p =
        {y:real^N | ?s u. FINITE s /\ s SUBSET p /\
             (!x. x IN s ==> &0 <= u x) /\
             sum s u = &1 /\ vsum s (\v. u v % v) = y}`,
   REWRITE_TAC[CONVEX_HULL_INDEXED;EXTENSION;IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MAP_EVERY  EXISTS_TAC [`IMAGE (x':num->real^N) (1..k)`;
                           `\v:real^N.sum {i | i IN (1..k) /\ x' i = v} u`]
    THEN ASM_SIMP_TAC[FINITE_IMAGE;FINITE_NUMSEG;IN_IMAGE] THEN
    REPEAT STRIP_TAC THENL
    [REWRITE_TAC[IMAGE;SUBSET;IN_ELIM_THM;IN_NUMSEG] THEN
       ASM_MESON_TAC[];
     MATCH_MP_TAC SUM_POS_LE THEN
       ASM_SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;IN_ELIM_THM;IN_NUMSEG];
     ASM_SIMP_TAC[GSYM SUM_IMAGE_GEN;FINITE_IMAGE;FINITE_NUMSEG];
     FIRST_X_ASSUM (fun th -> REWRITE_TAC[GSYM th]) THEN
     ASM_SIMP_TAC[GSYM VSUM_IMAGE_GEN;FINITE_IMAGE;
                  FINITE_NUMSEG;VSUM_VMUL;FINITE_RESTRICT] THEN
       MP_TAC (ISPECL [`x':num->real^N`;`\i:num.u i % (x' i):real^N`;`(1..k)`]
                      (GSYM VSUM_IMAGE_GEN)) THEN
       ASM_SIMP_TAC[FINITE_NUMSEG]];ALL_TAC] THEN
   STRIP_ASSUME_TAC (ASM_REWRITE_RULE [ASSUME `FINITE (s:real^N->bool)`]
    (ISPEC `s:real^N->bool` FINITE_INDEX_NUMSEG)) THEN
   MAP_EVERY EXISTS_TAC [`CARD (s:real^N->bool)`;
                         `(u:real^N->real) o (f:num->real^N)`;
                         `(f:num->real^N)`] THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC[o_DEF] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM SUBST1_TAC THEN
      REWRITE_TAC[IN_IMAGE;IN_NUMSEG] THEN
      ASM_MESON_TAC[];
    MATCH_MP_TAC (REWRITE_RULE [SUBSET]
      (ASSUME `(s:real^N->bool) SUBSET p`)) THEN
      FIRST_ASSUM SUBST1_TAC THEN
      REWRITE_TAC[IN_IMAGE;IN_NUMSEG] THEN
      ASM_MESON_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum (s:real^N->bool) u` THEN
      CONJ_TAC THENL [ALL_TAC;ASM_REWRITE_TAC[]] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [ASSUME `(s:real^N->bool) = IMAGE f (1..CARD s)`] THEN
      MATCH_MP_TAC (GSYM SUM_IMAGE) THEN
      ASM_MESON_TAC[];
    REWRITE_TAC[MESON [o_THM;FUN_EQ_THM]
     `(\i:num. (u o f) i % f i) = (\v:real^N. u v % v) o f`] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `vsum (s:real^N->bool) (\v. u v % v)` THEN
      CONJ_TAC THENL [ALL_TAC;ASM_REWRITE_TAC[]] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [ASSUME `(s:real^N->bool) = IMAGE f (1..CARD s)`] THEN
      MATCH_MP_TAC (GSYM VSUM_IMAGE) THEN
      ASM SET_TAC[FINITE_NUMSEG]]);;

let CONVEX_HULL_FINITE = prove
 (`!s:real^N->bool.
        convex hull s =
          {y | ?u. (!x. x IN s ==> &0 <= u x) /\
                   sum s u = &1 /\
                   vsum s (\x. u x % x) = y}`,
  GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `f:real^N->real`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `\x:real^N. if x IN t then f x else &0` THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; VECTOR_MUL_LZERO] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET; GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`] THEN
    REWRITE_TAC[REAL_LE_REFL; COND_ID];
    X_GEN_TAC `f:real^N->real` THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH] THEN STRIP_TAC THEN
    EXISTS_TAC `support (+) (f:real^N->real) s` THEN
    EXISTS_TAC `f:real^N->real` THEN
    MP_TAC(ASSUME `sum s (f:real^N->real) = &1`) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [sum] THEN
    REWRITE_TAC[iterate] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[NEUTRAL_REAL_ADD; REAL_OF_NUM_EQ; ARITH] THEN
    DISCH_THEN(K ALL_TAC) THEN
    UNDISCH_TAC `sum s (f:real^N->real) = &1` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM SUM_SUPPORT] THEN
    ASM_CASES_TAC `support (+) (f:real^N->real) s = {}` THEN
    ASM_SIMP_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH] THEN
    DISCH_TAC THEN REWRITE_TAC[SUPPORT_SUBSET] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[support; IN_ELIM_THM]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[SUPPORT_SUBSET] THEN
    REWRITE_TAC[support; IN_ELIM_THM; NEUTRAL_REAL_ADD] THEN
    MESON_TAC[VECTOR_MUL_LZERO]]);;

let CONVEX_HULL_UNION_EXPLICIT = prove
 (`!s t:real^N->bool.
        convex s /\ convex t
        ==> convex hull (s UNION t) =
             s UNION t UNION
             {(&1 - u) % x + u % y | x IN s /\ y IN t /\ &0 <= u /\ u <= &1}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_EXPLICIT] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `u:real^N->bool`; `f:real^N->real`] THEN
    REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    SUBST1_TAC(SET_RULE `u:real^N->bool = (u INTER s) UNION (u DIFF s)`) THEN
    ASM_SIMP_TAC[SUM_UNION; VSUM_UNION; FINITE_INTER; FINITE_DIFF;
                 SET_RULE `DISJOINT (u INTER s) (u DIFF s)`] THEN
    ASM_CASES_TAC `sum (u INTER s) (f:real^N->real) = &0` THENL
     [SUBGOAL_THEN `!x. x IN (u INTER s) ==> (f:real^N->real) x = &0`
      ASSUME_TAC THENL
       [ASM_MESON_TAC[SUM_POS_EQ_0; FINITE_INTER; IN_INTER];
        ASM_SIMP_TAC[VECTOR_MUL_LZERO; VSUM_0] THEN
        REWRITE_TAC[VECTOR_ADD_LID; REAL_ADD_LID] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
        REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ1_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_EXPLICIT]) THEN
        ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `sum (u DIFF s) (f:real^N->real) = &0` THENL
     [SUBGOAL_THEN `!x. x IN (u DIFF s) ==> (f:real^N->real) x = &0`
      ASSUME_TAC THENL
       [ASM_MESON_TAC[SUM_POS_EQ_0; FINITE_DIFF; IN_DIFF];
        ASM_SIMP_TAC[VECTOR_MUL_LZERO; VSUM_0] THEN
        REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
        REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_EXPLICIT]) THEN
        ASM_SIMP_TAC[FINITE_INTER; IN_INTER] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`vsum(u INTER s) (\v:real^N. (f v / sum(u INTER s) f) % v)`;
      `sum(u DIFF s) (f:real^N->real)`;
      `vsum(u DIFF s) (\v:real^N. (f v / sum(u DIFF s) f) % v)`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_EXPLICIT]) THEN
      ASM_SIMP_TAC[INTER_SUBSET; FINITE_INTER; SUM_POS_LE; REAL_LE_DIV;
                   IN_INTER; real_div; SUM_RMUL; REAL_MUL_RINV];
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_EXPLICIT]) THEN
      ASM_SIMP_TAC[SUBSET_DIFF; FINITE_DIFF; SUM_POS_LE; REAL_LE_DIV;
                   IN_DIFF; real_div; SUM_RMUL; REAL_MUL_RINV] THEN
      ASM SET_TAC[];
      ASM_SIMP_TAC[SUM_POS_LE; IN_DIFF; FINITE_DIFF];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `a + b = &1 ==> &0 <= a ==> b <= &1`)) THEN
      ASM_SIMP_TAC[SUM_POS_LE; IN_INTER; FINITE_INTER];
      ASM_SIMP_TAC[GSYM VSUM_LMUL; FINITE_INTER; FINITE_DIFF] THEN
      SIMP_TAC[VECTOR_MUL_ASSOC; REAL_ARITH `a * b / c:real = a / c * b`] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `a + b = &1 ==> &1 - b = a`)) THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_MUL_LID]];
    REWRITE_TAC[GSYM UNION_ASSOC] THEN ONCE_REWRITE_TAC[UNION_SUBSET] THEN
    REWRITE_TAC[HULL_SUBSET] THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `u:real`; `y:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] CONVEX_CONVEX_HULL) THEN
    ASM_SIMP_TAC[HULL_INC; IN_UNION]]);;

let CONVEX_HULL_UNION_NONEMPTY_EXPLICIT = prove
 (`!s t:real^N->bool.
        convex s /\ ~(s = {}) /\ convex t /\ ~(t = {})
        ==> convex hull (s UNION t) =
             {(&1 - u) % x + u % y | x IN s /\ y IN t /\ &0 <= u /\ u <= &1}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONVEX_HULL_UNION_EXPLICIT] THEN
  SIMP_TAC[SET_RULE `s UNION t UNION u = u <=> s SUBSET u /\ t SUBSET u`] THEN
  CONJ_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN
  DISCH_TAC THENL
   [MAP_EVERY EXISTS_TAC [`z:real^N`; `&0`] THEN
    REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; REAL_POS; VECTOR_MUL_LZERO;
                VECTOR_ADD_RID] THEN
    ASM SET_TAC[];
    SUBGOAL_THEN `?a:real^N. a IN s` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`&1`; `z:real^N`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN VECTOR_ARITH_TAC]);;

let CONVEX_HULL_UNION_UNIONS = prove
 (`!f s:real^N->bool.
        convex(UNIONS f) /\ ~(f = {})
        ==> convex hull (s UNION UNIONS f) =
            UNIONS {convex hull (s UNION t) | t IN f}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_SIMP_TAC[UNION_EMPTY; HULL_P; UNIONS_SUBSET] THEN
    X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull u:real^N->bool` THEN
    REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `UNIONS f :real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[UNION_EMPTY] THEN
    SUBGOAL_THEN `?u:real^N->bool. u IN f` CHOOSE_TAC THENL
     [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull (s UNION u:real^N->bool)` THEN
    ASM_SIMP_TAC[HULL_MONO; SUBSET_UNION] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [HULL_UNION_LEFT] THEN
  ASM_SIMP_TAC[CONVEX_HULL_UNION_NONEMPTY_EXPLICIT; CONVEX_HULL_EQ_EMPTY;
               CONVEX_CONVEX_HULL] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_UNIONS] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `u:real^N->bool`] THEN DISCH_TAC THEN
  X_GEN_TAC `y:real^N` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] CONVEX_CONVEX_HULL) THEN
  ASM_MESON_TAC[HULL_MONO; IN_UNION; SUBSET; HULL_INC]);;

(* ------------------------------------------------------------------------- *)
(* A stepping theorem for that expansion.                                    *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_FINITE_STEP = prove
 (`((?u. (!x. x IN {} ==> &0 <= u x) /\
         sum {} u = w /\
         vsum {} (\x. u(x) % x) = y) <=> w = &0 /\ y = vec 0) /\
   (FINITE(s:real^N->bool)
    ==> ((?u. (!x. x IN (a INSERT s) ==> &0 <= u x) /\
              sum (a INSERT s) u = w /\
              vsum (a INSERT s) (\x. u(x) % x) = y) <=>
         ?v. &0 <= v /\
             ?u. (!x. x IN s ==> &0 <= u x) /\
              sum s u = w - v /\
              vsum s (\x. u(x) % x) = y - v % a))`,
  MP_TAC(ISPEC `\x:real^N y:real. &0 <= y` AFFINE_HULL_FINITE_STEP_GEN) THEN
  SIMP_TAC[REAL_ARITH `&0 <= x / &2 <=> &0 <= x`; REAL_LE_ADD] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM]);;

(* ------------------------------------------------------------------------- *)
(* Hence some special cases.                                                 *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_2 = prove
 (`!a b. convex hull {a,b} =
         {u % a + v % b | &0 <= u /\ &0 <= v /\ u + v = &1}`,
  SIMP_TAC[CONVEX_HULL_FINITE; FINITE_INSERT; FINITE_RULES] THEN
  SIMP_TAC[CONVEX_HULL_FINITE_STEP; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[REAL_ARITH `x - y = z:real <=> x = y + z`;
              VECTOR_ARITH `x - y = z:real^N <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN SET_TAC[]);;

let CONVEX_HULL_2_ALT = prove
 (`!a b. convex hull {a,b} = {a + u % (b - a) | &0 <= u /\ u <= &1}`,
  ONCE_REWRITE_TAC[SET_RULE `{a,b} = {b,a}`] THEN
  REWRITE_TAC[CONVEX_HULL_2; EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_ADD_ASSOC; CONJ_ASSOC] THEN
  REWRITE_TAC[TAUT `(a /\ x + y = &1) /\ b <=> x + y = &1 /\ a /\ b`] THEN
  REWRITE_TAC[REAL_ARITH `x + y = &1 <=> y = &1 - x`; UNWIND_THM2] THEN
  REPEAT GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  BINOP_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let CONVEX_HULL_3 = prove
 (`convex hull {a,b,c} =
    { u % a + v % b + w % c |
      &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1}`,
  SIMP_TAC[CONVEX_HULL_FINITE; FINITE_INSERT; FINITE_RULES] THEN
  SIMP_TAC[CONVEX_HULL_FINITE_STEP; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[REAL_ARITH `x - y = z:real <=> x = y + z`;
              VECTOR_ARITH `x - y = z:real^N <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN SET_TAC[]);;

let CONVEX_HULL_3_ALT = prove
 (`!a b c. convex hull {a,b,c} =
                {a + u % (b - a) + v % (c - a) |
                   &0 <= u /\ &0 <= v /\ u + v <= &1}`,
  ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,c,a}`] THEN
  REWRITE_TAC[CONVEX_HULL_3; EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_ADD_ASSOC; CONJ_ASSOC] THEN
  REWRITE_TAC[TAUT `(a /\ x + y = &1) /\ b <=> x + y = &1 /\ a /\ b`] THEN
  REWRITE_TAC[REAL_ARITH `x + y = &1 <=> y = &1 - x`; UNWIND_THM2] THEN
  REPEAT GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  BINOP_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let CONVEX_HULL_SUMS = prove
 (`!s t:real^N->bool.
        convex hull {x + y | x IN s /\ y IN t} =
        {x + y | x IN convex hull s /\ y IN convex hull t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    SIMP_TAC[CONVEX_SUMS; CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[HULL_INC];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CONVEX_HULL_INDEXED] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`k1:num`; `u1:num->real`; `x1:num->real^N`;
      `k2:num`; `u2:num->real`; `x2:num->real^N`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `x + y:real^N =
      vsum(1..k1) (\i. vsum(1..k2) (\j. u1 i % u2 j % (x1 i + x2 j)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VSUM_ADD_NUMSEG] THEN
      ASM_SIMP_TAC[VSUM_LMUL; VSUM_RMUL; VECTOR_MUL_LID];
      REWRITE_TAC[VSUM_LMUL] THEN MATCH_MP_TAC CONVEX_VSUM THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; CONVEX_CONVEX_HULL; IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_VSUM THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; CONVEX_CONVEX_HULL; IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]]]);;

let AFFINE_HULL_PCROSS,CONVEX_HULL_PCROSS = (CONJ_PAIR o prove)
 (`(!s:real^M->bool t:real^N->bool.
        affine hull (s PCROSS t) =
        (affine hull s) PCROSS (affine hull t)) /\
   (!s:real^M->bool t:real^N->bool.
        convex hull (s PCROSS t) =
        (convex hull s) PCROSS (convex hull t))`,
  let lemma1 = prove
   (`!u v x y:real^M z:real^N.
       u + v = &1
          ==> pastecart z (u % x + v % y) =
              u % pastecart z x + v % pastecart z y /\
              pastecart (u % x + v % y) z =
              u % pastecart x z + v % pastecart y z`,
    REWRITE_TAC[PASTECART_ADD; GSYM PASTECART_CMUL] THEN
    SIMP_TAC[GSYM VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID])
  and lemma2 = prove
   (`INTERS {{x | pastecart x y IN u} | y IN t} =
     {x | !y. y IN t ==> pastecart x y IN u}`,
    REWRITE_TAC[INTERS_GSPEC; EXTENSION; IN_ELIM_THM] THEN SET_TAC[]) in
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN
      SIMP_TAC[AFFINE_PCROSS; AFFINE_AFFINE_HULL; HULL_SUBSET; PCROSS_MONO];
      REWRITE_TAC[SUBSET; FORALL_IN_PCROSS] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      MATCH_MP_TAC HULL_INDUCT THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        MATCH_MP_TAC HULL_INDUCT THEN CONJ_TAC THENL
         [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
          SUBGOAL_THEN `pastecart (x:real^M) (y:real^N) IN s PCROSS t` MP_TAC
          THENL [ASM_REWRITE_TAC[PASTECART_IN_PCROSS]; ALL_TAC] THEN
          REWRITE_TAC[HULL_INC];
          ALL_TAC];
        REWRITE_TAC[GSYM lemma2] THEN MATCH_MP_TAC AFFINE_INTERS THEN
        REWRITE_TAC[FORALL_IN_GSPEC]] THEN
      SIMP_TAC[affine; IN_ELIM_THM; lemma1;
               ONCE_REWRITE_RULE[affine] AFFINE_AFFINE_HULL]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN
      SIMP_TAC[CONVEX_PCROSS; CONVEX_CONVEX_HULL; HULL_SUBSET; PCROSS_MONO];
      REWRITE_TAC[SUBSET; FORALL_IN_PCROSS] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      MATCH_MP_TAC HULL_INDUCT THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        MATCH_MP_TAC HULL_INDUCT THEN CONJ_TAC THENL
         [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
          SUBGOAL_THEN `pastecart (x:real^M) (y:real^N) IN s PCROSS t` MP_TAC
          THENL [ASM_REWRITE_TAC[PASTECART_IN_PCROSS]; ALL_TAC] THEN
          REWRITE_TAC[HULL_INC];
          ALL_TAC];
        REWRITE_TAC[GSYM lemma2] THEN MATCH_MP_TAC CONVEX_INTERS THEN
        REWRITE_TAC[FORALL_IN_GSPEC]] THEN
      SIMP_TAC[convex; IN_ELIM_THM; lemma1;
               ONCE_REWRITE_RULE[convex] CONVEX_CONVEX_HULL]]]);;

(* ------------------------------------------------------------------------- *)
(* Relations among closure notions and corresponding hulls.                  *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_IMP_AFFINE = prove
 (`!s. subspace s ==> affine s`,
  REWRITE_TAC[subspace; affine] THEN MESON_TAC[]);;

let AFFINE_IMP_CONVEX = prove
 (`!s. affine s ==> convex s`,
  REWRITE_TAC[affine; convex] THEN MESON_TAC[]);;

let SUBSPACE_IMP_CONVEX = prove
 (`!s. subspace s ==> convex s`,
  MESON_TAC[SUBSPACE_IMP_AFFINE; AFFINE_IMP_CONVEX]);;

let AFFINE_HULL_SUBSET_SPAN = prove
 (`!s. (affine hull s) SUBSET (span s)`,
  GEN_TAC THEN REWRITE_TAC[span] THEN MATCH_MP_TAC HULL_ANTIMONO THEN
  REWRITE_TAC[SUBSET; IN; SUBSPACE_IMP_AFFINE]);;

let CONVEX_HULL_SUBSET_SPAN = prove
 (`!s. (convex hull s) SUBSET (span s)`,
  GEN_TAC THEN REWRITE_TAC[span] THEN MATCH_MP_TAC HULL_ANTIMONO THEN
  REWRITE_TAC[SUBSET; IN; SUBSPACE_IMP_CONVEX]);;

let CONVEX_HULL_SUBSET_AFFINE_HULL = prove
 (`!s. (convex hull s) SUBSET (affine hull s)`,
  GEN_TAC THEN REWRITE_TAC[span] THEN MATCH_MP_TAC HULL_ANTIMONO THEN
  REWRITE_TAC[SUBSET; IN; AFFINE_IMP_CONVEX]);;

let COLLINEAR_CONVEX_HULL_COLLINEAR = prove
 (`!s:real^N->bool. collinear(convex hull s) <=> collinear s`,
  MESON_TAC[COLLINEAR_SUBSET; HULL_SUBSET; SUBSET_TRANS;
            COLLINEAR_AFFINE_HULL_COLLINEAR; CONVEX_HULL_SUBSET_AFFINE_HULL]);;

let AFFINE_SPAN = prove
 (`!s. affine(span s)`,
  SIMP_TAC[SUBSPACE_IMP_AFFINE; SUBSPACE_SPAN]);;

let CONVEX_SPAN = prove
 (`!s. convex(span s)`,
  SIMP_TAC[SUBSPACE_IMP_CONVEX; SUBSPACE_SPAN]);;

let AFFINE_EQ_SUBSPACE = prove
 (`!s:real^N->bool. vec 0 IN s ==> (affine s <=> subspace s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[subspace; affine] THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN STRIP_TAC THEN
    SUBST1_TAC(VECTOR_ARITH `c % x:real^N = c % x + (&1 - c) % vec 0`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
    STRIP_TAC THEN SUBST1_TAC(VECTOR_ARITH
     `x + y:real^N = &2 % (&1 / &2 % x + &1 / &2 % y)`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let AFFINE_IMP_SUBSPACE = prove
 (`!s. affine s /\ vec 0 IN s ==> subspace s`,
  SIMP_TAC[GSYM AFFINE_EQ_SUBSPACE]);;

let AFFINE_HULL_EQ_SPAN = prove
 (`!s:real^N->bool. (vec 0) IN affine hull s ==> affine hull s = span s`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[AFFINE_HULL_SUBSET_SPAN] THEN
  REWRITE_TAC[SUBSET] THEN MATCH_MP_TAC SPAN_INDUCT THEN
  ASM_REWRITE_TAC[SUBSET; subspace; IN_ELIM_THM; HULL_INC] THEN
  REPEAT STRIP_TAC THENL
   [SUBST1_TAC(VECTOR_ARITH
     `x + y:real^N = &2 % (&1 / &2 % x + &1 / &2 % y) + --(&1) % vec 0`) THEN
    MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    SUBST1_TAC(VECTOR_ARITH
     `c % x:real^N = c % x + (&1 - c) % vec 0`) THEN
    MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let CLOSED_AFFINE = prove
 (`!s:real^N->bool. affine s ==> closed s`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  SUBGOAL_THEN `affine (IMAGE (\x:real^N. --a + x) s)
                ==> closed (IMAGE (\x:real^N. --a + x) s)`
  MP_TAC THENL
   [DISCH_THEN(fun th -> MATCH_MP_TAC CLOSED_SUBSPACE THEN MP_TAC th) THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC AFFINE_EQ_SUBSPACE THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[AFFINE_TRANSLATION_EQ; CLOSED_TRANSLATION_EQ]]);;

let CLOSED_AFFINE_HULL = prove
 (`!s. closed(affine hull s)`,
  SIMP_TAC[CLOSED_AFFINE; AFFINE_AFFINE_HULL]);;

let CLOSURE_SUBSET_AFFINE_HULL = prove
 (`!s. closure s SUBSET affine hull s`,
  GEN_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
  REWRITE_TAC[CLOSED_AFFINE_HULL; HULL_SUBSET]);;

let AFFINE_HULL_CLOSURE = prove
 (`!s:real^N->bool. affine hull (closure s) = affine hull s`,
  GEN_TAC THEN MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[CLOSURE_SUBSET_AFFINE_HULL; AFFINE_AFFINE_HULL] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]);;

let AFFINE_HULL_EQ_SPAN_EQ = prove
 (`!s:real^N->bool. (affine hull s = span s) <=> (vec 0) IN affine hull s`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[SPAN_0; AFFINE_HULL_EQ_SPAN]);;

let AFFINE_DEPENDENT_IMP_DEPENDENT = prove
 (`!s. affine_dependent s ==> dependent s`,
  REWRITE_TAC[affine_dependent; dependent] THEN
  MESON_TAC[SUBSET; AFFINE_HULL_SUBSET_SPAN]);;

let DEPENDENT_AFFINE_DEPENDENT_CASES = prove
 (`!s:real^N->bool.
        dependent s <=> affine_dependent s \/ (vec 0) IN affine hull s`,
  REWRITE_TAC[DEPENDENT_EXPLICIT; AFFINE_DEPENDENT_EXPLICIT;
              AFFINE_HULL_EXPLICIT_ALT; IN_ELIM_THM] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[OR_EXISTS_THM] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN
  ASM_CASES_TAC `FINITE(t:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN
   (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC))
  THENL
   [ASM_CASES_TAC `sum t (u:real^N->real) = &0` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISJ2_TAC THEN EXISTS_TAC `\v:real^N. inv(sum t u) * u v` THEN
    ASM_SIMP_TAC[SUM_LMUL; VSUM_LMUL; GSYM VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO; REAL_MUL_LINV];
    EXISTS_TAC `u:real^N->real` THEN ASM_MESON_TAC[];
    EXISTS_TAC `u:real^N->real` THEN
    ASM_REWRITE_TAC[SET_RULE
     `(?v. v IN t /\ ~p v) <=> ~(!v. v IN t ==> p v)`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x = &1 ==> x = &0 ==> F`)) THEN
    ASM_MESON_TAC[SUM_EQ_0]]);;

let DEPENDENT_IMP_AFFINE_DEPENDENT = prove
 (`!a:real^N s. dependent {x - a | x IN s} /\ ~(a IN s)
                ==> affine_dependent(a INSERT s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[DEPENDENT_EXPLICIT; AFFINE_DEPENDENT_EXPLICIT] THEN
  REWRITE_TAC[SIMPLE_IMAGE; CONJ_ASSOC; FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `a /\ x = IMAGE f s /\ b <=> x = IMAGE f s /\ a /\ b`] THEN
  REWRITE_TAC[UNWIND_THM2; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` (X_CHOOSE_THEN `t:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[VSUM_IMAGE; VECTOR_ARITH `x - a:real^N = y - a <=> x = y`] THEN
  ASM_SIMP_TAC[o_DEF; VECTOR_SUB_LDISTRIB; VSUM_SUB; VSUM_RMUL] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(a:real^N) INSERT t`;
    `\x. if x = a then --sum t (\x. u (x - a))
         else (u:real^N->real) (x - a)`] THEN
  ASM_REWRITE_TAC[FINITE_INSERT; SUBSET_REFL] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x = y ==> --x + y = &0`) THEN
    MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[];
    EXISTS_TAC `x:real^N` THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC(VECTOR_ARITH
     `!s. s - t % a = vec 0 /\ s = u ==> --t % a + u = vec 0`) THEN
    EXISTS_TAC `vsum t (\x:real^N. u(x - a) % x)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let AFFINE_DEPENDENT_BIGGERSET = prove
 (`!s:real^N->bool.
        (FINITE s ==> CARD s >= dimindex(:N) + 2) ==> affine_dependent s`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[CARD_CLAUSES; ARITH_RULE `~(0 >= n + 2)`; FINITE_RULES] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; IN_DELETE] THEN
  REWRITE_TAC[ARITH_RULE `SUC x >= n + 2 <=> x > n`] THEN DISCH_TAC THEN
  MATCH_MP_TAC DEPENDENT_IMP_AFFINE_DEPENDENT THEN
  REWRITE_TAC[IN_DELETE] THEN MATCH_MP_TAC DEPENDENT_BIGGERSET THEN
  REWRITE_TAC[SET_RULE `{x - a:real^N | x | x IN s /\ ~(x = a)} =
                        IMAGE (\x. x - a) (s DELETE a)`] THEN
  ASM_SIMP_TAC[FINITE_IMAGE_INJ_EQ;
               VECTOR_ARITH `x - a = y - a <=> x:real^N = y`;
               CARD_IMAGE_INJ]);;

let AFFINE_DEPENDENT_BIGGERSET_GENERAL = prove
 (`!s:real^N->bool. (FINITE s ==> CARD s >= dim s + 2) ==> affine_dependent s`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[CARD_CLAUSES; ARITH_RULE `~(0 >= n + 2)`; FINITE_RULES] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; IN_DELETE] THEN
  REWRITE_TAC[ARITH_RULE `SUC x >= n + 2 <=> x > n`] THEN DISCH_TAC THEN
  MATCH_MP_TAC DEPENDENT_IMP_AFFINE_DEPENDENT THEN
  REWRITE_TAC[IN_DELETE] THEN
  MATCH_MP_TAC DEPENDENT_BIGGERSET_GENERAL THEN
  REWRITE_TAC[SET_RULE `{x - a:real^N | x | x IN s /\ ~(x = a)} =
                        IMAGE (\x. x - a) (s DELETE a)`] THEN
  ASM_SIMP_TAC[FINITE_IMAGE_INJ_EQ; FINITE_DELETE;
               VECTOR_ARITH `x - a = y - a <=> x:real^N = y`;
               CARD_IMAGE_INJ] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) THEN
  ASM_REWRITE_TAC[FINITE_DELETE] THEN
  MATCH_MP_TAC(ARITH_RULE `c:num <= b ==> (a > b ==> a > c)`) THEN
  MATCH_MP_TAC SUBSET_LE_DIM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  SIMP_TAC[SPAN_SUB; SPAN_SUPERSET; IN_INSERT]);;

let AFFINE_INDEPENDENT_IMP_FINITE = prove
 (`!s:real^N->bool. ~(affine_dependent s) ==> FINITE s`,
  MESON_TAC[AFFINE_DEPENDENT_BIGGERSET]);;

let AFFINE_INDEPENDENT_CARD_LE = prove
 (`!s:real^N->bool. ~(affine_dependent s) ==> CARD s <= dimindex(:N) + 1`,
  REWRITE_TAC[ARITH_RULE `s <= n + 1 <=> ~(n + 2 <= s)`; CONTRAPOS_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AFFINE_DEPENDENT_BIGGERSET THEN
  ASM_REWRITE_TAC[GE]);;

let AFFINE_INDEPENDENT_CONVEX_AFFINE_HULL = prove
 (`!s t:real^N->bool.
        ~affine_dependent s /\ t SUBSET s
        ==> convex hull t = affine hull t INTER convex hull s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  SUBGOAL_THEN `FINITE(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `ct SUBSET a /\ ct SUBSET cs /\ a INTER cs SUBSET ct
    ==> ct = a INTER cs`) THEN
  ASM_SIMP_TAC[HULL_MONO; CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
  REWRITE_TAC[SUBSET; IN_INTER; CONVEX_HULL_FINITE; AFFINE_HULL_FINITE] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `v:real^N->real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `u:real^N->real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
    [AFFINE_DEPENDENT_EXPLICIT]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`;
        `\x:real^N. if x IN t then v x - u x:real else v x`]) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN REWRITE_TAC[MESON[]
   `(if p then a else b) % x = if p then a % x else b % x`] THEN
  ASM_SIMP_TAC[VSUM_CASES; SUM_CASES; SET_RULE
   `t SUBSET s ==> {x | x IN s /\ x IN t} = t`] THEN
  ASM_SIMP_TAC[GSYM DIFF; SUM_DIFF; VSUM_DIFF; VECTOR_SUB_RDISTRIB;
               SUM_SUB; VSUM_SUB] THEN
  REWRITE_TAC[REAL_ARITH `a - b + b - a = &0`; NOT_EXISTS_THM;
              VECTOR_ARITH `a - b + b - a:real^N = vec 0`] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ASM_REWRITE_TAC[REAL_SUB_0] THEN ASM SET_TAC[]);;

let DISJOINT_AFFINE_HULL = prove
 (`!s t u:real^N->bool.
        ~affine_dependent s /\ t SUBSET s /\ u SUBSET s /\ DISJOINT t u
        ==> DISJOINT (affine hull t) (affine hull u)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  SUBGOAL_THEN `FINITE(t:real^N->bool) /\ FINITE (u:real^N->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[IN_DISJOINT; AFFINE_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `a:real^N->real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `b:real^N->real` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
    [AFFINE_DEPENDENT_EXPLICIT]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`s:real^N->bool`;
    `\x:real^N. if x IN t then a x else if x IN u then --(b x) else &0`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN REWRITE_TAC[MESON[]
   `(if p then a else b) % x = if p then a % x else b % x`] THEN
  ASM_SIMP_TAC[SUM_CASES; SUBSET_REFL; VSUM_CASES; GSYM DIFF; SUM_DIFF;
      VSUM_DIFF; SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`] THEN
  ASM_SIMP_TAC[SUM_0; VSUM_0; VECTOR_MUL_LZERO; SUM_NEG; VSUM_NEG;
    VECTOR_MUL_LNEG; SET_RULE `DISJOINT t u ==> ~(x IN t /\ x IN u)`] THEN
  REWRITE_TAC[EMPTY_GSPEC; SUM_CLAUSES; VSUM_CLAUSES] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
  UNDISCH_TAC `sum t (a:real^N->real) = &1` THEN
  ASM_CASES_TAC `!x:real^N. x IN t ==> a x = &0` THEN
  ASM_SIMP_TAC[SUM_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

let AFFINE_INDEPENDENT_SPAN_EQ = prove
 (`!s. ~(affine_dependent s) /\ CARD s = dimindex(:N) + 1
       ==> affine hull s = (:real^N)`,
  MATCH_MP_TAC SET_PROVE_CASES THEN
  REWRITE_TAC[CARD_CLAUSES; ARITH_RULE `~(0 = n + 1)`] THEN
  SIMP_TAC[IMP_CONJ; AFFINE_INDEPENDENT_IMP_FINITE; MESON[HAS_SIZE]
   `FINITE s ==> (CARD s = n <=> s HAS_SIZE n)`] THEN
  X_GEN_TAC `orig:real^N` THEN GEOM_ORIGIN_TAC `orig:real^N` THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; IN_INSERT; SPAN_INSERT_0; HULL_INC] THEN
  SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_INSERT; IMP_CONJ] THEN
  REWRITE_TAC[ARITH_RULE `SUC n = m + 1 <=> n = m`; GSYM UNIV_SUBSET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
  ASM_REWRITE_TAC[DIM_UNIV; SUBSET_UNIV; LE_REFL; independent] THEN
  UNDISCH_TAC `~affine_dependent((vec 0:real^N) INSERT s)` THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC DEPENDENT_IMP_AFFINE_DEPENDENT THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO; SET_RULE `{x | x IN s} = s`]);;

let AFFINE_INDEPENDENT_SPAN_GT = prove
 (`!s:real^N->bool.
        ~(affine_dependent s) /\ dimindex(:N) < CARD s
        ==> affine hull s = (:real^N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AFFINE_INDEPENDENT_SPAN_EQ THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `s:real^N->bool` AFFINE_DEPENDENT_BIGGERSET) THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN ASM_ARITH_TAC);;

let EMPTY_INTERIOR_AFFINE_HULL = prove
 (`!s:real^N->bool.
        FINITE s /\ CARD(s) <= dimindex(:N)
        ==> interior(affine hull s) = {}`,
  REWRITE_TAC[IMP_CONJ] THEN  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[AFFINE_HULL_EMPTY; INTERIOR_EMPTY] THEN
  SUBGOAL_THEN
   `!x s:real^N->bool n.
        ~(x IN s) /\ (x INSERT s) HAS_SIZE n /\ n <= dimindex(:N)
        ==> interior(affine hull(x INSERT s)) = {}`
   (fun th -> MESON_TAC[th; HAS_SIZE; FINITE_INSERT]) THEN
  X_GEN_TAC `orig:real^N` THEN GEOM_ORIGIN_TAC `orig:real^N` THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; IN_INSERT; SPAN_INSERT_0; HULL_INC] THEN
  REWRITE_TAC[HAS_SIZE; FINITE_INSERT; IMP_CONJ] THEN
  SIMP_TAC[CARD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EMPTY_INTERIOR_LOWDIM THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `CARD(s:real^N->bool)` THEN
  ASM_SIMP_TAC[DIM_LE_CARD; DIM_SPAN] THEN ASM_ARITH_TAC);;

let EMPTY_INTERIOR_CONVEX_HULL = prove
 (`!s:real^N->bool.
        FINITE s /\ CARD(s) <= dimindex(:N)
        ==> interior(convex hull s) = {}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!t. s SUBSET t /\ t = {} ==> s = {}`) THEN
  EXISTS_TAC `interior(affine hull s):real^N->bool` THEN
  SIMP_TAC[SUBSET_INTERIOR; CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
  ASM_SIMP_TAC[EMPTY_INTERIOR_AFFINE_HULL]);;

let AFFINE_DEPENDENT_CHOOSE = prove
 (`!s a:real^N.
       ~(affine_dependent s)
       ==> (affine_dependent(a INSERT s) <=> ~(a IN s) /\ a IN affine hull s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(a:real^N) IN s` THEN
  ASM_SIMP_TAC[SET_RULE `a IN s ==> a INSERT s = s`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  EQ_TAC THENL
   [UNDISCH_TAC `~(affine_dependent(s:real^N->bool))` THEN
    ASM_SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT_FINITE; AFFINE_HULL_FINITE;
                 FINITE_INSERT; IN_ELIM_THM; SUM_CLAUSES; VSUM_CLAUSES] THEN
    DISCH_TAC THEN REWRITE_TAC[EXISTS_IN_INSERT] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` MP_TAC) THEN
    ASM_CASES_TAC `(u:real^N->real) a = &0` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[REAL_ADD_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^N->real`) THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_ARITH `ua + sa = &0 <=> sa = --ua`;
                   VECTOR_ARITH `va + sa:real^N = vec 0 <=> sa = --va`] THEN
      STRIP_TAC THEN EXISTS_TAC `(\x. --(inv(u a)) * u x):real^N->real` THEN
      ASM_SIMP_TAC[SUM_LMUL; GSYM VECTOR_MUL_ASSOC; VSUM_LMUL] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_MUL_LNEG] THEN
      REWRITE_TAC[REAL_ARITH `--a * --b:real = a * b`] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID]];
    DISCH_TAC THEN REWRITE_TAC[affine_dependent] THEN
    EXISTS_TAC `a:real^N` THEN
    ASM_SIMP_TAC[IN_INSERT; SET_RULE
     `~(a IN s) ==> (a INSERT s) DELETE a = s`]]);;

let AFFINE_INDEPENDENT_INSERT = prove
 (`!s a:real^N.
        ~(affine_dependent s) /\ ~(a IN affine hull s)
        ==> ~(affine_dependent(a INSERT s))`,
  SIMP_TAC[AFFINE_DEPENDENT_CHOOSE]);;

let AFFINE_HULL_EXPLICIT_UNIQUE = prove
 (`!s:real^N->bool u u'.
      ~(affine_dependent s) /\
      sum s u = &1 /\ sum s u' = &1 /\
      vsum s (\x. u x % x) = vsum s (\x. u' x % x)
      ==> !x. x IN s ==> u x = u' x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP AFFINE_DEPENDENT_EXPLICIT_FINITE) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(\x. u x - u' x):real^N->real`) THEN
  ASM_SIMP_TAC[VSUM_SUB; SUM_SUB; REAL_SUB_REFL; VECTOR_SUB_RDISTRIB;
               VECTOR_SUB_REFL; VECTOR_SUB_EQ; REAL_SUB_0] THEN
  MESON_TAC[]);;

let INDEPENDENT_IMP_AFFINE_DEPENDENT_0 = prove
 (`!s. independent s ==> ~(affine_dependent(vec 0 INSERT s))`,
  REWRITE_TAC[independent; DEPENDENT_AFFINE_DEPENDENT_CASES] THEN
  SIMP_TAC[DE_MORGAN_THM; AFFINE_INDEPENDENT_INSERT]);;

let AFFINE_INDEPENDENT_STDBASIS = prove
 (`~(affine_dependent
      ((vec 0:real^N) INSERT {basis i | 1 <= i /\ i <= dimindex (:N)}))`,
  SIMP_TAC[INDEPENDENT_IMP_AFFINE_DEPENDENT_0; INDEPENDENT_STDBASIS]);;

(* ------------------------------------------------------------------------- *)
(* Nonempty affine sets are translates of (unique) subspaces.                *)
(* ------------------------------------------------------------------------- *)

let AFFINE_TRANSLATION_SUBSPACE = prove
 (`!t:real^N->bool.
        affine t /\ ~(t = {}) <=> ?a s. subspace s /\ t = IMAGE (\x. a + x) s`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUBSPACE_IMP_NONEMPTY; IMAGE_EQ_EMPTY;
               AFFINE_TRANSLATION; SUBSPACE_IMP_AFFINE] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[TRANSLATION_GALOIS] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[UNWIND_THM2] THEN MATCH_MP_TAC AFFINE_IMP_SUBSPACE THEN
  ASM_REWRITE_TAC[AFFINE_TRANSLATION_EQ; IN_IMAGE] THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let AFFINE_TRANSLATION_UNIQUE_SUBSPACE = prove
 (`!t:real^N->bool.
        affine t /\ ~(t = {}) <=>
        ?!s. ?a. subspace s /\ t = IMAGE (\x. a + x) s`,
  GEN_TAC THEN REWRITE_TAC[AFFINE_TRANSLATION_SUBSPACE] THEN
  MATCH_MP_TAC(MESON[]
   `(!a a' s s'. P s a /\ P s' a' ==> s = s')
    ==> ((?a s. P s a) <=> (?!s. ?a. P s a))`) THEN
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[TRANSLATION_GALOIS] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ADD_ASSOC] THEN
  MATCH_MP_TAC SUBSPACE_TRANSLATION_SELF THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `--a' + a:real^N = --(a' - a)`] THEN
  MATCH_MP_TAC SUBSPACE_NEG THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `t = IMAGE (\x:real^N. a' + x) s'` THEN
  DISCH_THEN(MP_TAC o AP_TERM `\s. (a':real^N) IN s`) THEN
  REWRITE_TAC[IN_IMAGE; VECTOR_ARITH `a:real^N = a + x <=> x = vec 0`] THEN
  ASM_SIMP_TAC[UNWIND_THM2; SUBSPACE_0] THEN
  REWRITE_TAC[IN_IMAGE; VECTOR_ARITH `a':real^N = a + x <=> x = a' - a`] THEN
  REWRITE_TAC[UNWIND_THM2]);;

let AFFINE_TRANSLATION_SUBSPACE_EXPLICIT = prove
 (`!t:real^N->bool a.
        affine t /\ a IN t
        ==> subspace {x - a | x IN t} /\
            t = IMAGE (\x. a + x) {x - a | x IN t}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[AFFINE_DIFFS_SUBSPACE] THEN
  ASM_REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o] THEN
  REWRITE_TAC[o_DEF; VECTOR_SUB_ADD2; IMAGE_ID]);;

(* ------------------------------------------------------------------------- *)
(* If we take a slice out of a set, we can do it perpendicularly,            *)
(* with the normal vector to the slice parallel to the affine hull.          *)
(* ------------------------------------------------------------------------- *)

let AFFINE_PARALLEL_SLICE = prove
  (`!s a:real^N b.
       affine s
       ==> s INTER {x | a dot x <= b} = {} \/ s SUBSET {x | a dot x <= b} \/
           ?a' b'. ~(a' = vec 0) /\

                   s INTER {x | a' dot x <= b'} = s INTER {x | a dot x <= b} /\
                   s INTER {x | a' dot x = b'} = s INTER {x | a dot x = b} /\
                   !w. w IN s ==> (w + a') IN s`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `s INTER {x:real^N | a dot x = b} = {}` THENL
    [MATCH_MP_TAC(TAUT `~(~p /\ ~q) ==> p \/ q \/ r`) THEN
     REPEAT STRIP_TAC THEN SUBGOAL_THEN
      `?u v:real^N. u IN s /\ v IN s /\
                    a dot u <= b /\ ~(a dot v <= b)`
     STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `(a:real^N) dot u < b` ASSUME_TAC THENL
      [ASM_REWRITE_TAC[REAL_LT_LE] THEN ASM SET_TAC[]; ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
     REWRITE_TAC[NOT_IN_EMPTY; IN_INTER; NOT_FORALL_THM; IN_ELIM_THM] THEN
     EXISTS_TAC
      `u + (b - a dot u) / (a dot v - a dot u) % (v - u):real^N` THEN
     ASM_SIMP_TAC[IN_AFFINE_ADD_MUL_DIFF] THEN
     REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN
     REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
     DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
     REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN POP_ASSUM MP_TAC THEN
     GEN_GEOM_ORIGIN_TAC `z:real^N` ["a"; "a'"; "b'"; "w"] THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[VECTOR_ADD_RID; FORALL_IN_IMAGE] THEN
     REWRITE_TAC[DOT_RADD; REAL_ARITH `a + x <= a <=> x <= &0`] THEN
     SUBGOAL_THEN `subspace(s:real^N->bool) /\ span s = s`
     STRIP_ASSUME_TAC THENL
      [ASM_MESON_TAC[AFFINE_IMP_SUBSPACE; SPAN_EQ_SELF]; ALL_TAC] THEN
     MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`]
           ORTHOGONAL_SUBSPACE_DECOMP_EXISTS) THEN
     ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; orthogonal] THEN
     MAP_EVERY X_GEN_TAC [`a':real^N`; `a'':real^N`] THEN
     ASM_CASES_TAC `a':real^N = vec 0` THENL
      [ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN
       ASM_CASES_TAC `a'':real^N = a` THEN ASM_REWRITE_TAC[] THEN
       SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_LE_REFL];
       ALL_TAC] THEN
     STRIP_TAC THEN REPEAT DISJ2_TAC THEN
     EXISTS_TAC `a':real^N` THEN ASM_REWRITE_TAC[] THEN
     EXISTS_TAC `(a':real^N) dot z` THEN
     REPEAT(CONJ_TAC THENL
      [MATCH_MP_TAC(SET_RULE
        `(!x. x IN s ==> (p x <=> q x))
         ==> s INTER {x | p x} = s INTER {x | q x}`) THEN
       ASM_SIMP_TAC[DOT_LADD] THEN REAL_ARITH_TAC;
       ALL_TAC]) THEN
     X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
     EXISTS_TAC `x + a':real^N` THEN
     ASM_SIMP_TAC[SUBSPACE_ADD; VECTOR_ADD_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* Affine dimension.                                                         *)
(* ------------------------------------------------------------------------- *)

let MAXIMAL_AFFINE_INDEPENDENT_SUBSET = prove
 (`!s b:real^N->bool.
        b SUBSET s /\ ~(affine_dependent b) /\
        (!b'. b SUBSET b' /\ b' SUBSET s /\ ~(affine_dependent b') ==> b' = b)
        ==> s SUBSET (affine hull b)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `(!a. a IN t /\ ~(a IN s) ==> F) ==> t SUBSET s`) THEN
  X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a:real^N) INSERT b`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] HULL_INC)) THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_INSERT; INSERT_SUBSET] THEN
  ASM SET_TAC[]);;

let MAXIMAL_AFFINE_INDEPENDENT_SUBSET_AFFINE = prove
 (`!s b:real^N->bool.
        affine s /\ b SUBSET s /\ ~(affine_dependent b) /\
        (!b'. b SUBSET b' /\ b' SUBSET s /\ ~(affine_dependent b') ==> b' = b)
        ==> affine hull b = s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HULL_MONO; HULL_P];
    ASM_MESON_TAC[MAXIMAL_AFFINE_INDEPENDENT_SUBSET]]);;

let EXTEND_TO_AFFINE_BASIS = prove
 (`!s u:real^N->bool.
        ~(affine_dependent s) /\ s SUBSET u
        ==> ?t. ~(affine_dependent t) /\ s SUBSET t /\ t SUBSET u /\
                affine hull t = affine hull u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\n. ?t:real^N->bool. ~(affine_dependent t) /\ s SUBSET t /\
                                    t SUBSET u /\ CARD t = n`
   num_MAX) THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[SUBSET_REFL; AFFINE_INDEPENDENT_CARD_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HULL_MONO; HULL_P]; ALL_TAC] THEN
  MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
  MATCH_MP_TAC MAXIMAL_AFFINE_INDEPENDENT_SUBSET THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CARD(c:real^N->bool)`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^N->bool`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_LE THEN
  ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]);;

let AFFINE_BASIS_EXISTS = prove
 (`!s:real^N->bool.
      ?b. ~(affine_dependent b) /\ b SUBSET s /\
          affine hull b = affine hull s`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`{}:real^N->bool`; `s:real^N->bool`]
    EXTEND_TO_AFFINE_BASIS) THEN
  REWRITE_TAC[AFFINE_INDEPENDENT_EMPTY; EMPTY_SUBSET]);;

let aff_dim = new_definition
  `aff_dim s =
        @d:int. ?b. affine hull b = affine hull s /\ ~(affine_dependent b) /\
                    &(CARD b) = d + &1`;;

let AFF_DIM = prove
 (`!s. ?b. affine hull b = affine hull s /\
           ~(affine_dependent b) /\
           aff_dim s = &(CARD b) - &1`,
  GEN_TAC THEN
  REWRITE_TAC[aff_dim; INT_ARITH `y:int = x + &1 <=> x = y - &1`] THEN
  CONV_TAC SELECT_CONV THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
  MESON_TAC[AFFINE_BASIS_EXISTS]);;

let AFF_DIM_EMPTY = prove
 (`aff_dim {} = -- &1`,
  REWRITE_TAC[aff_dim; AFFINE_HULL_EMPTY; AFFINE_HULL_EQ_EMPTY] THEN
  REWRITE_TAC[UNWIND_THM2; AFFINE_INDEPENDENT_EMPTY; CARD_CLAUSES] THEN
  REWRITE_TAC[INT_ARITH `&0 = d + &1 <=> d:int = -- &1`; SELECT_REFL]);;

let AFF_DIM_AFFINE_HULL = prove
 (`!s. aff_dim(affine hull s) = aff_dim s`,
  REWRITE_TAC[aff_dim; HULL_HULL]);;

let AFF_DIM_TRANSLATION_EQ = prove
 (`!a:real^N s. aff_dim (IMAGE (\x. a + x) s) = aff_dim s`,
  REWRITE_TAC[aff_dim] THEN GEOM_TRANSLATE_TAC[] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a /\ b ==> ~c)`] THEN
  SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE; CARD_IMAGE_INJ;
           VECTOR_ARITH `a + x:real^N = a + y <=> x = y`]);;

add_translation_invariants [AFF_DIM_TRANSLATION_EQ];;

let AFFINE_INDEPENDENT_CARD_DIM_DIFFS = prove
 (`!s a:real^N.
        ~affine_dependent s /\ a IN s
        ==> CARD s = dim {x - a | x IN s} + 1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  MATCH_MP_TAC(ARITH_RULE `~(s = 0) /\ v = s - 1 ==> s = v + 1`) THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC DIM_UNIQUE THEN
  EXISTS_TAC `{b - a:real^N |b| b IN (s DELETE a)}` THEN REPEAT CONJ_TAC THENL
   [SET_TAC[];
    REWRITE_TAC[SIMPLE_IMAGE; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_CASES_TAC `x:real^N = a` THENL
     [ASM_REWRITE_TAC[VECTOR_SUB_REFL; SPAN_0];
      MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC[]];
    UNDISCH_TAC `~affine_dependent(s:real^N->bool)` THEN
    REWRITE_TAC[independent; CONTRAPOS_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s = (a:real^N) INSERT (s DELETE a)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC DEPENDENT_IMP_AFFINE_DEPENDENT THEN
    ASM_REWRITE_TAC[IN_DELETE];
    REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    SIMP_TAC[VECTOR_ARITH `x - a:real^N = y - a <=> x = y`] THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE]]);;

let AFF_DIM_DIM_AFFINE_DIFFS = prove
 (`!a:real^N s. affine s /\ a IN s ==> aff_dim s = &(dim {x - a | x IN s})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` AFF_DIM) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` MP_TAC) THEN
  ASM_CASES_TAC `b:real^N->bool = {}` THENL
   [ASM_MESON_TAC[AFFINE_HULL_EQ_EMPTY; NOT_IN_EMPTY]; ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[INT_EQ_SUB_RADD; INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^N`) THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `dim {x - c:real^N | x IN b} + 1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_CARD_DIM_DIFFS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `dim {x - c:real^N | x IN affine hull b} + 1` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[DIFFS_AFFINE_HULL_SPAN; DIM_SPAN]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `affine hull s:real^N->bool = s` SUBST1_TAC THENL
   [ASM_MESON_TAC[AFFINE_HULL_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_HULL_EQ; HULL_INC]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SIMP_TAC[VECTOR_ARITH `x - c:real^N = y - a <=> y = x + &1 % (a - c)`] THEN
  ASM_MESON_TAC[IN_AFFINE_ADD_MUL_DIFF]);;

let AFF_DIM_DIM_0 = prove
 (`!s:real^N->bool. vec 0 IN affine hull s ==> aff_dim s = &(dim s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `affine hull s:real^N->bool`]
    AFF_DIM_DIM_AFFINE_DIFFS) THEN
  ASM_REWRITE_TAC[AFFINE_AFFINE_HULL; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[AFF_DIM_AFFINE_HULL; SET_RULE `{x | x IN s} = s`] THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; DIM_SPAN]);;

let AFF_DIM_DIM_SUBSPACE = prove
 (`!s:real^N->bool. subspace s ==> aff_dim s = &(dim s)`,
  MESON_TAC[AFF_DIM_DIM_0; SUBSPACE_0; HULL_INC]);;

let AFF_DIM_LINEAR_IMAGE_LE = prove
 (`!f:real^M->real^N s. linear f ==> aff_dim(IMAGE f s) <= aff_dim s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  ASM_SIMP_TAC[AFFINE_HULL_LINEAR_IMAGE] THEN
  MP_TAC(ISPEC `s:real^M->bool` AFFINE_AFFINE_HULL) THEN
  SPEC_TAC(`affine hull s:real^M->bool`,`s:real^M->bool`) THEN
  GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; AFF_DIM_EMPTY; INT_LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^M`) THEN
  SUBGOAL_THEN `dim {x - f(a) |x| x IN IMAGE (f:real^M->real^N) s} <=
                dim {x - a | x IN s}`
  MP_TAC THENL
   [REWRITE_TAC[SET_RULE `{f x | x IN IMAGE g s} = {f (g x) | x IN s}`] THEN
    ASM_SIMP_TAC[GSYM LINEAR_SUB] THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN REWRITE_TAC[IMAGE_o] THEN
    MATCH_MP_TAC DIM_LINEAR_IMAGE_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    BINOP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC AFF_DIM_DIM_AFFINE_DIFFS THEN
    ASM_SIMP_TAC[AFFINE_LINEAR_IMAGE; FUN_IN_IMAGE]]);;

let AFF_DIM_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> aff_dim(IMAGE f s) = aff_dim s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[AFF_DIM_LINEAR_IMAGE_LE]; ALL_TAC] THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC
   `aff_dim(IMAGE (g:real^N->real^M) (IMAGE (f:real^M->real^N) s))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID; INT_LE_REFL];
    MATCH_MP_TAC AFF_DIM_LINEAR_IMAGE_LE THEN ASM_REWRITE_TAC[]]);;

add_linear_invariants [AFF_DIM_INJECTIVE_LINEAR_IMAGE];;

let AFF_DIM_AFFINE_INDEPENDENT = prove
 (`!b:real^N->bool.
        ~(affine_dependent b) ==> aff_dim b = &(CARD b) - &1`,
  GEN_TAC THEN ASM_CASES_TAC `b:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES; AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `a:real^N`]
   AFFINE_INDEPENDENT_CARD_DIM_DIFFS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; INT_ARITH `(a + b) - b:int = a`] THEN
  MP_TAC(ISPECL [`a:real^N`; `affine hull b:real^N->bool`]
   AFF_DIM_DIM_AFFINE_DIFFS) THEN
  ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC; AFF_DIM_AFFINE_HULL] THEN
  DISCH_THEN(K ALL_TAC) THEN AP_TERM_TAC THEN
  ASM_MESON_TAC[DIFFS_AFFINE_HULL_SPAN; DIM_SPAN]);;

let AFF_DIM_UNIQUE = prove
 (`!s b:real^N->bool.
        affine hull b = affine hull s /\ ~(affine_dependent b)
        ==> aff_dim s = &(CARD b) - &1`,
  MESON_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_AFFINE_INDEPENDENT]);;

let AFF_DIM_SING = prove
 (`!a:real^N. aff_dim {a} = &0`,
  GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `&(CARD {a:real^N}) - &1:int` THEN CONJ_TAC THENL
   [MATCH_MP_TAC AFF_DIM_AFFINE_INDEPENDENT THEN
    REWRITE_TAC[AFFINE_INDEPENDENT_1];
    SIMP_TAC[CARD_CLAUSES; FINITE_RULES; ARITH; NOT_IN_EMPTY; INT_SUB_REFL]]);;

let AFF_DIM_LE_CARD = prove
 (`!s:real^N->bool. FINITE s ==> aff_dim s <= &(CARD s) - &1`,
  MATCH_MP_TAC SET_PROVE_CASES THEN
  SIMP_TAC[AFF_DIM_EMPTY; CARD_CLAUSES] THEN CONV_TAC INT_REDUCE_CONV THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN
  SIMP_TAC[AFF_DIM_DIM_0; IN_INSERT; HULL_INC] THEN
  SIMP_TAC[CARD_IMAGE_INJ; VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  SIMP_TAC[DIM_INSERT_0; INT_LE_SUB_LADD; CARD_CLAUSES; FINITE_INSERT] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LE; ADD1; LE_ADD_RCANCEL] THEN
  SIMP_TAC[DIM_LE_CARD]);;

let AFF_DIM_GE = prove
 (`!s:real^N->bool. -- &1 <= aff_dim s`,
  GEN_TAC THEN MP_TAC(ISPEC `s:real^N->bool` AFF_DIM) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[INT_LE_SUB_LADD; INT_ADD_LINV; INT_POS]);;

let AFF_DIM_SUBSET = prove
 (`!s t:real^N->bool. s SUBSET t ==> aff_dim s <= aff_dim t`,
  MATCH_MP_TAC SET_PROVE_CASES THEN REWRITE_TAC[AFF_DIM_GE; AFF_DIM_EMPTY] THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vec 0:real^N) IN t` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_DIM_DIM_0; IN_INSERT; HULL_INC; INT_OF_NUM_LE; DIM_SUBSET]);;

let AFF_DIM_LE_DIM = prove
 (`!s:real^N->bool. aff_dim s <= &(dim s)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  ASM_SIMP_TAC[GSYM AFF_DIM_DIM_SUBSPACE; SUBSPACE_SPAN] THEN
  MATCH_MP_TAC AFF_DIM_SUBSET THEN REWRITE_TAC[SPAN_INC]);;

let AFF_DIM_CONVEX_HULL = prove
 (`!s:real^N->bool. aff_dim(convex hull s) = aff_dim s`,
  GEN_TAC THEN MATCH_MP_TAC(INT_ARITH
   `!c:int. c = a /\ a <= b /\ b <= c ==> b = a`) THEN
  EXISTS_TAC `aff_dim(affine hull s:real^N->bool)` THEN
  SIMP_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_SUBSET; HULL_SUBSET;
           CONVEX_HULL_SUBSET_AFFINE_HULL]);;

let AFF_DIM_CLOSURE = prove
 (`!s:real^N->bool. aff_dim(closure s) = aff_dim s`,
  GEN_TAC THEN MATCH_MP_TAC(INT_ARITH
   `!h. h = s /\ s <= c /\ c <= h ==> c:int = s`) THEN
  EXISTS_TAC `aff_dim(affine hull s:real^N->bool)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[AFF_DIM_AFFINE_HULL];
    MATCH_MP_TAC AFF_DIM_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET];
    MATCH_MP_TAC AFF_DIM_SUBSET THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN
    REWRITE_TAC[CLOSED_AFFINE_HULL; HULL_SUBSET]]);;

let AFF_DIM_2 = prove
 (`!a b:real^N. aff_dim {a,b} = if a = b then &0 else &1`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[INSERT_AC; AFF_DIM_SING]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `&(CARD {a:real^N,b}) - &1:int` THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_2] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC);;

let AFF_DIM_EQ_MINUS1 = prove
 (`!s:real^N->bool. aff_dim s = -- &1 <=> s = {}`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[AFF_DIM_EMPTY] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC(INT_ARITH `&0:int <= n ==> ~(n = -- &1)`) THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim {a:real^N}` THEN
  ASM_SIMP_TAC[AFF_DIM_SUBSET; SING_SUBSET] THEN
  REWRITE_TAC[AFF_DIM_SING; INT_LE_REFL]);;

let AFF_DIM_POS_LE = prove
 (`!s:real^N->bool. &0 <= aff_dim s <=> ~(s = {})`,
  GEN_TAC THEN REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN
  MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN INT_ARITH_TAC);;

let AFF_DIM_EQ_0 = prove
 (`!s:real^N->bool. aff_dim s = &0 <=> ?a. s = {a}`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[AFF_DIM_SING; LEFT_IMP_EXISTS_THM] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
  CONV_TAC INT_REDUCE_CONV THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC(SET_RULE
   `(!b. ~(b = a) /\ {a,b} SUBSET s ==> F) ==> a IN s ==> s = {a}`) THEN
  X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] AFF_DIM_2) THEN
  ASM_SIMP_TAC[] THEN INT_ARITH_TAC);;

let CONNECTED_IMP_PERFECT_AFF_DIM = prove
 (`!s x:real^N.
        connected s /\ ~(aff_dim s = &0) /\ x IN s ==> x limit_point_of s`,
  REWRITE_TAC[AFF_DIM_EQ_0; CONNECTED_IMP_PERFECT]);;

let AFF_DIM_UNIV = prove
 (`aff_dim(:real^N) = &(dimindex(:N))`,
  SIMP_TAC[AFF_DIM_DIM_SUBSPACE; SUBSPACE_UNIV; DIM_UNIV]);;

let AFF_DIM_EQ_AFFINE_HULL = prove
 (`!s t:real^N->bool.
        s SUBSET t /\ aff_dim t <= aff_dim s
        ==> affine hull s = affine hull t`,
  MATCH_MP_TAC SET_PROVE_CASES THEN
  SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_EQ_MINUS1; AFF_DIM_GE;
           INT_ARITH `a:int <= x ==> (x <= a <=> x = a)`] THEN
  X_GEN_TAC `a:real^N` THEN GEOM_ORIGIN_TAC `a:real^N` THEN
  SIMP_TAC[INSERT_SUBSET; IMP_CONJ; AFF_DIM_DIM_0; IN_INSERT; DIM_EQ_SPAN;
           HULL_INC; AFFINE_HULL_EQ_SPAN; INT_OF_NUM_LE]);;

let AFF_DIM_SUMS_INTER = prove
 (`!s t:real^N->bool.
        affine s /\ affine t /\ ~(s INTER t = {})
        ==> aff_dim {x + y | x IN s /\ y IN t} =
                (aff_dim s + aff_dim t) - aff_dim(s INTER t)`,
  REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN X_GEN_TAC `a:real^N` THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN
  REWRITE_TAC[VECTOR_ARITH `(a + x) + (a + y):real^N = &2 % a + (x + y)`] THEN
  ONCE_REWRITE_TAC[SET_RULE `{a + x + y:real^N | x IN s /\ y IN t} =
                            IMAGE (\x. a + x) {x + y | x IN s /\ y IN t}`] THEN
  REWRITE_TAC[AFF_DIM_TRANSLATION_EQ; IN_INTER] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN STRIP_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(vec 0:real^N) IN {x + y | x IN s /\ y IN t}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT(EXISTS_TAC `vec 0:real^N`) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_LID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_DIM_DIM_0; HULL_INC; IN_INTER] THEN
  REWRITE_TAC[INT_EQ_SUB_LADD; INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  MATCH_MP_TAC DIM_SUMS_INTER THEN ASM_SIMP_TAC[AFFINE_IMP_SUBSPACE]);;

let AFF_DIM_PSUBSET = prove
 (`!s t. (affine hull s) PSUBSET (affine hull t) ==> aff_dim s < aff_dim t`,
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  SIMP_TAC[PSUBSET; AFF_DIM_SUBSET; INT_LT_LE] THEN
  MESON_TAC[INT_EQ_IMP_LE; AFF_DIM_EQ_AFFINE_HULL; HULL_HULL]);;

let AFF_DIM_EQ_FULL = prove
 (`!s. aff_dim s = &(dimindex(:N)) <=> affine hull s = (:real^N)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM AFFINE_HULL_UNIV] THEN
    MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; AFF_DIM_UNIV; INT_LE_REFL];
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
    SIMP_TAC[AFF_DIM_UNIV]]);;

let AFF_DIM_LE_UNIV = prove
 (`!s:real^N->bool. aff_dim s <= &(dimindex(:N))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_UNIV] THEN
  MATCH_MP_TAC AFF_DIM_SUBSET THEN REWRITE_TAC[SUBSET_UNIV]);;

let AFFINE_INDEPENDENT_IFF_CARD = prove
 (`!s:real^N->bool.
        ~affine_dependent s <=> FINITE s /\ aff_dim s = &(CARD s) - &1`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_IMP_FINITE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC
   (ISPEC `s:real^N->bool` AFFINE_BASIS_EXISTS) THEN
  MATCH_MP_TAC(ARITH_RULE `!b:int. a <= b - &1 /\ b < s ==> ~(a = s - &1)`) THEN
  EXISTS_TAC `&(CARD(b:real^N->bool)):int` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_LE_CARD; FINITE_SUBSET; AFF_DIM_AFFINE_HULL];
    REWRITE_TAC[INT_OF_NUM_LT] THEN MATCH_MP_TAC CARD_PSUBSET THEN
    ASM_REWRITE_TAC[PSUBSET] THEN ASM_MESON_TAC[]]);;

let AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR = prove
 (`!s t:real^N->bool.
        convex s /\ ~(s INTER interior t = {})
        ==> affine hull (s INTER t) = affine hull s`,
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; RIGHT_AND_EXISTS_THM;
              LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`; `a:real^N`] THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REWRITE_TAC[IN_INTER] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
  SIMP_TAC[SUBSET_HULL; AFFINE_AFFINE_HULL] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SIMP_RULE[SUBSET] INTERIOR_SUBSET)) THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INTER] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR_CBALL]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET; IN_CBALL_0] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_UNIV] THEN
  X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
  ASM_SIMP_TAC[SPAN_SUPERSET; IN_INTER] THEN DISCH_TAC THEN
  ABBREV_TAC `k = min (&1 / &2) (e / norm(x:real^N))` THEN
  SUBGOAL_THEN `&0 < k /\ k < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; NORM_POS_LT; REAL_MIN_LT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `x:real^N = inv k % k % x` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
  REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[VECTOR_ARITH
     `k % x:real^N = (&1 - k) % vec 0 + k % x`] THEN
    MATCH_MP_TAC IN_CONVEX_SET THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "k" THEN
    ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LE_RDIV_EQ; NORM_POS_LT] THEN
    ASM_REAL_ARITH_TAC]);;

let AFFINE_HULL_CONVEX_INTER_OPEN = prove
 (`!s t:real^N->bool.
        convex s /\ open t /\ ~(s INTER t = {})
        ==> affine hull (s INTER t) = affine hull s`,
  ASM_SIMP_TAC[AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR; INTERIOR_OPEN]);;

let AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR = prove
 (`!s t:real^N->bool.
        affine s /\ ~(s INTER interior t = {})
        ==> affine hull (s INTER t) = s`,
  SIMP_TAC[AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR; AFFINE_IMP_CONVEX;
           HULL_P]);;

let AFFINE_HULL_AFFINE_INTER_OPEN = prove
 (`!s t:real^N->bool.
        affine s /\ open t /\ ~(s INTER t = {})
        ==> affine hull (s INTER t) = s`,
  SIMP_TAC[AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR; INTERIOR_OPEN]);;

let CONVEX_AND_AFFINE_INTER_OPEN = prove
 (`!s t u:real^N->bool.
        convex s /\ affine t /\ open u /\
        s INTER u = t INTER u /\ ~(s INTER u = {})
        ==> affine hull s = t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[] `!u v. x = u /\ u = v /\ v = y ==> x = y`) THEN
  MAP_EVERY EXISTS_TAC
   [`affine hull (s INTER u:real^N->bool)`;
    `affine hull t:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN
    ASM_SIMP_TAC[AFFINE_IMP_CONVEX] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[AFFINE_HULL_EQ]]);;

let AFFINE_HULL_CONVEX_INTER_OPEN_IN = prove
 (`!s t:real^N->bool.
        convex s /\ open_in (subtopology euclidean (affine hull s)) t /\
        ~(s INTER t = {})
        ==> affine hull (s INTER t) = affine hull s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER t INTER u = s INTER u`;
               HULL_SUBSET] THEN
  MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN ASM SET_TAC[]);;

let AFFINE_HULL_AFFINE_INTER_OPEN_IN = prove
 (`!s t:real^N->bool.
        affine s /\ open_in (subtopology euclidean s) t /\ ~(s INTER t = {})
        ==> affine hull (s INTER t) = s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`affine hull s:real^N->bool`; `t:real^N->bool`]
        AFFINE_HULL_CONVEX_INTER_OPEN_IN) THEN
  ASM_SIMP_TAC[HULL_HULL; AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL; HULL_P]);;

let AFFINE_HULL_OPEN_IN = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean (affine hull t)) s /\ ~(s = {})
        ==> affine hull s = affine hull t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AFFINE_HULL_AFFINE_INTER_OPEN THEN
  REWRITE_TAC[AFFINE_AFFINE_HULL] THEN ASM SET_TAC[]);;

let AFFINE_HULL_OPEN = prove
 (`!s. open s /\ ~(s = {}) ==> affine hull s = (:real^N)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBST1_TAC(SET_RULE `s = (:real^N) INTER s`) THEN
  ASM_SIMP_TAC[AFFINE_HULL_CONVEX_INTER_OPEN; CONVEX_UNIV] THEN
  REWRITE_TAC[AFFINE_HULL_UNIV]);;

let AFFINE_HULL_NONEMPTY_INTERIOR = prove
 (`!s. ~(interior s = {}) ==> affine hull s = (:real^N)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
  EXISTS_TAC `affine hull (interior s:real^N->bool)` THEN
  SIMP_TAC[HULL_MONO; INTERIOR_SUBSET] THEN
  ASM_SIMP_TAC[AFFINE_HULL_OPEN; OPEN_INTERIOR]);;

let AFF_DIM_OPEN = prove
 (`!s:real^N->bool. open s /\ ~(s = {}) ==> aff_dim s = &(dimindex(:N))`,
  SIMP_TAC[AFF_DIM_EQ_FULL; AFFINE_HULL_OPEN]);;

let AFF_DIM_NONEMPTY_INTERIOR = prove
 (`!s:real^N->bool. ~(interior s = {}) ==> aff_dim s = &(dimindex(:N))`,
  SIMP_TAC[AFF_DIM_EQ_FULL; AFFINE_HULL_NONEMPTY_INTERIOR]);;

let SPAN_OPEN = prove
 (`!s. open s /\ ~(s = {}) ==> span s = (:real^N)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
  EXISTS_TAC `affine hull s:real^N->bool` THEN
  ASM_SIMP_TAC[AFFINE_HULL_OPEN; AFFINE_HULL_SUBSET_SPAN]);;

let DIM_OPEN = prove
 (`!s:real^N->bool. open s /\ ~(s = {}) ==> dim s = dimindex(:N)`,
  SIMP_TAC[DIM_EQ_FULL; SPAN_OPEN]);;

let AFF_DIM_INSERT = prove
 (`!a:real^N s.
        aff_dim (a INSERT s) =
        if a IN affine hull s then aff_dim s else aff_dim s + &1`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC SET_PROVE_CASES THEN
  SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_SING; AFFINE_HULL_EMPTY; NOT_IN_EMPTY] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:real^N`; `s:real^N->bool`; `a:real^N`] THEN
  GEOM_ORIGIN_TAC `b:real^N` THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; AFF_DIM_DIM_0; HULL_INC; IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `s:real^N->bool`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`(vec 0:real^N) INSERT s`,`s:real^N->bool`) THEN
  SIMP_TAC[DIM_INSERT; INT_OF_NUM_ADD] THEN MESON_TAC[]);;

let AFFINE_BOUNDED_EQ_TRIVIAL = prove
 (`!s:real^N->bool.
        affine s ==> (bounded s <=> s = {} \/ ?a. s = {a})`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[BOUNDED_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N` MP_TAC) THEN
  GEOM_ORIGIN_TAC `b:real^N` THEN SIMP_TAC[AFFINE_EQ_SUBSPACE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUBSPACE_BOUNDED_EQ_TRIVIAL] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUBSPACE_0) THEN SET_TAC[]);;

let AFFINE_BOUNDED_EQ_LOWDIM = prove
 (`!s:real^N->bool.
        affine s ==> (bounded s <=> aff_dim s <= &0)`,
  SIMP_TAC[AFF_DIM_GE; INT_ARITH
   `--(&1):int <= x ==> (x <= &0 <=> x = --(&1) \/ x = &0)`] THEN
  SIMP_TAC[AFF_DIM_EQ_0; AFF_DIM_EQ_MINUS1; AFFINE_BOUNDED_EQ_TRIVIAL]);;

let COLLINEAR_AFF_DIM = prove
 (`!s:real^N->bool. collinear s <=> aff_dim s <= &1`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[COLLINEAR_AFFINE_HULL; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim{u:real^N,v}` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_SUBSET; AFF_DIM_AFFINE_HULL];
      MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `&(CARD{u:real^N,v}) - &1:int` THEN
      SIMP_TAC[AFF_DIM_LE_CARD; FINITE_INSERT; FINITE_EMPTY] THEN
      REWRITE_TAC[INT_ARITH `x - &1:int <= &1 <=> x <= &2`; INT_OF_NUM_LE] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC];
    ONCE_REWRITE_TAC[GSYM COLLINEAR_AFFINE_HULL_COLLINEAR;
                     GSYM AFF_DIM_AFFINE_HULL] THEN
    MP_TAC(ISPEC `s:real^N->bool` AFFINE_BASIS_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` (STRIP_ASSUME_TAC o GSYM)) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [AFFINE_INDEPENDENT_IFF_CARD]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[COLLINEAR_AFFINE_HULL_COLLINEAR;
                    AFF_DIM_AFFINE_HULL] THEN
    REWRITE_TAC[INT_ARITH `x - &1:int <= &1 <=> x <= &2`; INT_OF_NUM_LE] THEN
    ASM_SIMP_TAC[COLLINEAR_SMALL]]);;

let HOMEOMORPHIC_AFFINE_SETS = prove
 (`!s:real^M->bool t:real^N->bool.
        affine s /\ affine t /\ aff_dim s = aff_dim t ==> s homeomorphic t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_EQ_MINUS1; HOMEOMORPHIC_EMPTY] THEN
  POP_ASSUM MP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_EQ_MINUS1; HOMEOMORPHIC_EMPTY] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC
   [GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM; RIGHT_IMP_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^N`] THEN
  GEOM_ORIGIN_TAC `a:real^M` THEN GEOM_ORIGIN_TAC `b:real^N` THEN
  SIMP_TAC[AFFINE_EQ_SUBSPACE; AFF_DIM_DIM_0; HULL_INC; INT_OF_NUM_EQ] THEN
  MESON_TAC[HOMEOMORPHIC_SUBSPACES]);;

let AFF_DIM_OPEN_IN = prove
 (`!s t:real^N->bool.
        ~(s = {}) /\ open_in (subtopology euclidean t) s /\ affine t
        ==> aff_dim s = aff_dim t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN GEOM_ORIGIN_TAC `a:real^N` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  SUBGOAL_THEN `(vec 0:real^N) IN t` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_DIM_DIM_0; HULL_INC; AFFINE_EQ_SUBSPACE] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[GSYM LE_ANTISYM; DIM_SUBSET] THEN
  SUBGOAL_THEN `?e. &0 < e /\ cball(vec 0:real^N,e) INTER t SUBSET s`
  MP_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^N` o
      GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    ASM SET_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; IN_CBALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHONORMAL_BASIS_SUBSPACE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `IMAGE (\x:real^N. e % x) b`]
   INDEPENDENT_CARD_LE_DIM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[CARD_IMAGE_INJ; VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ] THEN
  ANTS_TAC THENL [REWRITE_TAC[SUBSET]; MESON_TAC[]] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[NORM_MUL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SUBSPACE_MUL] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE THEN
    ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ; LINEAR_SCALING]]);;

let DIM_OPEN_IN = prove
 (`!s t:real^N->bool.
        ~(s = {}) /\ open_in (subtopology euclidean t) s /\ subspace t
        ==> dim s = dim t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[GSYM LE_ANTISYM; DIM_SUBSET] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(s:real^N->bool)` THEN
  REWRITE_TAC[AFF_DIM_LE_DIM] THEN ASM_SIMP_TAC[GSYM AFF_DIM_DIM_SUBSPACE] THEN
  MATCH_MP_TAC INT_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC AFF_DIM_OPEN_IN THEN ASM_SIMP_TAC[SUBSPACE_IMP_AFFINE]);;

let AFF_DIM_CONVEX_INTER_NONEMPTY_INTERIOR = prove
 (`!s t:real^N->bool.
        convex s /\ ~(s INTER interior t = {})
        ==> aff_dim(s INTER t) = aff_dim s`,
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  ASM_SIMP_TAC[AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR] THEN
  REWRITE_TAC[AFF_DIM_AFFINE_HULL]);;

let AFF_DIM_CONVEX_INTER_OPEN = prove
 (`!s t:real^N->bool.
        convex s /\ open t /\ ~(s INTER t = {})
        ==> aff_dim(s INTER t) = aff_dim s`,
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  ASM_SIMP_TAC[AFFINE_HULL_CONVEX_INTER_OPEN] THEN
  REWRITE_TAC[AFF_DIM_AFFINE_HULL]);;

let AFFINE_HULL_HALFSPACE_LT = prove
 (`!a b. affine hull {x | a dot x < b} =
         if a = vec 0 /\ b <= &0 then {} else (:real^N)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_EMPTY; HALFSPACE_EQ_EMPTY_LT;
               AFFINE_HULL_OPEN; OPEN_HALFSPACE_LT]);;

let AFFINE_HULL_HALFSPACE_LE = prove
 (`!a b. affine hull {x | a dot x <= b} =
         if a = vec 0 /\ b < &0 then {} else (:real^N)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_SIMP_TAC[DOT_LZERO; SET_RULE `{x | p} = if p then UNIV else {}`] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[AFFINE_HULL_EMPTY; AFFINE_HULL_UNIV] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[GSYM CLOSURE_HALFSPACE_LT; AFFINE_HULL_CLOSURE] THEN
    ASM_REWRITE_TAC[AFFINE_HULL_HALFSPACE_LT]]);;

let AFFINE_HULL_HALFSPACE_GT = prove
 (`!a b. affine hull {x | a dot x > b} =
         if a = vec 0 /\ b >= &0 then {} else (:real^N)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_EMPTY; HALFSPACE_EQ_EMPTY_GT;
               AFFINE_HULL_OPEN; OPEN_HALFSPACE_GT]);;

let AFFINE_HULL_HALFSPACE_GE = prove
 (`!a b. affine hull {x | a dot x >= b} =
         if a = vec 0 /\ b > &0 then {} else (:real^N)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`--a:real^N`; `--b:real`] AFFINE_HULL_HALFSPACE_LE) THEN
  SIMP_TAC[real_ge; DOT_LNEG; REAL_LE_NEG2; VECTOR_NEG_EQ_0] THEN
  REWRITE_TAC[REAL_ARITH `--b < &0 <=> b > &0`]);;

let AFF_DIM_HALFSPACE_LT = prove
 (`!a:real^N b.
        aff_dim {x | a dot x < b} =
        if a = vec 0 /\ b <= &0 then --(&1) else &(dimindex(:N))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  SIMP_TAC[AFFINE_HULL_HALFSPACE_LT] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_UNIV]);;

let AFF_DIM_HALFSPACE_LE = prove
 (`!a:real^N b.
        aff_dim {x | a dot x <= b} =
        if a = vec 0 /\ b < &0 then --(&1) else &(dimindex(:N))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  SIMP_TAC[AFFINE_HULL_HALFSPACE_LE] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_UNIV]);;

let AFF_DIM_HALFSPACE_GT = prove
 (`!a:real^N b.
        aff_dim {x | a dot x > b} =
        if a = vec 0 /\ b >= &0 then --(&1) else &(dimindex(:N))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  SIMP_TAC[AFFINE_HULL_HALFSPACE_GT] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_UNIV]);;

let AFF_DIM_HALFSPACE_GE = prove
 (`!a:real^N b.
        aff_dim {x | a dot x >= b} =
        if a = vec 0 /\ b > &0 then --(&1) else &(dimindex(:N))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  SIMP_TAC[AFFINE_HULL_HALFSPACE_GE] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_UNIV]);;

let CHOOSE_AFFINE_SUBSET = prove
 (`!s:real^N->bool d.
        affine s /\ --(&1) <= d /\ d <= aff_dim s
        ==> ?t. affine t /\ t SUBSET s /\ aff_dim t = d`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d:int = --(&1)` THENL
   [STRIP_TAC THEN EXISTS_TAC `{}:real^N->bool` THEN
    ASM_REWRITE_TAC[EMPTY_SUBSET; AFFINE_EMPTY; AFF_DIM_EMPTY];
    ASM_SIMP_TAC[INT_ARITH
     `~(d:int = --(&1)) ==> (--(&1) <= d <=> &0 <= d)`] THEN
    POP_ASSUM(K ALL_TAC)] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    POP_ASSUM MP_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` MP_TAC) THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN
  SIMP_TAC[IMP_CONJ; AFF_DIM_DIM_SUBSPACE; AFFINE_EQ_SUBSPACE] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  REWRITE_TAC[INT_OF_NUM_LE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `n:num`]
        CHOOSE_SUBSPACE_OF_SUBSPACE) THEN
  ASM_SIMP_TAC[SPAN_OF_SUBSPACE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN
  ASM_SIMP_TAC[AFF_DIM_DIM_SUBSPACE; SUBSPACE_IMP_AFFINE]);;
