(* ========================================================================= *)
(* Complex transcendentals and their real counterparts.                      *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

open Hol_core
open Floor
open Products
open Vectors
open Determinants
open Topology
open Convex
open Paths
open Dimension
open Derivatives
open Complexes
open Canal


prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The complex exponential function.                                         *)
(* ------------------------------------------------------------------------- *)

let cexp = new_definition
 `cexp z = infsum (from 0) (\n. z pow n / Cx(&(FACT n)))`;;

let CEXP_0 = prove
 (`cexp(Cx(&0)) = Cx(&1)`,
  REWRITE_TAC[cexp] THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
  MP_TAC(ISPECL [`\i. Cx(&0) pow i / Cx(&(FACT i))`; `{0}`; `from 0`]
         SERIES_FINITE_SUPPORT) THEN
  SIMP_TAC[FROM_0; INTER_UNIV; FINITE_INSERT; FINITE_RULES] THEN ANTS_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[IN_SING; NOT_SUC] THEN
    REWRITE_TAC[complex_div; complex_pow; COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
    REWRITE_TAC[VSUM_SING; FACT; COMPLEX_DIV_1; complex_pow]]);;

let CEXP_CONVERGES_UNIFORMLY_CAUCHY = prove
 (`!R e. &0 < e /\ &0 < R
         ==> ?N. !m n z. m >= N /\ norm(z) <= R
                         ==> norm(vsum(m..n) (\i. z pow i / Cx(&(FACT i))))
                                     < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&1 / &2`; `\i. Cx(R) pow i / Cx(&(FACT i))`;
                 `from 0`] SERIES_RATIO) THEN
  REWRITE_TAC[SERIES_CAUCHY; LEFT_FORALL_IMP_THM] THEN
  MP_TAC(SPEC `&2 * norm(Cx(R))` REAL_ARCH_SIMPLE) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_DIV; COMPLEX_NORM_POW] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (c ==> d) ==> a ==> (b ==> c) ==> d`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
    SIMP_TAC[FACT; real_pow; GSYM REAL_OF_NUM_MUL; real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_ARITH
     `(z * zn) * (is * ik) <= (&1 * inv(&2)) * zn * ik <=>
      &0 <= (&1 - (&2 * z) * is) * zn * ik`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE; REAL_SUB_LE;
             REAL_LE_INV_EQ; REAL_ABS_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_0] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_SUC] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    REWRITE_TAC[FROM_0; INTER_UNIV] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[GSYM CX_DIV; GSYM CX_POW; VSUM_CX_NUMSEG; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
    SUBGOAL_THEN `abs (sum (m..n) (\i. R pow i / &(FACT i))) =
                  sum (m..n) (\i. R pow i / &(FACT i))`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE;REAL_LT_DIV; REAL_OF_NUM_LT;
                   FACT_LT; REAL_POW_LT];
      ALL_TAC] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN
    REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_POW; COMPLEX_NORM_CX] THEN
    SIMP_TAC[REAL_ABS_NUM; REAL_LE_DIV2_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
    ASM_SIMP_TAC[REAL_POW_LE2; NORM_POS_LE]]);;

let CEXP_CONVERGES = prove
 (`!z. ((\n. z pow n / Cx(&(FACT n))) sums cexp(z)) (from 0)`,
  GEN_TAC THEN REWRITE_TAC[cexp; SUMS_INFSUM; summable; SERIES_CAUCHY] THEN
  REWRITE_TAC[FROM_0; INTER_UNIV] THEN
  MP_TAC(SPEC `norm(z:complex) + &1` CEXP_CONVERGES_UNIFORMLY_CAUCHY) THEN
  SIMP_TAC[REAL_ARITH `&0 <= x ==> &0 < x + &1`; NORM_POS_LE] THEN
  MESON_TAC[REAL_ARITH `x <= x + &1`]);;

let CEXP_CONVERGES_UNIQUE = prove
 (`!w z. ((\n. z pow n / Cx(&(FACT n))) sums w) (from 0) <=> w = cexp(z)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[CEXP_CONVERGES] THEN
  DISCH_THEN(MP_TAC o C CONJ (SPEC `z:complex` CEXP_CONVERGES)) THEN
  REWRITE_TAC[SERIES_UNIQUE]);;

let CEXP_CONVERGES_UNIFORMLY = prove
 (`!R e. &0 < R /\ &0 < e
         ==> ?N. !n z. n >= N /\ norm(z) < R
                       ==> norm(vsum(0..n) (\i. z pow i / Cx(&(FACT i))) -
                                cexp(z)) <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`R:real`; `e / &2`] CEXP_CONVERGES_UNIFORMLY_CAUCHY) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:complex`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `z:complex` CEXP_CONVERGES) THEN
  REWRITE_TAC[sums; LIM_SEQUENTIALLY; FROM_0; INTER_UNIV; dist] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `n + M + 1`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n + 1`; `n + M + 1`; `z:complex`]) THEN
  ASM_SIMP_TAC[ARITH_RULE `(n >= N ==> n + 1 >= N) /\ M <= n + M + 1`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; VSUM_ADD_SPLIT; LE_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV `i:num`)) THEN NORM_ARITH_TAC);;

let HAS_COMPLEX_DERIVATIVE_CEXP = prove
 (`!z. (cexp has_complex_derivative cexp(z)) (at z)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
   [`ball(Cx(&0),norm(z:complex) + &1)`;
    `\n z. z pow n / Cx(&(FACT n))`;
    `\n z. if n = 0 then Cx(&0) else z pow (n-1) / Cx(&(FACT(n-1)))`;
    `cexp:complex->complex`;
    `(from 0)`]
   HAS_COMPLEX_DERIVATIVE_SERIES) THEN
  REWRITE_TAC[CONVEX_BALL; OPEN_BALL; IN_BALL; dist] THEN
  SIMP_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; OPEN_BALL; IN_BALL;
           dist; COMPLEX_SUB_LZERO; COMPLEX_SUB_RZERO; NORM_NEG] THEN
  ANTS_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
    SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[ARITH; complex_div; COMPLEX_MUL_LZERO] THEN
    MP_TAC(SPECL [`&n + &1`; `&0`] CX_INJ) THEN
    REWRITE_TAC[NOT_SUC; SUC_SUB1; GSYM REAL_OF_NUM_SUC; FACT;
         CX_ADD; CX_MUL; GSYM REAL_OF_NUM_MUL; COMPLEX_INV_MUL] THEN
    REWRITE_TAC[REAL_ARITH `~(&n + &1 = &0)`] THEN
    ABBREV_TAC `a = inv(Cx(&(FACT n)))` THEN CONV_TAC COMPLEX_FIELD;
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`norm(z:complex) + &1`; `e:real`]
       CEXP_CONVERGES_UNIFORMLY) THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N + 1` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `w:complex`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n - 1`; `w:complex`]) THEN
    ASM_SIMP_TAC[ARITH_RULE `n >= m + 1 ==> n - 1 >= m`] THEN
    REWRITE_TAC[FROM_0; INTER_UNIV] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `0..n = 0 INSERT (IMAGE SUC (0..n-1))` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_IMAGE; IN_NUMSEG] THEN
      INDUCT_TAC THEN REWRITE_TAC[LE_0; NOT_SUC; SUC_INJ; UNWIND_THM1] THEN
      UNDISCH_TAC `n >= N + 1` THEN ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[VSUM_CLAUSES; FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[IN_IMAGE; NOT_SUC; COMPLEX_ADD_LID] THEN
    SIMP_TAC[VSUM_IMAGE; FINITE_NUMSEG; SUC_INJ] THEN
    MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_NUMSEG; NOT_SUC; o_THM; SUC_SUB1];
    MAP_EVERY EXISTS_TAC [`Cx(&0)`; `cexp(Cx(&0))`] THEN
    REWRITE_TAC[CEXP_CONVERGES; COMPLEX_NORM_0] THEN
    SIMP_TAC[REAL_ARITH `&0 <= z ==> &0 < z + &1`; NORM_POS_LE];
    DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` MP_TAC) THEN
    REWRITE_TAC[CEXP_CONVERGES_UNIQUE] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`g:complex->complex`; `&1`] THEN
    REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
     [ALL_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]]] THEN
    POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC `w:complex` THEN MATCH_MP_TAC MONO_IMP THEN SIMP_TAC[] THEN
    NORM_ARITH_TAC]);;

let COMPLEX_DIFFERENTIABLE_AT_CEXP = prove
 (`!z. cexp complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CEXP]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CEXP = prove
 (`!s z. cexp complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CEXP]);;

let CONTINUOUS_AT_CEXP = prove
 (`!z. cexp continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CEXP;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CEXP = prove
 (`!s z. cexp continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CEXP]);;

let CONTINUOUS_ON_CEXP = prove
 (`!s. cexp continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CEXP]);;

let HOLOMORPHIC_ON_CEXP = prove
 (`!s. cexp holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CEXP]);;

(* ------------------------------------------------------------------------- *)
(* Add it to the database.                                                   *)
(* ------------------------------------------------------------------------- *)

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV
             HAS_COMPLEX_DERIVATIVE_CEXP)));;

(* ------------------------------------------------------------------------- *)
(* Hence the main results.                                                   *)
(* ------------------------------------------------------------------------- *)

let CEXP_ADD_MUL = prove
 (`!w z. cexp(w + z) * cexp(--z) = cexp(w)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `(!x. P x) <=> (!x. x IN UNIV ==> P x)`] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_ZERO_UNIQUE THEN
  EXISTS_TAC `Cx(&0)` THEN REWRITE_TAC[OPEN_UNIV; CONVEX_UNIV; IN_UNIV] THEN
  REWRITE_TAC[COMPLEX_ADD_RID; COMPLEX_NEG_0; CEXP_0; COMPLEX_MUL_RID] THEN
  GEN_TAC THEN COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING);;

let CEXP_NEG_RMUL = prove
 (`!z. cexp(z) * cexp(--z) = Cx(&1)`,
  MP_TAC(SPEC `Cx(&0)` CEXP_ADD_MUL) THEN MATCH_MP_TAC MONO_FORALL THEN
  SIMP_TAC[COMPLEX_ADD_LID; CEXP_0]);;

let CEXP_NEG_LMUL = prove
 (`!z. cexp(--z) * cexp(z) = Cx(&1)`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN REWRITE_TAC[CEXP_NEG_RMUL]);;

let CEXP_NEG = prove
 (`!z. cexp(--z) = inv(cexp z)`,
  MP_TAC CEXP_NEG_LMUL THEN MATCH_MP_TAC MONO_FORALL THEN
  CONV_TAC COMPLEX_FIELD);;

let CEXP_ADD = prove
 (`!w z. cexp(w + z) = cexp(w) * cexp(z)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`w:complex`; `z:complex`] CEXP_ADD_MUL) THEN
  MP_TAC(SPEC `z:complex` CEXP_NEG_LMUL) THEN CONV_TAC COMPLEX_FIELD);;

let CEXP_SUB = prove
 (`!w z. cexp(w - z) = cexp(w) / cexp(z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[complex_sub; complex_div; CEXP_ADD; CEXP_NEG]);;

let CEXP_NZ = prove
 (`!z. ~(cexp(z) = Cx(&0))`,
  MP_TAC CEXP_NEG_LMUL THEN MATCH_MP_TAC MONO_FORALL THEN
  CONV_TAC COMPLEX_FIELD);;

let CEXP_N = prove
 (`!n x. cexp(Cx(&n) * x) = cexp(x) pow n`,
  INDUCT_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC; CX_ADD] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; complex_pow; CEXP_0] THEN
  ASM_REWRITE_TAC[COMPLEX_ADD_RDISTRIB; CEXP_ADD; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let CEXP_VSUM = prove
 (`!f s. FINITE s ==> cexp(vsum s f) = cproduct s (\x. cexp(f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; CPRODUCT_CLAUSES; CEXP_ADD; COMPLEX_VEC_0; CEXP_0]);;

let LIM_CEXP_MINUS_1 = prove
 (`((\z. (cexp(z) - Cx(&1)) / z) --> Cx(&1)) (at (Cx(&0)))`,
  MP_TAC(COMPLEX_DIFF_CONV
      `((\z. cexp(z) - Cx(&1)) has_complex_derivative f') (at(Cx(&0)))`) THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_AT; CEXP_0; COMPLEX_SUB_REFL] THEN
  REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_SUB_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Crude bounds on complex exponential function, usable to get tighter ones. *)
(* ------------------------------------------------------------------------- *)

let CEXP_BOUND_BLEMMA = prove
 (`!B. (!z. norm(z) <= &1 / &2 ==> norm(cexp z) <= B)
       ==> !z. norm(z) <= &1 / &2 ==> norm(cexp z) <= &1 + B / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cexp`; `cexp`; `cball(Cx(&0),&1 / &2)`; `B:real`]
                COMPLEX_DIFFERENTIABLE_BOUND) THEN
  ASM_SIMP_TAC[CONVEX_CBALL; IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG;
    HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CEXP] THEN
  DISCH_THEN(MP_TAC o SPECL [`z:complex`; `Cx(&0)`]) THEN
  REWRITE_TAC[COMPLEX_NORM_0; CEXP_0; COMPLEX_SUB_RZERO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(y) = &1 /\ d <= e ==> norm(x - y) <= d ==> norm(x) <= &1 + e`) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; real_div; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&0)`) THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN POP_ASSUM MP_TAC THEN
  NORM_ARITH_TAC);;

let CEXP_BOUND_HALF = prove
 (`!z. norm(z) <= &1 / &2 ==> norm(cexp z) <= &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE cexp (cball(Cx(&0),&1 / &2))`; `Cx(&0)`]
    DISTANCE_ATTAINS_SUP) THEN
  SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; COMPACT_CBALL; CONTINUOUS_ON_CEXP;
           IMAGE_EQ_EMPTY; CBALL_EQ_EMPTY; FORALL_IN_IMAGE; EXISTS_IN_IMAGE;
           IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `w:complex` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `w:complex` o MATCH_MP CEXP_BOUND_BLEMMA) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CEXP_BOUND_LEMMA = prove
 (`!z. norm(z) <= &1 / &2 ==> norm(cexp z) <= &1 + &2 * norm(z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cexp`; `cexp`; `cball(Cx(&0),&1 / &2)`; `&2`]
                COMPLEX_DIFFERENTIABLE_BOUND) THEN
  ASM_SIMP_TAC[CONVEX_CBALL; IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG;
               HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CEXP;
               CEXP_BOUND_HALF] THEN
  DISCH_THEN(MP_TAC o SPECL [`z:complex`; `Cx(&0)`]) THEN
  REWRITE_TAC[COMPLEX_NORM_0; CEXP_0; COMPLEX_SUB_RZERO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(y) = &1 ==> norm(x - y) <= d ==> norm(x) <= &1 + d`) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Complex trig functions.                                                   *)
(* ------------------------------------------------------------------------- *)

let ccos = new_definition
  `ccos z = (cexp(ii * z) + cexp(--ii * z)) / Cx(&2)`;;

let csin = new_definition
  `csin z = (cexp(ii * z) - cexp(--ii * z)) / (Cx(&2) * ii)`;;

let CSIN_0 = prove
 (`csin(Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[csin; COMPLEX_MUL_RZERO; COMPLEX_SUB_REFL] THEN
  CONV_TAC COMPLEX_FIELD);;

let CCOS_0 = prove
 (`ccos(Cx(&0)) = Cx(&1)`,
  REWRITE_TAC[ccos; COMPLEX_MUL_RZERO; CEXP_0] THEN
  CONV_TAC COMPLEX_FIELD);;

let CSIN_CIRCLE = prove
 (`!z. csin(z) pow 2 + ccos(z) pow 2 = Cx(&1)`,
  GEN_TAC THEN REWRITE_TAC[csin; ccos] THEN
  MP_TAC(SPEC `ii * z` CEXP_NEG_LMUL) THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG] THEN
  CONV_TAC COMPLEX_FIELD);;

let CSIN_ADD = prove
 (`!w z. csin(w + z) = csin(w) * ccos(z) + ccos(w) * csin(z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[csin; ccos; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
  CONV_TAC COMPLEX_FIELD);;

let CCOS_ADD = prove
 (`!w z. ccos(w + z) = ccos(w) * ccos(z) - csin(w) * csin(z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[csin; ccos; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
  CONV_TAC COMPLEX_FIELD);;

let CSIN_NEG = prove
 (`!z. csin(--z) = --(csin(z))`,
  REWRITE_TAC[csin; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG] THEN
  CONV_TAC COMPLEX_FIELD);;

let CCOS_NEG = prove
 (`!z. ccos(--z) = ccos(z)`,
  REWRITE_TAC[ccos; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG] THEN
  CONV_TAC COMPLEX_FIELD);;

let CSIN_DOUBLE = prove
 (`!z. csin(Cx(&2) * z) = Cx(&2) * csin(z) * ccos(z)`,
  REWRITE_TAC[COMPLEX_RING `Cx(&2) * x = x + x`; CSIN_ADD] THEN
  CONV_TAC COMPLEX_RING);;

let CCOS_DOUBLE = prove
 (`!z. ccos(Cx(&2) * z) = (ccos(z) pow 2) - (csin(z) pow 2)`,
  REWRITE_TAC[COMPLEX_RING `Cx(&2) * x = x + x`; CCOS_ADD] THEN
  CONV_TAC COMPLEX_RING);;

let CSIN_SUB = prove
 (`!w z. csin(w - z) = csin(w) * ccos(z) - ccos(w) * csin(z)`,
  REWRITE_TAC[complex_sub; COMPLEX_MUL_RNEG; CSIN_ADD; CSIN_NEG; CCOS_NEG]);;

let CCOS_SUB = prove
 (`!w z. ccos(w - z) = ccos(w) * ccos(z) + csin(w) * csin(z)`,
  REWRITE_TAC[complex_sub; CCOS_ADD; CSIN_NEG; CCOS_NEG;
              COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG]);;

let COMPLEX_MUL_CSIN_CSIN = prove
 (`!w z. csin(w) * csin(z) = (ccos(w - z) - ccos(w + z)) / Cx(&2)`,
  REWRITE_TAC[CCOS_ADD; CCOS_SUB] THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_MUL_CSIN_CCOS = prove
 (`!w z. csin(w) * ccos(z) = (csin(w + z) + csin(w - z)) / Cx(&2)`,
  REWRITE_TAC[CSIN_ADD; CSIN_SUB] THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_MUL_CCOS_CSIN = prove
 (`!w z. ccos(w) * csin(z) = (csin(w + z) - csin(w - z)) / Cx(&2)`,
  REWRITE_TAC[CSIN_ADD; CSIN_SUB] THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_MUL_CCOS_CCOS = prove
 (`!w z. ccos(w) * ccos(z) = (ccos(w - z) + ccos(w + z)) / Cx(&2)`,
  REWRITE_TAC[CCOS_ADD; CCOS_SUB] THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_ADD_CSIN = prove
 (`!w z. csin(w) + csin(z) =
         Cx(&2) * csin((w + z) / Cx(&2)) * ccos((w - z) / Cx(&2))`,
  SIMP_TAC[COMPLEX_MUL_CSIN_CCOS; COMPLEX_RING `Cx(&2) * x / Cx(&2) = x`] THEN
  REPEAT GEN_TAC THEN BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_SUB_CSIN = prove
 (`!w z. csin(w) - csin(z) =
         Cx(&2) * csin((w - z) / Cx(&2)) * ccos((w + z) / Cx(&2))`,
  SIMP_TAC[COMPLEX_MUL_CSIN_CCOS; COMPLEX_RING `Cx(&2) * x / Cx(&2) = x`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_sub; GSYM CSIN_NEG] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_ADD_CCOS = prove
 (`!w z. ccos(w) + ccos(z) =
         Cx(&2) * ccos((w + z) / Cx(&2)) * ccos((w - z) / Cx(&2))`,
  SIMP_TAC[COMPLEX_MUL_CCOS_CCOS; COMPLEX_RING `Cx(&2) * x / Cx(&2) = x`] THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [COMPLEX_ADD_SYM] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_SUB_CCOS = prove
 (`!w z. ccos(w) - ccos(z) =
         Cx(&2) * csin((w + z) / Cx(&2)) * csin((z - w) / Cx(&2))`,
  SIMP_TAC[COMPLEX_MUL_CSIN_CSIN; COMPLEX_RING `Cx(&2) * x / Cx(&2) = x`] THEN
  REPEAT GEN_TAC THEN BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

let CCOS_DOUBLE_CCOS = prove
 (`!z. ccos(Cx(&2) * z) = Cx(&2) * ccos z pow 2 - Cx(&1)`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_RING `Cx(&2) * x = x + x`; CCOS_ADD] THEN
  MP_TAC(SPEC `z:complex` CSIN_CIRCLE) THEN CONV_TAC COMPLEX_RING);;

let CCOS_DOUBLE_CSIN = prove
 (`!z. ccos(Cx(&2) * z) = Cx(&1) - Cx(&2) * csin z pow 2`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_RING `Cx(&2) * x = x + x`; CCOS_ADD] THEN
  MP_TAC(SPEC `z:complex` CSIN_CIRCLE) THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Euler and de Moivre formulas.                                             *)
(* ------------------------------------------------------------------------- *)

let CEXP_EULER = prove
 (`!z. cexp(ii * z) = ccos(z) + ii * csin(z)`,
  REWRITE_TAC[ccos; csin] THEN CONV_TAC COMPLEX_FIELD);;

let DEMOIVRE = prove
 (`!z n. (ccos z + ii * csin z) pow n =
         ccos(Cx(&n) * z) + ii * csin(Cx(&n) * z)`,
  REWRITE_TAC[GSYM CEXP_EULER; GSYM CEXP_N] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Real exponential function. Same names as old Library/transc.ml.           *)
(* ------------------------------------------------------------------------- *)

let exp = new_definition `exp(x) = Re(cexp(Cx x))`;;

let CNJ_CEXP = prove
 (`!z. cnj(cexp z) = cexp(cnj z)`,
  GEN_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`\n. cnj(z pow n / Cx(&(FACT n)))`; `from 0`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUMS_CNJ; CEXP_CONVERGES];
    REWRITE_TAC[CNJ_DIV; CNJ_CX; CNJ_POW; CEXP_CONVERGES]]);;

let REAL_EXP = prove
 (`!z. real z ==> real(cexp z)`,
  SIMP_TAC[REAL_CNJ; CNJ_CEXP]);;

let CX_EXP = prove
 (`!x. Cx(exp x) = cexp(Cx x)`,
  REWRITE_TAC[exp] THEN MESON_TAC[REAL; REAL_CX; REAL_EXP]);;

let REAL_EXP_ADD = prove
 (`!x y. exp(x + y) = exp(x) * exp(y)`,
  REWRITE_TAC[GSYM CX_INJ; CX_MUL; CX_EXP; CX_ADD; CEXP_ADD]);;

let REAL_EXP_0 = prove
 (`exp(&0) = &1`,
  REWRITE_TAC[GSYM CX_INJ; CX_EXP; CEXP_0]);;

let REAL_EXP_ADD_MUL = prove
 (`!x y. exp(x + y) * exp(--x) = exp(y)`,
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM CX_INJ; CX_MUL; CX_EXP; CX_ADD; CX_NEG; CEXP_ADD_MUL]);;

let REAL_EXP_NEG_MUL = prove
 (`!x. exp(x) * exp(--x) = &1`,
  REWRITE_TAC[GSYM CX_INJ; CX_MUL; CX_EXP; CX_NEG; CEXP_NEG_RMUL]);;

let REAL_EXP_NEG_MUL2 = prove
 (`!x. exp(--x) * exp(x) = &1`,
  REWRITE_TAC[GSYM CX_INJ; CX_MUL; CX_EXP; CX_NEG; CEXP_NEG_LMUL]);;

let REAL_EXP_NEG = prove
 (`!x. exp(--x) = inv(exp(x))`,
  REWRITE_TAC[GSYM CX_INJ; CX_INV; CX_EXP; CX_NEG; CEXP_NEG]);;

let REAL_EXP_N = prove
 (`!n x. exp(&n * x) = exp(x) pow n`,
  REWRITE_TAC[GSYM CX_INJ; CX_EXP; CX_POW; CX_MUL; CEXP_N]);;

let REAL_EXP_SUB = prove
 (`!x y. exp(x - y) = exp(x) / exp(y)`,
  REWRITE_TAC[GSYM CX_INJ; CX_SUB; CX_DIV; CX_EXP; CEXP_SUB]);;

let REAL_EXP_NZ = prove
 (`!x. ~(exp(x) = &0)`,
  REWRITE_TAC[GSYM CX_INJ; CX_EXP; CEXP_NZ]);;

let REAL_EXP_POS_LE = prove
 (`!x. &0 <= exp(x)`,
  GEN_TAC THEN SUBST1_TAC(REAL_ARITH `x = x / &2 + x / &2`) THEN
  REWRITE_TAC[REAL_EXP_ADD; REAL_LE_SQUARE]);;

let REAL_EXP_POS_LT = prove
 (`!x. &0 < exp(x)`,
  REWRITE_TAC[REAL_LT_LE; REAL_EXP_NZ; REAL_EXP_POS_LE]);;

let REAL_EXP_LE_X = prove
 (`!x. &1 + x <= exp(x)`,
  GEN_TAC THEN ASM_CASES_TAC `&1 + x < &0` THENL
   [MP_TAC(SPEC `x:real` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[exp; RE_DEF] THEN
  MATCH_MP_TAC(MATCH_MP
   (ONCE_REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`]
        LIM_COMPONENT_LBOUND)
   (REWRITE_RULE[sums] (SPEC `Cx x` CEXP_CONVERGES))) THEN
  SIMP_TAC[DIMINDEX_2; ARITH; TRIVIAL_LIMIT_SEQUENTIALLY;
           VSUM_COMPONENT; EVENTUALLY_SEQUENTIALLY; FROM_0; INTER_UNIV] THEN
  REWRITE_TAC[GSYM CX_DIV; GSYM RE_DEF; RE_CX; GSYM CX_POW] THEN
  EXISTS_TAC `1` THEN SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[real_pow; REAL_POW_1; REAL_DIV_1; REAL_LE_ADDR; REAL_ADD_ASSOC] THEN
  SUBGOAL_THEN
   `!n. &0 <= sum(2*1..2*n+1) (\k. x pow k / &(FACT k))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[SUM_PAIR] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM ADD1; real_pow; FACT; GSYM REAL_OF_NUM_MUL] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; FACT_NZ; NOT_SUC; REAL_FIELD
     `~(k = &0) /\ ~(f = &0)
      ==> p / f + (x * p) / (k * f) = p / f * (&1 + x / k)`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_ARITH `&0 <= a + b <=> --a <= b`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; LT_0; REAL_OF_NUM_LT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC];
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(SPEC `n - 1` EVEN_OR_ODD) THEN
    ASM_SIMP_TAC[EVEN_EXISTS; ODD_EXISTS;
                 ARITH_RULE `1 <= n ==> (n - 1 = d <=> n = SUC d)`] THEN
    STRIP_TAC THENL [ASM_MESON_TAC[ADD1]; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC(2 * n) = 2 * n + 1`] THEN
    ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC(2 * m + 1) = 2 * (m + 1)`]] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_POW; REAL_POW_LE; REAL_LE_POW_2]);;

let REAL_EXP_LT_1 = prove
 (`!x. &0 < x ==> &1 < exp(x)`,
  MP_TAC REAL_EXP_LE_X THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let REAL_EXP_MONO_IMP = prove
 (`!x y. x < y ==> exp(x) < exp(y)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_SUB_LT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_EXP_LT_1) THEN
  SIMP_TAC[REAL_EXP_SUB; REAL_LT_RDIV_EQ; REAL_EXP_POS_LT; REAL_MUL_LID]);;

let REAL_EXP_MONO_LT = prove
 (`!x y. exp(x) < exp(y) <=> x < y`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `(x < y ==> f < g) /\ (x = y ==> f = g) /\ (y < x ==> g < f)
    ==> (f < g <=> x < y)`) THEN
  SIMP_TAC[REAL_EXP_MONO_IMP]);;

let REAL_EXP_MONO_LE = prove
 (`!x y. exp(x) <= exp(y) <=> x <= y`,
  REWRITE_TAC[GSYM REAL_NOT_LT; REAL_EXP_MONO_LT]);;

let REAL_EXP_INJ = prove
 (`!x y. (exp(x) = exp(y)) <=> (x = y)`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; REAL_EXP_MONO_LE]);;

let REAL_EXP_EQ_1 = prove
 (`!x. exp(x) = &1 <=> x = &0`,
  ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_INJ]);;

let REAL_ABS_EXP = prove
 (`!x. abs(exp x) = exp x`,
  REWRITE_TAC[real_abs; REAL_EXP_POS_LE]);;

let REAL_EXP_SUM = prove
 (`!f s. FINITE s ==> exp(sum s f) = product s (\x. exp(f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; PRODUCT_CLAUSES; REAL_EXP_ADD; REAL_EXP_0]);;

let REAL_EXP_BOUND_LEMMA = prove
 (`!x. &0 <= x /\ x <= inv(&2) ==> exp(x) <= &1 + &2 * x`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `Cx x` CEXP_BOUND_LEMMA) THEN
  REWRITE_TAC[GSYM CX_EXP; COMPLEX_NORM_CX; RE_CX] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Real trig functions, their reality,  derivatives of complex versions.     *)
(* ------------------------------------------------------------------------- *)

let sin = new_definition `sin(x) = Re(csin(Cx x))`;;

let cos = new_definition `cos(x) = Re(ccos(Cx x))`;;

let CNJ_CSIN = prove
 (`!z. cnj(csin z) = csin(cnj z)`,
  REWRITE_TAC[csin; CNJ_DIV; CNJ_SUB; CNJ_MUL; CNJ_CX; CNJ_CEXP;
              CNJ_NEG; CNJ_II; COMPLEX_NEG_NEG] THEN
  CONV_TAC COMPLEX_FIELD);;

let CNJ_CCOS = prove
 (`!z. cnj(ccos z) = ccos(cnj z)`,
  REWRITE_TAC[ccos; CNJ_DIV; CNJ_ADD; CNJ_MUL; CNJ_CX; CNJ_CEXP;
              CNJ_NEG; CNJ_II; COMPLEX_NEG_NEG; COMPLEX_ADD_AC]);;

let REAL_SIN = prove
 (`!z. real z ==> real(csin z)`,
  SIMP_TAC[REAL_CNJ; CNJ_CSIN]);;

let REAL_COS = prove
 (`!z. real z ==> real(ccos z)`,
  SIMP_TAC[REAL_CNJ; CNJ_CCOS]);;

let CX_SIN = prove
 (`!x. Cx(sin x) = csin(Cx x)`,
  REWRITE_TAC[sin] THEN MESON_TAC[REAL; REAL_CX; REAL_SIN]);;

let CX_COS = prove
 (`!x. Cx(cos x) = ccos(Cx x)`,
  REWRITE_TAC[cos] THEN MESON_TAC[REAL; REAL_CX; REAL_COS]);;

let HAS_COMPLEX_DERIVATIVE_CSIN = prove
 (`!z. (csin has_complex_derivative ccos z) (at z)`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[csin; ccos] THEN COMPLEX_DIFF_TAC THEN
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_DIFFERENTIABLE_AT_CSIN = prove
 (`!z. csin complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CSIN]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CSIN = prove
 (`!s z. csin complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CSIN]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV
             HAS_COMPLEX_DERIVATIVE_CSIN)));;

let HAS_COMPLEX_DERIVATIVE_CCOS = prove
 (`!z. (ccos has_complex_derivative --csin z) (at z)`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[csin; ccos] THEN COMPLEX_DIFF_TAC THEN
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_DIFFERENTIABLE_AT_CCOS = prove
 (`!z. ccos complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CCOS]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CCOS = prove
 (`!s z. ccos complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CCOS]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV
             HAS_COMPLEX_DERIVATIVE_CCOS)));;

let CONTINUOUS_AT_CSIN = prove
 (`!z. csin continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CSIN;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CSIN = prove
 (`!s z. csin continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CSIN]);;

let CONTINUOUS_ON_CSIN = prove
 (`!s. csin continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CSIN]);;

let HOLOMORPHIC_ON_CSIN = prove
 (`!s. csin holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CSIN]);;

let CONTINUOUS_AT_CCOS = prove
 (`!z. ccos continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CCOS;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CCOS = prove
 (`!s z. ccos continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CCOS]);;

let CONTINUOUS_ON_CCOS = prove
 (`!s. ccos continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CCOS]);;

let HOLOMORPHIC_ON_CCOS = prove
 (`!s. ccos holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CCOS]);;

(* ------------------------------------------------------------------------- *)
(* Slew of theorems for compatibility with old transc.ml file.               *)
(* ------------------------------------------------------------------------- *)

let SIN_0 = prove
 (`sin(&0) = &0`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CSIN_0]);;

let COS_0 = prove
 (`cos(&0) = &1`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CCOS_0]);;

let SIN_CIRCLE = prove
 (`!x. (sin(x) pow 2) + (cos(x) pow 2) = &1`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_POW; CSIN_CIRCLE]);;

let SIN_ADD = prove
 (`!x y. sin(x + y) = sin(x) * cos(y) + cos(x) * sin(y)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_MUL; CSIN_ADD]);;

let COS_ADD = prove
 (`!x y. cos(x + y) = cos(x) * cos(y) - sin(x) * sin(y)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CCOS_ADD]);;

let SIN_NEG = prove
 (`!x. sin(--x) = --(sin(x))`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CX_NEG; CSIN_NEG]);;

let COS_NEG = prove
 (`!x. cos(--x) = cos(x)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_NEG; CCOS_NEG]);;

let SIN_DOUBLE = prove
 (`!x. sin(&2 * x) = &2 * sin(x) * cos(x)`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CX_COS; CX_MUL; CSIN_DOUBLE]);;

let COS_DOUBLE = prove
 (`!x. cos(&2 * x) = (cos(x) pow 2) - (sin(x) pow 2)`,
  SIMP_TAC[GSYM CX_INJ; CX_SIN; CX_COS; CX_SUB; CX_MUL; CX_POW; CCOS_DOUBLE]);;

let COS_DOUBLE_COS = prove
 (`!x. cos(&2 * x) = &2 * cos(x) pow 2 - &1`,
  MP_TAC SIN_CIRCLE THEN MATCH_MP_TAC MONO_FORALL THEN
  REWRITE_TAC[COS_DOUBLE] THEN REAL_ARITH_TAC);;

let (SIN_BOUND,COS_BOUND) = (CONJ_PAIR o prove)
 (`(!x. abs(sin x) <= &1) /\ (!x. abs(cos x) <= &1)`,
  CONJ_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_ABS_NUM] THEN
  ONCE_REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN
  MAP_EVERY (MP_TAC o C SPEC REAL_LE_SQUARE) [`sin x`; `cos x`] THEN
  REAL_ARITH_TAC);;

let SIN_BOUNDS = prove
 (`!x. --(&1) <= sin(x) /\ sin(x) <= &1`,
  MP_TAC SIN_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let COS_BOUNDS = prove
 (`!x. --(&1) <= cos(x) /\ cos(x) <= &1`,
  MP_TAC COS_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let COS_ABS = prove
 (`!x. cos(abs x) = cos(x)`,
  REWRITE_TAC[real_abs] THEN MESON_TAC[COS_NEG]);;

let SIN_SUB = prove
 (`!w z. sin(w - z) = sin(w) * cos(z) - cos(w) * sin(z)`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CX_COS; CX_SUB; CX_MUL; CSIN_SUB]);;

let COS_SUB = prove
 (`!w z. cos(w - z) = cos(w) * cos(z) + sin(w) * sin(z)`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CX_COS; CX_SUB; CX_ADD; CX_MUL; CCOS_SUB]);;

let REAL_MUL_SIN_SIN = prove
 (`!x y. sin(x) * sin(y) = (cos(x - y) - cos(x + y)) / &2`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_MUL_CSIN_CSIN]);;

let REAL_MUL_SIN_COS = prove
 (`!x y. sin(x) * cos(y) = (sin(x + y) + sin(x - y)) / &2`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_MUL_CSIN_CCOS]);;

let REAL_MUL_COS_SIN = prove
 (`!x y. cos(x) * sin(y) = (sin(x + y) - sin(x - y)) / &2`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_MUL_CCOS_CSIN]);;

let REAL_MUL_COS_COS = prove
 (`!x y. cos(x) * cos(y) = (cos(x - y) + cos(x + y)) / &2`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_MUL_CCOS_CCOS]);;

let REAL_ADD_SIN = prove
 (`!x y. sin(x) + sin(y) = &2 * sin((x + y) / &2) * cos((x - y) / &2)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_ADD_CSIN]);;

let REAL_SUB_SIN = prove
 (`!x y. sin(x) - sin(y) = &2 * sin((x - y) / &2) * cos((x + y) / &2)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_SUB_CSIN]);;

let REAL_ADD_COS = prove
 (`!x y. cos(x) + cos(y) = &2 * cos((x + y) / &2) * cos((x - y) / &2)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_ADD_CCOS]);;

let REAL_SUB_COS = prove
 (`!x y. cos(x) - cos(y) = &2 * sin((x + y) / &2) * sin((y - x) / &2)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CX_SIN; CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_SUB_CCOS]);;

let COS_DOUBLE_SIN = prove
 (`!x. cos(&2 * x) = &1 - &2 * sin x pow 2`,
  GEN_TAC THEN REWRITE_TAC[REAL_RING `&2 * x = x + x`; COS_ADD] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Get a nice real/imaginary separation in Euler's formula.                  *)
(* ------------------------------------------------------------------------- *)

let EULER = prove
 (`!z. cexp(z) = Cx(exp(Re z)) * (Cx(cos(Im z)) + ii * Cx(sin(Im z)))`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
  REWRITE_TAC[CEXP_ADD; CEXP_EULER; GSYM CX_SIN; GSYM CX_COS; GSYM CX_EXP]);;

let RE_CEXP = prove
 (`!z. Re(cexp z) = exp(Re z) * cos(Im z)`,
  REWRITE_TAC[EULER; RE_ADD; RE_MUL_CX; RE_MUL_II; IM_CX; RE_CX] THEN
  REAL_ARITH_TAC);;

let IM_CEXP = prove
 (`!z. Im(cexp z) = exp(Re z) * sin(Im z)`,
  REWRITE_TAC[EULER; IM_ADD; IM_MUL_CX; IM_MUL_II; IM_CX; RE_CX] THEN
  REAL_ARITH_TAC);;

let RE_CSIN = prove
 (`!z. Re(csin z) = (exp(Im z) + exp(--(Im z))) / &2 * sin(Re z)`,
  GEN_TAC THEN REWRITE_TAC[csin] THEN
  SIMP_TAC[COMPLEX_FIELD `x / (Cx(&2) * ii) = ii * --(x / Cx(&2))`] THEN
  REWRITE_TAC[IM_MUL_II; IM_DIV_CX; RE_NEG; IM_SUB; IM_CEXP;
              RE_MUL_II; COMPLEX_MUL_LNEG; IM_NEG] THEN
  REWRITE_TAC[REAL_NEG_NEG; SIN_NEG] THEN CONV_TAC REAL_RING);;

let IM_CSIN = prove
 (`!z. Im(csin z) = (exp(Im z) - exp(--(Im z))) / &2 * cos(Re z)`,
  GEN_TAC THEN REWRITE_TAC[csin] THEN
  SIMP_TAC[COMPLEX_FIELD `x / (Cx(&2) * ii) = ii * --(x / Cx(&2))`] THEN
  REWRITE_TAC[IM_MUL_II; RE_DIV_CX; RE_NEG; RE_SUB; RE_CEXP;
              RE_MUL_II; COMPLEX_MUL_LNEG; IM_NEG] THEN
  REWRITE_TAC[REAL_NEG_NEG; COS_NEG] THEN CONV_TAC REAL_RING);;

let RE_CCOS = prove
 (`!z. Re(ccos z) = (exp(Im z) + exp(--(Im z))) / &2 * cos(Re z)`,
  GEN_TAC THEN REWRITE_TAC[ccos] THEN
  REWRITE_TAC[RE_DIV_CX; RE_ADD; RE_CEXP; COMPLEX_MUL_LNEG;
              RE_MUL_II; IM_MUL_II; RE_NEG; IM_NEG; COS_NEG] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN CONV_TAC REAL_RING);;

let IM_CCOS = prove
 (`!z. Im(ccos z) = (exp(--(Im z)) - exp(Im z)) / &2 * sin(Re z)`,
  GEN_TAC THEN REWRITE_TAC[ccos] THEN
  REWRITE_TAC[IM_DIV_CX; IM_ADD; IM_CEXP; COMPLEX_MUL_LNEG;
              RE_MUL_II; IM_MUL_II; RE_NEG; IM_NEG; SIN_NEG] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Some special intermediate value theorems over the reals.                  *)
(* ------------------------------------------------------------------------- *)

let IVT_INCREASING_RE = prove
 (`!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Re(f(Cx a)) <= y /\ y <= Re(f(Cx b))
        ==> ?x. a <= x /\ x <= b /\ Re(f(Cx x)) = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(f:complex->complex) o Cx o drop`;
                 `lift a`; `lift b`; `y:real`; `1`]
        IVT_INCREASING_COMPONENT_1) THEN
  REWRITE_TAC[EXISTS_DROP; GSYM drop; LIFT_DROP; o_THM; GSYM RE_DEF] THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; GSYM CONJ_ASSOC; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[DIMINDEX_2; ARITH] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
  ASM_SIMP_TAC[o_THM] THEN REWRITE_TAC[continuous_at; o_THM] THEN
  REWRITE_TAC[dist; GSYM CX_SUB; GSYM DROP_SUB; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[GSYM ABS_DROP] THEN MESON_TAC[]);;

let IVT_DECREASING_RE = prove
 (`!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Re(f(Cx b)) <= y /\ y <= Re(f(Cx a))
        ==> ?x. a <= x /\ x <= b /\ Re(f(Cx x)) = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EQ_NEG2] THEN
  REWRITE_TAC[GSYM RE_NEG] THEN MATCH_MP_TAC IVT_INCREASING_RE THEN
  ASM_SIMP_TAC[CONTINUOUS_NEG; RE_NEG; REAL_LE_NEG2]);;

let IVT_INCREASING_IM = prove
 (`!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Im(f(Cx a)) <= y /\ y <= Im(f(Cx b))
        ==> ?x. a <= x /\ x <= b /\ Im(f(Cx x)) = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EQ_NEG2] THEN
  REWRITE_TAC[SYM(CONJUNCT2(SPEC_ALL RE_MUL_II))] THEN
  MATCH_MP_TAC IVT_DECREASING_RE THEN
  ASM_SIMP_TAC[CONTINUOUS_COMPLEX_MUL; ETA_AX; CONTINUOUS_CONST] THEN
  ASM_REWRITE_TAC[RE_MUL_II; REAL_LE_NEG2]);;

let IVT_DECREASING_IM = prove
 (`!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Im(f(Cx b)) <= y /\ y <= Im(f(Cx a))
        ==> ?x. a <= x /\ x <= b /\ Im(f(Cx x)) = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EQ_NEG2] THEN
  REWRITE_TAC[GSYM IM_NEG] THEN MATCH_MP_TAC IVT_INCREASING_IM THEN
  ASM_SIMP_TAC[CONTINUOUS_NEG; IM_NEG; REAL_LE_NEG2]);;

(* ------------------------------------------------------------------------- *)
(* Some minimal properties of real logs help to define complex logs.         *)
(* ------------------------------------------------------------------------- *)

let log_def = new_definition
 `log y = @x. exp(x) = y`;;

let EXP_LOG = prove
 (`!x. &0 < x ==> exp(log x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[log_def] THEN CONV_TAC SELECT_CONV THEN
  SUBGOAL_THEN `?y. --inv(x) <= y /\ y <= x /\ Re(cexp(Cx y)) = x`
  MP_TAC THENL [ALL_TAC; MESON_TAC[CX_EXP; RE_CX]] THEN
  MATCH_MP_TAC IVT_INCREASING_RE THEN
  SIMP_TAC[GSYM CX_EXP; RE_CX; CONTINUOUS_AT_CEXP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x /\ &0 < y ==> --y <= x`) THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ];
    ONCE_REWRITE_TAC[GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_EXP_NEG; REAL_INV_INV; REAL_LT_INV_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 + x <= y ==> x <= y`) THEN
  ASM_SIMP_TAC[REAL_EXP_LE_X; REAL_LE_INV_EQ; REAL_LT_IMP_LE]);;

let LOG_EXP = prove
 (`!x. log(exp x) = x`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_INJ] THEN
  SIMP_TAC[EXP_LOG; REAL_EXP_POS_LT]);;

let REAL_EXP_LOG = prove
 (`!x. (exp(log x) = x) <=> &0 < x`,
  MESON_TAC[EXP_LOG; REAL_EXP_POS_LT]);;

let LOG_MUL = prove
 (`!x y. &0 < x /\ &0 < y ==> (log(x * y) = log(x) + log(y))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_INJ] THEN
  ASM_SIMP_TAC[REAL_EXP_ADD; REAL_LT_MUL; EXP_LOG]);;

let LOG_INJ = prove
 (`!x y. &0 < x /\ &0 < y ==> (log(x) = log(y) <=> x = y)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_INJ] THEN
  ASM_SIMP_TAC[EXP_LOG]);;

let LOG_1 = prove
 (`log(&1) = &0`,
  ONCE_REWRITE_TAC[GSYM REAL_EXP_INJ] THEN
  REWRITE_TAC[REAL_EXP_0; REAL_EXP_LOG; REAL_LT_01]);;

let LOG_INV = prove
 (`!x. &0 < x ==> (log(inv x) = --(log x))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_INJ] THEN
  ASM_SIMP_TAC[REAL_EXP_NEG; EXP_LOG; REAL_LT_INV_EQ]);;

let LOG_DIV = prove
 (`!x y. &0 < x /\ &0 < y ==> log(x / y) = log(x) - log(y)`,
  SIMP_TAC[real_div; real_sub; LOG_MUL; LOG_INV; REAL_LT_INV_EQ]);;

let LOG_MONO_LT = prove
 (`!x y. &0 < x /\ &0 < y ==> (log(x) < log(y) <=> x < y)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_MONO_LT] THEN
  ASM_SIMP_TAC[EXP_LOG]);;

let LOG_MONO_LT_IMP = prove
 (`!x y. &0 < x /\ x < y ==> log(x) < log(y)`,
  MESON_TAC[LOG_MONO_LT; REAL_LT_TRANS]);;

let LOG_MONO_LT_REV = prove
 (`!x y. &0 < x /\ &0 < y /\ log x < log y ==> x < y`,
  MESON_TAC[LOG_MONO_LT]);;

let LOG_MONO_LE = prove
 (`!x y. &0 < x /\ &0 < y ==> (log(x) <= log(y) <=> x <= y)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG]);;

let LOG_MONO_LE_IMP = prove
 (`!x y. &0 < x /\ x <= y ==> log(x) <= log(y)`,
  MESON_TAC[LOG_MONO_LE; REAL_LT_IMP_LE; REAL_LTE_TRANS]);;

let LOG_MONO_LE_REV = prove
 (`!x y. &0 < x /\ &0 < y /\ log x <= log y ==> x <= y`,
  MESON_TAC[LOG_MONO_LE]);;

let LOG_POW = prove
 (`!n x. &0 < x ==> (log(x pow n) = &n * log(x))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_INJ] THEN
  ASM_SIMP_TAC[REAL_EXP_N; EXP_LOG; REAL_POW_LT]);;

let LOG_LE_STRONG = prove
 (`!x. &0 < &1 + x ==> log(&1 + x) <= x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_EXP_LE_X]);;

let LOG_LE = prove
 (`!x. &0 <= x ==> log(&1 + x) <= x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&0 <= x ==> &0 < &1 + x`; REAL_EXP_LE_X]);;

let LOG_LT_X = prove
 (`!x. &0 < x ==> log(x) < x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN
  ASM_SIMP_TAC[EXP_LOG] THEN MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let LOG_POS = prove
 (`!x. &1 <= x ==> &0 <= log(x)`,
  REWRITE_TAC[GSYM LOG_1] THEN
  SIMP_TAC[LOG_MONO_LE; ARITH_RULE `&1 <= x ==> &0 < x`; REAL_LT_01]);;

let LOG_POS_LT = prove
 (`!x. &1 < x ==> &0 < log(x)`,
  REWRITE_TAC[GSYM LOG_1] THEN
  SIMP_TAC[LOG_MONO_LT; ARITH_RULE `&1 < x ==> &0 < x`; REAL_LT_01]);;

let LOG_PRODUCT = prove
 (`!f:A->real s.
        FINITE s /\ (!x. x IN s ==> &0 < f x)
        ==> log(product s f) = sum s (\x. log(f x))`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; SUM_CLAUSES; LOG_1; FORALL_IN_INSERT; LOG_MUL;
           PRODUCT_POS_LT]);;

(* ------------------------------------------------------------------------- *)
(* Deduce periodicity just from derivative and zero values.                  *)
(* ------------------------------------------------------------------------- *)

let SIN_NEARZERO = prove
 (`?x. &0 < x /\ !y. &0 < y /\ y <= x ==> &0 < sin(y)`,
  MP_TAC(SPEC `&1 / &2` (CONJUNCT2
   (REWRITE_RULE[has_complex_derivative; HAS_DERIVATIVE_AT_ALT]
    (ISPEC `Cx(&0)` HAS_COMPLEX_DERIVATIVE_CSIN)))) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[CSIN_0; COMPLEX_SUB_RZERO; CCOS_0; COMPLEX_MUL_LZERO;
              COMPLEX_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Cx y`) THEN
  ASM_REWRITE_TAC[GSYM CX_SIN; COMPLEX_NORM_CX; GSYM CX_SUB] THEN
  ASM_REAL_ARITH_TAC);;

let SIN_NONTRIVIAL = prove
 (`?x. &0 < x /\ ~(sin x = &0)`,
  MESON_TAC[REAL_LE_REFL; REAL_LT_REFL; SIN_NEARZERO]);;

let COS_NONTRIVIAL = prove
 (`?x. &0 < x /\ ~(cos x = &1)`,
  MP_TAC SIN_NONTRIVIAL THEN MATCH_MP_TAC MONO_EXISTS THEN
  MP_TAC SIN_CIRCLE THEN MATCH_MP_TAC MONO_FORALL THEN
  CONV_TAC REAL_FIELD);;

let COS_DOUBLE_BOUND = prove
 (`!x. &0 <= cos x ==> &2 * (&1 - cos x) <= &1 - cos(&2 * x)`,
  REWRITE_TAC[COS_DOUBLE_COS] THEN REWRITE_TAC[REAL_ARITH
   `&2 * (&1 - a) <= &1 - (&2 * b - &1) <=> b <= &1 * a`] THEN
  SIMP_TAC[REAL_POW_2; REAL_LE_RMUL; COS_BOUNDS]);;

let COS_GOESNEGATIVE_LEMMA = prove
 (`!x. cos(x) < &1 ==> ?n. cos(&2 pow n * x) < &0`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> p) ==> p`) THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n.  &2  pow n * (&1 - cos x) <= &1 - cos(&2 pow n * x)`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[real_pow; REAL_MUL_LID; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (&1 - cos(&2 pow n * x))` THEN
    ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_LE_LMUL; REAL_POS; COS_DOUBLE_BOUND];
    MP_TAC(ISPEC `&1 / (&1 - cos(x))` REAL_ARCH_POW2) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`)) THEN REAL_ARITH_TAC]);;

let COS_GOESNEGATIVE = prove
 (`?x. &0 < x /\ cos(x) < &0`,
  X_CHOOSE_TAC `x:real` COS_NONTRIVIAL THEN
  MP_TAC(SPEC `x:real` COS_GOESNEGATIVE_LEMMA) THEN ANTS_TAC THENL
   [MP_TAC(SPEC `x:real` COS_BOUNDS) THEN
    ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_ARITH `&0 < &2`]]);;

let COS_HASZERO = prove
 (`?x. &0 < x /\ cos(x) = &0`,
  X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC COS_GOESNEGATIVE THEN
  SUBGOAL_THEN `?x. &0 <= x /\ x <= z /\ Re(ccos(Cx x)) = &0` MP_TAC THENL
   [MATCH_MP_TAC IVT_DECREASING_RE THEN
    ASM_SIMP_TAC[GSYM CX_COS; RE_CX; REAL_LT_IMP_LE; COS_0; REAL_POS] THEN
    MESON_TAC[HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT;
              HAS_COMPLEX_DERIVATIVE_CCOS];
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[GSYM CX_COS; RE_CX] THEN
    MESON_TAC[COS_0; REAL_LE_LT; REAL_ARITH `~(&1 = &0)`]]);;

let SIN_HASZERO = prove
 (`?x. &0 < x /\ sin(x) = &0`,
  X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC COS_HASZERO THEN
  EXISTS_TAC `&2 * x` THEN ASM_SIMP_TAC[SIN_DOUBLE] THEN
  ASM_REAL_ARITH_TAC);;

let SIN_HASZERO_MINIMAL = prove
 (`?p. &0 < p /\ sin p = &0 /\ !x. &0 < x /\ x < p ==> ~(sin x = &0)`,
  X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC SIN_NEARZERO THEN
  MP_TAC(ISPECL
    [`{z | z IN IMAGE Cx {x | x >= e} /\ csin z IN {Cx(&0)}}`; `Cx(&0)`]
    DISTANCE_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC; IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING; real_ge; GSYM CX_COS; CX_INJ] THEN
    REWRITE_TAC[dist; GSYM CX_SUB; GSYM CX_SIN; CX_INJ; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    REWRITE_TAC[REAL_ARITH `abs(&0 - x) = abs x`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `x:real` THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real`))] THEN
    ASM_REAL_ARITH_TAC] THEN
  X_CHOOSE_TAC `a:real` SIN_HASZERO THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `Cx a` THEN
    ASM_REWRITE_TAC[IN_SING; IN_IMAGE; IN_ELIM_THM; GSYM CX_SIN] THEN
    ASM_MESON_TAC[REAL_ARITH `x >= w \/ x <= w`; REAL_LT_REFL]] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
  REWRITE_TAC[CONTINUOUS_ON_CSIN; CLOSED_SING] THEN
  SUBGOAL_THEN
   `IMAGE Cx {x | x >= e} = {z | Im(z) = &0} INTER {z | Re(z) >= e}`
   (fun th -> SIMP_TAC[th; CLOSED_INTER; CLOSED_HALFSPACE_IM_EQ;
                           CLOSED_HALFSPACE_RE_GE]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
  REWRITE_TAC[FORALL_COMPLEX; COMPLEX_EQ; RE; IM; RE_CX; IM_CX] THEN
  MESON_TAC[]);;

let pi = new_definition
 `pi = @p. &0 < p /\ sin(p) = &0 /\ !x. &0 < x /\ x < p ==> ~(sin(x) = &0)`;;

let PI_WORKS = prove
 (`&0 < pi /\ sin(pi) = &0 /\ !x. &0 < x /\ x < pi ==> ~(sin x = &0)`,
  REWRITE_TAC[pi] THEN CONV_TAC SELECT_CONV THEN
  REWRITE_TAC[SIN_HASZERO_MINIMAL]);;

(* ------------------------------------------------------------------------- *)
(* Now more relatively easy consequences.                                    *)
(* ------------------------------------------------------------------------- *)

let PI_POS = prove
 (`&0 < pi`,
  REWRITE_TAC[PI_WORKS]);;

let PI_POS_LE = prove
 (`&0 <= pi`,
  REWRITE_TAC[REAL_LE_LT; PI_POS]);;

let PI_NZ = prove
 (`~(pi = &0)`,
  SIMP_TAC[PI_POS; REAL_LT_IMP_NZ]);;

let REAL_ABS_PI = prove
 (`abs pi = pi`,
  REWRITE_TAC[real_abs; PI_POS_LE]);;

let SIN_PI = prove
 (`sin(pi) = &0`,
  REWRITE_TAC[PI_WORKS]);;

let SIN_POS_PI = prove
 (`!x. &0 < x /\ x < pi ==> &0 < sin(x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC SIN_NEARZERO THEN
  MP_TAC(ISPECL [`csin`; `e:real`; `x:real`; `&0`] IVT_DECREASING_RE) THEN
  ASM_SIMP_TAC[NOT_IMP; CONTINUOUS_AT_CSIN; GSYM CX_SIN; RE_CX; SIN_0] THEN
  ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LET_ANTISYM; PI_WORKS; REAL_LET_TRANS;
                REAL_LTE_TRANS]);;

let COS_PI2 = prove
 (`cos(pi / &2) = &0`,
  MP_TAC(SYM(SPEC `pi / &2` SIN_DOUBLE)) THEN
  REWRITE_TAC[REAL_HALF; SIN_PI; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < y ==> y = &0 \/ z = &0 ==> z = &0`) THEN
  MATCH_MP_TAC SIN_POS_PI THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let COS_PI = prove
 (`cos(pi) = -- &1`,
  ONCE_REWRITE_TAC[REAL_ARITH `pi = &2 * pi / &2`] THEN
  REWRITE_TAC[COS_DOUBLE_COS; COS_PI2] THEN REAL_ARITH_TAC);;

let SIN_PI2 = prove
 (`sin(pi / &2) = &1`,
  MP_TAC(SPEC `pi / &2` SIN_CIRCLE) THEN
  REWRITE_TAC[COS_PI2; REAL_POW_2; REAL_ADD_RID; REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_RING `x * x = &1 <=> x = &1 \/ x = -- &1`] THEN
  MP_TAC(SPEC `pi / &2` SIN_POS_PI) THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let SIN_COS = prove
 (`!x. sin(x) = cos(pi / &2 - x)`,
  REWRITE_TAC[COS_SUB; COS_PI2; SIN_PI2] THEN REAL_ARITH_TAC);;

let COS_SIN = prove
 (`!x. cos(x) = sin(pi / &2 - x)`,
  REWRITE_TAC[SIN_SUB; COS_PI2; SIN_PI2] THEN REAL_ARITH_TAC);;

let SIN_PERIODIC_PI = prove
 (`!x. sin(x + pi) = --(sin(x))`,
  REWRITE_TAC[SIN_ADD; SIN_PI; COS_PI] THEN REAL_ARITH_TAC);;

let COS_PERIODIC_PI = prove
 (`!x. cos(x + pi) = --(cos(x))`,
  REWRITE_TAC[COS_ADD; SIN_PI; COS_PI] THEN REAL_ARITH_TAC);;

let SIN_PERIODIC = prove
 (`!x. sin(x + &2 * pi) = sin(x)`,
  REWRITE_TAC[REAL_MUL_2; REAL_ADD_ASSOC; SIN_PERIODIC_PI; REAL_NEG_NEG]);;

let COS_PERIODIC = prove
 (`!x. cos(x + &2 * pi) = cos(x)`,
  REWRITE_TAC[REAL_MUL_2; REAL_ADD_ASSOC; COS_PERIODIC_PI; REAL_NEG_NEG]);;

let SIN_NPI = prove
 (`!n. sin(&n * pi) = &0`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_MUL_LID; REAL_ADD_RDISTRIB;
                  REAL_NEG_0; SIN_PERIODIC_PI; REAL_MUL_LZERO; SIN_0]);;

let COS_NPI = prove
 (`!n. cos(&n * pi) = --(&1) pow n`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[real_pow; REAL_MUL_LZERO; COS_0; COS_PERIODIC_PI;
    REAL_MUL_LID; REAL_MUL_LNEG; GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB]);;

let COS_POS_PI2 = prove
 (`!x. &0 < x /\ x < pi / &2 ==> &0 < cos(x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ccos`; `&0`; `x:real`; `&0`] IVT_DECREASING_RE) THEN
  ASM_SIMP_TAC[CONTINUOUS_AT_CCOS; REAL_LT_IMP_LE; GSYM CX_COS; RE_CX] THEN
  REWRITE_TAC[COS_0; REAL_POS] THEN DISCH_THEN(X_CHOOSE_TAC `y:real`) THEN
  MP_TAC(SPEC `y:real` SIN_DOUBLE) THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  MATCH_MP_TAC(last(CONJUNCTS PI_WORKS)) THEN REPEAT(POP_ASSUM MP_TAC) THEN
  ASM_CASES_TAC `y = &0` THEN ASM_REWRITE_TAC[COS_0] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let SIN_POS_PI2 = prove
 (`!x. &0 < x /\ x < pi / &2 ==> &0 < sin(x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN
  ASM_REAL_ARITH_TAC);;

let COS_POS_PI = prove
 (`!x. --(pi / &2) < x /\ x < pi / &2 ==> &0 < cos(x)`,
  GEN_TAC THEN MP_TAC(SPEC `abs x` COS_POS_PI2) THEN REWRITE_TAC[COS_ABS] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[COS_0] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let COS_POS_PI_LE = prove
 (`!x. --(pi / &2) <= x /\ x <= pi / &2 ==> &0 <= cos(x)`,
  REWRITE_TAC[REAL_LE_LT] THEN MESON_TAC[COS_PI2; COS_NEG; COS_POS_PI]);;

let SIN_POS_PI_LE = prove
 (`!x. &0 <= x /\ x <= pi ==> &0 <= sin(x)`,
  REWRITE_TAC[REAL_LE_LT] THEN MESON_TAC[SIN_0; SIN_PI; SIN_POS_PI]);;

let SIN_PIMUL_EQ_0 = prove
 (`!n. sin(n * pi) = &0 <=> integer(n)`,
  SUBGOAL_THEN `!n. integer n ==> sin(n * pi) = &0 /\ ~(cos(n * pi) = &0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[INTEGER_CASES] THEN GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_LNEG; COS_NPI; SIN_NPI;
                 SIN_NEG; COS_NEG; REAL_POW_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[] THEN
  SUBST1_TAC(last(CONJUNCTS(SPEC `n:real` FLOOR_FRAC))) THEN
  ASM_SIMP_TAC[REAL_ADD_RDISTRIB; FLOOR; SIN_ADD; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[REAL_ADD_LID; REAL_ENTIRE; FLOOR] THEN
  DISCH_TAC THEN MP_TAC(SPEC `frac n * pi` SIN_POS_PI) THEN
  ASM_SIMP_TAC[REAL_LT_REFL; GSYM REAL_LT_RDIV_EQ; GSYM REAL_LT_LDIV_EQ;
               PI_POS; REAL_DIV_REFL; REAL_LT_IMP_NZ] THEN
  MP_TAC(SPEC `n:real` FLOOR_FRAC) THEN ASM_CASES_TAC `frac n = &0` THEN
  ASM_REWRITE_TAC[FLOOR; REAL_ADD_RID] THEN
  ASM_REAL_ARITH_TAC);;

let SIN_EQ_0 = prove
 (`!x. sin(x) = &0 <=> ?n. integer n /\ x = n * pi`,
  GEN_TAC THEN MP_TAC(SPEC `x / pi` SIN_PIMUL_EQ_0) THEN
  SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; GSYM REAL_EQ_LDIV_EQ; PI_POS] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM1]);;

let COS_EQ_0 = prove
 (`!x. cos(x) = &0 <=> ?n. integer n /\ x = (n + &1 / &2) * pi`,
  GEN_TAC THEN REWRITE_TAC[COS_SIN; SIN_EQ_0] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `--n:real` THEN ASM_REWRITE_TAC[INTEGER_NEG] THEN
  ASM_REAL_ARITH_TAC);;

let SIN_ZERO_PI = prove
 (`!x. sin(x) = &0 <=> (?n. x = &n * pi) \/ (?n. x = --(&n * pi))`,
  REWRITE_TAC[SIN_EQ_0; INTEGER_CASES] THEN MESON_TAC[REAL_MUL_LNEG]);;

let COS_ZERO_PI = prove
 (`!x. cos(x) = &0 <=>
       (?n. x = (&n + &1 / &2) * pi) \/ (?n. x = --((&n + &1 / &2) * pi))`,
  GEN_TAC THEN REWRITE_TAC[COS_EQ_0; INTEGER_CASES; RIGHT_OR_DISTRIB] THEN
  REWRITE_TAC[EXISTS_OR_THM; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN SIMP_TAC[UNWIND_THM2] THEN EQ_TAC THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THENL
   [DISJ1_TAC THEN EXISTS_TAC `n:num`;
    ASM_CASES_TAC `n = 0` THENL
     [DISJ1_TAC THEN EXISTS_TAC `0`;
      DISJ2_TAC THEN EXISTS_TAC `n - 1`];
    DISJ1_TAC THEN EXISTS_TAC `n:num`;
    DISJ2_TAC THEN EXISTS_TAC `n + 1`] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD;
               ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  REAL_ARITH_TAC);;

let SIN_ZERO = prove
 (`!x. (sin(x) = &0) <=> (?n. EVEN n /\ x = &n * (pi / &2)) \/
                         (?n. EVEN n /\ x = --(&n * (pi / &2)))`,
  REWRITE_TAC[SIN_ZERO_PI; EVEN_EXISTS; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_MUL; REAL_ARITH `(&2 * x) * y / &2 = x * y`]);;

let COS_ZERO = prove
 (`!x. cos(x) = &0 <=> (?n. ~EVEN n /\ (x = &n * (pi / &2))) \/
                       (?n. ~EVEN n /\ (x = --(&n * (pi / &2))))`,
  REWRITE_TAC[COS_ZERO_PI; NOT_EVEN; ODD_EXISTS; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUC;
           REAL_ARITH `(&2 * x + &1) * y / &2 = (x + &1 / &2) * y`]);;

let COS_ONE_2PI = prove
 (`!x. (cos(x) = &1) <=> (?n. x = &n * &2 * pi) \/ (?n. x = --(&n * &2 * pi))`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `sin(x)` o MATCH_MP (REAL_RING
     `c = &1 ==> !s. s pow 2 + c pow 2 = &1 ==> s = &0`)) THEN
    REWRITE_TAC[SIN_ZERO_PI; SIN_CIRCLE] THEN
    DISCH_THEN(DISJ_CASES_THEN(X_CHOOSE_THEN `n:num` SUBST_ALL_TAC)) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[COS_NEG; COS_NPI; REAL_POW_NEG] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_POW_ONE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM (DISJ_CASES_THEN CHOOSE_TAC) THEN
    ASM_REWRITE_TAC[COS_NEG; REAL_MUL_ASSOC; REAL_OF_NUM_MUL; COS_NPI;
                    REAL_POW_NEG; EVEN_MULT; ARITH; REAL_POW_ONE]]);;

let SIN_COS_SQRT = prove
 (`!x. &0 <= sin(x) ==> (sin(x) = sqrt(&1 - (cos(x) pow 2)))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
  ASM_REWRITE_TAC[SIN_CIRCLE; REAL_EQ_SUB_LADD]);;

let SIN_EQ_0_PI = prove
 (`!x. --pi < x /\ x < pi /\ sin(x) = &0 ==> x = &0`,
  GEN_TAC THEN REWRITE_TAC[SIN_EQ_0; CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
   (X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[REAL_ARITH
   `--p < n * p /\ n * p < p <=> -- &1 * p < n * p /\ n * p < &1 * p`] THEN
  SIMP_TAC[REAL_ENTIRE; REAL_LT_IMP_NZ; REAL_LT_RMUL_EQ; PI_POS] THEN
  MP_TAC(SPEC `n:real` REAL_ABS_INTEGER_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let COS_TREBLE_COS = prove
 (`!x. cos(&3 * x) = &4 * cos(x) pow 3 - &3 * cos x`,
  GEN_TAC THEN REWRITE_TAC[COS_ADD; REAL_ARITH `&3 * x = &2 * x + x`] THEN
  REWRITE_TAC[SIN_DOUBLE; COS_DOUBLE_COS] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

let COS_PI6 = prove
 (`cos(pi / &6) = sqrt(&3) / &2`,
  MP_TAC(ISPEC `pi / &6` COS_TREBLE_COS) THEN
  REWRITE_TAC[REAL_ARITH `&3 * x / &6 = x / &2`; COS_PI2] THEN
  REWRITE_TAC[REAL_RING `&0 = &4 * c pow 3 - &3 * c <=>
                         c = &0 \/ (&2 * c) pow 2 = &3`] THEN
  SUBGOAL_THEN `&0 < cos(pi / &6)` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_POS_PI THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `sqrt`) THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LE_MUL; REAL_LT_IMP_LE; REAL_POS] THEN
    REAL_ARITH_TAC]);;

let SIN_PI6 = prove
 (`sin(pi / &6) = &1 / &2`,
  MP_TAC(SPEC `pi / &6` SIN_CIRCLE) THEN REWRITE_TAC[COS_PI6] THEN
  SIMP_TAC[REAL_POW_DIV; SQRT_POW_2; REAL_POS] THEN MATCH_MP_TAC(REAL_FIELD
   `~(s + &1 / &2 = &0) ==> s pow 2 + &3 / &2 pow 2 = &1 ==> s = &1 / &2`) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x + &1 / &2 = &0)`) THEN
  MATCH_MP_TAC SIN_POS_PI THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let SIN_POS_PI_REV = prove
 (`!x. &0 <= x /\ x <= &2 * pi /\ &0 < sin x ==> &0 < x /\ x < pi`,
  GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[SIN_0; REAL_LT_REFL] THEN
  ASM_CASES_TAC `x = pi` THEN
  ASM_REWRITE_TAC[SIN_PI; REAL_LT_REFL] THEN
  ASM_CASES_TAC `x = &2 * pi` THEN
  ASM_REWRITE_TAC[SIN_NPI; REAL_LT_REFL] THEN
  REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sin(&2 * pi - x)` MP_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SIN_SUB; SIN_NPI; COS_NPI] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Prove totality of trigs.                                                  *)
(* ------------------------------------------------------------------------- *)

let SIN_TOTAL_POS = prove
 (`!y. &0 <= y /\ y <= &1
       ==> ?x. &0 <= x /\ x <= pi / &2 /\ sin(x) = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`csin`; `&0`; `pi / &2`; `y:real`] IVT_INCREASING_RE) THEN
  ASM_REWRITE_TAC[GSYM CX_SIN; RE_CX; SIN_0; SIN_PI2] THEN
  SIMP_TAC[CONTINUOUS_AT_CSIN; PI_POS; REAL_ARITH `&0 < x ==> &0 <= x / &2`]);;

let SINCOS_TOTAL_PI2 = prove
 (`!x y. &0 <= x /\ &0 <= y /\ x pow 2 + y pow 2 = &1
         ==> ?t. &0 <= t /\ t <= pi / &2 /\ x = cos t /\ y = sin t`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `y:real` SIN_TOTAL_POS) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x pow 2 + y pow 2 = &1
      ==> (&1 < y ==> &1 pow 2 < y pow 2) /\ &0 <= x * x
          ==> y <= &1`)) THEN
    SIMP_TAC[REAL_LE_SQUARE; REAL_POW_LT2; REAL_POS; ARITH];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `x = cos t \/ x = --(cos t)` MP_TAC THENL
     [MP_TAC(SPEC `t:real` SIN_CIRCLE);
      MP_TAC(SPEC `t:real` COS_POS_PI_LE)] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD]);;

let SINCOS_TOTAL_PI = prove
 (`!x y. &0 <= y /\ x pow 2 + y pow 2 = &1
         ==> ?t. &0 <= t /\ t <= pi /\ x = cos t /\ y = sin t`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH `&0 <= x \/ &0 <= --x`) THENL
   [MP_TAC(SPECL [`x:real`; `y:real`] SINCOS_TOTAL_PI2);
    MP_TAC(SPECL [`--x:real`; `y:real`] SINCOS_TOTAL_PI2)] THEN
  ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `t:real`; EXISTS_TAC `pi - t`] THEN
  ASM_REWRITE_TAC[SIN_SUB; COS_SUB; SIN_PI; COS_PI] THEN
  ASM_REAL_ARITH_TAC);;

let SINCOS_TOTAL_2PI = prove
 (`!x y. x pow 2 + y pow 2 = &1
         ==> ?t. &0 <= t /\ t < &2 * pi /\ x = cos t /\ y = sin t`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = &1 /\ y = &0` THENL
   [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[SIN_0; COS_0] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `&0 <= y \/ &0 <= --y`) THENL
   [MP_TAC(SPECL [`x:real`; `y:real`] SINCOS_TOTAL_PI);
    MP_TAC(SPECL [`x:real`; `--y:real`] SINCOS_TOTAL_PI)] THEN
  ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `t:real`; EXISTS_TAC `&2 * pi - t`] THEN
  ASM_REWRITE_TAC[SIN_SUB; COS_SUB; SIN_NPI; COS_NPI] THENL
   [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN ASM_CASES_TAC `t = &0` THEN
  ASM_REWRITE_TAC[SIN_0; COS_0] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let CIRCLE_SINCOS = prove
 (`!x y. x pow 2 + y pow 2 = &1 ==> ?t. x = cos(t) /\ y = sin(t)`,
  MESON_TAC[SINCOS_TOTAL_2PI]);;

(* ------------------------------------------------------------------------- *)
(* Polar representation.                                                     *)
(* ------------------------------------------------------------------------- *)

let CX_PI_NZ = prove
 (`~(Cx pi = Cx(&0))`,
  SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ; PI_POS]);;

let COMPLEX_UNIMODULAR_POLAR = prove
 (`!z. (norm z = &1) ==> ?x. z = complex(cos(x),sin(x))`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o C AP_THM `2` o AP_TERM `(pow):real->num->real`) THEN
  REWRITE_TAC[complex_norm] THEN
  SIMP_TAC[REAL_POW_2; REWRITE_RULE[REAL_POW_2] SQRT_POW_2;
           REAL_LE_SQUARE; REAL_LE_ADD] THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:real` o MATCH_MP CIRCLE_SINCOS) THEN
  EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[COMPLEX_EQ; RE; IM]);;

let SIN_INTEGER_2PI = prove
 (`!n. integer n ==> sin((&2 * pi) * n) = &0`,
  REWRITE_TAC[SIN_EQ_0; REAL_ARITH `(&2 * pi) * n = (&2 * n) * pi`] THEN
  MESON_TAC[INTEGER_CLOSED]);;

let SIN_INTEGER_PI = prove
 (`!n. integer n ==> sin (n * pi) = &0`,
  REWRITE_TAC[INTEGER_CASES] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LNEG; SIN_NPI; SIN_NEG; REAL_NEG_0]);;

let COS_INTEGER_2PI = prove
 (`!n. integer n ==> cos((&2 * pi) * n) = &1`,
  REWRITE_TAC[INTEGER_CASES; REAL_ARITH `(&2 * pi) * n = (&2 * n) * pi`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RNEG; REAL_OF_NUM_MUL] THEN
  SIMP_TAC[COS_NEG; COS_NPI; REAL_POW_NEG; REAL_MUL_LNEG;
           ARITH; EVEN_MULT; REAL_POW_ONE]);;

let SINCOS_PRINCIPAL_VALUE = prove
 (`!x. ?y. (--pi < y /\ y <= pi) /\ (sin(y) = sin(x) /\ cos(y) = cos(x))`,
  GEN_TAC THEN EXISTS_TAC `pi - (&2 * pi) * frac((pi - x) / (&2 * pi))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[REAL_ARITH `--p < p - x <=> x < (&2 * p) * &1`;
             REAL_ARITH `p - x <= p <=> (&2 * p) * &0 <= x`;
             REAL_LT_LMUL_EQ; REAL_LE_LMUL_EQ; REAL_LT_MUL;
             PI_POS; REAL_OF_NUM_LT; ARITH; FLOOR_FRAC];
   REWRITE_TAC[FRAC_FLOOR; REAL_SUB_LDISTRIB] THEN
   SIMP_TAC[REAL_DIV_LMUL; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH; REAL_LT_IMP_NZ;
    PI_POS; REAL_ARITH `a - (a - b - c):real = b + c`; SIN_ADD; COS_ADD] THEN
   SIMP_TAC[FLOOR_FRAC; SIN_INTEGER_2PI; COS_INTEGER_2PI] THEN
   CONV_TAC REAL_RING]);;

let CEXP_COMPLEX = prove
 (`!r t. cexp(complex(r,t)) = Cx(exp r) * complex(cos t,sin t)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
  REWRITE_TAC[RE; IM; CEXP_ADD; CEXP_EULER; CX_EXP] THEN
  REWRITE_TAC[COMPLEX_TRAD; CX_SIN; CX_COS]);;

let NORM_COSSIN = prove
 (`!t. norm(complex(cos t,sin t)) = &1`,
  REWRITE_TAC[complex_norm; RE; IM] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[SIN_CIRCLE; SQRT_1]);;

let NORM_CEXP = prove
 (`!z. norm(cexp z) = exp(Re z)`,
  REWRITE_TAC[FORALL_COMPLEX; CEXP_COMPLEX; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[NORM_COSSIN; RE; COMPLEX_NORM_CX] THEN
  MP_TAC REAL_EXP_POS_LT THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let NORM_CEXP_II = prove
 (`!t. norm (cexp (ii * Cx t)) = &1`,
  REWRITE_TAC [NORM_CEXP; RE_MUL_II; IM_CX; REAL_NEG_0; REAL_EXP_0]);;

let NORM_CEXP_IMAGINARY = prove
 (`!z. norm(cexp z) = &1 ==> Re(z) = &0`,
  REWRITE_TAC[NORM_CEXP; REAL_EXP_EQ_1]);;

let CEXP_EQ_1 = prove
 (`!z. cexp z = Cx(&1) <=> Re(z) = &0 /\ ?n. integer n /\ Im(z) = &2 * n * pi`,
  REWRITE_TAC[FORALL_COMPLEX; CEXP_COMPLEX; RE; IM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(MP_TAC o AP_TERM `norm:complex->real`) THEN
    SIMP_TAC[COMPLEX_NORM_MUL; CX_EXP; NORM_CEXP; RE_CX; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[NORM_COSSIN; REAL_ABS_NUM; REAL_ABS_EXP; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_EXP_EQ_1] THEN DISCH_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_EXP_0; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[COMPLEX_EQ; RE; IM; RE_CX; IM_CX] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SIN_EQ_0]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    EXISTS_TAC `m / &2` THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    ONCE_REWRITE_TAC[GSYM INTEGER_ABS] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [GSYM COS_ABS]) THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [integer]) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THEN
    SIMP_TAC[real_abs; PI_POS; REAL_LT_IMP_LE; COS_NPI] THEN
    REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN
    COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_ARITH `(&2 * x) / &2 = x`] THEN
    REWRITE_TAC[INTEGER_CLOSED];
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (X_CHOOSE_TAC `n:real`)) THEN
    ASM_SIMP_TAC[REAL_EXP_0; COMPLEX_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `&2 * x * y = (&2 * y) * x`] THEN
    ASM_SIMP_TAC[SIN_INTEGER_2PI; COS_INTEGER_2PI] THEN
    SIMPLE_COMPLEX_ARITH_TAC]);;

let CEXP_EQ = prove
 (`!w z. cexp w = cexp z <=> ?n. integer n /\ w = z + Cx(&2 * n * pi) * ii`,
  SIMP_TAC[CEXP_NZ; COMPLEX_FIELD
   `~(z = Cx(&0)) ==> (w = z <=> w / z = Cx(&1))`] THEN
  REWRITE_TAC[GSYM CEXP_SUB; CEXP_EQ_1; RE_SUB; IM_SUB; REAL_SUB_0] THEN
  SIMP_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_NEG_0; REAL_ADD_RID; REAL_EQ_SUB_RADD] THEN
  MESON_TAC[REAL_ADD_SYM]);;

let COMPLEX_EQ_CEXP = prove
 (`!w z. abs(Im w - Im z) < &2 * pi /\ cexp w = cexp z ==> w = z`,
  SIMP_TAC[CEXP_NZ; GSYM CEXP_SUB; CEXP_EQ_1; COMPLEX_FIELD
   `~(a = Cx(&0)) /\ ~(b = Cx(&0)) ==> (a = b <=> a / b = Cx(&1))`] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `abs(Im w - Im z) < &2 * pi` THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM IM_SUB; REAL_ABS_MUL; REAL_ABS_PI; REAL_ABS_NUM] THEN
  SIMP_TAC[REAL_MUL_ASSOC; REAL_LT_RMUL_EQ; PI_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> ~(&2 * x < &2)`) THEN
  MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(w:complex = z)` THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0] THEN
  ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX; REAL_MUL_LZERO; REAL_MUL_RZERO]);;

let CEXP_INTEGER_2PI = prove
 (`!n. integer n ==> cexp(Cx(&2 * n * pi) * ii) = Cx(&1)`,
  REWRITE_TAC[CEXP_EQ_1; IM_MUL_II; RE_MUL_II; RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_NEG_0] THEN MESON_TAC[]);;

let SIN_COS_EQ = prove
 (`!x y. sin y = sin x /\ cos y = cos x <=>
         ?n. integer n /\ y = x + &2 * n * pi`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL [`ii * Cx y`; `ii * Cx x`] CEXP_EQ) THEN
  REWRITE_TAC[CEXP_EULER; GSYM CX_SIN; GSYM CX_COS] THEN
  REWRITE_TAC[COMPLEX_RING `ii * y = ii * x + z * ii <=> y = x + z`] THEN
  REWRITE_TAC[GSYM CX_ADD; CX_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX;
              REAL_NEG_0; REAL_ADD_LID; REAL_ADD_RID] THEN
  MESON_TAC[]);;

let SIN_COS_INJ = prove
 (`!x y. sin x = sin y /\ cos x = cos y /\ abs(x - y) < &2 * pi ==> x = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM CX_INJ] THEN
  MATCH_MP_TAC(COMPLEX_RING `ii * x = ii * y ==> x = y`) THEN
  MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
  ASM_REWRITE_TAC[CEXP_EULER; GSYM CX_SIN; GSYM CX_COS] THEN
  ASM_REWRITE_TAC[IM_MUL_II; RE_CX]);;

let CEXP_II_NE_1 = prove
 (`!x. &0 < x /\ x < &2 * pi ==> ~(cexp(ii * Cx x) = Cx(&1))`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[CEXP_EQ_1] THEN
  REWRITE_TAC[RE_MUL_II; IM_CX; IM_MUL_II; IM_CX; REAL_NEG_0; RE_CX] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  UNDISCH_TAC `&0 < &2 * n * pi` THEN ASM_CASES_TAC `n = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL] THEN
  MP_TAC(ISPEC `n:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
   `&2 * n * pi < &2 * pi ==> &0 < (&1 - n) * &2 * pi`)) THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ; PI_POS; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  ASM_REAL_ARITH_TAC);;

let CSIN_EQ_0 = prove
 (`!z. csin z = Cx(&0) <=> ?n. integer n /\ z = Cx(n * pi)`,
  GEN_TAC THEN REWRITE_TAC[csin; COMPLEX_MUL_LNEG; CEXP_NEG] THEN
  SIMP_TAC[CEXP_NZ; COMPLEX_FIELD `~(z = Cx(&0))
        ==> ((z - inv z) / (Cx(&2) * ii) = Cx(&0) <=> z pow 2 = Cx(&1))`] THEN
  REWRITE_TAC[GSYM CEXP_N; CEXP_EQ_1] THEN
  REWRITE_TAC[RE_MUL_CX; IM_MUL_CX; RE_MUL_II; IM_MUL_II] THEN
  REWRITE_TAC[COMPLEX_EQ; IM_CX; RE_CX; RIGHT_AND_EXISTS_THM] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN REAL_ARITH_TAC);;

let CCOS_EQ_0 = prove
 (`!z. ccos z = Cx(&0) <=> ?n. integer n /\ z = Cx((n + &1 / &2) * pi)`,
  GEN_TAC THEN MP_TAC(SPEC `z - Cx(pi / &2)` CSIN_EQ_0) THEN
  REWRITE_TAC[CSIN_SUB; GSYM CX_SIN; GSYM CX_COS; SIN_PI2; COS_PI2] THEN
  SIMP_TAC[COMPLEX_RING `s * Cx(&0) - c * Cx(&1) = Cx(&0) <=> c = Cx(&0)`] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; COMPLEX_EQ_SUB_RADD; CX_ADD] THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 * x = x / &2`]);;

let CCOS_EQ_1 = prove
 (`!z. ccos z = Cx(&1) <=> ?n. integer n /\ z = Cx(&2 * n * pi)`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
   [COMPLEX_RING `z = Cx(&2) * z / Cx(&2)`] THEN
  REWRITE_TAC[CCOS_DOUBLE_CSIN; COMPLEX_RING
   `a - Cx(&2) * s pow 2 = a <=> s = Cx(&0)`] THEN
  REWRITE_TAC[CSIN_EQ_0; CX_MUL] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN
  CONV_TAC COMPLEX_RING);;

let CSIN_EQ_1 = prove
 (`!z. csin z = Cx(&1) <=> ?n. integer n /\ z = Cx((&2 * n + &1 / &2) * pi)`,
  GEN_TAC THEN MP_TAC(SPEC `z - Cx(pi / &2)` CCOS_EQ_1) THEN
  REWRITE_TAC[CCOS_SUB; GSYM CX_SIN; GSYM CX_COS; SIN_PI2; COS_PI2] THEN
  SIMP_TAC[COMPLEX_RING `s * Cx(&0) + c * Cx(&1) = Cx(&1) <=> c = Cx(&1)`] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; COMPLEX_EQ_SUB_RADD; CX_ADD] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; REAL_ARITH `&1 / &2 * x = x / &2`]);;

let CSIN_EQ_MINUS1 = prove
 (`!z. csin z = --Cx(&1) <=>
       ?n. integer n /\ z = Cx((&2 * n + &3 / &2) * pi)`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_RING `z:complex = --w <=> --z = w`] THEN
  REWRITE_TAC[GSYM CSIN_NEG; CSIN_EQ_1] THEN
  REWRITE_TAC[COMPLEX_RING `--z:complex = w <=> z = --w`] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GSYM CX_NEG; CX_INJ] THEN
  EXISTS_TAC `--(n + &1)` THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

let CCOS_EQ_MINUS1 = prove
 (`!z. ccos z = --Cx(&1) <=>
       ?n. integer n /\ z = Cx((&2 * n + &1) * pi)`,
  GEN_TAC THEN MP_TAC(SPEC `z - Cx(pi / &2)` CSIN_EQ_1) THEN
  REWRITE_TAC[CSIN_SUB; GSYM CX_SIN; GSYM CX_COS; SIN_PI2; COS_PI2] THEN
  SIMP_TAC[COMPLEX_RING
    `s * Cx(&0) - c * Cx(&1) = Cx(&1) <=> c = --Cx(&1)`] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; COMPLEX_EQ_SUB_RADD; GSYM CX_ADD] THEN
  DISCH_TAC THEN EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
  SIMP_TAC[CX_INJ] THEN REAL_ARITH_TAC);;

let COS_EQ_1 = prove
 (`!x. cos x = &1 <=> ?n. integer n /\ x = &2 * n * pi`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CCOS_EQ_1]);;

let SIN_EQ_1 = prove
 (`!x. sin x = &1 <=> ?n. integer n /\ x = (&2 * n + &1 / &2) * pi`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CSIN_EQ_1]);;

let SIN_EQ_MINUS1 = prove
 (`!x. sin x = --(&1) <=> ?n. integer n /\ x = (&2 * n + &3 / &2) * pi`,
  REWRITE_TAC[GSYM CX_INJ; CX_NEG; CX_SIN; CSIN_EQ_MINUS1]);;

let COS_EQ_MINUS1 = prove
 (`!x. cos x = --(&1) <=>
       ?n. integer n /\ x = (&2 * n + &1) * pi`,
  REWRITE_TAC[GSYM CX_INJ; CX_NEG; CX_COS; CCOS_EQ_MINUS1]);;

let DIST_CEXP_II_1 = prove
 (`!z. norm(cexp(ii * Cx t) - Cx(&1)) = &2 * abs(sin(t / &2))`,
  GEN_TAC THEN REWRITE_TAC[NORM_EQ_SQUARE] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[GSYM NORM_POW_2]] THEN
  REWRITE_TAC[CEXP_EULER; COMPLEX_SQNORM; GSYM CX_COS; GSYM CX_SIN] THEN
  REWRITE_TAC[IM_ADD; RE_ADD; IM_SUB; RE_SUB; IM_MUL_II; RE_MUL_II] THEN
  REWRITE_TAC[RE_CX; IM_CX; REAL_POW2_ABS; REAL_POW_MUL] THEN
  MP_TAC(ISPEC `t / &2` COS_DOUBLE_SIN) THEN
  REWRITE_TAC[REAL_ARITH `&2 * t / &2 = t`] THEN
  MP_TAC(SPEC `t:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

let CX_SINH = prove
 (`Cx((exp x - inv(exp x)) / &2) = --ii * csin(ii * Cx x)`,
  REWRITE_TAC[csin; COMPLEX_RING `--ii * ii * z = z /\ ii * ii * z = --z`] THEN
  REWRITE_TAC[CEXP_NEG; GSYM CX_EXP; GSYM CX_INV; CX_SUB; CX_DIV] THEN
  CONV_TAC COMPLEX_FIELD);;

let CX_COSH = prove
 (`Cx((exp x + inv(exp x)) / &2) = ccos(ii * Cx x)`,
  REWRITE_TAC[ccos; COMPLEX_RING `--ii * ii * z = z /\ ii * ii * z = --z`] THEN
  REWRITE_TAC[CEXP_NEG; GSYM CX_EXP; GSYM CX_INV; CX_ADD; CX_DIV] THEN
  CONV_TAC COMPLEX_FIELD);;

let NORM_CCOS_POW_2 = prove
 (`!z. norm(ccos z) pow 2 =
       cos(Re z) pow 2 + (exp(Im z) - inv(exp(Im z))) pow 2 / &4`,
  REWRITE_TAC[FORALL_COMPLEX; RE; IM] THEN
  REWRITE_TAC[COMPLEX_TRAD; CCOS_ADD; COMPLEX_SQNORM] THEN
  SIMP_TAC[RE_SUB; IM_SUB; GSYM CX_COS; GSYM CX_SIN; IM_MUL_CX; RE_MUL_CX] THEN
  REWRITE_TAC[ccos; csin; CEXP_NEG; COMPLEX_FIELD
   `--ii * ii * z = z /\ ii * ii * z = --z /\
    z / (Cx(&2) * ii) = --(ii * z / Cx(&2))`] THEN
  REWRITE_TAC[RE_ADD; RE_SUB; IM_ADD; IM_SUB; RE_MUL_II; IM_MUL_II;
              RE_DIV_CX; IM_DIV_CX; RE_NEG; IM_NEG] THEN
  REWRITE_TAC[GSYM CX_EXP; GSYM CX_INV; IM_CX; RE_CX] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN MP_TAC(SPEC `y:real` REAL_EXP_NZ) THEN
  CONV_TAC REAL_FIELD);;

let NORM_CSIN_POW_2 = prove
 (`!z. norm(csin z) pow 2 =
       (exp(&2 * Im z) + inv(exp(&2 * Im z)) - &2 * cos(&2 * Re z)) / &4`,
  REWRITE_TAC[FORALL_COMPLEX; RE; IM] THEN
  REWRITE_TAC[COMPLEX_TRAD; CSIN_ADD; COMPLEX_SQNORM] THEN
  SIMP_TAC[RE_ADD; IM_ADD; GSYM CX_SIN; GSYM CX_SIN; IM_MUL_CX; RE_MUL_CX;
           GSYM CX_COS] THEN
  REWRITE_TAC[ccos; csin; CEXP_NEG; COMPLEX_FIELD
   `--ii * ii * z = z /\ ii * ii * z = --z /\
    z / (Cx(&2) * ii) = --(ii * z / Cx(&2))`] THEN
  REWRITE_TAC[RE_ADD; RE_SUB; IM_ADD; IM_SUB; RE_MUL_II; IM_MUL_II;
              RE_DIV_CX; IM_DIV_CX; RE_NEG; IM_NEG] THEN
  REWRITE_TAC[GSYM CX_EXP; GSYM CX_INV; IM_CX; RE_CX] THEN
  REWRITE_TAC[REAL_EXP_N; COS_DOUBLE] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN MP_TAC(SPEC `y:real` REAL_EXP_NZ) THEN
  CONV_TAC REAL_FIELD);;

let CSIN_EQ = prove
 (`!w z. csin w = csin z <=>
         ?n. integer n /\
             (w = z + Cx(&2 * n * pi) \/ w = --z + Cx((&2 * n + &1) * pi))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_SUB_0] THEN
  REWRITE_TAC[COMPLEX_SUB_CSIN; COMPLEX_ENTIRE; CSIN_EQ_0; CCOS_EQ_0] THEN
  REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ; OR_EXISTS_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:real` THEN
  ASM_CASES_TAC `integer(n)` THEN
  ASM_REWRITE_TAC[COMPLEX_FIELD `a / Cx(&2) = b <=> a = Cx(&2) * b`] THEN
  REWRITE_TAC[GSYM CX_MUL; REAL_ARITH
    `&2 * (n + &1 / &2) * pi = (&2 * n + &1) * pi`] THEN
  CONV_TAC COMPLEX_RING);;

let CCOS_EQ = prove
 (`!w z. ccos(w) = ccos(z) <=>
         ?n. integer n /\
             (w = z + Cx(&2 * n * pi) \/ w = --z + Cx(&2 * n * pi))`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV SYM_CONV) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM COMPLEX_SUB_0] THEN
  REWRITE_TAC[COMPLEX_SUB_CCOS; COMPLEX_ENTIRE; CSIN_EQ_0] THEN
  REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ; OR_EXISTS_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:real` THEN
  ASM_CASES_TAC `integer(n)` THEN ASM_REWRITE_TAC[CX_MUL] THEN
  CONV_TAC COMPLEX_RING);;

let SIN_EQ = prove
 (`!x y. sin x = sin y <=>
         ?n. integer n /\
             (x = y + &2 * n * pi \/ x = --y + (&2 * n + &1) * pi)`,
  REWRITE_TAC[GSYM CX_INJ; CX_SIN; CSIN_EQ] THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_NEG; CX_INJ]);;

let COS_EQ = prove
 (`!x y. cos x = cos y <=>
         ?n. integer n /\
             (x = y + &2 * n * pi \/ x = --y + &2 * n * pi)`,
  REWRITE_TAC[GSYM CX_INJ; CX_COS; CCOS_EQ] THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_NEG; CX_INJ]);;

let NORM_CCOS_LE = prove
 (`!z. norm(ccos z) <= exp(norm z)`,
  GEN_TAC THEN REWRITE_TAC[ccos] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 <= y <=> x <= &2 * y`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a) + norm(b) <= d ==> norm(a + b) <= d`) THEN
  REWRITE_TAC[NORM_CEXP; COMPLEX_MUL_LNEG; RE_NEG; REAL_EXP_NEG] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; RE_MUL_II; REAL_ABS_NUM] THEN
  MATCH_MP_TAC(REAL_ARITH
   `exp(&0) = &1 /\ (exp(&0) <= w \/ exp(&0) <= z) /\ (w <= u /\ z <= u)
    ==> w + z <= &2 * u`) THEN
  REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
  REWRITE_TAC[REAL_EXP_0] THEN
  MP_TAC(SPEC `z:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REAL_ARITH_TAC);;

let NORM_CCOS_PLUS1_LE = prove
 (`!z. norm(Cx(&1) + ccos z) <= &2 * exp(norm z)`,
  GEN_TAC THEN REWRITE_TAC[ccos] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM; COMPLEX_RING
   `Cx(&1) + (z + z') / Cx(&2) = (Cx(&2) + z + z') / Cx(&2)`] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 <= &2 * y <=> x <= &4 * y`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a) + norm(b) + norm(c) <= d ==> norm(a + b + c) <= d`) THEN
  REWRITE_TAC[NORM_CEXP; COMPLEX_MUL_LNEG; RE_NEG; REAL_EXP_NEG] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; RE_MUL_II; REAL_ABS_NUM] THEN
  MATCH_MP_TAC(REAL_ARITH
   `exp(&0) = &1 /\ (exp(&0) <= w \/ exp(&0) <= z) /\ (w <= u /\ z <= u)
    ==> &2 + w + z <= &4 * u`) THEN
  REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_EXP_MONO_LE] THEN
  REWRITE_TAC[REAL_EXP_0] THEN
  MP_TAC(SPEC `z:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Taylor series for complex exponential.                                    *)
(* ------------------------------------------------------------------------- *)

let TAYLOR_CEXP = prove
 (`!n z. norm(cexp z - vsum(0..n) (\k. z pow k / Cx(&(FACT k))))
         <= exp(abs(Re z)) * (norm z) pow (n + 1) / &(FACT n)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
   [`\k:num. cexp`; `n:num`; `segment[Cx(&0),z]`; `exp(abs(Re z))`]
        COMPLEX_TAYLOR) THEN
  REWRITE_TAC[CONVEX_SEGMENT; NORM_CEXP; REAL_EXP_MONO_LE] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN REPEAT STRIP_TAC THENL
     [GEN_REWRITE_TAC(RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
      COMPLEX_DIFF_TAC THEN REWRITE_TAC[COMPLEX_MUL_LID];
      ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0; VECTOR_MUL_RZERO] THEN
      REWRITE_TAC[VECTOR_ADD_LID; COMPLEX_CMUL; COMPLEX_NORM_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
      REWRITE_TAC[RE_MUL_CX; REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPECL [`Cx(&0)`; `z:complex`]) THEN
    SIMP_TAC[ENDS_IN_SEGMENT; COMPLEX_SUB_RZERO; CEXP_0; COMPLEX_MUL_LID]]);;

(* ------------------------------------------------------------------------- *)
(* Approximation to e.                                                       *)
(* ------------------------------------------------------------------------- *)

let E_APPROX_32 = prove
 (`abs(exp(&1) - &5837465777 / &2147483648) <= inv(&2 pow 32)`,
  MP_TAC(ISPECL [`14`; `Cx(&1)`] TAYLOR_CEXP) THEN
  SIMP_TAC[RE_CX; REAL_ABS_NUM; GSYM CX_EXP; GSYM CX_DIV; GSYM CX_SUB;
           COMPLEX_POW_ONE; COMPLEX_NORM_CX] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_VSUM_CONV) THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Taylor series for complex sine and cosine.                                *)
(* ------------------------------------------------------------------------- *)

let TAYLOR_CSIN_RAW = prove
 (`!n z. norm(csin z -
              vsum(0..n) (\k. if ODD k
                              then --ii * (ii * z) pow k / Cx(&(FACT k))
                              else Cx(&0)))
         <= exp(abs(Im z)) * (norm z) pow (n + 1) / &(FACT n)`,
  MP_TAC TAYLOR_CEXP THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN X_GEN_TAC `z:complex` THEN REWRITE_TAC[csin] THEN
  REWRITE_TAC[COMPLEX_FIELD
    `a / (Cx(&2) * ii) - b = (a - Cx(&2) * ii * b) / (Cx(&2) * ii)`] THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(SPEC `ii * z` th) THEN MP_TAC(SPEC `--ii * z` th)) THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; RE_NEG; REAL_ABS_NEG; RE_MUL_II] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_NEG;
              COMPLEX_NORM_II; REAL_ABS_NUM; REAL_MUL_RID; REAL_MUL_LID;
              REAL_ARITH `x / &2 <= y <=> x <= &2 * y`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `sp - sn = s2
    ==> norm(en - sn) <= d
        ==> norm(ep - sp) <= d ==> norm(ep - en - s2) <= &2 * d`) THEN
  SIMP_TAC[GSYM VSUM_SUB; GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_POW_NEG; GSYM NOT_EVEN] THEN ASM_CASES_TAC `EVEN k` THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[COMPLEX_RING `Cx(&2) * ii * --(ii * z) = Cx(&2) * z`] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let TAYLOR_CSIN = prove
 (`!n z. norm(csin z -
              vsum(0..n) (\k. --Cx(&1) pow k *
                              z pow (2 * k + 1) / Cx(&(FACT(2 * k + 1)))))
         <= exp(abs(Im z)) * norm(z) pow (2 * n + 3) / &(FACT(2 * n + 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`SUC(2 * n + 1)`; `z:complex`] TAYLOR_CSIN_RAW) THEN
  SIMP_TAC[VSUM_CLAUSES_NUMSEG; VSUM_PAIR_0; ODD_ADD; ODD_MULT; ARITH_ODD;
           LE_0; ODD; COMPLEX_ADD_LID; COMPLEX_ADD_RID] THEN
  SIMP_TAC[ARITH_RULE `SUC(2 * n + 1) = 2 * n + 2`; GSYM ADD_ASSOC; ARITH] THEN
  MATCH_MP_TAC(NORM_ARITH
   `s = t ==> norm(x - s) <= e ==> norm(x - t) <= e`) THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_POW_MUL; complex_div; COMPLEX_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[COMPLEX_POW_ADD; GSYM COMPLEX_POW_POW] THEN
  REWRITE_TAC[COMPLEX_POW_II_2] THEN CONV_TAC COMPLEX_RING);;

let CSIN_CONVERGES = prove
 (`!z. ((\n. --Cx(&1) pow n * z pow (2 * n + 1) / Cx(&(FACT(2 * n + 1))))
        sums csin(z)) (from 0)`,
  GEN_TAC THEN REWRITE_TAC[sums; FROM_0; INTER_UNIV] THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. exp(abs(Im z)) * norm z pow (2 * n + 3) / &(FACT(2 * n + 2))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[TAYLOR_CSIN] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LIM_NULL_CMUL THEN
  REWRITE_TAC[ARITH_RULE `2 * n + 3 = SUC(2 * n + 2)`; real_div] THEN
  REWRITE_TAC[LIFT_CMUL; real_pow] THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC LIM_NULL_CMUL THEN
  MP_TAC(MATCH_MP SERIES_TERMS_TOZERO (SPEC `z:complex` CEXP_CONVERGES)) THEN
  GEN_REWRITE_TAC LAND_CONV [LIM_NULL_NORM] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_POW; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_NUM; GSYM LIFT_CMUL; GSYM real_div] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let TAYLOR_CCOS_RAW = prove
 (`!n z. norm(ccos z -
              vsum(0..n) (\k. if EVEN k
                              then (ii * z) pow k / Cx(&(FACT k))
                              else Cx(&0)))
         <= exp(abs(Im z)) * (norm z) pow (n + 1) / &(FACT n)`,
  MP_TAC TAYLOR_CEXP THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN X_GEN_TAC `z:complex` THEN REWRITE_TAC[ccos] THEN
  REWRITE_TAC[COMPLEX_FIELD
    `a / Cx(&2) - b = (a - Cx(&2) * b) / Cx(&2)`] THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(SPEC `ii * z` th) THEN MP_TAC(SPEC `--ii * z` th)) THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; RE_NEG; REAL_ABS_NEG; RE_MUL_II] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_NEG;
              COMPLEX_NORM_II; REAL_ABS_NUM; REAL_MUL_RID; REAL_MUL_LID;
              REAL_ARITH `x / &2 <= y <=> x <= &2 * y`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `sp + sn = s2
    ==> norm(en - sn) <= d
        ==> norm(ep - sp) <= d ==> norm((ep + en) - s2) <= &2 * d`) THEN
  SIMP_TAC[GSYM VSUM_ADD; GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_POW_NEG; GSYM NOT_EVEN] THEN ASM_CASES_TAC `EVEN k` THEN
  ASM_REWRITE_TAC[COMPLEX_ADD_RINV; COMPLEX_MUL_RZERO] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let TAYLOR_CCOS = prove
 (`!n z. norm(ccos z -
              vsum(0..n) (\k. --Cx(&1) pow k *
                              z pow (2 * k) / Cx(&(FACT(2 * k)))))
         <= exp(abs(Im z)) * norm(z) pow (2 * n + 2) / &(FACT(2 * n + 1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2 * n + 1`; `z:complex`] TAYLOR_CCOS_RAW) THEN
  SIMP_TAC[VSUM_PAIR_0; EVEN_ADD; EVEN_MULT; ARITH_EVEN;
           LE_0; EVEN; COMPLEX_ADD_LID; COMPLEX_ADD_RID] THEN
  SIMP_TAC[ARITH_RULE `(2 * n + 1) + 1 = 2 * n + 2`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `s = t ==> norm(x - s) <= e ==> norm(x - t) <= e`) THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_POW_MUL; complex_div; COMPLEX_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_POW_POW; COMPLEX_POW_II_2]);;

let CCOS_CONVERGES = prove
 (`!z. ((\n. --Cx(&1) pow n * z pow (2 * n) / Cx(&(FACT(2 * n))))
        sums ccos(z)) (from 0)`,
  GEN_TAC THEN REWRITE_TAC[sums; FROM_0; INTER_UNIV] THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. exp(abs(Im z)) * norm z pow (2 * n + 2) / &(FACT(2 * n + 1))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[TAYLOR_CCOS] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LIM_NULL_CMUL THEN
  REWRITE_TAC[ARITH_RULE `2 * n + 2 = SUC(2 * n + 1)`; real_div] THEN
  REWRITE_TAC[LIFT_CMUL; real_pow] THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC LIM_NULL_CMUL THEN
  MP_TAC(MATCH_MP SERIES_TERMS_TOZERO (SPEC `z:complex` CEXP_CONVERGES)) THEN
  GEN_REWRITE_TAC LAND_CONV [LIM_NULL_NORM] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_POW; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_NUM; GSYM LIFT_CMUL; GSYM real_div] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The argument of a complex number, where 0 <= arg(z) < 2 pi                *)
(* ------------------------------------------------------------------------- *)

let Arg_DEF = new_definition
 `Arg z = if z = Cx(&0) then &0
          else @t. &0 <= t /\ t < &2 * pi /\
                   z = Cx(norm(z)) * cexp(ii * Cx t)`;;

let ARG_0 = prove
 (`Arg(Cx(&0)) = &0`,
  REWRITE_TAC[Arg_DEF]);;

let ARG = prove
 (`!z. &0 <= Arg(z) /\ Arg(z) < &2 * pi /\
       z = Cx(norm z) * cexp(ii * Cx(Arg z))`,
  GEN_TAC THEN REWRITE_TAC[Arg_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_NORM_0; COMPLEX_MUL_LZERO] THEN
  SIMP_TAC[REAL_LE_REFL; REAL_LT_MUL; PI_POS; REAL_ARITH `&0 < &2`] THEN
  CONV_TAC SELECT_CONV THEN
  MP_TAC(SPECL [`Re(z) / norm z`; `Im(z) / norm z`]
        SINCOS_TOTAL_2PI) THEN
  ASM_SIMP_TAC[COMPLEX_SQNORM; COMPLEX_NORM_ZERO; REAL_FIELD
    `~(z = &0) /\ x pow 2 + y pow 2 = z pow 2
      ==> (x / z) pow 2 + (y / z) pow 2 = &1`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[COMPLEX_NORM_ZERO; REAL_FIELD
   `~(z = &0) ==> (x / z = y <=> x = z * y)`] THEN
  REWRITE_TAC[COMPLEX_EQ; RE_MUL_CX; IM_MUL_CX; CEXP_EULER; RE_ADD; IM_ADD;
        RE_MUL_II; IM_MUL_II; GSYM CX_SIN; GSYM CX_COS; RE_CX; IM_CX] THEN
  REAL_ARITH_TAC);;

let COMPLEX_NORM_EQ_1_CEXP = prove
 (`!z. norm z = &1 <=> (?t. z = cexp(ii * Cx t))`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [NORM_CEXP; RE_MUL_II; IM_CX; REAL_NEG_0; REAL_EXP_0] THEN
  MP_TAC (SPEC `z:complex` ARG) THEN ASM_REWRITE_TAC [COMPLEX_MUL_LID] THEN
  MESON_TAC[]);;

let ARG_UNIQUE = prove
 (`!a r z. &0 < r /\ Cx r * cexp(ii * Cx a) = z /\ &0 <= a /\ a < &2 * pi
           ==> Arg z = a`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM CX_INJ] THEN
  MATCH_MP_TAC(COMPLEX_RING `ii * x = ii * y ==> x = y`) THEN
  MATCH_MP_TAC COMPLEX_EQ_CEXP THEN CONJ_TAC THENL
   [REWRITE_TAC[IM_MUL_II; RE_CX] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < p /\ &0 <= y /\ y < p
                             ==> abs(x - y) < p`) THEN
    ASM_SIMP_TAC[ARG];
    MATCH_MP_TAC(COMPLEX_RING
     `!a b. Cx a = Cx b /\ ~(Cx b = Cx(&0)) /\
            Cx a * w = Cx b * z ==> w = z`) THEN
    MAP_EVERY EXISTS_TAC [`norm(z:complex)`; `r:real`] THEN
    ASM_REWRITE_TAC[GSYM ARG] THEN ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ] THEN
    EXPAND_TAC "z" THEN
    REWRITE_TAC[NORM_CEXP_II; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_REAL_ARITH_TAC]);;

let ARG_MUL_CX = prove
 (`!r z. &0 < r ==> Arg(Cx r * z) = Arg(z)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `z = Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_MUL_RZERO] THEN
  MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC `r * norm(z:complex)` THEN
  ASM_REWRITE_TAC[CX_MUL; GSYM COMPLEX_MUL_ASSOC; GSYM ARG] THEN
  ASM_SIMP_TAC[REAL_LT_MUL; COMPLEX_NORM_NZ]);;

let ARG_DIV_CX = prove
 (`!r z. &0 < r ==> Arg(z / Cx r) = Arg(z)`,
  REWRITE_TAC[ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] complex_div] THEN
  SIMP_TAC[GSYM CX_INV; ARG_MUL_CX; REAL_LT_INV_EQ]);;

let ARG_LT_NZ = prove
 (`!z. &0 < Arg z <=> ~(Arg z = &0)`,
  MP_TAC ARG THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let ARG_LE_PI = prove
 (`!z. Arg z <= pi <=> &0 <= Im z`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
   [ASM_REWRITE_TAC[Arg_DEF; IM_CX; REAL_LE_REFL; PI_POS_LE]; ALL_TAC] THEN
  GEN_REWRITE_TAC (funpow 3 RAND_CONV) [ARG] THEN
  ASM_SIMP_TAC[IM_MUL_CX; CEXP_EULER; REAL_LE_MUL_EQ; COMPLEX_NORM_NZ] THEN
  REWRITE_TAC[IM_ADD; GSYM CX_SIN; GSYM CX_COS; IM_CX; IM_MUL_II; RE_CX] THEN
  REWRITE_TAC[REAL_ADD_LID] THEN EQ_TAC THEN SIMP_TAC[ARG; SIN_POS_PI_LE] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sin(&2 * pi - Arg z)` MP_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI THEN MP_TAC(SPEC `z:complex` ARG) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SIN_SUB; SIN_NPI; COS_NPI] THEN REAL_ARITH_TAC]);;

let ARG_LT_PI = prove
 (`!z. &0 < Arg z /\ Arg z < pi <=> &0 < Im z`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
   [ASM_REWRITE_TAC[Arg_DEF; IM_CX; REAL_LT_REFL; PI_POS_LE]; ALL_TAC] THEN
  GEN_REWRITE_TAC (funpow 3 RAND_CONV) [ARG] THEN
  ASM_SIMP_TAC[IM_MUL_CX; CEXP_EULER; REAL_LT_MUL_EQ; COMPLEX_NORM_NZ] THEN
  REWRITE_TAC[IM_ADD; GSYM CX_SIN; GSYM CX_COS; IM_CX; IM_MUL_II; RE_CX] THEN
  REWRITE_TAC[REAL_ADD_LID] THEN EQ_TAC THEN SIMP_TAC[SIN_POS_PI] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  ASM_CASES_TAC `Arg z = &0` THEN
  ASM_REWRITE_TAC[SIN_0; REAL_LT_REFL] THEN
  ASM_SIMP_TAC[ARG; REAL_ARITH `~(x = &0) ==> (&0 < x <=> &0 <= x)`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= sin(&2 * pi - Arg z)` MP_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI_LE THEN MP_TAC(SPEC `z:complex` ARG) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SIN_SUB; SIN_NPI; COS_NPI] THEN REAL_ARITH_TAC]);;

let ARG_EQ_0 = prove
 (`!z. Arg z = &0 <=> real z /\ &0 <= Re z`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
   [ASM_REWRITE_TAC[REAL_CX; RE_CX; Arg_DEF; REAL_LE_REFL]; ALL_TAC] THEN
  CONV_TAC(RAND_CONV(SUBS_CONV[last(CONJUNCTS(SPEC `z:complex` ARG))])) THEN
  ASM_SIMP_TAC[RE_MUL_CX; REAL_MUL_CX; REAL_LE_MUL_EQ; COMPLEX_NORM_NZ] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_ZERO; CEXP_EULER] THEN
  REWRITE_TAC[real; RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II;
              GSYM CX_SIN; GSYM CX_COS; RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_ADD_RID; REAL_ADD_LID; REAL_NEG_0] THEN
  EQ_TAC THEN SIMP_TAC[SIN_0; COS_0; REAL_POS] THEN
  ASM_CASES_TAC `Arg z = pi` THENL
   [ASM_REWRITE_TAC[COS_PI] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `z:complex` ARG) THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP
   (REAL_ARITH `&0 <= x /\ x < &2 * pi
                ==> --pi < x /\ x < pi \/ --pi < x - pi /\ x - pi < pi`)) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIN_EQ_0_PI] THEN
  UNDISCH_TAC `~(Arg z = pi)` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_ARITH `x = pi <=> x - pi = &0`] THEN
  MATCH_MP_TAC SIN_EQ_0_PI THEN ASM_REWRITE_TAC[SIN_SUB; SIN_PI] THEN
  REAL_ARITH_TAC);;

let ARG_NUM = prove
 (`!n. Arg(Cx(&n)) = &0`,
  REWRITE_TAC[ARG_EQ_0; REAL_CX; RE_CX; REAL_POS]);;

let ARG_EQ_PI = prove
 (`!z. Arg z = pi <=> real z /\ Re z < &0`,
  SIMP_TAC[ARG; PI_POS; REAL_ARITH
    `&0 < pi /\ &0 <= z
     ==> (z = pi <=> z <= pi /\ ~(z = &0) /\ ~(&0 < z /\ z < pi))`] THEN
  REWRITE_TAC[ARG_EQ_0; ARG; ARG_LT_PI; ARG_LE_PI; real] THEN
  REAL_ARITH_TAC);;

let ARG_EQ_0_PI = prove
 (`!z. Arg z = &0 \/ Arg z = pi <=> real z`,
  REWRITE_TAC[ARG_EQ_0; ARG_EQ_PI; real] THEN REAL_ARITH_TAC);;

let ARG_INV = prove
 (`!z. ~(real z /\ &0 <= Re z) ==> Arg(inv z) = &2 * pi - Arg z`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[REAL_CX; RE_CX; REAL_LE_REFL] THEN
  REWRITE_TAC[real] THEN STRIP_TAC THEN MATCH_MP_TAC ARG_UNIQUE THEN
  EXISTS_TAC `inv(norm(z:complex))` THEN
  ASM_SIMP_TAC[COMPLEX_NORM_NZ; REAL_LT_INV_EQ] THEN
  REWRITE_TAC[CX_SUB; CX_MUL; COMPLEX_SUB_LDISTRIB; CEXP_SUB] THEN
  SUBST1_TAC(SPEC `Cx(&2) * Cx pi` CEXP_EULER) THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_SIN; GSYM CX_COS] THEN
  REWRITE_TAC[SIN_NPI; COS_NPI; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_LID; CX_INV; GSYM COMPLEX_INV_MUL] THEN
  REWRITE_TAC[GSYM ARG] THEN
  MP_TAC(SPEC `z:complex` ARG_EQ_0) THEN ASM_REWRITE_TAC[real] THEN
  MP_TAC(SPEC `z:complex` ARG) THEN REAL_ARITH_TAC);;

let ARG_EQ = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> (Arg w = Arg z <=> ?x. &0 < x /\ w = Cx(x) * z)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; STRIP_TAC THEN ASM_SIMP_TAC[ARG_MUL_CX]] THEN
  DISCH_TAC THEN
  MAP_EVERY (MP_TAC o CONJUNCT2 o CONJUNCT2 o C SPEC ARG)
   [`z:complex`; `w:complex`] THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(fun th -> CONV_TAC(SUBS_CONV(CONJUNCTS th))) THEN
  EXISTS_TAC `norm(w:complex) / norm(z:complex)` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; COMPLEX_NORM_NZ; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[COMPLEX_DIV_RMUL; COMPLEX_NORM_ZERO; CX_INJ]);;

let ARG_INV_EQ_0 = prove
 (`!z. Arg(inv z) = &0 <=> Arg z = &0`,
  GEN_TAC THEN REWRITE_TAC[ARG_EQ_0; REAL_INV_EQ] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  REWRITE_TAC[real] THEN DISCH_TAC THEN ASM_REWRITE_TAC[complex_inv; RE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_ADD_RID] THEN
  ASM_CASES_TAC `Re z = &0` THEN ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(x = &0) ==> x * inv(x pow 2) = inv x`] THEN
  REWRITE_TAC[REAL_LE_INV_EQ]);;

let ARG_LE_DIV_SUM = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0)) /\ Arg(w) <= Arg(z)
         ==> Arg(z) = Arg(w) + Arg(z / w)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a:real = b + c <=> c = a - b`] THEN
  MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC `norm(z / w)`THEN
  ASM_SIMP_TAC[ARG; REAL_ARITH
   `&0 <= a /\ a < &2 * pi /\ &0 <= b /\ b <= a ==> a - b < &2 * pi`] THEN
  ASM_REWRITE_TAC[REAL_SUB_LE] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_DIV; CX_DIV] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; COMPLEX_NORM_NZ] THEN
  REWRITE_TAC[COMPLEX_SUB_LDISTRIB; CEXP_SUB; CX_SUB] THEN
  REWRITE_TAC[complex_div] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `(a * b) * (c * d):complex = (a * c) * (b * d)`] THEN
  REWRITE_TAC[GSYM COMPLEX_INV_MUL] THEN ASM_SIMP_TAC[GSYM ARG]);;

let ARG_LE_DIV_SUM_EQ = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> (Arg(w) <= Arg(z) <=> Arg(z) = Arg(w) + Arg(z / w))`,
  MESON_TAC[ARG_LE_DIV_SUM; REAL_LE_ADDR; ARG]);;

let REAL_SUB_ARG = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> Arg w - Arg z = if Arg(z) <= Arg(w) then Arg(w / z)
                             else Arg(w / z) - &2 * pi`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`z:complex`; `w:complex`] ARG_LE_DIV_SUM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`w:complex`; `z:complex`] ARG_LE_DIV_SUM) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a - (a + b):real = --b`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM COMPLEX_INV_DIV] THEN
    MATCH_MP_TAC(REAL_ARITH `x = &2 * pi - y ==> --x = y - &2 * pi`) THEN
    MATCH_MP_TAC ARG_INV THEN REWRITE_TAC[GSYM ARG_EQ_0] THEN
    ONCE_REWRITE_TAC[GSYM COMPLEX_INV_DIV] THEN
    REWRITE_TAC[ARG_INV_EQ_0] THEN
    MP_TAC(ISPECL [`w:complex`; `z:complex`] ARG_LE_DIV_SUM) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let REAL_ADD_ARG = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> Arg(w) + Arg(z) =
             if Arg w + Arg z < &2 * pi
             then Arg(w * z)
             else Arg(w * z) + &2 * pi`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`w * z:complex`; `z:complex`] REAL_SUB_ARG) THEN
  MP_TAC(SPECL [`z:complex`; `w * z:complex`] ARG_LE_DIV_SUM_EQ) THEN
  ASM_SIMP_TAC[COMPLEX_ENTIRE; COMPLEX_FIELD
   `~(z = Cx(&0)) ==> (w * z) / z = w`] THEN
  ASM_CASES_TAC `Arg (w * z) = Arg z + Arg w` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[ARG; REAL_ADD_SYM];
    SIMP_TAC[REAL_ARITH `wz - z = w - &2 * pi <=> w + z = wz + &2 * pi`] THEN
    REWRITE_TAC[REAL_ARITH `w + p < p <=> ~(&0 <= w)`; ARG]]);;

let ARG_MUL = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> Arg(w * z) = if Arg w + Arg z < &2 * pi
                          then Arg w + Arg z
                          else (Arg w + Arg z) - &2 * pi`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_ADD_ARG) THEN
  REAL_ARITH_TAC);;

let ARG_CNJ = prove
 (`!z. Arg(cnj z) = if real z /\ &0 <= Re z then Arg z else &2 * pi - Arg z`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[CNJ_CX; ARG_0; REAL_CX; RE_CX; REAL_LE_REFL] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_IMP_CNJ] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `Arg(inv z)` THEN CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_INV_CNJ] THEN
    ASM_SIMP_TAC[GSYM CX_POW; ARG_DIV_CX; REAL_POW_LT; COMPLEX_NORM_NZ];
    ASM_SIMP_TAC[ARG_INV]]);;

let ARG_REAL = prove
 (`!z. real z ==> Arg z = if &0 <= Re z then &0 else pi`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ARG_EQ_PI; ARG_EQ_0] THEN ASM_REAL_ARITH_TAC);;

let ARG_CEXP = prove
 (`!z. &0 <= Im z /\ Im z < &2 * pi ==> Arg(cexp(z)) = Im z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARG_UNIQUE THEN
  EXISTS_TAC `exp(Re z)` THEN
  ASM_REWRITE_TAC[CX_EXP; GSYM CEXP_ADD; REAL_EXP_POS_LT] THEN
  REWRITE_TAC[GSYM COMPLEX_EXPAND]);;

(* ------------------------------------------------------------------------- *)
(* Properties of 2-D rotations, and their interpretation using cexp.         *)
(* ------------------------------------------------------------------------- *)

let rotate2d = new_definition
 `(rotate2d:real->real^2->real^2) t x =
        vector[x$1 * cos(t) - x$2 * sin(t);
               x$1 * sin(t) + x$2 * cos(t)]`;;

let LINEAR_ROTATE2D = prove
 (`!t. linear(rotate2d t)`,
  SIMP_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; rotate2d] THEN
  REAL_ARITH_TAC);;

let ROTATE2D_ADD_VECTORS = prove
 (`!t w z. rotate2d t (w + z) = rotate2d t w + rotate2d t z`,
  SIMP_TAC[LINEAR_ADD; LINEAR_ROTATE2D]);;

let ROTATE2D_SUB = prove
 (`!t w z. rotate2d t (w - z) = rotate2d t w - rotate2d t z`,
  SIMP_TAC[LINEAR_SUB; LINEAR_ROTATE2D]);;

let NORM_ROTATE2D = prove
 (`!t z. norm(rotate2d t z) = norm z`,
  REWRITE_TAC[NORM_EQ; rotate2d; DIMINDEX_2; DOT_2; VECTOR_2] THEN
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `t:real` SIN_CIRCLE) THEN
  CONV_TAC REAL_RING);;

let ROTATE2D_0 = prove
 (`!t. rotate2d t (Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[GSYM COMPLEX_NORM_ZERO; NORM_ROTATE2D; COMPLEX_NORM_0]);;

let ROTATE2D_EQ_0 = prove
 (`!t z. rotate2d t z = Cx(&0) <=> z = Cx(&0)`,
  REWRITE_TAC[GSYM COMPLEX_NORM_ZERO; NORM_ROTATE2D]);;

let ROTATE2D_ZERO = prove
 (`!z. rotate2d (&0) z = z`,
  REWRITE_TAC[rotate2d; SIN_0; COS_0] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let ORTHOGONAL_TRANSFORMATION_ROTATE2D = prove
 (`!t. orthogonal_transformation(rotate2d t)`,
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; LINEAR_ROTATE2D; NORM_ROTATE2D]);;

let ROTATE2D_POLAR = prove
 (`!r t s. rotate2d t (vector[r * cos(s); r * sin(s)]) =
                        vector[r * cos(t + s); r * sin(t + s)]`,
  SIMP_TAC[rotate2d; DIMINDEX_2; VECTOR_2; CART_EQ; FORALL_2] THEN
  REWRITE_TAC[SIN_ADD; COS_ADD] THEN REAL_ARITH_TAC);;

let MATRIX_ROTATE2D = prove
 (`!t. matrix(rotate2d t) = vector[vector[cos t;--(sin t)];
                                   vector[sin t; cos t]]`,
  SIMP_TAC[MATRIX_EQ; MATRIX_WORKS; LINEAR_ROTATE2D] THEN
  SIMP_TAC[matrix_vector_mul; rotate2d; CART_EQ; DIMINDEX_2; FORALL_2;
           LAMBDA_BETA; VECTOR_2; ARITH; SUM_2] THEN
  REAL_ARITH_TAC);;

let DET_MATRIX_ROTATE2D = prove
 (`!t. det(matrix(rotate2d t)) = &1`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_ROTATE2D; DET_2; VECTOR_2] THEN
  MP_TAC(SPEC `t:real` SIN_CIRCLE) THEN REAL_ARITH_TAC);;

let ROTATION_ROTATE2D = prove
 (`!f. orthogonal_transformation f /\ det(matrix f) = &1
       ==> ?t. &0 <= t /\ t < &2 * pi /\ f = rotate2d t`,
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX] THEN
  REWRITE_TAC[matrix_mul; orthogonal_matrix; transp] THEN
  SIMP_TAC[DIMINDEX_2; SUM_2; FORALL_2; LAMBDA_BETA; ARITH;
           CART_EQ; mat; DET_2] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(matrix f)$1$1 pow 2 + (matrix f)$2$1 pow 2 = &1 /\
                (matrix f)$1$2 = --((matrix f)$2$1) /\
                (matrix f:real^2^2)$2$2 = (matrix f)$1$1`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN CONV_TAC REAL_RING;
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SINCOS_TOTAL_2PI) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LINEAR_EQ_MATRIX THEN
    ASM_REWRITE_TAC[LINEAR_ROTATE2D; MATRIX_ROTATE2D] THEN
    ASM_SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]]);;

let ROTATE2D_ADD = prove
 (`!s t x. rotate2d (s + t) x = rotate2d s (rotate2d t x)`,
  SIMP_TAC[CART_EQ; rotate2d; LAMBDA_BETA; DIMINDEX_2; ARITH;
           FORALL_2; VECTOR_2] THEN
  REWRITE_TAC[SIN_ADD; COS_ADD] THEN REAL_ARITH_TAC);;

let ROTATE2D_COMPLEX = prove
 (`!t z. rotate2d t z = cexp(ii * Cx t) * z`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [complex_mul] THEN
  REWRITE_TAC[CEXP_EULER; rotate2d; GSYM CX_SIN; GSYM CX_COS;
              RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II; IM_CX; RE_CX] THEN
  REWRITE_TAC[CART_EQ; FORALL_2; VECTOR_2; DIMINDEX_2] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
  REAL_ARITH_TAC);;

let ROTATE2D_PI2 = prove
 (`!z. rotate2d (pi / &2) z = ii * z`,
  REWRITE_TAC[ROTATE2D_COMPLEX; CEXP_EULER; SIN_PI2; COS_PI2; GSYM CX_SIN;
              GSYM CX_COS] THEN
  CONV_TAC COMPLEX_RING);;

let ROTATE2D_PI = prove
 (`!z. rotate2d pi z = --z`,
  REWRITE_TAC[ROTATE2D_COMPLEX; CEXP_EULER; SIN_PI; COS_PI; GSYM CX_SIN;
              GSYM CX_COS] THEN
  CONV_TAC COMPLEX_RING);;

let ROTATE2D_NPI = prove
 (`!n z. rotate2d (&n * pi) z = --Cx(&1) pow n * z`,
  REWRITE_TAC[ROTATE2D_COMPLEX; CEXP_EULER; SIN_NPI; COS_NPI; GSYM CX_SIN;
              GSYM CX_COS; CX_NEG; CX_POW] THEN
  CONV_TAC COMPLEX_RING);;

let ROTATE2D_2PI = prove
 (`!z. rotate2d (&2 * pi) z = z`,
  REWRITE_TAC[ROTATE2D_NPI] THEN CONV_TAC COMPLEX_RING);;

let ARG_ROTATE2D = prove
 (`!t z. ~(z = Cx(&0)) /\ &0 <= t + Arg z /\ t + Arg z < &2 * pi
         ==> Arg(rotate2d t z) = t + Arg z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARG_UNIQUE THEN
  EXISTS_TAC `norm(z:complex)` THEN
  ASM_SIMP_TAC[ARG; ROTATE2D_COMPLEX; REAL_LE_ADD; COMPLEX_NORM_NZ] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ARG] THEN
  REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let ARG_ROTATE2D_UNIQUE = prove
 (`!t a z. ~(z = Cx(&0)) /\ Arg(rotate2d t z) = a
           ==> ?n. integer n /\ t = &2 * n * pi + (a - Arg z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(last(CONJUNCTS(ISPEC `rotate2d t z` ARG))) THEN
  ASM_REWRITE_TAC[NORM_ROTATE2D] THEN
  REWRITE_TAC[ROTATE2D_COMPLEX] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [ARG] THEN
  ASM_REWRITE_TAC[COMPLEX_RING `a * z * b = z * c <=> z = Cx(&0) \/ a * b = c`;
                  CX_INJ; COMPLEX_NORM_ZERO; GSYM CEXP_ADD; CEXP_EQ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_SUB; CX_INJ; COMPLEX_RING
   `ii * t + ii * z = ii * a + n * ii <=> t = n + (a - z)`]);;

let ARG_ROTATE2D_UNIQUE_2PI = prove
 (`!s t z. ~(z = Cx(&0)) /\
           &0 <= s /\ s < &2 * pi /\ &0 <= t /\ t < &2 * pi /\
           Arg(rotate2d s z) = Arg(rotate2d t z)
           ==> s = t`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `a = Arg(rotate2d t z)` THEN
  MP_TAC(ISPECL [`s:real`; `a:real`; `z:complex`] ARG_ROTATE2D_UNIQUE) THEN
  MP_TAC(ISPECL [`t:real`; `a:real`; `z:complex`] ARG_ROTATE2D_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SIN_COS_INJ THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[SIN_COS_EQ; REAL_RING
     `x + az:real = (y + az) + z <=> x - y = z`] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    ASM_MESON_TAC[INTEGER_CLOSED];
    ASM_REAL_ARITH_TAC]);;

let COMPLEX_DIV_ROTATION = prove
 (`!f w z. orthogonal_transformation f /\ det(matrix f) = &1
           ==> f w / f z = w / z`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ROTATION_ROTATE2D) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[ROTATE2D_COMPLEX] THEN
  SIMP_TAC[complex_div; COMPLEX_INV_MUL; CEXP_NZ; COMPLEX_FIELD
   `~(a = Cx(&0)) ==> (a * w) * (inv a * z) = w * z`]);;

let th = prove
 (`!f w z. linear f /\ (!x. norm(f x) = norm x) /\
           (2 <= dimindex(:2) ==> det(matrix f) = &1)
           ==> f w / f z = w / z`,
  REWRITE_TAC[CONJ_ASSOC; GSYM ORTHOGONAL_TRANSFORMATION;
              DIMINDEX_2; LE_REFL; COMPLEX_DIV_ROTATION]) in
add_linear_invariants [th];;

let th = prove
 (`!f t z. linear f /\ (!x. norm(f x) = norm x) /\
           (2 <= dimindex(:2) ==> det(matrix f) = &1)
           ==> rotate2d t (f z) = f(rotate2d t z)`,
  REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `f:complex->complex` ROTATION_ROTATE2D) THEN
  ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GSYM ROTATE2D_ADD] THEN REWRITE_TAC[REAL_ADD_SYM]) in
add_linear_invariants [th];;

let ROTATION_ROTATE2D_EXISTS_GEN = prove
 (`!x y. ?t. &0 <= t /\ t < &2 * pi /\ norm(y) % rotate2d t x = norm(x) % y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`norm(y:real^2) % x:real^2`; `norm(x:real^2) % y:real^2`]
               ROTATION_EXISTS) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; NORM_MUL; ARITH; REAL_ABS_NORM;
                  EQT_INTRO(SPEC_ALL REAL_MUL_SYM); CONJ_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (CONJUNCTS_THEN ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ROTATION_ROTATE2D) THEN
  MATCH_MP_TAC MONO_EXISTS THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LINEAR_CMUL; LINEAR_ROTATE2D]);;

let ROTATION_ROTATE2D_EXISTS = prove
 (`!x y. norm x = norm y ==> ?t. &0 <= t /\ t < &2 * pi /\ rotate2d t x = y`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `norm(y:complex) = &0` THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `&0` THEN
    SIMP_TAC[REAL_LT_MUL; PI_POS; REAL_OF_NUM_LT; ARITH; REAL_LE_REFL] THEN
    ASM_MESON_TAC[COMPLEX_NORM_ZERO; ROTATE2D_0];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`x:complex`; `y:complex`] ROTATION_ROTATE2D_EXISTS_GEN) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL]]);;

let ROTATION_ROTATE2D_EXISTS_ORTHOGONAL = prove
 (`!e1 e2. norm(e1) = &1 /\ norm(e2) = &1 /\ orthogonal e1 e2
           ==> e1 = rotate2d (pi / &2) e2 \/ e2 = rotate2d (pi / &2) e1`,
  REWRITE_TAC[NORM_EQ_1; orthogonal] THEN
  SIMP_TAC[DOT_2; CART_EQ; FORALL_2; DIMINDEX_2; rotate2d; VECTOR_2] THEN
  REWRITE_TAC[COS_PI2; SIN_PI2; REAL_MUL_RZERO; REAL_ADD_RID;
              REAL_SUB_LZERO; REAL_SUB_RZERO; REAL_MUL_RID] THEN
  CONV_TAC REAL_RING);;

let ROTATION_ROTATE2D_EXISTS_ORTHOGONAL_ORIENTED = prove
 (`!e1 e2. norm(e1) = &1 /\ norm(e2) = &1 /\ orthogonal e1 e2 /\
           &0 < e1$1 * e2$2 - e1$2 * e2$1
           ==> e2 = rotate2d (pi / &2) e1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
    ROTATION_ROTATE2D_EXISTS_ORTHOGONAL) THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LE]) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  SIMP_TAC[DOT_2; CART_EQ; FORALL_2; DIMINDEX_2; rotate2d; VECTOR_2] THEN
  REWRITE_TAC[COS_PI2; SIN_PI2; REAL_MUL_RZERO; REAL_ADD_RID;
              REAL_SUB_LZERO; REAL_SUB_RZERO; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `--x * x - y * y <= &0 <=> &0 <= x * x + y * y`] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_SQUARE]);;

let ROTATE2D_EQ = prove
 (`!t x y. rotate2d t x = rotate2d t y <=> x = y`,
  MESON_TAC[ORTHOGONAL_TRANSFORMATION_INJECTIVE;
            ORTHOGONAL_TRANSFORMATION_ROTATE2D]);;

let ROTATE2D_SUB_ARG = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> rotate2d(Arg w - Arg z) = rotate2d(Arg(w / z))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_SUB_ARG] THEN
  COND_CASES_TAC THEN REWRITE_TAC[real_sub; ROTATE2D_ADD; FUN_EQ_THM] THEN
  GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ROTATE2D_COMPLEX] THEN
  REWRITE_TAC[EULER; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX; COS_NEG; SIN_NEG] THEN
  REWRITE_TAC[SIN_NPI; COS_NPI; REAL_EXP_NEG; REAL_EXP_0; CX_NEG] THEN
  REWRITE_TAC[COMPLEX_NEG_0; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[COMPLEX_MUL_LID]);;

let ROTATION_MATRIX_ROTATE2D = prove
 (`!t. rotation_matrix(matrix(rotate2d t))`,
  SIMP_TAC[ROTATION_MATRIX_2; MATRIX_ROTATE2D; VECTOR_2] THEN
  MESON_TAC[SIN_CIRCLE; REAL_ADD_SYM]);;

let ROTATION_MATRIX_ROTATE2D_EQ = prove
 (`!A:real^2^2. rotation_matrix A <=> ?t. A = matrix(rotate2d t)`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; ROTATION_MATRIX_ROTATE2D] THEN
  REWRITE_TAC[ROTATION_MATRIX_2; MATRIX_ROTATE2D] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SINCOS_TOTAL_2PI) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  ASM_REAL_ARITH_TAC);;
