open Hol_core
open Floor
open Card
open Products
open Binomial
open Vectors
open Determinants
open Topology
open Convex
open Paths
open Derivatives
open Polytope
open Integration
open Measure
open Complexes
open Canal
open Transcendentals
include Realanalysis1

(* ------------------------------------------------------------------------- *)
(* Same again for being differentiable on a set.                             *)
(* ------------------------------------------------------------------------- *)

let REAL_DIFFERENTIABLE_ON_CONST = prove
 (`!c s. (\z. c) real_differentiable_on s`,
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
              REAL_DIFFERENTIABLE_CONST]);;

let REAL_DIFFERENTIABLE_ON_ID = prove
 (`!s. (\z. z) real_differentiable_on s`,
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE; REAL_DIFFERENTIABLE_ID]);;

let REAL_DIFFERENTIABLE_ON_COMPOSE = prove
 (`!f g s. f real_differentiable_on s /\ g real_differentiable_on (IMAGE f s)
           ==> (g o f) real_differentiable_on s`,
  SIMP_TAC[real_differentiable_on; GSYM real_differentiable;
           FORALL_IN_IMAGE] THEN
  MESON_TAC[REAL_DIFFERENTIABLE_COMPOSE_WITHIN]);;

let REAL_DIFFERENTIABLE_ON_NEG = prove
 (`!f s. f real_differentiable_on s ==> (\z. --(f z)) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE; REAL_DIFFERENTIABLE_NEG]);;

let REAL_DIFFERENTIABLE_ON_ADD = prove
 (`!f g s.
        f real_differentiable_on s /\ g real_differentiable_on s
        ==> (\z. f z + g z) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE; REAL_DIFFERENTIABLE_ADD]);;

let REAL_DIFFERENTIABLE_ON_SUB = prove
 (`!f g s.
        f real_differentiable_on s /\ g real_differentiable_on s
        ==> (\z. f z - g z) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE; REAL_DIFFERENTIABLE_SUB]);;

let REAL_DIFFERENTIABLE_ON_MUL = prove
 (`!f g s.
        f real_differentiable_on s /\ g real_differentiable_on s
        ==> (\z. f z * g z) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
           REAL_DIFFERENTIABLE_MUL_WITHIN]);;

let REAL_DIFFERENTIABLE_ON_INV = prove
 (`!f s. f real_differentiable_on s /\ (!z. z IN s ==> ~(f z = &0))
         ==> (\z. inv(f z)) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
           REAL_DIFFERENTIABLE_INV_WITHIN]);;

let REAL_DIFFERENTIABLE_ON_DIV = prove
 (`!f g s.
        f real_differentiable_on s /\ g real_differentiable_on s /\
        (!z. z IN s ==> ~(g z = &0))
        ==> (\z. f z / g z) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
           REAL_DIFFERENTIABLE_DIV_WITHIN]);;

let REAL_DIFFERENTIABLE_ON_POW = prove
 (`!f s n. f real_differentiable_on s
           ==> (\z. (f z) pow n) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
           REAL_DIFFERENTIABLE_POW_WITHIN]);;

let REAL_DIFFERENTIABLE_ON_SUM = prove
 (`!f s k. FINITE k /\ (!a. a IN k ==> (f a) real_differentiable_on s)
           ==> (\x. sum k (\a. f a x)) real_differentiable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC[SUM_CLAUSES] THEN
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_CONST; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_ADD THEN
  ASM_SIMP_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Derivative (and continuity) theorems for real transcendental functions.   *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_EXP = prove
 (`!x. (exp has_real_derivative exp(x)) (atreal x)`,
  GEN_TAC THEN MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT THEN
  EXISTS_TAC `cexp` THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN;
               HAS_COMPLEX_DERIVATIVE_CEXP; CX_EXP]);;

let REAL_DIFFERENTIABLE_AT_EXP = prove
 (`!x. exp real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_EXP]);;

let REAL_DIFFERENTIABLE_WITHIN_EXP = prove
 (`!s x. exp real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_EXP]);;

let REAL_CONTINUOUS_AT_EXP = prove
 (`!x. exp real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_EXP;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_EXP = prove
 (`!s x. exp real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_EXP]);;

let REAL_CONTINUOUS_ON_EXP = prove
 (`!s. exp real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHIN_EXP]);;

let HAS_REAL_DERIVATIVE_SIN = prove
 (`!x. (sin has_real_derivative cos(x)) (atreal x)`,
  GEN_TAC THEN MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT THEN
  EXISTS_TAC `csin` THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN;
               HAS_COMPLEX_DERIVATIVE_CSIN; CX_SIN; CX_COS]);;

let REAL_DIFFERENTIABLE_AT_SIN = prove
 (`!x. sin real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_SIN]);;

let REAL_DIFFERENTIABLE_WITHIN_SIN = prove
 (`!s x. sin real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_SIN]);;

let REAL_CONTINUOUS_AT_SIN = prove
 (`!x. sin real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_SIN;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_SIN = prove
 (`!s x. sin real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_SIN]);;

let REAL_CONTINUOUS_ON_SIN = prove
 (`!s. sin real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHIN_SIN]);;

let HAS_REAL_DERIVATIVE_COS = prove
 (`!x. (cos has_real_derivative --sin(x)) (atreal x)`,
  GEN_TAC THEN MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT THEN
  EXISTS_TAC `ccos` THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN;
               HAS_COMPLEX_DERIVATIVE_CCOS; CX_SIN; CX_COS; CX_NEG]);;

let REAL_DIFFERENTIABLE_AT_COS = prove
 (`!x. cos real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_COS]);;

let REAL_DIFFERENTIABLE_WITHIN_COS = prove
 (`!s x. cos real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_COS]);;

let REAL_CONTINUOUS_AT_COS = prove
 (`!x. cos real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_COS;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_COS = prove
 (`!s x. cos real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_COS]);;

let REAL_CONTINUOUS_ON_COS = prove
 (`!s. cos real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHIN_COS]);;

let HAS_REAL_DERIVATIVE_TAN = prove
 (`!x. ~(cos x = &0)
       ==> (tan has_real_derivative inv(cos(x) pow 2)) (atreal x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT THEN
  EXISTS_TAC `ctan` THEN REWRITE_TAC[CX_INV; CX_POW; CX_COS] THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN;
               HAS_COMPLEX_DERIVATIVE_CTAN; GSYM CX_COS; CX_INJ; CX_TAN]);;

let REAL_DIFFERENTIABLE_AT_TAN = prove
 (`!x. ~(cos x = &0) ==> tan real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_TAN]);;

let REAL_DIFFERENTIABLE_WITHIN_TAN = prove
 (`!s x. ~(cos x = &0) ==> tan real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_TAN]);;

let REAL_CONTINUOUS_AT_TAN = prove
 (`!x. ~(cos x = &0) ==> tan real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_TAN;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_TAN = prove
 (`!s x. ~(cos x = &0) ==> tan real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_TAN]);;

let REAL_CONTINUOUS_ON_TAN = prove
 (`!s. (!x. x IN s ==> ~(cos x = &0)) ==> tan real_continuous_on s`,
  MESON_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
            REAL_CONTINUOUS_WITHIN_TAN]);;

let HAS_REAL_DERIVATIVE_LOG = prove
 (`!x. &0 < x ==> (log has_real_derivative inv(x)) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT_GEN THEN
  MAP_EVERY EXISTS_TAC [`clog`; `x:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[CX_INV] THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CLOG THEN ASM_REWRITE_TAC[RE_CX];
    MATCH_MP_TAC(GSYM CX_LOG) THEN ASM_REAL_ARITH_TAC]);;

let REAL_DIFFERENTIABLE_AT_LOG = prove
 (`!x. &0 < x ==> log real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_LOG]);;

let REAL_DIFFERENTIABLE_WITHIN_LOG = prove
 (`!s x. &0 < x ==> log real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_LOG]);;

let REAL_CONTINUOUS_AT_LOG = prove
 (`!x. &0 < x ==> log real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_LOG;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_LOG = prove
 (`!s x. &0 < x ==> log real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_LOG]);;

let REAL_CONTINUOUS_ON_LOG = prove
 (`!s. (!x. x IN s ==> &0 < x) ==> log real_continuous_on s`,
  MESON_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
            REAL_CONTINUOUS_WITHIN_LOG]);;

let HAS_REAL_DERIVATIVE_SQRT = prove
 (`!x. &0 < x ==> (sqrt has_real_derivative inv(&2 * sqrt x)) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT_GEN THEN
  MAP_EVERY EXISTS_TAC [`csqrt`; `x:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[CX_INV; CX_MUL; CX_SQRT; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CSQRT THEN
    ASM_SIMP_TAC[RE_CX];
    MATCH_MP_TAC(GSYM CX_SQRT) THEN ASM_REAL_ARITH_TAC]);;

let REAL_DIFFERENTIABLE_AT_SQRT = prove
 (`!x. &0 < x ==> sqrt real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_SQRT]);;

let REAL_DIFFERENTIABLE_WITHIN_SQRT = prove
 (`!s x. &0 < x ==> sqrt real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_SQRT]);;

let REAL_CONTINUOUS_AT_SQRT = prove
 (`!x. &0 < x ==> sqrt real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_SQRT;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_SQRT = prove
 (`!s x. &0 < x ==> sqrt real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_SQRT]);;

let REAL_CONTINUOUS_WITHIN_SQRT_COMPOSE = prove
 (`!f s a:real^N.
        f real_continuous (at a within s) /\
        (&0 < f a \/ !x. x IN s ==> &0 <= f x)
        ==> (\x. sqrt(f x)) real_continuous (at a within s)`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF] THEN
  REWRITE_TAC[CONTINUOUS_WITHIN_SQRT_COMPOSE]);;

let REAL_CONTINUOUS_AT_SQRT_COMPOSE = prove
 (`!f a:real^N.
        f real_continuous (at a) /\
        (&0 < f a \/ !x. &0 <= f x)
        ==> (\x. sqrt(f x)) real_continuous (at a)`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF] THEN
  REWRITE_TAC[CONTINUOUS_AT_SQRT_COMPOSE]);;

let CONTINUOUS_WITHINREAL_SQRT_COMPOSE = prove
 (`!f s a. (\x. lift(f x)) continuous (atreal a within s) /\
           (&0 < f a \/ !x. x IN s ==> &0 <= f x)
           ==> (\x. lift(sqrt(f x))) continuous (atreal a within s)`,
  REWRITE_TAC[CONTINUOUS_CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC[o_DEF] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC CONTINUOUS_WITHIN_SQRT_COMPOSE THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP]);;

let CONTINUOUS_ATREAL_SQRT_COMPOSE = prove
 (`!f a. (\x. lift(f x)) continuous (atreal a) /\ (&0 < f a \/ !x. &0 <= f x)
         ==> (\x. lift(sqrt(f x))) continuous (atreal a)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `(:real)`; `a:real`]
        CONTINUOUS_WITHINREAL_SQRT_COMPOSE) THEN
  REWRITE_TAC[WITHINREAL_UNIV; IN_UNIV]);;

let REAL_CONTINUOUS_WITHINREAL_SQRT_COMPOSE = prove
 (`!f s a. f real_continuous (atreal a within s) /\
           (&0 < f a \/ !x. x IN s ==> &0 <= f x)
           ==> (\x. sqrt(f x)) real_continuous (atreal a within s)`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF] THEN
  REWRITE_TAC[CONTINUOUS_WITHINREAL_SQRT_COMPOSE]);;

let REAL_CONTINUOUS_ATREAL_SQRT_COMPOSE = prove
 (`!f a. f real_continuous (atreal a) /\
         (&0 < f a \/ !x. &0 <= f x)
         ==> (\x. sqrt(f x)) real_continuous (atreal a)`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF] THEN
  REWRITE_TAC[CONTINUOUS_ATREAL_SQRT_COMPOSE]);;

let HAS_REAL_DERIVATIVE_ATN = prove
 (`!x. (atn has_real_derivative inv(&1 + x pow 2)) (atreal x)`,
  GEN_TAC THEN MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT THEN
  EXISTS_TAC `catn` THEN REWRITE_TAC[CX_INV; CX_ADD; CX_ATN; CX_POW] THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CATN;
               IM_CX; REAL_ABS_NUM; REAL_LT_01]);;

let REAL_DIFFERENTIABLE_AT_ATN = prove
 (`!x. atn real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_ATN]);;

let REAL_DIFFERENTIABLE_WITHIN_ATN = prove
 (`!s x. atn real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_ATN]);;

let REAL_CONTINUOUS_AT_ATN = prove
 (`!x. atn real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_ATN;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_ATN = prove
 (`!s x. atn real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_ATN]);;

let REAL_CONTINUOUS_ON_ATN = prove
 (`!s. atn real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHIN_ATN]);;

let HAS_REAL_DERIVATIVE_ASN_COS = prove
 (`!x. abs(x) < &1 ==> (asn has_real_derivative inv(cos(asn x))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT_GEN THEN
  MAP_EVERY EXISTS_TAC [`casn`; `&1 - abs x`] THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[CX_INV; CX_COS; CX_ASN; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CASN THEN ASM_REWRITE_TAC[RE_CX];
    MATCH_MP_TAC(GSYM CX_ASN) THEN ASM_REAL_ARITH_TAC]);;

let HAS_REAL_DERIVATIVE_ASN = prove
 (`!x. abs(x) < &1
       ==> (asn has_real_derivative inv(sqrt(&1 - x pow 2))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_ASN_COS) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC COS_ASN THEN ASM_REAL_ARITH_TAC);;

let REAL_DIFFERENTIABLE_AT_ASN = prove
 (`!x. abs(x) < &1 ==> asn real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_ASN]);;

let REAL_DIFFERENTIABLE_WITHIN_ASN = prove
 (`!s x. abs(x) < &1 ==> asn real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_ASN]);;

let REAL_CONTINUOUS_AT_ASN = prove
 (`!x. abs(x) < &1 ==> asn real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_ASN;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_ASN = prove
 (`!s x. abs(x) < &1 ==> asn real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_ASN]);;

let HAS_REAL_DERIVATIVE_ACS_SIN = prove
 (`!x. abs(x) < &1 ==> (acs has_real_derivative --inv(sin(acs x))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT_GEN THEN
  MAP_EVERY EXISTS_TAC [`cacs`; `&1 - abs x`] THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[CX_INV; CX_SIN; CX_ACS; CX_NEG; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CACS THEN ASM_REWRITE_TAC[RE_CX];
    MATCH_MP_TAC(GSYM CX_ACS) THEN ASM_REAL_ARITH_TAC]);;

let HAS_REAL_DERIVATIVE_ACS = prove
 (`!x. abs(x) < &1
       ==> (acs has_real_derivative --inv(sqrt(&1 - x pow 2))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_ACS_SIN) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SIN_ACS THEN ASM_REAL_ARITH_TAC);;

let REAL_DIFFERENTIABLE_AT_ACS = prove
 (`!x. abs(x) < &1 ==> acs real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_ACS]);;

let REAL_DIFFERENTIABLE_WITHIN_ACS = prove
 (`!s x. abs(x) < &1 ==> acs real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_ACS]);;

let REAL_CONTINUOUS_AT_ACS = prove
 (`!x. abs(x) < &1 ==> acs real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_ACS;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_ACS = prove
 (`!s x. abs(x) < &1 ==> acs real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_ACS]);;

(* ------------------------------------------------------------------------- *)
(* Hence differentiation of the norm.                                        *)
(* ------------------------------------------------------------------------- *)

let DIFFERENTIABLE_NORM_AT = prove
 (`!a:real^N. ~(a = vec 0) ==> (\x. lift(norm x)) differentiable (at a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_norm] THEN
  SUBGOAL_THEN
   `(\x:real^N. lift(sqrt(x dot x))) =
    (lift o sqrt o drop) o (\x. lift(x dot x))`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
  REWRITE_TAC[DIFFERENTIABLE_SQNORM_AT; GSYM NORM_POW_2] THEN
  MP_TAC(ISPEC `norm(a:real^N) pow 2` REAL_DIFFERENTIABLE_AT_SQRT) THEN
  ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT; REAL_DIFFERENTIABLE_AT]);;

let DIFFERENTIABLE_ON_NORM = prove
 (`!s:real^N->bool. ~(vec 0 IN s) ==> (\x. lift(norm x)) differentiable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_NORM_AT THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some somewhat sharper continuity theorems including endpoints.            *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_WITHIN_SQRT_STRONG = prove
 (`!x. sqrt real_continuous (atreal x within {t | &0 <= t})`,
  GEN_TAC THEN REWRITE_TAC[REAL_COMPLEX_CONTINUOUS_WITHINREAL] THEN
  ASM_CASES_TAC `x IN {t | &0 <= t}` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`csqrt`; `&1`] THEN
    REWRITE_TAC[IMAGE_CX; IN_ELIM_THM; REAL_LT_01;
      CONTINUOUS_WITHIN_CSQRT_POSREAL;
      SET_RULE `real INTER {z | real z /\ P z} = {z | real z /\ P z}`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[REAL_CX; RE_CX; IMP_CONJ; FORALL_REAL; o_THM] THEN
    SIMP_TAC[CX_SQRT];
    MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `real INTER IMAGE Cx {t | &0 <= t} =
                    real INTER {t | Re t >= &0}`
       (fun th -> SIMP_TAC[th; CLOSED_INTER; CLOSED_REAL;
                           CLOSED_HALFSPACE_RE_GE]) THEN
     REWRITE_TAC[EXTENSION; IMAGE_CX; IN_ELIM_THM; IN_CBALL; IN_INTER] THEN
     REWRITE_TAC[real_ge; IN; CONJ_ACI];
      MATCH_MP_TAC(SET_RULE
       `(!x y. f x = f y ==> x = y) /\ ~(x IN s)
        ==> ~(f x IN t INTER IMAGE f s)`) THEN
      ASM_REWRITE_TAC[CX_INJ]]]);;

let REAL_CONTINUOUS_ON_SQRT = prove
 (`!s. (!x. x IN s ==> &0 <= x) ==> sqrt real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
  EXISTS_TAC `{x | &0 <= x}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; REAL_CONTINUOUS_WITHIN_SQRT_STRONG]);;

let REAL_CONTINUOUS_WITHIN_ASN_STRONG = prove
 (`!x. asn real_continuous (atreal x within {t | abs(t) <= &1})`,
  GEN_TAC THEN REWRITE_TAC[REAL_COMPLEX_CONTINUOUS_WITHINREAL] THEN
  ASM_CASES_TAC `x IN {t | abs(t) <= &1}` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`casn`; `&1`] THEN
    REWRITE_TAC[IMAGE_CX; IN_ELIM_THM; CONTINUOUS_WITHIN_CASN_REAL; REAL_LT_01;
     SET_RULE `real INTER {z | real z /\ P z} = {z | real z /\ P z}`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[REAL_CX; RE_CX; IMP_CONJ; FORALL_REAL; o_THM] THEN
    SIMP_TAC[CX_ASN];
    MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `real INTER IMAGE Cx {t | abs t <= &1} =
                    real INTER cball(Cx(&0),&1)`
       (fun th -> SIMP_TAC[th; CLOSED_INTER; CLOSED_REAL; CLOSED_CBALL]) THEN
      REWRITE_TAC[EXTENSION; IMAGE_CX; IN_ELIM_THM; IN_CBALL; IN_INTER] THEN
      REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG; IN] THEN
      MESON_TAC[REAL_NORM];
      MATCH_MP_TAC(SET_RULE
       `(!x y. f x = f y ==> x = y) /\ ~(x IN s)
        ==> ~(f x IN t INTER IMAGE f s)`) THEN
      ASM_REWRITE_TAC[CX_INJ]]]);;

let REAL_CONTINUOUS_ON_ASN = prove
 (`!s. (!x. x IN s ==> abs(x) <= &1) ==> asn real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
  EXISTS_TAC `{x | abs(x) <= &1}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; REAL_CONTINUOUS_WITHIN_ASN_STRONG]);;

let REAL_CONTINUOUS_WITHIN_ACS_STRONG = prove
 (`!x. acs real_continuous (atreal x within {t | abs(t) <= &1})`,
  GEN_TAC THEN REWRITE_TAC[REAL_COMPLEX_CONTINUOUS_WITHINREAL] THEN
  ASM_CASES_TAC `x IN {t | abs(t) <= &1}` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`cacs`; `&1`] THEN
    REWRITE_TAC[IMAGE_CX; IN_ELIM_THM; CONTINUOUS_WITHIN_CACS_REAL; REAL_LT_01;
     SET_RULE `real INTER {z | real z /\ P z} = {z | real z /\ P z}`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[REAL_CX; RE_CX; IMP_CONJ; FORALL_REAL; o_THM] THEN
    SIMP_TAC[CX_ACS];
    MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `real INTER IMAGE Cx {t | abs t <= &1} =
                    real INTER cball(Cx(&0),&1)`
       (fun th -> SIMP_TAC[th; CLOSED_INTER; CLOSED_REAL; CLOSED_CBALL]) THEN
      REWRITE_TAC[EXTENSION; IMAGE_CX; IN_ELIM_THM; IN_CBALL; IN_INTER] THEN
      REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG; IN] THEN
      MESON_TAC[REAL_NORM];
      MATCH_MP_TAC(SET_RULE
       `(!x y. f x = f y ==> x = y) /\ ~(x IN s)
        ==> ~(f x IN t INTER IMAGE f s)`) THEN
      ASM_REWRITE_TAC[CX_INJ]]]);;

let REAL_CONTINUOUS_ON_ACS = prove
 (`!s. (!x. x IN s ==> abs(x) <= &1) ==> acs real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
  EXISTS_TAC `{x | abs(x) <= &1}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; REAL_CONTINUOUS_WITHIN_ACS_STRONG]);;

(* ------------------------------------------------------------------------- *)
(* Differentiation conversion.                                               *)
(* ------------------------------------------------------------------------- *)

let real_differentiation_theorems = ref [];;

let add_real_differentiation_theorems =
  let ETA_THM = prove
   (`(f has_real_derivative f') net <=>
     ((\x. f x) has_real_derivative f') net`,
    REWRITE_TAC[ETA_AX]) in
  let ETA_TWEAK =
    PURE_REWRITE_RULE [IMP_CONJ] o
    GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [ETA_THM] o
    SPEC_ALL in
  fun l -> real_differentiation_theorems :=
              !real_differentiation_theorems @ map ETA_TWEAK l;;

add_real_differentiation_theorems
 ([HAS_REAL_DERIVATIVE_LMUL_WITHIN; HAS_REAL_DERIVATIVE_LMUL_ATREAL;
   HAS_REAL_DERIVATIVE_RMUL_WITHIN; HAS_REAL_DERIVATIVE_RMUL_ATREAL;
   HAS_REAL_DERIVATIVE_CDIV_WITHIN; HAS_REAL_DERIVATIVE_CDIV_ATREAL;
   HAS_REAL_DERIVATIVE_ID;
   HAS_REAL_DERIVATIVE_CONST;
   HAS_REAL_DERIVATIVE_NEG;
   HAS_REAL_DERIVATIVE_ADD;
   HAS_REAL_DERIVATIVE_SUB;
   HAS_REAL_DERIVATIVE_MUL_WITHIN; HAS_REAL_DERIVATIVE_MUL_ATREAL;
   HAS_REAL_DERIVATIVE_DIV_WITHIN; HAS_REAL_DERIVATIVE_DIV_ATREAL;
   HAS_REAL_DERIVATIVE_POW_WITHIN; HAS_REAL_DERIVATIVE_POW_ATREAL;
   HAS_REAL_DERIVATIVE_INV_WITHIN; HAS_REAL_DERIVATIVE_INV_ATREAL] @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN_UNIV
              HAS_REAL_DERIVATIVE_EXP))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN_UNIV
              HAS_REAL_DERIVATIVE_SIN))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN_UNIV
              HAS_REAL_DERIVATIVE_COS))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN
              HAS_REAL_DERIVATIVE_TAN))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN
              HAS_REAL_DERIVATIVE_LOG))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN
              HAS_REAL_DERIVATIVE_SQRT))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN_UNIV
              HAS_REAL_DERIVATIVE_ATN))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN
              HAS_REAL_DERIVATIVE_ASN))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN
              HAS_REAL_DERIVATIVE_ACS))));;

let rec REAL_DIFF_CONV =
  let partfn tm = let l,r = dest_comb tm in mk_pair(lhand l,r)
  and is_deriv = can (term_match [] `(f has_real_derivative f') net`) in
  let rec REAL_DIFF_CONV tm =
    try tryfind (fun th -> PART_MATCH partfn th (partfn tm))
                (!real_differentiation_theorems)
    with Failure _ ->
        let ith = tryfind (fun th ->
         PART_MATCH (partfn o repeat (snd o dest_imp)) th (partfn tm))
                    (!real_differentiation_theorems) in
        REAL_DIFF_ELIM ith
  and REAL_DIFF_ELIM th =
    let tm = concl th in
    if not(is_imp tm) then th else
    let t = lhand tm in
    if not(is_deriv t) then UNDISCH th
    else REAL_DIFF_ELIM (MATCH_MP th (REAL_DIFF_CONV t)) in
  REAL_DIFF_CONV;;

(* ------------------------------------------------------------------------- *)
(* Hence a tactic.                                                           *)
(* ------------------------------------------------------------------------- *)

let REAL_DIFF_TAC =
  let pth = MESON[]
   `(f has_real_derivative f') net
    ==> f' = g'
        ==> (f has_real_derivative g') net` in
  W(fun (asl,w) -> let th = MATCH_MP pth (REAL_DIFF_CONV w) in
       MATCH_MP_TAC(repeat (GEN_REWRITE_RULE I [IMP_IMP]) (DISCH_ALL th)));;

let REAL_DIFFERENTIABLE_TAC =
  let DISCH_FIRST th = DISCH (hd(hyp th)) th in
  GEN_REWRITE_TAC I [real_differentiable] THEN
  W(fun (asl,w) ->
        let th = REAL_DIFF_CONV(snd(dest_exists w)) in
        let f' = rand(rator(concl th)) in
        EXISTS_TAC f' THEN
        (if hyp th = [] then MATCH_ACCEPT_TAC th else
         let th' = repeat (GEN_REWRITE_RULE I [IMP_IMP] o DISCH_FIRST)
                          (DISCH_FIRST th) in
         MATCH_MP_TAC th'));;

(* ------------------------------------------------------------------------- *)
(* Analytic results for real power function.                                 *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_RPOW = prove
 (`!x y.
    &0 < x
    ==> ((\x. x rpow y) has_real_derivative y * x rpow (y - &1)) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\x. exp(y * log x)` THEN EXISTS_TAC `x:real` THEN
  ASM_SIMP_TAC[rpow; REAL_ARITH
    `&0 < x ==> (abs(y - x) < x <=> &0 < y /\ y < &2 * x)`] THEN
  REAL_DIFF_TAC THEN
  ASM_SIMP_TAC[REAL_SUB_RDISTRIB; REAL_EXP_SUB; REAL_MUL_LID; EXP_LOG] THEN
  REAL_ARITH_TAC);;

add_real_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (GEN `y:real` (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN
    (SPEC `y:real`
      (ONCE_REWRITE_RULE[SWAP_FORALL_THM] HAS_REAL_DERIVATIVE_RPOW))))));;

let HAS_REAL_DERIVATIVE_RPOW_RIGHT = prove
 (`!a x. &0 < a
         ==> ((\x. a rpow x) has_real_derivative log(a) * a rpow x)
              (atreal x)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[rpow] THEN
  REAL_DIFF_TAC THEN REAL_ARITH_TAC);;

add_real_differentiation_theorems
(CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN
              (SPEC `a:real` HAS_REAL_DERIVATIVE_RPOW_RIGHT))));;

let REAL_DIFFERENTIABLE_AT_RPOW = prove
 (`!x y. ~(x = &0) ==> (\x. x rpow y) real_differentiable atreal x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `~(x = &0) <=> &0 < x \/ &0 < --x`] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_TRANSFORM_ATREAL THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  EXISTS_TAC `abs x` THENL
   [EXISTS_TAC `\x. exp(y * log x)` THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> &0 < abs x`] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < z` (fun th -> REWRITE_TAC[rpow; th]) THEN
      ASM_REAL_ARITH_TAC;
      REAL_DIFFERENTIABLE_TAC THEN ASM_REAL_ARITH_TAC];
    ASM_CASES_TAC `?m n. ODD m /\ ODD n /\ abs y = &m / &n` THENL
     [EXISTS_TAC `\x. --(exp(y * log(--x)))`;
      EXISTS_TAC `\x. exp(y * log(--x))`] THEN
    (ASM_SIMP_TAC[REAL_ARITH `&0 < --x ==> &0 < abs x`] THEN CONJ_TAC THENL
      [X_GEN_TAC `z:real` THEN DISCH_TAC THEN
       SUBGOAL_THEN `~(&0 < z) /\ ~(z = &0)`
         (fun th -> ASM_REWRITE_TAC[rpow; th]) THEN
       ASM_REAL_ARITH_TAC;
       REAL_DIFFERENTIABLE_TAC THEN ASM_REAL_ARITH_TAC])]);;

let REAL_CONTINUOUS_AT_RPOW = prove
 (`!x y. (x = &0 ==> &0 <= y)
         ==> (\x. x rpow y) real_continuous (atreal x)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `y = &0` THEN
  ASM_REWRITE_TAC[RPOW_POW; real_pow; REAL_CONTINUOUS_CONST] THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[real_continuous_atreal; RPOW_ZERO] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_ABS_RPOW] THEN STRIP_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `e rpow inv(y)` THEN
    ASM_SIMP_TAC[RPOW_POS_LT] THEN X_GEN_TAC `z:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `e rpow inv y rpow y` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LT2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE; REAL_MUL_LINV] THEN
      REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL]];
    ASM_SIMP_TAC[REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL;
                 REAL_DIFFERENTIABLE_AT_RPOW]]);;

let REAL_CONTINUOUS_WITHIN_RPOW = prove
 (`!s x y. (x = &0 ==> &0 <= y)
           ==> (\x. x rpow y) real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_RPOW]);;

let REAL_CONTINUOUS_ON_RPOW = prove
 (`!s y. (&0 IN s ==> &0 <= y) ==> (\x. x rpow y) real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_RPOW THEN
  ASM_MESON_TAC[]);;

let REALLIM_RPOW = prove
 (`!net f l n.
        (f ---> l) net /\ (l = &0 ==> &0 <= n)
        ==> ((\x. f x rpow n) ---> l rpow n) net`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
  (REWRITE_RULE[] (ISPEC `\x. x rpow n` REALLIM_REAL_CONTINUOUS_FUNCTION)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW THEN
  ASM_REWRITE_TAC[]);;

let REALLIM_NULL_POW_EQ = prove
 (`!net f n.
        ~(n = 0)
        ==> (((\x. f x pow n) ---> &0) net <=> (f ---> &0) net)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[REALLIM_NULL_POW] THEN
  DISCH_THEN(MP_TAC o ISPEC `(\x. x rpow (inv(&n))) o abs` o
    MATCH_MP(REWRITE_RULE[IMP_CONJ_ALT] REALLIM_REAL_CONTINUOUS_FUNCTION)) THEN
  REWRITE_TAC[o_THM] THEN
  ASM_REWRITE_TAC[RPOW_ZERO; REAL_INV_EQ_0; REAL_OF_NUM_EQ; REAL_ABS_NUM] THEN
  SIMP_TAC[GSYM RPOW_POW; RPOW_RPOW; REAL_ABS_POS; REAL_ABS_RPOW] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[REALLIM_NULL_ABS; RPOW_POW; REAL_POW_1] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ABS THEN
    REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID];
    MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_RPOW THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]]);;

let LIM_NULL_COMPLEX_POW_EQ = prove
 (`!net f n.
        ~(n = 0)
        ==> (((\x. f x pow n) --> Cx(&0)) net <=> (f --> Cx(&0)) net)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  ONCE_REWRITE_TAC[LIM_NULL_NORM] THEN
  REWRITE_TAC[COMPLEX_NORM_POW; REAL_TENDSTO; o_DEF; LIFT_DROP] THEN
  ASM_SIMP_TAC[REALLIM_NULL_POW_EQ; DROP_VEC]);;

(* ------------------------------------------------------------------------- *)
(* Analytic result for "frac".                                               *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_FRAC = prove
 (`!x. ~(integer x) ==> (frac has_real_derivative (&1)) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\y. y - floor x` THEN
  EXISTS_TAC `min (frac x) (floor x + &1 - x)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_FRAC_POS_LT] THEN
  REWRITE_TAC[REAL_ARITH `&0 < x + &1 - y <=> y < x + &1`; FLOOR] THEN
  CONJ_TAC THENL [ALL_TAC; REAL_DIFF_TAC THEN REAL_ARITH_TAC] THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM FRAC_UNIQUE; REAL_ARITH `y - (y - x):real = x`] THEN
  MP_TAC(SPEC `x:real` FLOOR_FRAC) THEN SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

let REAL_DIFFERENTIABLE_FRAC = prove
 (`!x. ~(integer x) ==> frac real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_FRAC]);;

add_real_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
  (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN HAS_REAL_DERIVATIVE_FRAC)));;

(* ------------------------------------------------------------------------- *)
(* Polynomials are differentiable and continuous.                            *)
(* ------------------------------------------------------------------------- *)

let REAL_DIFFERENTIABLE_POLYNOMIAL_FUNCTION_ATREAL = prove
 (`!p x. polynomial_function p ==> p real_differentiable atreal x`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC POLYNOMIAL_FUNCTION_INDUCT THEN
  SIMP_TAC[REAL_DIFFERENTIABLE_CONST; REAL_DIFFERENTIABLE_ID;
           REAL_DIFFERENTIABLE_ADD; REAL_DIFFERENTIABLE_MUL_ATREAL]);;

let REAL_DIFFERENTIABLE_POLYNOMIAL_FUNCTION_WITHIN = prove
 (`!p s x. polynomial_function p ==> p real_differentiable atreal x within s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_POLYNOMIAL_FUNCTION_ATREAL;
           REAL_DIFFERENTIABLE_ATREAL_WITHIN]);;

let REAL_DIFFERENTIABLE_ON_POLYNOMIAL_FUNCTION = prove
 (`!p s. polynomial_function p ==> p real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
           REAL_DIFFERENTIABLE_POLYNOMIAL_FUNCTION_WITHIN]);;

let REAL_CONTINUOUS_POLYNOMIAL_FUNCTION_ATREAL = prove
 (`!p x. polynomial_function p ==> p real_continuous atreal x`,
  SIMP_TAC[REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL;
           REAL_DIFFERENTIABLE_POLYNOMIAL_FUNCTION_ATREAL]);;

let REAL_CONTINUOUS_POLYNOMIAL_FUNCTION_WITHIN = prove
 (`!p s x. polynomial_function p ==> p real_continuous atreal x within s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL;
           REAL_DIFFERENTIABLE_POLYNOMIAL_FUNCTION_WITHIN]);;

let REAL_CONTINUOUS_ON_POLYNOMIAL_FUNCTION = prove
 (`!p s. polynomial_function p ==> p real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
           REAL_CONTINUOUS_POLYNOMIAL_FUNCTION_WITHIN]);;

(* ------------------------------------------------------------------------- *)
(* Intermediate Value Theorem.                                               *)
(* ------------------------------------------------------------------------- *)

let REAL_IVT_INCREASING = prove
 (`!f a b y.
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        f a <= y /\ y <= f b
        ==> ?x. x IN real_interval [a,b] /\ f x = y`,
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift a`; `lift b`; `y:real`; `1`]
        IVT_INCREASING_COMPONENT_ON_1) THEN
  ASM_REWRITE_TAC[GSYM drop; o_THM; LIFT_DROP; DIMINDEX_1; LE_REFL] THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; EXISTS_IN_IMAGE; LIFT_DROP]);;

let REAL_IVT_DECREASING = prove
 (`!f a b y.
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        f b <= y /\ y <= f a
        ==> ?x. x IN real_interval [a,b] /\ f x = y`,
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift a`; `lift b`; `y:real`; `1`]
        IVT_DECREASING_COMPONENT_ON_1) THEN
  ASM_REWRITE_TAC[GSYM drop; o_THM; LIFT_DROP; DIMINDEX_1; LE_REFL] THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; EXISTS_IN_IMAGE; LIFT_DROP]);;

let IS_REALINTERVAL_CONTINUOUS_IMAGE = prove
 (`!s. f real_continuous_on s /\ is_realinterval s
       ==> is_realinterval(IMAGE f s)`,
  GEN_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON; IS_REALINTERVAL_CONNECTED] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONNECTED_CONTINUOUS_IMAGE) THEN
  REWRITE_TAC[IMAGE_o; REWRITE_RULE[IMAGE_o] IMAGE_LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Zeroness (or sign at boundary) of derivative at local extremum.           *)
(* ------------------------------------------------------------------------- *)

let REAL_DERIVATIVE_POS_LEFT_MINIMUM = prove
 (`!f f' a b e.
        a < b /\ &0 < e /\
        (f has_real_derivative f') (atreal a within real_interval[a,b]) /\
        (!x. x IN real_interval[a,b] /\ abs(x - a) < e ==> f a <= f x)
        ==> &0 <= f'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `\x:real^1. f' % x`;
                 `lift a`; `interval[lift a,lift b]`; `e:real`]
        DROP_DIFFERENTIAL_POS_AT_MINIMUM) THEN
  ASM_REWRITE_TAC[ENDS_IN_INTERVAL; CONVEX_INTERVAL; IN_INTER; IMP_CONJ] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IMAGE_EQ_EMPTY;
                  GSYM HAS_REAL_FRECHET_DERIVATIVE_WITHIN] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP; IN_BALL; DIST_LIFT;
               REAL_INTERVAL_NE_EMPTY; REAL_LT_IMP_LE] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_ABS_SUB]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
  ASM_SIMP_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_NE_EMPTY;
               REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[DROP_CMUL; DROP_SUB; LIFT_DROP; REAL_LE_MUL_EQ;
               REAL_SUB_LT]);;

let REAL_DERIVATIVE_NEG_LEFT_MAXIMUM = prove
 (`!f f' a b e.
        a < b /\ &0 < e /\
        (f has_real_derivative f') (atreal a within real_interval[a,b]) /\
        (!x. x IN real_interval[a,b] /\ abs(x - a) < e ==> f x <= f a)
        ==> f' <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `\x:real^1. f' % x`;
                 `lift a`; `interval[lift a,lift b]`; `e:real`]
        DROP_DIFFERENTIAL_NEG_AT_MAXIMUM) THEN
  ASM_REWRITE_TAC[ENDS_IN_INTERVAL; CONVEX_INTERVAL; IN_INTER; IMP_CONJ] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IMAGE_EQ_EMPTY;
                  GSYM HAS_REAL_FRECHET_DERIVATIVE_WITHIN] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP; IN_BALL; DIST_LIFT;
               REAL_INTERVAL_NE_EMPTY; REAL_LT_IMP_LE] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_ABS_SUB]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
  ASM_SIMP_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_NE_EMPTY;
               REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[DROP_CMUL; DROP_SUB; LIFT_DROP; REAL_LE_MUL_EQ;
               REAL_SUB_LT; REAL_ARITH `f * ba <= &0 <=> &0 <= --f * ba`] THEN
  REAL_ARITH_TAC);;

let REAL_DERIVATIVE_POS_RIGHT_MAXIMUM = prove
 (`!f f' a b e.
        a < b /\ &0 < e /\
        (f has_real_derivative f') (atreal b within real_interval[a,b]) /\
        (!x. x IN real_interval[a,b] /\ abs(x - b) < e ==> f x <= f b)
        ==> &0 <= f'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `\x:real^1. f' % x`;
                 `lift b`; `interval[lift a,lift b]`; `e:real`]
        DROP_DIFFERENTIAL_NEG_AT_MAXIMUM) THEN
  ASM_REWRITE_TAC[ENDS_IN_INTERVAL; CONVEX_INTERVAL; IN_INTER; IMP_CONJ] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IMAGE_EQ_EMPTY;
                  GSYM HAS_REAL_FRECHET_DERIVATIVE_WITHIN] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP; IN_BALL; DIST_LIFT;
               REAL_INTERVAL_NE_EMPTY; REAL_LT_IMP_LE] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_ABS_SUB]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real`) THEN
  ASM_SIMP_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_NE_EMPTY;
               REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[DROP_CMUL; DROP_SUB; LIFT_DROP; REAL_LE_MUL_EQ; REAL_SUB_LT;
               REAL_ARITH `f * (a - b) <= &0 <=> &0 <= f * (b - a)`]);;

let REAL_DERIVATIVE_NEG_RIGHT_MINIMUM = prove
 (`!f f' a b e.
        a < b /\ &0 < e /\
        (f has_real_derivative f') (atreal b within real_interval[a,b]) /\
        (!x. x IN real_interval[a,b] /\ abs(x - b) < e ==> f b <= f x)
        ==> f' <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `\x:real^1. f' % x`;
                 `lift b`; `interval[lift a,lift b]`; `e:real`]
        DROP_DIFFERENTIAL_POS_AT_MINIMUM) THEN
  ASM_REWRITE_TAC[ENDS_IN_INTERVAL; CONVEX_INTERVAL; IN_INTER; IMP_CONJ] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IMAGE_EQ_EMPTY;
                  GSYM HAS_REAL_FRECHET_DERIVATIVE_WITHIN] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP; IN_BALL; DIST_LIFT;
               REAL_INTERVAL_NE_EMPTY; REAL_LT_IMP_LE] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_ABS_SUB]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real`) THEN
  ASM_SIMP_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_NE_EMPTY;
               REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[DROP_CMUL; DROP_SUB; LIFT_DROP] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&0 <= f * (a - b) <=> &0 <= --f * (b - a)`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL_EQ; REAL_SUB_LT] THEN REAL_ARITH_TAC);;

let REAL_DERIVATIVE_ZERO_MAXMIN = prove
 (`!f f' x s.
        x IN s /\ real_open s /\
        (f has_real_derivative f') (atreal x) /\
        ((!y. y IN s ==> f y <= f x) \/ (!y. y IN s ==> f x <= f y))
        ==> f' = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `\x:real^1. f' % x`;
                 `lift x`; `IMAGE lift s`]
        DIFFERENTIAL_ZERO_MAXMIN) THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT; GSYM REAL_OPEN] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  DISCH_THEN(MP_TAC o C AP_THM `vec 1:real^1`) THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC; REAL_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* Rolle and Mean Value Theorem.                                             *)
(* ------------------------------------------------------------------------- *)

let REAL_ROLLE = prove
 (`!f f' a b.
        a < b /\ f a = f b /\
        f real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b)
             ==> (f has_real_derivative f'(x)) (atreal x))
        ==> ?x. x IN real_interval(a,b) /\ f'(x) = &0`,
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  REWRITE_TAC[GSYM IMAGE_o; IMAGE_LIFT_DROP; has_vector_derivative] THEN
  REWRITE_TAC[LIFT_DROP] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `\x:real^1 h:real^1. f'(drop x) % h`;
                 `lift a`; `lift b`] ROLLE) THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP] THEN ANTS_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_LIFT; LIFT_DROP; GSYM LIFT_CMUL] THEN
    REWRITE_TAC[REAL_MUL_AC];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^1` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o C AP_THM `lift(&1)`) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_NUM; LIFT_EQ; REAL_MUL_RID]]);;

let REAL_MVT = prove
 (`!f f' a b.
        a < b /\
        f real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b)
             ==> (f has_real_derivative f'(x)) (atreal x))
        ==> ?x. x IN real_interval(a,b) /\ f(b) - f(a) = f'(x) * (b - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. f(x) - (f b - f a) / (b - a) * x`;
                `(\x. f'(x) - (f b - f a) / (b - a)):real->real`;
                 `a:real`; `b:real`]
               REAL_ROLLE) THEN
  ASM_SIMP_TAC[REAL_FIELD
   `a < b ==> (fx - fba / (b - a) = &0 <=> fba = fx * (b - a))`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_LMUL;
               REAL_CONTINUOUS_ON_ID] THEN
  CONJ_TAC THENL [UNDISCH_TAC `a < b` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
  ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_LMUL_ATREAL; HAS_REAL_DERIVATIVE_ID]);;

let REAL_MVT_SIMPLE = prove
 (`!f f' a b.
        a < b /\
        (!x. x IN real_interval[a,b]
             ==> (f has_real_derivative f'(x))
                 (atreal x within real_interval[a,b]))
        ==> ?x. x IN real_interval(a,b) /\ f(b) - f(a) = f'(x) * (b - a)`,
  MP_TAC REAL_MVT THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    ASM_MESON_TAC[real_differentiable_on; real_differentiable];
    ASM_MESON_TAC[HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN; REAL_OPEN_REAL_INTERVAL;
                  REAL_INTERVAL_OPEN_SUBSET_CLOSED;
                  HAS_REAL_DERIVATIVE_WITHIN_SUBSET; SUBSET]]);;

let REAL_MVT_VERY_SIMPLE = prove
 (`!f f' a b.
        a <= b /\
        (!x. x IN real_interval[a,b]
             ==> (f has_real_derivative f'(x))
                 (atreal x within real_interval[a,b]))
        ==> ?x. x IN real_interval[a,b] /\ f(b) - f(a) = f'(x) * (b - a)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:real = a` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN
    REWRITE_TAC[REAL_INTERVAL_SING; IN_SING; EXISTS_REFL];
    ASM_REWRITE_TAC[REAL_LE_LT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_MVT_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[REWRITE_RULE[SUBSET] REAL_INTERVAL_OPEN_SUBSET_CLOSED]]);;

let REAL_ROLLE_SIMPLE = prove
 (`!f f' a b.
        a < b /\ f a = f b /\
        (!x. x IN real_interval[a,b]
             ==> (f has_real_derivative f'(x))
                 (atreal x within real_interval[a,b]))
        ==> ?x. x IN real_interval(a,b) /\ f'(x) = &0`,
  MP_TAC REAL_MVT_SIMPLE THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[REAL_RING `a - a = b * (c - d) <=> b = &0 \/ c = d`] THEN
  ASM_MESON_TAC[REAL_LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Cauchy MVT and l'Hospital's rule.                                         *)
(* ------------------------------------------------------------------------- *)

let REAL_MVT_CAUCHY = prove
 (`!f g f' g' a b.
           a < b /\
           f real_continuous_on real_interval[a,b] /\
           g real_continuous_on real_interval[a,b] /\
           (!x. x IN real_interval(a,b)
                ==> (f has_real_derivative f' x) (atreal x) /\
                    (g has_real_derivative g' x) (atreal x))
           ==> ?x. x IN real_interval(a,b) /\
                   (f b - f a) * g'(x) = (g b - g a) * f'(x)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL
   [`\x. (f:real->real)(x) * (g(b:real) - g(a)) - g(x) * (f(b) - f(a))`;
    `\x. (f':real->real)(x) * (g(b:real) - g(a)) - g'(x) * (f(b) - f(a))`;
    `a:real`; `b:real`] REAL_MVT) THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_RMUL;
               HAS_REAL_DERIVATIVE_SUB; HAS_REAL_DERIVATIVE_RMUL_ATREAL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN
  UNDISCH_TAC `a < b` THEN CONV_TAC REAL_FIELD);;

let LHOSPITAL = prove
 (`!f g f' g' c l d.
        &0 < d /\
        (!x. &0 < abs(x - c) /\ abs(x - c) < d
             ==> (f has_real_derivative f'(x)) (atreal x) /\
                 (g has_real_derivative g'(x)) (atreal x) /\
                 ~(g'(x) = &0)) /\
        (f ---> &0) (atreal c) /\ (g ---> &0) (atreal c) /\
        ((\x. f'(x) / g'(x)) ---> l) (atreal c)
        ==> ((\x. f(x) / g(x)) ---> l) (atreal c)`,
  SUBGOAL_THEN
    `!f g f' g' c l d.
        &0 < d /\
        (!x. &0 < abs(x - c) /\ abs(x - c) < d
             ==> (f has_real_derivative f'(x)) (atreal x) /\
                 (g has_real_derivative g'(x)) (atreal x) /\
                 ~(g'(x) = &0)) /\
        f(c) = &0 /\ g(c) = &0 /\
        (f ---> &0) (atreal c) /\ (g ---> &0) (atreal c) /\
        ((\x. f'(x) / g'(x)) ---> l) (atreal c)
        ==> ((\x. f(x) / g(x)) ---> l) (atreal c)`
  ASSUME_TAC THENL
   [REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(!x. abs(x - c) < d ==> f real_continuous atreal x) /\
      (!x. abs(x - c) < d ==> g real_continuous atreal x)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `x:real` THEN
      DISJ_CASES_TAC(REAL_ARITH `x = c \/ &0 < abs(x - c)`) THENL
       [ASM_REWRITE_TAC[REAL_CONTINUOUS_ATREAL]; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REWRITE_TAC[real_differentiable] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x.  &0 < abs(x - c) /\ abs(x - c) < d ==> ~(g x = &0)`
    STRIP_ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `c < x \/ x < c` DISJ_CASES_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`g:real->real`; `g':real->real`; `c:real`; `x:real`]
          REAL_ROLLE);
        MP_TAC(ISPECL [`g:real->real`; `g':real->real`; `x:real`; `c:real`]
          REAL_ROLLE)] THEN
      ASM_REWRITE_TAC[NOT_IMP; NOT_EXISTS_THM] THEN
      (REPEAT CONJ_TAC THENL
        [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
         REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
         MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL;
         REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC;
         X_GEN_TAC `y:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
         DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
         REWRITE_TAC[]] THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);
      ALL_TAC] THEN
    UNDISCH_TAC `((\x. f' x / g' x) ---> l) (atreal c)` THEN
    REWRITE_TAC[REALLIM_ATREAL] THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC `e:real` THEN ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d k:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?y. &0 < abs(y - c) /\ abs(y - c) < abs(x - c) /\
          (f:real->real) x / g x = f' y / g' y`
    STRIP_ASSUME_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_TRANS]] THEN
    SUBGOAL_THEN `c < x \/ x < c` DISJ_CASES_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL
       [`f:real->real`; `g:real->real`; `f':real->real`; `g':real->real`;
        `c:real`; `x:real`] REAL_MVT_CAUCHY);
      MP_TAC(ISPECL
       [`f:real->real`; `g:real->real`; `f':real->real`; `g':real->real`;
        `x:real`; `c:real`] REAL_MVT_CAUCHY)] THEN
    (ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL
      [REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
        [CONJ_TAC THEN
         REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
         REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
         MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL;
         REPEAT STRIP_TAC] THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
       MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
       GEN_TAC THEN STRIP_TAC THEN
        REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
       MATCH_MP_TAC(REAL_FIELD
        `f * g' = g * f' /\ ~(g = &0) /\ ~(g' = &0) ==> f / g = f' / g'`) THEN
       CONJ_TAC THENL [ASM_REAL_ARITH_TAC; CONJ_TAC] THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);
    REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`\x:real. if x = c then &0 else f(x)`;
                `\x:real. if x = c then &0 else g(x)`;
                `f':real->real`; `g':real->real`;
                `c:real`; `l:real`; `d:real`]) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
    TRY(SIMP_TAC[REALLIM_ATREAL;REAL_ARITH `&0 < abs(x - c) ==> ~(x = c)`] THEN
        NO_TAC) THEN
    DISCH_TAC THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
          HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL) THEN
    EXISTS_TAC `abs(x - c)` THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Darboux's theorem (intermediate value property for derivatives).          *)
(* ------------------------------------------------------------------------- *)

let REAL_DERIVATIVE_IVT_INCREASING = prove
 (`!f f' a b.
   a <= b /\
   (!x. x IN real_interval[a,b]
        ==> (f has_real_derivative f'(x)) (atreal x within real_interval[a,b]))
   ==> !t. f'(a) <= t /\ t <= f'(b)
           ==> ?x. x IN real_interval[a,b] /\ f' x = t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ASM_CASES_TAC `(f':real->real) a = t` THENL
   [ASM_MESON_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_NE_EMPTY];
    ALL_TAC] THEN
  ASM_CASES_TAC `(f':real->real) b = t` THENL
   [ASM_MESON_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_NE_EMPTY];
    ALL_TAC] THEN
  ASM_CASES_TAC `b:real = a` THEN ASM_REWRITE_TAC[REAL_LE_ANTISYM] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real. f x - t * x`; `real_interval[a,b]`]
        REAL_CONTINUOUS_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[REAL_INTERVAL_NE_EMPTY; REAL_COMPACT_INTERVAL] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_SUB THEN
    SIMP_TAC[REAL_DIFFERENTIABLE_ON_MUL; REAL_DIFFERENTIABLE_ON_ID;
             REAL_DIFFERENTIABLE_ON_CONST] THEN
    ASM_MESON_TAC[real_differentiable_on];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL
   [`\x:real. f x - t * x`; `(f':real->real) x - t:real`;
    `x:real`; `real_interval(a,b)`]
        REAL_DERIVATIVE_ZERO_MAXMIN) THEN
  ASM_REWRITE_TAC[REAL_SUB_0] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[REAL_OPEN_REAL_INTERVAL] THEN
  ASM_SIMP_TAC[REAL_OPEN_CLOSED_INTERVAL; IN_DIFF] THEN
  ASM_CASES_TAC `x:real = a` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL[`\x:real. f x - t * x`; `(f':real->real) a - t:real`;
                  `a:real`; `b:real`; `&1`]
        REAL_DERIVATIVE_POS_LEFT_MINIMUM) THEN
    ASM_SIMP_TAC[REAL_LT_01; REAL_SUB_LE] THEN
    MATCH_MP_TAC(TAUT `~q /\ p ==> (p ==> q) ==> r`) THEN
    ASM_REWRITE_TAC[REAL_NOT_LE] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
    CONJ_TAC THENL [ALL_TAC; REAL_DIFF_TAC THEN REWRITE_TAC[REAL_MUL_RID]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY];
    ALL_TAC] THEN
  ASM_CASES_TAC `x:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL[`\x:real. f x - t * x`; `(f':real->real) b - t:real`;
                  `a:real`; `b:real`; `&1`]
        REAL_DERIVATIVE_NEG_RIGHT_MINIMUM) THEN
    ASM_SIMP_TAC[REAL_LT_01; REAL_SUB_LE] THEN
    MATCH_MP_TAC(TAUT `~q /\ p ==> (p ==> q) ==> r`) THEN
    ASM_REWRITE_TAC[REAL_NOT_LE; REAL_SUB_LT] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
    CONJ_TAC THENL [ALL_TAC; REAL_DIFF_TAC THEN REWRITE_TAC[REAL_MUL_RID]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
  CONJ_TAC THENL [ALL_TAC; REAL_DIFF_TAC THEN REWRITE_TAC[REAL_MUL_RID]] THEN
  SUBGOAL_THEN
   `(f has_real_derivative f' x) (atreal x within real_interval(a,b))`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[a,b]` THEN
    ASM_SIMP_TAC[REAL_INTERVAL_OPEN_SUBSET_CLOSED];
    MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN THEN
    REWRITE_TAC[REAL_OPEN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[REAL_OPEN_CLOSED_INTERVAL] THEN ASM SET_TAC[]]);;

let REAL_DERIVATIVE_IVT_DECREASING = prove
 (`!f f' a b t.
   a <= b /\
   (!x. x IN real_interval[a,b]
        ==> (f has_real_derivative f'(x)) (atreal x within real_interval[a,b]))
   ==> !t. f'(b) <= t /\ t <= f'(a)
           ==> ?x. x IN real_interval[a,b] /\ f' x = t`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL
   [`\x. --((f:real->real) x)`; `\x. --((f':real->real) x)`;
    `a:real`; `b:real`] REAL_DERIVATIVE_IVT_INCREASING) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_NEG] THEN
  DISCH_THEN(MP_TAC o SPEC `--t:real`) THEN
  ASM_REWRITE_TAC[REAL_LE_NEG2; REAL_EQ_NEG2]);;

(* ------------------------------------------------------------------------- *)
(* Continuity and differentiability of inverse functions.                    *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_INVERSE_BASIC = prove
 (`!f g f' t y.
        (f has_real_derivative f') (atreal (g y)) /\
        ~(f' = &0) /\
        g real_continuous atreal y /\
        real_open t /\
        y IN t /\
        (!z. z IN t ==> f (g z) = z)
        ==> (g has_real_derivative inv(f')) (atreal y)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; REAL_OPEN;
              REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_BASIC THEN
  MAP_EVERY EXISTS_TAC
   [`lift o f o drop`; `\x:real^1. f' % x`; `IMAGE lift t`] THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP; LIFT_IN_IMAGE_LIFT] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; LIFT_DROP; LINEAR_COMPOSE_CMUL; LINEAR_ID] THEN
  REWRITE_TAC[FUN_EQ_THM; I_THM; o_THM; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID]);;

let HAS_REAL_DERIVATIVE_INVERSE_STRONG = prove
 (`!f g f' s x.
         real_open s /\
         x IN s /\
         f real_continuous_on s /\
         (!x. x IN s ==> g (f x) = x) /\
         (f has_real_derivative f') (atreal x) /\
         ~(f' = &0)
         ==> (g has_real_derivative inv(f')) (atreal (f x))`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; REAL_OPEN;
              REAL_CONTINUOUS_ON] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `lift o f o drop` HAS_DERIVATIVE_INVERSE_STRONG) THEN
  REWRITE_TAC[FORALL_LIFT; o_THM; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`\x:real^1. f' % x`; `IMAGE lift s`] THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP; LIFT_IN_IMAGE_LIFT] THEN
  ASM_SIMP_TAC[FUN_EQ_THM; I_THM; o_THM; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID]);;

let HAS_REAL_DERIVATIVE_INVERSE_STRONG_X = prove
 (`!f g f' s y.
        real_open s /\ (g y) IN s /\ f real_continuous_on s /\
        (!x. x IN s ==> (g(f(x)) = x)) /\
        (f has_real_derivative f') (atreal (g y)) /\ ~(f' = &0) /\
        f(g y) = y
        ==> (g has_real_derivative inv(f')) (atreal y)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; REAL_OPEN;
              REAL_CONTINUOUS_ON] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `lift o f o drop` HAS_DERIVATIVE_INVERSE_STRONG_X) THEN
  REWRITE_TAC[FORALL_LIFT; o_THM; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`\x:real^1. f' % x`; `IMAGE lift s`] THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP; LIFT_IN_IMAGE_LIFT] THEN
  ASM_SIMP_TAC[FUN_EQ_THM; I_THM; o_THM; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Real differentiation of sequences and series.                             *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_SEQUENCE = prove
 (`!s f f' g'.
         is_realinterval s /\
         (!n x. x IN s
                ==> (f n has_real_derivative f' n x) (atreal x within s)) /\
         (!e. &0 < e
              ==> ?N. !n x. n >= N /\ x IN s ==> abs(f' n x - g' x) <= e) /\
         (?x l. x IN s /\ ((\n. f n x) ---> l) sequentially)
         ==> ?g. !x. x IN s
                     ==> ((\n. f n x) ---> g x) sequentially /\
                         (g has_real_derivative g' x) (atreal x within s)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN; IS_REALINTERVAL_CONVEX;
              TENDSTO_REAL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE lift s`;
                 `\n:num. lift o f n o drop`;
                 `\n:num x:real^1 h:real^1. f' n (drop x) % h`;
                 `\x:real^1 h:real^1. g' (drop x) % h`]
         HAS_DERIVATIVE_SEQUENCE) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP] THEN ANTS_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_EXISTS_AND_THM; RIGHT_FORALL_IMP_THM;
                EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[EXISTS_LIFT; o_THM; LIFT_DROP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
    ASM_MESON_TAC[REAL_LE_RMUL; NORM_POS_LE];
    REWRITE_TAC[o_DEF; LIFT_DROP] THEN
    DISCH_THEN(X_CHOOSE_TAC `g:real^1->real^1`) THEN
    EXISTS_TAC `drop o g o lift` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]]);;

let HAS_REAL_DERIVATIVE_SERIES = prove
 (`!s f f' g' k.
         is_realinterval s /\
         (!n x. x IN s
                ==> (f n has_real_derivative f' n x) (atreal x within s)) /\
         (!e. &0 < e
              ==> ?N. !n x. n >= N /\ x IN s
                            ==> abs(sum (k INTER (0..n)) (\i. f' i x) - g' x)
                                    <= e) /\
         (?x l. x IN s /\ ((\n. f n x) real_sums l) k)
         ==> ?g. !x. x IN s
                     ==> ((\n. f n x) real_sums g x) k /\
                         (g has_real_derivative g' x) (atreal x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sums] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SEQUENCE THEN EXISTS_TAC
   `\n:num x:real. sum(k INTER (0..n)) (\n. f' n x):real` THEN
  ASM_SIMP_TAC[ETA_AX; FINITE_INTER_NUMSEG; HAS_REAL_DERIVATIVE_SUM]);;

let REAL_DIFFERENTIABLE_BOUND = prove
 (`!f f' s B.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s) /\
                        abs(f' x) <= B)
        ==> !x y. x IN s /\ y IN s ==> abs(f x - f y) <= B * abs(x - y)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN; IS_REALINTERVAL_CONVEX;
              o_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`lift o f o drop`; `\x h:real^1. f' (drop x) % h`;
    `IMAGE lift s`; `B:real`]
        DIFFERENTIABLE_BOUND) THEN
  ASM_SIMP_TAC[o_DEF; FORALL_IN_IMAGE; LIFT_DROP] THEN ANTS_TAC THENL
   [X_GEN_TAC `v:real` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `\h:real^1. f' (v:real) % h` ONORM) THEN
    SIMP_TAC[LINEAR_COMPOSE_CMUL; LINEAR_ID] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_LE_RMUL; NORM_POS_LE];
    SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; LIFT_DROP] THEN
    ASM_SIMP_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM LIFT_SUB; NORM_LIFT]]);;

let REAL_TAYLOR_MVT_POS = prove
 (`!f a x n.
    a < x /\
    (!i t. t IN real_interval[a,x] /\ i <= n
           ==> ((f i) has_real_derivative f (i + 1) t)
               (atreal t within real_interval[a,x]))
    ==> ?t. t IN real_interval(a,x) /\
            f 0 x =
              sum (0..n) (\i. f i a * (x - a) pow i / &(FACT i)) +
              f (n + 1) t * (x - a) pow (n + 1) / &(FACT(n + 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?B. sum (0..n) (\i. f i a * (x - a) pow i / &(FACT i)) +
        B * (x - a) pow (n + 1) = f 0 x`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[]
     `a + (y - a) / x * x:real = y ==> ?b. a + b * x = y`) THEN
    MATCH_MP_TAC(REAL_FIELD `~(x = &0) ==> a + (y - a) / x * x = y`) THEN
    ASM_REWRITE_TAC[REAL_POW_EQ_0; REAL_SUB_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`\t. sum(0..n) (\i. f i t * (x - t) pow i / &(FACT i)) +
                     B * (x - t) pow (n + 1)`;
                `\t. (f (n + 1) t * (x - t) pow n / &(FACT n)) -
                     B * &(n + 1) * (x - t) pow n`;
                `a:real`; `x:real`]
        REAL_ROLLE_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
      REWRITE_TAC[GSYM ADD1; real_pow; REAL_SUB_REFL; REAL_POW_ZERO;
                  REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[NOT_SUC; REAL_MUL_RZERO; REAL_DIV_1; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_ARITH `x = (x + y) + &0 <=> y = &0`] THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
      SIMP_TAC[ARITH; ARITH_RULE `1 <= i ==> ~(i = 0)`] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[real_sub] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [ALL_TAC;
      REAL_DIFF_TAC THEN REWRITE_TAC[ADD_SUB] THEN CONV_TAC REAL_RING] THEN
    REWRITE_TAC[GSYM real_sub] THEN
    MATCH_MP_TAC(MESON[]
     `!g'. f' = g' /\ (f has_real_derivative g') net
           ==> (f has_real_derivative f') net`) THEN
    EXISTS_TAC
     `sum (0..n) (\i. f i t * --(&i * (x - t) pow (i - 1)) / &(FACT i) +
                                f (i + 1) t * (x - t) pow i / &(FACT i))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_WITHIN THEN
      ASM_SIMP_TAC[ETA_AX] THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH; FACT; REAL_DIV_1;
             real_pow; REAL_MUL_LZERO; REAL_NEG_0; REAL_MUL_RZERO;
             REAL_MUL_RID; REAL_ADD_LID] THEN
    ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; FACT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[SPECL [`f:num->real`; `1`] SUM_OFFSET_0; LE_1] THEN
    REWRITE_TAC[ADD_SUB] THEN
    REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
                GSYM REAL_OF_NUM_SUC] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_ARITH `--(n * x) * (inv n * inv y):real =
                            --(n / n) * x / y`] THEN
    REWRITE_TAC[REAL_FIELD `--((&n + &1) / (&n + &1)) * x = --x`] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL; REAL_OF_NUM_MUL; REAL_OF_NUM_SUC] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 FACT)] THEN
    REWRITE_TAC[REAL_ARITH `a * --b + c:real = c - a * b`] THEN
    REWRITE_TAC[ADD1; GSYM real_div; SUM_DIFFS_ALT; LE_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 + 1 = n`; FACT] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
  REWRITE_TAC[REAL_EQ_ADD_LCANCEL] THEN
  REWRITE_TAC[REAL_ARITH `a * b / c:real = a / c * b`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
   `a * x / f - B * k * x = &0 ==> (B * k - a / f) * x = &0`)) THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_SUB_0] THEN
  ASM_CASES_TAC `x:real = t` THENL
   [ASM_MESON_TAC[IN_REAL_INTERVAL; REAL_LT_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM ADD1; FACT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD; ADD1] THEN
  SUBGOAL_THEN `~(&(FACT n) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ; FACT_NZ]; CONV_TAC REAL_FIELD]);;

let REAL_TAYLOR_MVT_NEG = prove
 (`!f a x n.
    x < a /\
    (!i t. t IN real_interval[x,a] /\ i <= n
           ==> ((f i) has_real_derivative f (i + 1) t)
               (atreal t within real_interval[x,a]))
    ==> ?t. t IN real_interval(x,a) /\
            f 0 x =
              sum (0..n) (\i. f i a * (x - a) pow i / &(FACT i)) +
              f (n + 1) t * (x - a) pow (n + 1) / &(FACT(n + 1))`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[REAL_NEG_NEG] `(?x:real. P x) <=> (?x. P(--x))`] THEN
  MP_TAC(SPECL [`\n x. (-- &1) pow n * (f:num->real->real) n (--x)`;
                `--a:real`; `  --x:real`; `n:num`]
        REAL_TAYLOR_MVT_POS) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(x * y) * z / w:real = y * (x * z) / w`] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_ARITH `-- &1 * (--x - --a) = x - a`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL; real_pow; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH `--a < t /\ t < --x <=> x < --t /\ --t < a`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_NEG2] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `t:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_ADD; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
  ONCE_REWRITE_TAC[REAL_ARITH `y pow 1 * x:real = x * y`] THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
    REAL_DIFF_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (--) (real_interval[--a,--x]) = real_interval[x,a]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_REAL_INTERVAL] THEN
    REWRITE_TAC[REAL_ARITH `x:real = --y <=> --x = y`; UNWIND_THM1] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let REAL_TAYLOR = prove
 (`!f n s B.
    is_realinterval s /\
    (!i x. x IN s /\ i <= n
           ==> ((f i) has_real_derivative f (i + 1) x) (atreal x within s)) /\
    (!x. x IN s ==> abs(f (n + 1) x) <= B)
    ==> !w z. w IN s /\ z IN s
              ==> abs(f 0 z -
                      sum (0..n) (\i. f i w * (z - w) pow i / &(FACT i)))
                  <= B * abs(z - w) pow (n + 1) / &(FACT(n + 1))`,
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `w = z \/ w < z \/ z < w`)
  THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; REAL_SUB_REFL; REAL_POW_ZERO;
                 REAL_ABS_0; ARITH; ADD_EQ_0; real_div] THEN
    REWRITE_TAC[REAL_MUL_LZERO; FACT; REAL_INV_1; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `y = &0 ==> abs(x - (x * &1 * &1 + y)) <= &0`) THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    SIMP_TAC[ARITH; LE_1; REAL_MUL_RZERO; REAL_MUL_LZERO];
    MP_TAC(ISPECL [`f:num->real->real`; `w:real`; `z:real`; `n:num`]
                  REAL_TAYLOR_MVT_POS) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `real_interval[w,z] SUBSET s` ASSUME_TAC THENL
     [SIMP_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[is_realinterval];
      ALL_TAC];
    MP_TAC(ISPECL [`f:num->real->real`; `w:real`; `z:real`; `n:num`]
                  REAL_TAYLOR_MVT_NEG) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `real_interval[z,w] SUBSET s` ASSUME_TAC THENL
     [SIMP_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[is_realinterval];
      ALL_TAC]] THEN
 (ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `t:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `s:real->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[REAL_ADD_SUB; REAL_ABS_MUL; REAL_ABS_DIV] THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_POW_LE; REAL_ABS_POS] THEN
  ASM_MESON_TAC[REAL_INTERVAL_OPEN_SUBSET_CLOSED; SUBSET]));;

(* ------------------------------------------------------------------------- *)
(* Comparing sums and "integrals" via real antiderivatives.                  *)
(* ------------------------------------------------------------------------- *)

let REAL_SUM_INTEGRAL_UBOUND_INCREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN real_interval[&m,&n + &1]
           ==> (g has_real_derivative f(x))
               (atreal x within real_interval[&m,&n + &1])) /\
      (!x y. &m <= x /\ x <= y /\ y <= &n + &1 ==> f x <= f y)
      ==> sum(m..n) (\k. f(&k)) <= g(&n + &1) - g(&m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(m..n) (\k. g(&(k + 1)) - g(&k))` THEN CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[SUM_DIFFS_ALT; REAL_OF_NUM_ADD; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real->real`; `f:real->real`; `&k`; `&(k + 1)`]
                REAL_MVT_SIMPLE) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `k < k + 1`] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_SUB] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[&m,&n + &1]` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL]);
      REWRITE_TAC[SUBSET] THEN GEN_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `t:real`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[REAL_MUL_RID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC]);;

let REAL_SUM_INTEGRAL_UBOUND_DECREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN real_interval[&m - &1,&n]
           ==> (g has_real_derivative f(x))
               (atreal x within real_interval[&m - &1,&n])) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n ==> f y <= f x)
      ==> sum(m..n) (\k. f(&k)) <= g(&n) - g(&m - &1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(m..n) (\k. g(&(k + 1) - &1) - g(&k - &1))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[SUM_DIFFS_ALT] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`] THEN
    REWRITE_TAC[REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real->real`; `f:real->real`; `&k - &1`; `&k`]
                REAL_MVT_SIMPLE) THEN
  ASM_REWRITE_TAC[REAL_ARITH `k - &1 < k`] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[&m - &1,&n]` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL]);
      REWRITE_TAC[SUBSET] THEN GEN_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(a + &1) - &1 = a`] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[REAL_ARITH `a * (x - (x - &1)) = a`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC]);;

let REAL_SUM_INTEGRAL_LBOUND_INCREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN real_interval[&m - &1,&n]
           ==> (g has_real_derivative f(x))
               (atreal x within real_interval[&m - &1,&n])) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n ==> f x <= f y)
      ==> g(&n) - g(&m - &1) <= sum(m..n) (\k. f(&k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. --((f:real->real) z)`;
                 `\z. --((g:real->real) z)`;
                 `m:num`; `n:num`] REAL_SUM_INTEGRAL_UBOUND_DECREASING) THEN
  REWRITE_TAC[RE_NEG; RE_SUB; SUM_NEG; REAL_LE_NEG2;
              REAL_ARITH `--x - --y:real = --(x - y)`] THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_NEG]);;

let REAL_SUM_INTEGRAL_LBOUND_DECREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN real_interval[&m,&n + &1]
           ==> (g has_real_derivative f(x))
               (atreal x within  real_interval[&m,&n + &1])) /\
      (!x y. &m <= x /\ x <= y /\ y <= &n + &1 ==> f y <= f x)
      ==> g(&n + &1) - g(&m) <= sum(m..n) (\k. f(&k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. --((f:real->real) z)`;
                 `\z. --((g:real->real) z)`;
                 `m:num`; `n:num`] REAL_SUM_INTEGRAL_UBOUND_INCREASING) THEN
  REWRITE_TAC[RE_NEG; RE_SUB; SUM_NEG; REAL_LE_NEG2;
              REAL_ARITH `--x - --y:real = --(x - y)`] THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_NEG]);;

let REAL_SUM_INTEGRAL_BOUNDS_INCREASING = prove
 (`!f g m n.
         m <= n /\
         (!x. x IN real_interval[&m - &1,&n + &1]
              ==> (g has_real_derivative f x)
                  (atreal x within real_interval[&m - &1,&n + &1])) /\
         (!x y. &m - &1 <= x /\ x <= y /\ y <= &n + &1 ==> f x <= f y)
         ==> g(&n) - g(&m - &1) <= sum(m..n) (\k. f(&k)) /\
             sum (m..n) (\k. f(&k)) <= g(&n + &1) - g(&m)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_SUM_INTEGRAL_LBOUND_INCREASING;
    MATCH_MP_TAC REAL_SUM_INTEGRAL_UBOUND_INCREASING] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `real_interval[&m - &1,&n + &1]` THEN CONJ_TAC) THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL])) THEN
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC);;

let REAL_SUM_INTEGRAL_BOUNDS_DECREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN real_interval[&m - &1,&n + &1]
           ==> (g has_real_derivative f(x))
               (atreal x within real_interval[&m - &1,&n + &1])) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n + &1 ==> f y <= f x)
      ==> g(&n + &1) - g(&m) <= sum(m..n) (\k. f(&k)) /\
          sum(m..n) (\k. f(&k)) <= g(&n) - g(&m - &1)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_SUM_INTEGRAL_LBOUND_DECREASING;
    MATCH_MP_TAC REAL_SUM_INTEGRAL_UBOUND_DECREASING] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `real_interval[&m - &1,&n + &1]` THEN CONJ_TAC) THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL])) THEN
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Relating different kinds of real limits.                                  *)
(* ------------------------------------------------------------------------- *)

let REALLIM_POSINFINITY_SEQUENTIALLY = prove
 (`!f l. (f ---> l) at_posinfinity ==> ((\n. f(&n)) ---> l) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_POSINFINITY_SEQUENTIALLY) THEN
  REWRITE_TAC[o_DEF]);;

let LIM_ZERO_POSINFINITY = prove
 (`!f l. ((\x. f(&1 / x)) --> l) (atreal (&0)) ==> (f --> l) at_posinfinity`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_ATREAL; LIM_AT_POSINFINITY] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[dist; REAL_SUB_RZERO; real_ge] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&2 / d` THEN X_GEN_TAC `z:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(z):real`) THEN
  REWRITE_TAC[real_div; REAL_MUL_LINV; REAL_INV_INV] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_ABS_INV; REAL_LT_INV_EQ] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `a <= z ==> &0 < a ==> &0 < abs z`));
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `&2 / d <= z ==> &0 < &2 / d ==> inv d < abs z`))] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH]);;

let LIM_ZERO_NEGINFINITY = prove
 (`!f l. ((\x. f(&1 / x)) --> l) (atreal (&0)) ==> (f --> l) at_neginfinity`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_ATREAL; LIM_AT_NEGINFINITY] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[dist; REAL_SUB_RZERO; real_ge] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `--(&2 / d)` THEN X_GEN_TAC `z:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(z):real`) THEN
  REWRITE_TAC[real_div; REAL_MUL_LINV; REAL_INV_INV] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_ABS_INV; REAL_LT_INV_EQ] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `z <= --a ==> &0 < a ==> &0 < abs z`));
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `z <= --(&2 / d) ==> &0 < &2 / d ==> inv d < abs z`))] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH]);;

let REALLIM_ZERO_POSINFINITY = prove
 (`!f l. ((\x. f(&1 / x)) ---> l) (atreal (&0)) ==> (f ---> l) at_posinfinity`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF; LIM_ZERO_POSINFINITY]);;

let REALLIM_ZERO_NEGINFINITY = prove
 (`!f l. ((\x. f(&1 / x)) ---> l) (atreal (&0)) ==> (f ---> l) at_neginfinity`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF; LIM_ZERO_NEGINFINITY]);;

(* ------------------------------------------------------------------------- *)
(* Real segments (bidirectional intervals).                                  *)
(* ------------------------------------------------------------------------- *)

let closed_real_segment = define
 `closed_real_segment[a,b] = {(&1 - u) * a + u * b | &0 <= u /\ u <= &1}`;;

let open_real_segment = new_definition
 `open_real_segment(a,b) = closed_real_segment[a,b] DIFF {a,b}`;;

make_overloadable "real_segment" `:A`;;

overload_interface("real_segment",`open_real_segment`);;
overload_interface("real_segment",`closed_real_segment`);;

let real_segment = prove
 (`real_segment[a,b] = {(&1 - u) * a + u * b | &0 <= u /\ u <= &1} /\
   real_segment(a,b) = real_segment[a,b] DIFF {a,b}`,
  REWRITE_TAC[open_real_segment; closed_real_segment]);;

let REAL_SEGMENT_SEGMENT = prove
 (`(!a b. real_segment[a,b] = IMAGE drop (segment[lift a,lift b])) /\
   (!a b. real_segment(a,b) = IMAGE drop (segment(lift a,lift b)))`,
  REWRITE_TAC[segment; real_segment] THEN
  SIMP_TAC[IMAGE_DIFF_INJ; DROP_EQ; IMAGE_CLAUSES; LIFT_DROP] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; DROP_ADD; DROP_CMUL; LIFT_DROP]);;

let SEGMENT_REAL_SEGMENT = prove
 (`(!a b. segment[a,b] = IMAGE lift (real_segment[drop a,drop b])) /\
   (!a b. segment(a,b) = IMAGE lift (real_segment(drop a,drop b)))`,
  REWRITE_TAC[REAL_SEGMENT_SEGMENT; GSYM IMAGE_o] THEN
  REWRITE_TAC[o_DEF; IMAGE_ID; LIFT_DROP]);;

let IMAGE_LIFT_REAL_SEGMENT = prove
 (`(!a b. IMAGE lift (real_segment[a,b]) = segment[lift a,lift b]) /\
   (!a b. IMAGE lift (real_segment(a,b)) = segment(lift a,lift b))`,
  REWRITE_TAC[SEGMENT_REAL_SEGMENT; LIFT_DROP]);;

let REAL_SEGMENT_INTERVAL = prove
 (`(!a b. real_segment[a,b] =
          if a <= b then real_interval[a,b] else real_interval[b,a]) /\
   (!a b. real_segment(a,b) =
          if a <= b then real_interval(a,b) else real_interval(b,a))`,
  REWRITE_TAC[REAL_SEGMENT_SEGMENT; SEGMENT_1; LIFT_DROP] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let REAL_CONTINUOUS_INJECTIVE_IFF_MONOTONIC = prove
 (`!f s.
        f real_continuous_on s /\ is_realinterval s
        ==> ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
             (!x y. x IN s /\ y IN s /\ x < y ==> f x < f y) \/
             (!x y. x IN s /\ y IN s /\ x < y ==> f y < f x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IS_REALINTERVAL_IS_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_INJECTIVE_IFF_MONOTONIC) THEN
  REWRITE_TAC[FORALL_LIFT; LIFT_IN_IMAGE_LIFT; o_THM; LIFT_DROP; LIFT_EQ]);;

let ENDS_IN_REAL_SEGMENT = prove
 (`!a b. a IN real_segment[a,b] /\ b IN real_segment[a,b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_SEGMENT_INTERVAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  ASM_REAL_ARITH_TAC);;

let IS_REAL_INTERVAL_CONTAINS_SEGMENT = prove
 (`!s. is_realinterval s <=>
       !a b. a IN s /\ b IN s ==> real_segment[a,b] SUBSET s`,
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT; IS_REALINTERVAL_CONVEX] THEN
  REWRITE_TAC[REAL_SEGMENT_SEGMENT; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE_LIFT_DROP]);;

let IS_REALINTERVAL_CONTAINS_SEGMENT_EQ = prove
 (`!s. is_realinterval s <=>
       !a b. real_segment [a,b] SUBSET s <=> a IN s /\ b IN s`,
  MESON_TAC[IS_REAL_INTERVAL_CONTAINS_SEGMENT;
            SUBSET; ENDS_IN_REAL_SEGMENT]);;

let IS_REALINTERVAL_CONTAINS_SEGMENT_IMP = prove
 (`!s a b. is_realinterval s
           ==> (real_segment [a,b] SUBSET s <=> a IN s /\ b IN s)`,
  MESON_TAC[IS_REALINTERVAL_CONTAINS_SEGMENT_EQ]);;

let IS_REALINTERVAL_SEGMENT = prove
 (`(!a b. is_realinterval(real_segment[a,b])) /\
   (!a b. is_realinterval(real_segment(a,b)))`,
  REWRITE_TAC[REAL_SEGMENT_INTERVAL] THEN
  MESON_TAC[IS_REALINTERVAL_INTERVAL]);;

let IN_REAL_SEGMENT = prove
 (`(!a b x. x IN real_segment[a,b] <=> a <= x /\ x <= b \/ b <= x /\ x <= a) /\
   (!a b x. x IN real_segment(a,b) <=> a < x /\ x < b \/ b < x /\ x < a)`,
  REWRITE_TAC[REAL_SEGMENT_INTERVAL] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Convex real->real functions.                                              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("real_convex_on",(12,"right"));;

let real_convex_on = new_definition
  `(f:real->real) real_convex_on s <=>
        !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
                  ==> f(u * x + v * y) <= u * f(x) + v * f(y)`;;

let REAL_CONVEX_ON = prove
 (`!f s. f real_convex_on s <=> (f o drop) convex_on (IMAGE lift s)`,
  REWRITE_TAC[real_convex_on; convex_on] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_THM; LIFT_DROP; DROP_ADD; DROP_CMUL]);;

let REAL_CONVEX_ON_SUBSET = prove
 (`!f s t. f real_convex_on t /\ s SUBSET t ==> f real_convex_on s`,
  REWRITE_TAC[REAL_CONVEX_ON] THEN
  MESON_TAC[CONVEX_ON_SUBSET; IMAGE_SUBSET]);;

let REAL_CONVEX_ADD = prove
 (`!s f g. f real_convex_on s /\ g real_convex_on s
           ==> (\x. f(x) + g(x)) real_convex_on s`,
  REWRITE_TAC[REAL_CONVEX_ON; o_DEF; CONVEX_ADD]);;

let REAL_CONVEX_LMUL = prove
 (`!s c f. &0 <= c /\ f real_convex_on s ==> (\x. c * f(x)) real_convex_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_CONVEX_ON; o_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONVEX_CMUL) THEN REWRITE_TAC[]);;

let REAL_CONVEX_RMUL = prove
 (`!s c f. &0 <= c /\ f real_convex_on s ==> (\x. f(x) * c) real_convex_on s`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_CONVEX_LMUL]);;

let REAL_CONVEX_CONVEX_COMPOSE = prove
 (`!f g s:real^N->bool t.
        f convex_on s /\ g real_convex_on t /\
        convex s /\ is_realinterval t /\ IMAGE f s SUBSET t /\
        (!x y. x IN t /\ y IN t /\ x <= y ==> g x <= g y)
        ==> (g o f) convex_on s`,
  REWRITE_TAC[convex_on; convex; IS_REALINTERVAL_CONVEX;
               real_convex_on; SUBSET] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; o_DEF] THEN
  REWRITE_TAC[IN_IMAGE_LIFT_DROP; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

let REAL_CONVEX_COMPOSE = prove
 (`!f g. f real_convex_on s /\ g real_convex_on t /\
         is_realinterval s /\ is_realinterval t /\ IMAGE f s SUBSET t /\
         (!x y. x IN t /\ y IN t /\ x <= y ==> g x <= g y)
        ==> (g o f) real_convex_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONVEX_ON; GSYM o_ASSOC] THEN
  MATCH_MP_TAC REAL_CONVEX_CONVEX_COMPOSE THEN EXISTS_TAC `t:real->bool` THEN
  ASM_REWRITE_TAC[GSYM REAL_CONVEX_ON; GSYM IMAGE_o; o_DEF; LIFT_DROP;
                  ETA_AX; GSYM IS_REALINTERVAL_CONVEX]);;

let REAL_CONVEX_LOWER = prove
 (`!f s x y. f real_convex_on s /\
             x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ u + v = &1
             ==> f(u * x + v * y) <= max (f(x)) (f(y))`,
  REWRITE_TAC[REAL_CONVEX_ON] THEN
  REWRITE_TAC[FORALL_DROP; GSYM IN_IMAGE_LIFT_DROP] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CONVEX_LOWER) THEN
  REWRITE_TAC[o_THM; DROP_ADD; DROP_CMUL]);;

let REAL_CONVEX_LOCAL_GLOBAL_MINIMUM = prove
 (`!f s t x.
       f real_convex_on s /\ x IN t /\ real_open t /\ t SUBSET s /\
       (!y. y IN t ==> f(x) <= f(y))
       ==> !y. y IN s ==> f(x) <= f(y)`,
  REWRITE_TAC[REAL_CONVEX_ON; REAL_OPEN] THEN
  REWRITE_TAC[FORALL_DROP; GSYM IN_IMAGE_LIFT_DROP] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(f:real->real) o drop`; `IMAGE lift s`;
                 `IMAGE lift t`; `x:real^1`] CONVEX_LOCAL_GLOBAL_MINIMUM) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_THM; IMAGE_SUBSET]);;

let REAL_CONVEX_DISTANCE = prove
 (`!s a. (\x. abs(a - x)) real_convex_on s`,
  REWRITE_TAC[REAL_CONVEX_ON; o_DEF; FORALL_DROP; GSYM DROP_SUB] THEN
  REWRITE_TAC[drop; GSYM NORM_REAL; GSYM dist; CONVEX_DISTANCE]);;

let REAL_CONVEX_ON_JENSEN = prove
 (`!f s. is_realinterval s
         ==> (f real_convex_on s <=>
                !k u x.
                   (!i:num. 1 <= i /\ i <= k ==> &0 <= u(i) /\ x(i) IN s) /\
                   (sum (1..k) u = &1)
                   ==> f(sum (1..k) (\i. u(i) * x(i)))
                           <= sum (1..k) (\i. u(i) * f(x(i))))`,
  REWRITE_TAC[IS_REALINTERVAL_CONVEX; REAL_CONVEX_ON] THEN
  SIMP_TAC[CONVEX_ON_JENSEN] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[o_DEF; DROP_VSUM; FINITE_NUMSEG] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `u:num->real` THEN REWRITE_TAC[] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `x:num->real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift o (x:num->real)`) THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; IN_IMAGE_LIFT_DROP] THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP];
    X_GEN_TAC `x:num->real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop o (x:num->real^1)`) THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; IN_IMAGE_LIFT_DROP] THEN
    ASM_REWRITE_TAC[DROP_CMUL; LIFT_DROP; GSYM IN_IMAGE_LIFT_DROP]]);;

let REAL_CONVEX_ON_IMP_JENSEN = prove
 (`!f s k:A->bool u x.
        f real_convex_on s /\ is_realinterval s /\ FINITE k /\
        (!i. i IN k ==> &0 <= u i /\ x i IN s) /\ sum k u = &1
        ==> f(sum k (\i. u i * x i)) <= sum k (\i. u i * f(x i))`,
  REWRITE_TAC[REAL_CONVEX_ON; IS_REALINTERVAL_IS_INTERVAL] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
   SPECL [`k:A->bool`; `u:A->real`; `\i:A. lift(x i)`] o
   MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] CONVEX_ON_IMP_JENSEN)) THEN
  ASM_REWRITE_TAC[LIFT_IN_IMAGE_LIFT; o_DEF; LIFT_DROP; DROP_VSUM; DROP_CMUL;
                  GSYM IS_INTERVAL_CONVEX_1]);;

let REAL_CONVEX_ON_CONTINUOUS = prove
 (`!f s. real_open s /\ f real_convex_on s ==> f real_continuous_on s`,
  REWRITE_TAC[REAL_CONVEX_ON; REAL_OPEN; REAL_CONTINUOUS_ON] THEN
  REWRITE_TAC[CONVEX_ON_CONTINUOUS]);;

let REAL_CONVEX_ON_LEFT_SECANT_MUL = prove
 (`!f s. f real_convex_on s <=>
          !a b x. a IN s /\ b IN s /\ x IN real_segment[a,b]
                  ==> (f x - f a) * abs(b - a) <= (f b - f a) * abs(x - a)`,
  REWRITE_TAC[REAL_CONVEX_ON; CONVEX_ON_LEFT_SECANT_MUL] THEN
  REWRITE_TAC[REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_RIGHT_SECANT_MUL = prove
 (`!f s. f real_convex_on s <=>
          !a b x. a IN s /\ b IN s /\ x IN real_segment[a,b]
                  ==> (f b - f a) * abs(b - x) <= (f b - f x) * abs(b - a)`,
  REWRITE_TAC[REAL_CONVEX_ON; CONVEX_ON_RIGHT_SECANT_MUL] THEN
  REWRITE_TAC[REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_LEFT_SECANT = prove
 (`!f s.
      f real_convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN real_segment(a,b)
                ==> (f x - f a) / abs(x - a) <= (f b - f a) / abs(b - a)`,
  REWRITE_TAC[REAL_CONVEX_ON; CONVEX_ON_LEFT_SECANT] THEN
  REWRITE_TAC[REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_RIGHT_SECANT = prove
 (`!f s.
      f real_convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN real_segment(a,b)
                ==> (f b - f a) / abs(b - a) <= (f b - f x) / abs(b - x)`,
  REWRITE_TAC[REAL_CONVEX_ON; CONVEX_ON_RIGHT_SECANT] THEN
  REWRITE_TAC[REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_DERIVATIVE_SECANT_IMP = prove
 (`!f f' s x y.
        f real_convex_on s /\ real_segment[x,y] SUBSET s /\
        (f has_real_derivative f') (atreal x within s)
        ==> f' * (y - x) <= f y - f x`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN;
              REAL_CONVEX_ON; REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE_LIFT_DROP] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_DROP] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  REWRITE_TAC[GSYM IN_IMAGE_LIFT_DROP; GSYM SUBSET] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[LIFT_DROP]
        `\x. lift(drop(f % x))`)] THEN
  REWRITE_TAC[GSYM o_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONVEX_ON_DERIVATIVE_SECANT_IMP) THEN
  REWRITE_TAC[o_THM; DROP_CMUL; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_SECANT_DERIVATIVE_IMP = prove
 (`!f f' s x y.
        f real_convex_on s /\ real_segment[x,y] SUBSET s /\
        (f has_real_derivative f') (atreal y within s)
        ==> f y - f x <= f' * (y - x)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN;
              REAL_CONVEX_ON; REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE_LIFT_DROP] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_DROP] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  REWRITE_TAC[GSYM IN_IMAGE_LIFT_DROP; GSYM SUBSET] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[LIFT_DROP]
        `\x. lift(drop(f % x))`)] THEN
  REWRITE_TAC[GSYM o_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONVEX_ON_SECANT_DERIVATIVE_IMP) THEN
  REWRITE_TAC[o_THM; DROP_CMUL; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_DERIVATIVES_IMP = prove
 (`!f f'x f'y s x y.
        f real_convex_on s /\ real_segment[x,y] SUBSET s /\
        (f has_real_derivative f'x) (atreal x within s) /\
        (f has_real_derivative f'y) (atreal y within s)
        ==> f'x * (y - x) <= f'y * (y - x)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN;
              REAL_CONVEX_ON; REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE_LIFT_DROP] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_DROP] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  REWRITE_TAC[GSYM IN_IMAGE_LIFT_DROP; GSYM SUBSET] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[LIFT_DROP]
        `\x. lift(drop(f % x))`)] THEN
  REWRITE_TAC[GSYM o_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONVEX_ON_DERIVATIVES_IMP) THEN
  REWRITE_TAC[o_THM; DROP_CMUL; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_DERIVATIVE_INCREASING_IMP = prove
 (`!f f'x f'y s x y.
        f real_convex_on s /\ real_interval[x,y] SUBSET s /\
        (f has_real_derivative f'x) (atreal x within s) /\
        (f has_real_derivative f'y) (atreal y within s) /\
        x < y
        ==> f'x <= f'y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `f'x:real`; `f'y:real`; `s:real->bool`;
                 `x:real`; `y:real`] REAL_CONVEX_ON_DERIVATIVES_IMP) THEN
  ASM_REWRITE_TAC[REAL_SEGMENT_INTERVAL] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_RMUL_EQ; REAL_SUB_LT]);;

let REAL_CONVEX_ON_DERIVATIVE_SECANT = prove
 (`!f f' s.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s))
        ==> (f real_convex_on s <=>
             !x y. x IN s /\ y IN s ==> f'(x) * (y - x) <= f y - f x)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN;
              REAL_CONVEX_ON; IS_REALINTERVAL_CONVEX] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FORALL_DROP; GSYM IN_IMAGE_LIFT_DROP; LIFT_DROP] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[LIFT_DROP; o_DEF]
        `lift o (\x. drop(f % x))`)] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP CONVEX_ON_DERIVATIVE_SECANT) THEN
  REWRITE_TAC[DROP_CMUL; DROP_SUB; o_THM]);;

let REAL_CONVEX_ON_SECANT_DERIVATIVE = prove
 (`!f f' s.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s))
        ==> (f real_convex_on s <=>
             !x y. x IN s /\ y IN s ==> f y - f x <= f'(y) * (y - x))`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN;
              REAL_CONVEX_ON; IS_REALINTERVAL_CONVEX] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FORALL_DROP; GSYM IN_IMAGE_LIFT_DROP; LIFT_DROP] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[LIFT_DROP; o_DEF]
        `lift o (\x. drop(f % x))`)] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP CONVEX_ON_SECANT_DERIVATIVE) THEN
  REWRITE_TAC[DROP_CMUL; DROP_SUB; o_THM]);;

let REAL_CONVEX_ON_DERIVATIVES = prove
 (`!f f' s.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s))
        ==> (f real_convex_on s <=>
             !x y. x IN s /\ y IN s ==> f'(x) * (y - x) <= f'(y) * (y - x))`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN;
              REAL_CONVEX_ON; IS_REALINTERVAL_CONVEX] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FORALL_DROP; GSYM IN_IMAGE_LIFT_DROP; LIFT_DROP] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[LIFT_DROP; o_DEF]
        `lift o (\x. drop(f % x))`)] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP CONVEX_ON_DERIVATIVES) THEN
  REWRITE_TAC[DROP_CMUL; DROP_SUB; o_THM]);;

let REAL_CONVEX_ON_DERIVATIVE_INCREASING = prove
 (`!f f' s.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s))
        ==> (f real_convex_on s <=>
             !x y. x IN s /\ y IN s /\ x <= y ==> f'(x) <= f'(y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_CONVEX_ON_DERIVATIVES) THEN
  EQ_TAC THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
    ASM_CASES_TAC `x:real = y` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_SUB_LT; REAL_LT_LE];
    DISJ_CASES_TAC(REAL_ARITH `x <= y \/ y <= x`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real`; `x:real`])] THEN
    ASM_CASES_TAC `x:real = y` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_SUB_LT; REAL_LT_LE] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `a * (y - x) <= b * (y - x) <=> b * (x - y) <= a * (x - y)`] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_SUB_LT; REAL_LT_LE]]);;

let HAS_REAL_DERIVATIVE_INCREASING_IMP = prove
 (`!f f' s a b.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s)) /\
        (!x. x IN s ==> &0 <= f'(x)) /\
        a IN s /\ b IN s /\ a <= b
        ==> f(a) <= f(b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[a,b] SUBSET s` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [is_realinterval]) THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `a:real`; `b:real`]
    REAL_MVT_VERY_SIMPLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `s:real->bool` THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `z:real` MP_TAC) THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [GSYM REAL_SUB_LE] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]]);;

let HAS_REAL_DERIVATIVE_INCREASING = prove
 (`!f f' s. is_realinterval s /\ ~(?a. s = {a}) /\
           (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s))
           ==> ((!x. x IN s ==> &0 <= f'(x)) <=>
                (!x y. x IN s /\ y IN s /\ x <= y ==> f(x) <= f(y)))`,
  REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[HAS_REAL_DERIVATIVE_INCREASING_IMP]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `atreal x within s` REALLIM_LBOUND) THEN
  EXISTS_TAC `\y:real. (f y - f x) / (y - x)` THEN
  ASM_SIMP_TAC[GSYM HAS_REAL_DERIVATIVE_WITHINREAL] THEN
  ASM_SIMP_TAC[TRIVIAL_LIMIT_WITHIN_REALINTERVAL] THEN
  REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  X_GEN_TAC `y:real` THEN
  REWRITE_TAC[REAL_ARITH `&0 < abs(y - x) <=> ~(y = x)`] THEN STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `~(y:real = x) ==> x < y \/ y < x`))
  THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
    REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
    REWRITE_TAC[REAL_NEG_NEG; GSYM real_div]] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN
  ASM_SIMP_TAC[REAL_SUB_LE; REAL_LT_IMP_LE]);;

let HAS_REAL_DERIVATIVE_STRICTLY_INCREASING_IMP = prove
 (`!f f' a b.
        (!x. x IN real_interval[a,b]
             ==> (f has_real_derivative f'(x))

                 (atreal x within real_interval[a,b])) /\
        (!x. x IN real_interval(a,b) ==> &0 < f'(x)) /\
        a < b
        ==> f(a) < f(b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `a:real`; `b:real`]
        REAL_MVT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_SUB_LT; REAL_LT_MUL]] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON;
                  real_differentiable_on];
    ASM_MESON_TAC[HAS_REAL_DERIVATIVE_WITHIN_SUBSET; SUBSET;
                  REAL_INTERVAL_OPEN_SUBSET_CLOSED; REAL_OPEN_REAL_INTERVAL;
                  HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN]]);;

let REAL_CONVEX_ON_SECOND_DERIVATIVE = prove
 (`!f f' f'' s.
        is_realinterval s /\ ~(?a. s = {a}) /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s)) /\
        (!x. x IN s ==> (f' has_real_derivative f''(x)) (atreal x within s))
        ==> (f real_convex_on s <=> !x. x IN s ==> &0 <= f''(x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `!x y. x IN s /\ y IN s /\ x <= y ==> (f':real->real)(x) <= f'(y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONVEX_ON_DERIVATIVE_INCREASING;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_INCREASING] THEN
  ASM_REWRITE_TAC[]);;

let REAL_CONVEX_ON_ASYM = prove
 (`!s f. f real_convex_on s <=>
         !x y u v.
                x IN s /\ y IN s /\ x < y /\ &0 <= u /\ &0 <= v /\ u + v = &1
                ==> f (u * x + v * y) <= u * f x + v * f y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_convex_on] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC REAL_WLOG_LT THEN
  SIMP_TAC[GSYM REAL_ADD_RDISTRIB; REAL_MUL_LID; REAL_LE_REFL] THEN
  ASM_MESON_TAC[REAL_ADD_SYM]);;

let REAL_CONVEX_ON_EXP = prove
 (`!s. exp real_convex_on s`,
  GEN_TAC THEN MATCH_MP_TAC REAL_CONVEX_ON_SUBSET THEN
  EXISTS_TAC `(:real)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
  MP_TAC(ISPECL [`exp`; `exp`; `exp`; `(:real)`]
     REAL_CONVEX_ON_SECOND_DERIVATIVE) THEN
  SIMP_TAC[HAS_REAL_DERIVATIVE_EXP; REAL_EXP_POS_LE;
           HAS_REAL_DERIVATIVE_ATREAL_WITHIN; IS_REALINTERVAL_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `&0 IN s /\ &1 IN s /\ ~(&1 = &0) ==> ~(?a. s = {a})`) THEN
  REWRITE_TAC[IN_UNIV] THEN REAL_ARITH_TAC);;

let REAL_CONVEX_ON_RPOW = prove
 (`!s t. s SUBSET {x | &0 <= x} /\ &1 <= t
         ==> (\x. x rpow t) real_convex_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONVEX_ON_SUBSET THEN
  EXISTS_TAC `{x | &0 <= x}` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. x rpow t) real_convex_on {x | &0 < x}` MP_TAC THENL
   [MP_TAC(ISPECL
     [`\x. x rpow t`; `\x. t * x rpow (t - &1)`;
      `\x. t * (t - &1) * x rpow (t - &2)`; `{x | &0 < x}`]
        REAL_CONVEX_ON_SECOND_DERIVATIVE) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(SET_RULE
         `&1 IN s /\ &2 IN s /\ ~(&1 = &2) ==> ~(?a. s = {a})`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
        ASM_REWRITE_TAC[REAL_ARITH `t - &1 - &1 = t - &2`] THEN
        ASM_REAL_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN REPEAT STRIP_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      MATCH_MP_TAC RPOW_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    REWRITE_TAC[REAL_CONVEX_ON_ASYM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_CASES_TAC `x = &0` THENL
     [DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[RPOW_ZERO; REAL_ARITH `&1 <= t ==> ~(t = &0)`] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
      ASM_CASES_TAC `v = &0` THEN
      ASM_SIMP_TAC[RPOW_ZERO; REAL_ARITH `&1 <= t ==> ~(t = &0)`;
                   REAL_MUL_LZERO; REAL_LE_REFL] THEN
      ASM_SIMP_TAC[RPOW_MUL; REAL_LT_LE] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE] THEN
       MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&1 * log v)` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[rpow; REAL_LT_LE; REAL_EXP_MONO_LE] THEN
        ONCE_REWRITE_TAC[REAL_ARITH
         `a * l <= b * l <=> --l * b <= --l * a`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GSYM LOG_INV; REAL_LT_LE] THEN MATCH_MP_TAC LOG_POS THEN
        MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_MUL_LID; EXP_LOG; REAL_LT_LE; REAL_LE_REFL]];
      ASM_MESON_TAC[REAL_LT_LE; REAL_LET_TRANS]]]);;

let REAL_CONVEX_ON_LOG = prove
 (`!s. s SUBSET {x | &0 < x} ==> (\x. --log x) real_convex_on s`,
  GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_CONVEX_ON_SUBSET) THEN
  MP_TAC(ISPECL [`\x. --log x`; `\x:real. --inv(x)`; `\x:real. inv(x pow 2)`;
                 `{x | &0 < x}`]
        REAL_CONVEX_ON_SECOND_DERIVATIVE) THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    MESON_TAC[REAL_ARITH `&0 < a ==> &0 < a + &1 /\ ~(a + &1 = a)`];
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN ASM_REAL_ARITH_TAC]);;

let REAL_CONTINUOUS_MIDPOINT_CONVEX = prove
 (`!f s. f real_continuous_on s /\ is_realinterval s /\
         (!x y. x IN s /\ y IN s ==> f ((x + y) / &2) <= (f x + f y) / &2)
         ==> f real_convex_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONVEX_ON] THEN
  MATCH_MP_TAC CONTINUOUS_MIDPOINT_CONVEX THEN
  ASM_REWRITE_TAC[GSYM REAL_CONTINUOUS_ON; GSYM IS_REALINTERVAL_CONVEX] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[midpoint; LIFT_DROP; o_THM; DROP_CMUL; DROP_ADD] THEN
  ASM_SIMP_TAC[REAL_ARITH `inv(&2) * x = x / &2`]);;

(* ------------------------------------------------------------------------- *)
(* Some convexity-derived inequalities including AGM and Young's inequality. *)
(* ------------------------------------------------------------------------- *)

let AGM_GEN = prove
 (`!a x k:A->bool.
        FINITE k /\ sum k a = &1 /\ (!i. i IN k ==> &0 <= a i /\ &0 <= x i)
        ==> product k (\i. x i rpow a i) <= sum k (\i. a i * x i)`,
  let version1 = prove
   (`!a x k:A->bool.
          FINITE k /\ sum k a = &1 /\ (!i. i IN k ==> &0 < a i /\ &0 < x i)
          ==> product k (\i. x i rpow a i) <= sum k (\i. a i * x i)`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `k:A->bool = {}` THEN
    ASM_REWRITE_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH_EQ] THEN STRIP_TAC THEN
    MATCH_MP_TAC LOG_MONO_LE_REV THEN
    ASM_SIMP_TAC[PRODUCT_POS_LT; RPOW_POS_LT; LOG_PRODUCT; LOG_RPOW;
                 SUM_POS_LT_ALL; REAL_LT_MUL] THEN
    MP_TAC(ISPECL [`\x. --log x`; `{x | &0 < x}`; `k:A->bool`; `a:A->real`;
                   `x:A->real`] REAL_CONVEX_ON_IMP_JENSEN) THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_CONVEX_ON_LOG; SUBSET_REFL; REAL_LT_IMP_LE;
                 is_realinterval] THEN
    REWRITE_TAC[REAL_MUL_RNEG; SUM_NEG; REAL_LE_NEG2] THEN
    DISCH_THEN MATCH_MP_TAC THEN REAL_ARITH_TAC) in
  let version2 = prove
   (`!a x k:A->bool.
          FINITE k /\ sum k a = &1 /\ (!i. i IN k ==> &0 < a i /\ &0 <= x i)
          ==> product k (\i. x i rpow a i) <= sum k (\i. a i * x i)`,
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `?i:A. i IN k /\ x i = &0` THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x = &0 ==> x <= y`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
        ASM_SIMP_TAC[PRODUCT_EQ_0; RPOW_EQ_0] THEN
        ASM_MESON_TAC[REAL_LT_IMP_NZ]];
      MATCH_MP_TAC version1 THEN ASM_MESON_TAC[REAL_LT_LE]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `product {i:A | i IN k /\ ~(a i = &0)} (\i. x i rpow a i)
    <= sum {i:A | i IN k /\ ~(a i = &0)} (\i. a i * x i)`
  MP_TAC THENL
   [MATCH_MP_TAC version2 THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; REAL_LT_LE; IN_ELIM_THM] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM SUM_SUPPORT] THEN
    REWRITE_TAC[support; NEUTRAL_REAL_ADD];
    MATCH_MP_TAC EQ_IMP THEN CONV_TAC SYM_CONV THEN BINOP_TAC THENL
     [MATCH_MP_TAC PRODUCT_SUPERSET;
      MATCH_MP_TAC SUM_SUPERSET] THEN
    SIMP_TAC[IN_ELIM_THM; SUBSET_RESTRICT; IMP_CONJ; RPOW_0] THEN
    REWRITE_TAC[REAL_MUL_LZERO]]);;

let AGM_RPOW = prove
 (`!k:A->bool x n.
        k HAS_SIZE n /\ ~(n = 0) /\ (!i. i IN k ==> &0 <= x(i))
        ==> product k (\i. x(i) rpow (&1 / &n)) <= sum k (\i. x(i) / &n)`,
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\i:A. &1 / &n`; `x:A->real`; `k:A->bool`]
        AGM_GEN) THEN
  ASM_SIMP_TAC[SUM_CONST; REAL_LE_DIV; REAL_OF_NUM_LT; LE_1; ARITH;
               REAL_DIV_LMUL; REAL_OF_NUM_EQ; REAL_POS] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_AC]);;

let AGM_ROOT = prove
 (`!k:A->bool x n.
        k HAS_SIZE n /\ ~(n = 0) /\ (!i. i IN k ==> &0 <= x(i))
        ==> root n (product k x) <= sum k x / &n`,
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ROOT_PRODUCT; real_div; GSYM SUM_RMUL] THEN
  ASM_SIMP_TAC[REAL_ROOT_RPOW; GSYM real_div] THEN
  REWRITE_TAC[REAL_ARITH `inv(x) = &1 / x`] THEN
  MATCH_MP_TAC AGM_RPOW THEN ASM_REWRITE_TAC[HAS_SIZE]);;

let AGM_SQRT = prove
 (`!x y. &0 <= x /\ &0 <= y ==> sqrt(x * y) <= (x + y) / &2`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPECL [`{0,1}`; `\n. if n = 0 then (x:real) else y`; `2`] AGM_ROOT) THEN
  SIMP_TAC[SUM_CLAUSES; PRODUCT_CLAUSES; FINITE_RULES] THEN
  REWRITE_TAC[ARITH_EQ; IN_INSERT; NOT_IN_EMPTY;
              HAS_SIZE_CONV`s HAS_SIZE 2 `] THEN
  ASM_SIMP_TAC[ROOT_2; REAL_MUL_RID; REAL_ADD_RID;
               REAL_ARITH `x / &2 + y / &2 = (x + y) / &2`] THEN
  ASM_MESON_TAC[ARITH_RULE `~(1 = 0)`]);;

let AGM = prove
 (`!k:A->bool x n.
        k HAS_SIZE n /\ ~(n = 0) /\ (!i. i IN k ==> &0 <= x(i))
        ==> product k x <= (sum k x / &n) pow n`,
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `root n (product (k:A->bool) x) pow n` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_ROOT; PRODUCT_POS_LE; REAL_LE_REFL];
    MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[AGM_ROOT; HAS_SIZE; ROOT_LE_0; PRODUCT_POS_LE]]);;

let AGM_2 = prove
 (`!x y u v.
        &0 <= x /\ &0 <= y /\ &0 <= u /\ &0 <= v /\ u + v = &1
        ==> x rpow u * y rpow v <= u * x + v * y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\i. if i = 0 then u:real else v`;
                 `\i. if i = 0 then x:real else y`; `0..SUC 0`]
        AGM_GEN) THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; PRODUCT_CLAUSES_NUMSEG; ARITH] THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ASM_MESON_TAC[]);;

let YOUNG_INEQUALITY = prove
 (`!a b p q. &0 <= a /\ &0 <= b /\ &0 < p /\ &0 < q /\ inv(p) + inv(q) = &1
             ==> a * b <= a rpow p / p + b rpow q / q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a rpow p`; `b rpow q`; `inv p:real`; `inv q:real`]
        AGM_2) THEN
  ASM_SIMP_TAC[RPOW_RPOW; RPOW_POS_LE; REAL_LE_INV_EQ; REAL_LT_IMP_LE;
               REAL_MUL_RINV; RPOW_POW; REAL_POW_1; REAL_LT_IMP_NZ] THEN
  REAL_ARITH_TAC);;

let HOELDER = prove
 (`!k:A->bool a x y.
        FINITE k /\ sum k a = &1 /\
        (!i. i IN k ==> &0 <= a i /\ &0 <= x i /\ &0 <= y i)
        ==> product k (\i. x i rpow a i) + product k (\i. y i rpow a i)
            <= product k (\i. (x i + y i) rpow a i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= product (k:A->bool) (\i. (x i + y i) rpow a i)`
  MP_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[REAL_LE_ADD; RPOW_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
  ASM_SIMP_TAC[PRODUCT_EQ_0; RPOW_EQ_0; TAUT `p /\ q <=> ~(p ==> ~q)`;
   REAL_ARITH `&0 <= x /\ &0 <= y ==> (x + y = &0 <=> x = &0 /\ y = &0)`] THEN
  REWRITE_TAC[NOT_IMP] THEN STRIP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `x = &0 /\ y = &0 /\ z = &0 ==> x + y <= z`) THEN
    ASM_SIMP_TAC[PRODUCT_EQ_0; RPOW_EQ_0] THEN ASM_MESON_TAC[REAL_ADD_LID];
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID]] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM PRODUCT_DIV; GSYM RPOW_DIV;
               REAL_ARITH `(x + y) / z:real = x / z + y / z`] THEN
  ASM_SIMP_TAC[GSYM RPOW_PRODUCT] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum k (\i:A. a i * (x i / (x i + y i))) +
    sum k (\i. a i * (y i / (x i + y i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC AGM_GEN THEN
    ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_DIV];
    ASM_SIMP_TAC[GSYM SUM_ADD]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `s = &1 ==> p = s ==> p <= &1`)) THEN
  MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(a:A->real) i = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
  ASM_SIMP_TAC[PRODUCT_EQ_0; RPOW_EQ_0; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Some other inequalities where it's handy just to use calculus.            *)
(* ------------------------------------------------------------------------- *)

let RPOW_MINUS1_QUOTIENT_LT = prove
 (`!a x y. &0 < a /\ ~(a = &1) /\ &0 < x /\ x < y
           ==> (a rpow x - &1) / x < (a rpow y - &1) / y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (a rpow x - &1) / x`;
                 `\x. log a * a rpow x / x - (a rpow x - &1) / x pow 2`;
                 `x:real`; `y:real`]
   HAS_REAL_DERIVATIVE_STRICTLY_INCREASING_IMP) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[rpow] THEN REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  X_GEN_TAC `z:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
  EXISTS_TAC `(z:real) pow 2` THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_MUL_RZERO; REAL_FIELD
   `&0 < x ==> x pow 2 * (a * b / x - c / x pow 2) = a * b * x - c`] THEN
  REWRITE_TAC[REAL_ARITH `l * a * z - (a - &1) = a * (l * z - &1) + &1`] THEN
  MP_TAC(ISPECL [`\x. a rpow x * (log a * x - &1) + &1`;
                 `\x. log(a) pow 2 * x * a rpow x`;
                 `&0`; `z:real`]
   HAS_REAL_DERIVATIVE_STRICTLY_INCREASING_IMP) THEN
  ASM_REWRITE_TAC[RPOW_0] THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[RPOW_POS_LT; REAL_LT_POW_2] THEN
    ASM_SIMP_TAC[GSYM LOG_1; LOG_INJ; REAL_LT_01]]);;

let RPOW_MINUS1_QUOTIENT_LE = prove
 (`!a x y. &0 < a /\ &0 < x /\ x <= y
           ==> (a rpow x - &1) / x <= (a rpow y - &1) / y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:real = y` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_CASES_TAC `a = &1` THEN
  ASM_REWRITE_TAC[real_div; RPOW_ONE; REAL_SUB_REFL; REAL_MUL_LZERO;
                  REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_LE_LT; GSYM real_div; RPOW_MINUS1_QUOTIENT_LT]);;

let REAL_EXP_LIMIT_RPOW_LT = prove
 (`!x r s. &0 < r /\ r < s /\ ~(x = &0) /\ x < r
           ==> (&1 - x / r) rpow r < (&1 - x / s) rpow s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - x / s` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(&1 - x / s) rpow (inv r)`; `r:real`; `s:real`]
        RPOW_MINUS1_QUOTIENT_LT) THEN
  ASM_SIMP_TAC[RPOW_RPOW; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LT_IMP_LE;
               RPOW_POW; REAL_POW_1; RPOW_POS_LT] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[rpow; GSYM REAL_EXP_0; REAL_EXP_INJ] THEN
    ASM_SIMP_TAC[REAL_ENTIRE; REAL_INV_EQ_0; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[REAL_EXP_0] THEN
    ASM_SIMP_TAC[GSYM LOG_1; LOG_INJ; REAL_LT_01] THEN
    REWRITE_TAC[REAL_ARITH `a - x = a <=> x = &0`; REAL_DIV_EQ_0] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `(&1 - x / s - &1) / r = --(x / r) / s`] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_ARITH
      `--x < a - &1 <=> &1 - x < a`] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real` o MATCH_MP(MESON[RPOW_LT2]
     `x < y ==> !z. &0 <= x /\ &0 < z ==> x rpow z < y rpow z`)) THEN
    ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE; REAL_FIELD
     `&0 < r ==> (inv r * s) * r = s`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let REAL_EXP_LIMIT_RPOW_LE = prove
 (`!x r s. &0 <= r /\ r <= s /\ x <= r
           ==> (&1 - x / r) rpow r <= (&1 - x / s) rpow s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_SUB_RZERO; RPOW_ONE];
    ALL_TAC] THEN
  ASM_CASES_TAC `r:real = s` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_CASES_TAC `r:real = x` THENL
   [ASM_SIMP_TAC[REAL_DIV_REFL; REAL_SUB_REFL; RPOW_ZERO] THEN
    STRIP_TAC THEN MATCH_MP_TAC RPOW_POS_LE THEN
    REWRITE_TAC[REAL_SUB_LE] THEN
    SUBGOAL_THEN `&0 < s` (fun th -> SIMP_TAC[th; REAL_LE_LDIV_EQ]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r = &0` THEN
  ASM_SIMP_TAC[REAL_LE_LT; REAL_EXP_LIMIT_RPOW_LT] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_LT; RPOW_POW; real_pow] THEN
  ASM_SIMP_TAC[rpow; REAL_SUB_LT; REAL_LT_LDIV_EQ] THEN COND_CASES_TAC THENL
   [ALL_TAC; MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC LOG_POS THEN
  REWRITE_TAC[REAL_ARITH `&1 <= &1 - x / y <=> &0 <= --x / y`] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC);;

let REAL_LE_X_SINH = prove
 (`!x. &0 <= x ==> x <= (exp x - inv(exp x)) / &2`,
  SUBGOAL_THEN
   `!a b. a <= b
          ==> exp a - inv(exp a) - &2 * a <= exp b - inv(exp b) - &2 * b`
   (MP_TAC o SPEC `&0`)
  THENL
   [MP_TAC(ISPECL
     [`\x. exp x - exp(--x) - &2 * x`; `\x. exp x + exp(--x) - &2`; `(:real)`]
     HAS_REAL_DERIVATIVE_INCREASING) THEN
    REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_UNIV; IN_UNIV] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [SET_TAC[REAL_ARITH `~(&1 = &0)`]; ALL_TAC] THEN
      GEN_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      SIMP_TAC[REAL_EXP_NEG] THEN DISCH_THEN(fun th -> SIMP_TAC[GSYM th]) THEN
      X_GEN_TAC `x:real` THEN
      SIMP_TAC[REAL_EXP_NZ; REAL_FIELD
       `~(e = &0) ==> e + inv e - &2 = (e - &1) pow 2 / e`] THEN
      SIMP_TAC[REAL_EXP_POS_LE; REAL_LE_DIV; REAL_LE_POW_2]];
    MATCH_MP_TAC MONO_FORALL THEN REWRITE_TAC[REAL_EXP_0] THEN
    REAL_ARITH_TAC]);;

let REAL_LE_ABS_SINH = prove
 (`!x. abs x <= abs((exp x - inv(exp x)) / &2)`,
  GEN_TAC THEN ASM_CASES_TAC `&0 <= x` THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= abs y`) THEN
    ASM_SIMP_TAC[REAL_LE_X_SINH];
    MATCH_MP_TAC(REAL_ARITH `~(&0 <= x) /\ --x <= --y ==> abs x <= abs y`) THEN
    ASM_REWRITE_TAC[REAL_ARITH `--((a - b) / &2) = (b - a) / &2`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(exp(--x) - inv(exp(--x))) / &2` THEN
    ASM_SIMP_TAC[REAL_LE_X_SINH; REAL_ARITH `~(&0 <= x) ==> &0 <= --x`] THEN
    REWRITE_TAC[REAL_EXP_NEG; REAL_INV_INV] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Log-convex functions.                                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("log_convex_on",(12,"right"));;

let log_convex_on = new_definition
 `f log_convex_on (s:real^N->bool) <=>
        (!x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ u + v = &1
                   ==> &0 <= f(u % x + v % y) /\
                       f(u % x + v % y) <= f(x) rpow u * f(y) rpow v)`;;

let LOG_CONVEX_ON_SUBSET = prove
 (`!f s t. f log_convex_on t /\ s SUBSET t ==> f log_convex_on s`,
  REWRITE_TAC[log_convex_on] THEN SET_TAC[]);;

let LOG_CONVEX_IMP_POS = prove
 (`!f s x:real^N.
        f log_convex_on s /\ x IN s ==> &0 <= f x`,
  REWRITE_TAC[log_convex_on] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `x:real^N`; `&0`; `&1`]) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_MESON_TAC[]);;

let LOG_CONVEX_ON_CONVEX = prove
 (`!f s:real^N->bool.
        convex s
        ==> (f log_convex_on s <=>
             (!x. x IN s ==> &0 <= f x) /\
             !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ u + v = &1
                       ==> f(u % x + v % y) <= f(x) rpow u * f(y) rpow v)`,
  REWRITE_TAC[convex] THEN REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [ASM_MESON_TAC[LOG_CONVEX_IMP_POS];
    ASM_MESON_TAC[log_convex_on];
    ASM_SIMP_TAC[log_convex_on] THEN ASM_MESON_TAC[]]);;

let LOG_CONVEX_ON = prove
 (`!f s:real^N->bool.
        convex s /\ (!x. x IN s ==> &0 < f x)
        ==> (f log_convex_on s <=> (log o f) convex_on s)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LOG_CONVEX_ON_CONVEX; REAL_LT_IMP_LE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[convex]) THEN REWRITE_TAC[convex_on; o_DEF] THEN
  GEN_REWRITE_TAC (RAND_CONV o funpow 4 BINDER_CONV o RAND_CONV)
    [GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG; rpow; REAL_EXP_ADD]);;

let LOG_CONVEX_IMP_CONVEX = prove
 (`!f s:real^N->bool. f log_convex_on s ==> f convex_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    LOG_CONVEX_IMP_POS)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[log_convex_on]) THEN REWRITE_TAC[convex_on] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC o SPECL [`x:real^N`; `y:real^N`; `u:real`; `v:real`]) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  MATCH_MP_TAC AGM_2 THEN ASM_SIMP_TAC[]);;

let LOG_CONVEX_ADD = prove
 (`!f g s:real^N->bool.
        f log_convex_on s /\ g log_convex_on s
        ==> (\x. f x + g x) log_convex_on s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN(ASSUME_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    LOG_CONVEX_IMP_POS))) THEN
  REWRITE_TAC[log_convex_on] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (ASSUME_TAC o REWRITE_RULE[log_convex_on])) THEN
  REWRITE_TAC[log_convex_on] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_ADD] THEN
  MP_TAC(ISPEC `0..SUC 0` HOELDER) THEN
  SIMP_TAC[PRODUCT_CLAUSES_NUMSEG;
           FINITE_NUMSEG; SUM_CLAUSES_NUMSEG; ARITH] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\i. if i = 0 then u:real else v`;
    `\i. if i = 0 then (f:real^N->real) x else f y`;
    `\i. if i = 0 then (g:real^N->real) x else g y`]) THEN
  REWRITE_TAC[ARITH] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_MESON_TAC[]);;

let LOG_CONVEX_MUL = prove
 (`!f g s:real^N->bool.
        f log_convex_on s /\ g log_convex_on s
        ==> (\x. f x * g x) log_convex_on s`,
  REWRITE_TAC[log_convex_on] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_MUL; RPOW_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(a * b) * (c * d):real = (a * c) * (b * d)`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL2]);;

let MIDPOINT_LOG_CONVEX = prove
 (`!f s:real^N->bool.
        (lift o f) continuous_on s /\ convex s /\
        (!x. x IN s ==> &0 < f x) /\
        (!x y. x IN s /\ y IN s ==> f(midpoint(x,y)) pow 2 <= f(x) * f(y))
        ==> f log_convex_on s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LOG_CONVEX_ON] THEN
  MATCH_MP_TAC CONTINUOUS_MIDPOINT_CONVEX THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `lift o log o (f:real^N->real) =
                  (lift o log o drop) o (lift o f)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_REWRITE_TAC[GSYM REAL_CONTINUOUS_ON; IMAGE_o] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LOG THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[o_DEF; REAL_ARITH `x <= y / &2 <=> &2 * x <= y`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[REAL_EXP_N; EXP_LOG; REAL_EXP_ADD; MIDPOINT_IN_CONVEX]]);;

let LOG_CONVEX_CONST = prove
 (`!s a. &0 <= a ==> (\x. a) log_convex_on s`,
  SIMP_TAC[log_convex_on; GSYM RPOW_ADD] THEN
  IMP_REWRITE_TAC[GSYM RPOW_ADD_ALT] THEN
  REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL] THEN REAL_ARITH_TAC);;

let LOG_CONVEX_PRODUCT = prove
 (`!f s k. FINITE k /\ (!i. i IN k ==> (\x. f x i) log_convex_on s)
           ==> (\x. product k (f x)) log_convex_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; LOG_CONVEX_CONST; REAL_POS] THEN
  SIMP_TAC[FORALL_IN_INSERT; LOG_CONVEX_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Real log-convex functions.                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("real_log_convex_on",(12,"right"));;

let real_log_convex_on = new_definition
 `(f:real->real) real_log_convex_on s <=>
        (!x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ u + v = &1
                   ==> &0 <= f(u * x + v * y) /\
                       f(u * x + v * y) <= f(x) rpow u * f(y) rpow v)`;;

let REAL_LOG_CONVEX_ON_SUBSET = prove
 (`!f s t. f real_log_convex_on t /\ s SUBSET t ==> f real_log_convex_on s`,
  REWRITE_TAC[real_log_convex_on] THEN SET_TAC[]);;

let REAL_LOG_CONVEX_LOG_CONVEX = prove
 (`!f s. f real_log_convex_on s <=> (f o drop) log_convex_on (IMAGE lift s)`,
  REWRITE_TAC[real_log_convex_on; log_convex_on] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_DEF; DROP_ADD; DROP_CMUL; LIFT_DROP]);;

let REAL_LOG_CONVEX_IMP_POS = prove
 (`!f s x.
        f real_log_convex_on s /\ x IN s ==> &0 <= f x`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; REAL_LOG_CONVEX_LOG_CONVEX] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] LOG_CONVEX_IMP_POS)) THEN
  REWRITE_TAC[o_DEF; FORALL_IN_IMAGE; LIFT_DROP]);;

let REAL_LOG_CONVEX_ON_CONVEX = prove
 (`!f s.
        is_realinterval s
        ==> (f real_log_convex_on s <=>
             (!x. x IN s ==> &0 <= f x) /\
             !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ u + v = &1
                       ==> f(u * x + v * y) <= f(x) rpow u * f(y) rpow v)`,
  REWRITE_TAC[REAL_CONVEX] THEN REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [ASM_MESON_TAC[REAL_LOG_CONVEX_IMP_POS];
    ASM_MESON_TAC[real_log_convex_on];
    ASM_SIMP_TAC[real_log_convex_on] THEN ASM_MESON_TAC[]]);;

let REAL_LOG_CONVEX_ON = prove
 (`!f s:real->bool.
        is_realinterval s /\ (!x. x IN s ==> &0 < f x)
        ==> (f real_log_convex_on s <=> (log o f) real_convex_on s)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LOG_CONVEX_ON_CONVEX; REAL_LT_IMP_LE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_CONVEX]) THEN
  REWRITE_TAC[real_convex_on; o_DEF] THEN
  GEN_REWRITE_TAC (RAND_CONV o funpow 4 BINDER_CONV o RAND_CONV)
    [GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG; rpow; REAL_EXP_ADD]);;

let REAL_LOG_CONVEX_IMP_CONVEX = prove
 (`!f s:real->bool. f real_log_convex_on s ==> f real_convex_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    REAL_LOG_CONVEX_IMP_POS)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[real_log_convex_on]) THEN
  REWRITE_TAC[real_convex_on] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `u:real`; `v:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC o SPECL [`x:real`; `y:real`; `u:real`; `v:real`]) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  MATCH_MP_TAC AGM_2 THEN ASM_SIMP_TAC[]);;

let REAL_LOG_CONVEX_ADD = prove
 (`!f g s:real->bool.
        f real_log_convex_on s /\ g real_log_convex_on s
        ==> (\x. f x + g x) real_log_convex_on s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN(ASSUME_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    REAL_LOG_CONVEX_IMP_POS))) THEN
  REWRITE_TAC[real_log_convex_on] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN
    (ASSUME_TAC o REWRITE_RULE[real_log_convex_on])) THEN
  REWRITE_TAC[real_log_convex_on] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `u:real`; `v:real`] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_ADD] THEN
  MP_TAC(ISPEC `0..SUC 0` HOELDER) THEN
  SIMP_TAC[PRODUCT_CLAUSES_NUMSEG;
           FINITE_NUMSEG; SUM_CLAUSES_NUMSEG; ARITH] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\i. if i = 0 then u:real else v`;
    `\i. if i = 0 then (f:real->real) x else f y`;
    `\i. if i = 0 then (g:real->real) x else g y`]) THEN
  REWRITE_TAC[ARITH] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_MESON_TAC[]);;

let REAL_LOG_CONVEX_MUL = prove
 (`!f g s:real->bool.
        f real_log_convex_on s /\ g real_log_convex_on s
        ==> (\x. f x * g x) real_log_convex_on s`,
  REWRITE_TAC[real_log_convex_on] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_MUL; RPOW_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(a * b) * (c * d):real = (a * c) * (b * d)`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL2]);;

let MIDPOINT_REAL_LOG_CONVEX = prove
 (`!f s:real->bool.
        f real_continuous_on s /\ is_realinterval s /\
        (!x. x IN s ==> &0 < f x) /\
        (!x y. x IN s /\ y IN s ==> f((x + y) / &2) pow 2 <= f(x) * f(y))
        ==> f real_log_convex_on s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LOG_CONVEX_ON] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_MIDPOINT_CONVEX THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LOG THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE];
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[o_DEF; REAL_ARITH `x <= y / &2 <=> &2 * x <= y`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC[REAL_EXP_N; EXP_LOG; REAL_EXP_ADD; REAL_MIDPOINT_IN_CONVEX]]);;

let REAL_LOG_CONVEX_CONST = prove
 (`!s a. &0 <= a ==> (\x. a) real_log_convex_on s`,
  SIMP_TAC[real_log_convex_on; GSYM RPOW_ADD] THEN
  IMP_REWRITE_TAC[GSYM RPOW_ADD_ALT] THEN
  REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL] THEN REAL_ARITH_TAC);;

let REAL_LOG_CONVEX_PRODUCT = prove
 (`!f s k. FINITE k /\ (!i. i IN k ==> (\x. f x i) real_log_convex_on s)
           ==> (\x. product k (f x)) real_log_convex_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; REAL_LOG_CONVEX_CONST; REAL_POS] THEN
  SIMP_TAC[FORALL_IN_INSERT; REAL_LOG_CONVEX_MUL]);;

let REAL_LOG_CONVEX_RPOW_RIGHT = prove
 (`!s a. &0 < a ==> (\x. a rpow x) real_log_convex_on s`,
  SIMP_TAC[real_log_convex_on; RPOW_POS_LE; REAL_LT_IMP_LE] THEN
  SIMP_TAC[DROP_ADD; DROP_CMUL; RPOW_ADD; RPOW_RPOW; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]);;

let REAL_LOG_CONVEX_LIM = prove
 (`!net:A net f g s.
       ~(trivial_limit net) /\
       (!x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ u + v = &1
                  ==> ((\i. f i (u * x + v * y)) ---> g(u * x + v * y)) net) /\
       eventually (\i. (f i) real_log_convex_on s) net
       ==> g real_log_convex_on s`,
  REWRITE_TAC[real_log_convex_on] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_LE] THEN
  CONJ_TAC THEN MATCH_MP_TAC(ISPEC `net:A net` REALLIM_LBOUND) THENL
   [EXISTS_TAC `\i. (f:A->real->real) i (u * x + v * y)`;
    EXISTS_TAC `\i. (f:A->real->real) i x rpow u * f i y rpow v -
                    f i (u * x + v * y)`] THEN
  ASM_SIMP_TAC[] THEN TRY CONJ_TAC THEN
  TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        EVENTUALLY_MONO))) THEN
  ASM_SIMP_TAC[REAL_SUB_LE] THEN
  MATCH_MP_TAC REALLIM_SUB THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `\x. x rpow y`
    REALLIM_REAL_CONTINUOUS_FUNCTION)) THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_AT_RPOW] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `x:real`; `&1`; `&0`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real`; `y:real`; `&1`; `&0`])] THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_ADD_RID; REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Integrals of real->real functions; measures of real sets.                 *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_real_integral",(12,"right"));;
parse_as_infix("real_integrable_on",(12,"right"));;
parse_as_infix("absolutely_real_integrable_on",(12,"right"));;
parse_as_infix("has_real_measure",(12,"right"));;

let has_real_integral = new_definition
 `(f has_real_integral y) s <=>
        ((lift o f o drop) has_integral (lift y)) (IMAGE lift s)`;;

let real_integrable_on = new_definition
 `f real_integrable_on i <=> ?y. (f has_real_integral y) i`;;

let real_integral = new_definition
 `real_integral i f = @y. (f has_real_integral y) i`;;

let real_negligible = new_definition
 `real_negligible s <=> negligible (IMAGE lift s)`;;

let absolutely_real_integrable_on = new_definition
 `f absolutely_real_integrable_on s <=>
        f real_integrable_on s /\ (\x. abs(f x)) real_integrable_on s`;;

let has_real_measure = new_definition
 `s has_real_measure m <=> ((\x. &1) has_real_integral m) s`;;

let real_measurable = new_definition
 `real_measurable s <=> ?m. s has_real_measure m`;;

let real_measure = new_definition
 `real_measure s = @m. s has_real_measure m`;;

let HAS_REAL_INTEGRAL = prove
 (`(f has_real_integral y) (real_interval[a,b]) <=>
   ((lift o f o drop) has_integral (lift y)) (interval[lift a,lift b])`,
  REWRITE_TAC[has_real_integral; IMAGE_LIFT_REAL_INTERVAL]);;

let REAL_INTEGRABLE_INTEGRAL = prove
 (`!f i. f real_integrable_on i
         ==> (f has_real_integral (real_integral i f)) i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_integrable_on; real_integral] THEN
  CONV_TAC(RAND_CONV SELECT_CONV) THEN REWRITE_TAC[]);;

let HAS_REAL_INTEGRAL_INTEGRABLE = prove
 (`!f i s. (f has_real_integral i) s ==> f real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[]);;

let HAS_REAL_INTEGRAL_INTEGRAL = prove
 (`!f s. f real_integrable_on s <=>
         (f has_real_integral (real_integral s f)) s`,
  MESON_TAC[REAL_INTEGRABLE_INTEGRAL; HAS_REAL_INTEGRAL_INTEGRABLE]);;

let HAS_REAL_INTEGRAL_UNIQUE = prove
 (`!f i k1 k2.
        (f has_real_integral k1) i /\ (f has_real_integral k2) i ==> k1 = k2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[LIFT_EQ]);;

let REAL_INTEGRAL_UNIQUE = prove
 (`!f y k.
      (f has_real_integral y) k ==> real_integral k f = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_integral] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE]);;

let HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL = prove
 (`!f i s.
        (f has_real_integral i) s <=>
        f real_integrable_on s /\ real_integral s f = i`,
  MESON_TAC[REAL_INTEGRABLE_INTEGRAL; REAL_INTEGRAL_UNIQUE;
            real_integrable_on]);;

let REAL_INTEGRAL_EQ_HAS_INTEGRAL = prove
 (`!s f y. f real_integrable_on s
           ==> (real_integral s f = y <=> (f has_real_integral y) s)`,
  MESON_TAC[REAL_INTEGRABLE_INTEGRAL; REAL_INTEGRAL_UNIQUE]);;

let REAL_INTEGRABLE_ON = prove
 (`f real_integrable_on s <=>
        (lift o f o drop) integrable_on (IMAGE lift s)`,
  REWRITE_TAC[real_integrable_on; has_real_integral; EXISTS_DROP;
              integrable_on; LIFT_DROP]);;

let ABSOLUTELY_REAL_INTEGRABLE_ON = prove
 (`f absolutely_real_integrable_on s <=>
        (lift o f o drop) absolutely_integrable_on (IMAGE lift s)`,
  REWRITE_TAC[absolutely_real_integrable_on; REAL_INTEGRABLE_ON;
              absolutely_integrable_on] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; NORM_LIFT]);;

let REAL_INTEGRAL = prove
 (`f real_integrable_on s
   ==> real_integral s f = drop(integral (IMAGE lift s) (lift o f o drop))`,
  REWRITE_TAC[REAL_INTEGRABLE_ON] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[has_real_integral; LIFT_DROP] THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

let HAS_REAL_INTEGRAL_ALT = prove
 (`!f s i.
         (f has_real_integral i) s <=>
         (!a b. (\x. if x IN s then f x else &0) real_integrable_on
                real_interval [a,b]) /\
         (!e. &0 < e
              ==> (?B. &0 < B /\
                       (!a b.
                            real_interval(--B,B) SUBSET real_interval[a,b]
                            ==> abs
                                (real_integral (real_interval[a,b])
                                 (\x. if x IN s then f x else &0) -
                                 i) < e)))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [has_real_integral] THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_ALT] THEN
  REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[GSYM FORALL_LIFT; COND_RAND; LIFT_NUM; IN_IMAGE_LIFT_DROP] THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> q')) ==> (p /\ q <=> p /\ q')`) THEN
  DISCH_TAC THEN REWRITE_TAC[BALL_1] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `e:real` THEN ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `B:real` THEN ASM_CASES_TAC `&0 < B` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_LIFT; VECTOR_ADD_LID; VECTOR_SUB_LZERO] THEN
  REWRITE_TAC[GSYM LIFT_NEG; GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[SUBSET_LIFT_IMAGE; NORM_REAL; GSYM drop] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `a:real` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `b:real` THEN
  ASM_CASES_TAC `real_interval(--B,B) SUBSET real_interval[a,b]` THEN
  ASM_REWRITE_TAC[DROP_SUB; LIFT_DROP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN IMP_REWRITE_TAC[REAL_INTEGRAL] THEN
  REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF; LIFT_DROP; COND_RAND] THEN
  ASM_REWRITE_TAC[LIFT_NUM; IMAGE_LIFT_REAL_INTERVAL]);;

let HAS_REAL_INTEGRAL_IS_0 = prove
 (`!f s. (!x. x IN s ==> f(x) = &0) ==> (f has_real_integral &0) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_real_integral; LIFT_NUM] THEN
  MATCH_MP_TAC HAS_INTEGRAL_IS_0 THEN
  ASM_REWRITE_TAC[LIFT_EQ; FORALL_IN_IMAGE; o_THM; LIFT_DROP; GSYM LIFT_NUM]);;

let HAS_REAL_INTEGRAL_0 = prove
 (`!s. ((\x. &0) has_real_integral &0) s`,
  SIMP_TAC[HAS_REAL_INTEGRAL_IS_0]);;

let HAS_REAL_INTEGRAL_0_EQ = prove
 (`!i s. ((\x. &0) has_real_integral i) s <=> i = &0`,
  MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE; HAS_REAL_INTEGRAL_0]);;

let HAS_REAL_INTEGRAL_LINEAR = prove
 (`!f:real->real y s h:real->real.
        (f has_real_integral y) s /\ linear(lift o h o drop)
        ==> ((h o f) has_real_integral h(y)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_LINEAR) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let HAS_REAL_INTEGRAL_LMUL = prove
 (`!(f:real->real) k s c.
        (f has_real_integral k) s
        ==> ((\x. c * f(x)) has_real_integral (c * k)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  REWRITE_TAC[GSYM LIFT_CMUL; o_DEF]);;

let HAS_REAL_INTEGRAL_RMUL = prove
 (`!(f:real->real) k s c.
        (f has_real_integral k) s
        ==> ((\x. f(x) * c) has_real_integral (k * c)) s`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_LMUL]);;

let HAS_REAL_INTEGRAL_NEG = prove
 (`!f k s. (f has_real_integral k) s
           ==> ((\x. --(f x)) has_real_integral (--k)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_NEG) THEN
  REWRITE_TAC[o_DEF; LIFT_NEG]);;

let HAS_REAL_INTEGRAL_ADD = prove
 (`!f:real->real g k l s.
        (f has_real_integral k) s /\ (g has_real_integral l) s
        ==> ((\x. f(x) + g(x)) has_real_integral (k + l)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_ADD) THEN
  REWRITE_TAC[o_DEF; LIFT_ADD]);;

let HAS_REAL_INTEGRAL_SUB = prove
 (`!f:real->real g k l s.
        (f has_real_integral k) s /\ (g has_real_integral l) s
        ==> ((\x. f(x) - g(x)) has_real_integral (k - l)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN
  REWRITE_TAC[o_DEF; LIFT_SUB]);;

let REAL_INTEGRAL_0 = prove
 (`!s. real_integral s (\x. &0) = &0`,
  MESON_TAC[REAL_INTEGRAL_UNIQUE; HAS_REAL_INTEGRAL_0]);;

let REAL_INTEGRAL_ADD = prove
 (`!f:real->real g s.
        f real_integrable_on s /\ g real_integrable_on s
        ==> real_integral s (\x. f x + g x) =
            real_integral s f + real_integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRAL_LMUL = prove
 (`!f:real->real c s.
        f real_integrable_on s
        ==> real_integral s (\x. c * f(x)) = c * real_integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRAL_RMUL = prove
 (`!f:real->real c s.
        f real_integrable_on s
        ==> real_integral s (\x. f(x) * c) = real_integral s f * c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRAL_NEG = prove
 (`!f:real->real s.
        f real_integrable_on s
        ==> real_integral s (\x. --f(x)) = --real_integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_NEG THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRAL_SUB = prove
 (`!f:real->real g s.
        f real_integrable_on s /\ g real_integrable_on s
        ==> real_integral s (\x. f x - g x) =
            real_integral s f - real_integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRABLE_0 = prove
 (`!s. (\x. &0) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_0]);;

let REAL_INTEGRABLE_ADD = prove
 (`!f:real->real g s.
        f real_integrable_on s /\ g real_integrable_on s
        ==> (\x. f x + g x) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_ADD]);;

let REAL_INTEGRABLE_LMUL = prove
 (`!f:real->real c s.
        f real_integrable_on s
        ==> (\x. c * f(x)) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_LMUL]);;

let REAL_INTEGRABLE_RMUL = prove
 (`!f:real->real c s.
        f real_integrable_on s
        ==> (\x. f(x) * c) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_RMUL]);;

let REAL_INTEGRABLE_LMUL_EQ = prove
 (`!f s c.
        (\x. c * f x) real_integrable_on s <=>
        c = &0 \/ f real_integrable_on s`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_INTEGRABLE_0] THEN
  ASM_CASES_TAC `c = &0` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv c:real` o
    MATCH_MP REAL_INTEGRABLE_LMUL) THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LID; REAL_MUL_LINV; ETA_AX]);;

let REAL_INTEGRABLE_RMUL_EQ = prove
 (`!f s c.
        (\x. f x * c) real_integrable_on s <=>
        c = &0 \/ f real_integrable_on s`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_INTEGRABLE_LMUL_EQ]);;

let REAL_INTEGRABLE_NEG = prove
 (`!f:real->real s.
        f real_integrable_on s ==> (\x. --f(x)) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_NEG]);;

let REAL_INTEGRABLE_SUB = prove
 (`!f:real->real g s.
        f real_integrable_on s /\ g real_integrable_on s
        ==> (\x. f x - g x) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_SUB]);;

let REAL_INTEGRABLE_LINEAR = prove
 (`!f h s. f real_integrable_on s /\
           linear(lift o h o drop) ==> (h o f) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_LINEAR]);;

let REAL_INTEGRAL_LINEAR = prove
 (`!f:real->real s h:real->real.
        f real_integrable_on s /\ linear(lift o h o drop)
        ==> real_integral s (h o f) = h(real_integral s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`(h:real->real) o (f:real->real)`; `s:real->bool`] THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC HAS_REAL_INTEGRAL_LINEAR] THEN
  ASM_SIMP_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL; REAL_INTEGRABLE_LINEAR]);;

let HAS_REAL_INTEGRAL_SUM = prove
 (`!f:A->real->real s t.
        FINITE t /\
        (!a. a IN t ==> ((f a) has_real_integral (i a)) s)
        ==> ((\x. sum t (\a. f a x)) has_real_integral (sum t i)) s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; HAS_REAL_INTEGRAL_0; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN
  ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let REAL_INTEGRAL_SUM = prove
 (`!f:A->real->real s t.
        FINITE t /\
        (!a. a IN t ==> (f a) real_integrable_on s)
        ==> real_integral s (\x. sum t (\a. f a x)) =
                sum t (\a. real_integral s (f a))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRABLE_SUM = prove
 (`!f:A->real->real s t.
        FINITE t /\
        (!a. a IN t ==> (f a) real_integrable_on s)
        ==>  (\x. sum t (\a. f a x)) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_SUM]);;

let HAS_REAL_INTEGRAL_EQ = prove
 (`!f:real->real g k s.
        (!x. x IN s ==> (f(x) = g(x))) /\
        (f has_real_integral k) s
        ==> (g has_real_integral k) s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_IS_0) MP_TAC) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN
   (MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_SUB) THEN
  SIMP_TAC[REAL_ARITH `x - (x - y:real) = y`; ETA_AX; REAL_SUB_RZERO]);;

let REAL_INTEGRABLE_EQ = prove
 (`!f:real->real g s.
        (!x. x IN s ==> (f(x) = g(x))) /\
        f real_integrable_on s
        ==> g real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_EQ]);;

let HAS_REAL_INTEGRAL_EQ_EQ = prove
 (`!f:real->real g k s.
        (!x. x IN s ==> (f(x) = g(x)))
        ==> ((f has_real_integral k) s <=> (g has_real_integral k) s)`,
  MESON_TAC[HAS_REAL_INTEGRAL_EQ]);;

let HAS_REAL_INTEGRAL_NULL = prove
 (`!f:real->real a b.
    b <= a ==> (f has_real_integral &0) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[has_real_integral; REAL_INTERVAL_INTERVAL] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP; LIFT_NUM] THEN
  REWRITE_TAC[SET_RULE `IMAGE (\x. x) s = s`] THEN
  MATCH_MP_TAC HAS_INTEGRAL_NULL THEN
  ASM_REWRITE_TAC[CONTENT_EQ_0_1; LIFT_DROP]);;

let HAS_REAL_INTEGRAL_NULL_EQ = prove
 (`!f a b i. b <= a
             ==> ((f has_real_integral i) (real_interval[a,b]) <=> i = &0)`,
  ASM_MESON_TAC[REAL_INTEGRAL_UNIQUE; HAS_REAL_INTEGRAL_NULL]);;

let REAL_INTEGRAL_NULL = prove
 (`!f a b. b <= a
           ==> real_integral(real_interval[a,b]) f = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_MESON_TAC[HAS_REAL_INTEGRAL_NULL]);;

let REAL_INTEGRABLE_ON_NULL = prove
 (`!f a b. b <= a
           ==> f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_NULL]);;

let HAS_REAL_INTEGRAL_EMPTY = prove
 (`!f. (f has_real_integral &0) {}`,
  GEN_TAC THEN REWRITE_TAC[EMPTY_AS_REAL_INTERVAL] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_NULL THEN REWRITE_TAC[REAL_POS]);;

let HAS_REAL_INTEGRAL_EMPTY_EQ = prove
 (`!f i. (f has_real_integral i) {} <=> i = &0`,
  MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE; HAS_REAL_INTEGRAL_EMPTY]);;

let REAL_INTEGRABLE_ON_EMPTY = prove
 (`!f. f real_integrable_on {}`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_EMPTY]);;

let REAL_INTEGRAL_EMPTY = prove
 (`!f. real_integral {} f = &0`,
  MESON_TAC[EMPTY_AS_REAL_INTERVAL; REAL_INTEGRAL_UNIQUE;
            HAS_REAL_INTEGRAL_EMPTY]);;

let HAS_REAL_INTEGRAL_REFL = prove
 (`!f a. (f has_real_integral &0) (real_interval[a,a])`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_NULL THEN
  REWRITE_TAC[REAL_LE_REFL]);;

let REAL_INTEGRABLE_ON_REFL = prove
 (`!f a. f real_integrable_on real_interval[a,a]`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_REFL]);;

let REAL_INTEGRAL_REFL = prove
 (`!f a. real_integral (real_interval[a,a]) f = &0`,
  MESON_TAC[REAL_INTEGRAL_UNIQUE; HAS_REAL_INTEGRAL_REFL]);;

let HAS_REAL_INTEGRAL_CONST = prove
 (`!a b c.
        a <= b
        ==> ((\x. c) has_real_integral (c * (b - a))) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[has_real_integral; IMAGE_LIFT_REAL_INTERVAL] THEN
  MP_TAC(ISPECL [`lift a`; `lift b`; `lift c`] HAS_INTEGRAL_CONST) THEN
  ASM_SIMP_TAC[o_DEF; CONTENT_1; LIFT_DROP; LIFT_CMUL]);;

let REAL_INTEGRABLE_CONST = prove
 (`!a b c. (\x. c) real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL;
              o_DEF; INTEGRABLE_CONST]);;

let REAL_INTEGRAL_CONST = prove
 (`!a b c.
        a <= b
        ==> real_integral (real_interval [a,b]) (\x. c) = c * (b - a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_CONST]);;

let HAS_REAL_INTEGRAL_BOUND = prove
 (`!f:real->real a b i B.
        &0 <= B /\ a <= b /\
        (f has_real_integral i) (real_interval[a,b]) /\
        (!x. x IN real_interval[a,b] ==> abs(f x) <= B)
        ==> abs i <= B * (b - a)`,
  REWRITE_TAC[HAS_REAL_INTEGRAL; REAL_INTERVAL_INTERVAL; GSYM NORM_LIFT] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o BINOP_CONV) [GSYM LIFT_DROP] THEN
  ASM_SIMP_TAC[GSYM CONTENT_1; LIFT_DROP] THEN
  MATCH_MP_TAC HAS_INTEGRAL_BOUND THEN
  EXISTS_TAC `lift o f o drop` THEN ASM_REWRITE_TAC[o_THM]);;

let HAS_REAL_INTEGRAL_LE = prove
 (`!f g s i j.
        (f has_real_integral i) s /\ (g has_real_integral j) s /\
        (!x. x IN s ==> f x <= g x)
        ==> i <= j`,
  REWRITE_TAC[has_real_integral] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM LIFT_DROP] THEN
  REWRITE_TAC[drop] THEN MATCH_MP_TAC
   (ISPECL [`lift o f o drop`; `lift o g o drop`; `IMAGE lift s`]
           HAS_INTEGRAL_COMPONENT_LE) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; DIMINDEX_1; LE_REFL; o_THM; LIFT_DROP;
                  GSYM drop]);;

let REAL_INTEGRAL_LE = prove
 (`!f:real->real g:real->real s.
        f real_integrable_on s /\ g real_integrable_on s /\
        (!x. x IN s ==> f x <= g x)
        ==> real_integral s f <= real_integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_LE THEN
  ASM_MESON_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let HAS_REAL_INTEGRAL_POS = prove
 (`!f:real->real s i.
        (f has_real_integral i) s /\
        (!x. x IN s ==> &0 <= f x)
        ==> &0 <= i`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(\x. &0):real->real`; `f:real->real`;
                 `s:real->bool`; `&0:real`;
                 `i:real`] HAS_REAL_INTEGRAL_LE) THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_0]);;

let REAL_INTEGRAL_POS = prove
 (`!f:real->real s.
        f real_integrable_on s /\
        (!x. x IN s ==> &0 <= f x)
        ==> &0 <= real_integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_POS THEN
  ASM_MESON_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let HAS_REAL_INTEGRAL_ISNEG = prove
 (`!f:real->real s i.
        (f has_real_integral i) s /\
        (!x. x IN s ==> f x <= &0)
        ==> i <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `(\x. &0):real->real`;
                 `s:real->bool`; `i:real`; `&0:real`;
                ] HAS_REAL_INTEGRAL_LE) THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_0]);;

let HAS_REAL_INTEGRAL_LBOUND = prove
 (`!f:real->real a b i.
        a <= b /\
        (f has_real_integral i) (real_interval[a,b]) /\
        (!x. x IN real_interval[a,b] ==> B <= f(x))
        ==> B * (b - a) <= i`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(\x. B):real->real`; `f:real->real`;
                 `real_interval[a,b]`;
                  `B * (b - a):real`;
                 `i:real`]
                HAS_REAL_INTEGRAL_LE) THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_CONST]);;

let HAS_REAL_INTEGRAL_UBOUND = prove
 (`!f:real->real a b i.
        a <= b /\
        (f has_real_integral i) (real_interval[a,b]) /\
        (!x. x IN real_interval[a,b] ==> f(x) <= B)
        ==> i <= B * (b - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `(\x. B):real->real`;
                 `real_interval[a,b]`; `i:real`;
                 `B * (b - a):real`]
                HAS_REAL_INTEGRAL_LE) THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_CONST]);;

let REAL_INTEGRAL_LBOUND = prove
 (`!f:real->real a b.
        a <= b /\
        f real_integrable_on real_interval[a,b] /\
        (!x. x IN real_interval[a,b] ==> B <= f(x))
        ==> B * (b - a) <= real_integral(real_interval[a,b]) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_LBOUND THEN
  EXISTS_TAC `f:real->real` THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL]);;

let REAL_INTEGRAL_UBOUND = prove
 (`!f:real->real a b.
        a <= b /\
        f real_integrable_on real_interval[a,b] /\
        (!x. x IN real_interval[a,b] ==> f(x) <= B)
        ==> real_integral(real_interval[a,b]) f <= B * (b - a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_UBOUND THEN
  EXISTS_TAC `f:real->real` THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL]);;

let REAL_INTEGRABLE_UNIFORM_LIMIT = prove
 (`!f a b. (!e. &0 < e
                ==> ?g. (!x. x IN real_interval[a,b] ==> abs(f x - g x) <= e) /\
                        g real_integrable_on real_interval[a,b] )
           ==> f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL; GSYM EXISTS_LIFT] THEN
  REWRITE_TAC[GSYM integrable_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_UNIFORM_LIMIT THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `lift o g o drop` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[o_THM; LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT]);;

let HAS_REAL_INTEGRAL_NEGLIGIBLE = prove
 (`!f s t.
        real_negligible s /\ (!x. x IN (t DIFF s) ==> f x = &0)
        ==> (f has_real_integral (&0)) t`,
  REWRITE_TAC[has_real_integral; real_negligible; LIFT_NUM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_NEGLIGIBLE THEN
  EXISTS_TAC `IMAGE lift s` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM; IN_DIFF; IMP_CONJ; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[LIFT_IN_IMAGE_LIFT; LIFT_DROP] THEN ASM SET_TAC[LIFT_NUM]);;

let HAS_REAL_INTEGRAL_SPIKE = prove
 (`!f g s t y.
        real_negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x) /\
        (f has_real_integral y) t
        ==> (g has_real_integral y) t`,
  REWRITE_TAC[has_real_integral; real_negligible] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  MAP_EVERY EXISTS_TAC [`lift o f o drop`; `IMAGE lift s`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM; IN_DIFF; IMP_CONJ; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[LIFT_IN_IMAGE_LIFT; LIFT_DROP] THEN ASM SET_TAC[LIFT_NUM]);;

let HAS_REAL_INTEGRAL_SPIKE_EQ = prove
 (`!f g s t y.
        real_negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> ((f has_real_integral y) t <=> (g has_real_integral y) t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE THENL
   [EXISTS_TAC `f:real->real`; EXISTS_TAC `g:real->real`] THEN
  EXISTS_TAC `s:real->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_ABS_SUB]);;

let REAL_INTEGRABLE_SPIKE = prove
 (`!f g s t.
        real_negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> f real_integrable_on t ==> g real_integrable_on  t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_REAL_INTEGRAL_SPIKE) THEN ASM_REWRITE_TAC[]);;

let REAL_INTEGRABLE_SPIKE_EQ = prove
 (`!f g s t.
         real_negligible s /\ (!x. x IN t DIFF s ==> g x = f x)
         ==> (f real_integrable_on t <=> g real_integrable_on t)`,
  MESON_TAC[REAL_INTEGRABLE_SPIKE]);;

let REAL_INTEGRAL_SPIKE = prove
 (`!f:real->real g s t.
        real_negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> real_integral t f = real_integral t g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE_EQ THEN
  ASM_MESON_TAC[]);;

let REAL_NEGLIGIBLE_SUBSET = prove
 (`!s:real->bool t:real->bool.
        real_negligible s /\ t SUBSET s ==> real_negligible t`,
  REWRITE_TAC[real_negligible] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `IMAGE lift s` THEN ASM_SIMP_TAC[IMAGE_SUBSET]);;

let REAL_NEGLIGIBLE_DIFF = prove
 (`!s t:real->bool. real_negligible s ==> real_negligible(s DIFF t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `s:real->bool` THEN ASM_REWRITE_TAC[SUBSET_DIFF]);;

let REAL_NEGLIGIBLE_INTER = prove
 (`!s t. real_negligible s \/ real_negligible t ==> real_negligible(s INTER t)`,
  MESON_TAC[REAL_NEGLIGIBLE_SUBSET; INTER_SUBSET]);;

let REAL_NEGLIGIBLE_UNION = prove
 (`!s t:real->bool.
       real_negligible s /\ real_negligible t ==> real_negligible (s UNION t)`,
  SIMP_TAC[NEGLIGIBLE_UNION; IMAGE_UNION; real_negligible]);;

let REAL_NEGLIGIBLE_UNION_EQ = prove
 (`!s t:real->bool.
        real_negligible (s UNION t) <=> real_negligible s /\ real_negligible t`,
  MESON_TAC[REAL_NEGLIGIBLE_UNION; SUBSET_UNION; REAL_NEGLIGIBLE_SUBSET]);;

let REAL_NEGLIGIBLE_SING = prove
 (`!a:real. real_negligible {a}`,
  REWRITE_TAC[real_negligible; NEGLIGIBLE_SING; IMAGE_CLAUSES]);;

let REAL_NEGLIGIBLE_INSERT = prove
 (`!a:real s. real_negligible(a INSERT s) <=> real_negligible s`,
  REWRITE_TAC[real_negligible; NEGLIGIBLE_INSERT; IMAGE_CLAUSES]);;

let REAL_NEGLIGIBLE_EMPTY = prove
 (`real_negligible {}`,
  REWRITE_TAC[real_negligible; NEGLIGIBLE_EMPTY; IMAGE_CLAUSES]);;

let REAL_NEGLIGIBLE_FINITE = prove
 (`!s. FINITE s ==> real_negligible s`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[REAL_NEGLIGIBLE_EMPTY; REAL_NEGLIGIBLE_INSERT]);;

let REAL_NEGLIGIBLE_UNIONS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> real_negligible t)
       ==> real_negligible(UNIONS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; REAL_NEGLIGIBLE_EMPTY; IN_INSERT] THEN
  SIMP_TAC[REAL_NEGLIGIBLE_UNION]);;

let HAS_REAL_INTEGRAL_SPIKE_FINITE = prove
 (`!f:real->real g s t y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x) /\
        (f has_real_integral y) t
        ==> (g has_real_integral y) t`,
  MESON_TAC[HAS_REAL_INTEGRAL_SPIKE; REAL_NEGLIGIBLE_FINITE]);;

let HAS_REAL_INTEGRAL_SPIKE_FINITE_EQ = prove
 (`!f:real->real g s y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> ((f has_real_integral y) t <=> (g has_real_integral y) t)`,
  MESON_TAC[HAS_REAL_INTEGRAL_SPIKE_FINITE]);;

let REAL_INTEGRABLE_SPIKE_FINITE = prove
 (`!f:real->real g s.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> f real_integrable_on t
            ==> g real_integrable_on  t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_REAL_INTEGRAL_SPIKE_FINITE) THEN ASM_REWRITE_TAC[]);;

let REAL_NEGLIGIBLE_FRONTIER_INTERVAL = prove
 (`!a b:real. real_negligible(real_interval[a,b] DIFF real_interval(a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_interval; DIFF; IN_ELIM_THM] THEN
  MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{(a:real),b}` THEN
  ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_RULES] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

let HAS_REAL_INTEGRAL_SPIKE_INTERIOR = prove
 (`!f:real->real g a b y.
        (!x. x IN real_interval(a,b) ==> g x = f x) /\
        (f has_real_integral y) (real_interval[a,b])
        ==> (g has_real_integral y) (real_interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                           HAS_REAL_INTEGRAL_SPIKE) THEN
  EXISTS_TAC `real_interval[a:real,b] DIFF real_interval(a,b)` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_FRONTIER_INTERVAL] THEN ASM SET_TAC[]);;

let HAS_REAL_INTEGRAL_SPIKE_INTERIOR_EQ = prove
 (`!f:real->real g a b y.
        (!x. x IN real_interval(a,b) ==> g x = f x)
        ==> ((f has_real_integral y) (real_interval[a,b]) <=>
             (g has_real_integral y) (real_interval[a,b]))`,
  MESON_TAC[HAS_REAL_INTEGRAL_SPIKE_INTERIOR]);;

let REAL_INTEGRABLE_SPIKE_INTERIOR = prove
 (`!f:real->real g a b.
        (!x. x IN real_interval(a,b) ==> g x = f x)
        ==> f real_integrable_on (real_interval[a,b])
            ==> g real_integrable_on  (real_interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_REAL_INTEGRAL_SPIKE_INTERIOR) THEN ASM_REWRITE_TAC[]);;

let REAL_INTEGRAL_EQ = prove
 (`!f g s.
        (!x. x IN s ==> f x = g x) ==> real_integral s f = real_integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
  EXISTS_TAC `{}:real->bool` THEN
  ASM_SIMP_TAC[REAL_NEGLIGIBLE_EMPTY; IN_DIFF]);;

let REAL_INTEGRAL_EQ_0 = prove
 (`!f s. (!x. x IN s ==> f x = &0) ==> real_integral s f = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `real_integral s (\x. &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_INTEGRAL_0]]);;

let REAL_INTEGRABLE_CONTINUOUS = prove
 (`!f a b.
        f real_continuous_on real_interval[a,b]
        ==> f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[REAL_CONTINUOUS_ON; real_integrable_on; has_real_integral;
              GSYM integrable_on; GSYM EXISTS_LIFT] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; INTEGRABLE_CONTINUOUS]);;

let REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS = prove
 (`!f f' a b.
        a <= b /\
        (!x. x IN real_interval[a,b]
             ==> (f has_real_derivative f'(x))
                 (atreal x within real_interval[a,b]))
        ==> (f' has_real_integral (f(b) - f(a))) (real_interval[a,b])`,
  REWRITE_TAC[has_real_integral; HAS_REAL_VECTOR_DERIVATIVE_WITHIN] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_SUB] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE; LIFT_DROP] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o BINOP_CONV) [GSYM LIFT_DROP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let REAL_INTEGRABLE_SUBINTERVAL = prove
 (`!f:real->real a b c d.
        f real_integrable_on real_interval[a,b] /\
        real_interval[c,d] SUBSET real_interval[a,b]
        ==> f real_integrable_on real_interval[c,d]`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL] THEN
  REWRITE_TAC[EXISTS_DROP; GSYM integrable_on; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`lift a`; `lift b`] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
  ASM_SIMP_TAC[IMAGE_SUBSET]);;

let HAS_REAL_INTEGRAL_COMBINE = prove
 (`!f i j a b c.
        a <= c /\ c <= b /\
        (f has_real_integral i) (real_interval[a,c]) /\
        (f has_real_integral j) (real_interval[c,b])
        ==> (f has_real_integral (i + j)) (real_interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_INTEGRAL; LIFT_ADD] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMBINE THEN
  EXISTS_TAC `lift c` THEN ASM_REWRITE_TAC[LIFT_DROP]);;

let REAL_INTEGRAL_COMBINE = prove
 (`!f a b c.
        a <= c /\ c <= b /\ f real_integrable_on (real_interval[a,b])
        ==> real_integral(real_interval[a,c]) f +
            real_integral(real_interval[c,b]) f =
            real_integral(real_interval[a,b]) f`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_COMBINE THEN
  EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
  MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL; REAL_LE_REFL]);;

let REAL_INTEGRABLE_COMBINE = prove
 (`!f a b c.
        a <= c /\ c <= b /\
        f real_integrable_on real_interval[a,c] /\
        f real_integrable_on real_interval[c,b]
        ==> f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_COMBINE]);;

let REAL_INTEGRABLE_ON_LITTLE_SUBINTERVALS = prove
 (`!f:real->real a b.
        (!x. x IN real_interval[a,b]
             ==> ?d. &0 < d /\
                     !u v. x IN real_interval[u,v] /\
                           (!y. y IN real_interval[u,v]
                                ==> abs(y - x) < d /\ y IN real_interval[a,b])
                           ==> f real_integrable_on real_interval[u,v])
        ==> f real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL; EXISTS_DROP;
              GSYM integrable_on; LIFT_DROP] THEN
  DISCH_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_LITTLE_SUBINTERVALS THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM EXISTS_DROP; FORALL_LIFT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_IN_IMAGE_LIFT];
    REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:real^1` o REWRITE_RULE[SUBSET])) THEN
    ASM_SIMP_TAC[IN_BALL; FUN_IN_IMAGE; dist; NORM_REAL] THEN
    REWRITE_TAC[GSYM drop; DROP_SUB; LIFT_DROP] THEN SIMP_TAC[REAL_ABS_SUB]]);;

let REAL_INTEGRAL_HAS_REAL_DERIVATIVE_POINTWISE = prove
 (`!f a b x.
        f real_integrable_on real_interval[a,b] /\ x IN real_interval[a,b] /\
        f real_continuous (atreal x within real_interval[a,b])
        ==> ((\u. real_integral(real_interval[a,u]) f)
                   has_real_derivative f(x))
                 (atreal x within real_interval[a,b])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; IMAGE_LIFT_REAL_INTERVAL;
              REAL_INTEGRABLE_ON; CONTINUOUS_CONTINUOUS_WITHINREAL;
              HAS_REAL_VECTOR_DERIVATIVE_WITHIN] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; IN_IMAGE_LIFT_DROP; GSYM o_ASSOC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRAL_HAS_VECTOR_DERIVATIVE_POINTWISE) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT
    `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> d ==> e`]
     HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN) THEN
  EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
  X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN
  REWRITE_TAC[LIFT_DROP] THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[INTERVAL_REAL_INTERVAL; GSYM IMAGE_o; LIFT_DROP; o_DEF] THEN
  REWRITE_TAC[GSYM o_DEF; SET_RULE `IMAGE (\x. x) s = s`] THEN
  MATCH_MP_TAC REAL_INTEGRAL THEN
  MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
  REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC);;

let REAL_INTEGRAL_HAS_REAL_DERIVATIVE = prove
 (`!f:real->real a b.
     f real_continuous_on real_interval[a,b]
     ==> !x. x IN real_interval[a,b]
             ==> ((\u. real_integral(real_interval[a,u]) f)
                  has_real_derivative f(x))
                 (atreal x within real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRAL_HAS_REAL_DERIVATIVE_POINTWISE THEN
  ASM_MESON_TAC[REAL_INTEGRABLE_CONTINUOUS;
                REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]);;

let REAL_ANTIDERIVATIVE_CONTINUOUS = prove
 (`!f a b.
     (f real_continuous_on real_interval[a,b])
     ==> ?g. !x. x IN real_interval[a,b]
                 ==> (g has_real_derivative f(x))
                     (atreal x within real_interval[a,b])`,
  MESON_TAC[REAL_INTEGRAL_HAS_REAL_DERIVATIVE]);;

let REAL_ANTIDERIVATIVE_INTEGRAL_CONTINUOUS = prove
 (`!f a b.
     (f real_continuous_on real_interval[a,b])
     ==> ?g. !u v. u IN real_interval[a,b] /\
                   v IN real_interval[a,b] /\ u <= v
                   ==> (f has_real_integral (g(v) - g(u)))
                       (real_interval[u,v])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_ANTIDERIVATIVE_CONTINUOUS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real->real` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN
  STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `real_interval[a:real,b]` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let HAS_REAL_INTEGRAL_AFFINITY = prove
 (`!f:real->real i a b m c.
        (f has_real_integral i) (real_interval[a,b]) /\ ~(m = &0)
        ==> ((\x. f(m * x + c)) has_real_integral (inv(abs(m)) * i))
            (IMAGE (\x. inv m * (x - c)) (real_interval[a,b]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_INTEGRAL] THEN
  DISCH_THEN(MP_TAC o SPEC `lift c` o MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
  REWRITE_TAC[DIMINDEX_1; REAL_POW_1; has_real_integral] THEN
  REWRITE_TAC[o_DEF; DROP_ADD; DROP_CMUL; LIFT_DROP; LIFT_CMUL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[INTERVAL_REAL_INTERVAL; GSYM IMAGE_o; LIFT_DROP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_DEF; LIFT_CMUL; LIFT_SUB] THEN VECTOR_ARITH_TAC);;

let REAL_INTEGRABLE_AFFINITY = prove
 (`!f a b m c.
        f real_integrable_on real_interval[a,b] /\ ~(m = &0)
        ==> (\x. f(m * x + c)) real_integrable_on
            (IMAGE (\x. inv m * (x - c)) (real_interval[a,b]))`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_AFFINITY]);;

let HAS_REAL_INTEGRAL_STRETCH = prove
 (`!f:real->real i a b m.
        (f has_real_integral i) (real_interval[a,b]) /\ ~(m = &0)
        ==> ((\x. f(m * x)) has_real_integral (inv(abs(m)) * i))
            (IMAGE (\x. inv m * x) (real_interval[a,b]))`,
  MP_TAC HAS_REAL_INTEGRAL_AFFINITY THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[REAL_ADD_RID; REAL_SUB_RZERO]);;

let REAL_INTEGRABLE_STRETCH = prove
 (`!f a b m.
        f real_integrable_on real_interval[a,b] /\ ~(m = &0)
        ==> (\x. f(m * x)) real_integrable_on
            (IMAGE (\x. inv m * x) (real_interval[a,b]))`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_STRETCH]);;

let HAS_REAL_INTEGRAL_REFLECT_LEMMA = prove
 (`!f:real->real i a b.
     (f has_real_integral i) (real_interval[a,b])
     ==> ((\x. f(--x)) has_real_integral i) (real_interval[--b,--a])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_INTEGRAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_REFLECT_LEMMA) THEN
  REWRITE_TAC[LIFT_NEG; o_DEF; DROP_NEG]);;

let HAS_REAL_INTEGRAL_REFLECT = prove
 (`!f:real->real i a b.
     ((\x. f(--x)) has_real_integral i) (real_interval[--b,--a]) <=>
     (f has_real_integral i) (real_interval[a,b])`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_REFLECT_LEMMA) THEN
  REWRITE_TAC[REAL_NEG_NEG; ETA_AX]);;

let REAL_INTEGRABLE_REFLECT = prove
 (`!f:real->real a b.
     (\x. f(--x)) real_integrable_on (real_interval[--b,--a]) <=>
     f real_integrable_on (real_interval[a,b])`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL_REFLECT]);;

let REAL_INTEGRAL_REFLECT = prove
 (`!f:real->real a b.
     real_integral (real_interval[--b,--a]) (\x. f(--x)) =
     real_integral (real_interval[a,b]) f`,
  REWRITE_TAC[real_integral; HAS_REAL_INTEGRAL_REFLECT]);;

let HAS_REAL_INTEGRAL_REFLECT_GEN = prove
 (`!f i s. ((\x. f(--x)) has_real_integral i) s <=>
           (f has_real_integral i) (IMAGE (--) s)`,
  REWRITE_TAC[has_real_integral; o_DEF; GSYM DROP_NEG;
              HAS_INTEGRAL_REFLECT_GEN; GSYM IMAGE_o; GSYM LIFT_NEG]);;

let REAL_INTEGRABLE_REFLECT_GEN = prove
 (`!f s. (\x. f(--x)) real_integrable_on s <=>
         f real_integrable_on (IMAGE (--) s)`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL_REFLECT_GEN]);;

let REAL_INTEGRAL_REFLECT_GEN = prove
 (`!f s. real_integral s (\x. f(--x)) = real_integral (IMAGE (--) s) f`,
   REWRITE_TAC[real_integral; HAS_REAL_INTEGRAL_REFLECT_GEN]);;

let REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR = prove
 (`!f:real->real f' a b.
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b)
             ==> (f has_real_derivative f'(x)) (atreal x))
        ==> (f' has_real_integral (f(b) - f(a))) (real_interval[a,b])`,
  REWRITE_TAC[has_real_integral; HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_SUB] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE; LIFT_DROP] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o BINOP_CONV) [GSYM LIFT_DROP] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG = prove
 (`!f f' s a b.
        COUNTABLE s /\
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b) DIFF s
             ==> (f has_real_derivative f'(x)) (atreal x))
        ==> (f' has_real_integral (f(b) - f(a))) (real_interval[a,b])`,
  REWRITE_TAC[has_real_integral; HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_SUB] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE; IMP_CONJ; IN_DIFF] THEN
  SUBGOAL_THEN `!x. drop x IN s <=> x IN IMAGE lift s`
    (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `COUNTABLE s <=> COUNTABLE(IMAGE lift s)` SUBST1_TAC THENL
   [EQ_TAC THEN SIMP_TAC[COUNTABLE_IMAGE] THEN
    DISCH_THEN(MP_TAC o ISPEC `drop` o MATCH_MP COUNTABLE_IMAGE) THEN
    REWRITE_TAC[GSYM IMAGE_o; IMAGE_LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM IN_DIFF; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o BINOP_CONV)
   [GSYM LIFT_DROP] THEN
  DISCH_THEN(MP_TAC o
    MATCH_MP FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;
