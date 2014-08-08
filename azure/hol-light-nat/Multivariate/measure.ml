open Hol_core
open Products
open Floor
open Card
open Permutations
open Determinants
open Vectors
open Topology
open Convex
open Paths
open Polytope
open Dimension
open Derivatives
open Integration
include Measure3

(* ------------------------------------------------------------------------- *)
(* Measurability of a.e. derivatives.                                        *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_VECTOR_DERIVATIVE = prove
 (`!f:real^1->real^N f' s k.
        negligible k /\ negligible(frontier s) /\
        (!x. x IN (s DIFF k) ==> (f has_vector_derivative f'(x)) (at x))
        ==> f' measurable_on s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  ABBREV_TAC `g:real^1->real^N = \x. if x IN s then f(x) else vec 0` THEN
  SUBGOAL_THEN `(g:real^1->real^N) measurable_on (:real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[MEASURABLE_ON_UNIV] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE_SET) THEN
    EXISTS_TAC `s DIFF k:real^1->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `k:real^1->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
        MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
        ASM_MESON_TAC[differentiable; has_vector_derivative];
        MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN
        ASM_SIMP_TAC[NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE] THEN
        ASM_SIMP_TAC[LEBESGUE_MEASURABLE_JORDAN]]];
     ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
  EXISTS_TAC `\n x. (&n + &1) % (g(x + lift(inv(&n + &1))) - g(x):real^N)` THEN
  EXISTS_TAC `k UNION frontier s:real^1->bool` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC MEASURABLE_ON_CMUL THEN
    MATCH_MP_TAC MEASURABLE_ON_SUB THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
    REWRITE_TAC[MEASURABLE_ON_TRANSLATION_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
     `g measurable_on s ==> t = s ==> g measurable_on t`)) THEN
    MATCH_MP_TAC(SET_RULE
     `!g. (!x. f(g x) = x /\ g(f x) = x) ==> IMAGE f UNIV = UNIV`) THEN
    EXISTS_TAC `\x. --(lift(inv(&n + &1))) + x` THEN VECTOR_ARITH_TAC;

    X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_UNIV; IN_DIFF; IN_UNION; DE_MORGAN_THM; frontier;
                CLOSURE_INTERIOR] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `d:real` THEN ASM_SIMP_TAC[DIST_REFL] THEN STRIP_TAC THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THENL
     [EXISTS_TAC `(\n. vec 0):num->real^N`;
      EXISTS_TAC `(\n. (&n + &1) % (f(x + lift (inv (&n + &1))) - f x))
                  :num->real^N`] THEN
    (CONJ_TAC THENL
      [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
       MP_TAC(SPEC `d:real` REAL_ARCH_INV) THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
       X_GEN_TAC `N:num` THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
       DISCH_TAC THEN
       SUBGOAL_THEN `dist(x,x + lift(inv(&n + &1))) < d` ASSUME_TAC THENL
        [REWRITE_TAC[NORM_ARITH `dist(a:real^N,a + x) = norm x`] THEN
         REWRITE_TAC[NORM_LIFT; REAL_ABS_INV] THEN
         REWRITE_TAC[REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
         MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&N)` THEN
         ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
         ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
         EXPAND_TAC "g" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[DIST_REFL] THEN
         VECTOR_ARITH_TAC];
       ALL_TAC]) THEN
     REWRITE_TAC[LIM_CONST] THEN
     UNDISCH_THEN
      `!x. x IN s DIFF k
           ==> ((f:real^1->real^N) has_vector_derivative f' x) (at x)`
      (MP_TAC o SPEC `x:real^1`) THEN
     ASM_SIMP_TAC[IN_DIFF; DIST_REFL; has_vector_derivative] THEN
     REWRITE_TAC[has_derivative; NETLIMIT_AT] THEN
     DISCH_THEN(MP_TAC o CONJUNCT2) THEN
     REWRITE_TAC[LIM_AT; LIM_SEQUENTIALLY] THEN DISCH_TAC THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
     MP_TAC(SPEC `k:real` REAL_ARCH_INV) THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
     X_GEN_TAC `N:num` THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
     DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `x +  lift(inv(&n + &1))` o CONJUNCT2) THEN
     REWRITE_TAC[NORM_ARITH `dist(x + a:real^N,x) = norm a`] THEN
     REWRITE_TAC[NORM_LIFT; REAL_ABS_INV; REAL_ARITH `abs(&n + &1) = &n + &1`;
              VECTOR_ARITH `(x + e) - x:real^N = e`; LIFT_DROP] THEN
     ANTS_TAC THENL
      [REWRITE_TAC[REAL_LT_INV_EQ] THEN
       CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_TRANS] THEN
       EXISTS_TAC `inv(&N)` THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
       ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
       MATCH_MP_TAC(NORM_ARITH
        `x - y:real^N = z ==> dist(z,vec 0) < e ==> dist(x,y) < e`) THEN
       REWRITE_TAC[REAL_INV_INV; VECTOR_SUB_LDISTRIB; VECTOR_ADD_LDISTRIB] THEN
       SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID;
                REAL_ARITH `~(&n + &1 = &0)`] THEN
       VECTOR_ARITH_TAC]]);;

let ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_INTER = prove
 (`!f:real^M->real^N s t.
        f absolutely_integrable_on s /\ lebesgue_measurable t
        ==> f absolutely_integrable_on (s INTER t)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC
    MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC
   `\x. lift(norm(if x IN s then (f:real^M->real^N) x else vec 0))` THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM; IN_UNIV; IN_INTER;
               ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[MESON[]
   `(if p /\ q then x else y) = if q then if p then x else y else y`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_CASES THEN
    ASM_REWRITE_TAC[SET_RULE `{x | x IN s} = s`; MEASURABLE_ON_0] THEN
    ASM_SIMP_TAC[INTEGRABLE_IMP_MEASURABLE;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `(x:real^M) IN t` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; LIFT_DROP; NORM_0; NORM_POS_LE]]);;

let ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_SUBSET = prove
 (`!f:real^M->real^N s t.
        f absolutely_integrable_on s /\ t SUBSET s /\ lebesgue_measurable t
        ==> f absolutely_integrable_on t`,
  MESON_TAC[ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_INTER;
            SET_RULE `s SUBSET t ==> s = t INTER s`]);;

(* ------------------------------------------------------------------------- *)
(* Approximation of L_1 functions by bounded continuous ones.                *)
(* Note that 100/fourier.ml has some generalizations to L_p spaces.          *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS = prove
 (`!f:real^M->real^N s e.
        lebesgue_measurable s /\ f absolutely_integrable_on s /\ &0 < e
        ==> ?g. g absolutely_integrable_on s /\
                g continuous_on (:real^M) /\
                bounded (IMAGE g (:real^M)) /\
                norm(integral s (\x. lift(norm(f x - g x)))) < e`,
  let lemma = prove
   (`!f:real^M->real^N s e.
          measurable s /\ f absolutely_integrable_on s /\ &0 < e
          ==> ?g. g absolutely_integrable_on s /\
                  g continuous_on (:real^M) /\
                  bounded (IMAGE g (:real^M)) /\
                  norm(integral s (\x. lift(norm(f x - g x)))) < e`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `?h. h absolutely_integrable_on s /\
           bounded (IMAGE h (:real^M)) /\
           norm(integral s (\x. lift(norm(f x - h x:real^N)))) < e / &2`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`\n x. lift(norm
         (f x - (lambda i. max (--(&n))
                             (min (&n) ((f:real^M->real^N)(x)$i)))))`;
        `(\x. vec 0):real^M->real^1`;
        `\x. lift(norm((f:real^M->real^N)(x)))`;
        `s:real^M->bool`]
            DOMINATED_CONVERGENCE) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `!n. ((\x. lambda i. max (--(&n)) (min (&n) ((f x:real^N)$i)))
            :real^M->real^N) absolutely_integrable_on s`
      ASSUME_TAC THENL
       [GEN_TAC THEN
        FIRST_ASSUM(MP_TAC o SPEC `(\x. lambda i. &n):real^M->real^N` o
          MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] ABSOLUTELY_INTEGRABLE_MIN)) THEN
        ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_ON_CONST] THEN
        DISCH_THEN(MP_TAC o SPEC `(\x. lambda i. --(&n)):real^M->real^N` o
          MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] ABSOLUTELY_INTEGRABLE_MAX)) THEN
        ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_ON_CONST] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
        SIMP_TAC[CART_EQ; LAMBDA_BETA];
        ALL_TAC] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [X_GEN_TAC `n:num` THEN
          MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
          MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
          ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_SUB];
          ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM;
                       ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
          MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN DISCH_TAC THEN
          REWRITE_TAC[LIFT_DROP; NORM_LIFT; REAL_ABS_NORM] THEN
          MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
          SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
          X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
          REWRITE_TAC[LIM_SEQUENTIALLY] THEN
          X_GEN_TAC `d:real` THEN DISCH_TAC THEN
          MP_TAC(SPEC `norm((f:real^M->real^N) x)` REAL_ARCH_SIMPLE) THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
          DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
          REWRITE_TAC[DIST_0; NORM_LIFT; REAL_ABS_NORM; GSYM LIFT_SUB] THEN
          MATCH_MP_TAC(NORM_ARITH
           `&0 < d /\ x = y ==> norm(x:real^N - y) < d`) THEN
          ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC(REAL_ARITH
            `abs(x) <= n ==> x = max (--n) (min n x)`) THEN
          ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS; REAL_OF_NUM_LE]];
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN
        DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
        REWRITE_TAC[INTEGRAL_0; DIST_0; LE_REFL] THEN DISCH_TAC THEN
        EXISTS_TAC `(\x. lambda i. max (--(&n)) (min (&n)
                               ((f:real^M->real^N)(x)$i))):real^M->real^N` THEN
        ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[BOUNDED_COMPONENTWISE] THEN
        REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXISTS_TAC `&n` THEN
        X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[NORM_LIFT; LAMBDA_BETA] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?k g. negligible k /\
            (!n. g n continuous_on (:real^M)) /\
            (!n x. norm(g n x:real^N) <= norm(B % vec 1:real^N)) /\
            (!x. x IN (s DIFF k)  ==> ((\n. g n x) --> h x) sequentially)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(h:real^M->real^N) measurable_on s` MP_TAC THENL
       [ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE]; ALL_TAC] THEN
      REWRITE_TAC[measurable_on] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `k:real^M->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `g:num->real^M->real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(\n x. lambda i. max (--B) (min B (((g n x):real^N)$i))):
                  num->real^M->real^N` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `n:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
        MP_TAC(ISPECL [`(:real^M)`; `(lambda i. B):real^N`]
                  CONTINUOUS_ON_CONST) THEN
        REWRITE_TAC[IMP_IMP] THEN
        DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_MIN) THEN
        MP_TAC(ISPECL [`(:real^M)`; `(lambda i. --B):real^N`]
                  CONTINUOUS_ON_CONST) THEN
        REWRITE_TAC[IMP_IMP] THEN
        DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_MAX) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
        SIMP_TAC[LAMBDA_BETA; VEC_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[LIM_SEQUENTIALLY] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `ee:real` THEN
        MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
        MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC(NORM_ARITH
         `norm(c - a:real^N) <= norm(b - a)
          ==> dist(b,a) < ee ==> dist(c,a) < ee`) THEN
        MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
        SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT] THEN
        X_GEN_TAC `k:num` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP NORM_BOUND_COMPONENT_LE) THEN
        DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. (g:num->real^M->real^N) n absolutely_integrable_on s`
    ASSUME_TAC THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC
        MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
      EXISTS_TAC `(\x. lift(norm(B % vec 1:real^N))):real^M->real^1` THEN
      ASM_REWRITE_TAC[LIFT_DROP; INTEGRABLE_ON_CONST] THEN
      ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
      MATCH_MP_TAC(REWRITE_RULE[lebesgue_measurable; indicator]
          MEASURABLE_ON_RESTRICT) THEN
      ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON; ETA_AX] THEN
      MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
      ASM_REWRITE_TAC[GSYM MEASURABLE_INTEGRABLE];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\n x. lift(norm((g:num->real^M->real^N) n x - h x))`;
      `(\x. vec 0):real^M->real^1`;
      `(\x. lift(B + norm(B % vec 1:real^N))):real^M->real^1`;
      `s DIFF k:real^M->bool`] DOMINATED_CONVERGENCE) THEN
    ASM_SIMP_TAC[INTEGRAL_0; INTEGRABLE_ON_CONST; MEASURABLE_DIFF;
                 NEGLIGIBLE_IMP_MEASURABLE] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NORM_LIFT; REAL_ABS_NORM] THEN REPEAT CONJ_TAC THENL
       [GEN_TAC THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
        EXISTS_TAC `s:real^M->bool` THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM;
                     ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
                     ABSOLUTELY_INTEGRABLE_SUB; ETA_AX] THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
        MATCH_MP_TAC(NORM_ARITH
         `norm(g:real^N) <= b /\ norm(h) <= a ==> norm(g - h) <= a + b`) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[GSYM LIM_NULL_NORM; GSYM LIM_NULL]];
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
      REWRITE_TAC[LE_REFL; DIST_0] THEN DISCH_TAC THEN
      EXISTS_TAC `(g:num->real^M->real^N) n` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm(integral s (\x. lift(norm(f x - h x)))) +
       norm(integral s (\x. lift(norm
             ((g:num->real^M->real^N) n x - h x))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(NORM_ARITH
         `norm(x:real^N) <= norm(y + z:real^N)
          ==> norm(x) <= norm(y) + norm(z)`) THEN
        W(MP_TAC o PART_MATCH (lhs o rand) (GSYM INTEGRAL_ADD) o
           rand o rand o snd) THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
                 ABSOLUTELY_INTEGRABLE_SUB; ETA_AX] THEN
        DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(MESON[]
         `norm x = drop x /\ norm(a:real^N) <= drop x
          ==> norm a <= norm x`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC NORM_1_POS THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
          SIMP_TAC[DROP_ADD; LIFT_DROP; NORM_POS_LE; REAL_LE_ADD] THEN
          MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC;
          MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
          REWRITE_TAC[DROP_ADD; LIFT_DROP; NORM_LIFT; REAL_ABS_NORM] THEN
          REWRITE_TAC[NORM_ARITH
           `norm(f - g:real^N) <= norm(f - h) + norm(g - h)`] THEN
          CONJ_TAC THENL
           [ALL_TAC; MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC]] THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM;
                     ABSOLUTELY_INTEGRABLE_SUB; ETA_AX];
        MATCH_MP_TAC(REAL_ARITH `a < e / &2 /\ b < e / &2 ==> a + b < e`) THEN
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
          (REAL_ARITH `x < e ==> x = y ==> y < e`)) THEN AP_TERM_TAC THEN
        MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(!u v. f absolutely_integrable_on (s INTER interval[u,v])) /\
    (!u v. (f:real^M->real^N) absolutely_integrable_on (s DIFF interval[u,v]))`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_INTER;
                 LEBESGUE_MEASURABLE_INTERVAL; LEBESGUE_MEASURABLE_DIFF;
                 LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a b. norm(integral (s INTER interval[a,b]) (\x. lift(norm(f x))) -
               integral s (\x. lift(norm((f:real^M->real^N) x)))) < e / &3`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [absolutely_integrable_on]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[HAS_INTEGRAL_INTEGRAL] THEN
    REWRITE_TAC[HAS_INTEGRAL_ALT; INTEGRAL_RESTRICT_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &3` o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[BOUNDED_SUBSET_CLOSED_INTERVAL; BOUNDED_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`; `s INTER interval[a:real^M,b]`; `e / &3`]
        lemma) THEN
  ASM_SIMP_TAC[MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE;
               MEASURABLE_INTERVAL; REAL_ARITH `&0 < e / &3 <=> &0 < e`] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?c d. interval[a:real^M,b] SUBSET interval(c,d) /\
          measure(interval(c,d)) - measure(interval[a,b]) < e / &3 / B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^M`; `b:real^M`;
                   `e / &3 / B / &2`]
        EXPAND_CLOSED_OPEN_INTERVAL) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; REAL_ARITH `&0 < &3`] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < e ==> x <= y + e / &2 ==> x - y < e`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &3`];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. if x IN interval[a,b] then (g:real^M->real^N) x else vec 0`;
    `(:real^M)`;
    `interval[a,b] UNION ((:real^M) DIFF interval(c,d))`;
    `B:real`] TIETZE) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; IN_UNIV] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; FORALL_IN_UNION] THEN
    SIMP_TAC[CLOSED_UNION; CLOSED_INTERVAL; GSYM OPEN_CLOSED; OPEN_INTERVAL;
             IN_DIFF; IN_UNIV] THEN
    ASM_SIMP_TAC[COND_RAND; NORM_0; COND_RATOR; REAL_LT_IMP_LE; COND_ID] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    SIMP_TAC[CLOSED_INTERVAL; GSYM OPEN_CLOSED; OPEN_INTERVAL] THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ASM SET_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^M->real^N`] THEN
  REWRITE_TAC[FORALL_IN_UNION; bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
    EXISTS_TAC `\x. if x IN s INTER interval(c,d)
                    then (h:real^M->real^N) x else vec 0` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_INTER] THEN
    MATCH_MP_TAC
      MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `(\x. lift B):real^M->real^1` THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST; LIFT_DROP] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_CASES THEN
      ASM_REWRITE_TAC[SET_RULE `{x | x IN s} = s`; MEASURABLE_ON_0] THEN
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      REWRITE_TAC[LEBESGUE_MEASURABLE_INTERVAL] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      REWRITE_TAC[INTEGRABLE_ON_OPEN_INTERVAL; INTEGRABLE_CONST];
      GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0; REAL_LT_IMP_LE]];
    DISCH_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!u v. h absolutely_integrable_on (s INTER interval[u,v])) /\
    (!u v. (h:real^M->real^N) absolutely_integrable_on (s DIFF interval[u,v]))`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_INTER;
                 LEBESGUE_MEASURABLE_INTERVAL; LEBESGUE_MEASURABLE_DIFF;
                 LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
    `norm(integral (s INTER interval[a,b])
                   (\x. lift(norm((f:real^M->real^N) x - h x)))) +
     norm(integral (s DIFF interval[a,b])
                   (\x. lift(norm(f x - h x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `a + b:real^N = c ==> norm(c) <= norm(a) + norm(b)`) THEN
    W(MP_TAC o PART_MATCH (rand o rand) INTEGRAL_UNION o lhand o snd) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM; ABSOLUTELY_INTEGRABLE_SUB;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; SET_RULE
     `(s INTER t) INTER (s DIFF t) = {} /\
      (s INTER t) UNION (s DIFF t) = s`] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
   `norm(integral s f) < e / &3
    ==> integral s f = integral s g /\
        y < &2 / &3 * e ==> norm(integral s g) + y < e`)) THEN
  CONJ_TAC THENL [MATCH_MP_TAC INTEGRAL_EQ THEN ASM SET_TAC[]; ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
    `drop(integral (s DIFF interval[a,b])
                   (\x. lift(norm((f:real^M->real^N) x)) +
                        lift(norm(h x:real^N))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM; ABSOLUTELY_INTEGRABLE_SUB;
                 ABSOLUTELY_INTEGRABLE_ADD; LIFT_DROP; DROP_ADD; NORM_LIFT;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    CONV_TAC NORM_ARITH;
    ASM_SIMP_TAC[INTEGRAL_ADD; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
                 ABSOLUTELY_INTEGRABLE_NORM; DROP_ADD]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x < e / &3 ==> z = x /\ y <= e / &3 ==> z + y < &2 / &3 * e`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN
    MATCH_MP_TAC(REAL_ARITH
     `z + y = x /\ &0 <= y ==> y = abs(z - x)`) THEN
    ASM_SIMP_TAC[INTEGRAL_DROP_POS; LIFT_DROP; NORM_POS_LE;
                  ABSOLUTELY_INTEGRABLE_NORM;
                  ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[GSYM DROP_ADD; DROP_EQ] THEN
    W(MP_TAC o PART_MATCH (rand o rand) INTEGRAL_UNION o lhand o snd) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; SET_RULE
     `(s INTER t) INTER (s DIFF t) = {} /\
      (s INTER t) UNION (s DIFF t) = s`]  THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `drop(integral (interval(c,d) DIFF interval[a,b]) (\x:real^M. lift B))` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; IN_UNIV] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM; INTEGRABLE_ON_CONST;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTERVAL] THEN
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_DIFF] THEN
    ASM_CASES_TAC `x IN interval(c:real^M,d)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `x IN interval[a:real^M,b]` THEN ASM_REWRITE_TAC[] THEN
    REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL; LIFT_DROP; NORM_0; REAL_LT_IMP_LE;
                 DROP_VEC] THEN
    ASM_MESON_TAC[IN_DIFF; IN_UNIV; NORM_0; REAL_LE_REFL];
    SIMP_TAC[LIFT_EQ_CMUL; INTEGRAL_CMUL; INTEGRABLE_ON_CONST;
             MEASURABLE_DIFF; MEASURABLE_INTERVAL; INTEGRAL_MEASURE] THEN
    REWRITE_TAC[DROP_CMUL; DROP_VEC; REAL_MUL_RID] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> y = x ==> y <= e`)) THEN
    MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
    ASM_REWRITE_TAC[MEASURABLE_INTERVAL]]);;

(* ------------------------------------------------------------------------- *)
(* Luzin's theorem (Talvila and Loeb's proof from Marius Junge's notes).     *)
(* ------------------------------------------------------------------------- *)

let LUZIN = prove
 (`!f:real^M->real^N s e.
        measurable s /\ f measurable_on s /\ &0 < e
        ==> ?k. compact k /\ k SUBSET s /\
                measure(s DIFF k) < e /\ f continuous_on k`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `v:num->real^N->bool` STRIP_ASSUME_TAC
    UNIV_SECOND_COUNTABLE_SEQUENCE THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`]
        MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`]
        MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. ?k k'.
        compact k /\ k SUBSET {x | x IN s /\ (f:real^M->real^N) x IN v n} /\
        compact k' /\ k' SUBSET {x | x IN s /\ f x IN ((:real^N) DIFF v n)} /\
        measure(s DIFF (k UNION k')) < e / &4 / &2 pow n`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`{x:real^M | x IN s /\ f(x) IN (v:num->real^N->bool) n}`;
                   `e / &4 / &2 / &2 pow n`] MEASURABLE_INNER_COMPACT) THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LT; ARITH; REAL_LT_DIV; REAL_LT_POW2] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`{x:real^M | x IN s /\ f(x) IN (:real^N) DIFF v(n:num)}`;
                   `e / &4 / &2 / &2 pow n`] MEASURABLE_INNER_COMPACT) THEN
    ASM_SIMP_TAC[GSYM OPEN_CLOSED; REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT;
                 ARITH] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k':real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
     `measure(({x | x IN s /\ (f:real^M->real^N) x IN v n} DIFF k) UNION
              ({x | x IN s /\ f x IN ((:real^N) DIFF v(n:num))} DIFF k'))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_UNION; MEASURABLE_COMPACT;
                   GSYM OPEN_CLOSED] THEN SET_TAC[];
      ASM_SIMP_TAC[MEASURE_UNION; MEASURABLE_DIFF; MEASURABLE_COMPACT;
                   GSYM OPEN_CLOSED; MEASURE_DIFF_SUBSET] THEN
      MATCH_MP_TAC(REAL_ARITH
       `s < k + e / &4 / &2 / d /\ s' < k' + e / &4 / &2 / d /\ m = &0
        ==> (s - k) + (s' - k') - m < e / &4 / d`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[MEASURE_EMPTY]
       `s = {} ==> measure s = &0`) THEN SET_TAC[]];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; IN_DIFF; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`k:num->real^M->bool`; `k':num->real^M->bool`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  EXISTS_TAC `INTERS {k n UNION k' n | n IN (:num)} :real^M->bool` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_INTERS THEN
    ASM_SIMP_TAC[FORALL_IN_GSPEC; COMPACT_UNION] THEN SET_TAC[];
    REWRITE_TAC[INTERS_GSPEC] THEN ASM SET_TAC[];
    REWRITE_TAC[DIFF_INTERS; SET_RULE
     `{f y | y IN {g x | x IN s}} = {f(g x) | x IN s}`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC
     (MESON[] `measurable s /\ measure s <= b ==> measure s <= b`) THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE THEN
    ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_UNION; MEASURABLE_COMPACT] THEN
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\i. e / &4 / &2 pow i)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_LE_NUMSEG; REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[real_div; SUM_LMUL; REAL_LE_LMUL_EQ; REAL_ARITH
     `(e * inv(&4)) * s <= e * inv(&2) <=> e * s <= e * &2`] THEN
    REWRITE_TAC[REAL_INV_POW; SUM_GP; LT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_ARITH
     `(&1 - s) / (&1 / &2) <= &2 <=> &0 <= s`] THEN
    MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV;

    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_OPEN; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?n:num. (f:real^M->real^N)(x) IN v(n) /\ v(n) SUBSET t`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_THEN
       `!s. open s ==> (?k. s:real^N->bool = UNIONS {v(n:num) | n IN k})`
       (MP_TAC o SPEC `t:real^N->bool`) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; UNIONS_GSPEC] THEN ASM SET_TAC[];
      EXISTS_TAC `(:real^M) DIFF k'(n:num)` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN ASM SET_TAC[]]]);;

let LUZIN_EQ,LUZIN_EQ_ALT = (CONJ_PAIR o prove)
 (`(!f:real^M->real^N s.
        measurable s
        ==> (f measurable_on s <=>
             !e. &0 < e
                 ==> ?k. compact k /\ k SUBSET s /\
                         measure(s DIFF k) < e /\ f continuous_on k)) /\
   (!f:real^M->real^N s.
        measurable s
        ==> (f measurable_on s <=>
             !e. &0 < e
                 ==> ?k g. compact k /\ k SUBSET s /\
                           measure(s DIFF k) < e /\
                           g continuous_on (:real^M) /\
                           (!x. x IN k ==> g x = f x)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `measurable(s:real^M->bool)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (q ==> r) /\ (r ==> p) ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[LUZIN];
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TIETZE_UNBOUNDED THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; SUBTOPOLOGY_UNIV; GSYM CLOSED_IN];
    DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&2 pow n)`) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num->real^M->bool`; `g:num->real^M->real^N`] THEN
    STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN MAP_EVERY EXISTS_TAC
     [`g:num->real^M->real^N`;
      `s DIFF UNIONS {INTERS {k m | n <= m} | n IN (:num)}:real^M->bool`] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_MESON_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; CONTINUOUS_ON_SUBSET;
                    SUBSET_UNIV];
      SIMP_TAC[DIFF_UNIONS_NONEMPTY; SET_RULE `~({f x | x IN UNIV} = {})`] THEN
      REWRITE_TAC[NEGLIGIBLE_OUTER] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`inv(&2)`; `e / &4`] REAL_ARCH_POW_INV) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_POW_INV]] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s DIFF INTERS {k m | n:num <= m}:real^M->bool` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[INTERS_GSPEC; FORALL_IN_GSPEC] THEN ASM SET_TAC[];
        MATCH_MP_TAC MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MEASURABLE_COUNTABLE_INTERS_GEN THEN
        ASM_SIMP_TAC[FORALL_IN_GSPEC; MEASURABLE_COMPACT] THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[LE_REFL]] THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
        MATCH_MP_TAC COUNTABLE_IMAGE THEN
        MESON_TAC[NUM_COUNTABLE; COUNTABLE_SUBSET; SUBSET_UNIV];
        REWRITE_TAC[DIFF_INTERS] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC
         (MESON[] `measurable s /\ measure s <= b ==> measure s <= b`) THEN
        MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_GEN THEN
        ASM_SIMP_TAC[FORALL_IN_GSPEC; MEASURABLE_COMPACT; MEASURABLE_DIFF] THEN
        CONJ_TAC THENL
         [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
          MATCH_MP_TAC COUNTABLE_IMAGE THEN
          REWRITE_TAC[SET_RULE `{x | x IN s} = s`] THEN
          ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
          MATCH_MP_TAC COUNTABLE_IMAGE THEN
          MESON_TAC[NUM_COUNTABLE; COUNTABLE_SUBSET; SUBSET_UNIV];
          REWRITE_TAC[SIMPLE_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
          REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
          ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
          REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
          X_GEN_TAC `ns:num->bool` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN
          W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_LE o lhand o snd) THEN
          ASM_SIMP_TAC[o_DEF; MEASURE_POS_LE; MEASURABLE_DIFF;
                       MEASURABLE_COMPACT] THEN
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
          FIRST_ASSUM(MP_TAC o SPEC `\x:num. x` o
            MATCH_MP UPPER_BOUND_FINITE_SET) THEN
          REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `m:num` THEN
          STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `sum (n..m) (\i. measure(s DIFF k i:real^M->bool))` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
            ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_DIFF; MEASURABLE_COMPACT;
                         FINITE_NUMSEG; SUBSET; IN_NUMSEG];
            ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `sum (n..m) (\i. inv(&2 pow i))` THEN
          ASM_SIMP_TAC[SUM_LE_NUMSEG; REAL_LT_IMP_LE] THEN
          REWRITE_TAC[REAL_INV_POW; SUM_GP; LT] THEN
          COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC(REAL_ARITH
           `a <= e / &4 /\ &0 <= b
            ==> (a - b) / (&1 / &2) <= e / &2`) THEN
          REWRITE_TAC[real_div; REAL_MUL_LID; REAL_POW_INV] THEN
          ASM_SIMP_TAC[GSYM real_div; REAL_LT_IMP_LE; REAL_LE_INV_EQ;
                       REAL_LT_POW2]]];
      REWRITE_TAC[SET_RULE `s DIFF (s DIFF t) = s INTER t`] THEN
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[UNIONS_GSPEC; IN_INTER] THEN
      REWRITE_TAC[IN_UNIV; IN_ELIM_THM; INTERS_GSPEC] THEN
      STRIP_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Egorov's thoerem.                                                         *)
(* ------------------------------------------------------------------------- *)

let EGOROV = prove
 (`!f:num->real^M->real^N g s t.
        measurable s /\ negligible t /\
        (!n. f n measurable_on s) /\ g measurable_on s /\
        (!x. x IN s DIFF t ==> ((\n. f n x) --> g x) sequentially)
        ==> !d. &0 < d
                ==> ?k. k SUBSET s /\ measurable k /\ measure k < d /\
                        !e. &0 < e
                            ==> ?N. !n x. N <= n /\ x IN s DIFF k
                                          ==> dist(f n x,g x) < e`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `e = \n m. UNIONS{{x | x IN s /\
                                    dist((f:num->real^M->real^N) k x,g x)
                                      >= inv(&m + &1)} | n <= k}` THEN
  SUBGOAL_THEN
   `!m n. measurable ((e:num->num->real^M->bool) n m)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MATCH_MP_TAC MEASURABLE_LEGESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "e" THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN SET_TAC[]] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_SUBSET_NUM; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_ARITH
     `dist(a:real^M,b) >= e <=> ~(dist(vec 0,a - b) < e)`] THEN
    REWRITE_TAC[GSYM IN_BALL; SET_RULE `~(x IN s) <=> x IN UNIV DIFF s`] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED THEN
    ASM_SIMP_TAC[GSYM OPEN_CLOSED; OPEN_BALL;
                 MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
    MATCH_MP_TAC MEASURABLE_ON_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE_SET) THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[ETA_AX] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     NEGLIGIBLE_SUBSET)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. ?k. measure((e:num->num->real^M->bool) k m) < d / &2 pow (m + 2)`
  MP_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPEC
      `\n. (e:num->num->real^M->bool) n m` HAS_MEASURE_NESTED_INTERS) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "e" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_UNIONS THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      ARITH_TAC;
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)] THEN
    SUBGOAL_THEN
     `measure (INTERS {(e:num->num->real^M->bool) n m | n IN (:num)}) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MEASURE_EQ_0 THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `t:real^M->bool` THEN
      ASM_REWRITE_TAC[INTERS_GSPEC; SUBSET; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `x:real^M` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
      ASM_CASES_TAC `(x:real^M) IN t` THEN ASM_REWRITE_TAC[IN_DIFF] THEN
      EXPAND_TAC "e" THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_DIFF] THEN
      ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; NOT_FORALL_THM; NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `inv(&m + &1)`) THEN
      REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &m + &1`] THEN
      REWRITE_TAC[DE_MORGAN_THM; real_ge; REAL_NOT_LE] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; LIFT_NUM; DIST_0; NORM_LIFT] THEN
    DISCH_THEN(MP_TAC o SPEC `d / &2 pow (m + 2)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_POW2] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_THEN(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:num->num` THEN DISCH_TAC] THEN
  EXISTS_TAC `UNIONS {(e:num->num->real^M->bool) (k m) m | m IN (:num)}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\m. (e:num->num->real^M->bool) (k m) m`; `d / &2`]
        MEASURE_COUNTABLE_UNIONS_LE) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `n:num`;
      ASM_MESON_TAC[REAL_ARITH `&0 < d /\ x <= d / &2 ==> x < d`]] THEN
    TRANS_TAC REAL_LE_TRANS `sum(0..n) (\m. d / &2 pow (m + 2))` THEN
    ASM_SIMP_TAC[SUM_LE_NUMSEG; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_POW; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[SUM_RMUL; SUM_LMUL; SUM_GP; CONJUNCT1 LT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x ==> (&1 - x) / (&1 / &2) * &1 / &4 <= &1 / &2`) THEN
    MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV;

    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN EXISTS_TAC `(k:num->num) m` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM; IN_UNIV] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
    ASM_REWRITE_TAC[REAL_NOT_LE; real_ge] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
     MATCH_MP (REAL_ARITH `i < e ==> m <= i ==> d < m ==> d < e`)) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A kind of absolute continuity of the integral.                            *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_CONTINUOUS_INTEGRAL = prove
 (`!f:real^M->real^N s e.
        f absolutely_integrable_on s /\ &0 < e
        ==> ?d. &0 < d /\
                !t. t SUBSET s /\ measurable t /\ measure t < d
                    ==> norm(integral t f) < e`,
  ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. if x IN s then (f:real^M->real^N) x else vec 0`;
    `(:real^M)`; `e / &2`]
   ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &2 / B` THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF] THEN
  X_GEN_TAC `t:real^M->bool` THEN STRIP_TAC THEN
  TRANS_TAC REAL_LET_TRANS
   `drop(integral t (\x. lift(norm((if x IN s then f x else vec 0) - g x)) +
                         lift(norm((g:real^M->real^N) x))))` THEN

  SUBGOAL_THEN
   `(g:real^M->real^N) absolutely_integrable_on t /\
    (\x. if x IN s then (f:real^M->real^N) x else vec 0)
    absolutely_integrable_on t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^M)` THEN
    ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N) absolutely_integrable_on t` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        ABSOLUTELY_INTEGRABLE_EQ)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
     [ABSOLUTELY_INTEGRABLE_NORM; ABSOLUTELY_INTEGRABLE_ADD;
      ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_SUB] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP; DROP_ADD] THEN
    COND_CASES_TAC THENL [CONV_TAC NORM_ARITH; ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [ABSOLUTELY_INTEGRABLE_NORM; INTEGRAL_ADD; DROP_ADD;
    ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `x < e / &2 /\ y < e / &2 ==> x + y < e`) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `norm(integral s (f:real^M->real^1)) < e / &2
      ==> drop(integral t f) <= norm(integral s f)
           ==> drop(integral t f) < e / &2`)) THEN
    REWRITE_TAC[NORM_REAL; GSYM drop] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM; IN_UNIV; SUBSET_UNIV; LIFT_DROP;
     ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_SUB] THEN
    REWRITE_TAC[NORM_POS_LE];

    TRANS_TAC REAL_LET_TRANS `drop(integral t (\x:real^M. lift B))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC[LIFT_DROP; ABSOLUTELY_INTEGRABLE_NORM; INTEGRABLE_ON_CONST;
                   ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      ASM_SIMP_TAC[LIFT_EQ_CMUL; INTEGRAL_CMUL; INTEGRABLE_ON_CONST;
                   INTEGRAL_MEASURE] THEN
      REWRITE_TAC[DROP_CMUL; DROP_VEC; REAL_MUL_RID] THEN
     ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
     ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]]]);;

(* ------------------------------------------------------------------------- *)
(* Convergence in measure implies convergence AE of a subsequence.           *)
(* ------------------------------------------------------------------------- *)

let CONVERGENCE_IN_MEASURE = prove
 (`!f:num->real^M->real^N g s.
        (!n. f n measurable_on s) /\
        (!e. &0 < e
             ==> eventually
                  (\n. ?t. {x | x IN s /\ dist(f n x,g x) >= e} SUBSET t /\
                           measurable t /\ measure t < e)
                  sequentially)
        ==> ?r t. (!m n:num. m < n ==> r m < r n) /\
                  negligible t /\ t SUBSET s /\
                  !x. x IN s DIFF t
                      ==> ((\n. f (r n) x) --> g x) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?r. (!n. ?t. {x | x IN s /\ dist(f (r n) x,(g:real^M->real^N) x)
                                >= inv(&2 pow n)} SUBSET t /\
                      measurable t /\ measure t < inv(&2 pow n)) /\
        (!n. r n :num < r(SUC n))`
  MP_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `&1`);
      MAP_EVERY X_GEN_TAC [`n:num`; `p:num`] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `inv(&2 pow (SUC n))`)] THEN
    ASM_REWRITE_TAC[REAL_LT_01; REAL_LT_INV_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THENL
     [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
      DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LE_REFL];
      DISCH_THEN(X_CHOOSE_THEN `m:num` (MP_TAC o SPEC `m + p + 1:num`)) THEN
      DISCH_THEN(fun th -> EXISTS_TAC `m + p + 1:num` THEN MP_TAC th) THEN
      REWRITE_TAC[LE_ADD; ARITH_RULE `p < m + p + 1`]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
    X_GEN_TAC `t:num->real^M->bool` THEN STRIP_TAC] THEN
  EXISTS_TAC `s INTER
       INTERS {UNIONS {(t:num->real^M->bool) k | n <= k} | n IN (:num)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MATCH_MP_TAC NEGLIGIBLE_INTER THEN DISJ2_TAC THEN
    SIMP_TAC[NEGLIGIBLE_OUTER_LE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`inv(&2)`; `e / &2`] REAL_ARCH_POW_INV) THEN
    ASM_REWRITE_TAC[REAL_POW_INV; REAL_HALF] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `UNIONS {(t:num->real^M->bool) k | N <= k}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `x IN s ==> INTERS s SUBSET x`) THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LE_EXISTS; SET_RULE
     `{f n | ?d. n = N + d} = {f(N + n) | n IN (:num)}`] THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN
    TRANS_TAC REAL_LE_TRANS `sum(0..n) (\k. inv(&2 pow (N + k)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_INV_MUL; SUM_LMUL; GSYM REAL_POW_INV] THEN
    REWRITE_TAC[SUM_GP; CONJUNCT1 LT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_INV_INV] THEN
    REWRITE_TAC[REAL_ARITH `x * y * &2 <= e <=> y * x <= e / &2`] THEN
    REWRITE_TAC[REAL_POW_INV] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REAL_ARITH `n < e / &2 ==> &0 <= x * n ==> (&1 - x) * n <= e / &2`)) THEN
    REWRITE_TAC[GSYM REAL_INV_MUL; REAL_LE_INV_EQ; GSYM REAL_POW_ADD] THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS];

    REWRITE_TAC[INTER_SUBSET];
    X_GEN_TAC `x:real^M` THEN
    REWRITE_TAC[SET_RULE `s DIFF (s INTER t) = s DIFF t`] THEN
    REWRITE_TAC[IN_DIFF; INTERS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `~(a /\ b) <=> a ==> ~b`] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "*")) THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
    ASM_REWRITE_TAC[REAL_POW_INV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N + M:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `x:real^M`]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; real_ge; REAL_NOT_LE] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LT_TRANS) THEN
    TRANS_TAC REAL_LET_TRANS `inv(&2 pow M)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_POW_INV] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Fubini-type results for measure.                                          *)
(* ------------------------------------------------------------------------- *)

let FUBINI_MEASURE = prove
 (`!s:real^(M,N)finite_sum->bool.
        measurable s
        ==> negligible {x | ~measurable {y | pastecart x y IN s}} /\
            ((\x. lift(measure {y | pastecart x y IN s}))
             has_integral lift(measure s)) UNIV`,
  let MEASURE_PASTECART_INTERVAL = prove
   (`!a b:real^(M,N)finite_sum.
          (!x. measurable {y | pastecart x y IN interval[a,b]}) /\
          ((\x. lift(measure {y | pastecart x y IN interval[a,b]}))
           has_integral lift(measure(interval[a,b]))) UNIV`,
    REWRITE_TAC[FORALL_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `c:real^N`; `b:real^M`; `d:real^N`] THEN
    REWRITE_TAC[GSYM PCROSS_INTERVAL; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[SET_RULE `{x | P /\ Q x} = if P then {x | Q x} else {}`] THEN
    REWRITE_TAC[COND_RAND; SET_RULE `{x | x IN s} = s`] THEN
    REWRITE_TAC[MEASURABLE_INTERVAL; MEASURABLE_EMPTY; COND_ID] THEN
    REWRITE_TAC[MEASURE_EMPTY; LIFT_NUM; HAS_INTEGRAL_RESTRICT_UNIV] THEN
    REWRITE_TAC[PCROSS_INTERVAL; MEASURE_INTERVAL; CONTENT_PASTECART] THEN
    REWRITE_TAC[LIFT_CMUL; HAS_INTEGRAL_CONST]) in
  let MEASURE_PASTECART_ELEMENTARY = prove
   (`!s:real^(M,N)finite_sum->bool.
          (?d. d division_of s)
          ==> (!x. measurable {y | pastecart x y IN s}) /\
              ((\x. lift(measure {y | pastecart x y IN s}))
               has_integral lift(measure s)) UNIV`,
    let lemma = prove
     (`{x | f x IN UNIONS s} = UNIONS {{x | f x IN d} | d IN s}`,
      REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
    GEN_TAC THEN REWRITE_TAC[division_of; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:(real^(M,N)finite_sum->bool)->bool` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[lemma] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real^M` THEN MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `k:real^(M,N)finite_sum->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?a b:real^(M,N)finite_sum. k = interval[a,b]`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[MEASURE_PASTECART_INTERVAL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((\x. vsum d (\k. lift(measure {y | pastecart x y IN k}))) has_integral
       vsum d (\k:real^(M,N)finite_sum->bool. lift(measure k))) UNIV`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `k:real^(M,N)finite_sum->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?a b:real^(M,N)finite_sum. k = interval[a,b]`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[MEASURE_PASTECART_INTERVAL];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[HAS_INTEGRAL_SPIKE]
     `!t. negligible t /\ a = b /\ (!x. x IN s DIFF t ==> g x = f x)
          ==> (f has_integral a) s ==> (g has_integral b) s`) THEN
    EXISTS_TAC
     `UNIONS { {x | (x:real^M)$i =
                    fstcart(interval_lowerbound k:real^(M,N)finite_sum)$i} |
               i IN 1..dimindex(:M) /\ k IN d} UNION
      UNIONS { {x | x$i = fstcart(interval_upperbound k)$i} |
               i IN 1..dimindex(:M) /\ k IN d}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
      CONJ_TAC THEN MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
      ASM_SIMP_TAC[ONCE_REWRITE_RULE[CONJ_SYM] FINITE_PRODUCT_DEPENDENT;
                   FINITE_NUMSEG] THEN
      SIMP_TAC[FORALL_IN_GSPEC; NEGLIGIBLE_STANDARD_HYPERPLANE; IN_NUMSEG];
      REWRITE_TAC[IN_DIFF; IN_UNIV]] THEN
    REWRITE_TAC[REWRITE_RULE[o_DEF] (GSYM LIFT_SUM); FUN_EQ_THM; LIFT_EQ] THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS;
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS_IMAGE] THEN
    ASM_REWRITE_TAC[GSYM HAS_MEASURE_MEASURE] THEN
    (CONJ_TAC THENL
      [ASM_MESON_TAC[MEASURE_PASTECART_INTERVAL; MEASURABLE_INTERVAL];
       ALL_TAC]) THEN
    MAP_EVERY X_GEN_TAC
     [`k:real^(M,N)finite_sum->bool`; `l:real^(M,N)finite_sum->bool`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`k:real^(M,N)finite_sum->bool`; `l:real^(M,N)finite_sum->bool`]) THEN
    ASM_REWRITE_TAC[GSYM INTERIOR_INTER] THEN
    (SUBGOAL_THEN
      `?a b:real^(M,N)finite_sum c d:real^(M,N)finite_sum.
              k = interval[a,b] /\ l = interval[c,d]`
     MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    SIMP_TAC[LEFT_IMP_EXISTS_THM; NEGLIGIBLE_CONVEX_INTERIOR;
             CONVEX_INTER; CONVEX_INTERVAL] THEN
    REWRITE_TAC[FORALL_PASTECART; GSYM PCROSS_INTERVAL;
                PASTECART_IN_PCROSS] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `{x | P /\ Q x} INTER {x | R /\ S x} =
      {x | P /\ R} INTER {x | Q x /\ S x}`] THEN
    REWRITE_TAC[INTER_PCROSS; INTERIOR_PCROSS; GSYM INTER] THEN
    REWRITE_TAC[SET_RULE `{x | P} = if P then UNIV else {}`] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; INTER_EMPTY; INTER_UNIV] THEN
    SIMP_TAC[NEGLIGIBLE_CONVEX_INTERIOR; CONVEX_INTER; CONVEX_INTERVAL] THEN
    REWRITE_TAC[PCROSS_EQ_EMPTY; TAUT `(if p then q else T) <=> p ==> q`] THEN
    REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    SIMP_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_UNION]) THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN(fun th ->
     MP_TAC(SPEC  `l:real^(M,N)finite_sum->bool` th) THEN
     MP_TAC(SPEC  `k:real^(M,N)finite_sum->bool` th))) THEN
    REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PCROSS_INTERVAL]) THEN
    REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[TAUT `~a \/ b <=> a ==> b`] THEN
    ASM_SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY; INTERVAL_UPPERBOUND_NONEMPTY;
                 FSTCART_PASTECART] THEN
    REPLICATE_TAC 3 (GEN_REWRITE_TAC I [IMP_IMP]) THEN
    MATCH_MP_TAC(TAUT `(a ==> c ==> ~b) ==> a ==> b ==> c ==> d`) THEN
    REWRITE_TAC[IN_INTERVAL; INTERVAL_NE_EMPTY; AND_FORALL_THM;
                INTERIOR_INTERVAL; IMP_IMP; INTER_INTERVAL] THEN
    MATCH_MP_TAC MONO_FORALL THEN SIMP_TAC[LAMBDA_BETA] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN REAL_ARITH_TAC) in
  let MEASURE_PASTECART_OPEN_MEASURABLE = prove
   (`!s:real^(M,N)finite_sum->bool.
          open s /\ measurable s
          ==> negligible {x | ~measurable {y | pastecart x y IN s}} /\
              ((\x. lift(measure {y | pastecart x y IN s}))
               has_integral lift(measure s)) UNIV`,
    let lemur = prove
     (`UNIONS {{y | pastecart x y IN g n} | n IN (:num)} =
       {y | pastecart x y IN UNIONS {g n | n IN (:num)}}`,
      REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
    GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `g:num->real^(M,N)finite_sum->bool`
     STRIP_ASSUME_TAC o MATCH_MP OPEN_COUNTABLE_LIMIT_ELEMENTARY) THEN
    SUBGOAL_THEN `!n:num. g n SUBSET (s:real^(M,N)finite_sum->bool)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\n:num x:real^M. lift(measure {y:real^N | pastecart x y IN (g n)})`;
      `(:real^M)`] BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING) THEN
    MP_TAC(GEN `n:num` (ISPEC `(g:num->real^(M,N)finite_sum->bool) n`
          MEASURE_PASTECART_ELEMENTARY)) THEN
    ASM_REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL; FORALL_AND_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; LIFT_DROP] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REPEAT GEN_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
        REPEAT(CONJ_TAC THENL
         [ASM_MESON_TAC[MEASURE_PASTECART_ELEMENTARY]; ALL_TAC]) THEN
        ASM SET_TAC[];
        REWRITE_TAC[bounded; FORALL_IN_GSPEC; NORM_LIFT] THEN
        EXISTS_TAC `measure(s:real^(M,N)finite_sum->bool)` THEN
        GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `&0 <= x /\ x <= y ==> abs x <= y`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MEASURE_POS_LE;
          MATCH_MP_TAC MEASURE_SUBSET] THEN
        ASM_MESON_TAC[MEASURABLE_ELEMENTARY]];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`f:real^M->real^1`; `t:real^M->bool`] THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    SUBGOAL_THEN
     `!x:real^M.
         ~(x IN t) ==> {y:real^N | pastecart x y IN s} has_measure drop(f x)`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGENT_IMP_BOUNDED) THEN
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV; NORM_LIFT] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN MP_TAC(ISPECL
       [`\n. {y | pastecart x y IN (g:num->real^(M,N)finite_sum->bool) n}`;
        `B:real`]
       HAS_MEASURE_NESTED_UNIONS) THEN
      ASM_SIMP_TAC[lemur; REAL_ARITH `abs x <= B ==> x <= B`] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE; GSYM LIFT_EQ] THEN
      ASM_MESON_TAC[LIM_UNIQUE; TRIVIAL_LIMIT_SEQUENTIALLY; LIFT_DROP];
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN
        REWRITE_TAC[measurable] THEN ASM SET_TAC[];
        MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
        MAP_EVERY EXISTS_TAC [`f:real^M->real^1`; `t:real^M->bool`] THEN
        ASM_REWRITE_TAC[NEGLIGIBLE; IN_DIFF; IN_UNIV] THEN
        REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[MEASURE_UNIQUE]; ALL_TAC] THEN
        ASM_REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
        MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN EXISTS_TAC
          `\k. lift(measure ((g:num->real^(M,N)finite_sum->bool) k))` THEN
        ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
        MP_TAC(ISPECL [`g:num->real^(M,N)finite_sum->bool`;
                       `measure(s:real^(M,N)finite_sum->bool)`]
                  HAS_MEASURE_NESTED_UNIONS) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_MESON_TAC[MEASURABLE_ELEMENTARY; MEASURE_SUBSET]]]) in
  let MEASURE_PASTECART_COMPACT = prove
   (`!s:real^(M,N)finite_sum->bool.
          compact s
          ==> (!x. measurable {y | pastecart x y IN s}) /\
              ((\x. lift(measure {y | pastecart x y IN s}))
               has_integral lift(measure s)) UNIV`,
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MEASURABLE_COMPACT THEN
      REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
        REWRITE_TAC[BOUNDED_POS; FORALL_IN_GSPEC] THEN
        MESON_TAC[NORM_LE_PASTECART; REAL_LE_TRANS];
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CONTINUOUS_PASTECART;
                     CONTINUOUS_CONST; CONTINUOUS_AT_ID]];
      DISCH_TAC] THEN
    SUBGOAL_THEN
     `?t:real^(M,N)finite_sum->bool.
          open t /\ measurable t /\ s SUBSET t`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[BOUNDED_SUBSET_BALL; COMPACT_IMP_BOUNDED;
                    MEASURABLE_BALL; OPEN_BALL];
      ALL_TAC] THEN
    MP_TAC(ISPEC `t:real^(M,N)finite_sum->bool`
      MEASURE_PASTECART_OPEN_MEASURABLE) THEN
    MP_TAC(ISPEC `t DIFF s:real^(M,N)finite_sum->bool`
      MEASURE_PASTECART_OPEN_MEASURABLE) THEN
    ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_COMPACT; OPEN_DIFF;
                 COMPACT_IMP_CLOSED; MEASURE_DIFF_SUBSET; IMP_IMP] THEN
    DISCH_THEN(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[LIFT_SUB; IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN
    REWRITE_TAC[VECTOR_ARITH `t - (t - s):real^1 = s`] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] (REWRITE_RULE[CONJ_ASSOC]
          HAS_INTEGRAL_SPIKE)) THEN
    EXISTS_TAC
     `{x | ~measurable {y | pastecart x y IN t DIFF s}} UNION
      {x:real^M | ~measurable {y:real^N | pastecart x y IN t}}` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `x:real^M` THEN
    SIMP_TAC[IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
    STRIP_TAC THEN REWRITE_TAC[LIFT_EQ; GSYM LIFT_SUB] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a:real = b - c <=> c = b - a`] THEN
    REWRITE_TAC[SET_RULE
     `{y | pastecart x y IN t /\ ~(pastecart x y IN s)} =
      {y | pastecart x y IN t} DIFF {y | pastecart x y IN s}`] THEN
    MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN ASM SET_TAC[]) in
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?f. (!n. compact(f n) /\ f n SUBSET s /\ measurable(f n) /\
             measure s < measure(f n) + inv(&n + &1)) /\
        (!n. (f:num->real^(M,N)finite_sum->bool) n SUBSET f(SUC n))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_INNER_COMPACT THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `t:real^(M,N)finite_sum->bool`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^(M,N)finite_sum->bool`; `inv(&(SUC n) + &1)`]
        MEASURABLE_INNER_COMPACT) THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^(M,N)finite_sum->bool`
        STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t UNION u:real^(M,N)finite_sum->bool` THEN
    ASM_SIMP_TAC[COMPACT_UNION; UNION_SUBSET; MEASURABLE_UNION] THEN
    REWRITE_TAC[SUBSET_UNION] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REAL_ARITH `s < a + e ==> a <= b ==> s < b + e`)) THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_UNION; SUBSET_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g. (!n. open(g n) /\ s SUBSET g n /\ measurable(g n) /\
             measure(g n) < measure s + inv(&n + &1)) /\
        (!n. (g:num->real^(M,N)finite_sum->bool) (SUC n) SUBSET g n)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_OUTER_OPEN THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `t:real^(M,N)finite_sum->bool`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^(M,N)finite_sum->bool`; `inv(&(SUC n) + &1)`]
        MEASURABLE_OUTER_OPEN) THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^(M,N)finite_sum->bool`
        STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t INTER u:real^(M,N)finite_sum->bool` THEN
    ASM_SIMP_TAC[OPEN_INTER; SUBSET_INTER; MEASURABLE_INTER] THEN
    REWRITE_TAC[INTER_SUBSET] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REAL_ARITH `a < s + e ==> b <= a ==> b < s + e`)) THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n:num x:real^M. lift(measure {y:real^N | pastecart x y IN (g n)}) -
                      lift(measure {y:real^N | pastecart x y IN (f n)})`;
    `(:real^M)`] BEPPO_LEVI_MONOTONE_CONVERGENCE_DECREASING_AE) THEN
  MP_TAC(GEN `n:num` (ISPEC `(f:num->real^(M,N)finite_sum->bool) n`
        MEASURE_PASTECART_COMPACT)) THEN
  MP_TAC(GEN `n:num` (ISPEC `(g:num->real^(M,N)finite_sum->bool) n`
        MEASURE_PASTECART_OPEN_MEASURABLE)) THEN
  ASM_REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL; FORALL_AND_THM] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; DROP_SUB; LIFT_DROP] THEN
  ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRAL_SUB] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN EXISTS_TAC
       `{x:real^M | ~measurable {y:real^N | pastecart x y IN g n}} UNION
        {x:real^M | ~measurable {y | pastecart x y IN g (SUC n)}}` THEN
      ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; IN_UNION; DE_MORGAN_THM] THEN
      X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `f <= f' /\ g' <= g ==> g' - f' <= g - f`) THEN
      CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN
      EXISTS_TAC `measure((g:num->real^(M,N)finite_sum->bool) 0) -
                  measure((f:num->real^(M,N)finite_sum->bool) 0)` THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!s. f' <= s /\ s <= g' /\ f <= f' /\ g' <= g
            ==> abs(g' - f') <= g - f`) THEN
      EXISTS_TAC `measure(s:real^(M,N)finite_sum->bool)` THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(ARITH_RULE `0 <= n`) THEN
      SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`0`,`m:num`) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`h:real^M->real^1`; `k:real^M->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `?t. negligible t /\
        (!n x. ~(x IN t) ==> measurable {y:real^N | pastecart x y IN g n}) /\
        (!x. ~(x IN t)
             ==> ((\k. lift(measure {y | pastecart x y IN g k}) -
                  lift(measure {y:real^N | pastecart x y IN f k})) --> vec 0)
                  sequentially) /\
        (!x. ~(x IN t) ==> (h:real^M->real^1) x = vec 0)`
  MP_TAC THENL
   [MP_TAC(ISPECL
     [`\x. if x IN UNIONS{ {x | ~measurable {y:real^N | pastecart x y IN g n}}
                           |  n IN (:num)} UNION k
           then vec 0 else (h:real^M->real^1) x`; `(:real^M)`]
     HAS_INTEGRAL_NEGLIGIBLE_EQ) THEN
    REWRITE_TAC[IN_UNIV; DIMINDEX_1; FORALL_1] THEN ANTS_TAC THENL
     [X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN
      COND_CASES_TAC THEN REWRITE_TAC[VEC_COMPONENT; REAL_LE_REFL] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_COMPONENT_LBOUND) THEN
      EXISTS_TAC
       `\k:num. lift(measure {y | pastecart x y IN
                                  (g:num->real^(M,N)finite_sum->bool) k}) -
                lift(measure {y | pastecart x y IN
                                  (f:num->real^(M,N)finite_sum->bool) k})` THEN
      REWRITE_TAC[DIMINDEX_1; TRIVIAL_LIMIT_SEQUENTIALLY; LE_REFL] THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[GSYM drop; DROP_SUB; LIFT_DROP] THEN
      REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[UNIONS_GSPEC]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
     [MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
      EXISTS_TAC `h:real^M->real^1` THEN
      EXISTS_TAC `UNIONS{ {x | ~measurable {y | pastecart x y IN
                                 (g:num->real^(M,N)finite_sum->bool) n}}
                           |  n IN (:num)} UNION k` THEN
      ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; IN_DIFF; IN_UNION; IN_UNIV] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IN_UNIV] NEGLIGIBLE_COUNTABLE_UNIONS) THEN
        ASM_REWRITE_TAC[];
        MESON_TAC[];
        ASM_REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
        MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN EXISTS_TAC
         `\k. lift(measure((g:num->real^(M,N)finite_sum->bool) k)) -
              lift(measure((f:num->real^(M,N)finite_sum->bool) k))` THEN
        ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
        REWRITE_TAC[LIM_SEQUENTIALLY; GSYM LIFT_SUB; DIST_0; NORM_LIFT] THEN
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        MP_TAC(SPEC `e / &2` REAL_ARCH_INV) THEN
        ASM_REWRITE_TAC[REAL_HALF] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `!s d. f <= s /\ s <= g /\ s < f + d /\ g < s + d /\ d <= e / &2
                ==> abs(g - f) < e`) THEN
        EXISTS_TAC `measure(s:real^(M,N)finite_sum->bool)` THEN
        EXISTS_TAC `inv(&n + &1)` THEN ASM_REWRITE_TAC[CONJ_ASSOC] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[MEASURE_SUBSET]; ALL_TAC] THEN
        TRANS_TAC REAL_LE_TRANS `inv(&N)` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
        ASM_ARITH_TAC];
      DISCH_TAC THEN EXISTS_TAC
       `{x | ~((if x IN
         UNIONS {{x | ~measurable {y | pastecart x y IN g n}} | n | T} UNION k
                then vec 0 else (h:real^M->real^1) x) = vec 0)} UNION
        UNIONS {{x | ~measurable {y | pastecart x y IN
                     (g:num->real^(M,N)finite_sum->bool) n}} | n | T} UNION
        k` THEN
      ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
      ASM_SIMP_TAC[IN_UNION; DE_MORGAN_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IN_UNIV] NEGLIGIBLE_COUNTABLE_UNIONS) THEN
        ASM_REWRITE_TAC[];
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]]];
    FIRST_X_ASSUM(K ALL_TAC o SPEC `x:real^M`) THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `!x:real^M. ~(x IN t) ==> measurable {y:real^N | pastecart x y IN s}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[MEASURABLE_INNER_OUTER] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `x:real^M` th) THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [LIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_SIMP_TAC[DIST_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
    REWRITE_TAC[LE_REFL; GSYM LIFT_SUB; NORM_LIFT] THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`{y | pastecart x y IN (f:num->real^(M,N)finite_sum->bool) N}`;
      `{y | pastecart x y IN (g:num->real^(M,N)finite_sum->bool) N}`] THEN
    ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `t:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n:num x:real^M. lift(measure {y:real^N | pastecart x y IN (g n)})`;
    `\x:real^M. lift(measure {y:real^N | pastecart x y IN s})`;
    `(:real^M)`; `t:real^M->bool`] MONOTONE_CONVERGENCE_DECREASING_AE) THEN
  ASM_REWRITE_TAC[LIFT_DROP; IN_UNIV; IN_DIFF] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[IN_DIFF] THEN ASM SET_TAC[];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(fun th ->
        MP_TAC(SPEC `x:real^M` th) THEN ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [LIM_SEQUENTIALLY]) THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_SIMP_TAC[DIST_0] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[DIST_LIFT; GSYM dist] THEN
      MATCH_MP_TAC(REAL_ARITH
       `f <= s /\ s <= g ==> abs(g - f) < e ==> abs(g - s) < e`) THEN
      CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[IN_DIFF] THEN ASM SET_TAC[];
      REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN
      EXISTS_TAC `measure((g:num->real^(M,N)finite_sum->bool) 0)` THEN
      ASM_SIMP_TAC[NORM_LIFT; real_abs; MEASURE_POS_LE] THEN
      X_GEN_TAC `m:num` THEN MP_TAC(ARITH_RULE `0 <= m`) THEN
      SPEC_TAC(`m:num`,`m:num`) THEN SPEC_TAC(`0`,`n:num`) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
      REPEAT(CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
      GEN_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\k. lift(measure((g:num->real^(M,N)finite_sum->bool) k))` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `!d. g < s + d /\ s <= g /\ d < e ==> abs(g - s) < e`) THEN
    EXISTS_TAC `inv(&n + &1)` THEN ASM_SIMP_TAC[MEASURE_SUBSET] THEN
    TRANS_TAC REAL_LET_TRANS `inv(&N)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
    ASM_ARITH_TAC]);;

let FUBINI_MEASURE_ALT = prove
 (`!s:real^(M,N)finite_sum->bool.
        measurable s
        ==> negligible {y | ~measurable {x | pastecart x y IN s}} /\
            ((\y. lift(measure {x | pastecart x y IN s}))
             has_integral lift(measure s)) UNIV`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (\z. pastecart (sndcart z) (fstcart z))
                      (s:real^(M,N)finite_sum->bool)`
        FUBINI_MEASURE) THEN
  MP_TAC(ISPEC
   `\z:real^(M,N)finite_sum. pastecart (sndcart z) (fstcart z)`
   HAS_MEASURE_ISOMETRY) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_SYM] THEN
    SIMP_TAC[LINEAR_PASTECART; LINEAR_FSTCART; LINEAR_SNDCART] THEN
    SIMP_TAC[FORALL_PASTECART; NORM_EQ; GSYM NORM_POW_2; SQNORM_PASTECART] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; REAL_ADD_AC];
    DISCH_TAC THEN ASM_REWRITE_TAC[measurable; measure] THEN
    ASM_REWRITE_TAC[GSYM measurable; GSYM measure] THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART;
                SNDCART_PASTECART; PASTECART_INJ] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1]]);;

let FUBINI_LEBESGUE_MEASURABLE = prove
 (`!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> negligible {x | ~lebesgue_measurable {y | pastecart x y IN s}}`,
  let lemma = prove
   (`{x | ?n. P n x} = UNIONS {{x | P n x} | n IN (:num)}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[NEGLIGIBLE_ON_COUNTABLE_INTERVALS] THEN
  X_GEN_TAC `m:num` THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_MEASURABLE_ON_COUNTABLE_SUBINTERVALS] THEN
  REWRITE_TAC[INTER; IN_ELIM_THM; NOT_FORALL_THM; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[lemma] THEN MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
  X_GEN_TAC `n:num` THEN
  MP_TAC(ISPEC `(s:real^(M,N)finite_sum->bool) INTER
                (interval[--vec m,vec m] PCROSS interval[--vec n,vec n])`
        FUBINI_MEASURE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PCROSS_INTERVAL] THEN
    ASM_MESON_TAC[LEBESGUE_MEASURABLE_MEASURABLE_ON_SUBINTERVALS];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS] THEN
  ASM_CASES_TAC `(x:real^M) IN interval[--vec m,vec m]` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; MEASURABLE_EMPTY]);;

let FUBINI_LEBESGUE_MEASURABLE_ALT = prove
 (`!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> negligible {y | ~lebesgue_measurable {x | pastecart x y IN s}}`,
  let lemma = prove
   (`{x | ?n. P n x} = UNIONS {{x | P n x} | n IN (:num)}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[NEGLIGIBLE_ON_COUNTABLE_INTERVALS] THEN
  X_GEN_TAC `n:num` THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_MEASURABLE_ON_COUNTABLE_SUBINTERVALS] THEN
  REWRITE_TAC[INTER; IN_ELIM_THM; NOT_FORALL_THM; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[lemma] THEN MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
  X_GEN_TAC `m:num` THEN
  MP_TAC(ISPEC `(s:real^(M,N)finite_sum->bool) INTER
                (interval[--vec m,vec m] PCROSS interval[--vec n,vec n])`
        FUBINI_MEASURE_ALT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PCROSS_INTERVAL] THEN
    ASM_MESON_TAC[LEBESGUE_MEASURABLE_MEASURABLE_ON_SUBINTERVALS];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS] THEN
  ASM_CASES_TAC `(y:real^N) IN interval[--vec n,vec n]` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; MEASURABLE_EMPTY]);;

let FUBINI_NEGLIGIBLE = prove
 (`!s. negligible s
       ==> negligible
            {x:real^M | ~negligible {y:real^N | pastecart x y IN s}}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_MEASURE o MATCH_MP
    NEGLIGIBLE_IMP_MEASURABLE) THEN
  ASM_SIMP_TAC[MEASURE_EQ_0; LIFT_NUM; IMP_CONJ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\x:real^M. lift (measure {y:real^N | pastecart x y IN s})`;
    `(:real^M)`;
    `{x:real^M | ~measurable {y:real^N | pastecart x y IN s}}`]
   HAS_INTEGRAL_NEGLIGIBLE_EQ_AE) THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_DIFF; IN_ELIM_THM] THEN
  SIMP_TAC[IMP_IMP; FORALL_1; DIMINDEX_1; GSYM drop; LIFT_DROP; IN_UNIV] THEN
  ASM_SIMP_TAC[MEASURE_POS_LE; IMP_CONJ] THEN DISCH_THEN(K ALL_TAC) THEN
  UNDISCH_TAC
   `negligible {x:real^M | ~measurable {y:real^N | pastecart x y IN s}}` THEN
  REWRITE_TAC[IMP_IMP; GSYM NEGLIGIBLE_UNION_EQ] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; GSYM DROP_EQ] THEN
  REWRITE_TAC[LIFT_DROP; DROP_VEC] THEN
  REWRITE_TAC[HAS_MEASURE_MEASURE; GSYM HAS_MEASURE_0] THEN
  SET_TAC[]);;

let FUBINI_NEGLIGIBLE_ALT = prove
 (`!s. negligible s
       ==> negligible
            {y:real^N | ~negligible {x:real^M | pastecart x y IN s}}`,
  let lemma = prove
   (`!s:real^(M,N)finite_sum->bool.
        negligible s
         ==> negligible (IMAGE (\z. pastecart (sndcart z) (fstcart z)) s)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_LINEAR_IMAGE_GEN THEN
    ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_SYM; LE_REFL] THEN
    REWRITE_TAC[linear; FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART;
                FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                GSYM PASTECART_ADD; GSYM PASTECART_CMUL]) in
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_NEGLIGIBLE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_INJ;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2]);;

let NEGLIGIBLE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        negligible(s PCROSS t) <=> negligible s \/ negligible t`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_NEGLIGIBLE) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[SET_RULE `{y | P /\ Q y} = if P then {y | Q y} else {}`] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
    ASM_CASES_TAC `negligible(t:real^N->bool)` THEN
    ASM_REWRITE_TAC[SET_RULE `~(if P then F else T) = P`;
                    SET_RULE `{x | x IN s} = s`];
    ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
    REWRITE_TAC[FORALL_PASTECART; GSYM PCROSS_INTERVAL; INTER_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`aa:real^M`; `a:real^N`; `bb:real^M`; `b:real^N`] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `(s:real^M->bool) PCROSS interval[a:real^N,b]` THEN
    REWRITE_TAC[SUBSET_PCROSS; INTER_SUBSET] THEN
    REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC(ISPECL
     [`s:real^M->bool`; `e / (content(interval[a:real^N,b]) + &1)`]
     MEASURABLE_OUTER_CLOSED_INTERVALS) THEN
    ASM_SIMP_TAC[NEGLIGIBLE_IMP_MEASURABLE; REAL_LT_DIV; CONTENT_POS_LE;
      MEASURE_EQ_0; REAL_ADD_LID; REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `UNIONS { (k:real^M->bool) PCROSS interval[a:real^N,b] |
                         k IN d}` THEN
    ASM_REWRITE_TAC[GSYM PCROSS_UNIONS; SUBSET_PCROSS; SUBSET_REFL] THEN
    REWRITE_TAC[PCROSS_UNIONS] THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MEASURABLE_INTERVAL; PCROSS_INTERVAL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
    X_GEN_TAC `D:(real^M->bool)->bool` THEN STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE_IMAGE o
      lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[MEASURABLE_INTERVAL; PCROSS_INTERVAL; SUBSET];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum D (\k:real^M->bool. measure k * content(interval[a:real^N,b]))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^M. k = interval[u,v]` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ASM_REWRITE_TAC[]] THEN
      ASM_REWRITE_TAC[PCROSS_INTERVAL; MEASURE_INTERVAL; CONTENT_PASTECART];
      REWRITE_TAC[SUM_RMUL]] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x * (y + &1) <= e ==> x * y <= e`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN
      ASM_MESON_TAC[MEASURE_POS_LE; SUBSET; MEASURABLE_INTERVAL];
      SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
               CONTENT_POS_LE]] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)) THEN
    TRANS_TAC REAL_LE_TRANS `measure(UNIONS D:real^M->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE;
      MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[SUBSET_UNIONS] THEN
      ASM_MESON_TAC[MEASURABLE_UNIONS; MEASURABLE_INTERVAL; SUBSET]] THEN
    TRANS_TAC EQ_TRANS `sum (D:(real^M->bool)->bool) content` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[MEASURE_INTERVAL; SUBSET];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_ELEMENTARY THEN
      REWRITE_TAC[division_of] THEN ASM SET_TAC[]];
    ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
    REWRITE_TAC[FORALL_PASTECART; GSYM PCROSS_INTERVAL; INTER_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `aa:real^N`; `b:real^M`; `bb:real^N`] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `interval[a:real^M,b] PCROSS (t:real^N->bool)` THEN
    REWRITE_TAC[SUBSET_PCROSS; INTER_SUBSET] THEN
    REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC(ISPECL
     [`t:real^N->bool`; `e / (content(interval[a:real^M,b]) + &1)`]
     MEASURABLE_OUTER_CLOSED_INTERVALS) THEN
    ASM_SIMP_TAC[NEGLIGIBLE_IMP_MEASURABLE; REAL_LT_DIV; CONTENT_POS_LE;
      MEASURE_EQ_0; REAL_ADD_LID; REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `UNIONS { interval[a:real^M,b] PCROSS (k:real^N->bool) |
                         k IN d}` THEN
    ASM_REWRITE_TAC[GSYM PCROSS_UNIONS; SUBSET_PCROSS; SUBSET_REFL] THEN
    REWRITE_TAC[PCROSS_UNIONS] THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MEASURABLE_INTERVAL; PCROSS_INTERVAL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
    X_GEN_TAC `D:(real^N->bool)->bool` THEN STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE_IMAGE o
      lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[MEASURABLE_INTERVAL; PCROSS_INTERVAL; SUBSET];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum D (\k:real^N->bool. content(interval[a:real^M,b]) * measure k)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^N. k = interval[u,v]` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ASM_REWRITE_TAC[]] THEN
      ASM_REWRITE_TAC[PCROSS_INTERVAL; MEASURE_INTERVAL; CONTENT_PASTECART];
      REWRITE_TAC[SUM_LMUL]] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x * (y + &1) <= e ==> y * x <= e`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN
      ASM_MESON_TAC[MEASURE_POS_LE; SUBSET; MEASURABLE_INTERVAL];
      SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
               CONTENT_POS_LE]] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)) THEN
    TRANS_TAC REAL_LE_TRANS `measure(UNIONS D:real^N->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE;
      MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[SUBSET_UNIONS] THEN
      ASM_MESON_TAC[MEASURABLE_UNIONS; MEASURABLE_INTERVAL; SUBSET]] THEN
    TRANS_TAC EQ_TRANS `sum (D:(real^N->bool)->bool) content` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[MEASURE_INTERVAL; SUBSET];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_ELEMENTARY THEN
      REWRITE_TAC[division_of] THEN ASM SET_TAC[]]]);;

let FUBINI_TONELLI_MEASURE = prove
 (`!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> (measurable s <=>
             negligible {x | ~measurable {y | pastecart x y IN s}} /\
             (\x. lift(measure {y | pastecart x y IN s})) integrable_on UNIV)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[FUBINI_MEASURE; integrable_on]; STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`\n. s INTER ball(vec 0:real^(M,N)finite_sum,&n)`;
    `drop(integral (:real^M)
       (\x. lift (measure {y:real^N | pastecart x y IN s})))`]
       MEASURABLE_NESTED_UNIONS) THEN
  ASM_SIMP_TAC[MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE;
               MEASURABLE_BALL; GSYM REAL_OF_NUM_SUC; SUBSET_BALL;
               REAL_ARITH `x <= x + &1`;
               SET_RULE `t SUBSET u ==> s INTER t SUBSET s INTER u`] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(SPEC `s INTER ball(vec 0:real^(M,N)finite_sum,&n)`
        FUBINI_MEASURE) THEN
    ASM_SIMP_TAC[MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE;
                 MEASURABLE_BALL; HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `{x:real^M | ~measurable {y:real^N | pastecart x y IN s}} UNION
                {x:real^M | ~measurable {y:real^N | pastecart x y IN s INTER
                                                    ball (vec 0,&n)}}` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; IN_DIFF; IN_UNIV; DE_MORGAN_THM;
                    IN_UNION; IN_ELIM_THM; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_INTER; IN_BALL_0; IN_UNIV] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[REAL_ARCH_LT]]);;

let FUBINI_TONELLI_MEASURE_ALT = prove
 (`!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> (measurable s <=>
             negligible {y | ~measurable {x | pastecart x y IN s}} /\
             (\y. lift(measure {x | pastecart x y IN s})) integrable_on UNIV)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (\z. pastecart (sndcart z) (fstcart z))
                      (s:real^(M,N)finite_sum->bool)`
        FUBINI_TONELLI_MEASURE) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN; LINEAR_PASTECART;
               LINEAR_FSTCART; LINEAR_SNDCART; DIMINDEX_FINITE_SUM;
               ARITH_RULE `m + n:num <= n + m`] THEN
  MP_TAC(ISPEC
   `\z:real^(M,N)finite_sum. pastecart (sndcart z) (fstcart z)`
   HAS_MEASURE_ISOMETRY) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_SYM] THEN
    SIMP_TAC[LINEAR_PASTECART; LINEAR_FSTCART; LINEAR_SNDCART] THEN
    SIMP_TAC[FORALL_PASTECART; NORM_EQ; GSYM NORM_POW_2; SQNORM_PASTECART] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; REAL_ADD_AC];
    DISCH_TAC THEN ASM_REWRITE_TAC[measurable; measure] THEN
    ASM_REWRITE_TAC[GSYM measurable; GSYM measure] THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART;
                SNDCART_PASTECART; PASTECART_INJ] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1]]);;

let FUBINI_TONELLI_NEGLIGIBLE = prove
 (`!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> (negligible s <=>
             negligible {x | ~negligible {y | pastecart x y IN s}})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[FUBINI_NEGLIGIBLE] THEN DISCH_TAC THEN
  REWRITE_TAC[NEGLIGIBLE_EQ_MEASURE_0] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[FUBINI_TONELLI_MEASURE] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; CONTRAPOS_THM;
                  NEGLIGIBLE_IMP_MEASURABLE];
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE)];
    DISCH_TAC THEN
    REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FUBINI_MEASURE) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          HAS_INTEGRAL_UNIQUE)) THEN
    MATCH_MP_TAC HAS_INTEGRAL_SPIKE] THEN
  EXISTS_TAC `(\x. vec 0):real^M->real^1` THEN
  EXISTS_TAC
   `{x:real^M | ~negligible {y:real^N | pastecart x y IN s}}` THEN
   ASM_REWRITE_TAC[INTEGRABLE_0; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
  SIMP_TAC[MEASURE_EQ_0; GSYM DROP_EQ; DROP_VEC; LIFT_DROP; HAS_INTEGRAL_0]);;

let FUBINI_TONELLI_NEGLIGIBLE_ALT = prove
 (`!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> (negligible s <=>
             negligible {y | ~negligible {x | pastecart x y IN s}})`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (\z. pastecart (sndcart z) (fstcart z))
                      (s:real^(M,N)finite_sum->bool)`
        FUBINI_TONELLI_NEGLIGIBLE) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN; LINEAR_PASTECART;
               LINEAR_FSTCART; LINEAR_SNDCART; DIMINDEX_FINITE_SUM;
               ARITH_RULE `m + n:num <= n + m`] THEN
  MP_TAC(ISPEC
   `\z:real^(M,N)finite_sum. pastecart (sndcart z) (fstcart z)`
   HAS_MEASURE_ISOMETRY) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_SYM] THEN
    SIMP_TAC[LINEAR_PASTECART; LINEAR_FSTCART; LINEAR_SNDCART] THEN
    SIMP_TAC[FORALL_PASTECART; NORM_EQ; GSYM NORM_POW_2; SQNORM_PASTECART] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; REAL_ADD_AC];
    DISCH_TAC THEN ASM_REWRITE_TAC[HAS_MEASURE_0] THEN
    ASM_REWRITE_TAC[GSYM HAS_MEASURE_0] THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART;
                SNDCART_PASTECART; PASTECART_INJ] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1]]);;

let LEBESGUE_MEASURABLE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        lebesgue_measurable(s PCROSS t) <=>
        negligible s \/ negligible t \/
        (lebesgue_measurable s /\ lebesgue_measurable t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `negligible(s:real^M->bool)` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_PCROSS; NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE];
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `negligible(t:real^N->bool)` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_PCROSS; NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[lebesgue_measurable; measurable_on; IN_UNIV] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC
     [`k:real^(M,N)finite_sum->bool`;
      `g:num->real^(M,N)finite_sum->real^1`] THEN
    STRIP_TAC THEN FIRST_ASSUM(fun th ->
      ASSUME_TAC(MATCH_MP FUBINI_NEGLIGIBLE th) THEN
      ASSUME_TAC(MATCH_MP FUBINI_NEGLIGIBLE_ALT th)) THEN
    SUBGOAL_THEN
     `~(s SUBSET {x:real^M | ~negligible {y:real^N | pastecart x y IN k}})`
    MP_TAC THENL [ASM_MESON_TAC[NEGLIGIBLE_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `~(t SUBSET {y:real^N | ~negligible {x:real^M | pastecart x y IN k}})`
    MP_TAC THENL [ASM_MESON_TAC[NEGLIGIBLE_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{x:real^M | pastecart x (y:real^N) IN k}` THEN
    EXISTS_TAC `\n x. (g:num->real^(M,N)finite_sum->real^1)
                      n (pastecart x y)` THEN
    EXISTS_TAC `{y:real^N | pastecart (x:real^M) y IN k}` THEN
    EXISTS_TAC `\n y. (g:num->real^(M,N)finite_sum->real^1)
                      n (pastecart x y)` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN
    (CONJ_TAC THENL
      [GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
       MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
       SIMP_TAC[CONTINUOUS_ON_PASTECART;
                CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
       ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
       ALL_TAC])
    THENL
     [X_GEN_TAC `u:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (u:real^M) (y:real^N)`);
      X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (x:real^M) (v:real^N)`)] THEN
    ASM_REWRITE_TAC[indicator; PASTECART_IN_PCROSS];
    MAP_EVERY X_GEN_TAC
     [`u:real^M->bool`; `f:num->real^M->real^1`;
      `v:real^N->bool`; `g:num->real^N->real^1`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `u PCROSS (:real^N) UNION (:real^M) PCROSS v` THEN
    EXISTS_TAC `\n:num z:real^(M,N)finite_sum.
      lift(drop(f n (fstcart z)) * drop(g n (sndcart z)))` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; NEGLIGIBLE_PCROSS] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      REWRITE_TAC[o_DEF; LIFT_DROP] THEN
      CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      REWRITE_TAC[FORALL_PASTECART; IN_UNION; PASTECART_IN_PCROSS] THEN
      REWRITE_TAC[IN_UNIV; DE_MORGAN_THM; LIFT_CMUL; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^N`] THEN STRIP_TAC THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      SUBGOAL_THEN `indicator (s PCROSS t) (pastecart x y) =
                    drop(indicator s (x:real^M)) % indicator t (y:real^N)`
      SUBST1_TAC THENL
       [REWRITE_TAC[indicator; PASTECART_IN_PCROSS] THEN
        MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(y:real^N) IN t`] THEN
        ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        MATCH_MP_TAC LIM_MUL THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN
        ASM_SIMP_TAC[]]]]);;

let MEASURABLE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        measurable(s PCROSS t) <=>
        negligible s \/ negligible t \/ (measurable s /\ measurable t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `negligible(s:real^M->bool)` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_PCROSS; NEGLIGIBLE_IMP_MEASURABLE];
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `negligible(t:real^N->bool)` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_PCROSS; NEGLIGIBLE_IMP_MEASURABLE];
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC
   `lebesgue_measurable((s:real^M->bool) PCROSS (t:real^N->bool))`
  THENL
   [ASM_SIMP_TAC[FUBINI_TONELLI_MEASURE; PASTECART_IN_PCROSS];
    ASM_MESON_TAC[LEBESGUE_MEASURABLE_PCROSS;
    MEASURABLE_IMP_LEBESGUE_MEASURABLE]] THEN
  REWRITE_TAC[SET_RULE `{x | P /\ x IN s} = if P then s else {}`] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[MEASURABLE_EMPTY; MEASURE_EMPTY] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[LIFT_NUM; INTEGRABLE_RESTRICT_UNIV; INTEGRABLE_ON_CONST] THEN
  REWRITE_TAC[SET_RULE
   `{x | if x IN s then P else F} = if P then s else {}`] THEN
  ASM_CASES_TAC `measurable(s:real^M->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `measurable(t:real^N->bool)` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN
  ASM_MESON_TAC[NEGLIGIBLE_EQ_MEASURE_0]);;

let HAS_MEASURE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool a b.
        s has_measure a /\ t has_measure b
        ==> (s PCROSS t) has_measure (a * b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(s:real^M->bool) PCROSS (t:real^N->bool)`
        FUBINI_MEASURE) THEN
  REWRITE_TAC[MEASURABLE_PCROSS; PASTECART_IN_PCROSS] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[measurable]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `{y | P /\ y IN s} = if P then s else {}`] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[MEASURABLE_EMPTY; MEASURE_EMPTY] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[LIFT_NUM; INTEGRABLE_RESTRICT_UNIV; INTEGRABLE_ON_CONST] THEN
  REWRITE_TAC[SET_RULE
   `{x | if x IN s then P else F} = if P then s else {}`] THEN
  REWRITE_TAC[HAS_INTEGRAL_RESTRICT_UNIV] THEN STRIP_TAC THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_PCROSS] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[measurable]; ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_EQ] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          HAS_INTEGRAL_UNIQUE)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
  ASM_REWRITE_TAC[LIFT_EQ_CMUL] THEN MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
  REWRITE_TAC[GSYM LIFT_EQ_CMUL] THEN
  ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  ASM_REWRITE_TAC[GSYM HAS_MEASURE; HAS_MEASURE_MEASURABLE_MEASURE]);;

let MEASURE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        measurable s /\ measurable t
        ==> measure(s PCROSS t) = measure s * measure t`,
  MESON_TAC[HAS_MEASURE_MEASURABLE_MEASURE; HAS_MEASURE_PCROSS]);;

(* ------------------------------------------------------------------------- *)
(* Relate the measurability of a function and of its ordinate set.           *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE = prove
 (`!f:real^M->real^N k.
        f measurable_on (:real^M)
        ==> lebesgue_measurable {pastecart x (y:real^N) | y$k <= (f x)$k}`,
  let lemma = prove
   (`!x y. x <= y <=> !q. rational q /\ y < q ==> x < q`,
    REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[REAL_LET_TRANS]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[REAL_NOT_LE; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
    MESON_TAC[RATIONAL_BETWEEN; REAL_LT_IMP_LE]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{pastecart (x:real^M) (y:real^N) | y$k <= (f x:real^N)$k} =
    INTERS {{pastecart x y | (f x)$k < q ==> y$k < q} | q IN rational}`
  SUBST1_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; EXTENSION; FORALL_PASTECART] THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN
    ONCE_REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN MESON_TAC[lemma; IN];
    ALL_TAC] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_INTERS THEN
  SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; COUNTABLE_RATIONAL] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN ONCE_REWRITE_TAC[SET_RULE
   `{f x y | P x y ==> Q x y} = {f x y | Q x y} UNION {f x y | ~(P x y)}`] THEN
  X_GEN_TAC `q:real` THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_UNION THEN
  REWRITE_TAC[REAL_NOT_LT; GSYM PCROSS; LEBESGUE_MEASURABLE_PCROSS;
   SET_RULE `{f x y |x,y| P x} = {f x y | x IN {x | P x} /\ y IN UNIV}`;
   SET_RULE `{f x y |x,y| Q y} = {f x y | x IN UNIV /\ y IN {x | Q x}}`] THEN
  CONJ_TAC THEN REPEAT DISJ2_TAC THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THENL
   [MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
    REWRITE_TAC[drop; OPEN_HALFSPACE_COMPONENT_LT];
    ONCE_REWRITE_TAC[SET_RULE
     `{x | q <= (f x)$k} = {x | f x IN {y | q <= y$k}}`] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_PREIMAGE_CLOSED THEN
    ASM_REWRITE_TAC[drop; GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE]]);;

let LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LT = prove
 (`!f:real^M->real^N k.
        f measurable_on (:real^M)
        ==> lebesgue_measurable {pastecart x (y:real^N) | y$k < (f x)$k}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `f < y <=> ~(--f <= --y)`] THEN
  MP_TAC(ISPECL [`(--) o (f:real^M->real^N)`; `k:num`]
    LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
    SIMP_TAC[CONTINUOUS_ON_NEG; CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  MP_TAC(ISPEC
   `\z:real^(M,N)finite_sum. pastecart (fstcart z) (--sndcart z)`
   LEBESGUE_MEASURABLE_LINEAR_IMAGE_EQ) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; PASTECART_INJ; VECTOR_EQ_NEG2;
              GSYM PASTECART_EQ] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[linear; PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART;
                FSTCART_ADD; FSTCART_CMUL; SNDCART_ADD; SNDCART_CMUL] THEN
    VECTOR_ARITH_TAC;
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th])] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM LEBESGUE_MEASURABLE_COMPL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `UNIV DIFF s = t <=> s = UNIV DIFF t`] THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_PASTECART_THM; o_DEF;
              FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; REAL_NEG_NEG] THEN
  MESON_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_NEG_NEG]);;

let LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE_EQ,
    LEBESGUE_MEASURABLE_FUNCTION_ORTHANT_SET_LE_EQ = (CONJ_PAIR o prove)
 (`(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !k. 1 <= k /\ k <= dimindex(:N)
            ==> lebesgue_measurable
                  {pastecart x (y:real^N) | y$k <= (f x)$k}) /\
   (!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        lebesgue_measurable
          {pastecart x (y:real^N) | !k. 1 <= k /\ k <= dimindex(:N)
                                        ==> y$k <= (f x)$k})`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (q ==> r) /\ (r ==> p)
    ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE];
    SUBGOAL_THEN
     `{ pastecart x y |
        !k. 1 <= k /\ k <= dimindex(:N)
            ==> (y:real^N)$k <= (f:real^M->real^N) x$k } =
      INTERS {{ pastecart x y | (y:real^N)$k <= (f:real^M->real^N) x$k} |
                k IN 1..dimindex(:N)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[INTERS_GSPEC; EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_INJ] THEN MESON_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_INTERS THEN
      SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; IN_NUMSEG]];
    MP_TAC(ISPECL
     [`f:real^M->real^N`;
      `{y | lebesgue_measurable
              {x | !k. 1 <= k /\ k <= dimindex (:N)
                       ==> (y:real^N)$k <= (f:real^M->real^N) x$k}}`]
     MEASURABLE_ON_PREIMAGE_ORTHANT_GE_DENSE) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; real_ge] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_LEBESGUE_MEASURABLE_ALT) THEN
    REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN
    REWRITE_TAC[SET_RULE `s = UNIV <=> UNIV DIFF s = {}`] THEN
    REWRITE_TAC[GSYM INTERIOR_COMPLEMENT; NEGLIGIBLE_EMPTY_INTERIOR]]);;

let LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LT_EQ,
    LEBESGUE_MEASURABLE_FUNCTION_ORTHANT_SET_LT_EQ = (CONJ_PAIR o prove)
 (`(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !k. 1 <= k /\ k <= dimindex(:N)
            ==> lebesgue_measurable
                  {pastecart x (y:real^N) | y$k < (f x)$k}) /\
   (!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        lebesgue_measurable
          {pastecart x (y:real^N) | !k. 1 <= k /\ k <= dimindex(:N)
                                        ==> y$k < (f x)$k})`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (q ==> r) /\ (r ==> p)
    ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LT];
    SUBGOAL_THEN
     `{ pastecart x y |
        !k. 1 <= k /\ k <= dimindex(:N)
            ==> (y:real^N)$k < (f:real^M->real^N) x$k } =
      INTERS {{ pastecart x y | (y:real^N)$k < (f:real^M->real^N) x$k} |
                k IN 1..dimindex(:N)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[INTERS_GSPEC; EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_INJ] THEN MESON_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_INTERS THEN
      SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; IN_NUMSEG]];
    MP_TAC(ISPECL
     [`f:real^M->real^N`;
      `{y | lebesgue_measurable
              {x | !k. 1 <= k /\ k <= dimindex (:N)
                       ==> (y:real^N)$k < (f:real^M->real^N) x$k}}`]
     MEASURABLE_ON_PREIMAGE_ORTHANT_GT_DENSE) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; real_gt] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_LEBESGUE_MEASURABLE_ALT) THEN
    REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN
    REWRITE_TAC[SET_RULE `s = UNIV <=> UNIV DIFF s = {}`] THEN
    REWRITE_TAC[GSYM INTERIOR_COMPLEMENT; NEGLIGIBLE_EMPTY_INTERIOR]]);;

let NEGLIGIBLE_MEASURABLE_FUNCTION_GRAPH = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) ==> negligible {pastecart x y | f x = y}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_DISJOINT_TRANSLATES THEN
  EXISTS_TAC `{pastecart (vec 0:real^M) x | x IN (:real^N)}` THEN
  EXISTS_TAC `vec 0:real^(M,N)finite_sum` THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `{pastecart x y | (f:real^M->real^N) x = y} =
      INTERS {{pastecart x y | y$i <= (f x)$i} DIFF
              {pastecart x y | y$i < (f x)$i} | i IN 1..dimindex(:N)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; INTERS_GSPEC; EXTENSION; FORALL_PASTECART] THEN
      REWRITE_TAC[IN_ELIM_PASTECART_THM; IN_NUMSEG] THEN
      ONCE_REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[IN_ELIM_PASTECART_THM; IN_DIFF; REAL_NOT_LT] THEN
      REWRITE_TAC[REAL_LE_ANTISYM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_INTERS THEN
    SIMP_TAC[FINITE_IMAGE; SIMPLE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG] THEN X_GEN_TAC `k:num` THEN
    STRIP_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE;
                 LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LT];
    MATCH_MP_TAC CONNECTED_IMP_PERFECT THEN
    REWRITE_TAC[GSYM PCROSS; SET_RULE
     `{f a x | x IN s} = {f w x | w IN {a} /\ x IN s}`] THEN
    REWRITE_TAC[GSYM PASTECART_VEC; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[CONNECTED_SING; CONNECTED_PCROSS_EQ; CONNECTED_UNIV] THEN
    REWRITE_TAC[IN_SING; IN_UNIV] THEN MATCH_MP_TAC(SET_RULE
     `!a b. a IN s /\ b IN s /\ ~(a = b) ==> ~(?a. s = {a})`) THEN
    EXISTS_TAC `pastecart (vec 0:real^M) (vec 0:real^N)` THEN
    EXISTS_TAC `pastecart (vec 0:real^M) (vec 1:real^N)` THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING; IN_UNIV] THEN
    REWRITE_TAC[PASTECART_INJ; VEC_EQ; ARITH_EQ];

    REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; PASTECART_INJ] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; PASTECART_INJ; FORALL_IN_IMAGE;
      SET_RULE `DISJOINT s t <=> !x. x IN s ==> !y. y IN t ==> ~(x = y)`] THEN
    REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; PASTECART_INJ] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^N`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x':real^M`; `y':real^N`] THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
    ASM_CASES_TAC `x':real^M = x` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(a:real^N = b)` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    CONV_TAC VECTOR_ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Hence relate integrals and "area under curve" for functions into R^+.     *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_IFF_LEBESGUE_MEASURABLE_UNDER_CURVE = prove
 (`!f:real^N->real^1.
        (!x. &0 <= drop(f x))
        ==> (f measurable_on (:real^N) <=>
             lebesgue_measurable { pastecart x y | y IN interval[vec 0,f x]})`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE_EQ] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; IN_INTERVAL_1; GSYM drop; DROP_VEC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN
     `{pastecart x y | &0 <= drop y /\ drop y <= drop (f x)} =
      (:real^N) PCROSS {y | &0 <= drop y} INTER
      {pastecart (x:real^N) y | drop y <= drop (f x)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  IN_INTER; IN_ELIM_PASTECART_THM] THEN
      REWRITE_TAC[IN_UNIV; IN_ELIM_THM];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_PCROSS; LEBESGUE_MEASURABLE_UNIV] THEN
      SIMP_TAC[LEBESGUE_MEASURABLE_CLOSED; GSYM real_ge; drop;
               CLOSED_HALFSPACE_COMPONENT_GE]];
    SUBGOAL_THEN
     `{pastecart (x:real^N) y | drop y <= drop (f x)} =
      {pastecart x y | &0 <= drop y /\ drop y <= drop (f x)} UNION
       (:real^N) PCROSS {y | drop y < &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  IN_UNION; IN_ELIM_PASTECART_THM] THEN
      REWRITE_TAC[IN_UNIV; IN_ELIM_THM] THEN
      ASM_MESON_TAC[REAL_NOT_LE; REAL_LT_IMP_LE; REAL_LE_TRANS];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_UNION THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_PCROSS; LEBESGUE_MEASURABLE_UNIV] THEN
      SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; drop;
               OPEN_HALFSPACE_COMPONENT_LT]]]);;

let INTEGRABLE_IFF_MEASURABLE_UNDER_CURVE = prove
 (`!f:real^N->real^1.
        (!x. &0 <= drop(f x))
        ==> (f integrable_on (:real^N) <=>
             measurable { pastecart x y | y IN interval[vec 0,f x]})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) FUBINI_TONELLI_MEASURE o snd) THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM; SET_RULE `{x | x IN s} = s`] THEN
    ASM_SIMP_TAC[MEASURE_INTERVAL_1; DROP_VEC; REAL_SUB_RZERO; LIFT_DROP] THEN
    REWRITE_TAC[MEASURABLE_INTERVAL; EMPTY_GSPEC; NEGLIGIBLE_EMPTY] THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `{pastecart x y | y IN interval [vec 0,f x]} =
      {pastecart x y | drop y <= drop(f x)} INTER
      (:real^N) PCROSS {x | &0 <= drop x}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_INTER; IN_ELIM_PASTECART_THM;
                  PASTECART_IN_PCROSS; IN_UNIV] THEN
      REWRITE_TAC[IN_INTERVAL_1; IN_ELIM_THM; DROP_VEC; CONJ_SYM];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN REWRITE_TAC[drop] THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE;
                   INTEGRABLE_IMP_MEASURABLE; LEBESGUE_MEASURABLE_PCROSS] THEN
      REPEAT DISJ2_TAC THEN REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_CLOSED THEN
      REWRITE_TAC[drop; GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE]];
    FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_MEASURE) THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM; SET_RULE `{x | x IN s} = s`] THEN
    ASM_SIMP_TAC[MEASURE_INTERVAL_1; DROP_VEC; REAL_SUB_RZERO; LIFT_DROP] THEN
    REWRITE_TAC[ETA_AX; GSYM LIFT_EQ] THEN MESON_TAC[integrable_on]]);;

let HAS_INTEGRAL_MEASURE_UNDER_CURVE = prove
 (`!f:real^N->real^1 m.
        (!x. &0 <= drop(f x))
        ==> ((f has_integral lift m) (:real^N) <=>
             { pastecart x y | y IN interval[vec 0,f x]} has_measure m)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE;
              HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  MATCH_MP_TAC(TAUT
   `(p <=> p') /\ (p /\ p' ==> (q <=> q')) ==> (p /\ q <=> p' /\ q')`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[INTEGRABLE_IFF_MEASURABLE_UNDER_CURVE]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_MEASURE) THEN
  REWRITE_TAC[IN_ELIM_PASTECART_THM; SET_RULE `{x | x IN s} = s`] THEN
  ASM_REWRITE_TAC[MEASURE_INTERVAL_1; DROP_VEC; REAL_SUB_RZERO; LIFT_DROP] THEN
  REWRITE_TAC[ETA_AX; GSYM LIFT_EQ] THEN
  ASM_MESON_TAC[integrable_on; INTEGRAL_UNIQUE]);;

(* ------------------------------------------------------------------------- *)
(* Some miscellanous lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_COMPOSE_FSTCART = prove
 (`!f:real^M->real^P.
        f measurable_on (:real^M)
        ==> (\z:real^(M,N)finite_sum. f(fstcart z)) measurable_on
            (:real^(M,N)finite_sum)`,
  GEN_TAC THEN REWRITE_TAC[measurable_on; LEFT_IMP_EXISTS_THM; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `g:num->real^M->real^P`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `(k:real^M->bool) PCROSS (:real^N)` THEN
  EXISTS_TAC `(\n z. g n (fstcart z)):num->real^(M,N)finite_sum->real^P` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_PCROSS; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_FSTCART; LINEAR_CONTINUOUS_ON] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let MEASURABLE_ON_COMPOSE_SNDCART = prove
 (`!f:real^N->real^P.
        f measurable_on (:real^N)
        ==> (\z:real^(M,N)finite_sum. f(sndcart z)) measurable_on
            (:real^(M,N)finite_sum)`,
  GEN_TAC THEN REWRITE_TAC[measurable_on; LEFT_IMP_EXISTS_THM; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `g:num->real^N->real^P`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `(:real^M) PCROSS (k:real^N->bool)` THEN
  EXISTS_TAC `(\n z. g n (sndcart z)):num->real^(M,N)finite_sum->real^P` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_PCROSS; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  IN_UNIV; SNDCART_PASTECART; SNDCART_PASTECART] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let MEASURABLE_ON_COMPOSE_SUB = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M)
        ==> (\z. f(fstcart z - sndcart z))
            measurable_on (:real^(M,M)finite_sum)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. f(fstcart z - sndcart z)):real^(M,M)finite_sum->real^N =
    (\z. f(fstcart z)) o
    (\z. pastecart (fstcart z - sndcart z) (sndcart z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    W(MP_TAC o PART_MATCH (lhs o rand) MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN o
      snd)] THEN
  REWRITE_TAC[FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PASTECART_INJ] THEN
    CONJ_TAC THENL [MATCH_MP_TAC LINEAR_PASTECART; CONV_TAC VECTOR_ARITH] THEN
    SIMP_TAC[LINEAR_SNDCART; LINEAR_FSTCART; LINEAR_COMPOSE_SUB];
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^(M,M)finite_sum)` THEN
    ASM_SIMP_TAC[MEASURABLE_ON_COMPOSE_FSTCART; SUBSET_UNIV] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN THEN
    REWRITE_TAC[LE_REFL; LEBESGUE_MEASURABLE_UNIV] THEN
    MATCH_MP_TAC LINEAR_PASTECART THEN
    SIMP_TAC[LINEAR_SNDCART; LINEAR_FSTCART; LINEAR_COMPOSE_SUB]]);;

(* ------------------------------------------------------------------------- *)
(* Fubini for absolute integrability.                                        *)
(* ------------------------------------------------------------------------- *)

let FUBINI_ABSOLUTELY_INTEGRABLE = prove
 (`!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on (:real^(M,N)finite_sum)
        ==> negligible
             {x | ~((\y. f(pastecart x y))
                     absolutely_integrable_on (:real^N))} /\
            ((\x. integral (:real^N) (\y. f(pastecart x y))) has_integral
             integral (:real^(M,N)finite_sum) f) (:real^M)`,
  let lemma = prove
   (`{x | ~(!i. i IN k ==> P i x)} = UNIONS {{x | ~P i x} | i IN k}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
  let assoclemma = prove
   (`!P:real^(M,N)finite_sum->real^P->bool.
          {pastecart x y | P x y} has_measure m
          ==> {pastecart x (pastecart y z) | P (pastecart x y) z}
              has_measure m`,
    GEN_TAC THEN MP_TAC(ISPECL
     [`\z. pastecart (fstcart(fstcart z):real^M)
                     (pastecart (sndcart(fstcart z):real^N)
                                (sndcart z:real^P))`;
      `{pastecart (x:real^(M,N)finite_sum) (y:real^P) | P x y}`;
      `m:real`] HAS_MEASURE_ISOMETRY) THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_AC] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC LINEAR_PASTECART THEN CONJ_TAC) THEN
        REWRITE_TAC[GSYM o_DEF] THEN
        REPEAT(MATCH_MP_TAC LINEAR_COMPOSE THEN CONJ_TAC) THEN
        REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART];
        SIMP_TAC[FORALL_PASTECART; NORM_EQ; GSYM NORM_POW_2; SQNORM_PASTECART;
                 FSTCART_PASTECART; SNDCART_PASTECART; REAL_ADD_AC]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC[FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART;
                  IN_ELIM_THM; EXISTS_PASTECART; PASTECART_INJ] THEN
      MESON_TAC[]]) in
  let FUBINI_LEMMA = prove
   (`!f:real^(M,N)finite_sum->real^1.
          f integrable_on (:real^(M,N)finite_sum) /\ (!x. &0 <= drop(f x))
          ==> negligible {x | ~((f o pastecart x) integrable_on (:real^N))} /\
              ((\x. integral (:real^N) (f o pastecart x)) has_integral
               integral (:real^(M,N)finite_sum) f) (:real^M)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPEC `f:real^(M,N)finite_sum->real^1`
      INTEGRABLE_IFF_MEASURABLE_UNDER_CURVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `measurable { pastecart x (pastecart y z) |
                   z IN interval[vec 0,(f:real^(M,N)finite_sum->real^1)
                                       (pastecart x y)] }`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [measurable]) THEN
      REWRITE_TAC[measurable] THEN MATCH_MP_TAC MONO_EXISTS THEN
      REWRITE_TAC[assoclemma];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_MEASURE) THEN
    REWRITE_TAC[IN_ELIM_THM; PASTECART_INJ] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    REWRITE_TAC[SET_RULE
     `{x | ?y z. P y z /\ x = pastecart y z} =
      {pastecart y z | P y z}`] THEN
    MP_TAC(GEN `x:real^M` (ISPEC
       `(f:real^(M,N)finite_sum->real^1) o pastecart x`
          INTEGRABLE_IFF_MEASURABLE_UNDER_CURVE)) THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `y = z /\ ((f has_integral y) s ==> (g has_integral y) s)
      ==> (f has_integral y) s ==> (g has_integral z) s`) THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
      ASM_SIMP_TAC[HAS_INTEGRAL_MEASURE_UNDER_CURVE] THEN
      ASM_REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
      MATCH_MP_TAC assoclemma THEN
      ASM_REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE];
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
          (REWRITE_RULE[CONJ_ASSOC] HAS_INTEGRAL_SPIKE)) THEN
      EXISTS_TAC
       `{x | ~((\y. (f:real^(M,N)finite_sum->real^1) (pastecart x y))
               integrable_on (:real^N))}` THEN
      ASM_REWRITE_TAC[IN_UNIV; IN_DIFF; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
      ASM_SIMP_TAC[HAS_INTEGRAL_MEASURE_UNDER_CURVE] THEN
      ASM_SIMP_TAC[GSYM HAS_MEASURE_MEASURE]]) in
  let FUBINI_1 = prove
   (`!f:real^(M,N)finite_sum->real^1.
          f absolutely_integrable_on (:real^(M,N)finite_sum)
          ==> negligible
               {x | ~((f o pastecart x) absolutely_integrable_on (:real^N))} /\
              ((\x. integral (:real^N) (f o pastecart x)) has_integral
               integral (:real^(M,N)finite_sum) f) (:real^M)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY ABBREV_TAC
     [`g = \x:real^(M,N)finite_sum. lift (max (&0) (drop(f x)))`;
      `h = \x:real^(M,N)finite_sum. --(lift (min (&0) (drop(f x))))`] THEN
    SUBGOAL_THEN `!x:real^(M,N)finite_sum. &0 <= drop(g x) /\ &0 <= drop(h x)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["g"; "h"] THEN
      REWRITE_TAC[DROP_NEG; LIFT_DROP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(g:real^(M,N)finite_sum->real^1) absolutely_integrable_on UNIV /\
      (h:real^(M,N)finite_sum->real^1) absolutely_integrable_on UNIV`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["g"; "h"] THEN REWRITE_TAC[] THEN CONJ_TAC THEN
      TRY(MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NEG) THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX_1;
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MIN_1] THEN
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX; LIFT_NUM] THEN
      REWRITE_TAC[ABSOLUTELY_INTEGRABLE_0];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(f:real^(M,N)finite_sum->real^1) = \x. g x - h x`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["g"; "h"] THEN
      REWRITE_TAC[FUN_EQ_THM; GSYM DROP_EQ; LIFT_DROP; DROP_SUB; DROP_NEG] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `h:real^(M,N)finite_sum->real^1` FUBINI_LEMMA) THEN
    MP_TAC(ISPEC `g:real^(M,N)finite_sum->real^1` FUBINI_LEMMA) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    ONCE_REWRITE_TAC[TAUT
     `p /\ q ==> r /\ s ==> t <=> p /\ r ==> q /\ s ==> t`] THEN
    REWRITE_TAC[GSYM NEGLIGIBLE_UNION_EQ; o_DEF] THEN DISCH_TAC THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; GSYM DE_MORGAN_THM] THEN
      REWRITE_TAC[CONTRAPOS_THM; o_DEF] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
      CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
      ASM_REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; IN_UNIV];
      ASM_SIMP_TAC[INTEGRAL_SUB; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
       (REWRITE_RULE[CONJ_ASSOC] HAS_INTEGRAL_SPIKE))) THEN
      FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
          CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNION; IN_ELIM_THM] THEN
      SIMP_TAC[DE_MORGAN_THM; INTEGRAL_SUB]]) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_COMPONENTWISE] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; lemma] THEN
    MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG];
    DISCH_TAC THEN
    ONCE_REWRITE_TAC[HAS_INTEGRAL_COMPONENTWISE]] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
    [ABSOLUTELY_INTEGRABLE_COMPONENTWISE]) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_1) THEN SIMP_TAC[o_DEF] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ASM_SIMP_TAC[LIFT_INTEGRAL_COMPONENT;
               ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] (REWRITE_RULE[CONJ_ASSOC]
        HAS_INTEGRAL_SPIKE)) THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
    CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  REWRITE_TAC[IN_UNIV; IN_DIFF; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[LIFT_INTEGRAL_COMPONENT;
               ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

let FUBINI_ABSOLUTELY_INTEGRABLE_ALT = prove
 (`!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on (:real^(M,N)finite_sum)
        ==> negligible
             {y | ~((\x. f(pastecart x y))
                     absolutely_integrable_on (:real^M))} /\
            ((\y. integral (:real^M) (\x. f(pastecart x y))) has_integral
             integral (:real^(M,N)finite_sum) f) (:real^N)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
   [GSYM ABSOLUTELY_INTEGRABLE_PASTECART_SYM_UNIV]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[INTEGRAL_PASTECART_SYM_UNIV]);;

let FUBINI_INTEGRAL = prove
 (`!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on UNIV
        ==> integral UNIV f =
            integral UNIV (\x. integral UNIV (\y. f(pastecart x y)))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o CONJUNCT2 o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REFL_TAC);;

let FUBINI_INTEGRAL_ALT = prove
 (`!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on UNIV
        ==> integral UNIV f =
            integral UNIV (\y. integral UNIV (\x. f(pastecart x y)))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
    (MP_TAC o CONJUNCT2 o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE_ALT) THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REFL_TAC);;

let FUBINI_INTEGRAL_INTERVAL = prove
 (`!f:real^(M,N)finite_sum->real^P a b c d.
        f absolutely_integrable_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[pastecart a c,pastecart b d]) f =
            integral (interval[a,b])
                     (\x. integral (interval[c,d])
                                   (\y. f(pastecart x y)))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_INTEGRAL) THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; GSYM PCROSS_INTERVAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGRAL_0] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV]);;

let FUBINI_INTEGRAL_INTERVAL_ALT = prove
 (`!f:real^(M,N)finite_sum->real^P a b c d.
        f absolutely_integrable_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[pastecart a c,pastecart b d]) f =
            integral (interval[c,d])
                     (\y. integral (interval[a,b])
                                   (\x. f(pastecart x y)))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_INTEGRAL_ALT) THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; GSYM PCROSS_INTERVAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGRAL_0] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV]);;

let INTEGRAL_PASTECART_CONTINUOUS = prove
 (`!f:real^(M,N)finite_sum->real^P a b c d.
        f continuous_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[pastecart a c,pastecart b d]) f =
            integral (interval[a,b])
                     (\x. integral (interval[c,d])
                                   (\y. f(pastecart x y)))`,
  SIMP_TAC[FUBINI_INTEGRAL_INTERVAL; ABSOLUTELY_INTEGRABLE_CONTINUOUS]);;

let INTEGRAL_SWAP_CONTINUOUS = prove
 (`!f:real^M->real^N->real^P a b c d.
        (\z. f (fstcart z) (sndcart z))
        continuous_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[a,b]) (\x. integral (interval[c,d]) (f x)) =
            integral (interval[c,d])
                     (\y. integral (interval[a,b]) (\x. f x y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_CONTINUOUS) THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(MATCH_MP FUBINI_INTEGRAL_INTERVAL_ALT th) THEN
    MP_TAC(MATCH_MP FUBINI_INTEGRAL_INTERVAL th)) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ETA_AX]);;

let FUBINI_TONELLI = prove
 (`!f:real^(M,N)finite_sum->real^P.
   f measurable_on (:real^(M,N)finite_sum)
   ==> (f absolutely_integrable_on (:real^(M,N)finite_sum) <=>
        negligible
          {x | ~((\y. f(pastecart x y)) absolutely_integrable_on (:real^N))} /\
        (\x. integral (:real^N) (\y. lift(norm(f(pastecart x y)))))
        integrable_on (:real^M))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
    DISCH_THEN(MP_TAC o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_INTEGRAL_INTEGRABLE);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE] THEN ABBREV_TAC
    `g = \n x. if x IN interval[--vec n,vec n]
               then lift(min (norm ((f:real^(M,N)finite_sum->real^P) x)) (&n))
               else vec 0` THEN
  SUBGOAL_THEN
   `!n. (g:num->real^(M,N)finite_sum->real^1) n absolutely_integrable_on UNIV`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    REWRITE_TAC[IN_UNIV; DIMINDEX_1; FORALL_1] THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; GSYM drop; LIFT_DROP; DROP_VEC] THEN
    CONJ_TAC THENL [CONV_TAC NORM_ARITH; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_CASES THEN
    REWRITE_TAC[INTEGRABLE_0; IN_UNIV; SET_RULE `{x | x IN s} = s`] THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x:real^(M,N)finite_sum. lift(&n)` THEN
    REWRITE_TAC[INTEGRABLE_CONST; NORM_LIFT; LIFT_DROP] THEN
    SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 <= x ==> abs(min x (&n)) <= &n`] THEN
    MP_TAC(ISPECL
     [`\x. lift(norm((f:real^(M,N)finite_sum->real^P) x))`;
      `\x:real^(M,N)finite_sum. lift(&n)`;
      `interval[--vec n:real^(M,N)finite_sum,vec n]`] MEASURABLE_ON_MIN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^(M,N)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_INTERVAL] THEN
      ASM_SIMP_TAC[MEASURABLE_ON_NORM; MEASURABLE_ON_CONST];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA] THEN
      REWRITE_TAC[DIMINDEX_1; LIFT_DROP; FORALL_1; GSYM drop]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`g:num->real^(M,N)finite_sum->real^1`;
    `\x. lift(norm((f:real^(M,N)finite_sum->real^P) x))`;
    `(:real^(M,N)finite_sum)`]
   MONOTONE_CONVERGENCE_INCREASING) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; IN_UNIV] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[LIFT_DROP]) THEN
    REWRITE_TAC[REAL_LE_REFL; DROP_VEC; GSYM REAL_OF_NUM_SUC] THEN
    TRY(CONV_TAC NORM_ARITH) THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (TAUT `~p ==> p ==> q`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s SUBSET t ==> x IN t`)) THEN
    REWRITE_TAC[SUBSET_INTERVAL; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REPEAT STRIP_TAC THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `z:real^(M,N)finite_sum` THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN
    MP_TAC(ISPEC `&1 + max (norm z) (norm((f:real^(M,N)finite_sum->real^P) z))`
        REAL_ARCH_SIMPLE) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN DISCH_TAC THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[REAL_ARITH `min a b = a <=> a <= b`] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (TAUT `~p ==> p ==> q`)) THEN
      REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
      REWRITE_TAC[GSYM REAL_ABS_BOUNDS] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(x$i) <= norm(x:real^N) /\ norm x <= a ==> abs(x$i) <= a`) THEN
      REWRITE_TAC[COMPONENT_LE_NORM] THEN ASM_REAL_ARITH_TAC];
    MP_TAC(GEN `n:num` (ISPEC `(g:num->real^(M,N)finite_sum->real^1) n`
      FUBINI_ABSOLUTELY_INTEGRABLE)) THEN
    ASM_REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th ->
     REWRITE_TAC[GSYM(MATCH_MP INTEGRAL_UNIQUE (SPEC `n:num` th))]) THEN
    REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN
    EXISTS_TAC
     `drop(integral (:real^M)
            (\x. lift(norm(integral (:real^N)
              (\y. lift(norm(
                (f:real^(M,N)finite_sum->real^P) (pastecart x y))))))))` THEN
    X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL_AE THEN
    EXISTS_TAC
     `{x | ~((\y. (f:real^(M,N)finite_sum->real^P)(pastecart x y))
             absolutely_integrable_on (:real^N))} UNION
      {x | ~((\y. (g:num->real^(M,N)finite_sum->real^1) n (pastecart x y))
             absolutely_integrable_on (:real^N))}` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[integrable_on];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE_AE THEN
      EXISTS_TAC
       `{x | ~((\y. (f:real^(M,N)finite_sum->real^P)(pastecart x y))
             absolutely_integrable_on (:real^N))}` THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^M` THEN
      REWRITE_TAC[absolutely_integrable_on; GSYM drop] THEN
      STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
      ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE];
      X_GEN_TAC `x:real^M` THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
      STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC(REAL_ARITH
        `drop a <= norm a /\ x <= drop a==> x <= norm a`) THEN CONJ_TAC
      THENL [REWRITE_TAC[drop; NORM_REAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
      ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_REFL; IN_UNIV] THEN
      X_GEN_TAC `y:real^N` THEN EXPAND_TAC "g" THEN
      COND_CASES_TAC THEN REWRITE_TAC[NORM_0; NORM_POS_LE] THEN
      REWRITE_TAC[NORM_LIFT] THEN CONV_TAC NORM_ARITH]]);;

let FUBINI_TONELLI_ALT = prove
 (`!f:real^(M,N)finite_sum->real^P.
   f measurable_on (:real^(M,N)finite_sum)
   ==> (f absolutely_integrable_on (:real^(M,N)finite_sum) <=>
        negligible
          {y | ~((\x. f(pastecart x y)) absolutely_integrable_on (:real^M))} /\
        (\y. integral (:real^M) (\x. lift(norm(f(pastecart x y)))))
        integrable_on (:real^N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC
   `(f:real^(M,N)finite_sum->real^P) o (\z. pastecart (sndcart z) (fstcart z))`
   FUBINI_TONELLI) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN o
        snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_SYM] THEN ANTS_TAC THENL
     [SIMP_TAC[linear; FORALL_PASTECART; FSTCART_PASTECART;
               SNDCART_PASTECART; PASTECART_INJ;
               FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL] THEN
      REWRITE_TAC[GSYM PASTECART_ADD; GSYM PASTECART_CMUL];
      DISCH_THEN SUBST1_TAC THEN POP_ASSUM MP_TAC THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC[IN_UNIV] THEN
      REWRITE_TAC[EXISTS_PASTECART; FORALL_PASTECART] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN MESON_TAC[]];
    REWRITE_TAC[ABSOLUTELY_INTEGRABLE_PASTECART_SYM_UNIV; o_DEF;
                FSTCART_PASTECART; SNDCART_PASTECART]]);;


print_endline "measure.ml loaded"
