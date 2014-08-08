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
include Realanalysis2

let REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG = prove
 (`!f f' s a b.
        COUNTABLE s /\
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval[a,b] DIFF s
             ==> (f has_real_derivative f'(x)) (atreal x))
        ==> (f' has_real_integral (f(b) - f(a))) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG THEN
  EXISTS_TAC `s:real->bool` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
  SIMP_TAC[IN_REAL_INTERVAL; IN_DIFF] THEN REAL_ARITH_TAC);;

let REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT = prove
 (`!f:real->real a b.
        f real_integrable_on real_interval[a,b]
        ==> (\x. real_integral (real_interval[a,x]) f)
            real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_INTEGRABLE_ON]) THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN
  GEN_REWRITE_TAC I [GSYM DROP_EQ] THEN
  REWRITE_TAC[INTERVAL_REAL_INTERVAL; LIFT_DROP; GSYM o_DEF] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL THEN
  MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
  REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC);;

let REAL_INDEFINITE_INTEGRAL_CONTINUOUS_LEFT = prove
 (`!f:real->real a b.
        f real_integrable_on real_interval[a,b]
        ==> (\x. real_integral (real_interval[x,b]) f)
            real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_INTEGRABLE_ON]) THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INDEFINITE_INTEGRAL_CONTINUOUS_LEFT) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN
  GEN_REWRITE_TAC I [GSYM DROP_EQ] THEN
  REWRITE_TAC[INTERVAL_REAL_INTERVAL; LIFT_DROP; GSYM o_DEF] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL THEN
  MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
  REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC);;

let HAS_REAL_DERIVATIVE_ZERO_UNIQUE_STRONG_INTERVAL = prove
 (`!f:real->real a b k y.
        COUNTABLE k /\ f real_continuous_on real_interval[a,b] /\ f a = y /\
        (!x. x IN (real_interval[a,b] DIFF k)
             ==> (f has_real_derivative &0)
                 (atreal x within real_interval[a,b]))
        ==> !x. x IN real_interval[a,b] ==> f x = y`,
  REWRITE_TAC[has_real_integral; HAS_REAL_VECTOR_DERIVATIVE_WITHIN] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_SUB] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE; IMP_CONJ; IN_DIFF] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMP_IMP; GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  REWRITE_TAC[GSYM IMP_CONJ; LIFT_DROP; has_vector_derivative] THEN
  REWRITE_TAC[LIFT_NUM; VECTOR_MUL_RZERO] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`lift o f o drop`; `lift a`; `lift b`; `IMAGE lift k`; `lift y`]
   HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_INTERVAL) THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; o_THM; LIFT_DROP; LIFT_EQ; IN_DIFF] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[LIFT_DROP]);;

let HAS_REAL_DERIVATIVE_ZERO_UNIQUE_STRONG_CONVEX = prove
 (`!f:real->real s k c y.
      is_realinterval s /\ COUNTABLE k /\ f real_continuous_on s /\
      c IN s /\ f c = y /\
      (!x. x IN (s DIFF k) ==> (f has_real_derivative &0) (atreal x within s))
      ==> !x. x IN s ==> f x = y`,
  REWRITE_TAC[has_real_integral; HAS_REAL_VECTOR_DERIVATIVE_WITHIN] THEN
  REWRITE_TAC[IS_REALINTERVAL_CONVEX; REAL_CONTINUOUS_ON] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_SUB] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE; IMP_CONJ; IN_DIFF] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMP_IMP; GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  REWRITE_TAC[GSYM IMP_CONJ; LIFT_DROP; has_vector_derivative] THEN
  REWRITE_TAC[LIFT_NUM; VECTOR_MUL_RZERO] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`lift o f o drop`; `IMAGE lift s`; `IMAGE lift k`; `lift c`; `lift y`]
   HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_CONVEX) THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; o_THM; LIFT_DROP; LIFT_EQ; IN_DIFF] THEN
  ASM_REWRITE_TAC[LIFT_IN_IMAGE_LIFT; FORALL_IN_IMAGE; LIFT_DROP] THEN
  ASM_SIMP_TAC[IMP_CONJ; FORALL_IN_IMAGE; LIFT_IN_IMAGE_LIFT]);;

let HAS_REAL_DERIVATIVE_INDEFINITE_INTEGRAL = prove
 (`!f a b.
        f real_integrable_on real_interval[a,b]
        ==> ?k. real_negligible k /\
                !x. x IN real_interval[a,b] DIFF k
                    ==> ((\x. real_integral(real_interval[a,x]) f)
                         has_real_derivative
                         f(x)) (atreal x within real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift a`; `lift b`]
        HAS_VECTOR_DERIVATIVE_INDEFINITE_INTEGRAL) THEN
  ASM_REWRITE_TAC[GSYM REAL_INTEGRABLE_ON; GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[IN_DIFF; FORALL_IN_IMAGE; IMP_CONJ] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE drop k` THEN
  ASM_REWRITE_TAC[real_negligible; HAS_REAL_VECTOR_DERIVATIVE_WITHIN] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  REWRITE_TAC[IN_IMAGE; GSYM LIFT_EQ; LIFT_DROP; UNWIND_THM1] THEN
  X_GEN_TAC `x:real` THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM; LIFT_DROP] THEN MATCH_MP_TAC(REWRITE_RULE
   [TAUT `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> d ==> e`]
        HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN) THEN
  EXISTS_TAC `&1` THEN ASM_SIMP_TAC[FUN_IN_IMAGE; REAL_LT_01] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `y:real` THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; o_THM] THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_INTEGRAL THEN
  MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  ASM_REAL_ARITH_TAC);;

let HAS_REAL_INTEGRAL_RESTRICT = prove
 (`!f:real->real s t.
        s SUBSET t
        ==> (((\x. if x IN s then f x else &0) has_real_integral i) t <=>
             (f has_real_integral i) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_real_integral; o_DEF] THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`; `IMAGE lift t`; `lift i`]
        HAS_INTEGRAL_RESTRICT) THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; IN_IMAGE_LIFT_DROP; o_DEF] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[LIFT_NUM]);;

let HAS_REAL_INTEGRAL_RESTRICT_UNIV = prove
 (`!f:real->real s i.
        ((\x. if x IN s then f x else &0) has_real_integral i) (:real) <=>
         (f has_real_integral i) s`,
  SIMP_TAC[HAS_REAL_INTEGRAL_RESTRICT; SUBSET_UNIV]);;

let HAS_REAL_INTEGRAL_SPIKE_SET_EQ = prove
 (`!f s t y.
        real_negligible(s DIFF t UNION t DIFF s)
        ==> ((f has_real_integral y) s <=> (f has_real_integral y) t)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE_EQ THEN
  EXISTS_TAC `s DIFF t UNION t DIFF s:real->bool` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let HAS_REAL_INTEGRAL_SPIKE_SET = prove
 (`!f s t y.
        real_negligible(s DIFF t UNION t DIFF s) /\
        (f has_real_integral y) s
        ==> (f has_real_integral y) t`,
  MESON_TAC[HAS_REAL_INTEGRAL_SPIKE_SET_EQ]);;

let REAL_INTEGRABLE_SPIKE_SET = prove
 (`!f s t.
        real_negligible(s DIFF t UNION t DIFF s)
        ==> f real_integrable_on s ==> f real_integrable_on t`,
  REWRITE_TAC[real_integrable_on] THEN
  MESON_TAC[HAS_REAL_INTEGRAL_SPIKE_SET_EQ]);;

let REAL_INTEGRABLE_SPIKE_SET_EQ = prove
 (`!f s t.
        real_negligible(s DIFF t UNION t DIFF s)
        ==> (f real_integrable_on s <=> f real_integrable_on t)`,
  MESON_TAC[REAL_INTEGRABLE_SPIKE_SET; UNION_COMM]);;

let REAL_INTEGRAL_SPIKE_SET = prove
 (`!f s t.
        real_negligible(s DIFF t UNION t DIFF s)
        ==> real_integral s f = real_integral t f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE_SET_EQ THEN
  ASM_MESON_TAC[]);;

let HAS_REAL_INTEGRAL_OPEN_INTERVAL = prove
 (`!f a b y. (f has_real_integral y) (real_interval(a,b)) <=>
             (f has_real_integral y) (real_interval[a,b])`,
  REWRITE_TAC[has_real_integral; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[HAS_INTEGRAL_OPEN_INTERVAL]);;

let REAL_INTEGRABLE_ON_OPEN_INTERVAL = prove
 (`!f a b. f real_integrable_on real_interval(a,b) <=>
           f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL_OPEN_INTERVAL]);;

let REAL_INTEGRAL_OPEN_INTERVAL = prove
 (`!f a b. real_integral(real_interval(a,b)) f =
           real_integral(real_interval[a,b]) f`,
  REWRITE_TAC[real_integral; HAS_REAL_INTEGRAL_OPEN_INTERVAL]);;

let HAS_REAL_INTEGRAL_ON_SUPERSET = prove
 (`!f s t.
        (!x. ~(x IN s) ==> f x = &0) /\ s SUBSET t /\ (f has_real_integral i) s
        ==> (f has_real_integral i) t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[]);;

let REAL_INTEGRABLE_ON_SUPERSET = prove
 (`!f s t.
        (!x. ~(x IN s) ==> f x = &0) /\ s SUBSET t /\ f real_integrable_on s
        ==> f real_integrable_on t`,
  REWRITE_TAC[real_integrable_on] THEN
  MESON_TAC[HAS_REAL_INTEGRAL_ON_SUPERSET]);;

let REAL_INTEGRABLE_RESTRICT_UNIV = prove
 (`!f s. (\x. if x IN s then f x else &0) real_integrable_on (:real) <=>
         f real_integrable_on s`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL_RESTRICT_UNIV]);;

let REAL_INTEGRAL_RESTRICT_UNIV = prove
 (`!f s.
     real_integral (:real) (\x. if x IN s then f x else &0) =
     real_integral s f`,
  REWRITE_TAC[real_integral; HAS_REAL_INTEGRAL_RESTRICT_UNIV]);;

let REAL_INTEGRAL_RESTRICT = prove
 (`!f s t.
        s SUBSET t
        ==> real_integral t (\x. if x IN s then f x else &0) =
            real_integral s f`,
  SIMP_TAC[real_integral; HAS_REAL_INTEGRAL_RESTRICT]);;

let HAS_REAL_INTEGRAL_RESTRICT_INTER = prove
 (`!f s t.
        ((\x. if x IN s then f x else &0) has_real_integral i) t <=>
        (f has_real_integral i) (s INTER t)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[IN_INTER] THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

let REAL_INTEGRAL_RESTRICT_INTER = prove
 (`!f s t.
        real_integral t (\x. if x IN s then f x else &0) =
        real_integral (s INTER t) f`,
  REWRITE_TAC[real_integral; HAS_REAL_INTEGRAL_RESTRICT_INTER]);;

let REAL_INTEGRABLE_RESTRICT_INTER = prove
 (`!f s t.
        (\x. if x IN s then f x else &0) real_integrable_on t <=>
        f real_integrable_on (s INTER t)`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL_RESTRICT_INTER]);;

let REAL_NEGLIGIBLE_ON_INTERVALS = prove
 (`!s. real_negligible s <=>
         !a b:real. real_negligible(s INTER real_interval[a,b])`,
  GEN_TAC THEN REWRITE_TAC[real_negligible] THEN
  GEN_REWRITE_TAC LAND_CONV [NEGLIGIBLE_ON_INTERVALS] THEN
  REWRITE_TAC[FORALL_LIFT; GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN AP_TERM_TAC THEN SET_TAC[LIFT_DROP]);;

let HAS_REAL_INTEGRAL_SUBSET_LE = prove
 (`!f:real->real s t i j.
        s SUBSET t /\ (f has_real_integral i) s /\ (f has_real_integral j) t /\
        (!x. x IN t ==> &0 <= f x)
        ==> i <= j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_LE THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real. if x IN s then f(x) else &0`;
    `\x:real. if x IN t then f(x) else &0`; `(:real)`] THEN
  ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV; IN_UNIV] THEN
  X_GEN_TAC `x:real` THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL]) THEN
  ASM SET_TAC[]);;

let REAL_INTEGRAL_SUBSET_LE = prove
 (`!f:real->real s t.
        s SUBSET t /\ f real_integrable_on s /\ f real_integrable_on t /\
        (!x. x IN t ==> &0 <= f(x))
        ==> real_integral s f <= real_integral t f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SUBSET_LE THEN
  ASM_MESON_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRABLE_ON_SUBINTERVAL = prove
 (`!f:real->real s a b.
        f real_integrable_on s /\ real_interval[a,b] SUBSET s
        ==> f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `IMAGE lift s` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
  ASM_SIMP_TAC[IMAGE_SUBSET]);;

let REAL_INTEGRABLE_STRADDLE = prove
 (`!f s.
        (!e. &0 < e
             ==> ?g h i j. (g has_real_integral i) s /\
                           (h has_real_integral j) s /\
                           abs(i - j) < e /\
                           !x. x IN s ==> g x <= f x /\ f x <= h x)
        ==> f real_integrable_on s`,
  REWRITE_TAC[REAL_INTEGRABLE_ON; has_real_integral] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_STRADDLE THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXISTS_DROP; FORALL_IN_IMAGE] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; GSYM DROP_SUB; LIFT_DROP; GSYM ABS_DROP] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real->real`; `h:real->real`; `i:real^1`; `j:real^1`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`lift o g o drop`; `lift o h o drop`; `i:real^1`; `j:real^1`] THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP]);;

let HAS_REAL_INTEGRAL_STRADDLE_NULL = prove
 (`!f g s. (!x. x IN s ==> &0 <= f x /\ f x <= g x) /\
           (g has_real_integral &0) s
           ==> (f has_real_integral &0) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_STRADDLE THEN
    GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(\x. &0):real->real`; `g:real->real`;
      `&0:real`; `&0:real`] THEN
    ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_0; REAL_SUB_REFL; REAL_ABS_NUM];
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`f:real->real`; `g:real->real`]
        HAS_REAL_INTEGRAL_LE);
      MATCH_MP_TAC(ISPECL [`(\x. &0):real->real`; `f:real->real`]
        HAS_REAL_INTEGRAL_LE)] THEN
    EXISTS_TAC `s:real->bool` THEN
    ASM_SIMP_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL; HAS_REAL_INTEGRAL_0]]);;

let HAS_REAL_INTEGRAL_UNION = prove
 (`!f i j s t.
        (f has_real_integral i) s /\ (f has_real_integral j) t /\
        real_negligible(s INTER t)
        ==> (f has_real_integral (i + j)) (s UNION t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_real_integral; real_negligible; LIFT_ADD; IMAGE_UNION] THEN
  DISCH_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_UNION THEN POP_ASSUM MP_TAC THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[LIFT_DROP]);;

let HAS_REAL_INTEGRAL_UNIONS = prove
 (`!f:real->real i t.
        FINITE t /\
        (!s. s IN t ==> (f has_real_integral (i s)) s) /\
        (!s s'. s IN t /\ s' IN t /\ ~(s = s') ==> real_negligible(s INTER s'))
        ==> (f has_real_integral (sum t i)) (UNIONS t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_real_integral; real_negligible; LIFT_ADD; IMAGE_UNIONS] THEN
  SIMP_TAC[LIFT_SUM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `\s. lift(i(IMAGE drop s))`;
                 `IMAGE (IMAGE lift) t`]
    HAS_INTEGRAL_UNIONS) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM;
               IMAGE_LIFT_DROP; GSYM IMAGE_o] THEN
  ASM_SIMP_TAC[LIFT_EQ; SET_RULE
   `(!x y. f x = f y <=> x = y)
    ==> (IMAGE f s = IMAGE f t <=> s = t) /\
        (IMAGE f s INTER IMAGE f t = IMAGE f (s INTER t))`] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[LIFT_DROP]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[o_DEF; GSYM IMAGE_o; IMAGE_LIFT_DROP]);;

let REAL_MONOTONE_CONVERGENCE_INCREASING = prove
 (`!f:num->real->real g s.
        (!k. (f k) real_integrable_on s) /\
        (!k x. x IN s ==> f k x <= f (SUC k) x) /\
        (!x. x IN s ==> ((\k. f k x) ---> g x) sequentially) /\
        real_bounded {real_integral s (f k) | k IN (:num)}
        ==> g real_integrable_on s /\
            ((\k. real_integral s (f k)) ---> real_integral s g) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_INTEGRABLE_ON; TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. lift(f (n:num) (drop x))`;
                 `lift o g o drop`;  `IMAGE lift s`]
                MONOTONE_CONVERGENCE_INCREASING) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_DEF] THEN
  SUBGOAL_THEN
   `!k:num. real_integral s (f k) =
            drop(integral (IMAGE lift s) (lift o f k o drop))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_bounded]) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; GSYM ABS_DROP] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN ANTS_TAC THENL
   [REWRITE_TAC[bounded] THEN EXISTS_TAC `B:real` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN REWRITE_TAC[LIFT_DROP] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_INTEGRAL THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF]);;

let REAL_MONOTONE_CONVERGENCE_DECREASING = prove
 (`!f:num->real->real g s.
        (!k. (f k) real_integrable_on s) /\
        (!k x. x IN s ==> f (SUC k) x <= f k x) /\
        (!x. x IN s ==> ((\k. f k x) ---> g x) sequentially) /\
        real_bounded {real_integral s (f k) | k IN (:num)}
        ==> g real_integrable_on s /\
            ((\k. real_integral s (f k)) ---> real_integral s g) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_INTEGRABLE_ON; TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. lift(f (n:num) (drop x))`;
                 `lift o g o drop`;  `IMAGE lift s`]
                MONOTONE_CONVERGENCE_DECREASING) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_DEF] THEN
  SUBGOAL_THEN
   `!k:num. real_integral s (f k) =
            drop(integral (IMAGE lift s) (lift o f k o drop))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_bounded]) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; GSYM ABS_DROP] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN ANTS_TAC THENL
   [REWRITE_TAC[bounded] THEN EXISTS_TAC `B:real` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN REWRITE_TAC[LIFT_DROP] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_INTEGRAL THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF]);;

let REAL_BEPPO_LEVI_INCREASING = prove
 (`!f s. (!k. (f k) real_integrable_on s) /\
         (!k x. x IN s ==> f k x <= f (SUC k) x) /\
         real_bounded {real_integral s (f k) | k IN (:num)}
         ==> ?g k. real_negligible k /\
                   !x. x IN (s DIFF k) ==> ((\k. f k x) ---> g x) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_INTEGRABLE_ON; TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. lift(f (n:num) (drop x))`;
                 `IMAGE lift s`]
                BEPPO_LEVI_INCREASING) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_DEF] THEN
  SUBGOAL_THEN
   `!k:num. real_integral s (f k) =
            drop(integral (IMAGE lift s) (lift o f k o drop))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_bounded]) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; GSYM ABS_DROP] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN ANTS_TAC THENL
   [REWRITE_TAC[bounded] THEN EXISTS_TAC `B:real` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_DIFF; IMP_CONJ; FORALL_IN_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `k:real^1->bool`] THEN
  REWRITE_TAC[IMP_IMP; LIFT_DROP] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`drop o g o lift`; `IMAGE drop k`] THEN
  ASM_REWRITE_TAC[real_negligible; GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  ASM_REWRITE_TAC[IN_IMAGE_LIFT_DROP; o_THM; LIFT_DROP]);;

let REAL_BEPPO_LEVI_DECREASING = prove
 (`!f s. (!k. (f k) real_integrable_on s) /\
         (!k x. x IN s ==> f (SUC k) x <= f k x) /\
         real_bounded {real_integral s (f k) | k IN (:num)}
         ==> ?g k. real_negligible k /\
                   !x. x IN (s DIFF k) ==> ((\k. f k x) ---> g x) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_INTEGRABLE_ON; TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. lift(f (n:num) (drop x))`;
                 `IMAGE lift s`]
                BEPPO_LEVI_DECREASING) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_DEF] THEN
  SUBGOAL_THEN
   `!k:num. real_integral s (f k) =
            drop(integral (IMAGE lift s) (lift o f k o drop))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_bounded]) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; GSYM ABS_DROP] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN ANTS_TAC THENL
   [REWRITE_TAC[bounded] THEN EXISTS_TAC `B:real` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_DIFF; IMP_CONJ; FORALL_IN_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `k:real^1->bool`] THEN
  REWRITE_TAC[IMP_IMP; LIFT_DROP] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`drop o g o lift`; `IMAGE drop k`] THEN
  ASM_REWRITE_TAC[real_negligible; GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  ASM_REWRITE_TAC[IN_IMAGE_LIFT_DROP; o_THM; LIFT_DROP]);;

let REAL_BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING = prove
 (`!f s.
     (!k. (f k) real_integrable_on s) /\
     (!k x. x IN s ==> f k x <= f (SUC k) x) /\
     real_bounded {real_integral s (f k) | k IN (:num)}
     ==> ?g k. real_negligible k /\
               (!x. x IN (s DIFF k) ==> ((\k. f k x) ---> g x) sequentially) /\
               g real_integrable_on s /\
               ((\k. real_integral s (f k)) ---> real_integral s g)
               sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_INTEGRABLE_ON; TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. lift(f (n:num) (drop x))`;
                 `IMAGE lift s`]
                BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_DEF] THEN
  SUBGOAL_THEN
   `!k:num. real_integral s (f k) =
            drop(integral (IMAGE lift s) (lift o f k o drop))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_bounded]) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; GSYM ABS_DROP] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN ANTS_TAC THENL
   [REWRITE_TAC[bounded] THEN EXISTS_TAC `B:real` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_DIFF; IMP_CONJ; FORALL_IN_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `k:real^1->bool`] THEN
  REWRITE_TAC[IMP_IMP; LIFT_DROP] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`drop o g o lift`; `IMAGE drop k`] THEN
  ASM_REWRITE_TAC[real_negligible; GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  ASM_REWRITE_TAC[IN_IMAGE_LIFT_DROP; o_THM; LIFT_DROP; ETA_AX] THEN
  SUBGOAL_THEN
   `real_integral s (drop o g o lift) =
            drop(integral (IMAGE lift s) (lift o (drop o g o lift) o drop))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF; LIFT_DROP; ETA_AX];
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]]);;

let REAL_BEPPO_LEVI_MONOTONE_CONVERGENCE_DECREASING = prove
 (`!f s.
     (!k. (f k) real_integrable_on s) /\
     (!k x. x IN s ==> f (SUC k) x <= f k x) /\
     real_bounded {real_integral s (f k) | k IN (:num)}
     ==> ?g k. real_negligible k /\
               (!x. x IN (s DIFF k) ==> ((\k. f k x) ---> g x) sequentially) /\
               g real_integrable_on s /\
               ((\k. real_integral s (f k)) ---> real_integral s g)
               sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_INTEGRABLE_ON; TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. lift(f (n:num) (drop x))`;
                 `IMAGE lift s`]
                BEPPO_LEVI_MONOTONE_CONVERGENCE_DECREASING) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_DEF] THEN
  SUBGOAL_THEN
   `!k:num. real_integral s (f k) =
            drop(integral (IMAGE lift s) (lift o f k o drop))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_bounded]) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; GSYM ABS_DROP] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN ANTS_TAC THENL
   [REWRITE_TAC[bounded] THEN EXISTS_TAC `B:real` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_DIFF; IMP_CONJ; FORALL_IN_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `k:real^1->bool`] THEN
  REWRITE_TAC[IMP_IMP; LIFT_DROP] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`drop o g o lift`; `IMAGE drop k`] THEN
  ASM_REWRITE_TAC[real_negligible; GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  ASM_REWRITE_TAC[IN_IMAGE_LIFT_DROP; o_THM; LIFT_DROP; ETA_AX] THEN
  SUBGOAL_THEN
   `real_integral s (drop o g o lift) =
            drop(integral (IMAGE lift s) (lift o (drop o g o lift) o drop))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF; LIFT_DROP; ETA_AX];
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]]);;

let REAL_INTEGRAL_ABS_BOUND_INTEGRAL = prove
 (`!f:real->real g s.
        f real_integrable_on s /\ g real_integrable_on s /\
        (!x. x IN s ==> abs(f x) <= g x)
        ==> abs(real_integral s f) <= real_integral s g`,
  SIMP_TAC[REAL_INTEGRAL; GSYM ABS_DROP] THEN
  SIMP_TAC[REAL_INTEGRABLE_ON; INTEGRAL_NORM_BOUND_INTEGRAL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP; NORM_LIFT]);;

let ABSOLUTELY_REAL_INTEGRABLE_LE = prove
 (`!f:real->real s.
        f absolutely_real_integrable_on s
        ==> abs(real_integral s f) <= real_integral s (\x. abs(f x))`,
  SIMP_TAC[absolutely_real_integrable_on] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

let ABSOLUTELY_REAL_INTEGRABLE_0 = prove
 (`!s. (\x. &0) absolutely_real_integrable_on s`,
  REWRITE_TAC[absolutely_real_integrable_on; REAL_ABS_NUM;
              REAL_INTEGRABLE_0]);;

let ABSOLUTELY_REAL_INTEGRABLE_CONST = prove
 (`!a b c. (\x. c) absolutely_real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[absolutely_real_integrable_on; REAL_INTEGRABLE_CONST]);;

let ABSOLUTELY_REAL_INTEGRABLE_LMUL = prove
 (`!f s c. f absolutely_real_integrable_on s
           ==> (\x. c * f(x)) absolutely_real_integrable_on s`,
  SIMP_TAC[absolutely_real_integrable_on;
           REAL_INTEGRABLE_LMUL; REAL_ABS_MUL]);;

let ABSOLUTELY_REAL_INTEGRABLE_RMUL = prove
 (`!f s c. f absolutely_real_integrable_on s
           ==> (\x. f(x) * c) absolutely_real_integrable_on s`,
  SIMP_TAC[absolutely_real_integrable_on;
           REAL_INTEGRABLE_RMUL; REAL_ABS_MUL]);;

let ABSOLUTELY_REAL_INTEGRABLE_NEG = prove
 (`!f s. f absolutely_real_integrable_on s
         ==> (\x. --f(x)) absolutely_real_integrable_on s`,
  SIMP_TAC[absolutely_real_integrable_on; REAL_INTEGRABLE_NEG; REAL_ABS_NEG]);;

let ABSOLUTELY_REAL_INTEGRABLE_ABS = prove
 (`!f s. f absolutely_real_integrable_on s
         ==> (\x. abs(f x)) absolutely_real_integrable_on s`,
  SIMP_TAC[absolutely_real_integrable_on; REAL_ABS_ABS]);;

let ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL = prove
 (`!f:real->real s a b.
        f absolutely_real_integrable_on s /\ real_interval[a,b] SUBSET s
        ==> f absolutely_real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[absolutely_real_integrable_on] THEN
  MESON_TAC[REAL_INTEGRABLE_ON_SUBINTERVAL]);;

let ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV = prove
 (`!f s. (\x. if x IN s then f x else &0)
              absolutely_real_integrable_on (:real) <=>
         f absolutely_real_integrable_on s`,
  REWRITE_TAC[absolutely_real_integrable_on; REAL_INTEGRABLE_RESTRICT_UNIV;
              COND_RAND; REAL_ABS_NUM]);;

let ABSOLUTELY_REAL_INTEGRABLE_ADD = prove
 (`!f:real->real g s.
        f absolutely_real_integrable_on s /\
        g absolutely_real_integrable_on s
        ==> (\x. f(x) + g(x)) absolutely_real_integrable_on s`,
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  SIMP_TAC[o_DEF; LIFT_ADD; ABSOLUTELY_INTEGRABLE_ADD]);;

let ABSOLUTELY_REAL_INTEGRABLE_SUB = prove
 (`!f:real->real g s.
        f absolutely_real_integrable_on s /\
        g absolutely_real_integrable_on s
        ==> (\x. f(x) - g(x)) absolutely_real_integrable_on s`,
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  SIMP_TAC[o_DEF; LIFT_SUB; ABSOLUTELY_INTEGRABLE_SUB]);;

let ABSOLUTELY_REAL_INTEGRABLE_LINEAR = prove
 (`!f h s.
        f absolutely_real_integrable_on s /\ linear(lift o h o drop)
        ==> (h o f) absolutely_real_integrable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_LINEAR) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let ABSOLUTELY_REAL_INTEGRABLE_SUM = prove
 (`!f:A->real->real s t.
        FINITE t /\
        (!a. a IN t ==> (f a) absolutely_real_integrable_on s)
        ==>  (\x. sum t (\a. f a x)) absolutely_real_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; ABSOLUTELY_REAL_INTEGRABLE_0; IN_INSERT;
           ABSOLUTELY_REAL_INTEGRABLE_ADD; ETA_AX]);;

let ABSOLUTELY_REAL_INTEGRABLE_MAX = prove
 (`!f:real->real g:real->real s.
        f absolutely_real_integrable_on s /\ g absolutely_real_integrable_on s
        ==> (\x. max (f x) (g x))
            absolutely_real_integrable_on s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `max a b = &1 / &2 * ((a + b) + abs(a - b))`] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB; ABSOLUTELY_REAL_INTEGRABLE_ADD;
               ABSOLUTELY_REAL_INTEGRABLE_ABS]);;

let ABSOLUTELY_REAL_INTEGRABLE_MIN = prove
 (`!f:real->real g:real->real s.
        f absolutely_real_integrable_on s /\ g absolutely_real_integrable_on s
        ==> (\x. min (f x) (g x))
            absolutely_real_integrable_on s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `min a b = &1 / &2 * ((a + b) - abs(a - b))`] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB; ABSOLUTELY_REAL_INTEGRABLE_ADD;
               ABSOLUTELY_REAL_INTEGRABLE_ABS]);;

let ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f s. f absolutely_real_integrable_on s ==> f real_integrable_on s`,
  SIMP_TAC[absolutely_real_integrable_on]);;

let ABSOLUTELY_REAL_INTEGRABLE_CONTINUOUS = prove
 (`!f a b.
        f real_continuous_on real_interval[a,b]
        ==> f absolutely_real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[REAL_CONTINUOUS_ON; ABSOLUTELY_REAL_INTEGRABLE_ON;
              has_real_integral;
              GSYM integrable_on; GSYM EXISTS_LIFT] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; ABSOLUTELY_INTEGRABLE_CONTINUOUS]);;

let NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE = prove
 (`!f s.
        (!x. x IN s ==> &0 <= f(x)) /\
        f real_integrable_on s
        ==> f absolutely_real_integrable_on s`,
  SIMP_TAC[absolutely_real_integrable_on] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
  EXISTS_TAC `f:real->real` THEN ASM_SIMP_TAC[real_abs]);;

let ABSOLUTELY_REAL_INTEGRABLE_INTEGRABLE_BOUND = prove
 (`!f:real->real g s.
        (!x. x IN s ==> abs(f x) <= g x) /\
        f real_integrable_on s /\ g real_integrable_on s
        ==> f absolutely_real_integrable_on s`,
  REWRITE_TAC[REAL_INTEGRABLE_ON; ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
  EXISTS_TAC `lift o g o drop` THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP; NORM_LIFT]);;

let ABSOLUTELY_REAL_INTEGRABLE_ABSOLUTELY_REAL_INTEGRABLE_BOUND = prove
 (`!f:real->real g:real->real s.
        (!x. x IN s ==> abs(f x) <= abs(g x)) /\
        f real_integrable_on s /\ g absolutely_real_integrable_on s
        ==> f absolutely_real_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_INTEGRABLE_BOUND THEN
  EXISTS_TAC `\x:real. abs(g x)` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[absolutely_real_integrable_on]) THEN
  ASM_REWRITE_TAC[]);;

let ABSOLUTELY_REAL_INTEGRABLE_ABSOLUTELY_REAL_INTEGRABLE_UBOUND = prove
 (`!f:real->real g:real->real s.
        (!x. x IN s ==> f x <= g x) /\
        f real_integrable_on s /\ g absolutely_real_integrable_on s
        ==> g absolutely_real_integrable_on s`,
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON; REAL_INTEGRABLE_ON] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
   ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_UBOUND THEN
  EXISTS_TAC `lift o g o drop` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; o_THM; LIFT_DROP;
                  GSYM drop]);;

let ABSOLUTELY_REAL_INTEGRABLE_ABSOLUTELY_REAL_INTEGRABLE_LBOUND = prove
 (`!f:real->real g:real->real s.
        (!x. x IN s ==> f x <= g x) /\
        f absolutely_real_integrable_on s /\ g real_integrable_on s
        ==> g absolutely_real_integrable_on s`,
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON; REAL_INTEGRABLE_ON] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
   ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_LBOUND THEN
  EXISTS_TAC `lift o f o drop` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; o_THM; LIFT_DROP;
                  GSYM drop]);;

let ABSOLUTELY_REAL_INTEGRABLE_INF = prove
 (`!fs s:real->bool k:A->bool.
        FINITE k /\ ~(k = {}) /\
        (!i. i IN k ==> (\x. fs x i) absolutely_real_integrable_on s)
        ==> (\x. inf (IMAGE (fs x) k)) absolutely_real_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
  SIMP_TAC[INF_INSERT_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `k:A->bool`] THEN
  ASM_CASES_TAC `k:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[IN_SING; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MIN THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let ABSOLUTELY_REAL_INTEGRABLE_SUP = prove
 (`!fs s:real->bool k:A->bool.
        FINITE k /\ ~(k = {}) /\
        (!i. i IN k ==> (\x. fs x i) absolutely_real_integrable_on s)
        ==> (\x. sup (IMAGE (fs x) k)) absolutely_real_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
  SIMP_TAC[SUP_INSERT_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `k:A->bool`] THEN
  ASM_CASES_TAC `k:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[IN_SING; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MAX THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let REAL_DOMINATED_CONVERGENCE = prove
 (`!f:num->real->real g h s.
        (!k. (f k) real_integrable_on s) /\ h real_integrable_on s /\
        (!k x. x IN s ==> abs(f k x) <= h x) /\
        (!x. x IN s ==> ((\k. f k x) ---> g x) sequentially)
        ==> g real_integrable_on s /\
            ((\k. real_integral s (f k)) ---> real_integral s g) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_INTEGRABLE_ON; TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. lift(f (n:num) (drop x))`;
                 `lift o g o drop`;  `lift o h o drop`; `IMAGE lift s`]
                DOMINATED_CONVERGENCE) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_DEF; NORM_LIFT] THEN
  SUBGOAL_THEN
   `!k:num. real_integral s (f k) =
            drop(integral (IMAGE lift s) (lift o f k o drop))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN REWRITE_TAC[LIFT_DROP] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_INTEGRAL THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF]);;

let HAS_REAL_MEASURE_HAS_MEASURE = prove
 (`!s m. s has_real_measure m <=> (IMAGE lift s) has_measure m`,
  REWRITE_TAC[has_real_measure; has_measure; has_real_integral] THEN
  REWRITE_TAC[o_DEF; LIFT_NUM]);;

let REAL_MEASURABLE_MEASURABLE = prove
 (`!s. real_measurable s <=> measurable(IMAGE lift s)`,
  REWRITE_TAC[real_measurable; measurable; HAS_REAL_MEASURE_HAS_MEASURE]);;

let REAL_MEASURE_MEASURE = prove
 (`!s. real_measure s = measure (IMAGE lift s)`,
  REWRITE_TAC[real_measure; measure; HAS_REAL_MEASURE_HAS_MEASURE]);;

let HAS_REAL_MEASURE_MEASURE = prove
 (`!s. real_measurable s <=> s has_real_measure (real_measure s)`,
  REWRITE_TAC[real_measure; real_measurable] THEN MESON_TAC[]);;

let HAS_REAL_MEASURE_UNIQUE = prove
 (`!s m1 m2. s has_real_measure m1 /\ s has_real_measure m2 ==> m1 = m2`,
  REWRITE_TAC[has_real_measure] THEN MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE]);;

let REAL_MEASURE_UNIQUE = prove
 (`!s m. s has_real_measure m ==> real_measure s = m`,
  MESON_TAC[HAS_REAL_MEASURE_UNIQUE; HAS_REAL_MEASURE_MEASURE;
            real_measurable]);;

let HAS_REAL_MEASURE_REAL_MEASURABLE_REAL_MEASURE = prove
 (`!s m. s has_real_measure m <=> real_measurable s /\ real_measure s = m`,
  REWRITE_TAC[HAS_REAL_MEASURE_MEASURE] THEN MESON_TAC[REAL_MEASURE_UNIQUE]);;

let HAS_REAL_MEASURE_IMP_REAL_MEASURABLE = prove
 (`!s m. s has_real_measure m ==> real_measurable s`,
  REWRITE_TAC[real_measurable] THEN MESON_TAC[]);;

let HAS_REAL_MEASURE = prove
 (`!s m. s has_real_measure m <=>
              ((\x. if x IN s then &1 else &0) has_real_integral m) (:real)`,
  SIMP_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV; has_real_measure]);;

let REAL_MEASURABLE = prove
 (`!s. real_measurable s <=> (\x. &1) real_integrable_on s`,
  REWRITE_TAC[real_measurable; real_integrable_on;
              has_real_measure; EXISTS_DROP; LIFT_DROP]);;

let REAL_MEASURABLE_REAL_INTEGRABLE = prove
 (`real_measurable s <=>
    (\x. if x IN s then &1 else &0) real_integrable_on UNIV`,
  REWRITE_TAC[real_measurable; real_integrable_on; HAS_REAL_MEASURE]);;

let REAL_MEASURE_REAL_INTEGRAL = prove
 (`!s. real_measurable s ==> real_measure s = real_integral s (\x. &1)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_REWRITE_TAC[GSYM has_real_measure; GSYM HAS_REAL_MEASURE_MEASURE]);;

let REAL_MEASURE_REAL_INTEGRAL_UNIV = prove
 (`!s. real_measurable s
       ==> real_measure s =
           real_integral UNIV (\x. if x IN s then &1 else &0)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_MEASURE; GSYM HAS_REAL_MEASURE_MEASURE]);;

let REAL_INTEGRAL_REAL_MEASURE = prove
 (`!s. real_measurable s ==> real_integral s (\x. &1) = real_measure s`,
  SIMP_TAC[GSYM DROP_EQ; LIFT_DROP; REAL_MEASURE_REAL_INTEGRAL]);;

let REAL_INTEGRAL_REAL_MEASURE_UNIV = prove
 (`!s. real_measurable s
       ==> real_integral UNIV (\x. if x IN s then &1 else &0) =
           real_measure s`,
  SIMP_TAC[REAL_MEASURE_REAL_INTEGRAL_UNIV]);;

let HAS_REAL_MEASURE_REAL_INTERVAL = prove
 (`(!a b. real_interval[a,b] has_real_measure (max (b - a) (&0))) /\
   (!a b. real_interval(a,b) has_real_measure (max (b - a) (&0)))`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_INTERVAL;
              MEASURE_INTERVAL] THEN
  REWRITE_TAC[CONTENT_CLOSED_INTERVAL_CASES; DIMINDEX_1; FORALL_1] THEN
  REWRITE_TAC[PRODUCT_1; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC);;

let REAL_MEASURABLE_REAL_INTERVAL = prove
 (`(!a b. real_measurable (real_interval[a,b])) /\
   (!a b. real_measurable (real_interval(a,b)))`,
  REWRITE_TAC[real_measurable] THEN
  MESON_TAC[HAS_REAL_MEASURE_REAL_INTERVAL]);;

let REAL_MEASURE_REAL_INTERVAL = prove
 (`(!a b. real_measure(real_interval[a,b]) = max (b - a) (&0)) /\
   (!a b. real_measure(real_interval(a,b)) = max (b - a) (&0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  REWRITE_TAC[HAS_REAL_MEASURE_REAL_INTERVAL]);;

let REAL_MEASURABLE_INTER = prove
 (`!s t. real_measurable s /\ real_measurable t
         ==> real_measurable (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_INTER) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[LIFT_DROP]);;

let REAL_MEASURABLE_UNION = prove
 (`!s t. real_measurable s /\ real_measurable t
         ==> real_measurable (s UNION t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_UNION) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[LIFT_DROP]);;

let HAS_REAL_MEASURE_DISJOINT_UNION = prove
 (`!s1 s2 m1 m2. s1 has_real_measure m1 /\ s2 has_real_measure m2 /\
                 DISJOINT s1 s2
                 ==> (s1 UNION s2) has_real_measure (m1 + m2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; IMAGE_UNION] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_DISJOINT_UNION THEN
  ASM SET_TAC[LIFT_DROP]);;

let REAL_MEASURE_DISJOINT_UNION = prove
 (`!s t. real_measurable s /\ real_measurable t /\ DISJOINT s t
         ==> real_measure(s UNION t) = real_measure s + real_measure t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_DISJOINT_UNION;
               GSYM HAS_REAL_MEASURE_MEASURE]);;

let HAS_REAL_MEASURE_POS_LE = prove
 (`!m s. s has_real_measure m ==> &0 <= m`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; HAS_MEASURE_POS_LE]);;

let REAL_MEASURE_POS_LE = prove
 (`!s. real_measurable s ==> &0 <= real_measure s`,
  REWRITE_TAC[HAS_REAL_MEASURE_MEASURE; HAS_REAL_MEASURE_POS_LE]);;

let HAS_REAL_MEASURE_SUBSET = prove
 (`!s1 s2 m1 m2.
        s1 has_real_measure m1 /\ s2 has_real_measure m2 /\ s1 SUBSET s2
        ==> m1 <= m2`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`IMAGE lift s1`; `IMAGE lift s2`]
    HAS_MEASURE_SUBSET) THEN
  ASM SET_TAC[HAS_MEASURE_SUBSET]);;

let REAL_MEASURE_SUBSET = prove
 (`!s t. real_measurable s /\ real_measurable t /\ s SUBSET t
         ==> real_measure s <= real_measure t`,
  REWRITE_TAC[HAS_REAL_MEASURE_MEASURE] THEN
  MESON_TAC[HAS_REAL_MEASURE_SUBSET]);;

let HAS_REAL_MEASURE_0 = prove
 (`!s. s has_real_measure &0 <=> real_negligible s`,
  REWRITE_TAC[real_negligible; HAS_REAL_MEASURE_HAS_MEASURE] THEN
  REWRITE_TAC[HAS_MEASURE_0]);;

let REAL_MEASURE_EQ_0 = prove
 (`!s. real_negligible s ==> real_measure s = &0`,
  MESON_TAC[REAL_MEASURE_UNIQUE; HAS_REAL_MEASURE_0]);;

let HAS_REAL_MEASURE_EMPTY = prove
 (`{} has_real_measure &0`,
  REWRITE_TAC[HAS_REAL_MEASURE_0; REAL_NEGLIGIBLE_EMPTY]);;

let REAL_MEASURE_EMPTY = prove
 (`real_measure {} = &0`,
  SIMP_TAC[REAL_MEASURE_EQ_0; REAL_NEGLIGIBLE_EMPTY]);;

let REAL_MEASURABLE_EMPTY = prove
 (`real_measurable {}`,
  REWRITE_TAC[real_measurable] THEN MESON_TAC[HAS_REAL_MEASURE_EMPTY]);;

let REAL_MEASURABLE_REAL_MEASURE_EQ_0 = prove
 (`!s. real_measurable s ==> (real_measure s = &0 <=> real_negligible s)`,
  REWRITE_TAC[HAS_REAL_MEASURE_MEASURE; GSYM HAS_REAL_MEASURE_0] THEN
  MESON_TAC[REAL_MEASURE_UNIQUE]);;

let REAL_MEASURABLE_REAL_MEASURE_POS_LT = prove
 (`!s. real_measurable s ==> (&0 < real_measure s <=> ~real_negligible s)`,
  SIMP_TAC[REAL_LT_LE; REAL_MEASURE_POS_LE;
           GSYM REAL_MEASURABLE_REAL_MEASURE_EQ_0] THEN
  REWRITE_TAC[EQ_SYM_EQ]);;

let REAL_NEGLIGIBLE_REAL_INTERVAL = prove
 (`(!a b. real_negligible(real_interval[a,b]) <=> real_interval(a,b) = {}) /\
   (!a b. real_negligible(real_interval(a,b)) <=> real_interval(a,b) = {})`,
  REWRITE_TAC[real_negligible; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[NEGLIGIBLE_INTERVAL] THEN
  REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY; INTERVAL_EQ_EMPTY_1; LIFT_DROP]);;

let REAL_MEASURABLE_UNIONS = prove
 (`!f. FINITE f /\ (!s. s IN f ==> real_measurable s)
       ==> real_measurable (UNIONS f)`,
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE; IMAGE_UNIONS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_UNIONS THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE]);;

let HAS_REAL_MEASURE_DIFF_SUBSET = prove
 (`!s1 s2 m1 m2.
        s1 has_real_measure m1 /\ s2 has_real_measure m2 /\ s2 SUBSET s1
        ==> (s1 DIFF s2) has_real_measure (m1 - m2)`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[IMAGE_DIFF_INJ; LIFT_EQ] THEN
  MATCH_MP_TAC HAS_MEASURE_DIFF_SUBSET THEN
  ASM_SIMP_TAC[IMAGE_SUBSET]);;

let REAL_MEASURABLE_DIFF = prove
 (`!s t. real_measurable s /\ real_measurable t
         ==> real_measurable (s DIFF t)`,
  SIMP_TAC[REAL_MEASURABLE_MEASURABLE; IMAGE_DIFF_INJ; LIFT_EQ] THEN
  REWRITE_TAC[MEASURABLE_DIFF]);;

let REAL_MEASURE_DIFF_SUBSET = prove
 (`!s t. real_measurable s /\ real_measurable t /\ t SUBSET s
         ==> real_measure(s DIFF t) = real_measure s - real_measure t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_DIFF_SUBSET; GSYM HAS_REAL_MEASURE_MEASURE]);;

let HAS_REAL_MEASURE_UNION_REAL_NEGLIGIBLE = prove
 (`!s t m.
        s has_real_measure m /\ real_negligible t
        ==> (s UNION t) has_real_measure m`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; real_negligible; IMAGE_UNION] THEN
  REWRITE_TAC[HAS_MEASURE_UNION_NEGLIGIBLE]);;

let HAS_REAL_MEASURE_DIFF_REAL_NEGLIGIBLE = prove
 (`!s t m.
        s has_real_measure m /\ real_negligible t
        ==> (s DIFF t) has_real_measure m`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; real_negligible] THEN
  SIMP_TAC[IMAGE_DIFF_INJ; LIFT_EQ] THEN
  REWRITE_TAC[HAS_MEASURE_DIFF_NEGLIGIBLE]);;

let HAS_REAL_MEASURE_UNION_REAL_NEGLIGIBLE_EQ = prove
 (`!s t m.
     real_negligible t
     ==> ((s UNION t) has_real_measure m <=> s has_real_measure m)`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; real_negligible; IMAGE_UNION] THEN
  REWRITE_TAC[HAS_MEASURE_UNION_NEGLIGIBLE_EQ]);;

let HAS_REAL_MEASURE_DIFF_REAL_NEGLIGIBLE_EQ = prove
 (`!s t m.
     real_negligible t
     ==> ((s DIFF t) has_real_measure m <=> s has_real_measure m)`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; real_negligible] THEN
  SIMP_TAC[IMAGE_DIFF_INJ; LIFT_EQ] THEN
  REWRITE_TAC[HAS_MEASURE_DIFF_NEGLIGIBLE_EQ]);;

let HAS_REAL_MEASURE_ALMOST = prove
 (`!s s' t m. s has_real_measure m /\ real_negligible t /\
              s UNION t = s' UNION t
              ==> s' has_real_measure m`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; real_negligible; IMAGE_UNION] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_ALMOST THEN
  MAP_EVERY EXISTS_TAC [`IMAGE lift s`; `IMAGE lift t`] THEN ASM SET_TAC[]);;

let HAS_REAL_MEASURE_ALMOST_EQ = prove
 (`!s s' t. real_negligible t /\ s UNION t = s' UNION t
            ==> (s has_real_measure m <=> s' has_real_measure m)`,
  MESON_TAC[HAS_REAL_MEASURE_ALMOST]);;

let REAL_MEASURABLE_ALMOST = prove
 (`!s s' t. real_measurable s /\ real_negligible t /\ s UNION t = s' UNION t
            ==> real_measurable s'`,
  REWRITE_TAC[real_measurable] THEN MESON_TAC[HAS_REAL_MEASURE_ALMOST]);;

let HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNION = prove
 (`!s1 s2 m1 m2.
        s1 has_real_measure m1 /\ s2 has_real_measure m2 /\
        real_negligible(s1 INTER s2)
        ==> (s1 UNION s2) has_real_measure (m1 + m2)`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; real_negligible; IMAGE_UNION] THEN
  SIMP_TAC[IMAGE_INTER_INJ; LIFT_EQ] THEN
  REWRITE_TAC[HAS_MEASURE_NEGLIGIBLE_UNION]);;

let REAL_MEASURE_REAL_NEGLIGIBLE_UNION = prove
 (`!s t. real_measurable s /\ real_measurable t /\ real_negligible(s INTER t)
         ==> real_measure(s UNION t) = real_measure s + real_measure t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNION;
               GSYM HAS_REAL_MEASURE_MEASURE]);;

let HAS_REAL_MEASURE_REAL_NEGLIGIBLE_SYMDIFF = prove
 (`!s t m.
        s has_real_measure m /\
        real_negligible((s DIFF t) UNION (t DIFF s))
        ==> t has_real_measure m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_MEASURE_ALMOST THEN
  MAP_EVERY EXISTS_TAC
    [`s:real->bool`; `(s DIFF t) UNION (t DIFF s):real->bool`] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let REAL_MEASURABLE_REAL_NEGLIGIBLE_SYMDIFF = prove
 (`!s t. real_measurable s /\ real_negligible((s DIFF t) UNION (t DIFF s))
         ==> real_measurable t`,
  REWRITE_TAC[real_measurable] THEN
  MESON_TAC[HAS_REAL_MEASURE_REAL_NEGLIGIBLE_SYMDIFF]);;

let REAL_MEASURE_REAL_NEGLIGIBLE_SYMDIFF = prove
 (`!s t. (real_measurable s \/ real_measurable t) /\
         real_negligible((s DIFF t) UNION (t DIFF s))
         ==> real_measure s = real_measure t`,
  MESON_TAC[HAS_REAL_MEASURE_REAL_NEGLIGIBLE_SYMDIFF; REAL_MEASURE_UNIQUE;
            UNION_COMM; HAS_REAL_MEASURE_MEASURE]);;

let HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS = prove
 (`!m f. FINITE f /\
         (!s. s IN f ==> s has_real_measure (m s)) /\
         (!s t. s IN f /\ t IN f /\ ~(s = t) ==> real_negligible(s INTER t))
         ==> (UNIONS f) has_real_measure (sum f m)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; UNIONS_0; UNIONS_INSERT; HAS_REAL_MEASURE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`s:real->bool`; `f:(real->bool)->bool`] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNION THEN
  REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[INTER_UNIONS] THEN MATCH_MP_TAC REAL_NEGLIGIBLE_UNIONS THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS = prove
 (`!m f. FINITE f /\
         (!s. s IN f ==> s has_real_measure (m s)) /\
         (!s t. s IN f /\ t IN f /\ ~(s = t) ==> real_negligible(s INTER t))
         ==> real_measure(UNIONS f) = sum f m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS]);;

let HAS_REAL_MEASURE_DISJOINT_UNIONS = prove
 (`!m f. FINITE f /\
         (!s. s IN f ==> s has_real_measure (m s)) /\
         (!s t. s IN f /\ t IN f /\ ~(s = t) ==> DISJOINT s t)
         ==> (UNIONS f) has_real_measure (sum f m)`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS THEN
  ASM_SIMP_TAC[REAL_NEGLIGIBLE_EMPTY]);;

let REAL_MEASURE_DISJOINT_UNIONS = prove
 (`!m f:(real->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_real_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> DISJOINT s t)
        ==> real_measure(UNIONS f) = sum f m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_DISJOINT_UNIONS]);;

let HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE = prove
 (`!f:A->(real->bool) s.
        FINITE s /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y)
               ==> real_negligible((f x) INTER (f y)))
        ==> (UNIONS (IMAGE f s)) has_real_measure
            (sum s (\x. real_measure(f x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum s (\x. real_measure(f x)) =
    sum (IMAGE (f:A->real->bool) s) real_measure`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC SUM_IMAGE_NONZERO THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
    ASM_SIMP_TAC[INTER_ACI; REAL_MEASURABLE_REAL_MEASURE_EQ_0];
    MATCH_MP_TAC HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS THEN
    ASM_SIMP_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[FINITE_IMAGE; HAS_REAL_MEASURE_MEASURE]]);;

let REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE = prove
 (`!f:A->real->bool s.
        FINITE s /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y)
               ==> real_negligible((f x) INTER (f y)))
        ==> real_measure(UNIONS (IMAGE f s)) = sum s (\x. real_measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE]);;

let HAS_REAL_MEASURE_DISJOINT_UNIONS_IMAGE = prove
 (`!f:A->real->bool s.
        FINITE s /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> (UNIONS (IMAGE f s)) has_real_measure
            (sum s (\x. real_measure(f x)))`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE THEN
  ASM_SIMP_TAC[REAL_NEGLIGIBLE_EMPTY]);;

let REAL_MEASURE_DISJOINT_UNIONS_IMAGE = prove
 (`!f:A->real->bool s.
        FINITE s /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> real_measure(UNIONS (IMAGE f s)) = sum s (\x. real_measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_DISJOINT_UNIONS_IMAGE]);;

let HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y)
               ==> real_negligible((f x) INTER (f y)))
        ==> (UNIONS (IMAGE f s)) has_real_measure
            (sum s (\x. real_measure(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real->bool`;
                 `{x | x IN s /\ ~((f:A->real->bool) x = {})}`]
        HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; FINITE_RESTRICT] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[NOT_IN_EMPTY];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; TAUT `a /\ ~(a /\ b) <=> a /\ ~b`] THEN
    REWRITE_TAC[REAL_MEASURE_EMPTY]]);;

let REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y)
               ==> real_negligible((f x) INTER (f y)))
        ==> real_measure(UNIONS (IMAGE f s)) = sum s (\x. real_measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE_STRONG]);;

let HAS_REAL_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> (UNIONS (IMAGE f s)) has_real_measure
            (sum s (\x. real_measure(f x)))`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE_STRONG THEN
  ASM_SIMP_TAC[REAL_NEGLIGIBLE_EMPTY]);;

let REAL_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> real_measure(UNIONS (IMAGE f s)) = sum s (\x. real_measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG]);;

let REAL_MEASURE_UNION = prove
 (`!s t. real_measurable s /\ real_measurable t
         ==> real_measure(s UNION t) =
             real_measure(s) + real_measure(t) - real_measure(s INTER t)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
   `s UNION t = (s INTER t) UNION (s DIFF t) UNION (t DIFF s)`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b - c:real = c + (a - c) + (b - c)`] THEN
  MP_TAC(ISPECL [`s DIFF t:real->bool`; `t DIFF s:real->bool`]
        REAL_MEASURE_DISJOINT_UNION) THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_DIFF] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s INTER t:real->bool`;
                 `(s DIFF t) UNION (t DIFF s):real->bool`]
                REAL_MEASURE_DISJOINT_UNION) THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_DIFF;
               REAL_MEASURABLE_UNION; REAL_MEASURABLE_INTER] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN AP_TERM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[REAL_EQ_SUB_LADD] THEN MATCH_MP_TAC EQ_TRANS THENL
   [EXISTS_TAC `real_measure((s DIFF t) UNION (s INTER t):real->bool)`;
    EXISTS_TAC `real_measure((t DIFF s) UNION (s INTER t):real->bool)`] THEN
  (CONJ_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MEASURE_DISJOINT_UNION THEN
     ASM_SIMP_TAC[REAL_MEASURABLE_DIFF; REAL_MEASURABLE_INTER];
     AP_TERM_TAC] THEN
   SET_TAC[]));;

let REAL_MEASURE_UNION_LE = prove
 (`!s t. real_measurable s /\ real_measurable t
         ==> real_measure(s UNION t) <= real_measure s + real_measure t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_MEASURE_UNION] THEN
  REWRITE_TAC[REAL_ARITH `a + b - c <= a + b <=> &0 <= c`] THEN
  MATCH_MP_TAC REAL_MEASURE_POS_LE THEN ASM_SIMP_TAC[REAL_MEASURABLE_INTER]);;

let REAL_MEASURE_UNIONS_LE = prove
 (`!f. FINITE f /\ (!s. s IN f ==> real_measurable s)
       ==> real_measure(UNIONS f) <= sum f (\s. real_measure s)`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[UNIONS_0; UNIONS_INSERT; SUM_CLAUSES] THEN
  REWRITE_TAC[REAL_MEASURE_EMPTY; REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`s:real->bool`; `f:(real->bool)->bool`] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_measure(s) + real_measure(UNIONS f)` THEN
  ASM_SIMP_TAC[REAL_MEASURE_UNION_LE; REAL_MEASURABLE_UNIONS] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[]);;

let REAL_MEASURE_UNIONS_LE_IMAGE = prove
 (`!f:A->bool s:A->(real->bool).
        FINITE f /\ (!a. a IN f ==> real_measurable(s a))
        ==> real_measure(UNIONS (IMAGE s f)) <= sum f (\a. real_measure(s a))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE s (f:A->bool)) (\k:real->bool. real_measure k)` THEN
  ASM_SIMP_TAC[REAL_MEASURE_UNIONS_LE; FORALL_IN_IMAGE; FINITE_IMAGE] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SUM_IMAGE_LE THEN
  ASM_SIMP_TAC[REAL_MEASURE_POS_LE]);;

let REAL_NEGLIGIBLE_OUTER = prove
 (`!s. real_negligible s <=>
       !e. &0 < e
           ==> ?t. s SUBSET t /\ real_measurable t /\ real_measure t < e`,
  REWRITE_TAC[real_negligible; REAL_MEASURABLE_MEASURABLE;
              REAL_MEASURE_MEASURE; SUBSET_LIFT_IMAGE;
              NEGLIGIBLE_OUTER; EXISTS_LIFT_IMAGE]);;

let REAL_NEGLIGIBLE_OUTER_LE = prove
 (`!s. real_negligible s <=>
       !e. &0 < e
           ==> ?t. s SUBSET t /\ real_measurable t /\ real_measure t <= e`,
  REWRITE_TAC[real_negligible; REAL_MEASURABLE_MEASURABLE;
              REAL_MEASURE_MEASURE; SUBSET_LIFT_IMAGE;
              NEGLIGIBLE_OUTER_LE; EXISTS_LIFT_IMAGE]);;

let REAL_MEASURABLE_INNER_OUTER = prove
 (`!s. real_measurable s <=>
                !e. &0 < e
                    ==> ?t u. t SUBSET s /\ s SUBSET u /\
                              real_measurable t /\ real_measurable u /\
                              abs(real_measure t - real_measure u) < e`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REPEAT(EXISTS_TAC `s:real->bool`) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; REAL_SUB_REFL; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MEASURABLE_REAL_INTEGRABLE] THEN
  MATCH_MP_TAC REAL_INTEGRABLE_STRADDLE THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real->bool`; `u:real->bool`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(\x. if x IN t then &1 else &0):real->real`;
    `(\x. if x IN u then &1 else &0):real->real`;
    `real_measure(t:real->bool)`;
    `real_measure(u:real->bool)`] THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_MEASURE; GSYM HAS_REAL_MEASURE_MEASURE] THEN
  ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[DROP_VEC; REAL_POS; REAL_LE_REFL]) THEN
  ASM SET_TAC[]);;

let HAS_REAL_MEASURE_INNER_OUTER = prove
 (`!s m. s has_real_measure m <=>
                (!e. &0 < e ==> ?t. t SUBSET s /\ real_measurable t /\
                                    m - e < real_measure t) /\
                (!e. &0 < e ==> ?u. s SUBSET u /\ real_measurable u /\
                                    real_measure u < m + e)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
      [HAS_REAL_MEASURE_REAL_MEASURABLE_REAL_MEASURE] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `s:real->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "t") (LABEL_TAC "u")) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [REAL_MEASURABLE_INNER_OUTER] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "u" (MP_TAC o SPEC `e / &2`) THEN
    REMOVE_THEN "t" (MP_TAC o SPEC `e / &2`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[IMP_IMP; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ t <= u /\ m - e / &2 < t /\ u < m + e / &2
                          ==> abs(t - u) < e`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_MEASURE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `~(&0 < x - y) /\ ~(&0 < y - x) ==> x = y`) THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [REMOVE_THEN "u" (MP_TAC o SPEC `real_measure(s:real->bool) - m`) THEN
      ASM_REWRITE_TAC[REAL_SUB_ADD2; GSYM REAL_NOT_LE];
      REMOVE_THEN "t" (MP_TAC o SPEC `m - real_measure(s:real->bool)`) THEN
      ASM_REWRITE_TAC[REAL_SUB_SUB2; GSYM REAL_NOT_LE]] THEN
    ASM_MESON_TAC[REAL_MEASURE_SUBSET]]);;

let HAS_REAL_MEASURE_INNER_OUTER_LE = prove
 (`!s:real->bool m.
        s has_real_measure m <=>
                (!e. &0 < e ==> ?t. t SUBSET s /\ real_measurable t /\
                                    m - e <= real_measure t) /\
                (!e. &0 < e ==> ?u. s SUBSET u /\ real_measurable u /\
                                    real_measure u <= m + e)`,
  REWRITE_TAC[HAS_REAL_MEASURE_INNER_OUTER] THEN
  MESON_TAC[REAL_ARITH `&0 < e /\ m - e / &2 <= t ==> m - e < t`;
            REAL_ARITH `&0 < e /\ u <= m + e / &2 ==> u < m + e`;
            REAL_ARITH `&0 < e <=> &0 < e / &2`; REAL_LT_IMP_LE]);;

let HAS_REAL_MEASURE_AFFINITY = prove
 (`!s m c y. s has_real_measure y
             ==> (IMAGE (\x. m * x + c) s) has_real_measure abs(m) * y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:real`; `lift c`] o MATCH_MP
    HAS_MEASURE_AFFINITY) THEN
  REWRITE_TAC[DIMINDEX_1; REAL_POW_1; GSYM IMAGE_o] THEN
  MATCH_MP_TAC EQ_IMP THEN REPEAT(AP_THM_TAC THEN AP_TERM_TAC) THEN
  SIMP_TAC[FUN_EQ_THM; FORALL_DROP; o_THM; LIFT_DROP; LIFT_ADD; LIFT_CMUL]);;

let HAS_REAL_MEASURE_SCALING = prove
 (`!s m y. s has_real_measure y
           ==> (IMAGE (\x. m * x) s) has_real_measure abs(m) * y`,
  ONCE_REWRITE_TAC[REAL_ARITH `m * x = m * x + &0`] THEN
  REWRITE_TAC[REAL_ARITH `abs m * x + &0 = abs m * x`] THEN
  REWRITE_TAC[HAS_REAL_MEASURE_AFFINITY]);;

let HAS_REAL_MEASURE_TRANSLATION = prove
 (`!s m a. s has_real_measure m ==> (IMAGE (\x. a + x) s) has_real_measure m`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + x = &1 * x + a`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_ARITH `m = abs(&1) * m`] THEN
  REWRITE_TAC[HAS_REAL_MEASURE_AFFINITY]);;

let REAL_NEGLIGIBLE_TRANSLATION = prove
 (`!s a. real_negligible s ==> real_negligible (IMAGE (\x. a + x) s)`,
  SIMP_TAC[GSYM HAS_REAL_MEASURE_0; HAS_REAL_MEASURE_TRANSLATION]);;

let HAS_REAL_MEASURE_TRANSLATION_EQ = prove
 (`!s m. (IMAGE (\x. a + x) s) has_real_measure m <=> s has_real_measure m`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  REWRITE_TAC[HAS_REAL_MEASURE_TRANSLATION] THEN
  DISCH_THEN(MP_TAC o SPEC `--a:real` o
    MATCH_MP HAS_REAL_MEASURE_TRANSLATION) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; REAL_ARITH `--a + a + b:real = b`] THEN
  SET_TAC[]);;

let REAL_NEGLIGIBLE_TRANSLATION_REV = prove
 (`!s a. real_negligible (IMAGE (\x. a + x) s) ==> real_negligible s`,
  SIMP_TAC[GSYM HAS_REAL_MEASURE_0; HAS_REAL_MEASURE_TRANSLATION_EQ]);;

let REAL_NEGLIGIBLE_TRANSLATION_EQ = prove
 (`!s a. real_negligible (IMAGE (\x. a + x) s) <=> real_negligible s`,
  SIMP_TAC[GSYM HAS_REAL_MEASURE_0; HAS_REAL_MEASURE_TRANSLATION_EQ]);;

let REAL_MEASURABLE_TRANSLATION = prove
 (`!s. real_measurable (IMAGE (\x. a + x) s) <=> real_measurable s`,
  REWRITE_TAC[real_measurable; HAS_REAL_MEASURE_TRANSLATION_EQ]);;

let REAL_MEASURE_TRANSLATION = prove
 (`!s. real_measurable s
       ==> real_measure(IMAGE (\x. a + x) s) = real_measure s`,
  REWRITE_TAC[HAS_REAL_MEASURE_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_REWRITE_TAC[HAS_REAL_MEASURE_TRANSLATION_EQ]);;

let HAS_REAL_MEASURE_SCALING_EQ = prove
 (`!s m c. ~(c = &0)
           ==> ((IMAGE (\x. c * x) s) has_real_measure (abs(c) * m) <=>
                s has_real_measure m)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[HAS_REAL_MEASURE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(c:real)` o
    MATCH_MP HAS_REAL_MEASURE_SCALING) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; GSYM REAL_ABS_MUL] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_MUL; REAL_MUL_LINV] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_ABS_NUM; REAL_MUL_LID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let REAL_MEASURABLE_SCALING = prove
 (`!s c. real_measurable s ==> real_measurable (IMAGE (\x. c * x) s)`,
  REWRITE_TAC[real_measurable] THEN MESON_TAC[HAS_REAL_MEASURE_SCALING]);;

let REAL_MEASURABLE_SCALING_EQ = prove
 (`!s c. ~(c = &0)
         ==> (real_measurable (IMAGE (\x. c * x) s) <=> real_measurable s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[REAL_MEASURABLE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c:real` o MATCH_MP REAL_MEASURABLE_SCALING) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; GSYM REAL_ABS_MUL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_LID] THEN
  SET_TAC[]);;

let REAL_MEASURE_SCALING = prove
 (`!s. real_measurable s
       ==> real_measure(IMAGE (\x. c * x) s) = abs(c) * real_measure s`,
  REWRITE_TAC[HAS_REAL_MEASURE_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_SCALING]);;

let HAS_REAL_MEASURE_NESTED_UNIONS = prove
 (`!s B. (!n. real_measurable(s n)) /\
         (!n. real_measure(s n) <= B) /\
         (!n. s(n) SUBSET s(SUC n))
         ==> real_measurable(UNIONS { s(n) | n IN (:num) }) /\
             ((\n. real_measure(s n))
                   ---> real_measure(UNIONS { s(n) | n IN (:num) }))
             sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[REAL_MEASURE_MEASURE] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`IMAGE lift o (s:num->real->bool)`; `B:real`]
        HAS_MEASURE_NESTED_UNIONS) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_SUBSET] THEN
  REWRITE_TAC[SET_RULE `{IMAGE f (s n) | P n} = IMAGE (IMAGE f) {s n | P n}`;
              GSYM IMAGE_UNIONS] THEN
  SIMP_TAC[REAL_MEASURE_MEASURE; REAL_MEASURABLE_MEASURABLE]);;

let REAL_MEASURABLE_NESTED_UNIONS = prove
 (`!s B. (!n. real_measurable(s n)) /\
         (!n. real_measure(s n) <= B) /\
         (!n. s(n) SUBSET s(SUC n))
         ==> real_measurable(UNIONS { s(n) | n IN (:num) })`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_MEASURE_NESTED_UNIONS) THEN
  SIMP_TAC[]);;

let HAS_REAL_MEASURE_COUNTABLE_REAL_NEGLIGIBLE_UNIONS = prove
 (`!s:num->real->bool B.
        (!n. real_measurable(s n)) /\
        (!m n. ~(m = n) ==> real_negligible(s m INTER s n)) /\
        (!n. sum (0..n) (\k. real_measure(s k)) <= B)
        ==> real_measurable(UNIONS { s(n) | n IN (:num) }) /\
            ((\n. real_measure(s n)) real_sums
             real_measure(UNIONS { s(n) | n IN (:num) })) (from 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. UNIONS (IMAGE s (0..n)):real->bool`; `B:real`]
               HAS_REAL_MEASURE_NESTED_UNIONS) THEN
  REWRITE_TAC[real_sums; FROM_0; INTER_UNIV] THEN
  SUBGOAL_THEN
   `!n. (UNIONS (IMAGE s (0..n)):real->bool) has_real_measure
        (sum(0..n) (\k. real_measure(s k)))`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    ASSUME_TAC(GEN `n:num` (MATCH_MP REAL_MEASURE_UNIQUE
     (SPEC `n:num` th)))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[real_measurable]; ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[LIFT_SUM; FINITE_NUMSEG; o_DEF] THEN
  SUBGOAL_THEN
   `UNIONS {UNIONS (IMAGE s (0..n)) | n IN (:num)}:real->bool =
    UNIONS (IMAGE s (:num))`
   (fun th -> REWRITE_TAC[th] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
              REWRITE_TAC[]) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real` THEN
  REWRITE_TAC[IN_UNIONS] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; EXISTS_IN_UNIONS; IN_UNIV] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
  REWRITE_TAC[IN_NUMSEG; LE_0] THEN MESON_TAC[LE_REFL]);;

let REAL_NEGLIGIBLE_COUNTABLE_UNIONS = prove
 (`!s:num->real->bool.
        (!n. real_negligible(s n))
        ==> real_negligible(UNIONS {s(n) | n IN (:num)})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:num->real->bool`; `&0`]
    HAS_REAL_MEASURE_COUNTABLE_REAL_NEGLIGIBLE_UNIONS) THEN
  ASM_SIMP_TAC[REAL_MEASURE_EQ_0; SUM_0; REAL_LE_REFL; LIFT_NUM] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[HAS_REAL_MEASURE_0; real_measurable; INTER_SUBSET;
                  REAL_NEGLIGIBLE_SUBSET];
    ALL_TAC] THEN
  SIMP_TAC[GSYM REAL_MEASURABLE_REAL_MEASURE_EQ_0] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN REWRITE_TAC[LIFT_NUM] THEN
  MAP_EVERY EXISTS_TAC [`(\k. &0):num->real`; `from 0`] THEN
  ASM_REWRITE_TAC[REAL_SERIES_0]);;

let REAL_MEASURABLE_COUNTABLE_UNIONS_STRONG = prove
 (`!s:num->real->bool B.
        (!n. real_measurable(s n)) /\
        (!n. real_measure(UNIONS {s k | k <= n}) <= B)
        ==> real_measurable(UNIONS { s(n) | n IN (:num) })`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. UNIONS (IMAGE s (0..n)):real->bool`; `B:real`]
               REAL_MEASURABLE_NESTED_UNIONS) THEN
  SUBGOAL_THEN
   `UNIONS {UNIONS (IMAGE s (0..n)) | n IN (:num)}:real->bool =
    UNIONS (IMAGE s (:num))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real` THEN
    REWRITE_TAC[IN_UNIONS] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE; EXISTS_IN_UNIONS; IN_UNIV] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[IN_NUMSEG; LE_0] THEN MESON_TAC[LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_MEASURABLE_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; FINITE_NUMSEG];
    ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_0];
    GEN_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG; LE_0] THEN ARITH_TAC]);;

let HAS_REAL_MEASURE_COUNTABLE_REAL_NEGLIGIBLE_UNIONS_BOUNDED = prove
 (`!s. (!n. real_measurable(s n)) /\
       (!m n. ~(m = n) ==> real_negligible(s m INTER s n)) /\
       real_bounded(UNIONS { s(n) | n IN (:num) })
       ==> real_measurable(UNIONS { s(n) | n IN (:num) }) /\
           ((\n. real_measure(s n)) real_sums
            real_measure(UNIONS { s(n) | n IN (:num) })) (from 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN
  REWRITE_TAC[REAL_BOUNDED] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[REAL_MEASURE_MEASURE] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE; real_negligible] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(ISPEC `IMAGE lift o (s:num->real->bool)`
        HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_SUBSET] THEN
  REWRITE_TAC[SET_RULE `{IMAGE f (s n) | P n} = IMAGE (IMAGE f) {s n | P n}`;
              GSYM IMAGE_UNIONS] THEN
  ASM_SIMP_TAC[GSYM IMAGE_INTER_INJ; LIFT_EQ] THEN
  SIMP_TAC[REAL_SUMS; o_DEF; REAL_MEASURE_MEASURE;
           REAL_MEASURABLE_MEASURABLE]);;

let REAL_MEASURABLE_COUNTABLE_UNIONS = prove
 (`!s B. (!n. real_measurable(s n)) /\
         (!n. sum (0..n) (\k. real_measure(s k)) <= B)
         ==> real_measurable(UNIONS { s(n) | n IN (:num) })`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_COUNTABLE_UNIONS_STRONG THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..n) (\k. real_measure(s k:real->bool))` THEN
  ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_MEASURE_UNIONS_LE_IMAGE o
       rand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
  REWRITE_TAC[IN_NUMSEG; LE_0]);;

let REAL_MEASURABLE_COUNTABLE_UNIONS_BOUNDED = prove
 (`!s. (!n. real_measurable(s n)) /\
       real_bounded(UNIONS { s(n) | n IN (:num) })
       ==> real_measurable(UNIONS { s(n) | n IN (:num) })`,
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE; REAL_BOUNDED] THEN
  SIMP_TAC[IMAGE_INTER_INJ; LIFT_EQ; IMAGE_UNIONS] THEN
  REWRITE_TAC[SET_RULE `IMAGE f {g x | x IN s} = {f(g x) | x IN s}`] THEN
  REWRITE_TAC[MEASURABLE_COUNTABLE_UNIONS_BOUNDED]);;

let REAL_MEASURABLE_COUNTABLE_INTERS = prove
 (`!s. (!n. real_measurable(s n))
       ==> real_measurable(INTERS { s(n) | n IN (:num) })`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `INTERS { s(n):real->bool | n IN (:num) } =
                s 0 DIFF (UNIONS {s 0 DIFF s n | n IN (:num)})`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTERS; IN_DIFF; IN_UNIONS] THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_MEASURABLE_COUNTABLE_UNIONS_STRONG THEN
  EXISTS_TAC `real_measure(s 0:real->bool)` THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_DIFF; LE_0] THEN
  GEN_TAC THEN MATCH_MP_TAC REAL_MEASURE_SUBSET THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[IN_DIFF]] THEN
  ONCE_REWRITE_TAC[GSYM IN_NUMSEG_0] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               REAL_MEASURABLE_DIFF; REAL_MEASURABLE_UNIONS]);;

let REAL_NEGLIGIBLE_COUNTABLE = prove
 (`!s. COUNTABLE s ==> real_negligible s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_negligible] THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE THEN ASM_SIMP_TAC[COUNTABLE_IMAGE]);;

let REAL_MEASURABLE_COMPACT = prove
 (`!s. real_compact s ==> real_measurable s`,
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE; real_compact; MEASURABLE_COMPACT]);;

let REAL_MEASURABLE_OPEN = prove
 (`!s. real_bounded s /\ real_open s ==> real_measurable s`,
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE; REAL_OPEN; REAL_BOUNDED;
              MEASURABLE_OPEN]);;

let HAS_REAL_INTEGRAL_NEGLIGIBLE_EQ = prove
 (`!f s. (!x. x IN s ==> &0 <= f(x))
         ==> ((f has_real_integral &0) s <=>
              real_negligible {x | x IN s /\ ~(f x = &0)})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HAS_REAL_INTEGRAL_NEGLIGIBLE THEN
    EXISTS_TAC `{x | x IN s /\ ~((f:real->real) x = &0)}` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]] THEN
  MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN EXISTS_TAC
   `UNIONS {{x:real | x IN s /\ abs(f x) >= &1 / (&n + &1)} |
            n IN (:num)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE_UNIONS THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GSYM HAS_REAL_MEASURE_0] THEN
    REWRITE_TAC[HAS_REAL_MEASURE] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_STRADDLE_NULL THEN
    EXISTS_TAC `\x:real. if x IN s then (&n + &1) * f(x) else &0` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIV; IN_ELIM_THM; real_ge] THEN
      X_GEN_TAC `x:real` THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_POS] THENL
       [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ a <= abs x ==> a <= x`) THEN
        ASM_SIMP_TAC[];
        COND_CASES_TAC THEN REWRITE_TAC[REAL_POS] THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL; REAL_LE_ADD]];
      REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
      SUBST1_TAC(REAL_ARITH `&0 = (&n + &1) * &0`) THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real` THEN
    REWRITE_TAC[REAL_ABS_NZ] THEN ONCE_REWRITE_TAC[REAL_ARCH_INV] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num`
      STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
    EXISTS_TAC `n - 1` THEN ASM_SIMP_TAC[IN_UNIV; IN_ELIM_THM; real_ge] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_ADD; SUB_ADD; LE_1] THEN
    ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_LT_IMP_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Integration by parts.                                                     *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGRATION_BY_PARTS = prove
 (`!f g f' g' a b c.
        a <= b /\ COUNTABLE c /\
        (\x. f x * g x) real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b) DIFF c
             ==> (f has_real_derivative f'(x)) (atreal x) /\
                 (g has_real_derivative g'(x)) (atreal x)) /\
        ((\x. f(x) * g'(x)) has_real_integral ((f b * g b - f a * g a) - y))
            (real_interval[a,b])
        ==> ((\x. f'(x) * g(x)) has_real_integral y) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (f:real->real)(x) * g(x)`;
                 `\x. (f:real->real)(x) * g'(x) + f'(x) * g(x)`;
                 `c:real->bool`; `a:real`; `b:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_MUL_ATREAL] THEN
  FIRST_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
        DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_SUB)) THEN
  REWRITE_TAC[REAL_ARITH `b - a - (b - a - y):real = y`; REAL_ADD_SUB]);;

let REAL_INTEGRATION_BY_PARTS_SIMPLE = prove
 (`!f g f' g' a b.
        a <= b /\
        (!x. x IN real_interval[a,b]
             ==> (f has_real_derivative f'(x))
                    (atreal x within real_interval[a,b]) /\
                 (g has_real_derivative g'(x))
                    (atreal x within real_interval[a,b])) /\
        ((\x. f(x) * g'(x)) has_real_integral ((f b * g b - f a * g a) - y))
            (real_interval[a,b])
        ==> ((\x. f'(x) * g(x)) has_real_integral y) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (f:real->real)(x) * g(x)`;
                 `\x. (f:real->real)(x) * g'(x) + f'(x) * g(x)`;
                 `a:real`; `b:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_MUL_WITHIN] THEN
  FIRST_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
        DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_SUB)) THEN
  REWRITE_TAC[REAL_ARITH `b - a - (b - a - y):real = y`; REAL_ADD_SUB]);;

let REAL_INTEGRABLE_BY_PARTS = prove
 (`!f g f' g' a b c.
        COUNTABLE c /\
        (\x. f x * g x) real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b) DIFF c
             ==> (f has_real_derivative f'(x)) (atreal x) /\
                 (g has_real_derivative g'(x)) (atreal x)) /\
        (\x. f(x) * g'(x)) real_integrable_on real_interval[a,b]
        ==> (\x. f'(x) * g(x)) real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(REAL_ARITH `b <= a \/ a <= b`) THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[real_integrable_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `((f:real->real) b * g b - f a * g a) - y` THEN
  MATCH_MP_TAC REAL_INTEGRATION_BY_PARTS THEN MAP_EVERY EXISTS_TAC
   [`f:real->real`; `g':real->real`; `c:real->bool`] THEN
  ASM_REWRITE_TAC[REAL_ARITH `b - a - ((b - a) - y):real = y`]);;

let REAL_INTEGRABLE_BY_PARTS_EQ = prove
 (`!f g f' g' a b c.
        COUNTABLE c /\
        (\x. f x * g x) real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b) DIFF c
             ==> (f has_real_derivative f'(x)) (atreal x) /\
                 (g has_real_derivative g'(x)) (atreal x))
        ==> ((\x. f(x) * g'(x)) real_integrable_on real_interval[a,b] <=>
             (\x. f'(x) * g(x)) real_integrable_on real_interval[a,b])`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[REAL_INTEGRABLE_BY_PARTS]; DISCH_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_INTEGRABLE_BY_PARTS THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Change of variable in real integral (one that we know exists).            *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_INTEGRAL_SUBSTITUTION_STRONG = prove
 (`!f g g' a b c d k.
        COUNTABLE k /\
        f real_integrable_on real_interval[c,d] /\
        g real_continuous_on real_interval[a,b] /\
        IMAGE g (real_interval[a,b]) SUBSET real_interval[c,d] /\
        (!x. x IN real_interval[a,b] DIFF k
                  ==> (g has_real_derivative g'(x))
                       (atreal x within real_interval[a,b]) /\
                      f real_continuous
                        (atreal(g x)) within real_interval[c,d]) /\
        a <= b /\ c <= d /\ g a <= g b
        ==> ((\x. f(g x) * g'(x)) has_real_integral
             real_integral (real_interval[g a,g b]) f) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ff = \x. real_integral (real_interval[c,x]) f` THEN
  MP_TAC(ISPECL
   [`(ff:real->real) o (g:real->real)`;
    `\x:real. (f:real->real)(g x) * g'(x)`; `k:real->bool`; `a:real`; `b:real`]
   REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval [c,d]` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "ff" THEN
      MATCH_MP_TAC REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
        REAL_INTERVAL_OPEN_SUBSET_CLOSED)) THEN
      SUBGOAL_THEN `(ff o g has_real_derivative f (g x:real) * g' x)
                    (atreal x within real_interval[a,b])`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN
        ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN; IN_DIFF] THEN
        MP_TAC(ISPECL [`f:real->real`; `c:real`; `d:real`; `(g:real->real) x`]
          REAL_INTEGRAL_HAS_REAL_DERIVATIVE_POINTWISE) THEN
        ASM_SIMP_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL; IN_DIFF] THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[HAS_REAL_DERIVATIVE_WITHIN_SUBSET];
        DISCH_THEN(MP_TAC o SPEC `real_interval(a,b)` o MATCH_MP
         (REWRITE_RULE[IMP_CONJ] HAS_REAL_DERIVATIVE_WITHIN_SUBSET)) THEN
        REWRITE_TAC[REAL_INTERVAL_OPEN_SUBSET_CLOSED] THEN
        REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL] THEN
        ASM_SIMP_TAC[REALLIM_WITHIN_REAL_OPEN; REAL_OPEN_REAL_INTERVAL] THEN
        REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL]]];
    EXPAND_TAC "ff" THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC(REAL_ARITH
     `z + w:real = y ==> y - z = w`) THEN
    MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        REAL_INTEGRABLE_SUBINTERVAL))] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_REAL_INTERVAL; SUBSET] THEN
    ASM_MESON_TAC[REAL_LE_REFL; REAL_LE_TRANS]]);;

let HAS_REAL_INTEGRAL_SUBSTITUTION = prove
 (`!f g g' a b c d k.
        COUNTABLE k /\
        f real_continuous_on real_interval[c,d] /\
        g real_continuous_on real_interval[a,b] /\
        IMAGE g (real_interval[a,b]) SUBSET real_interval[c,d] /\
        (!x. x IN real_interval[a,b] DIFF k
                  ==> (g has_real_derivative g'(x)) (atreal x)) /\
        a <= b /\ c <= d /\ g a <= g b
        ==> ((\x. f(g x) * g'(x)) has_real_integral
             real_integral (real_interval[g a,g b]) f) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `c:real`; `d:real`]
        REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `h = \u. real_integral (real_interval[c,u]) f` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`(h:real->real) o (g:real->real)`;
    `\x:real. (f:real->real)(g x) * g' x`;
    `k:real->bool`; `a:real`; `b:real`]
        REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG) THEN
  MP_TAC(ISPECL
   [`h:real->real`; `f:real->real`;
    `(g:real->real) a`; `(g:real->real) b`]
        REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `x IN s ==> s SUBSET t ==> x IN t`));
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
       HAS_REAL_DERIVATIVE_WITHIN_SUBSET)] THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `(c <= ga /\ ga <= d) /\ (c <= gb /\ gb <= d) /\ ga <= gb
      ==> c <= ga /\ ga <= gb /\ gb <= d`) THEN
    ASM_REWRITE_TAC[GSYM IN_REAL_INTERVAL] THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL];
    DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "h" THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_CONTINUOUS_ON_SUBSET)) THEN
      MATCH_MP_TAC REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS];
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
        REAL_INTERVAL_OPEN_SUBSET_CLOSED)) THEN
      SUBGOAL_THEN
       `(h o (g:real->real) has_real_derivative f(g x) * g' x)
        (atreal x within real_interval[a,b])`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN
        ASM_SIMP_TAC[IN_DIFF; HAS_REAL_DERIVATIVE_ATREAL_WITHIN] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `(g:real->real) x`) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
          HAS_REAL_DERIVATIVE_WITHIN_SUBSET) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL; HAS_REAL_DERIVATIVE_ATREAL;
                    REALLIM_WITHINREAL_WITHIN; REALLIM_ATREAL_AT] THEN
        REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; TENDSTO_REAL] THEN
        MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC LIM_WITHIN_INTERIOR THEN
        REWRITE_TAC[INTERIOR_INTERVAL; GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
        ASM_SIMP_TAC[FUN_IN_IMAGE]]]]);;

let REAL_INTEGRAL_SUBSTITUTION = prove
 (`!f g g' a b c d k.
        COUNTABLE k /\
        f real_continuous_on real_interval[c,d] /\
        g real_continuous_on real_interval[a,b] /\
        IMAGE g (real_interval[a,b]) SUBSET real_interval[c,d] /\
        (!x. x IN real_interval[a,b] DIFF k
                  ==> (g has_real_derivative g'(x)) (atreal x)) /\
        a <= b /\ c <= d /\ g a <= g b
        ==> real_integral (real_interval[a,b]) (\x. f(g x) * g'(x)) =
            real_integral (real_interval[g a,g b]) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_MESON_TAC[HAS_REAL_INTEGRAL_SUBSTITUTION]);;

let HAS_REAL_INTEGRAL_SUBSTITUTION_SIMPLE = prove
 (`!f g g' a b c d.
        f real_continuous_on real_interval[c,d] /\
        (!x. x IN real_interval[a,b]
                  ==> (g has_real_derivative g'(x))
                      (atreal x within real_interval[a,b])) /\
        IMAGE g (real_interval[a,b]) SUBSET real_interval[c,d] /\
        a <= b /\ c <= d /\ g a <= g b
        ==> ((\x. f(g x) * g'(x)) has_real_integral
             real_integral (real_interval[g a,g b]) f) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  ABBREV_TAC `h = \u. real_integral (real_interval[c,u]) f` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`(h:real->real) o (g:real->real)`;
    `\x:real. (f:real->real)(g x) * g' x`;
    `a:real`; `b:real`]
        REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  MP_TAC(ISPECL
   [`h:real->real`; `f:real->real`; `(g:real->real) a`; `(g:real->real) b`]
        REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `x IN s ==> s SUBSET t ==> x IN t`));
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
       HAS_REAL_DERIVATIVE_WITHIN_SUBSET)] THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `(c <= ga /\ ga <= d) /\ (c <= gb /\ gb <= d) /\ ga <= gb
      ==> c <= ga /\ ga <= gb /\ gb <= d`) THEN
    ASM_REWRITE_TAC[GSYM IN_REAL_INTERVAL] THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL];
    DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:real->real) x`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
      HAS_REAL_DERIVATIVE_WITHIN_SUBSET) THEN
    ASM_REWRITE_TAC[]]);;

let REAL_INTEGRAL_SUBSTITUTION_SIMPLE = prove
 (`!f g g' a b c d.
        f real_continuous_on real_interval[c,d] /\
        (!x. x IN real_interval[a,b]
                  ==> (g has_real_derivative g'(x))
                      (atreal x within real_interval[a,b])) /\
        IMAGE g (real_interval[a,b]) SUBSET real_interval[c,d] /\
        a <= b /\ c <= d /\ g a <= g b
        ==> real_integral (real_interval[a,b]) (\x. f(g x) * g'(x)) =
            real_integral (real_interval[g a,g b]) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_MESON_TAC[HAS_REAL_INTEGRAL_SUBSTITUTION_SIMPLE]);;

(* ------------------------------------------------------------------------- *)
(* Drop the k'th coordinate, or insert t at the k'th coordinate.             *)
(* ------------------------------------------------------------------------- *)

let dropout = new_definition
 `(dropout:num->real^N->real^M) k x =
        lambda i. if i < k then x$i else x$(i + 1)`;;

let pushin = new_definition
 `pushin k t x = lambda i. if i < k then x$i
                           else if i = k then t
                           else x$(i - 1)`;;

let DROPOUT_PUSHIN = prove
 (`!k t x.
        dimindex(:M) + 1 = dimindex(:N)
        ==> (dropout k:real^N->real^M) (pushin k t x) = x`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  ASM_SIMP_TAC[CART_EQ; dropout; pushin; LAMBDA_BETA;
               ARITH_RULE `1 <= n + 1`; ADD_SUB;
               ARITH_RULE `m <= n ==> m <= n + 1 /\ m + 1 <= n + 1`] THEN
  ARITH_TAC);;

let PUSHIN_DROPOUT = prove
 (`!k x.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> pushin k (x$k) ((dropout k:real^N->real^M) x) = x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN(ASSUME_TAC o GSYM)) THEN
  ASM_SIMP_TAC[CART_EQ; dropout; pushin; LAMBDA_BETA;
               ARITH_RULE `i <= n + 1 ==> i - 1 <= n`] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[LT_REFL] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = k) ==> i < k \/ k < i`)) THEN
  ASM_SIMP_TAC[ARITH_RULE `i:num < k ==> ~(k < i)`] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) LAMBDA_BETA o lhand o snd) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  ASM_SIMP_TAC[ARITH_RULE `k < i ==> ~(i - 1 < k)`] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let DROPOUT_GALOIS = prove
 (`!k x:real^N y:real^M.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (y = dropout k x <=> (?t. x = pushin k t y))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `(x:real^N)$k` THEN ASM_SIMP_TAC[PUSHIN_DROPOUT];
    DISCH_THEN(X_CHOOSE_THEN `t:real` SUBST1_TAC) THEN
    ASM_SIMP_TAC[DROPOUT_PUSHIN]]);;

let IN_IMAGE_DROPOUT = prove
 (`!x s.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (x IN IMAGE (dropout k:real^N->real^M) s <=>
             ?t. (pushin k t x) IN s)`,
  SIMP_TAC[IN_IMAGE; DROPOUT_GALOIS] THEN MESON_TAC[]);;

let CLOSED_INTERVAL_DROPOUT = prove
 (`!k a b. dimindex(:M) + 1 = dimindex(:N) /\
           1 <= k /\ k <= dimindex(:N) /\
           a$k <= b$k
           ==> interval[dropout k a,dropout k b] =
               IMAGE (dropout k:real^N->real^M) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EXTENSION; IN_IMAGE_DROPOUT; IN_INTERVAL] THEN
  X_GEN_TAC `x:real^M` THEN
  SIMP_TAC[pushin; dropout; LAMBDA_BETA] THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `(a:real^N)$k` THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[SUB_ADD]]];
    DISCH_THEN(X_CHOOSE_TAC `t:real`) THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `i + 1`) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[ADD_SUB]]]);;

let IMAGE_DROPOUT_CLOSED_INTERVAL = prove
 (`!k a b. dimindex(:M) + 1 = dimindex(:N) /\
           1 <= k /\ k <= dimindex(:N)
           ==> IMAGE (dropout k:real^N->real^M) (interval[a,b]) =
                  if a$k <= b$k then interval[dropout k a,dropout k b]
                  else {}`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CLOSED_INTERVAL_DROPOUT; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY; GSYM REAL_NOT_LE] THEN ASM_MESON_TAC[]);;

let LINEAR_DROPOUT = prove
 (`!k. dimindex(:M) < dimindex(:N)
       ==> linear(dropout k :real^N->real^M)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `m < n ==> !i:num. i <= m ==> i <= n /\ i + 1 <= n`)) THEN
  SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           dropout; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               ARITH_RULE `1 <= i + 1`]);;

let DROPOUT_EQ = prove
 (`!x y k. dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
           x$k = y$k /\ (dropout k:real^N->real^M) x = dropout k y
           ==> x = y`,
  SIMP_TAC[CART_EQ; dropout; VEC_COMPONENT; LAMBDA_BETA; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `k:num`] THEN
  STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = k) ==> i < k \/ k < i`))
  THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
    ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `k < i ==> ~(i - 1 < k)`]] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let DROPOUT_0 = prove
 (`dropout k (vec 0:real^N) = vec 0`,
  SIMP_TAC[dropout; VEC_COMPONENT; CART_EQ; COND_ID; LAMBDA_BETA]);;

let DOT_DROPOUT = prove
 (`!k x y:real^N.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (dropout k x:real^M) dot (dropout k y) = x dot y - x$k * y$k`,
  REPEAT STRIP_TAC THEN SIMP_TAC[dot; dropout; LAMBDA_BETA] THEN
  REWRITE_TAC[TAUT `(if p then x else y:real) * (if p then a else b) =
                    (if p then x * a else y * b)`] THEN
  SIMP_TAC[SUM_CASES; FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `(!i. i IN 1..dimindex(:M) /\ i < k <=> i IN 1..k-1) /\
    (!i.  i IN 1..dimindex(:M) /\ ~(i < k) <=> i IN k..dimindex(:M))`
  (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_ID] THEN
  REWRITE_TAC[GSYM(SPEC `1` SUM_OFFSET)] THEN
  W(MP_TAC o PART_MATCH (rhs o rand) SUM_UNION o lhs o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; DISJOINT_NUMSEG] THEN ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`\i. (x:real^N)$i * (y:real^N)$i`;
                 `1..dimindex(:N)`;
                 `k:num`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_UNION; IN_DELETE] THEN ASM_ARITH_TAC);;

let DOT_PUSHIN = prove
 (`!k a b x y:real^M.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (pushin k a x:real^N) dot (pushin k b y) = x dot y + a * b`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(dropout k (pushin k a (x:real^M):real^N):real^M) dot
              (dropout k (pushin k b (y:real^M):real^N):real^M) +
              a * b` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[DROPOUT_PUSHIN]] THEN
  ASM_SIMP_TAC[DOT_DROPOUT] THEN
  MATCH_MP_TAC(REAL_RING
   `a':real = a /\ b' = b ==> x = x - a' * b' + a * b`) THEN
  ASM_SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL]);;

let DROPOUT_ADD = prove
 (`!k x y:real^N. dropout k (x + y) = dropout k x + dropout k y`,
  SIMP_TAC[dropout; VECTOR_ADD_COMPONENT; CART_EQ; LAMBDA_BETA] THEN
  MESON_TAC[]);;

let DROPOUT_SUB = prove
 (`!k x y:real^N. dropout k (x - y) = dropout k x - dropout k y`,
  SIMP_TAC[dropout; VECTOR_SUB_COMPONENT; CART_EQ; LAMBDA_BETA] THEN
  MESON_TAC[]);;

let DROPOUT_MUL = prove
 (`!k c x:real^N. dropout k (c % x) = c % dropout k x`,
  SIMP_TAC[dropout; VECTOR_MUL_COMPONENT; CART_EQ; LAMBDA_BETA] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Take slice of set s at x$k = t and drop the k'th coordinate.              *)
(* ------------------------------------------------------------------------- *)

let slice = new_definition
 `slice k t s = IMAGE (dropout k) (s INTER {x | x$k = t})`;;

let IN_SLICE = prove
 (`!s:real^N->bool y:real^M.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (y IN slice k t s <=> pushin k t y IN s)`,
  SIMP_TAC[slice; IN_IMAGE_DROPOUT; IN_INTER; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[pushin] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; LT_REFL] THEN MESON_TAC[]);;

let INTERVAL_INTER_HYPERPLANE = prove
 (`!k t a b:real^N.
        1 <= k /\ k <= dimindex(:N)
        ==> interval[a,b] INTER {x | x$k = t} =
                if a$k <= t /\ t <= b$k
                then interval[(lambda i. if i = k then t else a$i),
                              (lambda i. if i = k then t else b$i)]
                else {}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERVAL; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[NOT_IN_EMPTY]] THEN
  SIMP_TAC[IN_INTERVAL; LAMBDA_BETA] THEN
  EQ_TAC THEN STRIP_TAC THENL [ASM_MESON_TAC[REAL_LE_ANTISYM]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_ANTISYM]] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SLICE_INTERVAL = prove
 (`!k a b t. dimindex(:M) + 1 = dimindex(:N) /\
             1 <= k /\ k <= dimindex(:N)
             ==> slice k t (interval[a,b]) =
                 if a$k <= t /\ t <= b$k
                 then interval[(dropout k:real^N->real^M) a,dropout k b]
                 else {}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[slice; INTERVAL_INTER_HYPERPLANE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  ASM_SIMP_TAC[IMAGE_DROPOUT_CLOSED_INTERVAL; LAMBDA_BETA; REAL_LE_REFL] THEN
  MATCH_MP_TAC(MESON[]
   `a = a' /\ b = b' ==> interval[a,b] = interval[a',b']`) THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; dropout] THEN
  SUBGOAL_THEN
   `!i. i <= dimindex(:M) ==> i <= dimindex(:N) /\ i + 1 <= dimindex(:N)`
  MP_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[LAMBDA_BETA; ARITH_RULE `1 <= i + 1`] THEN ARITH_TAC]);;

let SLICE_DIFF = prove
 (`!k a s t.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (slice k a:(real^N->bool)->(real^M->bool)) (s DIFF t) =
             (slice k a s) DIFF (slice k a t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN
  SIMP_TAC[SET_RULE `(s DIFF t) INTER u = (s INTER u) DIFF (t INTER u)`] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x y. x IN a /\ y IN a /\ f x = f y ==> x = y)
    ==> IMAGE f ((s INTER a) DIFF (t INTER a)) =
        IMAGE f (s INTER a) DIFF IMAGE f (t INTER a)`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[DROPOUT_EQ]);;

let SLICE_UNIV = prove
 (`!k a. dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> slice k a (:real^N) = (:real^M)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[EXTENSION; IN_UNIV; IN_IMAGE; slice; INTER_UNIV; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^M` THEN EXISTS_TAC `(pushin k a:real^M->real^N) y` THEN
  ASM_SIMP_TAC[DROPOUT_PUSHIN] THEN
  ASM_SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL]);;

let SLICE_EMPTY = prove
 (`!k a. slice k a {} = {}`,
  REWRITE_TAC[slice; INTER_EMPTY; IMAGE_CLAUSES]);;

let SLICE_SUBSET = prove
 (`!s t k a. s SUBSET t ==> slice k a s SUBSET slice k a t`,
  REWRITE_TAC[slice] THEN SET_TAC[]);;

let SLICE_UNIONS = prove
 (`!s k a. slice k a (UNIONS s) = UNIONS (IMAGE (slice k a) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[slice; INTER_UNIONS; IMAGE_UNIONS] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; slice]);;

let SLICE_UNION = prove
 (`!k a s t.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (slice k a:(real^N->bool)->(real^M->bool)) (s UNION t) =
             (slice k a s) UNION (slice k a t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[slice; IMAGE_UNION;
        SET_RULE `(s UNION t) INTER u = (s INTER u) UNION (t INTER u)`] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; slice]);;

let SLICE_INTER = prove
 (`!k a s t.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (slice k a:(real^N->bool)->(real^M->bool)) (s INTER t) =
             (slice k a s) INTER (slice k a t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN
  MATCH_MP_TAC(SET_RULE
    `(!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)
     ==> IMAGE f ((s INTER t) INTER u) =
         IMAGE f (s INTER u) INTER IMAGE f (t INTER u)`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[DROPOUT_EQ]);;

let CONVEX_SLICE = prove
 (`!k t s. dimindex(:M) < dimindex(:N) /\ convex s
           ==> convex((slice k t:(real^N->bool)->(real^M->bool)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN
  MATCH_MP_TAC CONVEX_LINEAR_IMAGE THEN ASM_SIMP_TAC[LINEAR_DROPOUT] THEN
  MATCH_MP_TAC CONVEX_INTER THEN ASM_REWRITE_TAC[CONVEX_STANDARD_HYPERPLANE]);;

let COMPACT_SLICE = prove
 (`!k t s. dimindex(:M) < dimindex(:N) /\ compact s
           ==> compact((slice k t:(real^N->bool)->(real^M->bool)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN
  MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_SIMP_TAC[LINEAR_DROPOUT] THEN
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    MATCH_MP_TAC CLOSED_INTER THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_STANDARD_HYPERPLANE]]);;

let CLOSED_SLICE = prove
 (`!k t s. dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
           closed s
           ==> closed((slice k t:(real^N->bool)->(real^M->bool)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN
  SUBGOAL_THEN
   `closed(IMAGE (dropout k:real^N->real^M)
                 (IMAGE (\x. x - t % basis k)
                        (s INTER {x | x$k = t})))`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; dropout] THEN
    SUBGOAL_THEN
     `!i. i <= dimindex(:M) ==> i <= dimindex(:N) /\ i + 1 <= dimindex(:N)`
    MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; CART_EQ;
             LAMBDA_BETA; BASIS_COMPONENT; ARITH_RULE `1 <= i + 1`] THEN
    SIMP_TAC[ARITH_RULE `i:num < k ==> ~(i = k)`;
             ARITH_RULE `~(i < k) ==> ~(i + 1 = k)`] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO]] THEN
  MATCH_MP_TAC CLOSED_INJECTIVE_IMAGE_SUBSET_SUBSPACE THEN
  EXISTS_TAC `{x:real^N | x$k = &0}` THEN
  ASM_SIMP_TAC[SUBSPACE_SPECIAL_HYPERPLANE; LINEAR_DROPOUT;
               ARITH_RULE `m + 1 = n ==> m < n`] THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[VECTOR_ARITH `x - t % b:real^N = --(t % b) + x`] THEN
    ASM_SIMP_TAC[CLOSED_TRANSLATION_EQ; CLOSED_INTER;
                 CLOSED_STANDARD_HYPERPLANE];
    MATCH_MP_TAC(SET_RULE
     `IMAGE f t SUBSET u ==> IMAGE f (s INTER t) SUBSET u`) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
                 REAL_MUL_RID; REAL_SUB_REFL];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DROPOUT_EQ THEN EXISTS_TAC `k:num` THEN
    ASM_REWRITE_TAC[DROPOUT_0; VEC_COMPONENT]]);;

let OPEN_SLICE = prove
 (`!k t s. dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
           open s
           ==> open((slice k t:(real^N->bool)->(real^M->bool)) s)`,
  REWRITE_TAC[OPEN_CLOSED] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closed(slice k t ((:real^N) DIFF s):real^M->bool)`
  MP_TAC THENL
   [ASM_SIMP_TAC[CLOSED_SLICE];
   ASM_SIMP_TAC[SLICE_DIFF; SLICE_UNIV]]);;

let BOUNDED_SLICE = prove
 (`!k t s. dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
           bounded s
           ==> bounded((slice k t:(real^N->bool)->(real^M->bool)) s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `(slice k t:(real^N->bool)->(real^M->bool)) (interval[a,b])` THEN
  ASM_SIMP_TAC[SLICE_SUBSET] THEN ASM_SIMP_TAC[SLICE_INTERVAL] THEN
  MESON_TAC[BOUNDED_EMPTY; BOUNDED_INTERVAL]);;

let SLICE_CBALL = prove
 (`!k t x r.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (slice k t:(real^N->bool)->(real^M->bool)) (cball(x,r)) =
                if abs(t - x$k) <= r
                then cball(dropout k x,sqrt(r pow 2 - (t - x$k) pow 2))
                else {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY; IN_CBALL] THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[dist] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `~(a <= r) ==> a <= b ==> b <= r ==> F`)) THEN
    ASM_MESON_TAC[VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM; NORM_SUB]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(REAL_ARITH `abs(x) <= r ==> &0 <= r`)) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_CBALL] THEN X_GEN_TAC `y:real^M` THEN
  ASM_SIMP_TAC[DROPOUT_GALOIS; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[IN_CBALL; IN_INTER; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  ASM_REWRITE_TAC[dist; NORM_LE_SQUARE; GSYM pushin] THEN
  ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE; REAL_SUB_LE; GSYM REAL_LE_SQUARE_ABS;
               REAL_ARITH `abs(x) <= r ==> abs(x) <= abs(r)`] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(x - y:real^N) dot (x - y) = x dot x + y dot y - &2 * x dot y`] THEN
  ASM_SIMP_TAC[DOT_DROPOUT; DOT_PUSHIN] THEN MATCH_MP_TAC(REAL_FIELD
     `a = t * k + b
      ==> (xx + (yy + t * t) - &2 * a <= r pow 2 <=>
           xx - k * k + yy - &2 * b <= r pow 2 - (t - k) pow 2)`) THEN
  SUBGOAL_THEN
   `y:real^M = dropout k (pushin k t y:real^N)`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC DROPOUT_PUSHIN THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[DOT_DROPOUT] THEN
    ASM_SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL] THEN REAL_ARITH_TAC]);;

let SLICE_BALL = prove
 (`!k t x r.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (slice k t:(real^N->bool)->(real^M->bool)) (ball(x,r)) =
                if abs(t - x$k) < r
                then ball(dropout k x,sqrt(r pow 2 - (t - x$k) pow 2))
                else {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY; IN_BALL] THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[dist] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `~(a < r) ==> a <= b ==> b < r ==> F`)) THEN
    ASM_MESON_TAC[VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM; NORM_SUB]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(REAL_ARITH `abs(x) < r ==> &0 < r`)) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL] THEN X_GEN_TAC `y:real^M` THEN
  ASM_SIMP_TAC[DROPOUT_GALOIS; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[IN_BALL; IN_INTER; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  ASM_REWRITE_TAC[dist; NORM_LT_SQUARE; GSYM pushin] THEN
  ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; REAL_SUB_LT; GSYM REAL_LT_SQUARE_ABS;
   REAL_LT_IMP_LE; REAL_ARITH `abs(x) < r ==> abs(x) < abs(r)`] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(x - y:real^N) dot (x - y) = x dot x + y dot y - &2 * x dot y`] THEN
  ASM_SIMP_TAC[DOT_DROPOUT; DOT_PUSHIN] THEN MATCH_MP_TAC(REAL_FIELD
     `a = t * k + b
      ==> (xx + (yy + t * t) - &2 * a < r pow 2 <=>
           xx - k * k + yy - &2 * b < r pow 2 - (t - k) pow 2)`) THEN
  SUBGOAL_THEN
   `y:real^M = dropout k (pushin k t y:real^N)`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC DROPOUT_PUSHIN THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[DOT_DROPOUT] THEN
    ASM_SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Weak but useful versions of Fubini's theorem.                             *)
(* ------------------------------------------------------------------------- *)

let FUBINI_CLOSED_INTERVAL = prove
 (`!k a b:real^N.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        a$k <= b$k
        ==> ((\t. measure (slice k t (interval[a,b]) :real^M->bool))
             has_real_integral
             (measure(interval[a,b]))) (:real)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SLICE_INTERVAL] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[MEASURE_EMPTY; MEASURE_INTERVAL] THEN
  REWRITE_TAC[GSYM IN_REAL_INTERVAL] THEN
  SIMP_TAC[HAS_REAL_INTEGRAL_RESTRICT; SUBSET_UNIV] THEN
  SUBGOAL_THEN
   `content(interval[a:real^N,b]) =
    content(interval[dropout k a:real^M,dropout k b]) * (b$k - a$k)`
  SUBST1_TAC THEN ASM_SIMP_TAC[HAS_REAL_INTEGRAL_CONST] THEN
  REWRITE_TAC[CONTENT_CLOSED_INTERVAL_CASES] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV) [COND_RAND] THEN
  GEN_REWRITE_TAC RAND_CONV [COND_RATOR] THEN
  REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC(TAUT
   `(p <=> p') /\ x = x'
    ==> (if p then x else y) = (if p' then x' else y)`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[dropout; LAMBDA_BETA] THEN EQ_TAC THEN DISCH_TAC THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i:num < k` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
        COND_CASES_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[SUB_ADD]]] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `1..dimindex(:N) =
                (1..(k-1)) UNION
                (k INSERT (IMAGE (\x. x + 1) (k..dimindex(:M))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_UNION; IN_INSERT; IN_IMAGE] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `1 <= k
      ==> (x = y + 1 /\ k <= y /\ y <= n <=>
           y = x - 1 /\ k + 1 <= x /\ x <= n + 1)`] THEN
    REWRITE_TAC[CONJ_ASSOC; LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `s UNION (x INSERT t) = x INSERT (s UNION t)`] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG; FINITE_UNION; FINITE_IMAGE] THEN
  ASM_SIMP_TAC[IN_NUMSEG; IN_UNION; IN_IMAGE; ARITH_RULE
   `1 <= k ==> ~(k <= k - 1)`] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`1`; `k - 1`; `dimindex(:M)`] NUMSEG_COMBINE_R) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) PRODUCT_UNION o lhand o snd) THEN
  SIMP_TAC[FINITE_NUMSEG; FINITE_IMAGE; IN_NUMSEG; SET_RULE
            `DISJOINT s (IMAGE f t) <=> !x. x IN t ==> ~(f x IN s)`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) PRODUCT_UNION o rand o snd) THEN
  SIMP_TAC[FINITE_NUMSEG; FINITE_IMAGE; IN_NUMSEG; SET_RULE
            `DISJOINT s t <=> !x. ~(x IN s /\ x IN t)`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_IMAGE; EQ_ADD_RCANCEL; SUB_ADD] THEN
  BINOP_TAC THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
  SIMP_TAC[dropout; LAMBDA_BETA; o_THM] THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THEN
  (W(MP_TAC o PART_MATCH (lhs o rand) LAMBDA_BETA o rand o snd) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
   REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_ARITH_TAC));;

let MEASURABLE_OUTER_INTERVALS_BOUNDED_EXPLICIT_SPECIAL = prove
 (`!s a b e.
        2 <= dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
        measurable s /\ s SUBSET interval[a,b] /\ &0 < e
        ==> ?f:num->real^N->bool.
              (!i. (f i) SUBSET interval[a,b] /\
                   ?c d. c$k <= d$k /\ f i = interval[c,d]) /\
              (!i j. ~(i = j) ==> negligible(f i INTER f j)) /\
              s SUBSET UNIONS {f n | n IN (:num)} /\
              measurable(UNIONS {f n | n IN (:num)}) /\
              measure(UNIONS {f n | n IN (:num)}) <= measure s + e`,
  let lemma = prove
   (`UNIONS {if n IN s then f n else {} | n IN (:num)} =
     UNIONS (IMAGE f s)`,
   SIMP_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV; EXISTS_IN_IMAGE] THEN
   MESON_TAC[NOT_IN_EMPTY]) in
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MEASURABLE_OUTER_INTERVALS_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `FINITE(d:(real^N->bool)->bool)` THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:num->real^N->bool`
     (fun th -> SUBST_ALL_TAC(CONJUNCT2 th) THEN ASSUME_TAC(CONJUNCT1 th))) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; FORALL_IN_IMAGE;
       RIGHT_FORALL_IMP_THM; IN_UNIV]) THEN
    EXISTS_TAC `\k. if k IN 1..CARD(d:(real^N->bool)->bool) then f k
                    else ({}:real^N->bool)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[REAL_NOT_LT; IN_NUMSEG; REAL_NOT_LE; INTERVAL_EQ_EMPTY];
        REWRITE_TAC[EMPTY_SUBSET] THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
        EXISTS_TAC `(lambda i. if i = k then &0 else &1):real^N` THEN
        EXISTS_TAC `(lambda i. if i = k then &1 else &0):real^N` THEN
        REWRITE_TAC[INTERVAL_EQ_EMPTY] THEN CONJ_TAC THENL
         [SIMP_TAC[LAMBDA_BETA; ASSUME `1 <= k`; ASSUME `k <= dimindex(:N)`;
                   REAL_POS];
          ALL_TAC] THEN
        SUBGOAL_THEN `?j. 1 <= j /\ j <= dimindex(:N) /\ ~(j = k)` MP_TAC THENL
         [MATCH_MP_TAC(MESON[] `P(k - 1) \/ P(k + 1) ==> ?i. P i`) THEN
          ASM_ARITH_TAC;
          MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[LAMBDA_BETA] THEN
          REAL_ARITH_TAC]];
      ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[lemma]] THEN
    REPEAT GEN_TAC THEN
      REPEAT(COND_CASES_TAC THEN
             ASM_REWRITE_TAC[INTER_EMPTY; NEGLIGIBLE_EMPTY]);
    MP_TAC(ISPEC `d:(real^N->bool)->bool` COUNTABLE_AS_INJECTIVE_IMAGE) THEN
    ASM_REWRITE_TAC[INFINITE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `f:num->real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; FORALL_IN_IMAGE;
       RIGHT_FORALL_IMP_THM; IN_UNIV]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM SIMPLE_IMAGE]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_NOT_LT; IN_NUMSEG; REAL_NOT_LE; INTERVAL_EQ_EMPTY];
        ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`]] THEN
  (DISCH_TAC THEN
   SUBGOAL_THEN `negligible(interior((f:num->real^N->bool) i) INTER
                            interior(f j))`
   MP_TAC THENL [ASM_MESON_TAC[NEGLIGIBLE_EMPTY]; ALL_TAC] THEN
   REWRITE_TAC[GSYM INTERIOR_INTER] THEN
   REWRITE_TAC[GSYM HAS_MEASURE_0] THEN
   MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
     HAS_MEASURE_NEGLIGIBLE_SYMDIFF) THEN
   SIMP_TAC[INTERIOR_SUBSET; SET_RULE
      `interior(s) SUBSET s
       ==> (interior s DIFF s) UNION (s DIFF interior s) =
           s DIFF interior s`] THEN
   SUBGOAL_THEN `(?c d. (f:num->real^N->bool) i = interval[c,d]) /\
                 (?c d. (f:num->real^N->bool) j = interval[c,d])`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[INTER_INTERVAL; NEGLIGIBLE_FRONTIER_INTERVAL;
                   INTERIOR_CLOSED_INTERVAL]));;

let REAL_MONOTONE_CONVERGENCE_INCREASING_AE = prove
 (`!f:num->real->real g s.
        (!k. (f k) real_integrable_on s) /\
        (!k x. x IN s ==> f k x <= f (SUC k) x) /\
        (?t. real_negligible t /\
             !x. x IN (s DIFF t) ==> ((\k. f k x) ---> g x) sequentially) /\
        real_bounded {real_integral s (f k) | k IN (:num)}
        ==> g real_integrable_on s /\
            ((\k. real_integral s (f k)) ---> real_integral s g) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `g real_integrable_on (s DIFF t) /\
    ((\k. real_integral (s DIFF t) (f k)) ---> real_integral (s DIFF t) g)
    sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_MONOTONE_CONVERGENCE_INCREASING THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `!k:num. f k real_integrable_on s` THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SPIKE_SET;
      ASM_SIMP_TAC[IN_DIFF];
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_bounded]) THEN
      REWRITE_TAC[real_bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC REAL_INTEGRAL_SPIKE_SET];
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SPIKE_SET_EQ THEN
      MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `t:real->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      AP_THM_TAC THEN BINOP_TAC THENL
       [ABS_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_INTEGRAL_SPIKE_SET]] THEN
  MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `t:real->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let FUBINI_SIMPLE_LEMMA = prove
 (`!k s:real^N->bool e.
        &0 < e /\
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\ measurable s /\
        (!t. measurable(slice k t s:real^M->bool)) /\
        (\t. measure (slice k t s:real^M->bool)) real_integrable_on (:real)
        ==> real_integral(:real) (\t. measure (slice k t s :real^M->bool))
                <= measure s + e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `b:real^N`; `e:real`]
        MEASURABLE_OUTER_INTERVALS_BOUNDED_EXPLICIT_SPECIAL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [SUBGOAL_THEN `1 <= dimindex(:M)` MP_TAC THENL
     [REWRITE_TAC[DIMINDEX_GE_1]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->(real^N->bool)` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t n:num. measurable((slice k t:(real^N->bool)->real^M->bool)
                                     (d n))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `n:num`] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONJUNCT2 o SPEC `n:num`) THEN
    ASM_SIMP_TAC[SLICE_INTERVAL] THEN
    MESON_TAC[MEASURABLE_EMPTY; MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(UNIONS {d n | n IN (:num)}:real^N->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
       [`\n t. sum(0..n)
           (\m. measure((slice k t:(real^N->bool)->real^M->bool)
                       (d m)))`;
        `\t. measure((slice k t:(real^N->bool)->real^M->bool)
                   (UNIONS {d n | n IN (:num)}))`; `(:real)`]
         REAL_MONOTONE_CONVERGENCE_INCREASING_AE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN MATCH_MP_TAC REAL_INTEGRABLE_SUM THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `j:num` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o SPEC `j:num`) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`k:num`; `u:real^N`; `v:real^N`]
        FUBINI_CLOSED_INTERVAL) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[real_integrable_on];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
      REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC MEASURE_POS_LE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[real_bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
      EXISTS_TAC `measure(interval[a:real^N,b])` THEN X_GEN_TAC `i:num` THEN
      W(MP_TAC o PART_MATCH (lhand o rand) REAL_INTEGRAL_SUM o
        rand o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `?u v. u$k <= v$k /\
                            (d:num->real^N->bool) j = interval[u,v]`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_integrable_on] THEN
        EXISTS_TAC `measure(interval[u:real^N,v])` THEN
        MATCH_MP_TAC FUBINI_CLOSED_INTERVAL THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(sum(0..i) (\m. measure(d m:real^N->bool)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
        MATCH_MP_TAC SUM_EQ_NUMSEG THEN
        X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
        SUBGOAL_THEN `?u v. u$k <= v$k /\
                            (d:num->real^N->bool) j = interval[u,v]`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FUBINI_CLOSED_INTERVAL THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= a ==> abs x <= a`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
        ASM_MESON_TAC[MEASURE_POS_LE; MEASURABLE_INTERVAL];
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (rhs o rand) MEASURE_NEGLIGIBLE_UNIONS_IMAGE o
        lhand o snd) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FINITE_NUMSEG] THEN ASM_MESON_TAC[MEASURABLE_INTERVAL];
        ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      REWRITE_TAC[MEASURABLE_INTERVAL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_UNIONS THEN
        ASM_SIMP_TAC[FINITE_NUMSEG; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
        ASM_MESON_TAC[MEASURABLE_INTERVAL];
        REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]]] THEN
    EXISTS_TAC
     `(IMAGE (\i. (interval_lowerbound(d i):real^N)$k) (:num)) UNION
      (IMAGE (\i. (interval_upperbound(d i):real^N)$k) (:num))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN
      SIMP_TAC[COUNTABLE_UNION; COUNTABLE_IMAGE; NUM_COUNTABLE];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN
    REWRITE_TAC[IN_DIFF; IN_UNION; IN_IMAGE] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [IN_UNIV] THEN
    REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `\n:num. (slice k t:(real^N->bool)->real^M->bool)
                          (d n)`
       HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED) THEN
    ASM_REWRITE_TAC[SLICE_UNIONS] THEN ANTS_TAC THENL
     [ALL_TAC;
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
      REWRITE_TAC[GSYM REAL_SUMS; real_sums; FROM_INTER_NUMSEG] THEN
      REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF]] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `(slice k t:(real^N->bool)->real^M->bool) (interval[a,b])` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[SLICE_INTERVAL] THEN
        MESON_TAC[BOUNDED_INTERVAL; BOUNDED_EMPTY];
        REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
        ASM_MESON_TAC[SLICE_SUBSET]]] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(d:num->real^N->bool) i = {}` THENL
     [ASM_REWRITE_TAC[INTER_EMPTY; NEGLIGIBLE_EMPTY; SLICE_EMPTY];
      UNDISCH_TAC `~((d:num->real^N->bool) i = {})`] THEN
    ASM_CASES_TAC `(d:num->real^N->bool) j = {}` THENL
     [ASM_REWRITE_TAC[INTER_EMPTY; NEGLIGIBLE_EMPTY; SLICE_EMPTY];
      UNDISCH_TAC `~((d:num->real^N->bool) j = {})`] THEN
    FIRST_ASSUM(fun th ->
      MAP_EVERY (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
       [SPEC `i:num` th; SPEC `j:num` th]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`w:real^N`; `x:real^N`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SLICE_INTERVAL; INTERVAL_NE_EMPTY] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[INTER_EMPTY; NEGLIGIBLE_EMPTY]) THEN
    REWRITE_TAC[INTER_INTERVAL; NEGLIGIBLE_INTERVAL; INTERVAL_EQ_EMPTY] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a /\ b ==> ~c)`] THEN
    SIMP_TAC[LAMBDA_BETA] THEN REWRITE_TAC[NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(l:num = k)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN
       (fun th -> MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `j:num` th))) THEN
      ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND] THEN
      REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `~(l:num = k) ==> l < k \/ k < l`))
    THENL
     [EXISTS_TAC `l:num` THEN
      MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[dropout; LAMBDA_BETA]] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `l - 1` THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[dropout; LAMBDA_BETA]] THEN
    ASM_SIMP_TAC[ARITH_RULE `k < l ==> ~(l - 1 < k)`] THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `real_integral (:real)
        (\t. measure ((slice k t :(real^N->bool)->real^M->bool)
                      (UNIONS {d n | n IN (:num)})))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[SLICE_SUBSET; SLICE_UNIONS] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
    MATCH_MP_TAC MEASURABLE_COUNTABLE_UNIONS_BOUNDED THEN
    ASM_REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `(slice k t:(real^N->bool)->real^M->bool) (interval[a,b])` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[SLICE_INTERVAL] THEN
      MESON_TAC[BOUNDED_INTERVAL; BOUNDED_EMPTY];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      ASM_MESON_TAC[SLICE_SUBSET]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
    EXISTS_TAC `\n. real_integral (:real)
       (\t. sum (0..n) (\m. measure((slice k t:(real^N->bool)->real^M->bool)

                         (d m))))` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MP_TAC(ISPEC `d:num->(real^N->bool)`
     HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MEASURABLE_INTERVAL]; ALL_TAC] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `interval[a:real^N,b]` THEN
      REWRITE_TAC[BOUNDED_INTERVAL; UNIONS_SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
    REWRITE_TAC[GSYM REAL_SUMS] THEN
    REWRITE_TAC[real_sums; FROM_INTER_NUMSEG] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) REAL_INTEGRAL_SUM o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v. u$k <= v$k /\
                          (d:num->real^N->bool) j = interval[u,v]`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_integrable_on] THEN
      EXISTS_TAC `measure(interval[u:real^N,v])` THEN
      MATCH_MP_TAC FUBINI_CLOSED_INTERVAL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    SUBGOAL_THEN `?u v. u$k <= v$k /\
                          (d:num->real^N->bool) j = interval[u,v]`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUBINI_CLOSED_INTERVAL THEN ASM_REWRITE_TAC[]]);;

let FUBINI_SIMPLE = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\
        measurable s /\
        (!t. measurable(slice k t s :real^M->bool)) /\
        (\t. measure (slice k t s :real^M->bool)) real_integrable_on (:real)
        ==> measure s =
              real_integral(:real)(\t. measure (slice k t s :real^M->bool))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[SLICE_EMPTY; MEASURE_EMPTY; REAL_INTEGRAL_0];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interval[a:real^N,b] = {})` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[INTERVAL_NE_EMPTY] THEN DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < b - a) /\ ~(&0 < a - b) ==> a:real = b`) THEN
  CONJ_TAC THEN MATCH_MP_TAC(MESON[]
     `(!e. x - y = e ==> ~(&0 < e)) ==> ~(&0 < x - y)`) THEN
  X_GEN_TAC `e:real` THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `e / &2`]
      FUBINI_SIMPLE_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `interval[a:real^N,b] DIFF s`; `e / &2`]
    FUBINI_SIMPLE_LEMMA) THEN
  ASM_REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [SIMP_TAC[BOUNDED_DIFF; BOUNDED_INTERVAL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTERVAL]; ALL_TAC] THEN
  ASM_SIMP_TAC[SLICE_DIFF] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN MATCH_MP_TAC MEASURABLE_DIFF THEN
    ASM_SIMP_TAC[SLICE_INTERVAL] THEN
    MESON_TAC[MEASURABLE_EMPTY; MEASURABLE_INTERVAL];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `!t. measure(slice k t (interval[a:real^N,b]) DIFF
                slice k t (s:real^N->bool) :real^M->bool) =
        measure(slice k t (interval[a:real^N,b]):real^M->bool) -
        measure(slice k t s :real^M->bool)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [X_GEN_TAC `t:real` THEN MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
    ASM_SIMP_TAC[SLICE_SUBSET] THEN
    ASM_SIMP_TAC[SLICE_INTERVAL] THEN
    MESON_TAC[MEASURABLE_EMPTY; MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `a:real^N`; `b:real^N`] FUBINI_CLOSED_INTERVAL) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN ASM_MESON_TAC[real_integrable_on];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  ASM_SIMP_TAC[MEASURE_DIFF_SUBSET; MEASURABLE_INTERVAL] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) REAL_INTEGRAL_SUB o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[real_integrable_on]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  ASM_REAL_ARITH_TAC);;

let FUBINI_SIMPLE_ALT = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\
        measurable s /\
        (!t. measurable(slice k t s :real^M->bool)) /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measure s = B`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `real_integral (:real)
                 (\t. measure (slice k t (s:real^N->bool) :real^M->bool))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FUBINI_SIMPLE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[real_integrable_on];
    MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]]);;

let FUBINI_SIMPLE_COMPACT_STRONG = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        compact s /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measurable s /\ measure s = B`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN
  MATCH_MP_TAC FUBINI_SIMPLE_ALT THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; MEASURABLE_COMPACT] THEN
  GEN_TAC THEN MATCH_MP_TAC MEASURABLE_COMPACT THEN
  MATCH_MP_TAC COMPACT_SLICE THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FUBINI_SIMPLE_COMPACT = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        compact s /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measure s = B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_SIMPLE_COMPACT_STRONG) THEN SIMP_TAC[]);;

let FUBINI_SIMPLE_CONVEX_STRONG = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\ convex s /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measurable s /\ measure s = B`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MEASURABLE_CONVEX] THEN
  MATCH_MP_TAC FUBINI_SIMPLE_ALT THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MEASURABLE_CONVEX] THEN
  GEN_TAC THEN MATCH_MP_TAC MEASURABLE_CONVEX THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_SLICE; MATCH_MP_TAC BOUNDED_SLICE] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FUBINI_SIMPLE_CONVEX = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\ convex s /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measure s = B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_SIMPLE_CONVEX_STRONG) THEN SIMP_TAC[]);;

let FUBINI_SIMPLE_OPEN_STRONG = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\ open s /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measurable s /\ measure s = B`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MEASURABLE_OPEN] THEN
  MATCH_MP_TAC FUBINI_SIMPLE_ALT THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MEASURABLE_OPEN] THEN
  GEN_TAC THEN MATCH_MP_TAC MEASURABLE_OPEN THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_SLICE; MATCH_MP_TAC OPEN_SLICE] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FUBINI_SIMPLE_OPEN = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\ open s /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measure s = B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_SIMPLE_OPEN_STRONG) THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Scaled integer, and hence rational, values are dense in the reals.        *)
(* ------------------------------------------------------------------------- *)

let REAL_OPEN_SET_RATIONAL = prove
 (`!s. real_open s /\ ~(s = {}) ==> ?x. rational x /\ x IN s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MP_TAC(ISPEC `IMAGE lift s` OPEN_SET_RATIONAL_COORDINATES) THEN
  ASM_REWRITE_TAC[GSYM REAL_OPEN; IMAGE_EQ_EMPTY; EXISTS_IN_IMAGE] THEN
  SIMP_TAC[DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP]);;

let REAL_OPEN_RATIONAL = prove
 (`!P. real_open {x | P x} /\ (?x. P x) ==> ?x. rational x /\ P x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `{x:real | P x}` REAL_OPEN_SET_RATIONAL) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let REAL_OPEN_SET_EXISTS_RATIONAL = prove
 (`!s. real_open s ==> ((?x. rational x /\ x IN s) <=> (?x. x IN s))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_MESON_TAC[REAL_OPEN_SET_RATIONAL; GSYM MEMBER_NOT_EMPTY]);;

let REAL_OPEN_EXISTS_RATIONAL = prove
 (`!P. real_open {x | P x} ==> ((?x. rational x /\ P x) <=> (?x. P x))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_OPEN_SET_EXISTS_RATIONAL) THEN
  REWRITE_TAC[IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Hence a criterion for two functions to agree.                             *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CONST_DYADIC_RATIONALS = prove
 (`!f:real^M->real^N a.
     f continuous_on (:real^M) /\
     (!x. (!i. 1 <= i /\ i <= dimindex(:M) ==> integer(x$i)) ==> f(x) = a) /\
     (!x. f(x) = a ==> f(inv(&2) % x) = a)
     ==> !x. f(x) = a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC(ISPECL
   [`f:real^M->real^N`;
    `{ inv(&2 pow n) % x:real^M |n,x|
       !i. 1 <= i /\ i <= dimindex(:M) ==> integer(x$i) }`;
    `a:real^N`] CONTINUOUS_CONSTANT_ON_CLOSURE) THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC; CLOSURE_DYADIC_RATIONALS; IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[real_pow; REAL_INV_1; VECTOR_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_INV_MUL; GSYM VECTOR_MUL_ASSOC]);;

let REAL_CONTINUOUS_ON_CONST_DYADIC_RATIONALS = prove
 (`!f a.
     f real_continuous_on (:real) /\
     (!x. integer(x) ==> f(x) = a) /\
     (!x. f(x) = a ==> f(x / &2) = a)
     ==> !x. f(x) = a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift a`]
    CONTINUOUS_ON_CONST_DYADIC_RATIONALS) THEN
  ASM_REWRITE_TAC[GSYM REAL_CONTINUOUS_ON; GSYM IMAGE_LIFT_UNIV] THEN
  ASM_SIMP_TAC[o_THM; DIMINDEX_1; FORALL_1; GSYM drop; LIFT_EQ; DROP_CMUL;
               REAL_ARITH `inv(&2) * x = x / &2`] THEN
  ASM_MESON_TAC[LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Various sufficient conditions for additivity to imply linearity.          *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ADDITIVE_IMP_LINEAR = prove
 (`!f:real^M->real^N.
        f continuous_on (:real^M) /\
        (!x y. f(x + y) = f(x) + f(y))
        ==> linear f`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) (vec 0) = vec 0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o repeat (SPEC `vec 0:real^M`)) THEN
    REWRITE_TAC[VECTOR_ADD_LID] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[linear] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN X_GEN_TAC `x:real^M` THEN
  MP_TAC(ISPECL [`\c. norm((f:real^M->real^N)(c % x) - c % f(x))`; `&0`]
        REAL_CONTINUOUS_ON_CONST_DYADIC_RATIONALS) THEN
  REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_UNIV; WITHIN_UNIV]) THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_UNIV] THEN
    GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN
    SIMP_TAC[REAL_CONTINUOUS_NORM_WITHIN] THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
    ASM_SIMP_TAC[REWRITE_RULE[GSYM REAL_CONTINUOUS_CONTINUOUS1]CONTINUOUS_VMUL;
                 REAL_CONTINUOUS_WITHIN_ID; CONTINUOUS_AT_WITHIN;
                 REWRITE_RULE[o_DEF] CONTINUOUS_WITHINREAL_COMPOSE];
    MATCH_MP_TAC FORALL_INTEGER THEN CONJ_TAC THENL
     [INDUCT_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO; GSYM REAL_OF_NUM_SUC] THEN
      ASM_REWRITE_TAC[VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID];
      X_GEN_TAC `c:real` THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`c % x:real^M`; `--(c % x):real^M`]) THEN
      ASM_REWRITE_TAC[VECTOR_ADD_RINV; VECTOR_MUL_LNEG; IMP_IMP] THEN
      VECTOR_ARITH_TAC];
    X_GEN_TAC `c:real` THEN
    FIRST_X_ASSUM(MP_TAC o funpow 2 (SPEC `c / &2 % x:real^M`)) THEN
    REWRITE_TAC[VECTOR_ARITH `c / &2 % x + c / &2 % x:real^N = c % x`] THEN
    REWRITE_TAC[IMP_IMP] THEN VECTOR_ARITH_TAC]);;

let OSTROWSKI_THEOREM = prove
 (`!f:real^M->real^N B s.
        (!x y. f(x + y) = f(x) + f(y)) /\
        (!x. x IN s ==> norm(f x) <= B) /\
        measurable s /\ &0 < measure s
        ==> linear f`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC o
    MATCH_MP STEINHAUS) THEN
  SUBGOAL_THEN `!x y. (f:real^M->real^N)(x - y) = f x - f y` ASSUME_TAC THENL
   [ASM_MESON_TAC[VECTOR_ARITH `x - y:real^M = z <=> x = y + z`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n x. &n % (f:real^M->real^N) x = f(&n % x)` ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [ASM_MESON_TAC[VECTOR_SUB_REFL; VECTOR_MUL_LZERO];
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC; VECTOR_ADD_RDISTRIB] THEN
      REWRITE_TAC[VECTOR_MUL_LID]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ADDITIVE_IMP_LINEAR THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. norm(x) < d ==> norm((f:real^M->real^N) x) <= &2 * B`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M` o GEN_REWRITE_RULE I [SUBSET]) THEN
    ASM_REWRITE_TAC[IN_BALL_0] THEN SPEC_TAC(`z:real^M`,`z:real^M`) THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN(ANTE_RES_THEN MP_TAC)) THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  REWRITE_TAC[continuous_on; IN_UNIV; dist] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `e:real`] THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC o SPEC `max (&1) (&2 * B)`) THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [REAL_ARITH_TAC; DISCH_TAC] THEN
  EXISTS_TAC `d / &n` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1] THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(&n % (f:real^M->real^N)(y - x)) <= &2 * B` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[NORM_MUL; REAL_ABS_NUM] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; LE_1];
    SIMP_TAC[NORM_MUL; REAL_ABS_NUM] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LET_TRANS) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    ASM_REAL_ARITH_TAC]);;

let MEASURABLE_ADDITIVE_IMP_LINEAR = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) /\ (!x y. f(x + y) = f(x) + f(y))
        ==> linear f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OSTROWSKI_THEOREM THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MEASURABLE_ON_NORM) THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `!b. negligible {x | norm((f:real^M->real^N) x) <= b}` THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP NEGLIGIBLE_COUNTABLE_UNIONS o
        GEN `n:num` o SPEC `&n:real`) THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV; REAL_ARCH_SIMPLE] THEN
    SIMP_TAC[SET_RULE `{x | T} = (:real^M)`; OPEN_NOT_NEGLIGIBLE;
             OPEN_UNIV; UNIV_NOT_EMPTY];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
    ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
    REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
    EXISTS_TAC `{x:real^M | norm(f x:real^N) <= B} INTER interval[a,b]` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER] THEN
    MATCH_MP_TAC(MESON[MEASURABLE_MEASURE_POS_LT]
     `measurable s /\ ~negligible s ==> measurable s /\ &0 < measure s`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE THEN
    ASM_REWRITE_TAC[MEASURABLE_INTERVAL]]);;

let REAL_CONTINUOUS_ADDITIVE_IMP_LINEAR = prove
 (`!f. f real_continuous_on (:real) /\
       (!x y. f(x + y) = f(x) + f(y))
       ==> !a x. f(a * x) = a * f(x)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `lift o f o drop` CONTINUOUS_ADDITIVE_IMP_LINEAR) THEN
  ASM_REWRITE_TAC[GSYM REAL_CONTINUOUS_ON; GSYM IMAGE_LIFT_UNIV] THEN
  ASM_REWRITE_TAC[linear; GSYM FORALL_DROP; o_THM; DROP_ADD; LIFT_DROP;
                  DROP_CMUL; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Extending a continuous function in a periodic way.                        *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_FLOOR = prove
 (`!x. ~(integer x) ==> floor real_continuous (atreal x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_continuous_atreal] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `min (x - floor x) ((floor x + &1) - x)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_SUB_LT; REAL_FLOOR_LT; FLOOR] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x = y ==> abs(x - y) < e`) THEN
  ASM_REWRITE_TAC[GSYM FLOOR_UNIQUE; FLOOR] THEN
  MP_TAC(ISPEC `x:real` FLOOR) THEN ASM_REAL_ARITH_TAC);;

let REAL_CONTINUOUS_FRAC = prove
 (`!x. ~(integer x) ==> frac real_continuous (atreal x)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[FRAC_FLOOR] THEN MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_FLOOR; REAL_CONTINUOUS_AT_ID]);;

let REAL_CONTINUOUS_ON_COMPOSE_FRAC = prove
 (`!f. f real_continuous_on real_interval[&0,&1] /\ f(&1) = f(&0)
       ==> (f o frac) real_continuous_on (:real)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `f real_continuous_on real_interval[&0,&1]` THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; WITHINREAL_UNIV] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `integer x` THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN
    ASM_SIMP_TAC[REAL_CONTINUOUS_FRAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [IN_REAL_INTERVAL] o
                  SPEC `frac x`) THEN
    ASM_SIMP_TAC[FLOOR_FRAC; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[real_continuous_atreal; real_continuous_withinreal] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d (min (frac x) (&1 - frac x))` THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_SUB_LT; FLOOR_FRAC; REAL_FRAC_POS_LT] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC[real_continuous_atreal; REAL_FRAC_ZERO; REAL_FLOOR_REFL] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (BINDER_CONV o LAND_CONV)
     [IN_REAL_INTERVAL]) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `&1` th) THEN MP_TAC(SPEC `&0` th)) THEN
  REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
  REWRITE_TAC[IMP_IMP; real_continuous_withinreal; AND_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)
               (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `min (&1) (min d1 d2)` THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_LT_MIN; o_DEF] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `x <= y \/ y < x`) THENL
   [SUBGOAL_THEN `floor y = floor x` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM FLOOR_UNIQUE; FLOOR] THEN
      ASM_SIMP_TAC[REAL_FLOOR_REFL] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[FRAC_FLOOR; REAL_FLOOR_REFL; REAL_SUB_REFL] THEN
      FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REAL_ARITH_TAC)];
    SUBGOAL_THEN `floor y = floor x - &1` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM FLOOR_UNIQUE; FLOOR] THEN
      ASM_SIMP_TAC[REAL_FLOOR_REFL; INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[FRAC_FLOOR; REAL_FLOOR_REFL; REAL_SUB_REFL] THEN
      FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REAL_ARITH_TAC)]]);;

let REAL_TIETZE_PERIODIC_INTERVAL = prove
 (`!f a b.
        f real_continuous_on real_interval[a,b] /\ f(a) = f(b)
        ==> ?g. g real_continuous_on (:real) /\
                (!x. x IN real_interval[a,b] ==> g(x) = f(x)) /\
                (!x. g(x + (b - a)) = g x)`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH `b:real <= a \/ a < b`) THENL
   [EXISTS_TAC `\x:real. (f:real->real) a` THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST] THEN
    ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_ANTISYM];
    EXISTS_TAC `(f:real->real) o (\y. a + (b - a) * y) o frac o
                (\x. (x - a) / (b - a))` THEN
    REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[real_div; REAL_CONTINUOUS_ON_RMUL; REAL_CONTINUOUS_ON_SUB;
               REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE_FRAC THEN
      ASM_SIMP_TAC[o_THM; REAL_MUL_RZERO; REAL_MUL_RID; REAL_SUB_ADD2;
                   REAL_ADD_RID] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[REAL_CONTINUOUS_ON_LMUL; REAL_CONTINUOUS_ON_ADD;
               REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        REAL_CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      ASM_SIMP_TAC[REAL_LE_ADDR; REAL_LE_MUL; REAL_LT_IMP_LE; REAL_SUB_LT] THEN
      REWRITE_TAC[REAL_ARITH
       `a + (b - a) * x <= b <=> &0 <= (b - a) * (&1 - x)`] THEN
       ASM_SIMP_TAC[REAL_LE_ADDR; REAL_LE_MUL; REAL_LT_IMP_LE; REAL_SUB_LE];
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN ASM_CASES_TAC `x:real = b` THENL
       [ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_SUB_LT] THEN
        ASM_REWRITE_TAC[FRAC_NUM; REAL_MUL_RZERO; REAL_ADD_RID];
        SUBGOAL_THEN `frac((x - a) / (b - a)) = (x - a) / (b - a)`
        SUBST1_TAC THENL
         [REWRITE_TAC[REAL_FRAC_EQ] THEN
          ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_SUB_LT] THEN
          ASM_REAL_ARITH_TAC;
          AP_TERM_TAC THEN UNDISCH_TAC `a:real < b` THEN CONV_TAC REAL_FIELD]];
      ASM_SIMP_TAC[REAL_FIELD
        `a < b ==> ((x + b - a) - a) / (b - a) = &1 + (x - a) / (b - a)`] THEN
      REWRITE_TAC[REAL_FRAC_ADD; FRAC_NUM; FLOOR_FRAC; REAL_ADD_LID]]]);;

(* ------------------------------------------------------------------------- *)
(* A variant of REAL_CONTINUOUS_ADDITIVE_IMP_LINEAR for intervals.           *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_ADDITIVE_EXTEND = prove
 (`!f. f real_continuous_on real_interval[&0,&1] /\
       (!x y. &0 <= x /\ &0 <= y /\ x + y <= &1
              ==> f(x + y) = f(x) + f(y))
       ==> ?g.  g real_continuous_on (:real) /\
                (!x y. g(x + y) = g(x) + g(y)) /\
                (!x. x IN real_interval[&0,&1] ==> g x = f x)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `f(&0) = &0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o ISPECL [`&0`; `&0`]) THEN
    REWRITE_TAC[REAL_ADD_LID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\x. f(&1) * floor(x) + f(frac x)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `f real_continuous_on real_interval[&0,&1]` THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; WITHINREAL_UNIV] THEN
    DISCH_TAC THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `integer x` THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN CONJ_TAC THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_LMUL; REAL_CONTINUOUS_FLOOR; ETA_AX] THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] REAL_CONTINUOUS_ATREAL_COMPOSE) THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_FRAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [IN_REAL_INTERVAL] o
                    SPEC `frac x`) THEN
      ASM_SIMP_TAC[FLOOR_FRAC; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[real_continuous_atreal; real_continuous_withinreal] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
      ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min d (min (frac x) (&1 - frac x))` THEN
      ASM_SIMP_TAC[REAL_LT_MIN; REAL_SUB_LT; FLOOR_FRAC; REAL_FRAC_POS_LT] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[real_continuous_atreal; REAL_FRAC_ZERO; REAL_FLOOR_REFL] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (BINDER_CONV o LAND_CONV)
       [IN_REAL_INTERVAL]) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `&1` th) THEN MP_TAC(SPEC `&0` th)) THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
    REWRITE_TAC[IMP_IMP; real_continuous_withinreal; AND_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)
                 (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `min (&1) (min d1 d2)` THEN
    ASM_REWRITE_TAC[REAL_LT_01; REAL_LT_MIN] THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `x <= y \/ y < x`) THENL
     [SUBGOAL_THEN `floor y = floor x` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM FLOOR_UNIQUE; FLOOR] THEN
        ASM_SIMP_TAC[REAL_FLOOR_REFL] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[FRAC_FLOOR; REAL_FLOOR_REFL] THEN
        REWRITE_TAC[REAL_ARITH `(a + x) - (a + &0) = x - &0`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `floor y = floor x - &1` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM FLOOR_UNIQUE; FLOOR] THEN
        ASM_SIMP_TAC[REAL_FLOOR_REFL; INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[FRAC_FLOOR; REAL_FLOOR_REFL] THEN
        REWRITE_TAC[REAL_ARITH `(f1 * (x - &1) + f) - (f1 * x + &0) =
                                f - f1`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    REPEAT GEN_TAC THEN REWRITE_TAC[REAL_FLOOR_ADD; REAL_FRAC_ADD] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; FLOOR_FRAC; REAL_LE_ADD] THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `f1 * ((x + y) + &1) + g = (f1 * x + z) + f1 * y + h <=>
      f1 / &2 + g / &2 = z / &2 + h / &2`] THEN
    SUBGOAL_THEN
     `!t. &0 <= t /\ t <= &1 ==> f(t) / &2 = f(t / &2)`
    ASSUME_TAC THENL
     [GEN_TAC THEN FIRST_ASSUM(MP_TAC o ISPECL [`t / &2`; `t / &2`]) THEN
      REWRITE_TAC[REAL_HALF] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_REFL; FLOOR_FRAC; REAL_LT_IMP_LE;
                 REAL_ARITH `~(x + y < &1) ==> &0 <= (x + y) - &1`;
                 REAL_ARITH `x < &1 /\ y < &1 ==> (x + y) - &1 <= &1`] THEN
    MATCH_MP_TAC(MESON[]
     `f(a + b) = f a + f b /\ f(c + d) = f(c) + f(d) /\ a + b = c + d
      ==> (f:real->real)(a) + f(b) = f(c) + f(d)`) THEN
    REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY (MP_TAC o C SPEC FLOOR_FRAC) [`x:real`; `y:real`] THEN
    ASM_REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_CASES_TAC `x = &1` THEN
    ASM_REWRITE_TAC[FLOOR_NUM; FRAC_NUM; REAL_MUL_RID; REAL_ADD_RID] THEN
    STRIP_TAC THEN SUBGOAL_THEN `floor x = &0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM FLOOR_UNIQUE; INTEGER_CLOSED];
      ASM_REWRITE_TAC[FRAC_FLOOR; REAL_SUB_RZERO]] THEN
    ASM_REAL_ARITH_TAC]);;

let REAL_CONTINUOUS_ADDITIVE_IMP_LINEAR_INTERVAL = prove
 (`!f b. (f ---> &0) (atreal (&0) within {x | &0 <= x}) /\
         (!x y. &0 <= x /\ &0 <= y /\ x + y <= b ==> f(x + y) = f(x) + f(y))
         ==> !a x. &0 <= x /\ x <= b /\
                   &0 <= a * x /\ a * x <= b
                   ==> f(a * x) = a * f(x)`,
  SUBGOAL_THEN
   `!f. (f ---> &0) (atreal (&0) within {x | &0 <= x}) /\
        (!x y. &0 <= x /\ &0 <= y /\ x + y <= &1 ==> f(x + y) = f(x) + f(y))
        ==> !a x. &0 <= x /\ x <= &1 /\ &0 <= a * x /\ a * x <= &1
                  ==> f(a * x) = a * f(x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!f. f real_continuous_on real_interval[&0,&1] /\
          (!x y. &0 <= x /\ &0 <= y /\ x + y <= &1 ==> f(x + y) = f(x) + f(y))
          ==> !a x. &0 <= x /\ x <= &1 /\ &0 <= a * x /\ a * x <= &1
                    ==> f(a * x) = a * f(x)`
    (fun th -> GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th) THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPEC `f:real->real` REAL_CONTINUOUS_ADDITIVE_EXTEND) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPEC `g:real->real` REAL_CONTINUOUS_ADDITIVE_IMP_LINEAR) THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[real_continuous_on; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_WITHINREAL]) THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
      ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
       (REAL_ARITH `y = x \/ y < x \/ x < y`) THENL
       [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM];
        SUBGOAL_THEN `(f:real->real)(y + (x - y)) = f(y) + f(x - y)`
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_SUB_ADD2] THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[REAL_ADD_SUB2; REAL_ABS_NEG] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `(f:real->real)(x + (y - x)) = f(x) + f(y - x)`
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_SUB_ADD2] THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[REAL_ADD_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (REAL_ARITH `b < &0 \/ b = &0 \/ &0 < b`)
    THENL
     [ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ARITH
       `a <= x /\ x <= a /\ a <= y /\ y <= a <=> x = a /\ y = a`] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `&0`]) THEN
      ASM_REWRITE_TAC[REAL_ADD_LID; REAL_LE_REFL] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o ISPEC `(\x. f(b * x)):real->real`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `a:real` THEN
      DISCH_THEN(fun th -> X_GEN_TAC `x:real` THEN STRIP_TAC THEN
                           MP_TAC(ISPEC `x / b:real` th)) THEN
      ASM_SIMP_TAC[REAL_FIELD `&0 < b ==> b * a * x / b = a * x`;
                   REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[REAL_ARITH `a * x / b:real = (a * x) / b`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_ARITH `b * x + b * y <= b <=> &0 <= b * (&1 - (x + y))`;
                   REAL_LE_MUL; REAL_LT_IMP_LE; REAL_SUB_LE]] THEN
    REWRITE_TAC[REALLIM_WITHINREAL] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_WITHINREAL]) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    REWRITE_TAC[REAL_SUB_RZERO; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d / b:real` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < b ==> abs b * x = x * b`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; GSYM REAL_LT_RDIV_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* More Steinhaus variants.                                                  *)
(* ------------------------------------------------------------------------- *)

let STEINHAUS_TRIVIAL = prove
 (`!s e. ~(negligible s) /\ &0 < e
         ==> ?x y:real^N. x IN s /\ y IN s /\ ~(x = y) /\ norm(x - y) < e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE THEN
  MATCH_MP_TAC DISCRETE_IMP_COUNTABLE THEN
  ASM_MESON_TAC[REAL_NOT_LT]);;

let REAL_STEINHAUS = prove
 (`!s. real_measurable s /\ &0 < real_measure s
       ==> ?d. &0 < d /\
               real_interval(--d,d) SUBSET {x - y | x IN s /\ y IN s}`,
  GEN_TAC THEN SIMP_TAC[IMP_CONJ; REAL_MEASURE_MEASURE] THEN
  REWRITE_TAC[IMP_IMP; REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP STEINHAUS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  REWRITE_TAC[SUBSET; BALL_INTERVAL; IN_INTERVAL_1; IN_REAL_INTERVAL] THEN
  REWRITE_TAC[SET_RULE `{g x y | x IN IMAGE f s /\ y IN IMAGE f t} =
                        {g (f x) (f y) | x IN s /\ y IN t}`] THEN
  REWRITE_TAC[GSYM LIFT_SUB] THEN
  REWRITE_TAC[SET_RULE `{lift(f x y) | P x y} = IMAGE lift {f x y | P x y}`;
              IN_IMAGE_LIFT_DROP; GSYM FORALL_DROP] THEN
  REWRITE_TAC[DROP_SUB; DROP_VEC; LIFT_DROP; DROP_ADD] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bernstein polynomials.                                                    *)
(* ------------------------------------------------------------------------- *)

let bernstein = new_definition
 `bernstein n k x = &(binom(n,k)) * x pow k * (&1 - x) pow (n - k)`;;

let BERNSTEIN_CONV =
  GEN_REWRITE_CONV I [bernstein] THENC
  COMB2_CONV (RAND_CONV(RAND_CONV NUM_BINOM_CONV))
             (RAND_CONV(RAND_CONV NUM_SUB_CONV)) THENC
  REAL_POLY_CONV;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about Bernstein polynomials.                                       *)
(* ------------------------------------------------------------------------- *)

let BERNSTEIN_POS = prove
 (`!n k x. &0 <= x /\ x <= &1 ==> &0 <= bernstein n k x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bernstein] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC);;

let SUM_BERNSTEIN = prove
 (`!n. sum (0..n) (\k. bernstein n k x) = &1`,
  REWRITE_TAC[bernstein; GSYM REAL_BINOMIAL_THEOREM] THEN
  REWRITE_TAC[REAL_SUB_ADD2; REAL_POW_ONE]);;

let BERNSTEIN_LEMMA = prove
 (`!n x. sum(0..n) (\k. (&k - &n * x) pow 2 * bernstein n k x) =
         &n * x * (&1 - x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!x y. sum(0..n) (\k. &(binom(n,k)) * x pow k * y pow (n - k)) =
           (x + y) pow n`
  (LABEL_TAC "0") THENL [ASM_REWRITE_TAC[REAL_BINOMIAL_THEOREM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. sum(0..n) (\k. &k * &(binom(n,k)) * x pow (k - 1) * y pow (n - k)) =
          &n * (x + y) pow (n - 1)`
  (LABEL_TAC "1") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC
     [`\x. sum(0..n) (\k. &(binom(n,k)) * x pow k * y pow (n - k))`;
      `x:real`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG];
      ASM_REWRITE_TAC[]] THEN
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. sum(0..n)
        (\k. &k * &(k - 1) * &(binom(n,k)) * x pow (k - 2) * y pow (n - k)) =
          &n * &(n - 1) * (x + y) pow (n - 2)`
  (LABEL_TAC "2") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC
     [`\x. sum(0..n) (\k. &k * &(binom(n,k)) * x pow (k - 1) * y pow (n - k))`;
      `x:real`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG];
      ASM_REWRITE_TAC[]] THEN
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
    REWRITE_TAC[ARITH_RULE `n - 1 - 1 = n - 2`] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `(a - b) pow 2 * x =
    a * (a - &1) * x + (&1 - &2 * b) * a * x + b * b * x`] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_BERNSTEIN] THEN
  SUBGOAL_THEN `sum(0..n) (\k. &k * bernstein n k x) = &n * x` SUBST1_TAC THENL
   [REMOVE_THEN "1" (MP_TAC o SPECL [`x:real`; `&1 - x`]) THEN
    REWRITE_TAC[REAL_SUB_ADD2; REAL_POW_ONE; bernstein; REAL_MUL_RID] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH
     `(k * b * xk * y) * x:real = k * b * (x * xk) * y`] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
    DISJ_CASES_TAC(ARITH_RULE `k = 0 \/ SUC(k - 1) = k`) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
  `sum(0..n) (\k. &k * (&k - &1) * bernstein n k x) = &n * (&n - &1) * x pow 2`
  SUBST1_TAC THENL [ALL_TAC; CONV_TAC REAL_RING] THEN
  REMOVE_THEN "2" (MP_TAC o SPECL [`x:real`; `&1 - x`]) THEN
  REWRITE_TAC[REAL_SUB_ADD2; REAL_POW_ONE; bernstein; REAL_MUL_RID] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[SUM_SING_NUMSEG; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LE_1; REAL_MUL_ASSOC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `((((k * k1) * b) * xk) * y) * x2:real =
                            k * k1 * b * y * (x2 * xk)`] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD; GSYM REAL_MUL_ASSOC] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (ARITH_RULE `k = 0 \/ k = 1 \/ 1 <= k /\ 2 + k - 2 = k`) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; SUB_REFL; REAL_SUB_REFL] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REWRITE_TAC[REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Explicit Bernstein version of 1D Weierstrass approximation theorem        *)
(* ------------------------------------------------------------------------- *)

let BERNSTEIN_WEIERSTRASS = prove
 (`!f e.
      f real_continuous_on real_interval[&0,&1] /\ &0 < e
      ==> ?N. !n x. N <= n /\ x IN real_interval[&0,&1]
                    ==> abs(f x -
                            sum(0..n) (\k. f(&k / &n) * bernstein n k x)) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_bounded(IMAGE f (real_interval[&0,&1]))` MP_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL];
    REWRITE_TAC[REAL_BOUNDED_POS; LEFT_IMP_EXISTS_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `M:real` THEN STRIP_TAC] THEN
  SUBGOAL_THEN `f real_uniformly_continuous_on real_interval[&0,&1]`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_COMPACT_UNIFORMLY_CONTINUOUS; REAL_COMPACT_INTERVAL];
    REWRITE_TAC[real_uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `!n x. 0 < n /\ &0 <= x /\ x <= &1
          ==> abs(f x - sum(0..n) (\k. f(&k / &n) * bernstein n k x))
                <= e / &2 + (&2 * M) / (d pow 2 * &n)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(sum(0..n) (\k. (f x - f(&k / &n)) * bernstein n k x))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG; SUM_LMUL] THEN
      REWRITE_TAC[SUM_BERNSTEIN; REAL_MUL_RID; REAL_LE_REFL];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH lhand SUM_ABS_NUMSEG o lhand o snd) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[BERNSTEIN_POS; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum(0..n) (\k. (e / &2 + &2 * M / d pow 2 * (x - &k / &n) pow 2) *
                     bernstein n k x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[BERNSTEIN_POS] THEN
      SUBGOAL_THEN `&0 <= &k / &n /\ &k / &n <= &1` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE; MULT_CLAUSES];
        ALL_TAC] THEN
      DISJ_CASES_TAC(REAL_ARITH
        `abs(x - &k / &n) < d \/ d <= abs(x - &k / &n)`)
      THENL
       [MATCH_MP_TAC(REAL_ARITH `x < e /\ &0 <= d ==> x <= e + d`) THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 <= &2 * x <=> &0 <= x`] THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_POW_2; REAL_LE_SQUARE;
                     REAL_LT_IMP_LE];
        MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= d ==> x <= e / &2 + d`) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH
         `abs(x) <= M /\ abs(y) <= M /\ M * &1 <= M * b / d
          ==> abs(x - y) <= &2 * M / d * b`) THEN
        ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_POW_LT; REAL_LE_RDIV_EQ] THEN
        REWRITE_TAC[REAL_MUL_LID; GSYM REAL_LE_SQUARE_ABS] THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG; SUM_LMUL] THEN
      REWRITE_TAC[SUM_BERNSTEIN; REAL_MUL_RID; REAL_LE_LADD] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN
      REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_OF_NUM_LT; ARITH; REAL_POW_LT;
                   REAL_LT_INV_EQ] THEN
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&n pow 2` THEN
      ASM_SIMP_TAC[GSYM SUM_LMUL; REAL_POW_LT; REAL_OF_NUM_LT; REAL_FIELD
        `&0 < n ==> n pow 2 * inv(n) = n`] THEN
      REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_MUL] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LT; REAL_FIELD
        `&0 < n ==> n * (x - k * inv n) = n * x - k`] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `(x - y:real) pow 2 = (y - x) pow 2`] THEN
      REWRITE_TAC[BERNSTEIN_LEMMA; REAL_ARITH
        `&n * x <= &n <=> &n * x <= &n * &1 * &1`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    MP_TAC(ISPEC `(e / &4 * d pow 2) / (&2 * M)` REAL_ARCH_INV) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH; REAL_LT_MUL] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_POW_LT; REAL_MUL_LZERO] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
    REWRITE_TAC[REAL_ARITH `(x * &2 * m) * i = (&2 * m) * (i * x)`] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:real`]) THEN ASM_SIMP_TAC[] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ k < e / &4 ==> x <= e / &2 + k ==> x < e`) THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> y <= x ==> y < e`)) THEN
    ASM_SIMP_TAC[real_div; REAL_LE_LMUL_EQ; REAL_LT_MUL;
                 REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_MUL; REAL_POW_LT;
                 REAL_OF_NUM_LT; LE_1; REAL_OF_NUM_LE]]);;

(* ------------------------------------------------------------------------- *)
(* General Stone-Weierstrass theorem.                                        *)
(* ------------------------------------------------------------------------- *)

let STONE_WEIERSTRASS_ALT = prove
 (`!(P:(real^N->real)->bool) (s:real^N->bool).
        compact s /\
        (!c. P(\x. c)) /\
        (!f g. P(f) /\ P(g) ==> P(\x. f x + g x)) /\
        (!f g. P(f) /\ P(g) ==> P(\x. f x * g x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y)
               ==> ?f. (!x. x IN s ==> f real_continuous (at x within s)) /\
                       P(f) /\ ~(f x = f y))
        ==> !f e. (!x. x IN s ==> f real_continuous (at x within s)) /\ &0 < e
                  ==> ?g. P(g) /\ !x. x IN s ==> abs(f x - g x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY ABBREV_TAC
   [`C = \f. !x:real^N. x IN s ==> f real_continuous at x within s`;
    `A = \f. C f /\
             !e. &0 < e
               ==> ?g. P(g) /\ !x:real^N. x IN s ==> abs(f x - g x) < e`] THEN
  SUBGOAL_THEN `!f:real^N->real. C(f) ==> A(f)` MP_TAC THENL
   [ALL_TAC; MAP_EVERY EXPAND_TAC ["A"; "C"] THEN SIMP_TAC[]] THEN
  SUBGOAL_THEN `!c:real. A(\x:real^N. c)` (LABEL_TAC "const") THENL
   [MAP_EVERY EXPAND_TAC ["A"; "C"] THEN X_GEN_TAC `c:real` THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN EXISTS_TAC `(\x. c):real^N->real` THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f g:real^N->real. A(f) /\ A(g) ==> A(\x. f x + g x)`
  (LABEL_TAC "add") THENL
   [MAP_EVERY EXPAND_TAC ["A"; "C"] THEN SIMP_TAC[REAL_CONTINUOUS_ADD] THEN
    MAP_EVERY X_GEN_TAC [`f:real^N->real`; `g:real^N->real`] THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `e / &2` o CONJUNCT2)) THEN
    ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g':real^N->real` THEN STRIP_TAC THEN
    X_GEN_TAC `f':real^N->real` THEN STRIP_TAC THEN
    EXISTS_TAC `(\x. f' x + g' x):real^N->real` THEN
    ASM_SIMP_TAC[REAL_ARITH
     `abs(f - f') < e / &2 /\ abs(g - g') < e / &2
      ==> abs((f + g) - (f' + g')) < e`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^N->real. A(f) ==> C(f)` (LABEL_TAC "AC") THENL
   [EXPAND_TAC "A" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^N->real. C(f) ==> real_bounded(IMAGE f s)`
  (LABEL_TAC "bound") THENL
   [GEN_TAC THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[REAL_BOUNDED; GSYM IMAGE_o] THEN
    REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1] THEN
    REWRITE_TAC[GSYM CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; COMPACT_CONTINUOUS_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f g:real^N->real. A(f) /\ A(g) ==> A(\x. f x * g x)`
  (LABEL_TAC "mul") THENL
   [MAP_EVERY X_GEN_TAC [`f:real^N->real`; `g:real^N->real`] THEN
    DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
    MAP_EVERY EXPAND_TAC ["A"; "C"] THEN SIMP_TAC[REAL_CONTINUOUS_MUL] THEN
    REWRITE_TAC[IMP_CONJ] THEN
    MAP_EVERY (DISCH_THEN o LABEL_TAC) ["cf"; "af"; "cg"; "ag"] THEN
    SUBGOAL_THEN
     `real_bounded(IMAGE (f:real^N->real) s) /\
      real_bounded(IMAGE (g:real^N->real) s)`
    MP_TAC THENL
     [ASM_SIMP_TAC[]; REWRITE_TAC[REAL_BOUNDED_POS_LT; FORALL_IN_IMAGE]] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `Bf:real` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `Bg:real` STRIP_ASSUME_TAC)) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "ag" (MP_TAC o SPEC `e / &2 / Bf`) THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g':real^N->real` THEN STRIP_TAC THEN
    REMOVE_THEN "af" (MP_TAC o SPEC `e / &2 / (Bg + e / &2 / Bf)`) THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; REAL_LT_ADD] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real^N->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(\x. f'(x) * g'(x)):real^N->real` THEN
    ASM_SIMP_TAC[REAL_ARITH
     `f * g - f' * g':real = f * (g - g') + g' * (f - f')`] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `e = Bf * e / &2 / Bf +
                      (Bg + e / &2 / Bf) * e / &2 / (Bg + e / &2 / Bf)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a = e / &2 /\ b = e / &2 ==> e = a + b`) THEN
      CONJ_TAC THEN MAP_EVERY MATCH_MP_TAC [REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_ADD; REAL_HALF];
      MATCH_MP_TAC(REAL_ARITH
       `abs a < c /\ abs b < d ==> abs(a + b) < c + d`) THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!g. abs(g) < Bg /\ abs(g - g') < e ==> abs(g') < Bg + e`) THEN
      EXISTS_TAC `(g:real^N->real) x` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN s /\ y IN s /\ ~(x = y)
          ==> ?f:real^N->real. A(f) /\ ~(f x = f y)`
  (LABEL_TAC "sep") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    MAP_EVERY EXPAND_TAC ["A"; "C"] THEN
    ASM_MESON_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f. A(f) ==> A(\x:real^N. abs(f x))` (LABEL_TAC "abs") THENL
   [SUBGOAL_THEN `!f. A(f) /\ (!x. x IN s ==> abs(f x) <= &1 / &4)
                      ==> A(\x:real^N. abs(f x))`
    ASSUME_TAC THENL
     [ALL_TAC;
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `real_bounded(IMAGE (f:real^N->real) s)` MP_TAC THENL
       [ASM_SIMP_TAC[]; REWRITE_TAC[REAL_BOUNDED_POS_LT; FORALL_IN_IMAGE]] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `A(\x:real^N. (&4 * B) * abs(inv(&4 * B) * f x)):bool`
      MP_TAC THENL
       [USE_THEN "mul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_ABS_MUL] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < B ==> abs(B) = B`;
                     REAL_LT_INV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_LT_MUL;
                     REAL_OF_NUM_LT; ARITH; REAL_MUL_ASSOC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_MUL_LID; REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < B ==> abs(B) = B`;
                     REAL_LT_INV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
        ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_LID;
                     REAL_ARITH `&0 < B ==> ~(&4 * B = &0)`]]] THEN
    X_GEN_TAC `f:real^N->real` THEN MAP_EVERY EXPAND_TAC ["A"; "C"] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
     [DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT1) THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT; o_DEF]
        REAL_CONTINUOUS_WITHIN_COMPOSE) THEN
      REWRITE_TAC[real_continuous_withinreal] THEN
      MESON_TAC[ARITH_RULE `abs(x - y) < d ==> abs(abs x - abs y) < d`];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(fun t -> X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC t) THEN
    DISCH_THEN(MP_TAC o SPEC `min (e / &2) (&1 / &4)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN; FORALL_AND_THM;
                TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N->real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\x. abs(x - &1 / &2)`; `e / &2`]
     BERNSTEIN_WEIERSTRASS) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[real_continuous_on; REAL_HALF] THEN
      MESON_TAC[ARITH_RULE
       `abs(x - y) < d ==> abs(abs(x - a) - abs(y - a)) < d`];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
    EXISTS_TAC `\x:real^N. sum(0..n) (\k. abs(&k / &n - &1 / &2) *
                                          bernstein n k (&1 / &2 + p x))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `!m c z. P(\x:real^N.
            sum(0..m) (\k. c k * bernstein (z m) k (&1 / &2 + p x)))`
       (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN
       `!m k. P(\x:real^N. bernstein m k (&1 / &2 + p x))`
      ASSUME_TAC THENL
       [ALL_TAC; INDUCT_TAC THEN ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0]] THEN
      REPEAT GEN_TAC THEN REWRITE_TAC[bernstein] THEN
      REWRITE_TAC[REAL_ARITH `&1 - (&1 / &2 + p) = &1 / &2 + -- &1 * p`] THEN
      REPEAT(FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]) THEN
      SUBGOAL_THEN
       `!f:real^N->real k. P(f) ==> P(\x. f(x) pow k)`
       (fun th -> ASM_SIMP_TAC[th]) THEN
      GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[real_pow];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
       `!p. abs(abs(p x) - s) < e / &2 /\
            abs(f x - p x) < e / &2
            ==> abs(abs(f x) - s) < e`) THEN
      EXISTS_TAC `p:real^N->real` THEN ASM_SIMP_TAC[] THEN
      GEN_REWRITE_TAC (PAT_CONV `\x. abs(abs x - a) < e`)
        [REAL_ARITH `x = (&1 / &2 + x) - &1 / &2`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!f. abs(f) <= &1 / &4 /\ abs(f - p) < &1 / &4
            ==> &0 <= &1 / &2 + p /\ &1 / &2 + p <= &1`) THEN
      EXISTS_TAC `(f:real^N->real) x` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^N->real g. A(f) /\ A(g) ==> A(\x. max (f x) (g x))`
  (LABEL_TAC "max") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ARITH
     `max a b = inv(&2) * (a + b + abs(a + -- &1 * b))`] THEN
    REPEAT(FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^N->real g. A(f) /\ A(g) ==> A(\x. min (f x) (g x))`
  (LABEL_TAC "min") THENL
   [ASM_SIMP_TAC[REAL_ARITH `min a b = -- &1 * (max(-- &1 * a) (-- &1 * b))`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. FINITE t /\ (!f. f IN t ==> A(f)) ==> A(\x:real^N. sup {f(x) | f IN t})`
  (LABEL_TAC "sup") THENL
   [REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[FORALL_IN_INSERT; SIMPLE_IMAGE; IMAGE_CLAUSES] THEN
    ASM_SIMP_TAC[SUP_INSERT_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`f:real^N->real`; `t:(real^N->real)->bool`] THEN
    ASM_CASES_TAC `t:(real^N->real)->bool = {}` THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. FINITE t /\ (!f. f IN t ==> A(f)) ==> A(\x:real^N. inf {f(x) | f IN t})`
  (LABEL_TAC "inf") THENL
   [REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[FORALL_IN_INSERT; SIMPLE_IMAGE; IMAGE_CLAUSES] THEN
    ASM_SIMP_TAC[INF_INSERT_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`f:real^N->real`; `t:(real^N->real)->bool`] THEN
    ASM_CASES_TAC `t:(real^N->real)->bool = {}` THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^N->real e.
      C(f) /\ &0 < e ==> ?g. A(g) /\ !x. x IN s ==> abs(f x - g x) < e`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `f:real^N->real` THEN DISCH_TAC THEN EXPAND_TAC "A" THEN
    CONJ_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:real^N->real`; `e / &2`]) THEN
    ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `h:real^N->real` THEN EXPAND_TAC "A" THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC[REAL_ARITH
     `abs(f - h) < e / &2 /\ abs(h - g) < e / &2 ==> abs(f - g) < e`]] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real`; `e:real`] THEN EXPAND_TAC "C" THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!x y. x IN s /\ y IN s
          ==> ?h:real^N->real. A(h) /\ h(x) = f(x) /\ h(y) = f(y)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `y:real^N = x` THENL
     [EXISTS_TAC `\z:real^N. (f:real^N->real) x` THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN `?h:real^N->real. A(h) /\ ~(h x = h y)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `\z. (f y - f x) / (h y - h x) * (h:real^N->real)(z) +
                      (f x - (f y - f x) / (h y - h x) * h(x))` THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `~((h:real^N->real) x = h y)` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f2:real^N->real^N->real^N->real` THEN DISCH_TAC THEN
  ABBREV_TAC `G = \x y.
    {z | z IN s /\ (f2:real^N->real^N->real^N->real) x y z < f(z) + e}` THEN
  SUBGOAL_THEN `!x y:real^N. x IN s /\ y IN s ==> x IN G x y /\ y IN G x y`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[REAL_LT_ADDR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s ==> ?f1. A(f1) /\ f1 x = f x /\
                        !y:real^N. y IN s ==> f1 y < f y + e`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY]) THEN
    DISCH_THEN(MP_TAC o SPEC
     `{(G:real^N->real^N->real^N->bool) x y | y IN s}`) THEN
    REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE; FORALL_IN_IMAGE; ETA_AX] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      EXPAND_TAC "G" THEN REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`lift o (\z:real^N. f2 (x:real^N) (w:real^N) z - f z)`;
                     `s:real^N->bool`;
                     `{x:real^1 | x$1 < e}`] CONTINUOUS_OPEN_IN_PREIMAGE) THEN
      REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM] THEN
      REWRITE_TAC[GSYM drop; LIFT_DROP; o_DEF] THEN
      REWRITE_TAC[LIFT_SUB; GSYM REAL_CONTINUOUS_CONTINUOUS1;
                  REAL_ARITH `x < y + e <=> x - y < e`] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN
      REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS1; ETA_AX] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
    REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE; UNIONS_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\z:real^N. inf {f2 (x:real^N) (y:real^N) z | y IN t}` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `x = min x x`] THEN
      REWRITE_TAC[REAL_MIN_INF; INSERT_AC] THEN AP_TERM_TAC THEN ASM SET_TAC[];
      REMOVE_THEN "inf" (MP_TAC o SPEC
       `IMAGE (\y z. (f2:real^N->real^N->real^N->real) x y z) t`) THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[SIMPLE_IMAGE; ETA_AX] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF];
      SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_INF_LT_FINITE; SIMPLE_IMAGE;
                   FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      UNDISCH_TAC
       `s SUBSET {y:real^N | ?z:real^N. z IN t /\ y IN G (x:real^N) z}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `f1:real^N->real^N->real` THEN DISCH_TAC] THEN
  ABBREV_TAC `H = \x:real^N. {z:real^N | z IN s /\ f z - e < f1 x z}` THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> x IN (H x)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[REAL_ARITH `x - e < x <=> &0 < e`];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o
  GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY]) THEN
  DISCH_THEN(MP_TAC o SPEC
   `{(H:real^N->real^N->bool) x | x IN s}`) THEN
  REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE; FORALL_IN_IMAGE; ETA_AX] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN EXPAND_TAC "H" THEN
    REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`lift o (\z:real^N. f z - f1 (x:real^N) z)`;
                   `s:real^N->bool`;
                   `{x:real^1 | x$1 < e}`] CONTINUOUS_OPEN_IN_PREIMAGE) THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP; o_DEF] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [REAL_ARITH `x - y < z <=> x - z < y`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LIFT_SUB; GSYM REAL_CONTINUOUS_CONTINUOUS1;
                REAL_ARITH `x < y + e <=> x - y < e`] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS1; ETA_AX] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE; UNIONS_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:real^N. sup {f1 (x:real^N) z | x IN t}` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REMOVE_THEN "sup" (MP_TAC o SPEC `IMAGE (f1:real^N->real^N->real) t`) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[SIMPLE_IMAGE; ETA_AX] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SIMPLE_IMAGE; REAL_ARITH
   `abs(f - s) < e <=> f - e < s /\ s < f + e`] THEN
  ASM_SIMP_TAC[REAL_SUP_LT_FINITE; REAL_LT_SUP_FINITE;
               FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  UNDISCH_TAC `s SUBSET {y:real^N | ?x:real^N. x IN t /\ y IN H x}` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "H" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]);;

let STONE_WEIERSTRASS = prove
 (`!(P:(real^N->real)->bool) (s:real^N->bool).
        compact s /\
        (!f. P(f) ==> !x. x IN s ==> f real_continuous (at x within s)) /\
        (!c. P(\x. c)) /\
        (!f g. P(f) /\ P(g) ==> P(\x. f x + g x)) /\
        (!f g. P(f) /\ P(g) ==> P(\x. f x * g x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> ?f. P(f) /\ ~(f x = f y))
        ==> !f e. (!x. x IN s ==> f real_continuous (at x within s)) /\ &0 < e
                  ==> ?g. P(g) /\ !x. x IN s ==> abs(f x - g x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC STONE_WEIERSTRASS_ALT THEN ASM_SIMP_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]);;
