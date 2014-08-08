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
include Realanalysis3

(* ------------------------------------------------------------------------- *)
(* Real and complex versions of Stone-Weierstrass theorem.                   *)
(* ------------------------------------------------------------------------- *)

let REAL_STONE_WEIERSTRASS_ALT = prove
 (`!P s. real_compact s /\
         (!c. P (\x. c)) /\
         (!f g. P f /\ P g ==> P (\x. f x + g x)) /\
         (!f g. P f /\ P g ==> P (\x. f x * g x)) /\
         (!x y. x IN s /\ y IN s /\ ~(x = y)
                ==> ?f. f real_continuous_on s /\ P f /\ ~(f x = f y))
         ==> !f e. f real_continuous_on s /\ &0 < e
                   ==> ?g. P g /\ !x. x IN s ==> abs(f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\f. (P:(real->real)->bool)(f o lift)`;
    `IMAGE lift s`] STONE_WEIERSTRASS_ALT) THEN
  ASM_SIMP_TAC[GSYM real_compact; o_DEF] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    X_GEN_TAC `y:real` THEN REWRITE_TAC[LIFT_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(g:real->real) o drop` THEN
    ASM_REWRITE_TAC[o_THM; LIFT_DROP; ETA_AX] THEN
    UNDISCH_TAC `g real_continuous_on s` THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_WITHINREAL] THEN
    REWRITE_TAC[real_continuous_within; continuous_within] THEN
    REWRITE_TAC[o_THM; LIFT_DROP; DIST_LIFT];
    DISCH_THEN(MP_TAC o SPEC `(f:real->real) o drop`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `f real_continuous_on s` THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_WITHINREAL] THEN
      REWRITE_TAC[real_continuous_within; continuous_within] THEN
      REWRITE_TAC[o_THM; LIFT_DROP; DIST_LIFT];
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
      ASM_REWRITE_TAC[o_DEF; LIFT_DROP] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^1->real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(g:real^1->real) o lift` THEN ASM_REWRITE_TAC[o_DEF]]]);;

let REAL_STONE_WEIERSTRASS = prove
 (`!P s. real_compact s /\
         (!f. P f ==> f real_continuous_on s) /\
         (!c. P (\x. c)) /\
         (!f g. P f /\ P g ==> P (\x. f x + g x)) /\
         (!f g. P f /\ P g ==> P (\x. f x * g x)) /\
         (!x y. x IN s /\ y IN s /\ ~(x = y) ==> ?f. P f /\ ~(f x = f y))
         ==> !f e. f real_continuous_on s /\ &0 < e
                   ==> ?g. P g /\ !x. x IN s ==> abs(f x - g x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_STONE_WEIERSTRASS_ALT THEN ASM_SIMP_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]);;

let COMPLEX_STONE_WEIERSTRASS_ALT = prove
 (`!P s. compact s /\
         (!c. P (\x. c)) /\
         (!f. P f ==> P(\x. cnj(f x))) /\
         (!f g. P f /\ P g ==> P (\x. f x + g x)) /\
         (!f g. P f /\ P g ==> P (\x. f x * g x)) /\
         (!x y. x IN s /\ y IN s /\ ~(x = y)
                ==> ?f. P f /\ f continuous_on s /\ ~(f x = f y))
         ==> !f:real^N->complex e.
                f continuous_on s /\ &0 < e
                ==> ?g. P g /\ !x. x IN s ==> norm(f x - g x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!f. P f ==> P(\x:real^N. Cx(Re(f x)))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CX_RE_CNJ; SIMPLE_COMPLEX_ARITH
     `x / Cx(&2) = inv(Cx(&2)) * x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f. P f ==> P(\x:real^N. Cx(Im(f x)))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CX_IM_CNJ; SIMPLE_COMPLEX_ARITH
     `x - y = x + --Cx(&1) * y /\ x / Cx(&2) = inv(Cx(&2)) * x`] THEN
    REPEAT STRIP_TAC THEN REPEAT(FIRST_ASSUM MATCH_MP_TAC ORELSE CONJ_TAC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. x IN {Re o f | P (f:real^N->complex)}`; `s:real^N->bool`]
        STONE_WEIERSTRASS_ALT) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[EXISTS_IN_GSPEC; IMP_IMP; GSYM CONJ_ASSOC] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `c:real` THEN EXISTS_TAC `\x:real^N. Cx(c)` THEN
      ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; RE_CX];
      MAP_EVERY X_GEN_TAC [`f:real^N->complex`; `g:real^N->complex`] THEN
      DISCH_TAC THEN EXISTS_TAC `(\x. f x + g x):real^N->complex` THEN
      ASM_SIMP_TAC[o_THM; RE_ADD; FUN_EQ_THM];
      MAP_EVERY X_GEN_TAC [`f:real^N->complex`; `g:real^N->complex`] THEN
      STRIP_TAC THEN
      EXISTS_TAC `\x:real^N. Cx(Re(f x)) * Cx(Re(g x))` THEN
      ASM_SIMP_TAC[FUN_EQ_THM; RE_CX; o_THM; RE_MUL_CX];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL  [`x:real^N`; `y:real^N`]) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `f:real^N->complex` THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_EQ] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THENL
       [EXISTS_TAC `\x:real^N. Re(f x)` THEN ASM_REWRITE_TAC[o_DEF] THEN
        CONJ_TAC THENL
         [ALL_TAC; EXISTS_TAC `f:real^N->complex` THEN ASM_REWRITE_TAC[]];
        EXISTS_TAC `\x:real^N. Im(f x)` THEN ASM_REWRITE_TAC[o_DEF] THEN
        CONJ_TAC THENL
         [ALL_TAC;
          EXISTS_TAC `\x:real^N. Cx(Im(f x))` THEN ASM_SIMP_TAC[RE_CX]]] THEN
      X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN REWRITE_TAC[GSYM o_DEF] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHIN_COMPOSE THEN
      SIMP_TAC[REAL_CONTINUOUS_COMPLEX_COMPONENTS_AT;
               REAL_CONTINUOUS_AT_WITHIN] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]];
    DISCH_THEN(LABEL_TAC "*") THEN X_GEN_TAC `f:real^N->complex` THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "*"
     (fun th -> MP_TAC(ISPEC `Re o (f:real^N->complex)` th) THEN
                MP_TAC(ISPEC `Im o (f:real^N->complex)` th)) THEN
    MATCH_MP_TAC(TAUT `(p1 /\ p2) /\ (q1 /\ q2 ==> r)
                       ==> (p1 ==> q1) ==> (p2 ==> q2) ==> r`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHIN_COMPOSE THEN
      SIMP_TAC[REAL_CONTINUOUS_COMPLEX_COMPONENTS_AT;
               REAL_CONTINUOUS_AT_WITHIN] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN];
      ALL_TAC] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; o_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `g:real^N->complex` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `h:real^N->complex` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `\x:real^N. Cx(Re(h x)) + ii * Cx(Re(g x))` THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [COMPLEX_EXPAND] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x1 - x2) < e / &2 /\ norm(y1 - y2) < e / &2
      ==> norm((x1 + y1) - (x2 + y2)) < e`) THEN
    ASM_SIMP_TAC[GSYM CX_SUB; COMPLEX_NORM_CX; GSYM COMPLEX_SUB_LDISTRIB;
                 COMPLEX_NORM_MUL; COMPLEX_NORM_II; REAL_MUL_LID]]);;

let COMPLEX_STONE_WEIERSTRASS = prove
 (`!P s. compact s /\
         (!f. P f ==> f continuous_on s) /\
         (!c. P (\x. c)) /\
         (!f. P f ==> P(\x. cnj(f x))) /\
         (!f g. P f /\ P g ==> P (\x. f x + g x)) /\
         (!f g. P f /\ P g ==> P (\x. f x * g x)) /\
         (!x y. x IN s /\ y IN s /\ ~(x = y) ==> ?f. P f /\ ~(f x = f y))
         ==> !f:real^N->complex e.
                f continuous_on s /\ &0 < e
                ==> ?g. P g /\ !x. x IN s ==> norm(f x - g x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC COMPLEX_STONE_WEIERSTRASS_ALT THEN ASM_SIMP_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Stone-Weierstrass for R^n -> R polynomials.                               *)
(* ------------------------------------------------------------------------- *)

let real_polynomial_function_RULES,
    real_polynomial_function_INDUCT,
    real_polynomial_function_CASES = new_inductive_definition
 `(!i. 1 <= i /\ i <= dimindex(:N)
       ==> real_polynomial_function(\x:real^N. x$i)) /\
  (!c. real_polynomial_function(\x:real^N. c)) /\
  (!f g. real_polynomial_function f /\ real_polynomial_function g
         ==> real_polynomial_function(\x:real^N. f x + g x)) /\
  (!f g. real_polynomial_function f /\ real_polynomial_function g
         ==> real_polynomial_function(\x:real^N. f x * g x))`;;

let REAL_CONTINUOUS_REAL_POLYMONIAL_FUNCTION = prove
 (`!f x:real^N.
        real_polynomial_function f ==> f real_continuous at x`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC real_polynomial_function_INDUCT THEN
  SIMP_TAC[REAL_CONTINUOUS_ADD; REAL_CONTINUOUS_MUL;
           REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_AT_COMPONENT]);;

let STONE_WEIERSTRASS_REAL_POLYNOMIAL_FUNCTION = prove
 (`!f:real^N->real s e.
        compact s /\
        (!x. x IN s ==> f real_continuous at x within s) /\
        &0 < e
        ==> ?g. real_polynomial_function g /\
                !x. x IN s ==> abs(f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
        STONE_WEIERSTRASS) THEN
  ASM_REWRITE_TAC[real_polynomial_function_RULES] THEN
  SIMP_TAC[REAL_CONTINUOUS_REAL_POLYMONIAL_FUNCTION;
           REAL_CONTINUOUS_AT_WITHIN] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CART_EQ] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x$i` THEN
  ASM_SIMP_TAC[real_polynomial_function_RULES]);;

(* ------------------------------------------------------------------------- *)
(*  Stone-Weierstrass for real^M->real^N polynomials.                        *)
(* ------------------------------------------------------------------------- *)

let vector_polynomial_function = new_definition
 `vector_polynomial_function (f:real^M->real^N) <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> real_polynomial_function(\x. f(x)$i)`;;

let REAL_POLYNOMIAL_FUNCTION_DROP = prove
 (`!f. real_polynomial_function(drop o f) <=> vector_polynomial_function f`,
  REWRITE_TAC[vector_polynomial_function; DIMINDEX_1; FORALL_1] THEN
  REWRITE_TAC[o_DEF; drop]);;

let VECTOR_POLYNOMIAL_FUNCTION_LIFT = prove
 (`!f. vector_polynomial_function(lift o f) <=> real_polynomial_function f`,
  REWRITE_TAC[GSYM REAL_POLYNOMIAL_FUNCTION_DROP; o_DEF; LIFT_DROP; ETA_AX]);;

let VECTOR_POLYNOMIAL_FUNCTION_CONST = prove
 (`!c. vector_polynomial_function(\x. c)`,
  SIMP_TAC[vector_polynomial_function; real_polynomial_function_RULES]);;

let VECTOR_POLYNOMIAL_FUNCTION_ID = prove
 (`vector_polynomial_function(\x. x)`,
  SIMP_TAC[vector_polynomial_function; real_polynomial_function_RULES]);;

let VECTOR_POLYNOMIAL_FUNCTION_COMPONENT = prove
 (`!f:real^M->real^N i.
        1 <= i /\ i <= dimindex(:N) /\ vector_polynomial_function f
        ==> vector_polynomial_function(\x. lift(f x$i))`,
  SIMP_TAC[vector_polynomial_function; FORALL_1; DIMINDEX_1; GSYM drop;
           LIFT_DROP]);;

let VECTOR_POLYNOMIAL_FUNCTION_ADD = prove
 (`!f g:real^M->real^N.
        vector_polynomial_function f /\ vector_polynomial_function g
        ==> vector_polynomial_function (\x. f x + g x)`,

  REWRITE_TAC[vector_polynomial_function] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; real_polynomial_function_RULES]);;

let VECTOR_POLYNOMIAL_FUNCTION_MUL = prove
 (`!f g:real^M->real^N.
        vector_polynomial_function(lift o f) /\ vector_polynomial_function g
        ==> vector_polynomial_function (\x. f x % g x)`,
  REWRITE_TAC[vector_polynomial_function; o_DEF; VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[FORALL_1; DIMINDEX_1; GSYM drop; LIFT_DROP; ETA_AX] THEN
  SIMP_TAC[real_polynomial_function_RULES]);;

let VECTOR_POLYNOMIAL_FUNCTION_CMUL = prove
 (`!f:real^M->real^N c.
        vector_polynomial_function f
        ==> vector_polynomial_function (\x. c % f x)`,
  SIMP_TAC[VECTOR_POLYNOMIAL_FUNCTION_CONST; VECTOR_POLYNOMIAL_FUNCTION_MUL;
           ETA_AX; o_DEF]);;

let VECTOR_POLYNOMIAL_FUNCTION_NEG = prove
 (`!f:real^M->real^N.
        vector_polynomial_function f
        ==> vector_polynomial_function (\x. --(f x))`,
  REWRITE_TAC[VECTOR_ARITH `--x:real^N = --(&1) % x`] THEN
  REWRITE_TAC[VECTOR_POLYNOMIAL_FUNCTION_CMUL]);;

let VECTOR_POLYNOMIAL_FUNCTION_SUB = prove
 (`!f g:real^M->real^N.
        vector_polynomial_function f /\ vector_polynomial_function g
        ==> vector_polynomial_function (\x. f x - g x)`,
  SIMP_TAC[VECTOR_SUB; VECTOR_POLYNOMIAL_FUNCTION_ADD;
           VECTOR_POLYNOMIAL_FUNCTION_NEG]);;

let VECTOR_POLYNOMIAL_FUNCTION_VSUM = prove
 (`!f:real^M->A->real^N s.
        FINITE s /\ (!i. i IN s ==> vector_polynomial_function (\x. f x i))
        ==> vector_polynomial_function (\x. vsum s (f x))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; FORALL_IN_INSERT; VECTOR_POLYNOMIAL_FUNCTION_CONST;
           VECTOR_POLYNOMIAL_FUNCTION_ADD]);;

let REAL_VECTOR_POLYNOMIAL_FUNCTION_o = prove
 (`!f:real^M->real^N g.
        vector_polynomial_function f /\ real_polynomial_function g
        ==> real_polynomial_function(g o f)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC real_polynomial_function_INDUCT THEN
  REWRITE_TAC[o_DEF; real_polynomial_function_RULES] THEN
  ASM_REWRITE_TAC[GSYM vector_polynomial_function]);;

let VECTOR_POLYNOMIAL_FUNCTION_o = prove
 (`!f:real^M->real^N g:real^N->real^P.
        vector_polynomial_function f /\ vector_polynomial_function g
        ==> vector_polynomial_function(g o f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    REAL_VECTOR_POLYNOMIAL_FUNCTION_o)) THEN
  SIMP_TAC[vector_polynomial_function; o_DEF]);;

let REAL_POLYNOMIAL_FUNCTION_1 = prove
 (`!f. real_polynomial_function f <=>
       ?a n. f = \x. sum(0..n) (\i. a i * drop x pow i)`,
  REWRITE_TAC[TAUT `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC real_polynomial_function_INDUCT THEN
    REWRITE_TAC[DIMINDEX_1; FORALL_1; FUN_EQ_THM] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`\i. if i = 1 then &1 else &0`; `1`] THEN
      SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH_EQ; REAL_MUL_LZERO; drop] THEN
      SIMP_TAC[ARITH; SUM_SING_NUMSEG] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `c:real` THEN
      MAP_EVERY EXISTS_TAC [`(\i. c):num->real`; `0`] THEN
      REWRITE_TAC[SUM_SING_NUMSEG; real_pow] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`f:real^1->real`; `g:real^1->real`] THEN
    REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:num->real`; `m:num`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`b:num->real`; `n:num`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [MAP_EVERY EXISTS_TAC
       [`\i:num. (if i <= m then a i else &0) + (if i <= n then b i else &0)`;
        `MAX m n`] THEN
      GEN_TAC THEN REWRITE_TAC[REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG] THEN
      REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
      REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN BINOP_TAC THEN
      BINOP_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
      REWRITE_TAC[GSYM SUM_RMUL] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
      SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
      EXISTS_TAC `\k. sum {x | x IN {i,j | i IN 0..m /\ j IN 0..n} /\
                               FST x + SND x = k}
                          (\(i,j). a i * b j)` THEN
      EXISTS_TAC `m + n:num` THEN X_GEN_TAC `x:real^1` THEN
      MP_TAC(ISPECL
       [`\(i:num,j). i + j`;
        `\(i,j). (a i * drop x pow i) * (b j * drop x pow j)`;
        `{i,j | i IN 0..m /\ j IN 0..n}`; `0..m+n`] SUM_GROUP) THEN
      SIMP_TAC[FINITE_PRODUCT; FINITE_NUMSEG; FORALL_IN_IMAGE;
               FORALL_IN_GSPEC; SUBSET; IN_NUMSEG; LE_0; LE_ADD2] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
      MATCH_MP_TAC(MESON[SUM_EQ] `s = t /\ (!x. x IN t ==> f x = g x)
                                  ==> sum s f = sum t g`) THEN
      SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC; IMP_CONJ] THEN
      SIMP_TAC[IN_ELIM_PAIR_THM; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM VECTOR_POLYNOMIAL_FUNCTION_LIFT] THEN
    SIMP_TAC[LIFT_SUM; o_DEF; FINITE_NUMSEG; FORALL_1; DIMINDEX_1] THEN
    MATCH_MP_TAC VECTOR_POLYNOMIAL_FUNCTION_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; LIFT_CMUL] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC VECTOR_POLYNOMIAL_FUNCTION_MUL THEN
    REWRITE_TAC[GSYM REAL_POLYNOMIAL_FUNCTION_DROP; o_DEF; LIFT_DROP] THEN
    REWRITE_TAC[real_polynomial_function_RULES] THEN
    SPEC_TAC(`i:num`,`k:num`) THEN REWRITE_TAC[drop] THEN
    INDUCT_TAC THEN
    ASM_SIMP_TAC[real_polynomial_function_RULES; real_pow; DIMINDEX_1;
                 ARITH]]);;

let CONTINUOUS_VECTOR_POLYNOMIAL_FUNCTION = prove
 (`!f:real^M->real^N x.
        vector_polynomial_function f ==> f continuous at x`,
  REWRITE_TAC[vector_polynomial_function; CONTINUOUS_COMPONENTWISE] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_REAL_POLYMONIAL_FUNCTION THEN
  ASM_SIMP_TAC[]);;

let CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION = prove
 (`!f:real^M->real^N s.
        vector_polynomial_function f ==> f continuous_on s`,
  SIMP_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON;
           CONTINUOUS_VECTOR_POLYNOMIAL_FUNCTION]);;

let HAS_VECTOR_DERIVATIVE_VECTOR_POLYNOMIAL_FUNCTION = prove
 (`!p:real^1->real^N.
        vector_polynomial_function p
        ==> ?p'. vector_polynomial_function p' /\
                 !x. (p has_vector_derivative p'(x)) (at x)`,
  let lemma = prove
   (`!p:real^1->real.
          real_polynomial_function p
          ==> ?p'. real_polynomial_function p' /\
                 !x. ((p o lift) has_real_derivative (p'(lift x))) (atreal x)`,
    MATCH_MP_TAC
     (derive_strong_induction(real_polynomial_function_RULES,
                              real_polynomial_function_INDUCT)) THEN
    REWRITE_TAC[DIMINDEX_1; FORALL_1; o_DEF; GSYM drop; LIFT_DROP] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `\x:real^1. &1` THEN
      REWRITE_TAC[real_polynomial_function_RULES; HAS_REAL_DERIVATIVE_ID];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `c:real` THEN EXISTS_TAC `\x:real^1. &0` THEN
      REWRITE_TAC[real_polynomial_function_RULES; HAS_REAL_DERIVATIVE_CONST];
      ALL_TAC] THEN
    CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`f:real^1->real`; `g:real^1->real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `f':real^1->real` STRIP_ASSUME_TAC))
     (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `g':real^1->real` STRIP_ASSUME_TAC)))
    THENL
     [EXISTS_TAC `\x. (f':real^1->real) x + g' x`;
      EXISTS_TAC `\x. (f:real^1->real) x * g' x + f' x * g x`] THEN
    ASM_SIMP_TAC[real_polynomial_function_RULES; HAS_REAL_DERIVATIVE_ADD;
                 HAS_REAL_DERIVATIVE_MUL_ATREAL]) in
  GEN_TAC THEN REWRITE_TAC[vector_polynomial_function] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> ?q. real_polynomial_function q /\
                (!x. ((\x. lift(((p x):real^N)$i)) has_vector_derivative
                      lift(q x)) (at x))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; FORALL_DROP];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `q:num->real^1->real` THEN DISCH_TAC THEN
    EXISTS_TAC `(\x. lambda i. (q:num->real^1->real) i x):real^1->real^N` THEN
    ASM_SIMP_TAC[LAMBDA_BETA; ETA_AX] THEN
    REWRITE_TAC[has_vector_derivative; has_derivative_at] THEN
    ONCE_REWRITE_TAC[LIM_COMPONENTWISE] THEN X_GEN_TAC `x:real^1` THEN
    SIMP_TAC[LINEAR_VMUL_DROP; LINEAR_ID] THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
    REWRITE_TAC[has_vector_derivative; has_derivative_at] THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; VEC_COMPONENT; VECTOR_SUB_COMPONENT;
                 VECTOR_ADD_COMPONENT; LAMBDA_BETA; REAL_TENDSTO] THEN
    SIMP_TAC[DROP_ADD; DROP_VEC; LIFT_DROP; DROP_CMUL; DROP_SUB; o_DEF]]);;

let STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION = prove
 (`!f:real^M->real^N s e.
        compact s /\ f continuous_on s /\ &0 < e
        ==> ?g. vector_polynomial_function g /\
                !x. x IN s ==> norm(f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
   [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
  REWRITE_TAC[CONTINUOUS_COMPONENTWISE] THEN
  REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> ?g. real_polynomial_function g /\
                !x. x IN s ==> abs((f:real^M->real^N) x$i - g x) <
                               e / &(dimindex(:N))`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC STONE_WEIERSTRASS_REAL_POLYNOMIAL_FUNCTION THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; DIMINDEX_GE_1; LE_1];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g:num->real^M->real` THEN DISCH_TAC THEN
    EXISTS_TAC `(\x. lambda i. g i x):real^M->real^N` THEN
    ASM_SIMP_TAC[vector_polynomial_function; LAMBDA_BETA; ETA_AX] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LET_TRANS) THEN
    MATCH_MP_TAC SUM_BOUND_LT_GEN THEN
    REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; NUMSEG_EMPTY; NOT_LT] THEN
    ASM_SIMP_TAC[IN_NUMSEG; DIMINDEX_GE_1; LAMBDA_BETA;
                 VECTOR_SUB_COMPONENT]]);;

let STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION_SUBSPACE = prove
 (`!f:real^M->real^N s e t.
        compact s /\ f continuous_on s /\ &0 < e /\
        subspace t /\ IMAGE f s SUBSET t
        ==> ?g. vector_polynomial_function g /\ IMAGE g s SUBSET t /\
                !x. x IN s ==> norm(f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHONORMAL_BASIS_SUBSPACE) THEN
  DISCH_THEN(X_CHOOSE_THEN `bas:real^N->bool` MP_TAC) THEN
  ASM_CASES_TAC `FINITE(bas:real^N->bool)` THENL
   [ALL_TAC; ASM_MESON_TAC[HAS_SIZE]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `n = CARD(bas:real^N->bool)` THEN
  REWRITE_TAC[INJECTIVE_ON_ALT; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `b:num->real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ASM_SIMP_TAC[REWRITE_RULE[INJECTIVE_ON_ALT] HAS_SIZE_IMAGE_INJ_EQ] THEN
  REWRITE_TAC[HAS_SIZE; FINITE_NUMSEG; CARD_NUMSEG_1] THEN
  ASM_CASES_TAC `dim(t:real^N->bool) = n` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `t:real^N->bool` DIM_SUBSET_UNIV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MP_TAC(ISPECL
   [`(\x. lambda i. (f x:real^N) dot (b i)):real^M->real^N`;
    `s:real^M->bool`; `e:real`]
   STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
    SIMP_TAC[LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `(\x. vsum(1..n) (\i. (g x:real^N)$i % b i)):real^M->real^N` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC VECTOR_POLYNOMIAL_FUNCTION_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_POLYNOMIAL_FUNCTION_MUL THEN
    REWRITE_TAC[VECTOR_POLYNOMIAL_FUNCTION_CONST; o_DEF] THEN
    MATCH_MP_TAC VECTOR_POLYNOMIAL_FUNCTION_COMPONENT THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSPACE_VSUM THEN
    ASM_SIMP_TAC[SUBSPACE_MUL; FINITE_NUMSEG];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS) THEN
    SUBGOAL_THEN
     `vsum(IMAGE b (1..n)) (\v. (v dot f x) % v) = (f:real^M->real^N) x`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th])
    THENL
     [MATCH_MP_TAC ORTHONORMAL_BASIS_EXPAND THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM SET_TAC[];
      ASM_SIMP_TAC[REWRITE_RULE[INJECTIVE_ON_ALT] VSUM_IMAGE;
                   FINITE_NUMSEG] THEN
      REWRITE_TAC[GSYM VSUM_SUB_NUMSEG; o_DEF; GSYM VECTOR_SUB_RDISTRIB] THEN
      REWRITE_TAC[NORM_LE; GSYM NORM_POW_2] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) NORM_VSUM_PYTHAGOREAN o
        lhand o snd) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[PAIRWISE_IMAGE]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
      ASM_SIMP_TAC[pairwise; ORTHOGONAL_MUL; FINITE_NUMSEG] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NORM_MUL] THEN
      REWRITE_TAC[NORM_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [dot] THEN
      SIMP_TAC[GSYM REAL_POW_2; VECTOR_SUB_COMPONENT; LAMBDA_BETA] THEN
      MATCH_MP_TAC SUM_LE_INCLUDED THEN EXISTS_TAC `\n:num. n` THEN
      REWRITE_TAC[FINITE_NUMSEG; REAL_LE_POW_2] THEN
      ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
      REWRITE_TAC[UNWIND_THM2] THEN
      ONCE_REWRITE_TAC[TAUT `p ==> q /\ r <=> p ==> q /\ (q ==> r)`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
      ASM_SIMP_TAC[LAMBDA_BETA; UNWIND_THM2; IN_NUMSEG] THEN
      REWRITE_TAC[REAL_MUL_RID; REAL_POW2_ABS; REAL_LE_REFL] THEN
      ASM_ARITH_TAC]]);;

let STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION_AFFINE = prove
 (`!f:real^M->real^N s e t.
        compact s /\ f continuous_on s /\ &0 < e /\
        affine t /\ IMAGE f s SUBSET t
        ==> ?g. vector_polynomial_function g /\ IMAGE g s SUBSET t /\
                !x. x IN s ==> norm(f x - g x) < e`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SUBSET_EMPTY; IMAGE_EQ_EMPTY] THENL
   [MESON_TAC[VECTOR_POLYNOMIAL_FUNCTION_CONST; NOT_IN_EMPTY];
    STRIP_TAC] THEN
  MP_TAC(ISPEC `t:real^N->bool` AFFINE_TRANSLATION_SUBSPACE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `u:real^N->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL
   [`(\x. f x - a):real^M->real^N`; `s:real^M->bool`; `e:real`;
   `u:real^N->bool`] STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION_SUBSPACE) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST] THEN
  FIRST_ASSUM(MP_TAC o ISPEC `\x:real^N. x - a` o MATCH_MP IMAGE_SUBSET) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ADD_SUB; IMAGE_ID] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(\x. g x + a):real^M->real^N` THEN
  ASM_SIMP_TAC[VECTOR_POLYNOMIAL_FUNCTION_ADD;
               VECTOR_POLYNOMIAL_FUNCTION_CONST;
               VECTOR_ARITH `a - (b + c):real^N = a - c - b`] THEN
  FIRST_ASSUM(MP_TAC o ISPEC `\x:real^N. a + x` o MATCH_MP IMAGE_SUBSET) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ADD_AC]);;

(* ------------------------------------------------------------------------- *)
(* One application is to pick a smooth approximation to a path, or just pick *)
(* a smooth path anyway in an open connected set.                            *)
(* ------------------------------------------------------------------------- *)

let PATH_VECTOR_POLYNOMIAL_FUNCTION = prove
 (`!g:real^1->real^N. vector_polynomial_function g ==> path g`,
  SIMP_TAC[path; CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION]);;

let PATH_APPROX_VECTOR_POLYNOMIAL_FUNCTION = prove
 (`!g:real^1->real^N e.
        path g /\ &0 < e
        ==> ?p. vector_polynomial_function p /\
                pathstart p = pathstart g /\
                pathfinish p = pathfinish g /\
                !t. t IN interval[vec 0,vec 1] ==> norm(p t - g t) < e`,
  REWRITE_TAC[path] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^1->real^N`; `interval[vec 0:real^1,vec 1]`; `e / &4`]
        STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL; REAL_ARITH `&0 < x / &4 <=> &0 < x`] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\t. (q:real^1->real^N)(t) + (g(vec 0:real^1) - q(vec 0)) +
                drop t % ((g(vec 1) - q(vec 1)) - (g(vec 0) - q(vec 0)))` THEN
  REWRITE_TAC[pathstart; pathfinish; DROP_VEC] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[vector_polynomial_function; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[vector_polynomial_function]) THEN
    MATCH_MP_TAC(el 2 (CONJUNCTS real_polynomial_function_RULES)) THEN
    ASM_SIMP_TAC[real_polynomial_function_RULES; drop; DIMINDEX_1; ARITH];
    VECTOR_ARITH_TAC;
    VECTOR_ARITH_TAC;
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x - a) < e / &4 /\ norm b < e / &4 /\ norm c <= &1 * e / &4 /\
        norm d <= &1 * e / &4
      ==> norm((a + b + c - d) - x:real^N) < e`) THEN
    ASM_SIMP_TAC[NORM_MUL; IN_INTERVAL_1; DROP_VEC; REAL_POS] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; IN_INTERVAL_1; DROP_VEC; REAL_POS;
                 REAL_LE_REFL; NORM_POS_LE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_REAL_ARITH_TAC]);;

let CONNECTED_OPEN_VECTOR_POLYNOMIAL_CONNECTED = prove
 (`!s:real^N->bool.
        open s /\ connected s
        ==> !x y. x IN s /\ y IN s
                  ==> ?g. vector_polynomial_function g /\
                          path_image g SUBSET s /\
                          pathstart g = x /\
                          pathfinish g = y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `path_connected(s:real^N->bool)` MP_TAC THENL
   [ASM_SIMP_TAC[CONNECTED_OPEN_PATH_CONNECTED];
    REWRITE_TAC[path_connected]] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?e. &0 < e /\ !x. x IN path_image p ==> ball(x:real^N,e) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `s = (:real^N)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THENL
     [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
    EXISTS_TAC `setdist(path_image p,(:real^N) DIFF s)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
      ASM_SIMP_TAC[SETDIST_POS_LE; SETDIST_EQ_0_COMPACT_CLOSED;
                   COMPACT_PATH_IMAGE; GSYM OPEN_CLOSED] THEN
      ASM_SIMP_TAC[PATH_IMAGE_NONEMPTY] THEN ASM SET_TAC[];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[SUBSET] THEN
      X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_BALL; GSYM REAL_NOT_LE] THEN
      MATCH_MP_TAC(SET_RULE
       `(w IN (UNIV DIFF s) ==> p) ==> (~p ==> w IN s)`) THEN
      ASM_SIMP_TAC[SETDIST_LE_DIST]];
    MP_TAC(ISPECL [`p:real^1->real^N`; `e:real`]
      PATH_APPROX_VECTOR_POLYNOMIAL_FUNCTION) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `q:real^1->real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[path_image; FORALL_IN_IMAGE; SUBSET] THEN RULE_ASSUM_TAC
     (REWRITE_RULE[SUBSET; path_image; FORALL_IN_IMAGE;IN_BALL; dist]) THEN
    ASM_MESON_TAC[NORM_SUB]]);;

(* ------------------------------------------------------------------------- *)
(* Lipschitz property for real and vector polynomials.                       *)
(* ------------------------------------------------------------------------- *)

let LIPSCHITZ_REAL_POLYNOMIAL_FUNCTION = prove
 (`!f:real^N->real s.
        real_polynomial_function f /\ bounded s
        ==> ?B. &0 < B /\
                !x y. x IN s /\ y IN s ==> abs(f x - f y) <= B * norm(x - y)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  ASM_CASES_TAC `bounded(s:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  MATCH_MP_TAC real_polynomial_function_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    ASM_SIMP_TAC[REAL_MUL_LID; GSYM VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM];
    GEN_TAC THEN EXISTS_TAC `&1` THEN
    SIMP_TAC[REAL_LT_01; REAL_SUB_REFL; REAL_ABS_NUM; REAL_MUL_LID;
             NORM_POS_LE];
    ALL_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real`; `g:real^N->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC))
  THENL
   [EXISTS_TAC `B1 + B2:real` THEN ASM_SIMP_TAC[REAL_LT_ADD] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `abs(f - f') <= B1 * n /\ abs(g - g') <= B2 * n
      ==> abs((f + g) - (f' + g')) <= (B1 + B2) * n`) THEN
    ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B1 * (abs(g(a:real^N)) + B2 * &2 * B) +
                B2 * (abs(f a) + B1 * &2 * B)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
       `&0 < x ==> &0 < abs a + x`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
       `abs((f - f') * g) <= a * n /\ abs((g - g') * f') <= b * n
        ==> abs(f * g - f' * g') <= (a + b) * n`) THEN
      ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = (a * c) * b`] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC(REAL_ARITH
       `abs(g x - g a) <= C * norm(x - a) /\
        C * norm(x - a:real^N) <= C * B ==> abs(g x) <= abs(g a) + C * B`) THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN MATCH_MP_TAC(NORM_ARITH
       `norm x <= B /\ norm a <= B ==> norm(x - a:real^N) <= &2 * B`) THEN
      ASM_SIMP_TAC[]]]);;

let LIPSCHITZ_VECTOR_POLYNOMIAL_FUNCTION = prove
 (`!f:real^M->real^N s.
        vector_polynomial_function f /\ bounded s
        ==> ?B. &0 < B /\
                !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y)`,
  REWRITE_TAC[vector_polynomial_function] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?b. !i. 1 <= i /\ i <= dimindex(:N)
            ==> &0 < (b:real^N)$i /\
                !x y. x IN s /\ y IN s
                      ==> abs((f:real^M->real^N) x$i - f y$i) <=
                          b$i * norm(x - y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LAMBDA_SKOLEM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LIPSCHITZ_REAL_POLYNOMIAL_FUNCTION THEN
    ASM_SIMP_TAC[LIPSCHITZ_REAL_POLYNOMIAL_FUNCTION];
    EXISTS_TAC `&1 + sum(1..dimindex(:N)) (\i. (b:real^N)$i)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REPEAT STRIP_TAC THEN
      W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM SUM_RMUL; REAL_MUL_LID] THEN
      MATCH_MP_TAC(NORM_ARITH `x <= y ==> x <= norm(a:real^N) + y`) THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN
      ASM_SIMP_TAC[VECTOR_SUB_COMPONENT]]]);;

(* ------------------------------------------------------------------------- *)
(* Differentiability of real and vector polynomial functions.                *)
(* ------------------------------------------------------------------------- *)

let DIFFERENTIABLE_REAL_POLYNOMIAL_FUNCTION_AT = prove
 (`!f:real^N->real a.
        real_polynomial_function f ==> (lift o f) differentiable (at a)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC real_polynomial_function_INDUCT THEN
  REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_CMUL] THEN
  REWRITE_TAC[DIFFERENTIABLE_LIFT_COMPONENT; DIFFERENTIABLE_CONST] THEN
  SIMP_TAC[DIFFERENTIABLE_ADD] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DIFFERENTIABLE_MUL_AT THEN
  ASM_REWRITE_TAC[o_DEF]);;

let DIFFERENTIABLE_ON_REAL_POLYNOMIAL_FUNCTION = prove
 (`!f:real^N->real s.
        real_polynomial_function f ==> (lift o f) differentiable_on s`,
  SIMP_TAC[DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON;
           DIFFERENTIABLE_REAL_POLYNOMIAL_FUNCTION_AT]);;

let DIFFERENTIABLE_VECTOR_POLYNOMIAL_FUNCTION = prove
 (`!f:real^M->real^N a.
        vector_polynomial_function f ==> f differentiable (at a)`,
  REWRITE_TAC[vector_polynomial_function] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[DIFFERENTIABLE_COMPONENTWISE_AT] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC DIFFERENTIABLE_REAL_POLYNOMIAL_FUNCTION_AT THEN
  ASM_SIMP_TAC[]);;

let DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION = prove
 (`!f:real^M->real^N s.
        vector_polynomial_function f ==> f differentiable_on s`,
  SIMP_TAC[DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON;
           DIFFERENTIABLE_VECTOR_POLYNOMIAL_FUNCTION]);;

(* ------------------------------------------------------------------------- *)
(* Non-trivial algebraic variety has empty interior.                         *)
(* ------------------------------------------------------------------------- *)

let NOWHERE_DENSE_ALGEBRAIC_VARIETY = prove
 (`!f c. real_polynomial_function f /\ ~(!x. f x = c)
         ==> interior {x:real^N | f(x) = c} = {}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?a n. !t. f(x + t % (y - x):real^N) - c = sum(0..n) (\i. a i * t pow i)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_DROP;
                GSYM(REWRITE_RULE[FUN_EQ_THM] REAL_POLYNOMIAL_FUNCTION_1)] THEN
    REWRITE_TAC[real_sub] THEN
    MATCH_MP_TAC(el 2 (CONJUNCTS real_polynomial_function_RULES)) THEN
    REWRITE_TAC[real_polynomial_function_RULES] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_VECTOR_POLYNOMIAL_FUNCTION_o THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC VECTOR_POLYNOMIAL_FUNCTION_ADD THEN
    REWRITE_TAC[VECTOR_POLYNOMIAL_FUNCTION_CONST] THEN
    MATCH_MP_TAC VECTOR_POLYNOMIAL_FUNCTION_MUL THEN
    SIMP_TAC[o_DEF; LIFT_DROP; VECTOR_POLYNOMIAL_FUNCTION_SUB;
             VECTOR_POLYNOMIAL_FUNCTION_ID; VECTOR_POLYNOMIAL_FUNCTION_CONST];
    FIRST_X_ASSUM(MP_TAC o GEN `t:real` o SPEC
     `x + t % (y - x):real^N` o GEN_REWRITE_RULE I [SUBSET]) THEN
    ASM_REWRITE_TAC[IN_BALL; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
    ASM_REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
    SIMP_TAC[SET_RULE `(!x. P x ==> Q x) <=> {x | P x} SUBSET {x | Q x}`] THEN
    MATCH_MP_TAC(MESON[FINITE_SUBSET; INFINITE]
     `FINITE t /\ INFINITE s ==> ~(s SUBSET t)`) THEN
    REWRITE_TAC[REAL_POLYFUN_FINITE_ROOTS] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      SIMP_TAC[NOT_EXISTS_THM; TAUT `~(p /\ ~q) <=> p ==> q`] THEN
      DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[REAL_MUL_LZERO; SUM_0] THEN
      ASM_REWRITE_TAC[REAL_SUB_0; VECTOR_ARITH `x + &1 % (y - x):real^N = y`];
      ASM_CASES_TAC `y:real^N = x` THENL
       [ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_SUB_REFL; NORM_0] THEN
        REWRITE_TAC[UNIV_GSPEC; real_INFINITE];
        ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LT_RDIV_EQ; NORM_POS_LT;
                     VECTOR_SUB_EQ; GSYM NORM_LIFT] THEN
        MATCH_MP_TAC INFINITE_SUPERSET THEN EXISTS_TAC
         `IMAGE drop (ball(vec 0:real^1,e / norm(y - x:real^N)))` THEN
        CONJ_TAC THENL
         [MP_TAC(ISPEC `drop` INFINITE_IMAGE_INJ) THEN
          SIMP_TAC[DROP_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
          REWRITE_TAC[INFINITE; FINITE_BALL; REAL_NOT_LE] THEN
          ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0;
                      IN_ELIM_THM; LIFT_DROP]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Bernoulli polynomials, defined recursively. We don't explicitly introduce *)
(* a definition for Bernoulli numbers, but use "bernoulli n (&0)" for that.  *)
(* ------------------------------------------------------------------------- *)

let bernoulli = define
 `(!x. bernoulli 0 x = &1) /\
  (!n x. bernoulli (n + 1) x =
          x pow (n + 1) -
          sum(0..n) (\k. &(binom(n+2,k)) * bernoulli k x) / (&n + &2))`;;

let BERNOULLI_CONV =
  let btm = `bernoulli` in
  let rec bernoullis n =
    if n < 0 then [] else
    if n = 0 then [CONJUNCT1 bernoulli] else
    let ths = bernoullis (n - 1) in
    let th1 = SPEC(mk_small_numeral (n - 1)) (CONJUNCT2 bernoulli) in
    let th2 =
      CONV_RULE(BINDER_CONV (COMB2_CONV (RAND_CONV(LAND_CONV NUM_ADD_CONV))
       (RAND_CONV(LAND_CONV EXPAND_SUM_CONV) THENC
        NUM_REDUCE_CONV THENC
        ONCE_DEPTH_CONV NUM_BINOM_CONV THENC
        REWRITE_CONV ths THENC
        REAL_POLY_CONV))) th1 in
    th2::ths in
  fun tm -> match tm with
             Comb(Comb(b,n),x) when b = btm ->
                let th = hd(bernoullis(dest_small_numeral n)) in
                (REWR_CONV th THENC REAL_POLY_CONV) tm
           | _ -> failwith "BERNOULLI_CONV";;

let BERNOULLI,BERNOULLI_EXPANSION = (CONJ_PAIR o prove)
 (`(!n x. sum(0..n) (\k. &(binom(n,k)) * bernoulli k x) - bernoulli n x =
          &n * x pow (n - 1)) /\
   (!n x. bernoulli n x =
          sum(0..n) (\k. &(binom(n,k)) * bernoulli k (&0) * x pow (n - k)))`,
  let lemma = prove
   (`(!n x. sum (0..n) (\k. &(binom(n,k)) * B k x) - B n x =
            &n * x pow (n - 1)) <=>
     (!x. B 0 x = &1) /\
     (!n x. B (n + 1) x =
            x pow (n + 1) -
            sum(0..n) (\k. &(binom(n+2,k)) * B k x) / (&n + &2))`,
    let cth = MESON[num_CASES] `(!n. P n) <=> P 0 /\ (!n. P(SUC n))` in
    GEN_REWRITE_TAC LAND_CONV [cth] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [cth] THEN
    SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0; BINOM_REFL; BINOM_PENULT; SUC_SUB1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO; REAL_SUB_REFL] THEN
    SIMP_TAC[ADD1; ARITH_RULE `(n + 1) + 1 = n + 2`; GSYM REAL_OF_NUM_ADD] THEN
    BINOP_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
    CONV_TAC REAL_FIELD) in
  REWRITE_TAC[lemma; bernoulli] THEN
  SUBGOAL_THEN
   `!n x. sum(0..n) (\k. &(binom(n,k)) *
                         sum (0..k)
                             (\l. &(binom(k,l)) *
                                  bernoulli l (&0) * x pow (k - l))) -
   sum(0..n) (\k. &(binom(n,k)) * bernoulli k (&0) * x pow (n - k)) =
   &n * x pow (n - 1)`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN MP_TAC(ISPECL
     [`\n. bernoulli n (&0)`; `n:num`; `x:real`; `&1`] APPELL_SEQUENCE) THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x + &1 = &1 + x`] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM APPELL_SEQUENCE] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID; GSYM SUM_SUB_NUMSEG] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM lemma] bernoulli] THEN
    REWRITE_TAC[REAL_POW_ZERO; COND_RAND; COND_RATOR] THEN
    REWRITE_TAC[ARITH_RULE `i - 1 = 0 <=> i = 0 \/ i = 1`] THEN
    REWRITE_TAC[MESON[]
     `(if p \/ q then x else y) = if q then x else if p then x else y`] THEN
    SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; COND_ID; SUM_DELTA] THEN
    REWRITE_TAC[IN_NUMSEG; LE_0; BINOM_1] THEN
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    ASM_SIMP_TAC[LE_1] THEN REAL_ARITH_TAC;
    REWRITE_TAC[lemma] THEN STRIP_TAC THEN
     MATCH_MP_TAC num_WF THEN MATCH_MP_TAC num_INDUCTION THEN
    ASM_SIMP_TAC[ADD1; bernoulli;
           ARITH_RULE `m < n + 1 <=> m <= n`]]);;

let BERNOULLI_ALT = prove
 (`!n x. sum(0..n) (\k. &(binom(n+1,k)) * bernoulli k x) =
         (&n + &1) * x pow n`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`SUC n`; `x:real`] BERNOULLI) THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; SUC_SUB1; BINOM_REFL] THEN
  REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let BERNOULLI_ADD = prove
 (`!n x y. bernoulli n (x + y) =
           sum(0..n) (\k. &(binom(n,k)) * bernoulli k x * y pow (n - k))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[BERNOULLI_EXPANSION] THEN
  REWRITE_TAC[APPELL_SEQUENCE]);;

let bernoulli_number = prove
 (`bernoulli 0 (&0) = &1 /\
  (!n. bernoulli (n + 1) (&0) =
       --sum(0..n) (\k. &(binom(n+2,k)) * bernoulli k (&0)) / (&n + &2))`,
  REWRITE_TAC[bernoulli; REAL_POW_ADD] THEN REAL_ARITH_TAC);;

let BERNOULLI_NUMBER = prove
 (`!n. sum (0..n) (\k. &(binom (n,k)) * bernoulli k (&0)) - bernoulli n (&0) =
       if n = 1 then &1 else &0`,
  REWRITE_TAC[BERNOULLI] THEN
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[ARITH; REAL_MUL_LZERO] THEN
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[SUC_SUB1] THEN
  REWRITE_TAC[ARITH_RULE `SUC n = 1 <=> n = 0`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
  REWRITE_TAC[NOT_SUC; REAL_MUL_LZERO; REAL_MUL_RZERO]);;

let BERNOULLI_NUMBER_ALT = prove
 (`!n. sum(0..n) (\k. &(binom(n+1,k)) * bernoulli k (&0)) =
       if n = 0 then &1 else &0`,
  REWRITE_TAC[BERNOULLI_ALT] THEN INDUCT_TAC THEN
  REWRITE_TAC[real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO; NOT_SUC] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_MUL_RID]);;

let BERNOULLI_SUB_ADD1 = prove
 (`!n x. bernoulli n (x + &1) - bernoulli n x = &n * x pow (n - 1)`,
  REWRITE_TAC[BERNOULLI_ADD; REAL_POW_ONE; REAL_MUL_RID] THEN
  REWRITE_TAC[BERNOULLI]);;

let BERNOULLI_1 = prove
 (`!n. bernoulli n (&1) =
       if n = 1 then bernoulli n (&0) + &1 else bernoulli n (&0)`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_ADD_LID] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x = y + &1 <=> x - y = &1`];
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0]] THEN
  REWRITE_TAC[BERNOULLI_SUB_ADD1; REAL_POW_ZERO] THEN
  ASM_REWRITE_TAC[SUB_REFL; REAL_MUL_RID] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SUM_OF_POWERS = prove
 (`!m n. sum(0..n) (\k. &k pow m) =
         (bernoulli (m + 1) (&n + &1) - bernoulli (m + 1) (&0)) / (&m + &1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINDER_CONV o RAND_CONV)
   [GSYM SUC_SUB1] THEN
  REWRITE_TAC[REAL_FIELD `x = y / (&m + &1) <=> (&m + &1) * x = y`] THEN
  REWRITE_TAC[GSYM SUM_LMUL; REAL_OF_NUM_SUC; GSYM BERNOULLI_SUB_ADD1] THEN
  REWRITE_TAC[ADD1; SUM_DIFFS_ALT; LE_0]);;

let HAS_REAL_DERIVATIVE_BERNOULLI = prove
 (`!n x. ((bernoulli n) has_real_derivative (&n * bernoulli (n - 1) x))
         (atreal x)`,
  INDUCT_TAC THEN GEN_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  ONCE_REWRITE_TAC[BERNOULLI_EXPANSION] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; SUB_REFL; CONJUNCT1 real_pow] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_MUL_LZERO; LE_0] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; SUC_SUB1; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REAL_DIFF_TAC THEN
  REWRITE_TAC[ADD1; BINOM_TOP_STEP_REAL] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUB; ARITH_RULE
   `k <= n ==> ~(k = n + 1) /\ (n + 1) - k - 1 = n - k /\ k <= n + 1`] THEN
  UNDISCH_TAC `k:num <= n` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  CONV_TAC REAL_FIELD);;

add_real_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
  (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN_UNIV
   (SPEC `n:num` HAS_REAL_DERIVATIVE_BERNOULLI))));;

let REAL_DIFFERENTIABLE_ON_BERNOULLI = prove
 (`!n s. (bernoulli n) real_differentiable_on s`,
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE; real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_BERNOULLI;
            HAS_REAL_DERIVATIVE_ATREAL_WITHIN]);;

let REAL_CONTINUOUS_ON_BERNOULLI = prove
 (`!n s. (bernoulli n) real_continuous_on s`,
  MESON_TAC[REAL_DIFFERENTIABLE_ON_BERNOULLI;
            REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON]);;

let HAS_REAL_INTEGRAL_BERNOULLI = prove
 (`!n. ((bernoulli n) has_real_integral (if n = 0 then &1 else &0))
       (real_interval[&0,&1])`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL
   [`\x. bernoulli (n + 1) x / (&n + &1)`; `bernoulli n`; `&0`; `&1`]
        REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[REAL_POS] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
    REWRITE_TAC[ADD_SUB; GSYM REAL_OF_NUM_ADD] THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[BERNOULLI_1; ARITH_RULE `n + 1 = 1 <=> n = 0`] THEN
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
    REWRITE_TAC[REAL_ADD_LID; ADD_CLAUSES; REAL_DIV_1; REAL_ADD_SUB]]);;

let POLYNOMIAL_FUNCTION_BERNOULLI = prove
 (`!n. polynomial_function(bernoulli n)`,
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
  ONCE_REWRITE_TAC[BERNOULLI_EXPANSION] THEN
  MATCH_MP_TAC POLYNOMIAL_FUNCTION_SUM THEN
  SIMP_TAC[FINITE_NUMSEG; POLYNOMIAL_FUNCTION_MUL; POLYNOMIAL_FUNCTION_POW;
           POLYNOMIAL_FUNCTION_ID; POLYNOMIAL_FUNCTION_CONST]);;

let BERNOULLI_UNIQUE = prove
 (`!p n. polynomial_function p /\
         (!x. p(x + &1) - p(x) = &n * x pow (n - 1)) /\
         (real_integral (real_interval[&0,&1]) p = if n = 0 then &1 else &0)
         ==> p = bernoulli n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  MP_TAC(SPECL [`\x. p x - bernoulli n x`; `p(&0) - bernoulli n (&0)`]
   POLYNOMIAL_FUNCTION_FINITE_ROOTS) THEN
  ASM_SIMP_TAC[POLYNOMIAL_FUNCTION_SUB;
               POLYNOMIAL_FUNCTION_BERNOULLI; ETA_AX] THEN
  MATCH_MP_TAC(TAUT `~p /\ (q ==> r) ==> (p <=> ~q) ==> r`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM INFINITE] THEN
    MATCH_MP_TAC INFINITE_SUPERSET THEN
    EXISTS_TAC `IMAGE (&) (:num)` THEN
    SIMP_TAC[INFINITE_IMAGE_INJ; REAL_OF_NUM_EQ; num_INFINITE;
             SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    CONV_TAC(BINDER_CONV SYM_CONV) THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    ASM_MESON_TAC[BERNOULLI_SUB_ADD1; REAL_ARITH
     `p - b:real = p' - b' <=> p' - p = b' - b`];
    DISCH_TAC THEN X_GEN_TAC `x:real` THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_UNIQUE THEN
    EXISTS_TAC `\x. p x - bernoulli n x` THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `x = x * (&1 - &0)`] THEN
      ONCE_ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN REWRITE_TAC[REAL_POS];
      GEN_REWRITE_TAC LAND_CONV
       [GSYM(SPEC `if n = 0 then &1 else &0` REAL_SUB_REFL)] THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN
      REWRITE_TAC[ETA_AX; HAS_REAL_INTEGRAL_BERNOULLI] THEN
      ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_ON_POLYNOMIAL_FUNCTION]]]);;

let BERNOULLI_RAABE_2 = prove
 (`!n x. bernoulli n ((x + &1) / &2) + bernoulli n (x / &2) =
         &2 / &2 pow n * bernoulli n x`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[bernoulli] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[REAL_LT_POW2; REAL_FIELD
   `&0 < p ==> (x = &2 / p * y <=> p / &2 * x = y)`] THEN
  GEN_REWRITE_TAC I [GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[ETA_AX] THEN  MATCH_MP_TAC BERNOULLI_UNIQUE THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC POLYNOMIAL_FUNCTION_LMUL THEN
    MATCH_MP_TAC POLYNOMIAL_FUNCTION_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] POLYNOMIAL_FUNCTION_o) THEN
    REWRITE_TAC[POLYNOMIAL_FUNCTION_BERNOULLI; real_div] THEN
    SIMP_TAC[POLYNOMIAL_FUNCTION_ADD; POLYNOMIAL_FUNCTION_CONST;
             POLYNOMIAL_FUNCTION_ID; POLYNOMIAL_FUNCTION_RMUL];
    REWRITE_TAC[REAL_ARITH `((x + &1) + &1) / &2 = x / &2 + &1`] THEN
    REWRITE_TAC[REAL_ARITH `a * (x + y) - a * (y + z):real = a * (x - z)`] THEN
    REWRITE_TAC[BERNOULLI_SUB_ADD1; REAL_POW_DIV] THEN GEN_TAC THEN
    REWRITE_TAC[REAL_ARITH `a / b * c * d / e:real = c * (a / b / e) * d`] THEN
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_MP_TAC(REAL_RING `b = &1 ==> a * b * c = a * c`) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`] THEN
    REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_DIV_REFL THEN
    REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN
     `(bernoulli n) real_integrable_on real_interval[&0,&1 / &2] /\
      (bernoulli n) real_integrable_on real_interval[&1 / &2,&1]`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      SIMP_TAC[REAL_CONTINUOUS_ON_POLYNOMIAL_FUNCTION;
               POLYNOMIAL_FUNCTION_BERNOULLI];
      DISCH_THEN(CONJUNCTS_THEN(MP_TAC o
       MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_AFFINITY) o
       MATCH_MP REAL_INTEGRABLE_INTEGRAL))] THEN
    REWRITE_TAC[REAL_ARITH `m * (x - c):real = m * x + m * --c`] THEN
    REWRITE_TAC[IMAGE_AFFINITY_REAL_INTERVAL; IMP_IMP] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC o SPECL [`inv(&2)`; `inv(&2)`])
     (MP_TAC o SPECL [`inv(&2)`; `&0`])) THEN
    REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_ADD) THEN
    DISCH_THEN(MP_TAC o SPEC `&2 pow n / &2` o
        MATCH_MP HAS_REAL_INTEGRAL_LMUL) THEN
    REWRITE_TAC[REAL_ARITH `&1 / &2 * x + &1 / &2 = (x + &1) / &2`;
                REAL_ARITH `&1 / &2 * x + &0 = x / &2`] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
    REWRITE_TAC[REAL_ARITH `&2 * x + &2 * y = &0 <=> y + x = &0`] THEN
    IMP_REWRITE_TAC[REAL_INTEGRAL_COMBINE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    ASM_MESON_TAC[HAS_REAL_INTEGRAL_BERNOULLI]]);;

let BERNOULLI_HALF = prove
 (`!n. bernoulli n (&1 / &2) = (&2 / &2 pow n - &1) * bernoulli n (&0)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `&1`] BERNOULLI_RAABE_2) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ARITH `a + b:real = c * a <=> b = (c - &1) * a`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[BERNOULLI_1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let BERNOULLI_REFLECT = prove
 (`!n x. bernoulli n (&1 - x) = --(&1) pow n * bernoulli n x`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  SUBGOAL_THEN
   `!n. sum(0..n) (\k. &(binom(n + 1,k)) *
                       (bernoulli k (&1 - x) - --(&1) pow k * bernoulli k x)) =
        &0`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUM_SUB_NUMSEG; REAL_SUB_LDISTRIB] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[REAL_SUB_0; BERNOULLI_ALT] THEN
    TRANS_TAC EQ_TRANS
     `--(&1) pow n * (bernoulli (n + 1) x - bernoulli (n + 1) (x - &1))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`n + 1`; `x - &1`] BERNOULLI_SUB_ADD1) THEN
      REWRITE_TAC[REAL_ARITH `x - a + a:real = x`] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ADD_SUB; REAL_ARITH `&1 - x = --(&1) * (x - &1)`] THEN
      REWRITE_TAC[REAL_POW_MUL; REAL_MUL_AC; GSYM REAL_OF_NUM_ADD];
      MATCH_MP_TAC(REAL_FIELD
       `z pow 2 = &1 /\ z * x = y ==> z * y = x`) THEN
      REWRITE_TAC[REAL_POW_POW] THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_NEG; EVEN_MULT; ARITH; REAL_POW_ONE];
        REWRITE_TAC[GSYM SUM_LMUL]] THEN
      MP_TAC(ISPECL [`SUC n`; `x:real`; `--(&1)`] BERNOULLI_ADD) THEN
      REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; BINOM_REFL; SUB_REFL] THEN
      REWRITE_TAC[GSYM real_sub; ADD1; REAL_MUL_LID; CONJUNCT1 real_pow] THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `--s' = s ==> s = b - (s' + b * &1)`) THEN
      REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_RING
       `--(&1) pow 1 * p = q * r ==> --(b * k * p) = q * b * r * k`) THEN
      REWRITE_TAC[GSYM REAL_POW_ADD] THEN REWRITE_TAC[REAL_POW_NEG] THEN
      REWRITE_TAC[EVEN_ADD; EVEN_SUB; REAL_POW_ONE; ARITH] THEN
      ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(n + 1 <= k)`] THEN
      REWRITE_TAC[TAUT `~(~p <=> q) <=> (p <=> q)`]];
    MATCH_MP_TAC num_WF THEN MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC[bernoulli; CONJUNCT1 real_pow; REAL_MUL_LID] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[LT_SUC_LE] THEN DISCH_THEN
     (fun th -> FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN ASSUME_TAC th) THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0; REAL_ADD_LID] THEN
    REWRITE_TAC[GSYM ADD1; BINOM_PENULT; GSYM REAL_OF_NUM_SUC] THEN
    REWRITE_TAC[REAL_ENTIRE; REAL_SUB_0] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let BERNOULLI_1_0 = prove
 (`!n. bernoulli n (&1) = --(&1) pow n * bernoulli n (&0)`,
  GEN_TAC THEN SUBST1_TAC(REAL_ARITH `&0 = &1 - &1`) THEN
  REWRITE_TAC[BERNOULLI_REFLECT; REAL_MUL_ASSOC; GSYM REAL_POW_MUL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID]);;

let BERNOULLI_NUMBER_ZERO = prove
 (`!n. ODD n /\ ~(n = 1) ==> bernoulli n (&0) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` BERNOULLI_1) THEN
  MP_TAC(SPEC `n:num` BERNOULLI_1_0) THEN
  ASM_REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE; GSYM NOT_ODD] THEN
  REAL_ARITH_TAC);;

let BERNOULLI_EVEN_BOUND = prove
 (`!n x. EVEN n /\ x IN real_interval[&0,&1]
         ==> abs(bernoulli n x) <= abs(bernoulli n (&0))`,
  let lemma = prove
   (`(!n x. x IN real_interval(&0,&1 / &2)
            ==> ~(bernoulli (2 * n + 1) x = &0)) /\
     (!n x y. x IN real_interval(&0,&1 / &2) /\
              y IN real_interval(&0,&1 / &2) /\
              bernoulli (2 * n) x = &0 /\ bernoulli (2 * n) y = &0
              ==> x = y)`,
    REWRITE_TAC[AND_FORALL_THM; IN_REAL_INTERVAL] THEN INDUCT_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV BERNOULLI_CONV) THEN REAL_ARITH_TAC;
      POP_ASSUM MP_TAC THEN REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
    MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_WLOG_LT THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [REWRITE_TAC[CONJ_ACI; EQ_SYM_EQ]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL
       [`\x. bernoulli (2 * SUC n) x / (&2 * &n + &2)`;
        `bernoulli (2 * n + 1)`; `x:real`; `y:real`]
          REAL_ROLLE_SIMPLE) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUC;
                    ARITH_RULE `2 * SUC n - 1 = 2 * n + 1`] THEN
        CONV_TAC REAL_FIELD;
        REWRITE_TAC[IN_REAL_INTERVAL; LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC `z:real` THEN
        DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
        ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC];
      POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
      X_GEN_TAC `x:real` THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL
       [`\x. bernoulli (2 * SUC n + 1) x / (&2 * &n + &3)`;
        `bernoulli (2 * SUC n)`; `&0`; `x:real`]
          REAL_ROLLE_SIMPLE) THEN
      ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ENTIRE] THEN DISJ1_TAC THEN
        MATCH_MP_TAC BERNOULLI_NUMBER_ZERO THEN
        REWRITE_TAC[ODD_ADD; ODD_MULT; ADD1; ARITH] THEN ARITH_TAC;
        REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
        SIMP_TAC[ADD_SUB; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD; ADD1] THEN
        CONV_TAC REAL_FIELD;
        REWRITE_TAC[IN_REAL_INTERVAL; NOT_EXISTS_THM] THEN
        X_GEN_TAC `u:real` THEN STRIP_TAC] THEN
      MP_TAC(ISPECL
       [`\x. bernoulli (2 * SUC n + 1) x / (&2 * &n + &3)`;
        `bernoulli (2 * SUC n)`; `x:real`; `&1 / &2`]
          REAL_ROLLE_SIMPLE) THEN
      ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN CONV_TAC SYM_CONV THEN
        REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[BERNOULLI_HALF] THEN
        REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
        MATCH_MP_TAC BERNOULLI_NUMBER_ZERO THEN
        REWRITE_TAC[ODD_ADD; ODD_MULT; ADD1; ARITH] THEN ARITH_TAC;
        REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
        SIMP_TAC[ADD_SUB; GSYM REAL_OF_NUM_MUL;
                 GSYM REAL_OF_NUM_ADD; ADD1] THEN
        CONV_TAC REAL_FIELD;
        REWRITE_TAC[IN_REAL_INTERVAL; NOT_EXISTS_THM] THEN
        X_GEN_TAC `v:real` THEN STRIP_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:real`; `v:real`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]) in
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[bernoulli; REAL_LE_REFL] THEN
  MP_TAC(ISPECL [`\x. abs(bernoulli n x)`; `real_interval[&0,&1]`]
        REAL_CONTINUOUS_ATTAINS_SUP) THEN
  REWRITE_TAC[REAL_COMPACT_INTERVAL; REAL_INTERVAL_NE_EMPTY; REAL_POS] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_ABS THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
    REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real` MP_TAC)] THEN
  ASM_CASES_TAC `z = &0` THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `z = &1` THEN ASM_REWRITE_TAC[BERNOULLI_1_0] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NEG; REAL_POW_ONE;
               REAL_ABS_NUM; REAL_MUL_LID] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`bernoulli n`; `&n * bernoulli (n - 1) z`;
                 `z:real`; `real_interval(&0,&1)`]
        REAL_DERIVATIVE_ZERO_MAXMIN) THEN
  REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_BERNOULLI] THEN
    ASM_CASES_TAC `&0 <= bernoulli n z` THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ENTIRE; REAL_OF_NUM_EQ] THEN DISCH_TAC THEN
  ASM_CASES_TAC `z = &1 / &2` THENL
   [MATCH_MP_TAC(REAL_ARITH `!z. x <= z /\ z <= &1 * y ==> x <= y`) THEN
    EXISTS_TAC `abs(bernoulli n (&1 / &2))` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[BERNOULLI_HALF; REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &1 ==> abs(x - &1) <= &1`) THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&2 pow 1 <= x ==> &2 <= x`) THEN
    MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < z /\ z < &1 / &2 \/ &1 / &2 < z /\ z < &1`
  STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`(n - 2) DIV 2`; `z:real`] (CONJUNCT1 lemma)) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    MP_TAC(ISPECL [`(n - 2) DIV 2`; `&1 - z`] (CONJUNCT1 lemma)) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[BERNOULLI_REFLECT]] THEN
    REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  SUBGOAL_THEN `2 * (n - 2) DIV 2 + 1 = n - 1`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
  DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
  UNDISCH_TAC `~(2 * m = 0)` THEN SPEC_TAC(`m:num`,`m:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_SUB2] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ARITH_TAC);;

let BERNOULLI_NUMBER_EQ_0 = prove
 (`!n. bernoulli n (&0) = &0 <=> ODD n /\ ~(n = 1)`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[BERNOULLI_NUMBER_ZERO] THEN
  ASM_CASES_TAC `n = 1` THEN
  ASM_REWRITE_TAC[BERNOULLI_CONV `bernoulli 1 (&0)`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`n:num`; `\k. &(binom(n,n - k)) * bernoulli (n - k) (&0)`]
        REAL_POLYFUN_FINITE_ROOTS) THEN
  MATCH_MP_TAC(TAUT `q /\ ~p ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [EXISTS_TAC `n:num` THEN SIMP_TAC[IN_NUMSEG; LE_0; LE_REFL; SUB_REFL] THEN
    REWRITE_TAC[binom; REAL_MUL_RID; bernoulli] THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM INFINITE] THEN MATCH_MP_TAC INFINITE_SUPERSET THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN
    REWRITE_TAC[real_interval; INFINITE; FINITE_REAL_INTERVAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`n:num`; `x:real`] BERNOULLI_EVEN_BOUND) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL;
      REAL_ARITH `abs x <= abs(&0) <=> x = &0`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EQ_TRANS) THEN
    GEN_REWRITE_TAC RAND_CONV [BERNOULLI_EXPANSION] THEN
    MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
    REPEAT(EXISTS_TAC `\k:num. n - k`) THEN
    SIMP_TAC[IN_NUMSEG; ARITH_RULE `k:num <= n ==> n - (n - k) = k`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* This is a simple though sub-optimal bound (we can actually get            *)
(* |B_{2n+1}(x)| <= (2n + 1) / (2 pi) * |B_{2n}(0)| with more work).         *)
(* ------------------------------------------------------------------------- *)

let BERNOULLI_BOUND = prove
 (`!n x. x IN real_interval[&0,&1]
         ==> abs(bernoulli n x)
             <= max (&n / &2) (&1) * abs(bernoulli (2 * n DIV 2) (&0))`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]);
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS])] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THENL
   [REWRITE_TAC[ARITH_RULE `(2 * m) DIV 2 = m`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&1 * y <= max x (&1) * y /\ a <= y ==> a <= max x (&1) * y`) THEN
    SIMP_TAC[REAL_LE_RMUL; REAL_ABS_POS; REAL_ARITH `y <= max x y`] THEN
    MATCH_MP_TAC BERNOULLI_EVEN_BOUND THEN ASM_REWRITE_TAC[EVEN_MULT; ARITH];
    POP_ASSUM MP_TAC THEN SPEC_TAC(`x:real`,`x:real`) THEN
    MATCH_MP_TAC(MESON[]
     `!Q. ((!x. P x /\ Q x ==> R x) ==> (!x. P x ==> R x)) /\
          (!x. P x /\ Q x ==> R x)
          ==> !x. P x ==> R x`) THEN
    EXISTS_TAC `\x. x IN real_interval[&0,&1 / &2]` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `x <= &1 / &2` THEN ASM_SIMP_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPEC `&1 - x`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[BERNOULLI_REFLECT; REAL_ABS_MUL; REAL_ABS_POW] THEN
      REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_MUL_LID; REAL_POW_ONE];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[ARITH_RULE `SUC(2 * m) DIV 2 = m`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[ADD1; REAL_ARITH `(x + &1) + &1 = x + &2`] THEN
      ASM_CASES_TAC `m = 0` THENL
       [ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
        CONV_TAC(ONCE_DEPTH_CONV BERNOULLI_CONV) THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`\x. bernoulli (2 * m + 1) x / &(2 * m + 1)`;
                       `bernoulli (2 * m)`; `&0`; `x:real`]
          REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
        ASM_SIMP_TAC[BERNOULLI_NUMBER_ZERO; ODD_ADD; ODD_MULT; ARITH;
                     ARITH_RULE `2 * m + 1 = 1 <=> m = 0`] THEN
        ANTS_TAC THENL
         [REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN REWRITE_TAC[ADD_SUB] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
          CONV_TAC REAL_FIELD;
          DISCH_THEN(MP_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
          REWRITE_TAC[REAL_FIELD
           `i = b / (&2 * &m + &1) - &0 / (&2 * &m + &1) <=>
            b = (&2 * &m + &1) * i`] THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[real_max; REAL_ARITH `(x + &1) / &2 <= &1 <=> x <= &1`;
                      REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
          ASM_REWRITE_TAC[ARITH_RULE `2 * m <= 1 <=> m = 0`] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_MUL; real_div; GSYM REAL_MUL_ASSOC] THEN
          REWRITE_TAC[REAL_ABS_MUL; REAL_ARITH
           `abs(&2 * &n + &1) = &2 * &n + &1`] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN
          CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          TRANS_TAC REAL_LE_TRANS
            `real_integral (real_interval [&0,x])
                           (\x. abs(bernoulli (2 * m) (&0)))` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
            SIMP_TAC[REAL_INTEGRABLE_CONST; REAL_INTEGRABLE_CONTINUOUS;
                     REAL_CONTINUOUS_ON_BERNOULLI] THEN
            REPEAT STRIP_TAC THEN MATCH_MP_TAC BERNOULLI_EVEN_BOUND THEN
            REWRITE_TAC[EVEN_MULT; ARITH; IN_REAL_INTERVAL] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
            ASM_REAL_ARITH_TAC;
            ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN
            REWRITE_TAC[REAL_ARITH `a * (x - &0) = x * a`] THEN
            MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
            ASM_REAL_ARITH_TAC]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Absolutely integrable functions remain so modified by Bernolli sawtooth.  *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_INTEGRABLE_ON_MUL_BERNOULLI_FRAC = prove
 (`!f:real^1->real^N s n.
        f absolutely_integrable_on s
        ==> (\x. bernoulli n (frac(drop x)) % f x)
            absolutely_integrable_on s`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  DISCH_TAC THEN MP_TAC(ISPECL
   [`\x y:real^N. drop(x) % y`;
    `\x:real^1. lift(bernoulli n (frac (drop x)))`;
    `\x. if x IN s then (f:real^1->real^N) x else vec 0`; `(:real^1)`]
   ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  ASM_REWRITE_TAC[LIFT_DROP; BILINEAR_DROP_MUL] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\x. lift(bernoulli n (frac (drop x)))) =
      (lift o bernoulli n o drop) o (lift o frac o drop)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS THEN CONJ_TAC THENL
     [MATCH_MP_TAC
        CONTINUOUS_AE_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `IMAGE lift integer` THEN
      SIMP_TAC[LEBESGUE_MEASURABLE_UNIV; NEGLIGIBLE_COUNTABLE;
               COUNTABLE_IMAGE; COUNTABLE_INTEGER] THEN
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_DIFF; IN_UNIV; LIFT_IN_IMAGE_LIFT] THEN
      REWRITE_TAC[IN] THEN
      REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_FRAC];
      MP_TAC(SPECL [`n:num`; `(:real)`] REAL_CONTINUOUS_ON_BERNOULLI) THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_UNIV]];
    REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_UNIV; NORM_LIFT] THEN
    SUBGOAL_THEN `real_compact (IMAGE (bernoulli n) (real_interval[&0,&1]))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_BERNOULLI; REAL_COMPACT_INTERVAL];
      DISCH_THEN(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      MESON_TAC[FLOOR_FRAC; REAL_LT_IMP_LE]]]);;

(* ------------------------------------------------------------------------- *)
(* The Euler-Maclaurin summation formula for real and complex functions.     *)
(* ------------------------------------------------------------------------- *)

let REAL_EULER_MACLAURIN = prove
 (`!f m n p.
    m <= n /\
    (!k x. k <= 2 * p + 1 /\ x IN real_interval[&m,&n]
           ==> ((f k) has_real_derivative f (k + 1) x)
               (atreal x within real_interval [&m,&n]))
    ==> (\x. bernoulli (2 * p + 1) (frac x) * f (2 * p + 1) x)
        real_integrable_on real_interval[&m,&n] /\
        sum(m..n) (\i. f 0 (&i)) =
        real_integral (real_interval [&m,&n]) (f 0) +
        (f 0 (&m) + f 0 (&n)) / &2 +
        sum (1..p) (\k. bernoulli (2 * k) (&0) / &(FACT(2 * k)) *
                        (f (2 * k - 1) (&n) - f (2 * k - 1) (&m))) +
        real_integral (real_interval [&m,&n])
                      (\x. bernoulli (2 * p + 1) (frac x) * f (2 * p + 1) x) /
        &(FACT(2 * p + 1))`,
  let lemma = prove
   (`!f k m n.
          f real_continuous_on real_interval[&m,&n] /\ m < n
          ==> ((\x. bernoulli k (frac x) * f x) has_real_integral
               sum(m..n-1) (\j. real_integral (real_interval[&j,&j + &1])
                                             (\x. bernoulli k (x - &j) * f x)))
              (real_interval[&m,&n])`,
    REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; LT_SUC_LE; SUC_SUB1] THEN STRIP_TAC THEN
    ASM_CASES_TAC `m:num = n` THENL
     [ASM_REWRITE_TAC[SUM_SING_NUMSEG] THEN (**** one ***) ALL_TAC;
      SUBGOAL_THEN `0 < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[SUM_CLAUSES_RIGHT] THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_COMBINE THEN EXISTS_TAC `&n` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_ARITH `x <= x + &1`] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LT_LE] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          REAL_CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_ARITH `x <= x + &1`; LE_REFL];
        ALL_TAC]] THEN
    MATCH_MP_TAC(MESON[REAL_INTEGRAL_SPIKE; HAS_REAL_INTEGRAL_INTEGRAL;
                       REAL_INTEGRABLE_SPIKE]
     `!t. g real_integrable_on s /\ real_negligible t /\
          (!x. x IN s DIFF t ==> f x = g x)
          ==>  (f has_real_integral (real_integral s g)) s`) THEN
    EXISTS_TAC `{&n + &1}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
       MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
        [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
         REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
         REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
         FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
           REAL_CONTINUOUS_ON_SUBSET)) THEN
         REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
         REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
       REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
       X_GEN_TAC `x:real` THEN STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
       AP_TERM_TAC THEN     REWRITE_TAC[GSYM FRAC_UNIQUE] THEN
       REWRITE_TAC[REAL_ARITH `x - (x - &n) = &n`; INTEGER_CLOSED] THEN
       ASM_REAL_ARITH_TAC])) in
  let step = prove
   (`!f f' k m n.
          m < n /\
          (!x. x IN real_interval[&m,&n]
               ==> (f has_real_derivative f' x)
                   (atreal x within real_interval[&m,&n])) /\
          f' real_continuous_on real_interval[&m,&n]
          ==> real_integral (real_interval[&m,&n])
                            (\x. bernoulli (k + 1) (frac x) * f' x) =
              (bernoulli (k + 1) (&0) * (f(&n) - f(&m)) +
               (if k = 0 then sum(m+1..n) (\i. f(&i)) else &0)) -
              (&k + &1) *
              real_integral (real_interval[&m,&n])
                            (\x. bernoulli k (frac x) * f x)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `f real_continuous_on real_interval[&m,&n]` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
                    real_differentiable;
                    REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON];
      ASM_SIMP_TAC[REWRITE_RULE[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL]
       lemma]] THEN
    TRANS_TAC EQ_TRANS
      `sum(m..n-1)
          (\j. (bernoulli (k + 1) (&0) * (f (&j + &1) - f (&j)) +
                (if k = 0 then f (&j + &1) else &0)) -
               (&k + &1) *
               real_integral (real_interval[&j,&j + &1])
                             (\x. bernoulli k (x - &j) * f x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
      MATCH_MP_TAC(ONCE_REWRITE_RULE[REAL_MUL_SYM]
        REAL_INTEGRATION_BY_PARTS_SIMPLE) THEN
      MAP_EVERY EXISTS_TAC
       [`f:real->real`; `\x. (&k + &1) * bernoulli k (x - &j)`] THEN
      REWRITE_TAC[REAL_ADD_SUB; REAL_SUB_REFL; BERNOULLI_1] THEN
      REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC;
        X_GEN_TAC `x:real` THEN DISCH_TAC THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
             `x IN s ==> s SUBSET t ==> x IN t`));
            MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
              HAS_REAL_DERIVATIVE_WITHIN_SUBSET)] THEN
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
          REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN ASM_ARITH_TAC;
          REAL_DIFF_TAC THEN  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; ADD_SUB] THEN
          REAL_ARITH_TAC];
        REWRITE_TAC[ARITH_RULE `k + 1 = 1 <=> k = 0`] THEN
        ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
         [REWRITE_TAC[REAL_ARITH
           `(b + &1) * f1 - b * f0 - ((b * (f1 - f0) + f1) - w):real = w`];
          REWRITE_TAC[REAL_ARITH
           `b * f1 - b * f0 - ((b * (f1 - f0) + &0) - w) = w`]] THEN
        REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
        MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
        MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
        (CONJ_TAC THENL
          [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
           REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
           REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
           FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
             REAL_CONTINUOUS_ON_SUBSET)) THEN
           REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
           REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN ASM_ARITH_TAC])];
      REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_SUB_NUMSEG] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN BINOP_TAC THENL
       [AP_TERM_TAC THEN REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; SUM_DIFFS_ALT] THEN
        COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        ASM_ARITH_TAC;
        ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[SUM_0] THEN
        REWRITE_TAC[GSYM(SPEC `1` SUM_OFFSET); REAL_OF_NUM_ADD] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `m:num <= n ==> m = n \/ m < n`))
  THENL
   [ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[SUM_SING_NUMSEG; REAL_SUB_REFL; REAL_MUL_LZERO] THEN
    SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL; REAL_ARITH `(x + x) / &2 = x`;
             REAL_MUL_RZERO; SUM_0; real_div; REAL_MUL_LZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_integrable_on] THEN
    MP_TAC(ISPECL [`f (2 * p + 1):real->real`; `2 * p + 1`; `m:num`; `n:num`]
        lemma) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
    REWRITE_TAC[real_differentiable] THEN ASM_MESON_TAC[LE_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_LEFT; LT_IMP_LE] THEN
  SUBGOAL_THEN
   `!k:num.  k <= 2 * p + 1
             ==> (f k) real_differentiable_on real_interval[&m,&n]`
  ASSUME_TAC THENL [ASM_MESON_TAC[real_differentiable_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:num->real->real) 0`; `(f:num->real->real) (0 + 1)`;
                 `0`; `m:num`; `n:num`] step) THEN
  ASM_SIMP_TAC[REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON;
               ARITH_RULE `0 + 1 <= 2 * p + 1`; LE_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CONJUNCT1 bernoulli] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_MUL_LID; ETA_AX] THEN
  REWRITE_TAC[BERNOULLI_CONV `bernoulli 1 (&0)`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `i' = r ==> i' = (-- &1 / &2 * (n - m) + s) - i
               ==> m + s = i + (m + n) / &2 + r`) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`p:num`,`p:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [ARITH_RULE `2 * SUC p + 1 = 2 * p + 3`] THEN
    FIRST_X_ASSUM(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[ARITH_RULE `k <= 2 * p + 1 ==> k <= 2 * p + 3`] THEN
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`(f:num->real->real) (2 * p + 1)`;
                 `(f:num->real->real) ((2 * p + 1) + 1)`;
                 `2 * p + 1`; `m:num`; `n:num`] step) THEN
  ASM_SIMP_TAC[REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON;
               ARITH_RULE `(2 * p + 1) + 1 <= 2 * p + 3`;
               ARITH_RULE `2 * p + 1 <= 2 * p + 3`] THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_ADD_RID] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_FIELD
   `x = y - ((&2 * &p + &1) + &1) * z <=> z = (y - x) / (&2 * &p + &2)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC p - 1 = 2 * p + 1`] THEN
  REWRITE_TAC[ARITH_RULE `(2 * p + 1) + 1 = 2 * SUC p`] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC p = SUC(2 * p + 1)`] THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * p + 1) + 1 = SUC(SUC(2 * p + 1))`] THEN
  REWRITE_TAC[FACT; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(t = &0) /\
    i2 = &0 - (&2 * &p + &3) * i1
    ==> (b * (fn - fm) - i1) / (&2 * &p + &2) / t =
        b / (((&2 * &p + &1) + &1) * t) * (fn - fm) +
        i2 / ((((&2 * &p + &1) + &1) + &1) * ((&2 * &p + &1) + &1) * t)`) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; FACT_NZ] THEN
  MP_TAC(ISPECL [`(f:num->real->real) (SUC(2 * p + 1))`;
                 `(f:num->real->real) (SUC(2 * p + 1) + 1)`;
                 `SUC(2 * p + 1)`; `m:num`; `n:num`] step) THEN
  ASM_SIMP_TAC[REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON; NOT_SUC;
               ARITH_RULE `SUC(2 * p + 1) + 1 <= 2 * p + 3`;
               ARITH_RULE `SUC(2 * p + 1) <= 2 * p + 3`] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC; REAL_OF_NUM_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_RID; GSYM REAL_OF_NUM_MUL] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
  REWRITE_TAC[BERNOULLI_NUMBER_EQ_0] THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN ARITH_TAC);;

let REAL_EULER_MACLAURIN_ANTIDERIVATIVE = prove
 (`!f m n p.
     m <= n /\
     (!k x. k <= 2 * p + 2 /\ x IN real_interval[&m,&n]
            ==> ((f k) has_real_derivative f (k + 1) x)
                (atreal x within real_interval [&m,&n]))
     ==> ((\x. bernoulli (2 * p + 1) (frac x) * f (2 * p + 2) x)
          real_integrable_on real_interval[&m,&n]) /\
         sum(m..n) (\i. f 1 (&i)) =
         (f 0 (&n) - f 0 (&m)) +
         (f 1 (&m) + f 1 (&n)) / &2 +
         sum (1..p) (\k. bernoulli (2 * k) (&0) / &(FACT(2 * k)) *
                         (f (2 * k) (&n) - f (2 * k) (&m))) +
         real_integral (real_interval [&m,&n])
                       (\x. bernoulli (2 * p + 1) (frac x) * f (2 * p + 2) x) /
         &(FACT(2 * p + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. (f:num->real->real)(SUC n)`; `m:num`; `n:num`; `p:num`]
        REAL_EULER_MACLAURIN) THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= 2 * p + 1 ==> SUC k <= 2 * p + 2`;
               ARITH_RULE `SUC(k + 1) = SUC k + 1`;
               ARITH_RULE `SUC(2 * p) + 1 = 2 * p + 2`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL
   [`f 0:real->real`; `f (0 + 1):real->real`; `&m`; `&n`]
        REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LE; LE_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * p) + 1 = 2 * p + 2`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[ARITH_RULE `1 <= k ==> SUC(2 * k - 1) = 2 * k`]);;

let COMPLEX_EULER_MACLAURIN_ANTIDERIVATIVE = prove
 (`!f m n p.
     m <= n /\
     (!k x. k <= 2 * p + 2 /\ &m <= x /\ x <= &n
            ==> ((f k) has_complex_derivative f (k + 1) (Cx x)) (at(Cx x)))
     ==> (\x. Cx(bernoulli (2 * p + 1) (frac(drop x))) *
                       f (2 * p + 2) (Cx(drop x)))
         integrable_on interval[lift(&m),lift(&n)] /\
         vsum(m..n) (\i. f 1 (Cx(&i))) =
         (f 0 (Cx(&n)) - f 0 (Cx(&m))) +
         (f 1 (Cx(&m)) + f 1 (Cx(&n))) / Cx(&2) +
         vsum (1..p) (\k. Cx(bernoulli (2 * k) (&0) / &(FACT(2 * k))) *
                          (f (2 * k) (Cx(&n)) - f (2 * k) (Cx(&m)))) +
         integral (interval[lift(&m),lift(&n)])
                  (\x. Cx(bernoulli (2 * p + 1) (frac(drop x))) *
                       f (2 * p + 2) (Cx(drop x))) /
         Cx(&(FACT(2 * p + 1)))`,
  let lemma_re,lemma_im = (CONJ_PAIR o prove)
   (`((f has_complex_derivative f') (at (Cx x))
      ==> ((Re o f o Cx) has_real_derivative (Re f')) (atreal x)) /\
     ((f has_complex_derivative f') (at (Cx x))
      ==> ((Im o f o Cx) has_real_derivative (Im f')) (atreal x))`,
    REPEAT GEN_TAC THEN CONJ_TAC THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_AT; HAS_REAL_DERIVATIVE_ATREAL] THEN
    REWRITE_TAC[LIM_AT; REALLIM_ATREAL; o_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `Cx y`) THEN
    ASM_REWRITE_TAC[DIST_CX; dist] THEN
    REWRITE_TAC[GSYM RE_SUB; GSYM IM_SUB; CX_SUB;
                GSYM RE_DIV_CX; GSYM IM_SUB; GSYM IM_DIV_CX] THEN
    MESON_TAC[COMPLEX_NORM_GE_RE_IM; REAL_LET_TRANS])
  and ilemma = prove
   (`f integrable_on interval[lift a,lift b]
     ==> Re(integral (interval[lift a,lift b]) f) =
         real_integral (real_interval[a,b]) (\x. Re(f(lift x))) /\
         Im(integral (interval[lift a,lift b]) f) =
         real_integral (real_interval[a,b]) (\x. Im(f(lift x)))`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[RE_DEF; IM_DEF] THEN
    ASM_SIMP_TAC[INTEGRAL_COMPONENT] THEN
    IMP_REWRITE_TAC[REAL_INTEGRAL] THEN
    REWRITE_TAC[o_DEF; IMAGE_LIFT_REAL_INTERVAL; LIFT_DROP] THEN
    REWRITE_TAC[REAL_INTEGRABLE_ON] THEN
    REWRITE_TAC[o_DEF; IMAGE_LIFT_REAL_INTERVAL; LIFT_DROP] THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[INTEGRABLE_COMPONENTWISE]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[DIMINDEX_2; ARITH]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[COMPLEX_EQ] THEN
  MAP_EVERY (MP_TAC o C SPEC REAL_EULER_MACLAURIN_ANTIDERIVATIVE)
   [`\n:num. (Im o f n o Cx)`; `\n:num. (Re o f n o Cx)`] THEN
  REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `n:num`; `p:num`]) THEN
  ASM_SIMP_TAC[lemma_re; lemma_im; HAS_REAL_DERIVATIVE_ATREAL_WITHIN;
               o_THM; IN_REAL_INTERVAL] THEN
  SIMP_TAC[RE_VSUM; IM_VSUM; FINITE_NUMSEG] THEN
  DISCH_THEN(CONJUNCTS_THEN(ASSUME_TAC o CONJUNCT1)) THEN
  SIMP_TAC[RE_DIV_CX; IM_DIV_CX; RE_VSUM; IM_VSUM; FINITE_NUMSEG; RE_ADD;
           RE_SUB;IM_ADD; IM_SUB; RE_MUL_CX; IM_MUL_CX; RE_CX; IM_CX] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[INTEGRABLE_COMPONENTWISE] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; GSYM RE_DEF; GSYM IM_DEF] THEN
    REWRITE_TAC[RE_MUL_CX; IM_MUL_CX] THEN
    ASM_REWRITE_TAC[REWRITE_RULE[o_DEF] (GSYM REAL_INTEGRABLE_ON);
                    GSYM IMAGE_LIFT_REAL_INTERVAL];
    SIMP_TAC[ilemma] THEN REWRITE_TAC[RE_MUL_CX; IM_MUL_CX; LIFT_DROP]]);;

(* ------------------------------------------------------------------------- *)
(* Specific properties of complex measurable functions.                      *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_COMPLEX_MUL = prove
 (`!f g:real^N->complex s.
         f measurable_on s /\ g measurable_on s
         ==> (\x. f x * g x) measurable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_COMBINE THEN
  ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
  CONJ_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

let MEASURABLE_ON_COMPLEX_INV = prove
 (`!f:real^N->real^2.
     f measurable_on (:real^N) /\ negligible {x | f x = Cx(&0)}
     ==> (\x. inv(f x)) measurable_on (:real^N)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[measurable_on; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `g:num->real^N->complex`] THEN
  STRIP_TAC THEN EXISTS_TAC `k UNION {x:real^N | f x = Cx(&0)}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_UNION] THEN
  SUBGOAL_THEN
   `!n. ?h. h continuous_on (:real^N) /\
            !x. x IN {x | g n x IN (:complex) DIFF ball(Cx(&0),inv(&n + &1))}
                ==> (h:real^N->complex) x = inv(g n x)`

  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC TIETZE_UNBOUNDED THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
      REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_BALL; ETA_AX] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
      REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
      MATCH_MP_TAC CONTINUOUS_COMPLEX_INV_AT THEN CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
        RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM; IN_UNIV; IN_DIFF]) THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_BALL]) THEN
        SIMP_TAC[CONTRAPOS_THM; DIST_REFL; REAL_LT_INV_EQ] THEN
        REAL_ARITH_TAC]];
    REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `h:num->real^N->complex` THEN
    REWRITE_TAC[FORALL_AND_THM; IN_ELIM_THM; IN_DIFF; IN_UNION; IN_UNIV] THEN
    REWRITE_TAC[IN_BALL; DE_MORGAN_THM; REAL_NOT_LT] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN MATCH_MP_TAC LIM_TRANSFORM THEN
    EXISTS_TAC `\n. inv((g:num->real^N->complex) n x)` THEN
    ASM_SIMP_TAC[o_DEF; LIM_COMPLEX_INV] THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    SUBGOAL_THEN `&0 < norm((f:real^N->complex) x)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `norm((f:real^N->complex) x) / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "*")) THEN
    MP_TAC(SPEC `norm((f:real^N->complex) x) / &2` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N1 + N2 + 1` THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; DIST_0] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NORM_ARITH
     `dist(g,f) < norm(f) / &2 ==> norm(f) / &2 <= norm g`)) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < y ==> z <= x ==> z <= y`)) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC]);;

let MEASURABLE_ON_COMPLEX_DIV = prove
 (`!f g:real^N->complex s.
        f measurable_on s /\ g measurable_on (:real^N) /\
        negligible {x | g(x) = Cx(&0)}
        ==> (\x. f(x) / g(x)) measurable_on s`,
  let lemma = prove
   (`!f g:real^N->complex.
        f measurable_on (:real^N) /\ g measurable_on (:real^N) /\
        negligible {x | g(x) = Cx(&0)}
        ==> (\x. f(x) / g(x)) measurable_on (:real^N)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[complex_div] THEN
    ASM_SIMP_TAC[MEASURABLE_ON_COMPLEX_MUL; MEASURABLE_ON_COMPLEX_INV]) in
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[IN_UNIV; ETA_AX] THEN DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; complex_div; COMPLEX_VEC_0] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_LZERO]);;

(* ------------------------------------------------------------------------- *)
(* Measurable real->real functions.                                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("real_measurable_on",(12,"right"));;

let real_measurable_on = new_definition
 `f real_measurable_on s <=>
        (lift o f o drop) measurable_on (IMAGE lift s)`;;

let real_lebesgue_measurable = new_definition
 `real_lebesgue_measurable s <=>
      (\x. if x IN s then &1 else &0) real_measurable_on (:real)`;;

let REAL_MEASURABLE_ON_UNIV = prove
 (`(\x.  if x IN s then f(x) else &0) real_measurable_on (:real) <=>
   f real_measurable_on s`,
  REWRITE_TAC[real_measurable_on; o_DEF; IMAGE_LIFT_UNIV] THEN
  SIMP_TAC[COND_RAND; LIFT_NUM; MEASURABLE_ON_UNIV; GSYM IN_IMAGE_LIFT_DROP]);;

let REAL_LEBESGUE_MEASURABLE = prove
 (`!s. real_lebesgue_measurable s <=> lebesgue_measurable (IMAGE lift s)`,
  REWRITE_TAC[real_lebesgue_measurable; lebesgue_measurable; COND_RAND;
    COND_RAND; real_measurable_on; indicator; IMAGE_LIFT_UNIV; o_DEF] THEN
  REWRITE_TAC[LIFT_NUM; IN_IMAGE_LIFT_DROP]);;

let REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f g s.
        f real_measurable_on s /\
        g real_integrable_on s /\
        (!x. x IN s ==> abs(f x) <= g x)
        ==> f real_integrable_on s`,
  REWRITE_TAC[real_measurable_on; REAL_INTEGRABLE_ON] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `lift o g o drop` THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP; NORM_LIFT]);;

let REAL_MEASURABLE_BOUNDED_AE_BY_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f g s k.
      f real_measurable_on s /\ g real_integrable_on s /\ real_negligible k /\
      (!x. x IN s DIFF k ==> abs(f x) <= g x)
      ==> f real_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC
   `\x. if x IN k then abs(f x) else (g:real->real) x` THEN
  ASM_SIMP_TAC[COND_RAND; IN_DIFF; LIFT_DROP; REAL_LE_REFL; COND_ID] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
  MAP_EVERY EXISTS_TAC [`g:real->real`; `k:real->bool`] THEN
  ASM_SIMP_TAC[IN_DIFF]);;

let REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE = prove
 (`!f g s.
        f real_measurable_on s /\
        g real_integrable_on s /\
        (!x. x IN s ==> abs(f x) <= g x)
        ==> f absolutely_real_integrable_on s`,
  REWRITE_TAC[real_measurable_on; REAL_INTEGRABLE_ON;
              ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `lift o g o drop` THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP; NORM_LIFT]);;

let INTEGRABLE_SUBINTERVALS_IMP_REAL_MEASURABLE = prove
 (`!f. (!a b. f real_integrable_on real_interval[a,b])
       ==> f real_measurable_on (:real)`,
  REWRITE_TAC[real_measurable_on; REAL_INTEGRABLE_ON; IMAGE_LIFT_UNIV] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_SUBINTERVALS_IMP_MEASURABLE THEN
  ASM_REWRITE_TAC[FORALL_LIFT]);;

let INTEGRABLE_IMP_REAL_MEASURABLE = prove
 (`!f:real->real s.
        f real_integrable_on s ==> f real_measurable_on s`,
  REWRITE_TAC[real_measurable_on; REAL_INTEGRABLE_ON] THEN
  REWRITE_TAC[INTEGRABLE_IMP_MEASURABLE]);;

let ABSOLUTELY_REAL_INTEGRABLE_REAL_MEASURABLE = prove
 (`!f s. f absolutely_real_integrable_on s <=>
         f real_measurable_on s /\ (\x. abs(f x)) real_integrable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[absolutely_real_integrable_on] THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (b /\ c ==> a) ==> (a /\ c <=> b /\ c)`) THEN
  REWRITE_TAC[INTEGRABLE_IMP_REAL_MEASURABLE] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. abs((f:real->real) x)` THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

let REAL_MEASURABLE_ON_COMPOSE_CONTINUOUS = prove
 (`!f g. f real_measurable_on (:real) /\ g real_continuous_on (:real)
         ==> (g o f) real_measurable_on (:real)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON; real_measurable_on] THEN
  REWRITE_TAC[IMAGE_LIFT_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_COMPOSE_CONTINUOUS) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let REAL_MEASURABLE_ON_COMPOSE_CONTINUOUS_0 = prove
 (`!f:real->real g:real->real s.
        f real_measurable_on s /\ g real_continuous_on (:real) /\ g(&0) = &0
        ==> (g o f) real_measurable_on s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_MEASURABLE_ON_UNIV] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`] THEN
  DISCH_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_MEASURABLE_ON_COMPOSE_CONTINUOUS) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_DEF] THEN ASM_MESON_TAC[]);;

let REAL_MEASURABLE_ON_COMPOSE_CONTINUOUS_OPEN_INTERVAL = prove
 (`!f:real->real g:real->real a b.
        f real_measurable_on (:real) /\
        (!x. f(x) IN real_interval(a,b)) /\
        g real_continuous_on real_interval(a,b)
        ==> (g o f) real_measurable_on (:real)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift o g o drop`; `lift a`; `lift b`]
        MEASURABLE_ON_COMPOSE_CONTINUOUS_OPEN_INTERVAL) THEN
  REWRITE_TAC[real_measurable_on; REAL_CONTINUOUS_ON] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; IMAGE_LIFT_UNIV; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM FORALL_DROP] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[INTERVAL_REAL_INTERVAL; LIFT_DROP] THEN ASM SET_TAC[]);;

let REAL_MEASURABLE_ON_COMPOSE_CONTINUOUS_CLOSED_SET = prove
 (`!f:real->real g:real->real s.
        real_closed s /\
        f real_measurable_on (:real) /\
        (!x. f(x) IN s) /\
        g real_continuous_on s
        ==> (g o f) real_measurable_on (:real)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift o g o drop`; `IMAGE lift s`]
        MEASURABLE_ON_COMPOSE_CONTINUOUS_CLOSED_SET) THEN
  REWRITE_TAC[real_measurable_on; REAL_CONTINUOUS_ON; REAL_CLOSED] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; IMAGE_LIFT_UNIV; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM FORALL_DROP] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[INTERVAL_REAL_INTERVAL; LIFT_DROP] THEN ASM SET_TAC[]);;

let REAL_MEASURABLE_ON_COMPOSE_CONTINUOUS_CLOSED_SET_0 = prove
 (`!f:real->real g:real->real s t.
        real_closed s /\
        f real_measurable_on t /\
        (!x. f(x) IN s) /\
        g real_continuous_on s /\
        &0 IN s /\ g(&0) = &0
        ==> (g o f) real_measurable_on t`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift o g o drop`;
                 `IMAGE lift s`; `IMAGE lift t`]
        MEASURABLE_ON_COMPOSE_CONTINUOUS_CLOSED_SET_0) THEN
  REWRITE_TAC[real_measurable_on; REAL_CONTINUOUS_ON; REAL_CLOSED] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; IMAGE_LIFT_UNIV; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM FORALL_DROP] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; LIFT_DROP; GSYM LIFT_NUM]);;

let CONTINUOUS_IMP_REAL_MEASURABLE_ON = prove
 (`!f. f real_continuous_on (:real) ==> f real_measurable_on (:real)`,
  REWRITE_TAC[REAL_CONTINUOUS_ON; real_measurable_on] THEN
  REWRITE_TAC[CONTINUOUS_IMP_MEASURABLE_ON; IMAGE_LIFT_UNIV]);;

let REAL_MEASURABLE_ON_CONST = prove
 (`!k:real. (\x. k) real_measurable_on (:real)`,
  SIMP_TAC[real_measurable_on; o_DEF; MEASURABLE_ON_CONST; IMAGE_LIFT_UNIV]);;

let REAL_MEASURABLE_ON_0 = prove
 (`!s. (\x. &0) real_measurable_on s`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[REAL_MEASURABLE_ON_CONST; COND_ID]);;

let REAL_MEASURABLE_ON_LMUL = prove
 (`!c f s. f real_measurable_on s ==> (\x. c * f x) real_measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_measurable_on] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP MEASURABLE_ON_CMUL) THEN
  REWRITE_TAC[o_DEF; LIFT_CMUL; LIFT_DROP]);;

let REAL_MEASURABLE_ON_RMUL = prove
 (`!c f s. f real_measurable_on s ==> (\x. f x * c) real_measurable_on s`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_MEASURABLE_ON_LMUL]);;

let REAL_MEASURABLE_ON_NEG = prove
 (`!f s. f real_measurable_on s ==> (\x. --(f x)) real_measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_measurable_on] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_NEG) THEN
  REWRITE_TAC[o_DEF; LIFT_NEG; LIFT_DROP]);;

let REAL_MEASURABLE_ON_NEG_EQ = prove
 (`!f s. (\x. --(f x)) real_measurable_on s <=> f real_measurable_on s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_MEASURABLE_ON_NEG) THEN
  REWRITE_TAC[REAL_NEG_NEG; ETA_AX]);;

let REAL_MEASURABLE_ON_ABS = prove
 (`!f s. f real_measurable_on s ==> (\x. abs(f x)) real_measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_measurable_on] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_NORM) THEN
  REWRITE_TAC[o_DEF; NORM_LIFT]);;

let REAL_MEASURABLE_ON_ADD = prove
 (`!f g s. f real_measurable_on s /\ g real_measurable_on s
           ==> (\x. f x + g x) real_measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_measurable_on] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_ADD) THEN
  REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_DROP]);;

let REAL_MEASURABLE_ON_SUB = prove
 (`!f g s.
        f real_measurable_on s /\ g real_measurable_on s
        ==> (\x. f x - g x) real_measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_measurable_on] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_SUB) THEN
  REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP]);;

let REAL_MEASURABLE_ON_MAX = prove
 (`!f g s.
        f real_measurable_on s /\ g real_measurable_on s
        ==> (\x. max (f x) (g x)) real_measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_measurable_on] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_MAX) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[FUN_EQ_THM; o_THM; CART_EQ; LAMBDA_BETA; DIMINDEX_1; FORALL_1] THEN
  REWRITE_TAC[GSYM drop; LIFT_DROP]);;

let REAL_MEASURABLE_ON_MIN = prove
 (`!f g s.
        f real_measurable_on s /\ g real_measurable_on s
        ==> (\x. min (f x) (g x)) real_measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_measurable_on] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_MIN) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[FUN_EQ_THM; o_THM; CART_EQ; LAMBDA_BETA; DIMINDEX_1; FORALL_1] THEN
  REWRITE_TAC[GSYM drop; LIFT_DROP]);;

let REAL_MEASURABLE_ON_MUL = prove
 (`!f g s.
        f real_measurable_on s /\ g real_measurable_on s
        ==> (\x. f x * g x) real_measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_measurable_on] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_DROP_MUL) THEN
  REWRITE_TAC[o_DEF; LIFT_CMUL; LIFT_DROP]);;

let REAL_MEASURABLE_ON_SPIKE_SET = prove
 (`!f:real->real s t.
        real_negligible (s DIFF t UNION t DIFF s)
        ==> f real_measurable_on s
            ==> f real_measurable_on t`,
  REWRITE_TAC[real_measurable_on; real_negligible] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC MEASURABLE_ON_SPIKE_SET THEN POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
  SET_TAC[]);;

let REAL_MEASURABLE_ON_RESTRICT = prove
 (`!f s. f real_measurable_on (:real) /\
         real_lebesgue_measurable s
         ==> (\x. if x IN s then f(x) else &0) real_measurable_on (:real)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_measurable_on; REAL_LEBESGUE_MEASURABLE;
              IMAGE_LIFT_UNIV] THEN
  REWRITE_TAC[o_DEF; COND_RAND; LIFT_NUM; GSYM IN_IMAGE_LIFT_DROP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_RESTRICT) THEN
  REWRITE_TAC[]);;

let REAL_MEASURABLE_ON_LIMIT = prove
 (`!f g s k.
        (!n. (f n) real_measurable_on s) /\
        real_negligible k /\
        (!x. x IN s DIFF k ==> ((\n. f n x) ---> g x) sequentially)
        ==> g real_measurable_on s`,
  REWRITE_TAC[real_measurable_on; real_negligible; TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN MAP_EVERY EXISTS_TAC
   [`\n:num. lift o f n o drop`; `IMAGE lift k`] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[LIFT_DROP; SET_RULE `(!x. drop(lift x) = x)
            ==> IMAGE lift s DIFF IMAGE lift t = IMAGE lift (s DIFF t)`] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; o_DEF; LIFT_DROP]);;

let ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT = prove
 (`!f g s. f real_measurable_on s /\ real_bounded (IMAGE f s) /\
           g absolutely_real_integrable_on s
           ==> (\x. f x * g x) absolutely_real_integrable_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_BOUNDED_POS]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `B:real` THEN STRIP_TAC THEN MATCH_MP_TAC
   REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x. B * abs((g:real->real) x)` THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_ON_MUL; INTEGRABLE_IMP_REAL_MEASURABLE;
    ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE; REAL_INTEGRABLE_LMUL;
    ABSOLUTELY_REAL_INTEGRABLE_ABS] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_LE_RMUL; REAL_ABS_POS]);;

let REAL_COMPLEX_MEASURABLE_ON = prove
 (`!f s. f real_measurable_on s <=>
         (Cx o f o drop) measurable_on (IMAGE lift s)`,
  ONCE_REWRITE_TAC[GSYM REAL_MEASURABLE_ON_UNIV;
                   GSYM MEASURABLE_ON_UNIV] THEN
  ONCE_REWRITE_TAC[MEASURABLE_ON_COMPONENTWISE] THEN
  REWRITE_TAC[FORALL_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[real_measurable_on; IMAGE_LIFT_UNIV] THEN
  REWRITE_TAC[o_DEF; IN_IMAGE_LIFT_DROP] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; LIFT_NUM; COMPLEX_VEC_0] THEN
  REWRITE_TAC[RE_CX; IM_CX; COND_ID; MEASURABLE_ON_CONST; LIFT_NUM]);;

let REAL_MEASURABLE_ON_INV = prove
 (`!f. f real_measurable_on (:real) /\ real_negligible {x | f x = &0}
       ==> (\x. inv(f x)) real_measurable_on (:real)`,
  GEN_TAC THEN REWRITE_TAC[REAL_COMPLEX_MEASURABLE_ON] THEN
  REWRITE_TAC[o_DEF; CX_INV; IMAGE_LIFT_UNIV] THEN STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_ON_COMPLEX_INV THEN ASM_REWRITE_TAC[CX_INJ] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_negligible]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN MESON_TAC[LIFT_DROP]);;

let REAL_MEASURABLE_ON_DIV = prove
 (`!f g. f real_measurable_on s /\ g real_measurable_on (:real) /\
         real_negligible {x | g(x) = &0}
         ==> (\x. f(x) / g(x)) real_measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_COMPLEX_MEASURABLE_ON] THEN
  REWRITE_TAC[o_DEF; CX_DIV; IMAGE_LIFT_UNIV] THEN STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_ON_COMPLEX_DIV THEN ASM_REWRITE_TAC[CX_INJ] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_negligible]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN MESON_TAC[LIFT_DROP]);;

let REAL_MEASURABLE_ON_RPOW = prove
 (`!f r s. f real_measurable_on s /\ &0 < r
           ==> (\x. f x rpow r) real_measurable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. f x rpow r) = (\x. x rpow r) o (f:real->real)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_MEASURABLE_ON_COMPOSE_CONTINUOUS_0 THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_ON_RPOW; RPOW_ZERO;
               REAL_LT_IMP_LE; REAL_LT_IMP_NZ]);;

(* ------------------------------------------------------------------------- *)
(* Properties of real Lebesgue measurable sets.                              *)
(* ------------------------------------------------------------------------- *)

let REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE = prove
 (`!s. real_measurable s ==> real_lebesgue_measurable s`,
  REWRITE_TAC[REAL_LEBESGUE_MEASURABLE; REAL_MEASURABLE_MEASURABLE;
              MEASURABLE_IMP_LEBESGUE_MEASURABLE]);;

let REAL_LEBESGUE_MEASURABLE_EMPTY = prove
 (`real_lebesgue_measurable {}`,
  REWRITE_TAC[REAL_LEBESGUE_MEASURABLE; IMAGE_CLAUSES;
              LEBESGUE_MEASURABLE_EMPTY]);;

let REAL_LEBESGUE_MEASURABLE_UNIV = prove
 (`real_lebesgue_measurable (:real)`,
  REWRITE_TAC[REAL_LEBESGUE_MEASURABLE; IMAGE_LIFT_UNIV;
              LEBESGUE_MEASURABLE_UNIV]);;

let REAL_LEBESGUE_MEASURABLE_COMPACT = prove
 (`!s. real_compact s ==> real_lebesgue_measurable s`,
  SIMP_TAC[REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE;
           REAL_MEASURABLE_COMPACT]);;

let REAL_LEBESGUE_MEASURABLE_INTERVAL = prove
 (`(!a b. real_lebesgue_measurable(real_interval[a,b])) /\
   (!a b. real_lebesgue_measurable(real_interval(a,b)))`,
  SIMP_TAC[REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE;
           REAL_MEASURABLE_REAL_INTERVAL]);;

let REAL_LEBESGUE_MEASURABLE_INTER = prove
 (`!s t. real_lebesgue_measurable s /\ real_lebesgue_measurable t
         ==> real_lebesgue_measurable(s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LEBESGUE_MEASURABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LEBESGUE_MEASURABLE_INTER) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN MP_TAC LIFT_DROP THEN SET_TAC[]);;

let REAL_LEBESGUE_MEASURABLE_UNION = prove
 (`!s t:real->bool.
        real_lebesgue_measurable s /\ real_lebesgue_measurable t
        ==> real_lebesgue_measurable(s UNION t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LEBESGUE_MEASURABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LEBESGUE_MEASURABLE_UNION) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN MP_TAC LIFT_DROP THEN SET_TAC[]);;

let REAL_LEBESGUE_MEASURABLE_COMPL = prove
 (`!s. real_lebesgue_measurable((:real) DIFF s) <=>
       real_lebesgue_measurable s`,
  GEN_TAC THEN REWRITE_TAC[REAL_LEBESGUE_MEASURABLE] THEN
  GEN_REWRITE_TAC (RAND_CONV) [GSYM LEBESGUE_MEASURABLE_COMPL] THEN
  AP_TERM_TAC THEN MP_TAC LIFT_DROP THEN SET_TAC[]);;

let REAL_LEBESGUE_MEASURABLE_DIFF = prove
 (`!s t:real->bool.
        real_lebesgue_measurable s /\ real_lebesgue_measurable t
        ==> real_lebesgue_measurable(s DIFF t)`,
  ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
  SIMP_TAC[REAL_LEBESGUE_MEASURABLE_COMPL; REAL_LEBESGUE_MEASURABLE_INTER]);;

let REAL_LEBESGUE_MEASURABLE_ON_SUBINTERVALS = prove
 (`!s. real_lebesgue_measurable s <=>
       !a b. real_lebesgue_measurable(s INTER real_interval[a,b])`,
  GEN_TAC THEN REWRITE_TAC[REAL_LEBESGUE_MEASURABLE] THEN
  GEN_REWRITE_TAC LAND_CONV [LEBESGUE_MEASURABLE_ON_SUBINTERVALS] THEN
  REWRITE_TAC[FORALL_DROP; GSYM IMAGE_DROP_INTERVAL] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN AP_TERM_TAC THEN
  MP_TAC LIFT_DROP THEN SET_TAC[]);;

let REAL_LEBESGUE_MEASURABLE_CLOSED = prove
 (`!s. real_closed s ==> real_lebesgue_measurable s`,
  REWRITE_TAC[REAL_LEBESGUE_MEASURABLE; REAL_CLOSED;
              LEBESGUE_MEASURABLE_CLOSED]);;

let REAL_LEBESGUE_MEASURABLE_OPEN = prove
 (`!s. real_open s ==> real_lebesgue_measurable s`,
  REWRITE_TAC[REAL_LEBESGUE_MEASURABLE; REAL_OPEN;
              LEBESGUE_MEASURABLE_OPEN]);;

let REAL_LEBESGUE_MEASURABLE_UNIONS = prove
 (`!f. FINITE f /\ (!s. s IN f ==> real_lebesgue_measurable s)
       ==> real_lebesgue_measurable (UNIONS f)`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[UNIONS_0; UNIONS_INSERT; REAL_LEBESGUE_MEASURABLE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LEBESGUE_MEASURABLE_UNION THEN ASM_SIMP_TAC[]);;

let REAL_LEBESGUE_MEASURABLE_COUNTABLE_UNIONS_EXPLICIT = prove
 (`!s:num->real->bool.
        (!n. real_lebesgue_measurable(s n))
        ==> real_lebesgue_measurable(UNIONS {s n | n IN (:num)})`,
  GEN_TAC THEN REWRITE_TAC[REAL_LEBESGUE_MEASURABLE] THEN DISCH_THEN(MP_TAC o
    MATCH_MP LEBESGUE_MEASURABLE_COUNTABLE_UNIONS_EXPLICIT) THEN
  REWRITE_TAC[IMAGE_UNIONS; SIMPLE_IMAGE] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]);;

let REAL_LEBESGUE_MEASURABLE_COUNTABLE_UNIONS = prove
 (`!f:(real->bool)->bool.
        COUNTABLE f /\ (!s. s IN f ==> real_lebesgue_measurable s)
        ==> real_lebesgue_measurable (UNIONS f)`,
  GEN_TAC THEN ASM_CASES_TAC `f:(real->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; REAL_LEBESGUE_MEASURABLE_EMPTY] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `f:(real->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
  MATCH_MP_TAC REAL_LEBESGUE_MEASURABLE_COUNTABLE_UNIONS_EXPLICIT THEN
  GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]);;

let REAL_LEBESGUE_MEASURABLE_COUNTABLE_INTERS = prove
 (`!f:(real->bool)->bool.
        COUNTABLE f /\ (!s. s IN f ==> real_lebesgue_measurable s)
        ==> real_lebesgue_measurable (INTERS f)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[INTERS_UNIONS; REAL_LEBESGUE_MEASURABLE_COMPL] THEN
  MATCH_MP_TAC REAL_LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; COUNTABLE_IMAGE;
               REAL_LEBESGUE_MEASURABLE_COMPL]);;

let REAL_LEBESGUE_MEASURABLE_COUNTABLE_INTERS_EXPLICIT = prove
 (`!s:num->real->bool.
        (!n. real_lebesgue_measurable(s n))
        ==> real_lebesgue_measurable(INTERS {s n | n IN (:num)})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LEBESGUE_MEASURABLE_COUNTABLE_INTERS THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE]);;

let REAL_LEBESGUE_MEASURABLE_INTERS = prove
 (`!f:(real->bool)->bool.
        FINITE f /\ (!s. s IN f ==> real_lebesgue_measurable s)
        ==> real_lebesgue_measurable (INTERS f)`,
  SIMP_TAC[REAL_LEBESGUE_MEASURABLE_COUNTABLE_INTERS; FINITE_IMP_COUNTABLE]);;

let REAL_LEBESGUE_MEASURABLE_IFF_MEASURABLE = prove
 (`!s. real_bounded s ==> (real_lebesgue_measurable s <=> real_measurable s)`,
  REWRITE_TAC[REAL_BOUNDED; REAL_LEBESGUE_MEASURABLE;
              REAL_MEASURABLE_MEASURABLE] THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_IFF_MEASURABLE]);;

let REAL_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET = prove
 (`!f s t. s SUBSET t /\ f real_measurable_on t /\
           real_lebesgue_measurable s
           ==> f real_measurable_on s`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_MEASURABLE_ON_RESTRICT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM SET_TAC[]);;

let REAL_MEASURABLE_ON_MEASURABLE_SUBSET = prove
 (`!f s t. s SUBSET t /\ f real_measurable_on t /\ real_measurable s
           ==> f real_measurable_on s`,
  MESON_TAC[REAL_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET;
            REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE]);;

let REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET = prove
 (`!f s. f real_continuous_on s /\ real_closed s ==> f real_measurable_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON; REAL_CLOSED; real_measurable_on] THEN
  REWRITE_TAC[CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET]);;

let REAL_CONTINUOUS_AE_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET = prove
 (`!f s m.
        f real_continuous_on s DIFF m /\
        real_lebesgue_measurable s /\
        real_negligible m
        ==> f real_measurable_on s`,
  REWRITE_TAC[real_measurable_on; real_negligible; REAL_LEBESGUE_MEASURABLE;
              REAL_CONTINUOUS_ON] THEN
  SIMP_TAC[IMAGE_DIFF_INJ; LIFT_EQ] THEN
  REWRITE_TAC[CONTINUOUS_AE_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET]);;

let REAL_MEASURABLE_ON_CASES = prove
 (`!P f g s.
        real_lebesgue_measurable {x | P x} /\
        f real_measurable_on s /\ g real_measurable_on s
        ==> (\x. if P x then f x else g x) real_measurable_on s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_MEASURABLE_ON_UNIV] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. (if x IN s then if P x then f x else g x else &0) =
        (if x IN {x | P x} then if x IN s then f x else &0 else &0) +
        (if x IN (:real) DIFF {x | P x}
         then if x IN s then g x else &0 else &0)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[IN_UNIV; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[REAL_ADD_LID; REAL_ADD_RID];
    MATCH_MP_TAC REAL_MEASURABLE_ON_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_MEASURABLE_ON_RESTRICT THEN
    ASM_REWRITE_TAC[REAL_LEBESGUE_MEASURABLE_COMPL]]);;

(* ------------------------------------------------------------------------- *)
(* Various common equivalent forms of function measurability.                *)
(* ------------------------------------------------------------------------- *)

let REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_LT = prove
 (`!f. f real_measurable_on (:real) <=>
        !a. real_lebesgue_measurable {x | f(x) < a}`,
  REWRITE_TAC[real_measurable_on; REAL_LEBESGUE_MEASURABLE; IMAGE_LIFT_UNIV;
   MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; o_DEF; LIFT_DROP] THEN
  GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

let REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_LE = prove
 (`!f. f real_measurable_on (:real) <=>
        !a. real_lebesgue_measurable {x | f(x) <= a}`,
  REWRITE_TAC[real_measurable_on; REAL_LEBESGUE_MEASURABLE; IMAGE_LIFT_UNIV;
   MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; o_DEF; LIFT_DROP] THEN
  GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

let REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_GT = prove
 (`!f. f real_measurable_on (:real) <=>
        !a. real_lebesgue_measurable {x | f(x) > a}`,
  REWRITE_TAC[real_measurable_on; REAL_LEBESGUE_MEASURABLE; IMAGE_LIFT_UNIV;
   MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; o_DEF; LIFT_DROP] THEN
  GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

let REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_GE = prove
 (`!f. f real_measurable_on (:real) <=>
        !a. real_lebesgue_measurable {x | f(x) >= a}`,
  REWRITE_TAC[real_measurable_on; REAL_LEBESGUE_MEASURABLE; IMAGE_LIFT_UNIV;
   MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GE] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; o_DEF; LIFT_DROP] THEN
  GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

let REAL_MEASURABLE_ON_PREIMAGE_OPEN_INTERVAL = prove
 (`!f. f real_measurable_on (:real) <=>
       !a b. real_lebesgue_measurable {x | f(x) IN real_interval(a,b)}`,
  REWRITE_TAC[real_measurable_on; REAL_LEBESGUE_MEASURABLE; IMAGE_LIFT_UNIV;
              MEASURABLE_ON_PREIMAGE_OPEN_INTERVAL; FORALL_DROP] THEN
  GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; o_DEF; GSYM IMAGE_DROP_INTERVAL; LIFT_DROP;
              FORALL_DROP; IN_IMAGE] THEN MESON_TAC[LIFT_DROP]);;

let REAL_MEASURABLE_ON_PREIMAGE_CLOSED_INTERVAL = prove
 (`!f. f real_measurable_on (:real) <=>
       !a b. real_lebesgue_measurable {x | f(x) IN real_interval[a,b]}`,
  REWRITE_TAC[real_measurable_on; REAL_LEBESGUE_MEASURABLE; IMAGE_LIFT_UNIV;
              MEASURABLE_ON_PREIMAGE_CLOSED_INTERVAL; FORALL_DROP] THEN
  GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; o_DEF; GSYM IMAGE_DROP_INTERVAL; LIFT_DROP;
              FORALL_DROP; IN_IMAGE] THEN MESON_TAC[LIFT_DROP]);;

let REAL_MEASURABLE_ON_PREIMAGE_OPEN = prove
 (`!f. f real_measurable_on (:real) <=>
       !t. real_open t ==> real_lebesgue_measurable {x | f(x) IN t}`,
  REWRITE_TAC[real_measurable_on; REAL_LEBESGUE_MEASURABLE; IMAGE_LIFT_UNIV;
              MEASURABLE_ON_PREIMAGE_OPEN; REAL_OPEN] THEN
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `t:real->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE lift t`) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real^1->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE drop t`) THEN
    ASM_REWRITE_TAC[IMAGE_LIFT_DROP; GSYM IMAGE_o]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THENL
   [CONV_TAC SYM_CONV; ALL_TAC] THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_IMAGE; o_DEF; IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

let REAL_MEASURABLE_ON_PREIMAGE_CLOSED = prove
 (`!f. f real_measurable_on (:real) <=>
       !t. real_closed t ==> real_lebesgue_measurable {x | f(x) IN t}`,
  REWRITE_TAC[real_measurable_on; REAL_LEBESGUE_MEASURABLE; IMAGE_LIFT_UNIV;
              MEASURABLE_ON_PREIMAGE_CLOSED; REAL_CLOSED] THEN
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `t:real->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE lift t`) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real^1->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE drop t`) THEN
    ASM_REWRITE_TAC[IMAGE_LIFT_DROP; GSYM IMAGE_o]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THENL
   [CONV_TAC SYM_CONV; ALL_TAC] THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_IMAGE; o_DEF; IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

let REAL_MEASURABLE_ON_SIMPLE_FUNCTION_LIMIT = prove
 (`!f. f real_measurable_on (:real) <=>
       ?g. (!n. (g n) real_measurable_on (:real)) /\
           (!n. FINITE(IMAGE (g n) (:real))) /\
           (!x. ((\n. g n x) ---> f x) sequentially)`,
  GEN_TAC THEN REWRITE_TAC[real_measurable_on; IMAGE_LIFT_UNIV] THEN
  GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_SIMPLE_FUNCTION_LIMIT] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:num->real^1->real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\n:num. drop o g n o lift` THEN
    REWRITE_TAC[TENDSTO_REAL] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX];
      GEN_TAC THEN REWRITE_TAC[IMAGE_o; IMAGE_LIFT_UNIV] THEN
      MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real` THEN REWRITE_TAC[TENDSTO_REAL] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `lift x`) THEN
      REWRITE_TAC[o_DEF; LIFT_DROP]];
    DISCH_THEN(X_CHOOSE_THEN `g:num->real->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\n:num. lift o g n o drop` THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      GEN_TAC THEN REWRITE_TAC[IMAGE_o; IMAGE_DROP_UNIV] THEN
      MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^1` THEN FIRST_X_ASSUM(MP_TAC o SPEC `drop x`) THEN
      REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP]]]);;

let REAL_LEBESGUE_MEASURABLE_PREIMAGE_OPEN = prove
 (`!f t. f real_measurable_on (:real) /\ real_open t
         ==> real_lebesgue_measurable {x | f(x) IN t}`,
  SIMP_TAC[REAL_MEASURABLE_ON_PREIMAGE_OPEN]);;

let REAL_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED = prove
 (`!f t. f real_measurable_on (:real) /\ real_closed t
         ==> real_lebesgue_measurable {x | f(x) IN t}`,
  SIMP_TAC[REAL_MEASURABLE_ON_PREIMAGE_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of measure within a halfspace w.r.t. to the boundary.          *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_MEASURE_IN_HALFSPACE_LE = prove
 (`!(s:real^N->bool) a i.
        measurable s /\ 1 <= i /\ i <= dimindex(:N)
        ==> (\a. measure(s INTER {x | x$i <= a})) real_continuous atreal a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1] THEN
  REWRITE_TAC[continuous_atreal; o_THM] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?u v:real^N. abs(measure(s INTER interval[u,v]) - measure s) < e / &2 /\
                 ~(interval(u,v) = {}) /\ u$i < a /\ a < v$i`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `e / &2`] MEASURE_LIMIT) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `ball(vec 0:real^N,B)` BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
    REWRITE_TAC[BOUNDED_BALL; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
    EXISTS_TAC `(lambda j. min (a - &1) ((u:real^N)$j)):real^N` THEN
    EXISTS_TAC `(lambda j. max (a + &1) ((v:real^N)$j)):real^N` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM
       (MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
      SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[INTERVAL_NE_EMPTY; LAMBDA_BETA] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`indicator(s:real^N->bool)`; `u:real^N`; `v:real^N`; `u:real^N`;
    `(lambda j. if j = i then min ((v:real^N)$i) a else v$j):real^N`;
    `e / &2`]
      INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN ANTS_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
    REWRITE_TAC[indicator; MESON[]
     `(if P then if Q then x else y else y) =
      (if P /\ Q then x else y)`] THEN
    REWRITE_TAC[GSYM IN_INTER; GSYM MEASURABLE_INTEGRABLE] THEN
    ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
    ASM_SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (min (a - (u:real^N)$i) ((v:real^N)$i - a))` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_SUB_LT] THEN
  X_GEN_TAC `b:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`;
   `(lambda j. if j = i then min ((v:real^N)$i) b else v$j):real^N`]) THEN
  REWRITE_TAC[dist] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
    ASM_SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[NORM_LE_SQUARE; dot; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
       `sum(1..dimindex(:N)) (\j. if j = i then d pow 2 else &0)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_POW_2; GSYM REAL_LE_SQUARE_ABS] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG; REAL_LE_REFL]]];
    SUBGOAL_THEN
     `!b. integral
           (interval[u:real^N,
                     (lambda j. if j = i then min (v$i) b else (v:real^N)$j)])
           (indicator s) =
          lift(measure(s INTER interval[u,v] INTER {x | x$i <= b}))`
     (fun th -> REWRITE_TAC[th])
    THENL
     [GEN_TAC THEN
      ASM_SIMP_TAC[MEASURE_INTEGRAL; MEASURABLE_INTER_HALFSPACE_LE;
                   MEASURABLE_INTER; MEASURABLE_INTERVAL; LIFT_DROP] THEN
      ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
      AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      ASM_SIMP_TAC[INTERVAL_SPLIT; indicator] THEN
      REWRITE_TAC[IN_INTER] THEN MESON_TAC[];
      REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
      SUBGOAL_THEN
       `!b. measure(s INTER {x:real^N | x$i <= b}) =
            measure((s INTER interval[u,v]) INTER {x | x$i <= b}) +
            measure((s DIFF interval[u,v]) INTER {x | x$i <= b})`
       (fun th -> REWRITE_TAC[th])
      THENL
       [GEN_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNION_EQ THEN
        ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_INTER_HALFSPACE_LE;
                     MEASURABLE_INTERVAL; MEASURABLE_DIFF] THEN
        CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY] `s = {} ==> negligible s`) THEN
        SET_TAC[];
        REWRITE_TAC[GSYM INTER_ASSOC] THEN MATCH_MP_TAC(REAL_ARITH
         `abs(nub - nua) < e / &2
          ==> abs(mub - mua) < e / &2
              ==> abs((mub + nub) - (mua + nua)) < e`) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `y < e ==> x <= y ==> x < e`)) THEN
        SUBGOAL_THEN
         `abs(measure(s INTER interval [u,v]) - measure s) =
          measure(s DIFF interval[u:real^N,v])`
        SUBST1_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH
           `x + z = y /\ &0 <= z ==> abs(x - y) = z`) THEN
          ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_DIFF;
                       MEASURABLE_INTERVAL] THEN
          MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNION_EQ THEN
          ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_DIFF;
                       MEASURABLE_INTERVAL] THEN
          CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY] `s = {} ==> negligible s`) THEN
          SET_TAC[];
          MATCH_MP_TAC(REAL_ARITH
           `&0 <= x /\ x <= a /\ &0 <= y /\ y <= a ==> abs(x - y) <= a`) THEN
          ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_INTER_HALFSPACE_LE;
            MEASURABLE_INTERVAL; MEASURABLE_DIFF; MEASURE_POS_LE] THEN
          CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
          ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_INTER_HALFSPACE_LE;
            MEASURABLE_INTERVAL; MEASURABLE_DIFF; MEASURE_POS_LE] THEN
          SET_TAC[]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Second mean value theorem and monotone integrability.                     *)
(* ------------------------------------------------------------------------- *)

let REAL_SECOND_MEAN_VALUE_THEOREM_FULL = prove
 (`!f g a b.
        ~(real_interval[a,b] = {}) /\
        f real_integrable_on real_interval[a,b] /\
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> g x <= g y)
        ==> ?c. c IN real_interval[a,b] /\
                ((\x. g x * f x) has_real_integral
                 (g(a) * real_integral (real_interval[a,c]) f +
                  g(b) * real_integral (real_interval[c,b]) f))
                (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `(g:real->real) o drop`;
                 `lift a`; `lift b`]
    SECOND_MEAN_VALUE_THEOREM_FULL) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IMAGE_EQ_EMPTY] THEN
  ASM_REWRITE_TAC[GSYM REAL_INTEGRABLE_ON] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  REWRITE_TAC[o_DEF; LIFT_CMUL; LIFT_ADD] THEN AP_TERM_TAC THEN
  BINOP_TAC THEN AP_TERM_TAC THEN ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) REAL_INTEGRAL o rand o snd) THEN
  REWRITE_TAC[o_DEF] THEN ANTS_TAC THEN SIMP_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY]) THEN
  ASM_REAL_ARITH_TAC);;

let REAL_SECOND_MEAN_VALUE_THEOREM = prove
 (`!f g a b.
        ~(real_interval[a,b] = {}) /\
        f real_integrable_on real_interval[a,b] /\
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> g x <= g y)
        ==> ?c. c IN real_interval[a,b] /\
                real_integral (real_interval[a,b]) (\x. g x * f x) =
                 g(a) * real_integral (real_interval[a,c]) f +
                 g(b) * real_integral (real_interval[c,b]) f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SECOND_MEAN_VALUE_THEOREM_FULL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[]);;

let REAL_SECOND_MEAN_VALUE_THEOREM_GEN_FULL = prove
 (`!f g a b u v.
        ~(real_interval[a,b] = {}) /\
        f real_integrable_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b) ==> u <= g x /\ g x <= v) /\
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> g x <= g y)
        ==> ?c. c IN real_interval[a,b] /\
                ((\x. g x * f x) has_real_integral
                 (u * real_integral (real_interval[a,c]) f +
                  v * real_integral (real_interval[c,b]) f))
                (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `(g:real->real) o drop`;
                 `lift a`; `lift b`; `u:real`; `v:real`]
    SECOND_MEAN_VALUE_THEOREM_GEN_FULL) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IMAGE_EQ_EMPTY] THEN
  ASM_REWRITE_TAC[GSYM REAL_INTEGRABLE_ON] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  REWRITE_TAC[o_DEF; LIFT_CMUL; LIFT_ADD] THEN AP_TERM_TAC THEN
  BINOP_TAC THEN AP_TERM_TAC THEN ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) REAL_INTEGRAL o rand o snd) THEN
  REWRITE_TAC[o_DEF] THEN ANTS_TAC THEN SIMP_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY]) THEN
  ASM_REAL_ARITH_TAC);;

let REAL_SECOND_MEAN_VALUE_THEOREM_GEN = prove
 (`!f g a b u v.
        ~(real_interval[a,b] = {}) /\
        f real_integrable_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b) ==> u <= g x /\ g x <= v) /\
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> g x <= g y)
        ==> ?c. c IN real_interval[a,b] /\
                real_integral (real_interval[a,b]) (\x. g x * f x) =
                 u * real_integral (real_interval[a,c]) f +
                 v * real_integral (real_interval[c,b]) f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SECOND_MEAN_VALUE_THEOREM_GEN_FULL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[]);;

let REAL_SECOND_MEAN_VALUE_THEOREM_BONNET_FULL = prove
 (`!f g a b.
        ~(real_interval[a,b] = {}) /\
        f real_integrable_on real_interval[a,b] /\
        (!x. x IN real_interval[a,b] ==> &0 <= g x) /\
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> g x <= g y)
        ==> ?c. c IN real_interval[a,b] /\
                ((\x. g x * f x) has_real_integral
                 (g(b) * real_integral (real_interval[c,b]) f))
                (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `(g:real->real) o drop`;
                 `lift a`; `lift b`]
    SECOND_MEAN_VALUE_THEOREM_BONNET_FULL) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IMAGE_EQ_EMPTY] THEN
  ASM_REWRITE_TAC[GSYM REAL_INTEGRABLE_ON] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  REWRITE_TAC[o_DEF; LIFT_CMUL; LIFT_ADD] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) REAL_INTEGRAL o rand o snd) THEN
  REWRITE_TAC[o_DEF] THEN ANTS_TAC THEN SIMP_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY]) THEN
  ASM_REAL_ARITH_TAC);;

let REAL_SECOND_MEAN_VALUE_THEOREM_BONNET = prove
 (`!f g a b.
        ~(real_interval[a,b] = {}) /\
        f real_integrable_on real_interval[a,b] /\
        (!x. x IN real_interval[a,b] ==> &0 <= g x) /\
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> g x <= g y)
        ==> ?c. c IN real_interval[a,b] /\
                real_integral (real_interval[a,b]) (\x. g x * f x) =
                g(b) * real_integral (real_interval[c,b]) f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SECOND_MEAN_VALUE_THEOREM_BONNET_FULL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[]);;

let REAL_INTEGRABLE_INCREASING_PRODUCT = prove
 (`!f g a b.
        f real_integrable_on real_interval[a,b] /\
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> g(x) <= g(y))
        ==> (\x. g(x) * f(x)) real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `(g:real->real) o drop`;
                 `lift a`; `lift b`]
    INTEGRABLE_INCREASING_PRODUCT) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL;
                  GSYM REAL_INTEGRABLE_ON] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[o_DEF; LIFT_DROP; REAL_INTEGRABLE_ON; LIFT_CMUL]);;

let REAL_INTEGRABLE_INCREASING_PRODUCT_UNIV = prove
 (`!f g B.
        f real_integrable_on (:real) /\
        (!x y. x <= y ==> g x <= g y) /\
        (!x. abs(g x) <= B)
         ==> (\x. g x * f x) real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `(g:real->real) o drop`; `B:real`]
    INTEGRABLE_INCREASING_PRODUCT_UNIV) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_UNIV;
                  GSYM REAL_INTEGRABLE_ON] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[o_DEF; LIFT_DROP; REAL_INTEGRABLE_ON; LIFT_CMUL]);;

let REAL_INTEGRABLE_INCREASING = prove
 (`!f a b.
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> f(x) <= f(y))
        ==> f real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift a`; `lift b`]
    INTEGRABLE_INCREASING_1) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL;
                  GSYM REAL_INTEGRABLE_ON] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[o_DEF; LIFT_DROP; REAL_INTEGRABLE_ON; LIFT_CMUL]);;

let REAL_INTEGRABLE_DECREASING_PRODUCT = prove
 (`!f g a b.
        f real_integrable_on real_interval[a,b] /\
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> g(y) <= g(x))
        ==> (\x. g(x) * f(x)) real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `(g:real->real) o drop`;
                 `lift a`; `lift b`]
    INTEGRABLE_DECREASING_PRODUCT) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL;
                  GSYM REAL_INTEGRABLE_ON] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[o_DEF; LIFT_DROP; REAL_INTEGRABLE_ON; LIFT_CMUL]);;

let REAL_INTEGRABLE_DECREASING_PRODUCT_UNIV = prove
 (`!f g B.
        f real_integrable_on (:real) /\
        (!x y. x <= y ==> g y <= g x) /\
        (!x. abs(g x) <= B)
         ==> (\x. g x * f x) real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `(g:real->real) o drop`; `B:real`]
    INTEGRABLE_DECREASING_PRODUCT_UNIV) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_UNIV;
                  GSYM REAL_INTEGRABLE_ON] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[o_DEF; LIFT_DROP; REAL_INTEGRABLE_ON; LIFT_CMUL]);;

let REAL_INTEGRABLE_DECREASING = prove
 (`!f a b.
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> f(y) <= f(x))
        ==> f real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift a`; `lift b`]
    INTEGRABLE_DECREASING_1) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL;
                  GSYM REAL_INTEGRABLE_ON] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[o_DEF; LIFT_DROP; REAL_INTEGRABLE_ON; LIFT_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* Measurability and absolute integrability of monotone functions.           *)
(* ------------------------------------------------------------------------- *)

let REAL_MEASURABLE_ON_INCREASING_UNIV = prove
 (`!f. (!x y. x <= y ==> f x <= f y) ==> f real_measurable_on (:real)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_LE] THEN
  X_GEN_TAC `y:real` THEN
  REPEAT_TCL STRIP_THM_THEN ASSUME_TAC
   (SET_RULE `{x | (f:real->real) x <= y} = {} \/
              {x | (f:real->real) x <= y} = UNIV \/
              ?a b. f a <= y /\ ~(f b <= y)`) THEN
  ASM_REWRITE_TAC[REAL_LEBESGUE_MEASURABLE_EMPTY;
                  REAL_LEBESGUE_MEASURABLE_UNIV] THEN
  MP_TAC(ISPEC `{x | (f:real->real) x <= y}` SUP) THEN
  REWRITE_TAC[IN_ELIM_THM; EXTENSION; NOT_IN_EMPTY] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LE_TRANS]; ALL_TAC] THEN
  ABBREV_TAC `s = sup {x | (f:real->real) x <= y}` THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(!x. (f:real->real) x <= y <=> x < s) \/
     (!x. (f:real->real) x <= y <=> x <= s)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(f:real->real) s <= y` THEN
    ASM_MESON_TAC[REAL_LE_TRANS; REAL_NOT_LE; REAL_LE_ANTISYM; REAL_LE_TOTAL];
    ASM_SIMP_TAC[REAL_OPEN_HALFSPACE_LT; REAL_LEBESGUE_MEASURABLE_OPEN];
    ASM_SIMP_TAC[REAL_CLOSED_HALFSPACE_LE; REAL_LEBESGUE_MEASURABLE_CLOSED]]);;

let REAL_MEASURABLE_ON_INCREASING = prove
 (`!f a b. (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
                  ==> f x <= f y)
           ==> f real_measurable_on real_interval[a,b]`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `real_interval[a,b] = {}` THENL
   [ONCE_REWRITE_TAC[GSYM REAL_MEASURABLE_ON_UNIV] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_MEASURABLE_ON_0];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_INTERVAL_EQ_EMPTY; REAL_NOT_LT])] THEN
  ABBREV_TAC `g = \x. if x < a then f(a)
                      else if b < x then f(b)
                      else (f:real->real) x` THEN
  SUBGOAL_THEN `g real_measurable_on real_interval[a,b]` MP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_MEASURABLE_ON_UNIV] THEN EXPAND_TAC "g" THEN
    SIMP_TAC[IN_REAL_INTERVAL; GSYM REAL_NOT_LT]] THEN
  MATCH_MP_TAC REAL_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `(:real)` THEN
  REWRITE_TAC[SUBSET_UNIV; REAL_LEBESGUE_MEASURABLE_INTERVAL] THEN
  MATCH_MP_TAC REAL_MEASURABLE_ON_INCREASING_UNIV THEN EXPAND_TAC "g" THEN
  ASM_MESON_TAC[REAL_LT_LE; REAL_LE_TRANS; REAL_LE_TOTAL; REAL_LE_ANTISYM;
                REAL_NOT_LT; REAL_LT_IMP_LE; REAL_LE_REFL]);;

let REAL_MEASURABLE_ON_DECREASING_UNIV = prove
 (`!f. (!x y. x <= y ==> f y <= f x) ==> f real_measurable_on (:real)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [GSYM REAL_MEASURABLE_ON_NEG_EQ] THEN
  MATCH_MP_TAC REAL_MEASURABLE_ON_INCREASING_UNIV THEN
  ASM_SIMP_TAC[REAL_LE_NEG2]);;

let REAL_MEASURABLE_ON_DECREASING = prove
 (`!f a b. (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
                  ==> f y <= f x)
           ==> f real_measurable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [GSYM REAL_MEASURABLE_ON_NEG_EQ] THEN
  MATCH_MP_TAC REAL_MEASURABLE_ON_INCREASING THEN
  ASM_SIMP_TAC[REAL_LE_NEG2]);;

let ABSOLUTELY_REAL_INTEGRABLE_INCREASING_PRODUCT = prove
 (`!f g a b.
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> f x <= f y) /\
        g absolutely_real_integrable_on real_interval[a,b]
        ==> (\x. f x * g x) absolutely_real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_ON_INCREASING] THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
  EXISTS_TAC `abs((f:real->real) a) + abs((f:real->real) b)` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
   (REAL_ARITH `a <= x /\ x <= b ==> abs x <= abs a + abs b`) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[IN_REAL_INTERVAL; REAL_LE_TRANS; REAL_LE_REFL]);;

let ABSOLUTELY_REAL_INTEGRABLE_INCREASING = prove
 (`!f a b. (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
                  ==> f x <= f y)
           ==> f absolutely_real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  GEN_REWRITE_TAC (LAND_CONV o ABS_CONV) [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_INCREASING_PRODUCT THEN
  ASM_REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST]);;

let ABSOLUTELY_REAL_INTEGRABLE_DECREASING_PRODUCT = prove
 (`!f g a b.
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> f y <= f x) /\
        g absolutely_real_integrable_on real_interval[a,b]
        ==> (\x. f x * g x) absolutely_real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_ON_DECREASING] THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
  EXISTS_TAC `abs((f:real->real) a) + abs((f:real->real) b)` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
   (REAL_ARITH `b <= x /\ x <= a ==> abs x <= abs a + abs b`) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[IN_REAL_INTERVAL; REAL_LE_TRANS; REAL_LE_REFL]);;

let ABSOLUTELY_REAL_INTEGRABLE_DECREASING = prove
 (`!f a b. (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
                  ==> f y <= f x)
           ==> f absolutely_real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  GEN_REWRITE_TAC (LAND_CONV o ABS_CONV) [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_DECREASING_PRODUCT THEN
  ASM_REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST]);;

(* ------------------------------------------------------------------------- *)
(* Real functions of bounded variation.                                      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_bounded_real_variation_on",(12,"right"));;

let has_bounded_real_variation_on = new_definition
 `f has_bounded_real_variation_on s <=>
  (lift o f o drop) has_bounded_variation_on (IMAGE lift s)`;;

let real_variation = new_definition
 `real_variation s f = vector_variation (IMAGE lift s) (lift o f o drop)`;;

let HAS_BOUNDED_REAL_VARIATION_ON_EQ = prove
 (`!f g s.
        (!x. x IN s ==> f x = g x) /\ f has_bounded_real_variation_on s


        ==> g has_bounded_real_variation_on s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[IMP_CONJ; has_bounded_real_variation_on] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_BOUNDED_VARIATION_ON_EQ) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP]);;

let HAS_BOUNDED_REAL_VARIATION_ON_SUBSET = prove
 (`!f s t. f has_bounded_real_variation_on s /\ t SUBSET s
           ==> f has_bounded_real_variation_on t`,
  REWRITE_TAC[has_bounded_real_variation_on] THEN
  MESON_TAC[HAS_BOUNDED_VARIATION_ON_SUBSET; IMAGE_SUBSET]);;

let HAS_BOUNDED_REAL_VARIATION_ON_LMUL = prove
 (`!f c s. f has_bounded_real_variation_on s
           ==> (\x. c * f x) has_bounded_real_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_real_variation_on] THEN
  REWRITE_TAC[o_DEF; LIFT_CMUL; HAS_BOUNDED_VARIATION_ON_CMUL]);;

let HAS_BOUNDED_REAL_VARIATION_ON_RMUL = prove
 (`!f c s. f has_bounded_real_variation_on s
           ==> (\x. f x * c) has_bounded_real_variation_on s`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[HAS_BOUNDED_REAL_VARIATION_ON_LMUL]);;

let HAS_BOUNDED_REAL_VARIATION_ON_NEG = prove
 (`!f s. f has_bounded_real_variation_on s
         ==> (\x. --f x) has_bounded_real_variation_on s`,
  REWRITE_TAC[has_bounded_real_variation_on; o_DEF; LIFT_NEG] THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_NEG]);;

let HAS_BOUNDED_REAL_VARIATION_ON_ADD = prove
 (`!f g s. f has_bounded_real_variation_on s /\
           g has_bounded_real_variation_on s
           ==> (\x. f x + g x) has_bounded_real_variation_on s`,
  REWRITE_TAC[has_bounded_real_variation_on; o_DEF; LIFT_ADD] THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_ADD]);;

let HAS_BOUNDED_REAL_VARIATION_ON_SUB = prove
 (`!f g s. f has_bounded_real_variation_on s /\
           g has_bounded_real_variation_on s
           ==> (\x. f x - g x) has_bounded_real_variation_on s`,
  REWRITE_TAC[has_bounded_real_variation_on; o_DEF; LIFT_SUB] THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_SUB]);;

let HAS_BOUNDED_REAL_VARIATION_ON_NULL = prove
 (`!f a b. b <= a ==> f has_bounded_real_variation_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_bounded_real_variation_on] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_NULL THEN
  ASM_REWRITE_TAC[BOUNDED_INTERVAL; CONTENT_EQ_0_1; LIFT_DROP]);;

let HAS_BOUNDED_REAL_VARIATION_ON_EMPTY = prove
 (`!f. f has_bounded_real_variation_on {}`,
  REWRITE_TAC[IMAGE_CLAUSES; has_bounded_real_variation_on] THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_EMPTY]);;

let HAS_BOUNDED_REAL_VARIATION_ON_ABS = prove
 (`!f s. f has_bounded_real_variation_on s
         ==> (\x. abs(f x)) has_bounded_real_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_real_variation_on] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_BOUNDED_VARIATION_ON_NORM) THEN
  REWRITE_TAC[o_DEF; NORM_REAL; GSYM drop; LIFT_DROP]);;

let HAS_BOUNDED_REAL_VARIATION_ON_MAX = prove
 (`!f g s. f has_bounded_real_variation_on s /\
           g has_bounded_real_variation_on s
           ==> (\x. max (f x) (g x)) has_bounded_real_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_real_variation_on] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_BOUNDED_VARIATION_ON_MAX) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let HAS_BOUNDED_REAL_VARIATION_ON_MIN = prove
 (`!f g s. f has_bounded_real_variation_on s /\
           g has_bounded_real_variation_on s
           ==> (\x. min (f x) (g x)) has_bounded_real_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_real_variation_on] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_BOUNDED_VARIATION_ON_MIN) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let HAS_BOUNDED_REAL_VARIATION_ON_IMP_BOUNDED_ON_INTERVAL = prove
 (`!f a b. f has_bounded_real_variation_on real_interval[a,b]
           ==> real_bounded(IMAGE f (real_interval[a,b]))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_bounded_real_variation_on; REAL_BOUNDED] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
    HAS_BOUNDED_VARIATION_ON_IMP_BOUNDED_ON_INTERVAL) THEN
  REWRITE_TAC[IMAGE_o; IMAGE_DROP_INTERVAL; LIFT_DROP]);;

let HAS_BOUNDED_REAL_VARIATION_ON_MUL = prove
 (`!f g a b.
        f has_bounded_real_variation_on real_interval[a,b] /\
        g has_bounded_real_variation_on real_interval[a,b]
        ==> (\x. f x * g x) has_bounded_real_variation_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_real_variation_on] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_BOUNDED_VARIATION_ON_MUL) THEN
  REWRITE_TAC[o_DEF; LIFT_CMUL; LIFT_DROP]);;

let REAL_VARIATION_POS_LE = prove
 (`!f s. f has_bounded_real_variation_on s ==> &0 <= real_variation s f`,
  REWRITE_TAC[real_variation; has_bounded_real_variation_on] THEN
  REWRITE_TAC[VECTOR_VARIATION_POS_LE]);;

let REAL_VARIATION_GE_ABS_FUNCTION = prove
 (`!f s a b.
        f has_bounded_real_variation_on s /\ real_segment[a,b] SUBSET s
        ==> abs(f b - f a) <= real_variation s f`,
  REWRITE_TAC[has_bounded_real_variation_on] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`lift o f o drop`; `IMAGE lift s`; `lift a`; `lift b`]
   VECTOR_VARIATION_GE_NORM_FUNCTION) THEN
  ASM_SIMP_TAC[GSYM IMAGE_LIFT_REAL_SEGMENT;
               IMAGE_EQ_EMPTY; IMAGE_SUBSET] THEN
  REWRITE_TAC[real_variation; o_THM; LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT]);;

let REAL_VARIATION_GE_FUNCTION = prove
 (`!f s a b.
        f has_bounded_real_variation_on s /\ real_segment[a,b] SUBSET s
        ==> f b - f a <= real_variation s f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
  ASM_MESON_TAC[REAL_VARIATION_GE_ABS_FUNCTION]);;

let REAL_VARIATION_MONOTONE = prove
 (`!f s t. f has_bounded_real_variation_on s /\ t SUBSET s
           ==> real_variation t f <= real_variation s f`,
  REWRITE_TAC[has_bounded_real_variation_on; real_variation] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_VARIATION_MONOTONE THEN
  ASM_SIMP_TAC[IMAGE_SUBSET]);;

let REAL_VARIATION_NEG = prove
 (`!f s. real_variation s (\x. --(f x)) = real_variation s f`,
  SIMP_TAC[real_variation; o_DEF; LIFT_NEG; VECTOR_VARIATION_NEG]);;

let REAL_VARIATION_TRIANGLE = prove
 (`!f g s. f has_bounded_real_variation_on s /\
           g has_bounded_real_variation_on s
           ==> real_variation s (\x. f x + g x)
               <= real_variation s f + real_variation s g`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_bounded_real_variation_on; real_variation] THEN
  DISCH_THEN(MP_TAC o MATCH_MP VECTOR_VARIATION_TRIANGLE) THEN
  REWRITE_TAC[o_DEF; LIFT_ADD]);;

let HAS_BOUNDED_REAL_VARIATION_ON_COMBINE = prove
 (`!f a b c.
        a <= c /\ c <= b
        ==> (f has_bounded_real_variation_on real_interval[a,b] <=>
             f has_bounded_real_variation_on real_interval[a,c] /\
             f has_bounded_real_variation_on real_interval[c,b])`,
  REWRITE_TAC[has_bounded_real_variation_on; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`lift o f o drop`; `lift a`; `lift b`; `lift c`]
        HAS_BOUNDED_VARIATION_ON_COMBINE) THEN
  ASM_REWRITE_TAC[LIFT_DROP; has_bounded_real_variation_on;
      IMAGE_LIFT_REAL_INTERVAL]);;

let REAL_VARIATION_COMBINE = prove
 (`!f a b c.
        a <= c /\ c <= b /\
        f has_bounded_real_variation_on real_interval[a,b]
        ==> real_variation (real_interval[a,c]) f +
            real_variation (real_interval[c,b]) f =
            real_variation (real_interval[a,b]) f`,
  REWRITE_TAC[has_bounded_real_variation_on; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`lift o f o drop`; `lift a`; `lift b`; `lift c`]
        VECTOR_VARIATION_COMBINE) THEN
  ASM_REWRITE_TAC[LIFT_DROP; real_variation; IMAGE_LIFT_REAL_INTERVAL]);;

let REAL_VARIATION_MINUS_FUNCTION_MONOTONE = prove
 (`!f a b c d.
        f has_bounded_real_variation_on real_interval[a,b] /\
        real_interval[c,d] SUBSET real_interval[a,b] /\
        ~(real_interval[c,d] = {})
        ==> real_variation (real_interval[c,d]) f - (f d - f c) <=
            real_variation (real_interval[a,b]) f - (f b - f a)`,
  REWRITE_TAC[has_bounded_real_variation_on; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`lift o f o drop`; `lift a`; `lift b`; `lift c`; `lift d`]
   VECTOR_VARIATION_MINUS_FUNCTION_MONOTONE) THEN
  ASM_SIMP_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; real_variation;
                IMAGE_EQ_EMPTY; IMAGE_SUBSET] THEN
  REWRITE_TAC[o_THM; LIFT_DROP; DROP_SUB]);;

let INCREASING_BOUNDED_REAL_VARIATION = prove
 (`!f a b.
      (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
             ==> f x <= f y)
      ==> f has_bounded_real_variation_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_bounded_real_variation_on] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC INCREASING_BOUNDED_VARIATION THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM FORALL_DROP; o_THM; LIFT_DROP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_MESON_TAC[]);;

let INCREASING_REAL_VARIATION = prove
 (`!f a b.
        ~(real_interval[a,b] = {}) /\
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> f x <= f y)
        ==> real_variation (real_interval[a,b]) f = f b - f a`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_variation; IMAGE_LIFT_REAL_INTERVAL] THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift a`; `lift b`]
        INCREASING_VECTOR_VARIATION) THEN
  REWRITE_TAC[o_THM; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[LIFT_DROP] THEN ASM_MESON_TAC[]);;

let HAS_BOUNDED_REAL_VARIATION_AFFINITY2_EQ = prove
 (`!m c f s.
        (\x. f (m * x + c)) has_bounded_real_variation_on


        IMAGE (\x. inv m * x + --(inv m * c)) s <=>
        m = &0 \/ f has_bounded_real_variation_on s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`m:real`; `lift c`; `lift o f o drop`; `IMAGE lift s`]
        HAS_BOUNDED_VARIATION_AFFINITY2_EQ) THEN
  REWRITE_TAC[o_DEF; has_bounded_real_variation_on; GSYM IMAGE_o;
   DROP_ADD; DROP_CMUL; LIFT_ADD; LIFT_CMUL; LIFT_NEG; LIFT_DROP]);;

let REAL_VARIATION_AFFINITY2 = prove
 (`!m c f s.
        real_variation (IMAGE (\x. inv m * x + --(inv m * c)) s)
                       (\x. f (m * x + c)) =
        if m = &0 then &0 else real_variation s f`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`m:real`; `lift c`; `lift o f o drop`; `IMAGE lift s`]
         VECTOR_VARIATION_AFFINITY2) THEN
  REWRITE_TAC[o_DEF; real_variation; GSYM IMAGE_o;
   DROP_ADD; DROP_CMUL; LIFT_ADD; LIFT_CMUL; LIFT_NEG; LIFT_DROP]);;

let HAS_BOUNDED_REAL_VARIATION_AFFINITY_EQ = prove
 (`!m c f s.
        (\x. f (m * x + c)) has_bounded_real_variation_on s <=>
        m = &0 \/ f has_bounded_real_variation_on IMAGE (\x. m * x + c) s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`m:real`; `lift c`; `lift o f o drop`; `IMAGE lift s`]
        HAS_BOUNDED_VARIATION_AFFINITY_EQ) THEN
  REWRITE_TAC[o_DEF; has_bounded_real_variation_on; GSYM IMAGE_o;
   DROP_ADD; DROP_CMUL; LIFT_ADD; LIFT_CMUL; LIFT_NEG; LIFT_DROP]);;

let REAL_VARIATION_AFFINITY = prove
 (`!m c f s.
        real_variation s (\x. f (m * x + c)) =
        if m = &0 then &0 else real_variation (IMAGE (\x. m * x + c) s) f`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`m:real`; `lift c`; `lift o f o drop`; `IMAGE lift s`]
         VECTOR_VARIATION_AFFINITY) THEN
  REWRITE_TAC[o_DEF; real_variation; GSYM IMAGE_o;
   DROP_ADD; DROP_CMUL; LIFT_ADD; LIFT_CMUL; LIFT_NEG; LIFT_DROP]);;

let HAS_BOUNDED_REAL_VARIATION_TRANSLATION2_EQ = prove
 (`!a f s.
      (\x. f(a + x)) has_bounded_real_variation_on (IMAGE (\x. --a + x) s) <=>
      f has_bounded_real_variation_on s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`lift a`; `lift o f o drop`; `IMAGE lift s`]
        HAS_BOUNDED_VARIATION_TRANSLATION2_EQ) THEN
  REWRITE_TAC[o_DEF; has_bounded_real_variation_on; GSYM IMAGE_o;
              DROP_ADD; LIFT_DROP; LIFT_ADD; LIFT_NEG]);;

let REAL_VARIATION_TRANSLATION2 = prove
 (`!a f s. real_variation (IMAGE (\x. --a + x) s) (\x. f(a + x)) =
           real_variation s f`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`lift a`; `lift o f o drop`; `IMAGE lift s`]
        VECTOR_VARIATION_TRANSLATION2) THEN
  REWRITE_TAC[o_DEF; real_variation; GSYM IMAGE_o;
              DROP_ADD; LIFT_DROP; LIFT_ADD; LIFT_NEG]);;

let HAS_BOUNDED_REAL_VARIATION_TRANSLATION_EQ = prove
 (`!a f s. (\x. f(a + x)) has_bounded_real_variation_on s <=>
           f has_bounded_real_variation_on (IMAGE (\x. a + x) s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`lift a`; `lift o f o drop`; `IMAGE lift s`]
        HAS_BOUNDED_VARIATION_TRANSLATION_EQ) THEN
  REWRITE_TAC[o_DEF; has_bounded_real_variation_on; GSYM IMAGE_o;
              DROP_ADD; LIFT_DROP; LIFT_ADD; LIFT_NEG]);;

let REAL_VARIATION_TRANSLATION = prove
 (`!a f s. real_variation s (\x. f(a + x)) =
           real_variation (IMAGE (\x. a + x) s) f`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`lift a`; `lift o f o drop`; `IMAGE lift s`]
        VECTOR_VARIATION_TRANSLATION) THEN
  REWRITE_TAC[o_DEF; real_variation; GSYM IMAGE_o;
              DROP_ADD; LIFT_DROP; LIFT_ADD; LIFT_NEG]);;

let HAS_BOUNDED_REAL_VARIATION_TRANSLATION_EQ_INTERVAL = prove
 (`!a f u v.
        (\x. f(a + x)) has_bounded_real_variation_on real_interval[u,v] <=>
        f has_bounded_real_variation_on real_interval[a+u,a+v]`,
  REWRITE_TAC[REAL_INTERVAL_TRANSLATION;
              HAS_BOUNDED_REAL_VARIATION_TRANSLATION_EQ]);;

let REAL_VARIATION_TRANSLATION_INTERVAL = prove
 (`!a f u v.
        real_variation (real_interval[u,v]) (\x. f(a + x)) =
        real_variation (real_interval[a+u,a+v]) f`,
  REWRITE_TAC[REAL_INTERVAL_TRANSLATION;
                REAL_VARIATION_TRANSLATION]);;

let HAS_BOUNDED_REAL_VARIATION_TRANSLATION = prove
 (`!f s a. f has_bounded_real_variation_on s
           ==> (\x. f(a + x)) has_bounded_real_variation_on
               (IMAGE (\x. --a + x) s)`,
  REWRITE_TAC[HAS_BOUNDED_REAL_VARIATION_TRANSLATION2_EQ]);;

let HAS_BOUNDED_REAL_VARIATION_REFLECT2_EQ = prove
 (`!f s. (\x. f(--x)) has_bounded_real_variation_on (IMAGE (--) s) <=>
         f has_bounded_real_variation_on s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`]
        HAS_BOUNDED_VARIATION_REFLECT2_EQ) THEN
  REWRITE_TAC[o_DEF; has_bounded_real_variation_on; GSYM IMAGE_o;
              DROP_NEG; LIFT_DROP; LIFT_NEG]);;

let REAL_VARIATION_REFLECT2 = prove
 (`!f s. real_variation (IMAGE (--) s) (\x. f(--x)) =
         real_variation s f`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`]
        VECTOR_VARIATION_REFLECT2) THEN
  REWRITE_TAC[o_DEF; real_variation; GSYM IMAGE_o;
              DROP_NEG; LIFT_DROP; LIFT_NEG]);;

let HAS_BOUNDED_REAL_VARIATION_REFLECT_EQ = prove
 (`!f s. (\x. f(--x)) has_bounded_real_variation_on s <=>
         f has_bounded_real_variation_on (IMAGE (--) s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`]
        HAS_BOUNDED_VARIATION_REFLECT_EQ) THEN
  REWRITE_TAC[o_DEF; has_bounded_real_variation_on; GSYM IMAGE_o;
              DROP_NEG; LIFT_DROP; LIFT_NEG]);;

let REAL_VARIATION_REFLECT = prove
 (`!f s. real_variation s (\x. f(--x)) =
         real_variation (IMAGE (--) s) f`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`]
        VECTOR_VARIATION_REFLECT) THEN
  REWRITE_TAC[o_DEF; real_variation; GSYM IMAGE_o;
              DROP_NEG; LIFT_DROP; LIFT_NEG]);;

let HAS_BOUNDED_REAL_VARIATION_REFLECT_EQ_INTERVAL = prove
 (`!f u v. (\x. f(--x)) has_bounded_real_variation_on real_interval[u,v] <=>
           f has_bounded_real_variation_on real_interval[--v,--u]`,
  REWRITE_TAC[GSYM REFLECT_REAL_INTERVAL;
              HAS_BOUNDED_REAL_VARIATION_REFLECT_EQ]);;

let REAL_VARIATION_REFLECT_INTERVAL = prove
 (`!f u v. real_variation (real_interval[u,v]) (\x. f(--x)) =
           real_variation (real_interval[--v,--u]) f`,
  REWRITE_TAC[GSYM REFLECT_REAL_INTERVAL; REAL_VARIATION_REFLECT]);;

let HAS_BOUNDED_REAL_VARIATION_DARBOUX = prove
 (`!f a b.
     f has_bounded_real_variation_on real_interval[a,b] <=>
     ?g h. (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
                  ==> g x <= g y) /\
           (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
                  ==> h x <= h y) /\
           (!x. f x = g x - h x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_real_variation_on] THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_DARBOUX; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE;
              GSYM IMAGE_LIFT_REAL_INTERVAL; LIFT_DROP] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM; o_THM] THENL
   [MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`drop o g o lift`; `drop o h o lift`] THEN
    ASM_REWRITE_TAC[o_THM] THEN REWRITE_TAC[GSYM LIFT_EQ; FORALL_DROP] THEN
    ASM_REWRITE_TAC[LIFT_DROP; LIFT_SUB];
    MAP_EVERY X_GEN_TAC [`g:real->real`; `h:real->real`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`lift o g o drop`; `lift o h o drop`] THEN
    ASM_REWRITE_TAC[o_THM; LIFT_DROP] THEN REWRITE_TAC[LIFT_SUB]]);;

let HAS_BOUNDED_REAL_VARIATION_DARBOUX_STRICT = prove
 (`!f a b.
     f has_bounded_real_variation_on real_interval[a,b] <=>
     ?g h. (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x < y
                  ==> g x < g y) /\
           (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x < y
                  ==> h x < h y) /\
           (!x. f x = g x - h x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_real_variation_on] THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_DARBOUX_STRICT;
              IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE;
              GSYM IMAGE_LIFT_REAL_INTERVAL; LIFT_DROP] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM; o_THM] THENL
   [MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`drop o g o lift`; `drop o h o lift`] THEN
    ASM_REWRITE_TAC[o_THM] THEN REWRITE_TAC[GSYM LIFT_EQ; FORALL_DROP] THEN
    ASM_REWRITE_TAC[LIFT_DROP; LIFT_SUB];
    MAP_EVERY X_GEN_TAC [`g:real->real`; `h:real->real`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`lift o g o drop`; `lift o h o drop`] THEN
    ASM_REWRITE_TAC[o_THM; LIFT_DROP] THEN REWRITE_TAC[LIFT_SUB]]);;

let INCREASING_LEFT_LIMIT = prove
 (`!f a b c.
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> f x <= f y) /\
        c IN real_interval[a,b]
       ==> ?l. (f ---> l) (atreal c within real_interval[a,c])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TENDSTO_REAL; GSYM EXISTS_LIFT] THEN
  REWRITE_TAC[LIM_WITHINREAL_WITHIN; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC INCREASING_LEFT_LIMIT_1 THEN EXISTS_TAC `lift b` THEN
  SIMP_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP; FUN_IN_IMAGE]);;

let DECREASING_LEFT_LIMIT = prove
 (`!f a b c.
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> f y <= f x) /\
        c IN real_interval[a,b]
        ==> ?l. (f ---> l) (atreal c within real_interval[a,c])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TENDSTO_REAL; GSYM EXISTS_LIFT] THEN
  REWRITE_TAC[LIM_WITHINREAL_WITHIN; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC DECREASING_LEFT_LIMIT_1 THEN EXISTS_TAC `lift b` THEN
  SIMP_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP; FUN_IN_IMAGE]);;

let INCREASING_RIGHT_LIMIT = prove
 (`!f a b c.
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> f x <= f y) /\
        c IN real_interval[a,b]
       ==> ?l. (f ---> l) (atreal c within real_interval[c,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TENDSTO_REAL; GSYM EXISTS_LIFT] THEN
  REWRITE_TAC[LIM_WITHINREAL_WITHIN; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC INCREASING_RIGHT_LIMIT_1 THEN EXISTS_TAC `lift a` THEN
  SIMP_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP; FUN_IN_IMAGE]);;

let DECREASING_RIGHT_LIMIT = prove
 (`!f a b c.
        (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
               ==> f y <= f x) /\
        c IN real_interval[a,b]
        ==> ?l. (f ---> l) (atreal c within real_interval[c,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TENDSTO_REAL; GSYM EXISTS_LIFT] THEN
  REWRITE_TAC[LIM_WITHINREAL_WITHIN; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC DECREASING_RIGHT_LIMIT_1 THEN EXISTS_TAC `lift a` THEN
  SIMP_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP; FUN_IN_IMAGE]);;

let HAS_BOUNDED_REAL_VARIATION_LEFT_LIMIT = prove
 (`!f a b c.
        f has_bounded_real_variation_on real_interval[a,b] /\
        c IN real_interval[a,b]
        ==> ?l. (f ---> l) (atreal c within real_interval[a,c])`,
  REWRITE_TAC[has_bounded_real_variation_on] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[TENDSTO_REAL; GSYM EXISTS_LIFT] THEN
  REWRITE_TAC[LIM_WITHINREAL_WITHIN; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC HAS_BOUNDED_VECTOR_VARIATION_LEFT_LIMIT THEN
  EXISTS_TAC `lift b` THEN
  ASM_SIMP_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; GSYM o_ASSOC; FUN_IN_IMAGE]);;

let HAS_BOUNDED_REAL_VARIATION_RIGHT_LIMIT = prove
 (`!f a b c.
        f has_bounded_real_variation_on real_interval[a,b] /\
        c IN real_interval[a,b]
        ==> ?l. (f ---> l) (atreal c within real_interval[c,b])`,
  REWRITE_TAC[has_bounded_real_variation_on] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[TENDSTO_REAL; GSYM EXISTS_LIFT] THEN
  REWRITE_TAC[LIM_WITHINREAL_WITHIN; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC HAS_BOUNDED_VECTOR_VARIATION_RIGHT_LIMIT THEN
  EXISTS_TAC `lift a` THEN
  ASM_SIMP_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; GSYM o_ASSOC; FUN_IN_IMAGE]);;

let REAL_VARIATION_CONTINUOUS_LEFT = prove
 (`!f a b c.
        f has_bounded_real_variation_on real_interval[a,b] /\
        c IN real_interval[a,b]
        ==> ((\x. real_variation(real_interval[a,x]) f)
             real_continuous (atreal c within real_interval[a,c]) <=>
            f real_continuous (atreal c within real_interval[a,c]))`,
  REWRITE_TAC[has_bounded_real_variation_on; real_variation] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL;
        REAL_CONTINUOUS_CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VECTOR_VARIATION_CONTINUOUS_LEFT THEN
  EXISTS_TAC `lift b` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; FUN_IN_IMAGE]);;

let REAL_VARIATION_CONTINUOUS_RIGHT = prove
 (`!f a b c.
        f has_bounded_real_variation_on real_interval[a,b] /\
        c IN real_interval[a,b]
        ==> ((\x. real_variation(real_interval[a,x]) f)
             real_continuous (atreal c within real_interval[c,b]) <=>
            f real_continuous (atreal c within real_interval[c,b]))`,
  REWRITE_TAC[has_bounded_real_variation_on; real_variation] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL;
        REAL_CONTINUOUS_CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VECTOR_VARIATION_CONTINUOUS_RIGHT THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; FUN_IN_IMAGE]);;

let REAL_VARIATION_CONTINUOUS = prove
 (`!f a b c.
        f has_bounded_real_variation_on real_interval[a,b] /\
        c IN real_interval[a,b]
        ==> ((\x. real_variation(real_interval[a,x]) f)
             real_continuous (atreal c within real_interval[a,b]) <=>
            f real_continuous (atreal c within real_interval[a,b]))`,
  REWRITE_TAC[has_bounded_real_variation_on; real_variation] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL;
        REAL_CONTINUOUS_CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VECTOR_VARIATION_CONTINUOUS THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; FUN_IN_IMAGE]);;

let HAS_BOUNDED_REAL_VARIATION_DARBOUX_STRONG = prove
 (`!f a b.
     f has_bounded_real_variation_on real_interval[a,b]
     ==> ?g h.
          (!x. f x = g x - h x) /\
          (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
                 ==> g x <= g y) /\
          (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x <= y
                 ==> h x <= h y) /\
          (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x < y
                 ==> g x < g y) /\
          (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x < y
                 ==> h x < h y) /\
          (!x. x IN real_interval[a,b] /\
               f real_continuous (atreal x within real_interval[a,x])
               ==> g real_continuous (atreal x within real_interval[a,x]) /\
                   h real_continuous (atreal x within real_interval[a,x])) /\
          (!x. x IN real_interval[a,b] /\
               f real_continuous (atreal x within real_interval[x,b])
               ==> g real_continuous (atreal x within real_interval[x,b]) /\
                   h real_continuous (atreal x within real_interval[x,b])) /\
          (!x. x IN real_interval[a,b] /\
               f real_continuous (atreal x within real_interval[a,b])
               ==> g real_continuous (atreal x within real_interval[a,b]) /\
                   h real_continuous (atreal x within real_interval[a,b]))`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x. x + real_variation (real_interval[a,x]) f`;
    `\x. x + real_variation (real_interval[a,x]) f - f x`] THEN
  REWRITE_TAC[REAL_ARITH `(x + l) - (x + l - f):real = f`] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_VARIATION_MONOTONE;
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x. a - (b - x) <= c - (d - x) ==> a - b <= c - d`) THEN
    EXISTS_TAC `(f:real->real) a` THEN
    MATCH_MP_TAC REAL_VARIATION_MINUS_FUNCTION_MONOTONE;
    MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_VARIATION_MONOTONE;
    MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x. a - (b - x) <= c - (d - x) ==> a - b <= c - d`) THEN
    EXISTS_TAC `(f:real->real) a` THEN
    MATCH_MP_TAC REAL_VARIATION_MINUS_FUNCTION_MONOTONE;
    MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN
    REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID] THEN
    MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`; `x:real`]
        REAL_VARIATION_CONTINUOUS_LEFT) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN
    REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`; `x:real`]
        REAL_VARIATION_CONTINUOUS_LEFT) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN
    REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID] THEN
    MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`; `x:real`]
        REAL_VARIATION_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN
    REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`; `x:real`]
        REAL_VARIATION_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN
    REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID] THEN
    MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`; `x:real`]
        REAL_VARIATION_CONTINUOUS) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN
    REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`; `x:real`]
        REAL_VARIATION_CONTINUOUS) THEN
    ASM_REWRITE_TAC[]] THEN
  (CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_BOUNDED_REAL_VARIATION_ON_SUBSET));
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN
    ASM_REAL_ARITH_TAC));;

let HAS_BOUNDED_REAL_VARIATION_COUNTABLE_DISCONTINUITIES = prove
 (`!f a b. f has_bounded_real_variation_on real_interval[a,b]
           ==> COUNTABLE {x | x IN real_interval[a,b] /\
                              ~(f real_continuous atreal x)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_real_variation_on] THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN DISCH_THEN(MP_TAC o
    MATCH_MP HAS_BOUNDED_VARIATION_COUNTABLE_DISCONTINUITIES) THEN
  DISCH_THEN(MP_TAC o ISPEC `drop` o MATCH_MP COUNTABLE_IMAGE) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_LIFT; LIFT_DROP; UNWIND_THM1] THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IN_ELIM_THM] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; GSYM CONJ_ASSOC; EXISTS_DROP; LIFT_DROP] THEN
  MESON_TAC[LIFT_DROP]);;

let REAL_INTEGRABLE_REAL_BOUNDED_VARIATION_PRODUCT = prove
 (`!f g a b.
        f real_integrable_on real_interval[a,b] /\
        g has_bounded_real_variation_on real_interval[a,b]
        ==> (\x. g x * f x) real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_bounded_real_variation_on; REAL_INTEGRABLE_ON] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_CMUL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_BOUNDED_VARIATION_PRODUCT) THEN
  REWRITE_TAC[LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Lebesgue density theorem. This isn't about R specifically, but it's most  *)
(* naturally stated as a real limit so it ends up here in this file.         *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_DENSITY_THEOREM = prove
 (`!s:real^N->bool.
      lebesgue_measurable s
      ==> ?k. negligible k /\
              !x. ~(x IN k)
                  ==> ((\e. measure(s INTER cball(x,e)) / measure(cball(x,e)))
                       ---> (if x IN s then &1 else &0))
                      (atreal(&0) within {e | &0 < e})`,
  REPEAT STRIP_TAC THEN MP_TAC (ISPEC
   `indicator(s:real^N->bool)` ABSOLUTELY_INTEGRABLE_LEBESGUE_POINTS) THEN
  ANTS_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[indicator] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
     [MESON_TAC[VEC_COMPONENT; REAL_POS]; ALL_TAC] THEN
    REWRITE_TAC[INTEGRABLE_RESTRICT_INTER] THEN
    ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
    REWRITE_TAC[GSYM MEASURABLE_INTEGRABLE] THEN
    MATCH_MP_TAC MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE THEN
    ASM_REWRITE_TAC[MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`x:real^N`; `e / &(dimindex(:N)) pow dimindex(:N)`]) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT;
               REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ;  REAL_POW_LT;
           REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS) THEN
  ASM_SIMP_TAC[MEASURE_CBALL_POS; REAL_FIELD
   `&0 < y ==> x / y - a = inv(y) * (x - a * y)`] THEN
  REWRITE_TAC[REAL_ABS_MUL; NORM_MUL] THEN ONCE_REWRITE_TAC
   [REAL_ARITH `x <= (abs a * b) * c <=> x <= (abs(a) * c) * b`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL
   [SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_POW_LT;
             REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1] THEN
    REWRITE_TAC[REAL_ABS_INV; real_div; GSYM REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_ABS_NZ; CONTENT_EQ_0] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
                  VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[real_abs; CONTENT_POS_LE; MEASURE_POS_LE; MEASURABLE_CBALL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `measure(interval[x - h / &(dimindex(:N)) % vec 1:real^N,
                                   x + h / &(dimindex(:N)) % vec 1]) *
                  &(dimindex (:N)) pow dimindex (:N)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
        REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
                    VECTOR_SUB_COMPONENT; REAL_MUL_RID] THEN
        ASM_SIMP_TAC[REAL_ARITH `x - h <= x + h <=> &0 <= h`;
                     REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
        REWRITE_TAC[REAL_ARITH `(x + h) - (x - h) = &2 * h`;
                    PRODUCT_CONST_NUMSEG_1; REAL_POW_DIV; REAL_POW_MUL] THEN
        MATCH_MP_TAC(REAL_ARITH `x = y ==> y <= x`) THEN
        REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC REAL_DIV_RMUL THEN
        REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; DIMINDEX_NONZERO];
        MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[REAL_POS; REAL_POW_LE] THEN
        MATCH_MP_TAC MEASURE_SUBSET THEN
        REWRITE_TAC[MEASURABLE_INTERVAL; MEASURABLE_CBALL] THEN
        REWRITE_TAC[SUBSET; IN_INTERVAL; IN_CBALL] THEN
        X_GEN_TAC `y:real^N` THEN
        REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
                    VECTOR_SUB_COMPONENT; REAL_MUL_RID; REAL_ARITH
                     `x - h <= y /\ y <= x + h <=> abs(x - y) <= h`] THEN
        STRIP_TAC THEN REWRITE_TAC[dist] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `sum(1..dimindex(:N)) (\i. abs((x - y:real^N)$i))` THEN
        REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_BOUND_GEN THEN
        ASM_REWRITE_TAC[CARD_NUMSEG_1; VECTOR_SUB_COMPONENT; IN_NUMSEG] THEN
        REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1]]];
    REWRITE_TAC[NORM_REAL; GSYM drop] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (cball(x:real^N,h))
                   (\t. lift(norm(indicator s t - indicator s x))))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[MEASURE_INTEGRAL; MEASURABLE_CBALL;
                   MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE] THEN
      REWRITE_TAC[GSYM INTEGRAL_RESTRICT_INTER; GSYM DROP_CMUL] THEN
      SIMP_TAC[GSYM INTEGRAL_CMUL; GSYM MEASURABLE; MEASURABLE_CBALL] THEN
      REWRITE_TAC[GSYM DROP_SUB; COND_RATOR; COND_RAND] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
      ASM_SIMP_TAC[GSYM INTEGRAL_SUB; INTEGRABLE_RESTRICT_INTER;
                   GSYM MEASURABLE; MEASURABLE_CBALL; INTEGRABLE_ON_CONST;
                   MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE] THEN
      REWRITE_TAC[GSYM NORM_REAL; drop] THEN REWRITE_TAC[GSYM drop] THEN
      MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRABLE_RESTRICT_INTER;
                   GSYM MEASURABLE; MEASURABLE_CBALL; INTEGRABLE_ON_CONST;
                   MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        GEN_TAC THEN DISCH_TAC THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[indicator]) THEN
        REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP; DROP_VEC] THEN
        REAL_ARITH_TAC];
      REWRITE_TAC[NORM_REAL; GSYM drop; LIFT_DROP] THEN
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_CBALL; IN_INTERVAL] THEN
        REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
                    VECTOR_SUB_COMPONENT; REAL_MUL_RID; REAL_ARITH
                       `x - h <= y /\ y <= x + h <=> abs(x - y) <= h`] THEN
        REWRITE_TAC[dist; GSYM VECTOR_SUB_COMPONENT] THEN
        MESON_TAC[REAL_LE_TRANS; COMPONENT_LE_NORM];
        ALL_TAC;
        ALL_TAC;
        REWRITE_TAC[LIFT_DROP; REAL_ABS_POS]]]] THEN
  REWRITE_TAC[GSYM NORM_REAL; drop] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
  MATCH_MP_TAC(INST_TYPE [`:1`,`:P`]
    ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND) THEN
  EXISTS_TAC `(\x. vec 1):real^N->real^1` THEN

  REWRITE_TAC[DROP_VEC; GSYM MEASURABLE; MEASURABLE_INTERVAL;
              MEASURABLE_CBALL] THEN
  (CONJ_TAC THENL
    [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[indicator] THEN
     REPEAT(COND_CASES_TAC THEN
            ASM_REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; DROP_VEC]) THEN
     CONV_TAC REAL_RAT_REDUCE_CONV;
     ALL_TAC]) THEN
  MATCH_MP_TAC INTEGRABLE_SUB THEN
  REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_INTERVAL; MEASURABLE_CBALL] THEN
  REWRITE_TAC[indicator; INTEGRABLE_RESTRICT_INTER] THEN
  REWRITE_TAC[GSYM MEASURABLE] THEN
  ASM_SIMP_TAC[MEASURABLE_CBALL; MEASURABLE_INTERVAL;
               MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE]);;


print_endline "realanalysis.ml loaded"
