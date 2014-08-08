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
include Integration2

(* ------------------------------------------------------------------------- *)
(* Monotone convergence (bounded interval first).                            *)
(* ------------------------------------------------------------------------- *)

let MONOTONE_CONVERGENCE_INTERVAL = prove
 (`!f:num->real^N->real^1 g a b.
        (!k. (f k) integrable_on interval[a,b]) /\
        (!k x. x IN interval[a,b] ==> drop(f k x) <= drop(f (SUC k) x)) /\
        (!x. x IN interval[a,b] ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral (interval[a,b]) (f k) | k IN (:num)}
        ==> g integrable_on interval[a,b] /\
            ((\k. integral (interval[a,b]) (f k))
             --> integral (interval[a,b]) g) sequentially`,
  let lemma = prove
   (`{(x,y) | P x y} = {p | P (FST p) (SND p)}`,
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^N,b]) = &0` THENL
   [ASM_SIMP_TAC[INTEGRAL_NULL; INTEGRABLE_ON_NULL; LIM_CONST];
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONTENT_LT_NZ])] THEN
  SUBGOAL_THEN
   `!x:real^N k:num. x IN interval[a,b] ==> drop(f k x) <= drop(g x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
    EXISTS_TAC `\k. (f:num->real^N->real^1) k x` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `k:num` THEN SPEC_TAC(`k:num`,`k:num`) THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN REWRITE_TAC[REAL_LE_TRANS] THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?i. ((\k. integral (interval[a,b]) (f k:real^N->real^1)) --> i)
        sequentially`
  CHOOSE_TAC THENL
   [MATCH_MP_TAC BOUNDED_INCREASING_CONVERGENT THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. drop(integral(interval[a,b]) ((f:num->real^N->real^1) k)) <= drop i`
  ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
     EXISTS_TAC `\k. integral(interval[a,b]) ((f:num->real^N->real^1) k)` THEN
     ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
     EXISTS_TAC `k:num` THEN SPEC_TAC(`k:num`,`k:num`) THEN
     MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
     ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LE_TRANS] THEN
     GEN_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
  SUBGOAL_THEN
   `((g:real^N->real^1) has_integral i) (interval[a,b])`
  ASSUME_TAC THENL
   [REWRITE_TAC[has_integral] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
     [HAS_INTEGRAL_INTEGRAL]) THEN
    REWRITE_TAC[has_integral] THEN
    DISCH_THEN(MP_TAC o GEN `k:num` o
      SPECL [`k:num`; `e / &2 pow (k + 2)`]) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    GEN_REWRITE_TAC LAND_CONV [SKOLEM_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
    X_GEN_TAC `b:num->real^N->real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?r. !k. r:num <= k
               ==> &0 <= drop i - drop(integral(interval[a:real^N,b]) (f k)) /\
                   drop i - drop(integral(interval[a,b]) (f k)) < e / &4`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
      DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[ABS_DROP; dist; DROP_SUB] THEN
      MATCH_MP_TAC(REAL_ARITH
       `x <= y ==> abs(x - y) < e ==> &0 <= y - x /\ y - x < e`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN interval[a:real^N,b]
          ==> ?n. r:num <= n /\
                  !k. n <= k ==> &0 <= drop(g x) - drop(f k x) /\
                                 drop(g x) - drop(f k x) <
                                   e / (&4 * content(interval[a,b]))`
    MP_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (BINDER_CONV o RAND_CONV)
        [LIM_SEQUENTIALLY]) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_SIMP_TAC[REAL_SUB_LE] THEN
      DISCH_THEN(MP_TAC o SPEC `e / (&4 * content(interval[a:real^N,b]))`) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[dist; ABS_DROP; DROP_SUB] THEN
      ASM_SIMP_TAC[REAL_ARITH `f <= g ==> abs(f - g) = g - f`] THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
      EXISTS_TAC `N + r:num` THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[ARITH_RULE `N + r:num <= k ==> N <= k`];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    REWRITE_TAC[FORALL_AND_THM; TAUT
     `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real^N->num` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `d:real^N->real^N->bool = \x. b(m x:num) x` THEN
    EXISTS_TAC `d:real^N->real^N->bool` THEN CONJ_TAC THENL
     [EXPAND_TAC "d" THEN REWRITE_TAC[gauge] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [gauge]) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `p:(real^N#(real^N->bool))->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(NORM_ARITH
     `!b c. norm(a - b) <= e / &4 /\
            norm(b - c) < e / &2 /\
            norm(c - d) < e / &4
            ==> norm(a - d) < e`) THEN
    EXISTS_TAC `vsum p (\(x:real^N,k:real^N->bool).
                  content k % (f:num->real^N->real^1) (m x) x)` THEN
    EXISTS_TAC `vsum p (\(x:real^N,k:real^N->bool).
                  integral k ((f:num->real^N->real^1) (m x)))` THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    SUBGOAL_THEN `?s:num. !t:real^N#(real^N->bool). t IN p ==> m(FST t) <= s`
    MP_TAC THENL [ASM_SIMP_TAC[UPPER_BOUND_FINITE_SET]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN DISCH_THEN(X_CHOOSE_TAC `s:num`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM VSUM_SUB] THEN REWRITE_TAC[LAMBDA_PAIR_THM] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `y <= e ==> x <= y ==> x <= e`) THEN
      REWRITE_TAC[LAMBDA_PAIR_THM] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `sum p (\(x:real^N,k:real^N->bool).
                 content k * e / (&4 * content (interval[a:real^N,b])))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [`x:real^N`; `k:real^N->bool`] THEN
        DISCH_TAC THEN REWRITE_TAC[NORM_MUL; GSYM VECTOR_SUB_LDISTRIB] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN
        REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
        REWRITE_TAC[ABS_DROP; DROP_SUB] THEN
        REWRITE_TAC[REAL_ARITH `abs(x) <= x <=> &0 <= x`] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[CONTENT_POS_LE; TAGGED_DIVISION_OF]; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= g - f /\ g - f < e ==> abs(g - f) <= e`) THEN
        CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[TAGGED_DIVISION_OF; SUBSET];
        ALL_TAC] THEN
      REWRITE_TAC[LAMBDA_PAIR; SUM_RMUL] THEN REWRITE_TAC[LAMBDA_PAIR_THM] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP
       ADDITIVE_CONTENT_TAGGED_DIVISION th]) THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < content(interval[a:real^N,b])` THEN
      CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[GSYM VSUM_SUB] THEN REWRITE_TAC[LAMBDA_PAIR_THM] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
        `norm(vsum (0..s)
               (\j. vsum {(x:real^N,k:real^N->bool) | (x,k) IN p /\ m(x) = j}
                         (\(x,k). content k % f (m x) x :real^1 -
                                  integral k (f (m x)))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[lemma] THEN
        AP_TERM_TAC THEN MATCH_MP_TAC(GSYM VSUM_GROUP) THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; LE_0] THEN
        ASM_REWRITE_TAC[FORALL_PAIR_THM];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `sum (0..s) (\i. e / &2 pow (i + 2))` THEN CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[real_div; GSYM REAL_POW_INV; SUM_LMUL] THEN
        REWRITE_TAC[REAL_POW_ADD; SUM_RMUL] THEN REWRITE_TAC[SUM_GP] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_LT_LMUL_EQ; CONJUNCT1 LT] THEN
        REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x * y ==> (&1 - x) * y < y`) THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC REAL_POW_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `t:num` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
       `norm(vsum {x:real^N,k:real^N->bool | x,k IN p /\ m x:num = t}
                  (\(x,k). content k % f t x - integral k (f t)):real^1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
        MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM];
        ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
        HENSTOCK_LEMMA_PART1) THEN
      MAP_EVERY EXISTS_TAC
       [`a:real^N`; `b:real^N`; `(b(t:num)):real^N->real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TAGGED_PARTIAL_DIVISION_SUBSET THEN
        EXISTS_TAC `p:(real^N#(real^N->bool))->bool` THEN
        SIMP_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
        ASM_MESON_TAC[tagged_division_of];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      EXPAND_TAC "d" THEN REWRITE_TAC[fine; IN_ELIM_PAIR_THM] THEN MESON_TAC[];

      MP_TAC(ISPECL [`(f:num->real^N->real^1) s`; `a:real^N`; `b:real^N`;
                     `p:(real^N#(real^N->bool))->bool`]
                    INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN) THEN
      MP_TAC(ISPECL [`(f:num->real^N->real^1) r`; `a:real^N`; `b:real^N`;
                     `p:(real^N#(real^N->bool))->bool`]
                    INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN) THEN
      ASM_SIMP_TAC[ABS_DROP; DROP_SUB; DROP_VSUM; GSYM DROP_EQ] THEN
      REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM] THEN MATCH_MP_TAC(REAL_ARITH
       `sr <= sx /\ sx <= ss /\ ks <= i /\ &0 <= i - kr /\ i - kr < e
        ==> kr = sr ==> ks = ss ==> abs(sx - i) < e`) THEN
      ASM_SIMP_TAC[LE_REFL] THEN CONJ_TAC THEN MATCH_MP_TAC SUM_LE THEN
      ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `i:real^N->bool`] THEN DISCH_TAC THEN
      (SUBGOAL_THEN `i SUBSET interval[a:real^N,b]` ASSUME_TAC THENL
        [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
       SUBGOAL_THEN `?u v:real^N. i = interval[u,v]`
        (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
       THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC]) THEN
      MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      REPEAT(CONJ_TAC THENL
       [ASM_MESON_TAC[INTEGRABLE_SUBINTERVAL]; ALL_TAC]) THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPEC
        `\m n:num. drop (f m (y:real^N)) <= drop (f n y)`
        TRANSITIVE_STEPWISE_LE) THEN
      REWRITE_TAC[REAL_LE_TRANS; REAL_LE_REFL] THEN
      (ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC]) THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[TAGGED_DIVISION_OF; SUBSET]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[integrable_on]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  ASM_REWRITE_TAC[]);;

let MONOTONE_CONVERGENCE_INCREASING = prove
 (`!f:num->real^N->real^1 g s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`,
  SUBGOAL_THEN
   `!f:num->real^N->real^1 g s.
        (!k x. x IN s ==> &0 <= drop(f k x)) /\
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o ISPECL
     [`\n x:real^N. f(SUC n) x - f 0 x:real^1`;
      `\x. (g:real^N->real^1) x - f 0 x`; `s:real^N->bool`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_SUB; REAL_SUB_LE] THEN
      MP_TAC(ISPEC
        `\m n:num. drop (f m (x:real^N)) <= drop (f n x)`
        TRANSITIVE_STEPWISE_LE) THEN
      REWRITE_TAC[REAL_LE_TRANS; REAL_LE_REFL] THEN ASM_MESON_TAC[LE_0];
      GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_SUB; REAL_SUB_LE] THEN
      ASM_SIMP_TAC[REAL_ARITH `x - a <= y - a <=> x <= y`];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_SUB THEN SIMP_TAC[LIM_CONST] THEN
      REWRITE_TAC[ADD1] THEN
      MATCH_MP_TAC(ISPECL[`f:num->real^1`; `l:real^1`; `1`] SEQ_OFFSET) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
      ASM_SIMP_TAC[INTEGRAL_SUB; ETA_AX; bounded] THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real`
        (fun th -> EXISTS_TAC `B + norm(integral s (f 0:real^N->real^1))` THEN
                   X_GEN_TAC `k:num` THEN MP_TAC(SPEC `SUC k` th))) THEN
      NORM_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRAL_SUB; ETA_AX; IMP_CONJ] THEN
      SUBGOAL_THEN `(f 0:real^N->real^1) integrable_on s` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ONCE_REWRITE_TAC[IMP_IMP]] THEN
      DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_ADD) THEN
      REWRITE_TAC[ETA_AX; VECTOR_ARITH `f + (g - f):real^N = g`] THEN
      DISCH_TAC THEN ASM_SIMP_TAC[INTEGRAL_SUB; ETA_AX] THEN
      MP_TAC(ISPECL [`sequentially`; `integral s (f 0:real^N->real^1)`]
                    LIM_CONST) THEN
      REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD) THEN
      REWRITE_TAC[ETA_AX; VECTOR_ARITH `f + (g - f):real^N = g`] THEN
      REWRITE_TAC[ADD1] THEN
      SIMP_TAC[ISPECL[`f:num->real^1`; `l:real^1`; `1`] SEQ_OFFSET_REV]]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^N k:num. x IN s ==> drop(f k x) <= drop(g x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
    EXISTS_TAC `\k. (f:num->real^N->real^1) k x` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `k:num` THEN SPEC_TAC(`k:num`,`k:num`) THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN REWRITE_TAC[REAL_LE_TRANS] THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?i. ((\k. integral s (f k:real^N->real^1)) --> i)
        sequentially`
  CHOOSE_TAC THENL
   [MATCH_MP_TAC BOUNDED_INCREASING_CONVERGENT THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. drop(integral s ((f:num->real^N->real^1) k)) <= drop i`
  ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
     EXISTS_TAC `\k. integral(s) ((f:num->real^N->real^1) k)` THEN
     ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
     EXISTS_TAC `k:num` THEN SPEC_TAC(`k:num`,`k:num`) THEN
     MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
     ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LE_TRANS] THEN
     GEN_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
  SUBGOAL_THEN `((g:real^N->real^1) has_integral i) s` ASSUME_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL [ASM_MESON_TAC[integrable_on]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[HAS_INTEGRAL_ALT] THEN
  MP_TAC(ISPECL
   [`\k x. if x IN s then (f:num->real^N->real^1) k x else vec 0`;
    `\x. if x IN s then (g:real^N->real^1) x else vec 0`]
   (MATCH_MP(MESON[] `(!a b c d. P a b c d ==> Q a b c d)
                      ==> !a b. (!c d. P a b c d) ==> (!c d. Q a b c d)`)
            MONOTONE_CONVERGENCE_INTERVAL)) THEN
  ANTS_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [INTEGRABLE_ALT]) THEN
      SIMP_TAC[];
      DISCH_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LIM_CONST];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[ABS_DROP] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 <= y /\ y <= x ==> abs(x) <= a ==> abs(y) <= a`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_REFL; DROP_VEC];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; IN_UNIV] THEN
    ASM_REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; ETA_AX] THEN
    GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL; DROP_VEC; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
  ASM_SIMP_TAC[dist; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
   [HAS_INTEGRAL_INTEGRAL]) THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [HAS_INTEGRAL_ALT] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`N:num`; `e / &4`]) THEN
  ASM_SIMP_TAC[dist; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ARITH_RULE `N:num <= N`)) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (NORM_ARITH
   `norm(x - y) < e / &4 /\ norm(z - x) < e / &4
    ==> norm(z - y) < e / &2`)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (BINDER_CONV o BINDER_CONV)
        [LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `e / &2`]) THEN
  ASM_REWRITE_TAC[dist; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `M + N:num`)) THEN
  REWRITE_TAC[LE_ADD; ABS_DROP; DROP_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH
   `f1 <= f2 /\ f2 <= i
    ==> abs(f2 - g) < e / &2 ==> abs(f1 - i) < e / &2 ==> abs(g - i) < e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MP_TAC(ISPEC
        `\m n:num. drop (f m (x:real^N)) <= drop (f n x)`
        TRANSITIVE_STEPWISE_LE) THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_LE_TRANS] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s ((f:num->real^N->real^1) (M + N)))` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; IN_UNIV] THEN
  ASM_REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; ETA_AX] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_LE_REFL; DROP_VEC; REAL_LE_REFL]);;

let MONOTONE_CONVERGENCE_DECREASING = prove
 (`!f:num->real^N->real^1 g s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f (SUC k) x) <= drop(f k x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`(\k x. --(f k x)):num->real^N->real^1`;
    `(\x. --(g x)):real^N->real^1`; `s:real^N->bool`]
        MONOTONE_CONVERGENCE_INCREASING) THEN
  FIRST_ASSUM MP_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (c ==> d) ==> a ==> (b ==> c) ==> d`) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
     [MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_NEG) THEN REWRITE_TAC[];
      SIMP_TAC[DROP_NEG; REAL_LE_NEG2];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_NEG THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (\x. --x)
                      {integral s (f k:real^N->real^1) | k IN (:num)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_LINEAR_IMAGE THEN
      ASM_SIMP_TAC[LINEAR_COMPOSE_NEG; LINEAR_ID];
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN
      GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
      MATCH_MP_TAC INTEGRAL_NEG THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o MATCH_MP INTEGRABLE_NEG) (MP_TAC o MATCH_MP LIM_NEG)) THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  BINOP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN TRY GEN_TAC THEN
  MATCH_MP_TAC(VECTOR_ARITH `x:real^N = --y ==> --x = y`) THEN
  MATCH_MP_TAC INTEGRAL_NEG THEN ASM_REWRITE_TAC[]);;

let MONOTONE_CONVERGENCE_INCREASING_AE = prove
 (`!f:num->real^N->real^1 g s t.
        (!k. (f k) integrable_on s) /\
        negligible t /\
        (!k x. x IN s DIFF t ==> drop(f k x) <= drop(f (SUC k) x)) /\
        (!x. x IN s DIFF t ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n x. if x IN t then vec 0
           else (f:num->real^N->real^1) n x`;
    `\x. if x IN t then vec 0
           else (g:real^N->real^1) x`; `s:real^N->bool`]
        MONOTONE_CONVERGENCE_INCREASING) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `(f:num->real^N->real^1) k` THEN
      EXISTS_TAC `t:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF];
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^N) IN t` THEN ASM_REWRITE_TAC[LIM_CONST] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        BOUNDED_SUBSET)) THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> f x = g x)
        ==> {f x | x IN s} SUBSET {g x | x IN s}`) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC `t:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF]];
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SPIKE THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF]]]);;

let MONOTONE_CONVERGENCE_DECREASING_AE = prove
 (`!f:num->real^N->real^1 g s t.
        (!k. (f k) integrable_on s) /\
        negligible t /\
        (!k x. x IN s DIFF t ==> drop(f (SUC k) x) <= drop(f k x)) /\
        (!x. x IN s DIFF t ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n x. if x IN t then vec 0
           else (f:num->real^N->real^1) n x`;
    `\x. if x IN t then vec 0
           else (g:real^N->real^1) x`; `s:real^N->bool`]
        MONOTONE_CONVERGENCE_DECREASING) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `(f:num->real^N->real^1) k` THEN
      EXISTS_TAC `t:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF];
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^N) IN t` THEN ASM_REWRITE_TAC[LIM_CONST] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        BOUNDED_SUBSET)) THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> f x = g x)
        ==> {f x | x IN s} SUBSET {g x | x IN s}`) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC `t:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF]];
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SPIKE THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF]]]);;

(* ------------------------------------------------------------------------- *)
(* More lemmas about existence and bounds between integrals.                 *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_NORM_BOUND_INTEGRAL = prove
 (`!f:real^M->real^N g s.
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> norm(f x) <= drop(g x))
        ==> norm(integral s f) <= drop(integral s g)`,
  let lemma = prove
   (`(!e. &0 < e ==> x < y + e) ==> x <= y`,
    DISCH_THEN(MP_TAC o SPEC `x - y:real`) THEN REAL_ARITH_TAC) in
  SUBGOAL_THEN
   `!f:real^M->real^N g a b.
        f integrable_on interval[a,b] /\ g integrable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> norm(f x) <= drop(g x))
        ==> norm(integral(interval[a,b]) f) <= drop(integral(interval[a,b]) g)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(f:real^M->real^N) integrable_on interval[a,b]` THEN
    DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
    REWRITE_TAC[has_integral] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d1:real^M->real^M->bool` THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d2:real^M->real^M->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(ISPECL [`d1:real^M->real^M->bool`; `d2:real^M->real^M->bool`]
                  GAUGE_INTER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP FINE_DIVISION_EXISTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `b:real^M`]) THEN
    REWRITE_TAC[FINE_INTER; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `p:(real^M#(real^M->bool))->bool` THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `p:(real^M#(real^M->bool))->bool`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:(real^M#(real^M->bool))->bool`) THEN
    ASM_REWRITE_TAC[ABS_DROP; DROP_SUB] THEN MATCH_MP_TAC(NORM_ARITH
     `norm(sg) <= dsa
      ==> abs(dsa - dia) < e / &2 ==> norm(sg - ig) < e / &2
          ==> norm(ig) < dia + e`) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[DROP_VSUM] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
    ASM_REWRITE_TAC[o_DEF; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_MUL; DROP_CMUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
    REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
    ASM_MESON_TAC[CONTENT_POS_LE; TAGGED_DIVISION_OF; SUBSET];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th ->
     ASSUME_TAC(CONJUNCT1(GEN_REWRITE_RULE I [INTEGRABLE_ALT] th)) THEN
     MP_TAC(MATCH_MP INTEGRABLE_INTEGRAL th))) THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL] THEN
  DISCH_THEN(LABEL_TAC "A") THEN DISCH_TAC THEN MATCH_MP_TAC lemma THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REMOVE_THEN "A" (MP_TAC o SPEC `e / &2`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A"))) THEN
  MP_TAC(ISPEC `ball(vec 0,max B1 B2):real^M->bool`
    BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[BOUNDED_BALL; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[BALL_MAX_UNION; UNION_SUBSET] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  DISCH_THEN(CONJUNCTS_THEN(ANTE_RES_THEN MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^1` (CONJUNCTS_THEN2 ASSUME_TAC
     (fun th -> DISCH_THEN(X_CHOOSE_THEN `w:real^N`
                (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN MP_TAC th))) THEN
  ASM_REWRITE_TAC[ABS_DROP; DROP_SUB] THEN MATCH_MP_TAC(NORM_ARITH
     `norm(sg) <= dsa
      ==> abs(dsa - dia) < e / &2 ==> norm(sg - ig) < e / &2
          ==> norm(ig) < dia + e`) THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP INTEGRAL_UNIQUE)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0; DROP_VEC; REAL_LE_REFL]);;

let INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT = prove
 (`!f:real^M->real^N g:real^M->real^P s k.
        1 <= k /\ k <= dimindex(:P) /\
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> norm(f x) <= (g x)$k)
        ==> norm(integral s f) <= (integral s g)$k`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s ((\y. lift(y$k)) o (g:real^M->real^P)))` THEN
  SUBGOAL_THEN `linear(\y:real^P. lift(y$k))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                 LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[o_THM; LIFT_DROP] THEN MATCH_MP_TAC INTEGRABLE_LINEAR THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s ((\y. lift (y$k)) o (g:real^M->real^P)) =
        (\y. lift (y$k)) (integral s g)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_LINEAR THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_DROP; REAL_LE_REFL]]);;

let HAS_INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT = prove
 (`!f:real^M->real^N g:real^M->real^P s i j k.
        1 <= k /\ k <= dimindex(:P) /\
        (f has_integral i) s /\ (g has_integral j) s /\
        (!x. x IN s ==> norm(f x) <= (g x)$k)
        ==> norm(i) <= j$k`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
   SUBST1_TAC(SYM(MATCH_MP INTEGRAL_UNIQUE th)) THEN
   ASSUME_TAC(MATCH_MP HAS_INTEGRAL_INTEGRABLE th))) THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT THEN
  ASM_REWRITE_TAC[]);;

let INTEGRABLE_ON_ALL_INTERVALS_INTEGRABLE_BOUND = prove
 (`!f:real^M->real^N g s.
        (!a b. (\x. if x IN s then f x else vec 0)
               integrable_on interval[a,b]) /\
        (!x. x IN s ==> norm(f x) <= drop(g x)) /\
        g integrable_on s
        ==> f integrable_on s`,
  let lemma = prove
   (`!f:real^M->real^N g.
          (!a b. f integrable_on interval[a,b]) /\
          (!x. norm(f x) <= drop(g x)) /\
          g integrable_on (:real^M)
          ==> f integrable_on (:real^M)`,
    REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ONCE_REWRITE_TAC[INTEGRABLE_ALT_SUBSET] THEN
    ASM_REWRITE_TAC[IN_UNIV; ETA_AX] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b < c ==> a < c`) THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_SIMP_TAC[GSYM INTEGRAL_DIFF; NEGLIGIBLE_EMPTY;
                 SET_RULE `s SUBSET t ==> s DIFF t = {}`] THEN
    REWRITE_TAC[ABS_DROP] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_MESON_TAC[integrable_on; HAS_INTEGRAL_DIFF; NEGLIGIBLE_EMPTY;
                 SET_RULE `s SUBSET t ==> s DIFF t = {}`]) in
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
  DISCH_TAC THEN MATCH_MP_TAC lemma THEN
  EXISTS_TAC `(\x. if x IN s then g x else vec 0):real^M->real^1` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0; DROP_VEC; REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* Explicit limit statement for integrals over [0,inf].                      *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_LIM_AT_POSINFINITY = prove
 (`!f l:real^N.
        (f has_integral l) {t | &0 <= drop t} <=>
        (!a. f integrable_on interval[vec 0,a]) /\
        ((\a. integral (interval[vec 0,lift a]) f) --> l) at_posinfinity`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_ALT] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_INTER; INTEGRABLE_RESTRICT_INTER] THEN
  SUBGOAL_THEN
   `!a b. {t | &0 <= drop t} INTER interval[a,b] =
          interval[lift(max (&0) (drop a)),b]`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[EXTENSION; FORALL_LIFT; IN_INTER; IN_INTERVAL_1;
                LIFT_DROP; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIM_AT_POSINFINITY; dist; real_ge] THEN
  EQ_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `a:real^1` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^1`; `a:real^1`]) THEN
    REWRITE_TAC[DROP_VEC; LIFT_NUM; REAL_ARITH `max x x = x`];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
    X_GEN_TAC `b:real` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPECL [`lift(--b)`; `lift b`]) THEN
    REWRITE_TAC[DROP_VEC; LIFT_NUM; LIFT_DROP] THEN
    SUBGOAL_THEN `max (&0) (--b) = &0` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[LIFT_NUM]] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[BALL_1; SUBSET_INTERVAL_1] THEN
    REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_VEC; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b:real^1`) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INTEGRABLE_SUBINTERVAL) THEN
    SIMP_TAC[SUBSET_INTERVAL_1; DROP_ADD; DROP_SUB; DROP_VEC; LIFT_DROP] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "*")) THEN
    EXISTS_TAC `abs B + &1` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN
    REWRITE_TAC[BALL_1; SUBSET_INTERVAL_1] THEN
    REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_VEC; LIFT_DROP] THEN
    STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `max (&0) (drop a) = &0` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[LIFT_NUM]] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop b`) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

let HAS_INTEGRAL_LIM_SEQUENTIALLY = prove
 (`!f:real^1->real^N l.
           (f o lift --> vec 0) at_posinfinity /\
           (!n. f integrable_on interval[vec 0,vec n]) /\
           ((\n. integral (interval[vec 0,vec n]) f) --> l) sequentially
           ==> (f has_integral l) {t | &0 <= drop t}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL_LIM_AT_POSINFINITY] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [X_GEN_TAC `a:real^1` THEN MP_TAC(SPEC `drop a` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INTEGRABLE_SUBINTERVAL) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  REWRITE_TAC[LIM_AT_POSINFINITY; real_ge] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_AT_POSINFINITY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF; o_THM; real_ge; FORALL_DROP; LIFT_DROP] THEN
  REWRITE_TAC[DIST_0; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `B:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `max (&N) B + &1` THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN MP_TAC(SPEC `drop x` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN
   `integral(interval[vec 0,x]) (f:real^1->real^N) =
    integral(interval[vec 0,vec n]) f + integral(interval[vec n,x]) f`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_COMBINE THEN
    ASM_REWRITE_TAC[DROP_VEC] THEN
    MP_TAC(SPEC `drop x` FLOOR) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `dist(a:real^N,l) < e / &2 /\ norm b <= e / &2 ==> dist(a + b,l) < e`) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    MP_TAC(SPEC `drop x` FLOOR) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
    `drop(integral(interval[vec n:real^1,x]) (\x. lift(e / &2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST; IN_INTERVAL_1; LIFT_DROP] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `interval[vec 0:real^1,x]` THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[DROP_VEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(SPEC `drop x` FLOOR) THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[INTEGRAL_CONST] THEN IMP_REWRITE_TAC[CONTENT_1] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM LIFT_CMUL; LIFT_DROP; DROP_VEC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      MP_TAC(SPEC `drop x` FLOOR) THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[DROP_VEC] THEN MP_TAC(SPEC `drop x` FLOOR) THEN
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Interval functions of bounded variation on a set.                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_bounded_setvariation_on",(12,"right"));;

let set_variation = new_definition
 `set_variation s (f:(real^M->bool)->real^N) =
        sup { sum d (\k. norm(f k)) | ?t. d division_of t /\ t SUBSET s}`;;

let has_bounded_setvariation_on = new_definition
  `(f:(real^M->bool)->real^N) has_bounded_setvariation_on s <=>
        ?B. !d t. d division_of t /\ t SUBSET s
                  ==> sum d (\k. norm(f k)) <= B`;;

let HAS_BOUNDED_SETVARIATION_ON = prove
 (`!f:(real^M->bool)->real^N s.
        f  has_bounded_setvariation_on s <=>
        ?B. &0 < B /\ !d t. d division_of t /\ t SUBSET s
                            ==> sum d (\k. norm(f k)) <= B`,
  REWRITE_TAC[has_bounded_setvariation_on] THEN
  MESON_TAC[REAL_ARITH `&0 < abs B + &1 /\ (x <= B ==> x <= abs B + &1)`]);;

let HAS_BOUNDED_SETVARIATION_ON_EQ = prove
 (`!f g:(real^M->bool)->real^N s.
        (!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s
               ==> f(interval[a,b]) = g(interval[a,b])) /\
        f has_bounded_setvariation_on s
        ==> g has_bounded_setvariation_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[has_bounded_setvariation_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `d:(real^M->bool)->bool` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^M->bool` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= B ==> y <= B`) THEN
  MATCH_MP_TAC SUM_EQ THEN FIRST_ASSUM(fun th ->
  GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[division_of; SUBSET_TRANS]);;

let SET_VARIATION_EQ = prove
 (`!f g:(real^M->bool)->real^N s.
        (!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s
               ==> f(interval[a,b]) = g(interval[a,b]))
        ==> set_variation s f = set_variation s g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[set_variation] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SUM_EQ THEN FIRST_ASSUM(fun th ->
  GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[division_of; SUBSET_TRANS]);;

let HAS_BOUNDED_SETVARIATION_ON_COMPONENTWISE = prove
 (`!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\k. lift(f k$i)) has_bounded_setvariation_on s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_bounded_setvariation_on; NORM_LIFT] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXISTS_TAC `B:real` THEN
    MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
      [`d:(real^M->bool)->bool`; `t:real^M->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
    ASM_MESON_TAC[DIVISION_OF_FINITE];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `B:num->real` THEN DISCH_TAC THEN
    EXISTS_TAC `sum (1..dimindex(:N)) B` THEN
    MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum d (\k. sum (1..dimindex(:N))
                           (\i. abs(((f:(real^M->bool)->real^N) k)$i)))` THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[SUM_LE; NORM_LE_L1] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_MESON_TAC[]]);;

let SETVARIATION_EQUAL_LEMMA = prove
 (`!mf:((real^M->bool)->real^N)->((real^M->bool)->real^N) ms ms'.
        (!s. ms'(ms s) = s /\ ms(ms' s) = s) /\
        (!f a b. ~(interval[a,b] = {})
                 ==> mf f (ms (interval[a,b])) = f (interval[a,b]) /\
                     ?a' b'. ~(interval[a',b'] = {}) /\
                             ms' (interval[a,b]) = interval[a',b']) /\
        (!t u. t SUBSET u ==> ms t SUBSET ms u /\ ms' t SUBSET ms' u) /\
        (!d t. d division_of t
               ==> (IMAGE ms d) division_of ms t /\
                   (IMAGE ms' d) division_of ms' t)
   ==> (!f s. (mf f) has_bounded_setvariation_on (ms s) <=>
              f has_bounded_setvariation_on s) /\
       (!f s. set_variation (ms s) (mf f) = set_variation s f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[has_bounded_setvariation_on; set_variation] THEN
  MATCH_MP_TAC(MESON[]
   `((!f s. s1 f s = s2 f s) ==> P) /\
    (!f s. s1 f s = s2 f s)
    ==> P /\ (!f s. sup (s1 f s) = sup (s2 f s))`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `IMAGE (ms':(real^M->bool)->real^M->bool) d`;
    EXISTS_TAC `IMAGE (ms:(real^M->bool)->real^M->bool) d`] THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[o_THM] THEN FIRST_ASSUM
   (fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN STRIP_TAC THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `?a' b':real^M. ~(interval[a',b'] = {}) /\
                        ms' (interval[a:real^M,b]) = interval[a',b']`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let HAS_BOUNDED_SETVARIATION_ON_ELEMENTARY = prove
 (`!f:(real^M->bool)->real^N s.
        (?d. d division_of s)
        ==> (f has_bounded_setvariation_on s <=>
             ?B. !d. d division_of s ==> sum d (\k. norm(f k)) <= B)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[has_bounded_setvariation_on] THEN EQ_TAC THEN
  MATCH_MP_TAC MONO_EXISTS THENL [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `d':(real^M->bool)->bool`) THEN
  MP_TAC(ISPECL [`d:(real^M->bool)->bool`; `d':(real^M->bool)->bool`;
             `t:real^M->bool`; `s:real^M->bool`] PARTIAL_DIVISION_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `d'':(real^M->bool)->bool`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d'' (\k:real^M->bool. norm(f k:real^N))` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_MESON_TAC[DIVISION_OF_FINITE]);;

let HAS_BOUNDED_SETVARIATION_ON_INTERVAL = prove
 (`!f:(real^M->bool)->real^N a b.
        f has_bounded_setvariation_on interval[a,b] <=>
        ?B. !d. d division_of interval[a,b] ==> sum d (\k. norm(f k)) <= B`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_BOUNDED_SETVARIATION_ON_ELEMENTARY THEN
  REWRITE_TAC[ELEMENTARY_INTERVAL]);;

let HAS_BOUNDED_SETVARIATION_ON_UNIV = prove
 (`!f:(real^M->bool)->real^N.
        f has_bounded_setvariation_on (:real^M) <=>
        ?B. !d. d division_of UNIONS d ==> sum d (\k. norm(f k)) <= B`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_bounded_setvariation_on; SUBSET_UNIV] THEN
  MESON_TAC[DIVISION_OF_UNION_SELF]);;

let HAS_BOUNDED_SETVARIATION_ON_SUBSET = prove
 (`!f:(real^M->bool)->real^N s t.
        f has_bounded_setvariation_on s /\ t SUBSET s
        ==> f has_bounded_setvariation_on t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[has_bounded_setvariation_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[SUBSET_TRANS]);;

let HAS_BOUNDED_SETVARIATION_ON_IMP_BOUNDED_ON_SUBINTERVALS = prove
 (`!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s
        ==> bounded { f(interval[c,d]) | interval[c,d] SUBSET s}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_setvariation_on; bounded] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `max (abs B) (norm((f:(real^M->bool)->real^N) {}))` THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^M`; `d:real^M`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `interval[c:real^M,d] = {}` THEN
  ASM_REWRITE_TAC[REAL_ARITH `a <= max b a`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`{interval[c:real^M,d]}`; `interval[c:real^M,d]`]) THEN
  ASM_SIMP_TAC[DIVISION_OF_SELF; SUM_SING] THEN REAL_ARITH_TAC);;

let HAS_BOUNDED_SETVARIATION_ON_NORM = prove
 (`!f:(real^M->bool)->real^N s.
        (\x. lift(norm(f x))) has_bounded_setvariation_on s <=>
        f has_bounded_setvariation_on s`,
  REWRITE_TAC[has_bounded_setvariation_on; NORM_REAL; GSYM drop] THEN
  REWRITE_TAC[REAL_ABS_NORM; LIFT_DROP]);;

let HAS_BOUNDED_SETVARIATION_ON_COMPOSE_LINEAR = prove
 (`!f:(real^M->bool)->real^N g:real^N->real^P s.
        f has_bounded_setvariation_on s /\ linear g
        ==> (g o f) has_bounded_setvariation_on s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`) ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `C:real` o MATCH_MP LINEAR_BOUNDED_POS) THEN
  EXISTS_TAC `B * C:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
  STRIP_TAC THEN REWRITE_TAC[o_THM] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d (\k. C * norm((f:(real^M->bool)->real^N) k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_MESON_TAC[DIVISION_OF_FINITE];
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[SUM_LMUL] THEN ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
    ASM_MESON_TAC[]]);;

let HAS_BOUNDED_SETVARIATION_ON_0 = prove
 (`!s:real^N->bool. (\x. vec 0) has_bounded_setvariation_on s`,
  REWRITE_TAC[has_bounded_setvariation_on; NORM_0; SUM_0] THEN
  MESON_TAC[REAL_LE_REFL]);;

let SET_VARIATION_0 = prove
 (`!s:real^N->bool. set_variation s (\x. vec 0) = &0`,
  GEN_TAC THEN REWRITE_TAC[set_variation; NORM_0; SUM_0] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SUP_SING] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
  MESON_TAC[ELEMENTARY_EMPTY; EMPTY_SUBSET]);;

let HAS_BOUNDED_SETVARIATION_ON_CMUL = prove
 (`!f:(real^M->bool)->real^N c s.
        f has_bounded_setvariation_on s
        ==> (\x. c % f x) has_bounded_setvariation_on s`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT; o_DEF]
     HAS_BOUNDED_SETVARIATION_ON_COMPOSE_LINEAR) THEN
  REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC);;

let HAS_BOUNDED_SETVARIATION_ON_NEG = prove
 (`!f:(real^M->bool)->real^N s.
        (\x. --(f x)) has_bounded_setvariation_on s <=>
        f has_bounded_setvariation_on s`,
  REWRITE_TAC[has_bounded_setvariation_on; NORM_NEG]);;

let HAS_BOUNDED_SETVARIATION_ON_ADD = prove
 (`!f:(real^M->bool)->real^N g s.
        f has_bounded_setvariation_on s /\
        g has_bounded_setvariation_on s
        ==> (\x. f x + g x) has_bounded_setvariation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_setvariation_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `B + C:real` THEN
  MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d (\k. norm((f:(real^M->bool)->real^N) k)) +
              sum d (\k. norm((g:(real^M->bool)->real^N) k))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_ADD2]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM SUM_ADD] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[NORM_TRIANGLE]);;

let HAS_BOUNDED_SETVARIATION_ON_SUB = prove
 (`!f:(real^M->bool)->real^N g s.
        f has_bounded_setvariation_on s /\
        g has_bounded_setvariation_on s
        ==> (\x. f x - g x) has_bounded_setvariation_on s`,
  REWRITE_TAC[VECTOR_ARITH `x - y:real^N = x + --y`] THEN
  SIMP_TAC[HAS_BOUNDED_SETVARIATION_ON_ADD; HAS_BOUNDED_SETVARIATION_ON_NEG]);;

let HAS_BOUNDED_SETVARIATION_ON_NULL = prove
 (`!f:(real^M->bool)->real^N s.
        (!a b. content(interval[a,b]) = &0 ==> f(interval[a,b]) = vec 0) /\
        content s = &0 /\ bounded s
        ==> f has_bounded_setvariation_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_bounded_setvariation_on] THEN
  EXISTS_TAC `&0` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &0`) THEN
  MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[NORM_EQ_0] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC CONTENT_0_SUBSET_GEN THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[division_of; SUBSET_TRANS]);;

let SET_VARIATION_ELEMENTARY_LEMMA = prove
 (`!f:(real^M->bool)->real^N s.
        (?d. d division_of s)
        ==> ((!d t. d division_of t /\ t SUBSET s
                    ==> sum d (\k. norm(f k)) <= b) <=>
             (!d. d division_of s ==> sum d (\k. norm(f k)) <= b))`,
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `d1:(real^M->bool)->bool`) THEN
  EQ_TAC THENL [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `d2:(real^M->bool)->bool` THEN
  X_GEN_TAC `t:real^M->bool` THEN STRIP_TAC THEN MP_TAC(ISPECL
   [`d2:(real^M->bool)->bool`; `d1:(real^M->bool)->bool`;
    `t:real^M->bool`; `s:real^M->bool`] PARTIAL_DIVISION_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `d3:(real^M->bool)->bool`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d3 (\k:real^M->bool. norm(f k:real^N))` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_MESON_TAC[DIVISION_OF_FINITE]);;

let SET_VARIATION_ON_ELEMENTARY = prove
 (`!f:(real^M->bool)->real^N s.
        (?d. d division_of s)
        ==> set_variation s f =
             sup { sum d (\k. norm(f k)) | d division_of s}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[set_variation; sup] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; LEFT_IMP_EXISTS_THM] THEN
  ASM_SIMP_TAC[SET_VARIATION_ELEMENTARY_LEMMA]);;

let SET_VARIATION_ON_INTERVAL = prove
 (`!f:(real^M->bool)->real^N a b.
        set_variation (interval[a,b]) f =
        sup { sum d (\k. norm(f k)) | d division_of interval[a,b]}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SET_VARIATION_ON_ELEMENTARY THEN
  REWRITE_TAC[ELEMENTARY_INTERVAL]);;

let HAS_BOUNDED_SETVARIATION_WORKS = prove
 (`!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s
        ==> (!d t. d division_of t /\ t SUBSET s
                   ==> sum d (\k. norm(f k)) <= set_variation s f) /\
            (!B. (!d t. d division_of t /\ t SUBSET s
                        ==> sum d (\k. norm (f k)) <= B)
                 ==> set_variation s f <= B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_setvariation_on] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `{ sum d (\k. norm((f:(real^M->bool)->real^N) k)) |
                  ?t. d division_of t /\ t SUBSET s}`
         SUP) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[set_variation] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`&0`; `{}:(real^M->bool)->bool`] THEN
  REWRITE_TAC[SUM_CLAUSES] THEN EXISTS_TAC `{}:real^M->bool` THEN
  SIMP_TAC[division_of; EMPTY_SUBSET; NOT_IN_EMPTY; FINITE_EMPTY; UNIONS_0]);;

let HAS_BOUNDED_SETVARIATION_WORKS_ON_ELEMENTARY = prove
 (`!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s /\ (?d. d division_of s)
        ==> (!d. d division_of s
                 ==> sum d (\k. norm(f k)) <= set_variation s f) /\
            (!B. (!d. d division_of s ==> sum d (\k. norm(f k)) <= B)
                 ==> set_variation s f <= B)`,
  SIMP_TAC[GSYM SET_VARIATION_ELEMENTARY_LEMMA] THEN
  MESON_TAC[HAS_BOUNDED_SETVARIATION_WORKS]);;

let HAS_BOUNDED_SETVARIATION_WORKS_ON_INTERVAL = prove
 (`!f:(real^M->bool)->real^N a b.
      f has_bounded_setvariation_on interval[a,b]
      ==> (!d. d division_of interval[a,b]
               ==> sum d (\k. norm(f k)) <= set_variation (interval[a,b]) f) /\
          (!B. (!d. d division_of interval[a,b]
                    ==> sum d (\k. norm(f k)) <= B)
               ==> set_variation (interval[a,b]) f <= B)`,
  SIMP_TAC[HAS_BOUNDED_SETVARIATION_WORKS_ON_ELEMENTARY; ELEMENTARY_INTERVAL]);;

let SET_VARIATION_UBOUND = prove
 (`!f:(real^M->bool)->real^N s B.
        f has_bounded_setvariation_on s /\
        (!d t. d division_of t /\ t SUBSET s ==> sum d (\k. norm(f k)) <= B)
        ==> set_variation s f <= B`,
  MESON_TAC[HAS_BOUNDED_SETVARIATION_WORKS]);;

let SET_VARIATION_UBOUND_ON_INTERVAL = prove
 (`!f:(real^M->bool)->real^N a b B.
        f has_bounded_setvariation_on interval[a,b] /\
        (!d. d division_of interval[a,b] ==> sum d (\k. norm(f k)) <= B)
        ==> set_variation (interval[a,b]) f <= B`,
  SIMP_TAC[GSYM SET_VARIATION_ELEMENTARY_LEMMA; ELEMENTARY_INTERVAL] THEN
  MESON_TAC[SET_VARIATION_UBOUND]);;

let SET_VARIATION_LBOUND = prove
 (`!f:(real^M->bool)->real^N s B.
        f has_bounded_setvariation_on s /\
        (?d t. d division_of t /\ t SUBSET s /\ B <= sum d (\k. norm(f k)))
        ==> B <= set_variation s f`,
  MESON_TAC[HAS_BOUNDED_SETVARIATION_WORKS; REAL_LE_TRANS]);;

let SET_VARIATION_LBOUND_ON_INTERVAL = prove
 (`!f:(real^M->bool)->real^N a b B.
        f has_bounded_setvariation_on interval[a,b] /\
        (?d. d division_of interval[a,b] /\ B <= sum d (\k. norm(f k)))
        ==> B <= set_variation (interval[a,b]) f`,
  MESON_TAC[HAS_BOUNDED_SETVARIATION_WORKS_ON_INTERVAL; REAL_LE_TRANS]);;

let SET_VARIATION = prove
 (`!f:(real^M->bool)->real^N s d t.
        f has_bounded_setvariation_on s /\ d division_of t /\ t SUBSET s
        ==> sum d (\k. norm(f k)) <= set_variation s f`,
  MESON_TAC[HAS_BOUNDED_SETVARIATION_WORKS]);;

let SET_VARIATION_WORKS_ON_INTERVAL = prove
 (`!f:(real^M->bool)->real^N a b d.
        f has_bounded_setvariation_on interval[a,b] /\
        d division_of interval[a,b]
        ==> sum d (\k. norm(f k)) <= set_variation (interval[a,b]) f`,
  MESON_TAC[HAS_BOUNDED_SETVARIATION_WORKS_ON_INTERVAL]);;

let SET_VARIATION_POS_LE = prove
 (`!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s ==> &0 <= set_variation s f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] SET_VARIATION)) THEN
  DISCH_THEN(MP_TAC o SPECL[`{}:(real^M->bool)->bool`; `{}:real^M->bool`]) THEN
  REWRITE_TAC[EMPTY_SUBSET; SUM_CLAUSES; DIVISION_OF_TRIVIAL]);;

let SET_VARIATION_GE_FUNCTION = prove
 (`!f:(real^M->bool)->real^N s a b.
        f has_bounded_setvariation_on s /\
        interval[a,b] SUBSET s /\ ~(interval[a,b] = {})
        ==> norm(f(interval[a,b])) <= set_variation s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SET_VARIATION_LBOUND THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `{interval[a:real^M,b]}` THEN
  EXISTS_TAC `interval[a:real^M,b]` THEN
  ASM_REWRITE_TAC[SUM_SING; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[DIVISION_OF_SELF]);;

let SET_VARIATION_ON_NULL = prove
 (`!f:(real^M->bool)->real^N s.
        (!a b. content(interval[a,b]) = &0 ==> f(interval[a,b]) = vec 0) /\
        content s = &0 /\ bounded s
        ==> set_variation s f = &0`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SET_VARIATION_UBOUND THEN
    ASM_SIMP_TAC[HAS_BOUNDED_SETVARIATION_ON_NULL] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &0`) THEN
    MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[NORM_EQ_0] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC CONTENT_0_SUBSET_GEN THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[division_of; SUBSET_TRANS];
    MATCH_MP_TAC SET_VARIATION_POS_LE THEN
    ASM_SIMP_TAC[HAS_BOUNDED_SETVARIATION_ON_NULL]]);;

let SET_VARIATION_TRIANGLE = prove
 (`!f:(real^M->bool)->real^N g s.
        f has_bounded_setvariation_on s /\
        g has_bounded_setvariation_on s
        ==> set_variation s (\x. f x + g x)
             <= set_variation s f + set_variation s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SET_VARIATION_UBOUND THEN
  ASM_SIMP_TAC[HAS_BOUNDED_SETVARIATION_ON_ADD] THEN
  MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d (\k. norm((f:(real^M->bool)->real^N) k)) +
              sum d (\k. norm((g:(real^M->bool)->real^N) k))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[GSYM SUM_ADD] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[NORM_TRIANGLE];
    MATCH_MP_TAC REAL_LE_ADD2 THEN
    CONJ_TAC THEN MATCH_MP_TAC SET_VARIATION THEN ASM_MESON_TAC[]]);;

let OPERATIVE_LIFTED_SETVARIATION = prove
 (`!f:(real^M->bool)->real^N.
        operative(+) f
        ==> operative (lifted(+))
                      (\i. if f has_bounded_setvariation_on i
                           then SOME(set_variation i f) else NONE)`,
  let lemma1 = prove
   (`!f:(real^M->bool)->real B1 B2 k a b.
      1 <= k /\ k <= dimindex(:M) /\
      (!a b. content(interval[a,b]) = &0 ==> f(interval[a,b]) = &0) /\
      (!a b c. f(interval[a,b]) <=
               f(interval[a,b] INTER {x | x$k <= c}) +
               f(interval[a,b] INTER {x | x$k >= c})) /\
      (!d. d division_of (interval[a,b] INTER {x | x$k <= c})
           ==> sum d f <= B1) /\
      (!d. d division_of (interval[a,b] INTER {x | x$k >= c})
           ==> sum d f <= B2)
      ==> !d. d division_of interval[a,b] ==> sum d f <= B1 + B2`,
    REPEAT GEN_TAC THEN
    REPLICATE_TAC 4 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L") (LABEL_TAC "R")) THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum {l INTER {x:real^M | x$k <= c} | l | l IN d /\
                                        ~(l INTER {x | x$k <= c} = {})} f +
      sum {l INTER {x | x$k >= c} | l | l IN d /\
                                        ~(l INTER {x | x$k >= c} = {})} f` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[DIVISION_SPLIT]] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    W(fun (asl,w) ->
         MP_TAC(PART_MATCH (lhs o rand) SUM_IMAGE_NONZERO (lhand(rand w))) THEN
         MP_TAC(PART_MATCH (lhs o rand) SUM_IMAGE_NONZERO (rand(rand w)))) THEN
    MATCH_MP_TAC(TAUT
     `(a1 /\ a2) /\ (b1 /\ b2 ==> c)
      ==> (a1 ==> b1) ==> (a2 ==> b2) ==> c`) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_RESTRICT; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[GSYM INTERVAL_SPLIT] THENL
       [MATCH_MP_TAC DIVISION_SPLIT_RIGHT_INJ;
        MATCH_MP_TAC DIVISION_SPLIT_LEFT_INJ] THEN
      ASM_MESON_TAC[];
      DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum d (f o (\l. l INTER {x | x$k <= c})) +
      sum d (f o (\l. l INTER {x:real^M | x$k >= c}))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
      ASM_REWRITE_TAC[o_THM] THEN
      FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]);
      MATCH_MP_TAC(REAL_ARITH `x = y /\ w = z ==> x + w <= y + z`) THEN
      CONJ_TAC THEN MATCH_MP_TAC SUM_SUPERSET THEN
      REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} SUBSET s`] THEN
      REWRITE_TAC[SET_RULE `(x IN s /\ ~(x IN {x | x IN s /\ ~P x}) ==> Q x) <=>
                            (x IN s ==> P x ==> Q x)`] THEN
      SIMP_TAC[o_THM] THEN ASM_MESON_TAC[EMPTY_AS_INTERVAL; CONTENT_EMPTY]])
  and lemma2 = prove
   (`!f:(real^M->bool)->real B k.
      1 <= k /\ k <= dimindex(:M) /\
      (!a b. content(interval[a,b]) = &0 ==> f(interval[a,b]) = &0) /\
      (!d. d division_of interval[a,b] ==> sum d f <= B)
      ==> !d1 d2. d1 division_of (interval[a,b] INTER {x | x$k <= c}) /\
                  d2 division_of (interval[a,b] INTER {x | x$k >= c})
                  ==> sum d1 f + sum d2 f <= B`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d1 UNION d2:(real^M->bool)->bool`) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN
       `interval[a,b] = (interval[a,b] INTER {x:real^M | x$k <= c}) UNION
                        (interval[a,b] INTER {x:real^M | x$k >= c})`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `(!x. x IN t \/ x IN u) ==> (s = s INTER t UNION s INTER u)`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC DIVISION_DISJOINT_UNION THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM INTERIOR_INTER] THEN
        MATCH_MP_TAC(SET_RULE
         `!t. interior s SUBSET interior t /\ interior t = {}
              ==> interior s = {}`) THEN
        EXISTS_TAC `{x:real^M | x$k = c}` THEN CONJ_TAC THENL
         [ALL_TAC; REWRITE_TAC[INTERIOR_STANDARD_HYPERPLANE]] THEN
        MATCH_MP_TAC SUBSET_INTERIOR THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= b ==> y <= b`) THEN
      MATCH_MP_TAC SUM_UNION_NONZERO THEN
      REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_FINITE]; ALL_TAC]) THEN
      X_GEN_TAC `k:real^M->bool` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
        (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC CONTENT_0_SUBSET_GEN THEN
      EXISTS_TAC `interval[a,b] INTER {x:real^M | x$k = c}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `(interval[a,b] INTER {x:real^M | x$k <= c}) INTER
                    (interval[a,b] INTER {x:real^M | x$k >= c})` THEN
        CONJ_TAC THENL
         [ONCE_REWRITE_TAC[SUBSET_INTER] THEN ASM_MESON_TAC[division_of];
          REWRITE_TAC[SET_RULE
            `(s INTER t) INTER (s INTER u) = s INTER t INTER u`] THEN
          SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC];
        SIMP_TAC[BOUNDED_INTER; BOUNDED_INTERVAL] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [REAL_ARITH `x = y <=> x <= y /\ x >= y`] THEN
        REWRITE_TAC[SET_RULE
         `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
        ASM_SIMP_TAC[GSYM INTER_ASSOC; INTERVAL_SPLIT] THEN
        REWRITE_TAC[CONTENT_EQ_0] THEN EXISTS_TAC `k:num` THEN
        ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC]]) in
  REWRITE_TAC[operative; NEUTRAL_VECTOR_ADD] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN
  ASM_SIMP_TAC[HAS_BOUNDED_SETVARIATION_ON_NULL; BOUNDED_INTERVAL;
   MONOIDAL_REAL_ADD; SET_VARIATION_ON_NULL; NEUTRAL_LIFTED;
   NEUTRAL_REAL_ADD] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `c:real`; `k:num`] THEN
  STRIP_TAC THEN ASM_CASES_TAC
   `(f:(real^M->bool)->real^N) has_bounded_setvariation_on interval[a,b]` THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `(f:(real^M->bool)->real^N) has_bounded_setvariation_on
      interval[a,b] INTER {x | x$k <= c} /\
      (f:(real^M->bool)->real^N) has_bounded_setvariation_on
      interval[a,b] INTER {x | x$k >= c}`
    ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] HAS_BOUNDED_SETVARIATION_ON_SUBSET)) THEN
      REWRITE_TAC[INTER_SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[lifted] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SET_VARIATION_UBOUND_ON_INTERVAL THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC
       (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] lemma1) THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `a:real^M`; `b:real^M`] THEN
      ASM_SIMP_TAC[NORM_0] THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN
        MATCH_MP_TAC(NORM_ARITH
          `x:real^N = y + z ==> norm(x) <= norm y + norm z`) THEN
        ASM_SIMP_TAC[];
        FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_AND) THEN
        ASM_SIMP_TAC[INTERVAL_SPLIT; SET_VARIATION_WORKS_ON_INTERVAL]];
      ONCE_REWRITE_TAC[REAL_ARITH `x + y <= z <=> x <= z - y`] THEN
      ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
      MATCH_MP_TAC SET_VARIATION_UBOUND_ON_INTERVAL THEN
      ASM_SIMP_TAC[GSYM INTERVAL_SPLIT] THEN
      X_GEN_TAC `d1:(real^M->bool)->bool` THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[REAL_ARITH `x <= y - z <=> z <= y - x`] THEN
      ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
      MATCH_MP_TAC SET_VARIATION_UBOUND_ON_INTERVAL THEN
      ASM_SIMP_TAC[GSYM INTERVAL_SPLIT] THEN
      X_GEN_TAC `d2:(real^M->bool)->bool` THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ARITH `x <= y - z <=> z + x <= y`] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC
       (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] lemma2) THEN
      EXISTS_TAC `k:num` THEN
      ASM_SIMP_TAC[NORM_0; SET_VARIATION_WORKS_ON_INTERVAL]];
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[lifted]) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_INTERVAL] THEN
    EXISTS_TAC `set_variation (interval[a,b] INTER {x | x$k <= c})
                              (f:(real^M->bool)->real^N) +
                set_variation (interval[a,b] INTER {x | x$k >= c}) f` THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC
       (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] lemma1) THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `a:real^M`; `b:real^M`] THEN
      ASM_SIMP_TAC[NORM_0] THEN REPEAT CONJ_TAC THENL
       [REPEAT GEN_TAC THEN
        MATCH_MP_TAC(NORM_ARITH
          `x:real^N = y + z ==> norm(x) <= norm y + norm z`) THEN
        ASM_SIMP_TAC[];
        UNDISCH_TAC
         `(f:(real^M->bool)->real^N) has_bounded_setvariation_on
          (interval[a,b] INTER {x | x$k <= c})` THEN
        ASM_SIMP_TAC[INTERVAL_SPLIT; SET_VARIATION_WORKS_ON_INTERVAL];
        UNDISCH_TAC
         `(f:(real^M->bool)->real^N) has_bounded_setvariation_on
          (interval[a,b] INTER {x | x$k >= c})` THEN
        ASM_SIMP_TAC[INTERVAL_SPLIT; SET_VARIATION_WORKS_ON_INTERVAL]]]);;

let HAS_BOUNDED_SETVARIATION_ON_DIVISION = prove
 (`!f:(real^M->bool)->real^N a b d.
        operative (+) f /\ d division_of interval[a,b]
        ==> ((!k. k IN d ==> f has_bounded_setvariation_on k) <=>
             f has_bounded_setvariation_on interval[a,b])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPERATIVE_DIVISION_AND THEN
  ASM_REWRITE_TAC[operative; NEUTRAL_AND] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[operative; NEUTRAL_VECTOR_ADD]) THEN
    ASM_SIMP_TAC[HAS_BOUNDED_SETVARIATION_ON_NULL; BOUNDED_INTERVAL];
    FIRST_ASSUM(MP_TAC o MATCH_MP OPERATIVE_LIFTED_SETVARIATION) THEN
    REWRITE_TAC[operative] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[lifted; distinctness "option"])]);;

let SET_VARIATION_ON_DIVISION = prove
 (`!f:(real^M->bool)->real^N a b d.
        operative (+) f /\ d division_of interval[a,b] /\
        f has_bounded_setvariation_on interval[a,b]
        ==> sum d (\k. set_variation k f) = set_variation (interval[a,b]) f`,
  let lemma0 = prove
   (`!op x y. lifted op (SOME x) y = SOME z <=> ?w. y = SOME w /\ op x w = z`,
    GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
    REWRITE_TAC[lifted; distinctness "option"; injectivity "option"] THEN
    MESON_TAC[]) in
  let lemma = prove
   (`!P op f s z.
          monoidal op /\ FINITE s /\
          iterate(lifted op) s (\i. if P i then SOME(f i) else NONE) = SOME z
          ==> iterate op s f = z`,
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_LIFTED; NEUTRAL_LIFTED] THEN
    REWRITE_TAC[injectivity "option"] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[lifted; distinctness "option"] THEN ASM_MESON_TAC[lemma0]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPERATIVE_LIFTED_SETVARIATION) THEN
  DISCH_THEN(MP_TAC o SPECL[`d:(real^M->bool)->bool`; `a:real^M`; `b:real^M`] o
    MATCH_MP (REWRITE_RULE [TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`]
        OPERATIVE_DIVISION)) THEN
  ASM_SIMP_TAC[MONOIDAL_LIFTED; MONOIDAL_REAL_ADD] THEN
  MP_TAC(ISPECL
   [`\k. (f:(real^M->bool)->real^N) has_bounded_setvariation_on k`;
    `(+):real->real->real`;
    `\k. set_variation k (f:(real^M->bool)->real^N)`;
    `d:(real^M->bool)->bool`;
    `set_variation (interval[a,b]) (f:(real^M->bool)->real^N)`]
   lemma) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_REWRITE_TAC[sum; MONOIDAL_REAL_ADD]);;

let SET_VARIATION_MONOTONE = prove
 (`!f:(real^M->bool)->real^N s t.
        f has_bounded_setvariation_on s /\ t SUBSET s
        ==> set_variation t f <= set_variation s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[set_variation] THEN
  MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`&0`; `{}:(real^M->bool)->bool`] THEN
    REWRITE_TAC[SUM_CLAUSES] THEN EXISTS_TAC `{}:real^M->bool` THEN
    REWRITE_TAC[EMPTY_SUBSET; DIVISION_OF_TRIVIAL];
    MATCH_MP_TAC(SET_RULE
     `(!d. P d ==> Q d) ==> {f d | P d} SUBSET {f d | Q d}`) THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    REWRITE_TAC[FORALL_IN_GSPEC; LEFT_IMP_EXISTS_THM] THEN
    ASM_REWRITE_TAC[GSYM has_bounded_setvariation_on]]);;

let HAS_BOUNDED_SETVARIATION_REFLECT2_EQ,SET_VARIATION_REFLECT2 =
 (CONJ_PAIR o prove)
 (`(!f:(real^M->bool)->real^N s.
        (\k. f(IMAGE (--) k)) has_bounded_setvariation_on (IMAGE (--) s) <=>
        f has_bounded_setvariation_on s) /\
   (!f:(real^M->bool)->real^N s.
        set_variation (IMAGE (--) s) (\k. f(IMAGE (--) k)) =
        set_variation s f)`,
  MATCH_MP_TAC SETVARIATION_EQUAL_LEMMA THEN
  EXISTS_TAC `IMAGE ((--):real^M->real^M)` THEN
  SIMP_TAC[IMAGE_SUBSET; GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[VECTOR_NEG_NEG; IMAGE_ID; REFLECT_INTERVAL] THEN
  SIMP_TAC[ETA_AX; DIVISION_OF_REFLECT] THEN
  SIMP_TAC[EQ_INTERVAL; TAUT `~q /\ (p /\ q \/ r) <=> ~q /\ r`] THEN
  REWRITE_TAC[TAUT `p /\ q /\ r <=> r /\ q /\ p`] THEN
  REWRITE_TAC[UNWIND_THM1; CONTRAPOS_THM] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY; VECTOR_NEG_COMPONENT; REAL_LT_NEG2]);;

let HAS_BOUNDED_SETVARIATION_TRANSLATION2_EQ, SET_VARIATION_TRANSLATION2 =
 (CONJ_PAIR o prove)
 (`(!a f:(real^M->bool)->real^N s.
          (\k. f(IMAGE (\x. a + x) k))
          has_bounded_setvariation_on (IMAGE (\x. --a + x) s) <=>
          f has_bounded_setvariation_on s) /\
   (!a f:(real^M->bool)->real^N s.
          set_variation (IMAGE (\x. --a + x) s) (\k. f(IMAGE (\x. a + x) k)) =
          set_variation s f)`,
  GEN_REWRITE_TAC I [AND_FORALL_THM] THEN X_GEN_TAC `a:real^M` THEN
  MATCH_MP_TAC SETVARIATION_EQUAL_LEMMA THEN
  EXISTS_TAC `\s. IMAGE (\x:real^M. a + x) s` THEN
  SIMP_TAC[IMAGE_SUBSET; GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[VECTOR_ARITH `a + --a + x:real^N = x`; IMAGE_ID;
              VECTOR_ARITH `--a + a + x:real^N = x`] THEN
  REWRITE_TAC[GSYM INTERVAL_TRANSLATION] THEN
  SIMP_TAC[EQ_INTERVAL; TAUT `~q /\ (p /\ q \/ r) <=> ~q /\ r`] THEN
  REWRITE_TAC[TAUT `p /\ q /\ r <=> r /\ q /\ p`] THEN
  REWRITE_TAC[UNWIND_THM1; CONTRAPOS_THM] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY; VECTOR_ADD_COMPONENT; REAL_LT_LADD] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ETA_AX] THEN
  ASM_SIMP_TAC[DIVISION_OF_TRANSLATION]);;

let HAS_BOUNDED_SETVARIATION_TRANSLATION = prove
 (`!f:(real^M->bool)->real^N s a.
        f has_bounded_setvariation_on s
        ==> (\k. f(IMAGE (\x. a + x) k))
            has_bounded_setvariation_on (IMAGE (\x. --a + x) s)`,
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_TRANSLATION2_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Absolute integrability (this is the same as Lebesgue integrability).      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("absolutely_integrable_on",(12,"right"));;

let absolutely_integrable_on = new_definition
 `f absolutely_integrable_on s <=>
        f integrable_on s /\ (\x. lift(norm(f x))) integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f s. f absolutely_integrable_on s ==> f integrable_on s`,
  SIMP_TAC[absolutely_integrable_on]);;

let ABSOLUTELY_INTEGRABLE_LE = prove
 (`!f:real^M->real^N s.
        f absolutely_integrable_on s
        ==> norm(integral s f) <= drop(integral s (\x. lift(norm(f x))))`,
  REWRITE_TAC[absolutely_integrable_on] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
  ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_REFL]);;

let ABSOLUTELY_INTEGRABLE_ON_NULL = prove
 (`!f a b. content(interval[a,b]) = &0
           ==> f absolutely_integrable_on interval[a,b]`,
  SIMP_TAC[absolutely_integrable_on; INTEGRABLE_ON_NULL]);;

let ABSOLUTELY_INTEGRABLE_0 = prove
 (`!s. (\x. vec 0) absolutely_integrable_on s`,
  REWRITE_TAC[absolutely_integrable_on; NORM_0; LIFT_NUM; INTEGRABLE_0]);;

let ABSOLUTELY_INTEGRABLE_CMUL = prove
 (`!f s c. f absolutely_integrable_on s
           ==> (\x. c % f(x)) absolutely_integrable_on s`,
  SIMP_TAC[absolutely_integrable_on; INTEGRABLE_CMUL; NORM_MUL; LIFT_CMUL]);;

let ABSOLUTELY_INTEGRABLE_NEG = prove
 (`!f s. f absolutely_integrable_on s
         ==> (\x. --f(x)) absolutely_integrable_on s`,
  SIMP_TAC[absolutely_integrable_on; INTEGRABLE_NEG; NORM_NEG]);;

let ABSOLUTELY_INTEGRABLE_NORM = prove
 (`!f s. f absolutely_integrable_on s
         ==> (\x. lift(norm(f x))) absolutely_integrable_on s`,
  SIMP_TAC[absolutely_integrable_on; NORM_LIFT; REAL_ABS_NORM]);;

let ABSOLUTELY_INTEGRABLE_ABS_1 = prove
 (`!f s. f absolutely_integrable_on s
         ==> (\x. lift(abs(drop(f x)))) absolutely_integrable_on s`,
  REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP; ABSOLUTELY_INTEGRABLE_NORM]);;

let ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL = prove
 (`!f:real^M->real^N s a b.
        f absolutely_integrable_on s /\ interval[a,b] SUBSET s
        ==> f absolutely_integrable_on interval[a,b]`,
  REWRITE_TAC[absolutely_integrable_on] THEN
  MESON_TAC[INTEGRABLE_ON_SUBINTERVAL]);;

let ABSOLUTELY_INTEGRABLE_SPIKE = prove
 (`!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN t DIFF s ==> g x = f x)
        ==> f absolutely_integrable_on t ==> g absolutely_integrable_on t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[absolutely_integrable_on] THEN MATCH_MP_TAC MONO_AND THEN
  CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_SPIKE THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[]);;

let ABSOLUTELY_INTEGRABLE_RESTRICT_INTER = prove
 (`!f:real^M->real^N s t.
        (\x. if x IN s then f x else vec 0) absolutely_integrable_on t <=>
        f absolutely_integrable_on (s INTER t)`,
  REWRITE_TAC[absolutely_integrable_on; GSYM INTEGRABLE_RESTRICT_INTER] THEN
  REWRITE_TAC[COND_RAND; NORM_0; LIFT_NUM]);;

let ABSOLUTELY_INTEGRABLE_EQ = prove
 (`!f:real^M->real^N g s.
        (!x. x IN s ==> f x = g x) /\ f absolutely_integrable_on s
        ==> g absolutely_integrable_on s`,
  REWRITE_TAC[absolutely_integrable_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_EQ THENL
   [EXISTS_TAC `f:real^M->real^N`;
    EXISTS_TAC `\x. lift(norm((f:real^M->real^N) x))`] THEN
  ASM_SIMP_TAC[]);;

let ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION = prove
 (`!f:real^M->real^N s.
        f absolutely_integrable_on s
        ==> (\k. integral k f) has_bounded_setvariation_on s`,
  REWRITE_TAC[has_bounded_setvariation_on] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `drop(integral (s:real^M->bool) (\x. lift(norm(f x:real^N))))` THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN
  X_GEN_TAC `t:real^M->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(UNIONS d:real^M->bool) SUBSET s` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS; division_of]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (UNIONS d) (\x. lift(norm((f:real^M->real^N) x))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
      EXISTS_TAC `s:real^M->bool` THEN
      EXISTS_TAC `d:(real^M->bool)->bool` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[DIVISION_OF_SUBSET; division_of]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(vsum d (\i. integral i (\x:real^M. lift(norm(f x:real^N)))))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[DROP_VSUM] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[o_THM] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_MESON_TAC[division_of; SUBSET_TRANS];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_COMBINE_DIVISION_TOPDOWN THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[DIVISION_OF_UNION_SELF]] THEN
    MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
    MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `d:(real^M->bool)->bool`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_UNION_SELF]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[]]);;

let lemma = prove
 (`!f:A->real^N g s e.
        sum s (\x. norm(f x - g x)) < e
        ==> FINITE s
            ==> abs(sum s (\x. norm(f x)) - sum s (\x. norm(g x))) < e`,
  REPEAT GEN_TAC THEN SIMP_TAC[GSYM SUM_SUB] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_ABS o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN NORM_ARITH_TAC);;

let BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE_INTERVAL = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b] /\
        (\k. integral k f) has_bounded_setvariation_on interval[a,b]
        ==> f absolutely_integrable_on interval[a,b]`,
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_INTERVAL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[absolutely_integrable_on] THEN
  MP_TAC(ISPEC `IMAGE (\d. sum d (\k. norm(integral k (f:real^M->real^N))))
                      {d | d division_of interval[a,b] }`
         SUP) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  ABBREV_TAC
   `i = sup (IMAGE (\d. sum d (\k. norm(integral k (f:real^M->real^N))))
                      {d | d division_of interval[a,b] })` THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ELEMENTARY_INTERVAL] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[integrable_on] THEN EXISTS_TAC `lift i` THEN
  REWRITE_TAC[has_integral] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - e / &2`) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> ~(i <= i - e / &2)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  SUBGOAL_THEN
   `!x. ?e. &0 < e /\
            !i. i IN d /\ ~(x IN i) ==> ball(x:real^M,e) INTER i = {}`
  MP_TAC THENL
   [X_GEN_TAC `x:real^M` THEN MP_TAC(ISPECL
     [`UNIONS {i:real^M->bool | i IN d /\ ~(x IN i)}`; `x:real^M`]
     SEPARATE_POINT_CLOSED) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; IMP_CONJ] THEN
      FIRST_ASSUM(fun t -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION t]) THEN
      REWRITE_TAC[CLOSED_INTERVAL];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN
    SIMP_TAC[FORALL_IN_UNIONS; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_BALL] THEN
    REWRITE_TAC[IN_ELIM_THM; DE_MORGAN_THM; REAL_NOT_LT] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `k:real^M->real` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `e / &2` o MATCH_MP HENSTOCK_LEMMA) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:real^M. g(x) INTER ball(x,k x)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC GAUGE_INTER THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[gauge; CENTRE_IN_BALL; OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[FINE_INTER] THEN X_GEN_TAC `p:(real^M#(real^M->bool))->bool` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ABBREV_TAC
   `p' = {(x:real^M,k:real^M->bool) |
                ?i l. x IN i /\ i IN d /\ (x,l) IN p /\ k = i INTER l}` THEN
  SUBGOAL_THEN `g fine (p':(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "p'" THEN
    MP_TAC(ASSUME `g fine (p:(real^M#(real^M->bool))->bool)`) THEN
    REWRITE_TAC[fine; IN_ELIM_PAIR_THM] THEN
    MESON_TAC[SET_RULE `k SUBSET l ==> (i INTER k) SUBSET l`];
    ALL_TAC] THEN
  SUBGOAL_THEN `p' tagged_division_of interval[a:real^M,b]` ASSUME_TAC THENL
   [REWRITE_TAC[TAGGED_DIVISION_OF] THEN EXPAND_TAC "p'" THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `IMAGE (\(k,(x,l)). x,k INTER l)
              {k,xl | k IN (d:(real^M->bool)->bool) /\
                      xl IN (p:(real^M#(real^M->bool))->bool)}` THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_PRODUCT] THEN
      EXPAND_TAC "p'" THEN REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM; IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`i:real^M->bool`; `l:real^M->bool`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_SIMP_TAC[IN_INTER] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `l SUBSET s ==> (k INTER l) SUBSET s`) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `l:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      DISCH_THEN(MP_TAC o SPEC `i:real^M->bool` o el 1 o CONJUNCTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[INTER_INTERVAL] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [DISCH_TAC THEN MAP_EVERY X_GEN_TAC
       [`x1:real^M`; `k1:real^M->bool`; `x2:real^M`; `k2:real^M->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `i1:real^M->bool` (X_CHOOSE_THEN `l1:real^M->bool`
          STRIP_ASSUME_TAC)) MP_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `i2:real^M->bool` (X_CHOOSE_THEN `l2:real^M->bool`
          STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MATCH_MP_TAC(SET_RULE
       `(interior(i1) INTER interior(i2) = {} \/
         interior(l1) INTER interior(l2) = {}) /\
        interior(i1 INTER l1) SUBSET interior(i1) /\
        interior(i2 INTER l2) SUBSET interior(i2) /\
        interior(i1 INTER l1) SUBSET interior(l1) /\
        interior(i2 INTER l2) SUBSET interior(l2)
        ==> interior(i1 INTER l1) INTER interior(i2 INTER l2) = {}`) THEN
      SIMP_TAC[SUBSET_INTERIOR; INTER_SUBSET] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`x1:real^M`; `l1:real^M->bool`; `x2:real^M`; `l2:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o SPECL [`i1:real^M->bool`; `i2:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check(is_neg o concl)) THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `i SUBSET s ==> (i INTER k) SUBSET s`) THEN
      ASM_MESON_TAC[division_of];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[MESON[]
     `p /\ q /\ r /\ x = t /\ P x <=> x = t /\ p /\ q /\ r /\ P t`] THEN
    ONCE_REWRITE_TAC[MESON[]
     `(?a b c d. P a b c d) <=> (?d b c a. P a b c d)`] THEN
    REWRITE_TAC[IN_INTER; UNWIND_THM2] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^M->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^M` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o last o CONJUNCTS o
        GEN_REWRITE_RULE I [division_of]) THEN
    REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `k:real^M->bool`]) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `y:real^M` THEN ASM_REWRITE_TAC[INTER; IN_ELIM_THM] THEN
    UNDISCH_TAC `(\x:real^M. ball (x,k x)) fine p` THEN
    REWRITE_TAC[fine; SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p':(real^M#(real^M->bool))->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[tagged_division_of]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  REWRITE_TAC[LAMBDA_PAIR] THEN DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  ASM_SIMP_TAC[DROP_VSUM; o_DEF; SUM_SUB; DROP_SUB; ABS_DROP] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM; DROP_CMUL; NORM_MUL; LIFT_DROP] THEN
  MATCH_MP_TAC(REAL_ARITH
    `!sni. i - e / &2 < sni /\
           sni' <= i /\ sni <= sni' /\ sf' = sf
              ==> abs(sf' - sni') < e / &2
                  ==> abs(sf - i) < e`) THEN
  EXISTS_TAC `sum d (\k. norm (integral k (f:real^M->real^N)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\k. norm(integral k (f:real^M->real^N))`;
                   `p':(real^M#(real^M->bool))->bool`;
                   `interval[a:real^M,b]`] SUM_OVER_TAGGED_DIVISION_LEMMA) THEN
    ASM_SIMP_TAC[INTEGRAL_NULL; NORM_0] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIVISION_OF_TAGGED_DIVISION];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p' = {x:real^M,(i INTER l:real^M->bool) |
            (x,l) IN p /\ i IN d /\ ~(i INTER l = {})}`
  (LABEL_TAC "p'") THENL
   [EXPAND_TAC "p'" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
    REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `i:real^M->bool` THEN REWRITE_TAC[] THEN
    CONV_TAC(RAND_CONV UNWIND_CONV) THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `l:real^M->bool` THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `k:real^M->bool = i INTER l` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[IN_INTER; GSYM MEMBER_NOT_EMPTY] THEN
    EQ_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^M` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `i:real^M->bool`]) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `y:real^M` THEN ASM_REWRITE_TAC[INTER; IN_ELIM_THM] THEN
    UNDISCH_TAC `(\x:real^M. ball (x,k x)) fine p` THEN
    REWRITE_TAC[fine; SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\y. norm(integral y (f:real^M->real^N))`;
      `p':(real^M#(real^M->bool))->bool`;
      `interval[a:real^M,b]`]
     SUM_OVER_TAGGED_DIVISION_LEMMA) THEN
    ASM_SIMP_TAC[INTEGRAL_NULL; NORM_0] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {i INTER l | i IN d /\
                 (l IN IMAGE SND (p:(real^M#(real^M->bool))->bool))}
                    (\k. norm(integral k (f:real^M->real^N)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_SUPERSET THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        REWRITE_TAC[FORALL_PAIR_THM] THEN
        REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; PAIR_EQ; EXISTS_PAIR_THM] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC
       [`kk:real^M->bool`; `i:real^M->bool`; `l:real^M->bool`] THEN
      ASM_CASES_TAC `kk:real^M->bool = i INTER l` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; UNWIND_THM1] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `x:real^M`)) MP_TAC) THEN
      REWRITE_TAC[IN_ELIM_THM; PAIR_EQ; NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPECL
       [`x:real^M`; `x:real^M`; `i:real^M->bool`; `l:real^M->bool`]) THEN
      ASM_SIMP_TAC[INTEGRAL_EMPTY; NORM_0]] THEN
    SUBGOAL_THEN
     `{k INTER l | k IN d /\ l IN IMAGE SND (p:(real^M#(real^M->bool))->bool)} =
      IMAGE (\(k,l). k INTER l) {k,l | k IN d /\ l IN IMAGE SND p}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM; FORALL_PAIR_THM] THEN
      REWRITE_TAC[PAIR_EQ] THEN
      CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN MESON_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_NONZERO o rand o snd) THEN
    ANTS_TAC THENL
     [ASSUME_TAC(MATCH_MP DIVISION_OF_TAGGED_DIVISION
        (ASSUME `p tagged_division_of interval[a:real^M,b]`)) THEN
      ASM_SIMP_TAC[FINITE_PRODUCT; FINITE_IMAGE] THEN
      REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC
       [`l1:real^M->bool`; `k1:real^M->bool`;
        `l2:real^M->bool`; `k2:real^M->bool`] THEN
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
      SUBGOAL_THEN `interior(l2 INTER k2:real^M->bool) = {}` MP_TAC THENL
       [ALL_TAC;
        MP_TAC(ASSUME `d division_of interval[a:real^M,b]`) THEN
        REWRITE_TAC[division_of] THEN
        DISCH_THEN(MP_TAC o SPEC `l2:real^M->bool` o el 1 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME
         `(IMAGE SND (p:(real^M#(real^M->bool))->bool))
                division_of interval[a:real^M,b]`) THEN
        REWRITE_TAC[division_of] THEN
        DISCH_THEN(MP_TAC o SPEC `k2:real^M->bool` o el 1 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[INTER_INTERVAL] THEN DISCH_TAC THEN
        REWRITE_TAC[NORM_EQ_0] THEN
        MATCH_MP_TAC INTEGRAL_NULL THEN
        ASM_REWRITE_TAC[CONTENT_EQ_0_INTERIOR]] THEN
      MATCH_MP_TAC(SET_RULE
       `(interior(k1) INTER interior(k2) = {} \/
         interior(l1) INTER interior(l2) = {}) /\
        interior(l1 INTER k1) SUBSET interior(k1) /\
        interior(l2 INTER k2) SUBSET interior(k2) /\
        interior(l1 INTER k1) SUBSET interior(l1) /\
        interior(l2 INTER k2) SUBSET interior(l2) /\
        interior(l1 INTER k1) = interior(l2 INTER k2)
        ==> interior(l2 INTER k2) = {}`) THEN
      SIMP_TAC[SUBSET_INTERIOR; INTER_SUBSET] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `d division_of interval[a:real^M,b]`) THEN
      REWRITE_TAC[division_of] THEN DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o SPECL [`l1:real^M->bool`; `l2:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME
       `(IMAGE SND (p:(real^M#(real^M->bool))->bool))
              division_of interval[a:real^M,b]`) THEN
      REWRITE_TAC[division_of] THEN DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o SPECL [`k1:real^M->bool`; `k2:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [LAMBDA_PAIR_THM] THEN
    ASM_SIMP_TAC[GSYM SUM_SUM_PRODUCT; FINITE_IMAGE] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum { k INTER l |
             l IN IMAGE SND (p:(real^M#(real^M->bool))->bool)}
          (\k. norm(integral k (f:real^M->real^N)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE_NONZERO o lhand o snd) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[o_DEF; REAL_LE_REFL]] THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN
      MAP_EVERY X_GEN_TAC [`k1:real^M->bool`; `k2:real^M->bool`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `interior(k INTER k2:real^M->bool) = {}` MP_TAC THENL
       [ALL_TAC;
        MP_TAC(MATCH_MP DIVISION_OF_TAGGED_DIVISION
         (ASSUME `p tagged_division_of interval[a:real^M,b]`)) THEN
        MP_TAC(ASSUME `d division_of interval[a:real^M,b]`) THEN
        REWRITE_TAC[division_of] THEN
        DISCH_THEN(MP_TAC o SPEC `k:real^M->bool` o el 1 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `k2:real^M->bool` o el 1 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[INTER_INTERVAL; GSYM CONTENT_EQ_0_INTERIOR] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[INTER_INTERVAL] THEN
        SIMP_TAC[GSYM CONTENT_EQ_0_INTERIOR; INTEGRAL_NULL; NORM_0]] THEN
      MATCH_MP_TAC(SET_RULE
       `interior(k INTER k2) SUBSET interior(k1 INTER k2) /\
        interior(k1 INTER k2) = {}
        ==> interior(k INTER k2) = {}`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(MATCH_MP DIVISION_OF_TAGGED_DIVISION
         (ASSUME `p tagged_division_of interval[a:real^M,b]`)) THEN
      REWRITE_TAC[division_of] THEN
      DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
      REWRITE_TAC[INTERIOR_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
     (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    SUBGOAL_THEN `interval[u:real^M,v] SUBSET interval[a,b]` ASSUME_TAC THENL
     [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    ABBREV_TAC `d' =
        {interval[u,v] INTER l |l|
                l IN IMAGE SND (p:(real^M#(real^M->bool))->bool) /\
                ~(interval[u,v] INTER l = {})}` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum d' (\k. norm (integral k (f:real^M->real^N)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SUM_SUPERSET THEN
      EXPAND_TAC "d'" THEN REWRITE_TAC[SUBSET; SET_RULE
       `a IN {f x |x| x IN s /\ ~(f x = b)} <=>
        a IN {f x | x IN s} /\ ~(a = b)`] THEN
      SIMP_TAC[IMP_CONJ; INTEGRAL_EMPTY; NORM_0]] THEN
    SUBGOAL_THEN `d' division_of interval[u:real^M,v]` ASSUME_TAC THENL
     [EXPAND_TAC "d'" THEN MATCH_MP_TAC DIVISION_INTER_1 THEN
      EXISTS_TAC `interval[a:real^M,b]` THEN
      ASM_SIMP_TAC[DIVISION_OF_TAGGED_DIVISION];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vsum d' (\i. integral i (f:real^M->real^N)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      MATCH_MP_TAC INTEGRAL_COMBINE_DIVISION_TOPDOWN THEN
      ASM_MESON_TAC[INTEGRABLE_ON_SUBINTERVAL];
      ALL_TAC] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN
    REWRITE_TAC[REAL_LE_REFL] THEN ASM_MESON_TAC[division_of];
    ALL_TAC] THEN
  REMOVE_THEN "p'" SUBST_ALL_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {x,i INTER l | (x,l) IN p /\ i IN d}
                  (\(x,k:real^M->bool).
                      abs(content k) * norm((f:real^M->real^N) x))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `i:real^M->bool`] THEN
    ASM_CASES_TAC `i:real^M->bool = {}` THEN
    ASM_SIMP_TAC[CONTENT_EMPTY; REAL_ABS_NUM; REAL_MUL_LZERO] THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> a /\ ~b ==> c`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x,i INTER l | x,l IN (p:(real^M#(real^M->bool))->bool) /\ i IN d} =
    IMAGE (\((x,l),k). x,k INTER l) {m,k | m IN p /\ k IN d}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM; FORALL_PAIR_THM] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_NONZERO o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_PRODUCT] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`x1:real^M`; `l1:real^M->bool`; `k1:real^M->bool`;
      `x2:real^M`; `l2:real^M->bool`; `k2:real^M->bool`] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    ASM_CASES_TAC `x1:real^M = x2` THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
    REWRITE_TAC[REAL_ABS_ZERO] THEN
    SUBGOAL_THEN `interior(k2 INTER l2:real^M->bool) = {}` MP_TAC THENL
     [ALL_TAC;
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      DISCH_THEN(MP_TAC o SPEC `k2:real^M->bool` o el 1 o CONJUNCTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `p tagged_division_of interval[a:real^M,b]`) THEN
      REWRITE_TAC[TAGGED_DIVISION_OF] THEN
      DISCH_THEN(MP_TAC o el 1 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o SPECL [`x2:real^M`; `l2:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[INTER_INTERVAL; CONTENT_EQ_0_INTERIOR]] THEN
    MATCH_MP_TAC(SET_RULE
     `(interior(k1) INTER interior(k2) = {} \/
       interior(l1) INTER interior(l2) = {}) /\
      interior(k1 INTER l1) SUBSET interior(k1) /\
      interior(k2 INTER l2) SUBSET interior(k2) /\
      interior(k1 INTER l1) SUBSET interior(l1) /\
      interior(k2 INTER l2) SUBSET interior(l2) /\
      interior(k1 INTER l1) = interior(k2 INTER l2)
      ==> interior(k2 INTER l2) = {}`) THEN
    SIMP_TAC[SUBSET_INTERIOR; INTER_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`k1:real^M->bool`; `k2:real^M->bool`]) THEN
    MP_TAC(ASSUME `p tagged_division_of interval[a:real^M,b]`) THEN
    REWRITE_TAC[TAGGED_DIVISION_OF] THEN
    DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`x2:real^M`; `l1:real^M->bool`; `x2:real^M`; `l2:real^M->bool`]) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [LAMBDA_PAIR_THM] THEN
  ASM_SIMP_TAC[GSYM SUM_SUM_PRODUCT] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN
  DISCH_TAC THEN REWRITE_TAC[o_THM; SUM_RMUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `?u v:real^M. l = interval[u,v]`
   (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
  THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum d (\k. content(k INTER interval[u:real^M,v]))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[real_abs] THEN
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?w z:real^M. k = interval[w,z]`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    REWRITE_TAC[INTER_INTERVAL; CONTENT_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {k INTER interval[u:real^M,v] | k IN d} content` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_IMAGE_NONZERO THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`k1:real^M->bool`; `k2:real^M->bool`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `interior(k2 INTER interval[u:real^M,v]) = {}` MP_TAC THENL
     [ALL_TAC;
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      DISCH_THEN(MP_TAC o SPEC `k2:real^M->bool` o el 1 o CONJUNCTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[INTER_INTERVAL; CONTENT_EQ_0_INTERIOR]] THEN
    MATCH_MP_TAC(SET_RULE
     `interior(k2 INTER i) SUBSET interior(k1 INTER k2) /\
      interior(k1 INTER k2) = {}
      ==> interior(k2 INTER i) = {}`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
    REWRITE_TAC[INTERIOR_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[u:real^M,v] SUBSET interval[a,b]` ASSUME_TAC THENL
   [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {k INTER interval[u:real^M,v] |k|
                      k IN d /\ ~(k INTER interval[u,v] = {})} content` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; SET_RULE
     `a IN {f x |x| x IN s /\ ~(f x = b)} <=>
      a IN {f x | x IN s} /\ ~(a = b)`] THEN
    SIMP_TAC[IMP_CONJ; CONTENT_EMPTY];
    ALL_TAC] THEN
  MATCH_MP_TAC ADDITIVE_CONTENT_DIVISION THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC DIVISION_INTER_1 THEN
  EXISTS_TAC `interval[a:real^M,b]` THEN ASM_REWRITE_TAC[]);;

let BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE = prove
 (`!f:real^M->real^N.
        f integrable_on UNIV /\
        (\k. integral k f) has_bounded_setvariation_on (:real^M)
        ==> f absolutely_integrable_on UNIV`,
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_UNIV] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[absolutely_integrable_on] THEN
  MP_TAC(ISPEC `IMAGE (\d. sum d (\k. norm(integral k (f:real^M->real^N))))
                      {d | d division_of (UNIONS d) }`
         SUP) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  ABBREV_TAC
   `i = sup (IMAGE (\d. sum d (\k. norm(integral k (f:real^M->real^N))))
                      {d | d division_of (UNIONS d) })` THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    EXISTS_TAC `{}:(real^M->bool)->bool` THEN
    REWRITE_TAC[UNIONS_0; DIVISION_OF_TRIVIAL];
    ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[integrable_on] THEN EXISTS_TAC `lift i` THEN
  REWRITE_TAC[HAS_INTEGRAL_ALT; IN_UNIV] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`]
      (REWRITE_RULE[HAS_BOUNDED_SETVARIATION_ON_INTERVAL]
       BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE_INTERVAL)) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[absolutely_integrable_on]] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN EXISTS_TAC `(:real^M)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    EXISTS_TAC `B:real` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIVISION_OF_UNION_SELF];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - e`) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> ~(i <= i - e)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `bounded(UNIONS d:real^M->bool)` MP_TAC THENL
   [ASM_MESON_TAC[ELEMENTARY_BOUNDED]; ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K + &1` THEN ASM_SIMP_TAC[REAL_LT_ADD; REAL_LT_01] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
  REWRITE_TAC[ABS_DROP; DROP_SUB; LIFT_DROP] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s1. i - e < s1 /\ s1 <= s /\ s < i + e ==> abs(s - i) < e`) THEN
  EXISTS_TAC `sum (d:(real^M->bool)->bool) (\k. norm (integral k
                    (f:real^M->real^N)))` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum d
      (\k. drop(integral k (\x. lift(norm((f:real^M->real^N) x)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN
      FIRST_ASSUM(fun t -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION t]) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LE THEN
      ASM_REWRITE_TAC[absolutely_integrable_on] THEN
      MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (UNIONS d)
                      (\x. lift(norm((f:real^M->real^N) x))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(MESON[REAL_LE_REFL; LIFT_DROP]
       `lift x = y ==> x <= drop y`) THEN
      ASM_SIMP_TAC[LIFT_SUM; o_DEF; LIFT_DROP] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC INTEGRAL_COMBINE_DIVISION_BOTTOMUP THEN
      FIRST_ASSUM(fun t -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION t]);
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(vec 0:real^M,K + &1)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      ASM_SIMP_TAC[NORM_ARITH `norm(x) <= K ==> dist(vec 0,x) < K + &1`];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
    EXISTS_TAC `interval[a:real^M,b]` THEN
    EXISTS_TAC `d:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^M`; `b:real^M`]) THEN
  REWRITE_TAC[HAS_INTEGRAL_INTEGRAL; has_integral] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`]
                HENSTOCK_LEMMA) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "+")) THEN
  SUBGOAL_THEN `?p. p tagged_division_of interval[a:real^M,b] /\
                    d1 fine p /\ d2 fine p`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FINE_INTER] THEN MATCH_MP_TAC FINE_DIVISION_EXISTS THEN
    ASM_SIMP_TAC[GAUGE_INTER];
    ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `p:(real^M#(real^M->bool)->bool)`) THEN
  REMOVE_THEN "+" (MP_TAC o SPEC `p:(real^M#(real^M->bool)->bool)`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[tagged_division_of]; ALL_TAC] THEN
  REWRITE_TAC[ABS_DROP; DROP_SUB] THEN
  REWRITE_TAC[LAMBDA_PAIR] THEN DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[DROP_VSUM; o_DEF; SUM_SUB] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM; DROP_CMUL; NORM_MUL; LIFT_DROP] THEN
  MATCH_MP_TAC(REAL_ARITH
   `sf' = sf /\ si <= i
    ==> abs(sf - si) < e / &2
        ==> abs(sf' - di) < e / &2
            ==> di < i + e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM; real_abs] THEN
    ASM_MESON_TAC[CONTENT_POS_LE; TAGGED_DIVISION_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum p (\(x:real^M,k). norm(integral k f)) =
    sum (IMAGE SND p) (\k. norm(integral k (f:real^M->real^N)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_OVER_TAGGED_DIVISION_LEMMA THEN
    EXISTS_TAC `interval[a:real^M,b]` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[INTEGRAL_NULL; NORM_0];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC PARTIAL_DIVISION_OF_TAGGED_DIVISION THEN
  EXISTS_TAC `interval[a:real^M,b]` THEN ASM_MESON_TAC[tagged_division_of]);;

let ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION_UNIV_EQ = prove
 (`!f:real^M->real^N.
        f absolutely_integrable_on (:real^M) <=>
        f integrable_on (:real^M) /\
        (\k. integral k f) has_bounded_setvariation_on (:real^M)`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION;
           BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE;
           ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

let ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION_EQ = prove
 (`!f:real^M->real^N a b.
        f absolutely_integrable_on interval[a,b] <=>
        f integrable_on interval[a,b] /\
        (\k. integral k f) has_bounded_setvariation_on interval[a,b]`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION;
           BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE_INTERVAL;
           ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

let ABSOLUTELY_INTEGRABLE_SET_VARIATION = prove
 (`!f:real^M->real^N a b.
        f absolutely_integrable_on interval[a,b]
        ==> set_variation (interval[a,b]) (\k. integral k f) =
                 drop(integral (interval[a,b]) (\x. lift(norm(f x))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[set_variation] THEN
  MATCH_MP_TAC REAL_SUP_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN CONJ_TAC THENL
   [X_GEN_TAC `d:(real^M->bool)->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral s (\x. lift(norm((f:real^M->real^N) x))))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x. lift(norm((f:real^M->real^N) x))`;
                     `d:(real^M->bool)->bool`; `s:real^M->bool`]
        INTEGRAL_COMBINE_DIVISION_TOPDOWN) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
        EXISTS_TAC `interval[a:real^M,b]` THEN ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
      ASM_SIMP_TAC[DROP_VSUM] THEN MATCH_MP_TAC SUM_LE THEN
      ASM_REWRITE_TAC[o_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      REWRITE_TAC[LIFT_DROP; REAL_LE_REFL; GSYM absolutely_integrable_on] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[division_of]) THEN
      ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL; SUBSET_TRANS];
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
      EXISTS_TAC `interval[a:real^M,b]` THEN ASM_MESON_TAC[]];
    X_GEN_TAC `B:real` THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
    ABBREV_TAC `e = drop(integral (interval [a,b])
                                  (\x. lift(norm((f:real^M->real^N) x)))) -
                    B` THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2` o MATCH_MP HENSTOCK_LEMMA) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool`
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F"))) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [absolutely_integrable_on]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[HAS_INTEGRAL_INTEGRAL; has_integral] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool`
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A"))) THEN
    MP_TAC(ISPECL
     [`\x. (d1:real^M->real^M->bool) x INTER d2 x`;
      `a:real^M`; `b:real^M`]
     FINE_DIVISION_EXISTS) THEN
    ASM_SIMP_TAC[GAUGE_INTER; FINE_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^M#(real^M->bool)->bool`
        STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "A" (MP_TAC o SPEC  `p:real^M#(real^M->bool)->bool`) THEN
    REMOVE_THEN "F" (MP_TAC o SPEC  `p:real^M#(real^M->bool)->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[tagged_division_of]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\x. lift(norm((f:real^M->real^N) x))`;
      `a:real^M`; `b:real^M`; `p:real^M#(real^M->bool)->bool`]
      INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN) THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST_ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `abs(sum p (\(x,k). content k * norm((f:real^M->real^N) x)) -
          sum p (\(x,k:real^M->bool). norm(integral k f))) < e / &2`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_LET_TRANS)) THEN
      ASM_SIMP_TAC[GSYM SUM_SUB] THEN MATCH_MP_TAC SUM_ABS_LE THEN
      ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(NORM_ARITH
       `x = norm u ==> abs(x - norm v) <= norm(u - v:real^N)`) THEN
      REWRITE_TAC[NORM_MUL; real_abs] THEN
      ASM_MESON_TAC[CONTENT_POS_LE; TAGGED_DIVISION_OF];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM NORM_LIFT] THEN
    ASM_SIMP_TAC[LIFT_SUB; LIFT_SUM] THEN
    REWRITE_TAC[LAMBDA_PAIR_THM; o_DEF; LIFT_CMUL; IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NORM_ARITH
     `norm(x - y:real^N) < e / &2 /\ norm(x - z) < e / &2
      ==> norm(y - z) < e`)) THEN
    REWRITE_TAC[NORM_1; DROP_SUB] THEN
    DISCH_THEN(MP_TAC o SPEC `B:real` o MATCH_MP
     (REAL_ARITH `!B. abs(x - y) < e ==> y - B = e ==> &0 < x - B`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DROP_VSUM; REAL_SUB_LT] THEN
    REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM; LIFT_DROP] THEN DISCH_TAC THEN
    EXISTS_TAC `IMAGE SND (p:real^M#(real^M->bool)->bool)` THEN CONJ_TAC THENL
     [EXISTS_TAC `interval[a:real^M,b]` THEN
      ASM_SIMP_TAC[DIVISION_OF_TAGGED_DIVISION; SUBSET_REFL];
      FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SUM_OVER_TAGGED_DIVISION_LEMMA)) THEN
      DISCH_THEN(fun th ->
       W(MP_TAC o PART_MATCH (rand o rand) th o rand o snd)) THEN
      SIMP_TAC[INTEGRAL_NULL; NORM_0] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]]);;

let ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV = prove
 (`!f s. (\x. if x IN s then f x else vec 0)
              absolutely_integrable_on (:real^M) <=>
         f absolutely_integrable_on s`,
  REWRITE_TAC[absolutely_integrable_on; INTEGRABLE_RESTRICT_UNIV;
              COND_RAND; NORM_0; LIFT_NUM]);;

let ABSOLUTELY_INTEGRABLE_CONST = prove
 (`!a b c. (\x. c) absolutely_integrable_on interval[a,b]`,
  REWRITE_TAC[absolutely_integrable_on; INTEGRABLE_CONST]);;

let ABSOLUTELY_INTEGRABLE_ADD = prove
 (`!f:real^M->real^N g s.
        f absolutely_integrable_on s /\
        g absolutely_integrable_on s
        ==> (\x. f(x) + g(x)) absolutely_integrable_on s`,
  SUBGOAL_THEN
   `!f:real^M->real^N g.
        f absolutely_integrable_on (:real^M) /\
        g absolutely_integrable_on (:real^M)
        ==> (\x. f(x) + g(x)) absolutely_integrable_on (:real^M)`
  ASSUME_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_LID]] THEN
  REPEAT STRIP_TAC THEN
  EVERY_ASSUM(STRIP_ASSUME_TAC o
   GEN_REWRITE_RULE I [absolutely_integrable_on]) THEN
  MATCH_MP_TAC BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE THEN
  ASM_SIMP_TAC[INTEGRABLE_ADD] THEN
  MP_TAC(ISPECL [`g:real^M->real^N`; `(:real^M)`]
     ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(:real^M)`]
     ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION) THEN
  ASM_REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_UNIV] THEN
  DISCH_THEN(X_CHOOSE_TAC `B1:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `B2:real`) THEN EXISTS_TAC `B1 + B2:real` THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `d:(real^M->bool)->bool`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `a <= B1 ==> x <= a + B2 ==> x <= B1 + B2`)) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `b <= B2 ==> x <= a + b ==> x <= a + B2`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
  FIRST_ASSUM(fun t -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION t]) THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(NORM_ARITH `x = y + z ==> norm(x) <= norm(y) + norm(z)`) THEN
  MATCH_MP_TAC INTEGRAL_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]);;

let ABSOLUTELY_INTEGRABLE_SUB = prove
 (`!f:real^M->real^N g s.
        f absolutely_integrable_on s /\
        g absolutely_integrable_on s
        ==> (\x. f(x) - g(x)) absolutely_integrable_on s`,
  REWRITE_TAC[VECTOR_SUB] THEN
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_ADD; ABSOLUTELY_INTEGRABLE_NEG]);;

let ABSOLUTELY_INTEGRABLE_LINEAR = prove
 (`!f:real^M->real^N h:real^N->real^P s.
        f absolutely_integrable_on s /\ linear h
        ==> (h o f) absolutely_integrable_on s`,
  SUBGOAL_THEN
   `!f:real^M->real^N h:real^N->real^P.
        f absolutely_integrable_on (:real^M) /\ linear h
        ==> (h o f) absolutely_integrable_on (:real^M)`
  ASSUME_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
     ANTE_RES_THEN MP_TAC th THEN
     ASSUME_TAC(MATCH_MP LINEAR_0 (CONJUNCT2 th))) THEN
    ASM_REWRITE_TAC[o_DEF; COND_RAND]] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE THEN
  FIRST_ASSUM(MP_TAC o
    MATCH_MP ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
  ASM_SIMP_TAC[INTEGRABLE_LINEAR; HAS_BOUNDED_SETVARIATION_ON_UNIV] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o MATCH_MP
              LINEAR_BOUNDED_POS) THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real`) THEN EXISTS_TAC `B * b:real` THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `B * sum d (\k. norm(integral k (f:real^M->real^N)))` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  FIRST_ASSUM(fun t -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION t]) THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(h(integral (interval[a,b]) (f:real^M->real^N)):real^P)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC HAS_INTEGRAL_LINEAR THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
  MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]);;

let ABSOLUTELY_INTEGRABLE_VSUM = prove
 (`!f:A->real^M->real^N s t.
        FINITE t /\
        (!a. a IN t ==> (f a) absolutely_integrable_on s)
        ==>  (\x. vsum t (\a. f a x)) absolutely_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; ABSOLUTELY_INTEGRABLE_0; IN_INSERT;
           ABSOLUTELY_INTEGRABLE_ADD; ETA_AX]);;

let ABSOLUTELY_INTEGRABLE_ABS = prove
 (`!f:real^M->real^N s.
        f absolutely_integrable_on s
        ==> (\x. (lambda i. abs(f(x)$i)):real^N) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. (lambda i. abs(f(x)$i))):real^M->real^N =
    (\x. vsum (1..dimindex(:N))
        (\i. (((\y. (lambda j. if j = i then drop y else &0)) o
               (\x. lift(norm((lambda j. if j = i then x$i else &0):real^N))) o
               (f:real^M->real^N)) x)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
    GEN_REWRITE_TAC I [CART_EQ] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; VSUM_COMPONENT; o_THM] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG; LIFT_DROP] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    REWRITE_TAC[vector_norm; dot] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sqrt(sum (1..dimindex(:N))
                         (\k. if k = i then ((f:real^M->real^N) x)$i pow 2
                              else &0))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG; POW_2_SQRT_ABS]; ALL_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_NUMSEG; LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_POW_2];
    ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_VSUM THEN
  REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LINEAR THEN CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[DROP_ADD; REAL_ADD_LID; DROP_CMUL; REAL_MUL_RZERO]] THEN
  REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
  SUBGOAL_THEN
    `(\x. lambda j. if j = i then (f x:real^N)$i else &0):real^M->real^N =
     (\x. lambda j. if j = i then x$i else &0) o f`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LINEAR THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT]);;

let ABSOLUTELY_INTEGRABLE_MAX = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        f absolutely_integrable_on s /\ g absolutely_integrable_on s
        ==> (\x. (lambda i. max (f(x)$i) (g(x)$i)):real^N)
            absolutely_integrable_on s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_SUB) THEN
  DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_ABS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_ADD) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o
     MATCH_MP ABSOLUTELY_INTEGRABLE_CMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; CART_EQ] THEN
  SIMP_TAC[LAMBDA_BETA; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT;
           VECTOR_ADD_COMPONENT] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let ABSOLUTELY_INTEGRABLE_MAX_1 = prove
 (`!f:real^M->real g:real^M->real s.
        (\x. lift(f x)) absolutely_integrable_on s /\
        (\x. lift(g x)) absolutely_integrable_on s
        ==> (\x. lift(max (f x) (g x))) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (lambda i. max (lift(f x)$i) (lift(g x)$i)):real^1)
                absolutely_integrable_on (s:real^M->bool)`
  MP_TAC THENL [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_MAX]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; CART_EQ] THEN SIMP_TAC[LAMBDA_BETA; lift]);;

let ABSOLUTELY_INTEGRABLE_MIN = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        f absolutely_integrable_on s /\ g absolutely_integrable_on s
        ==> (\x. (lambda i. min (f(x)$i) (g(x)$i)):real^N)
            absolutely_integrable_on s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_SUB) THEN
  DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_ABS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_ADD) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_SUB) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o
     MATCH_MP ABSOLUTELY_INTEGRABLE_CMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; CART_EQ] THEN
  SIMP_TAC[LAMBDA_BETA; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT;
           VECTOR_ADD_COMPONENT] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let ABSOLUTELY_INTEGRABLE_MIN_1 = prove
 (`!f:real^M->real g:real^M->real s.
        (\x. lift(f x)) absolutely_integrable_on s /\
        (\x. lift(g x)) absolutely_integrable_on s
        ==> (\x. lift(min (f x) (g x))) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (lambda i. min (lift(f x)$i) (lift(g x)$i)):real^1)
                absolutely_integrable_on (s:real^M->bool)`
  MP_TAC THENL [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_MIN]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; CART_EQ] THEN SIMP_TAC[LAMBDA_BETA; lift]);;

let ABSOLUTELY_INTEGRABLE_ABS_EQ = prove
 (`!f:real^M->real^N s.
        f absolutely_integrable_on s <=>
          f integrable_on s /\
          (\x. (lambda i. abs(f(x)$i)):real^N) integrable_on s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_ABS;
           ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  SUBGOAL_THEN
   `!f:real^M->real^N.
        f integrable_on (:real^M) /\
        (\x. (lambda i. abs(f(x)$i)):real^N) integrable_on (:real^M)
        ==> f absolutely_integrable_on (:real^M)`
  ASSUME_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV;
                     GSYM INTEGRABLE_RESTRICT_UNIV] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    REWRITE_TAC[CART_EQ] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; COND_COMPONENT; VEC_COMPONENT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ABS_0]] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE THEN
  ASM_REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_UNIV] THEN
  EXISTS_TAC
   `sum (1..dimindex(:N))
        (\i. integral (:real^M)
              (\x. (lambda j. abs ((f:real^M->real^N) x$j)):real^N)$i)` THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d (\k. sum (1..dimindex(:N))
      (\i. integral k
              (\x. (lambda j. abs ((f:real^M->real^N) x$j)):real^N)$i))` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    FIRST_ASSUM(fun t -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION t]) THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (1..dimindex(:N))
             (\i. abs((integral (interval[a,b]) (f:real^M->real^N))$i))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ --x <= y ==> abs(x) <= y`) THEN
    ASM_SIMP_TAC[GSYM VECTOR_NEG_COMPONENT] THEN
    SUBGOAL_THEN `(f:real^M->real^N) integrable_on interval[a,b] /\
        (\x. (lambda i. abs (f x$i)):real^N) integrable_on interval[a,b]`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM INTEGRAL_NEG] THEN
    CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_COMPONENT_LE THEN
    ASM_SIMP_TAC[INTEGRABLE_NEG; LAMBDA_BETA] THEN
    ASM_SIMP_TAC[VECTOR_NEG_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `(integral (UNIONS d)
              (\x. (lambda j. abs ((f:real^M->real^N) x$j)):real^N))$k` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM VSUM_COMPONENT] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_COMBINE_DIVISION_TOPDOWN THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRAL_SUBSET_COMPONENT_LE THEN
    ASM_SIMP_TAC[LAMBDA_BETA; SUBSET_UNIV; REAL_ABS_POS]] THEN
  MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
  MAP_EVERY EXISTS_TAC [`(:real^M)`; `d:(real^M->bool)->bool`] THEN
  ASM_REWRITE_TAC[SUBSET_UNIV]);;

let NONNEGATIVE_ABSOLUTELY_INTEGRABLE = prove
 (`!f:real^M->real^N s.
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N)
               ==> &0 <= f(x)$i) /\
        f integrable_on s
        ==> f absolutely_integrable_on s`,
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_ABS_EQ] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_EQ THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; real_abs]);;

let ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND = prove
 (`!f:real^M->real^N g s.
        (!x. x IN s ==> norm(f x) <= drop(g x)) /\
        f integrable_on s /\ g integrable_on s
        ==> f absolutely_integrable_on s`,
  SUBGOAL_THEN
   `!f:real^M->real^N g.
        (!x. norm(f x) <= drop(g x)) /\
        f integrable_on (:real^M) /\ g integrable_on (:real^M)
        ==> f absolutely_integrable_on (:real^M)`
  ASSUME_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV; GSYM
                     ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(\x. if x IN s then g x else vec 0):real^M->real^1` THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL; NORM_0; DROP_VEC]] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE THEN
  ASM_REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_UNIV] THEN
  EXISTS_TAC `drop(integral(:real^M) g)` THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d (\k. drop(integral k (g:real^M->real^1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (UNIONS d:real^M->bool) g)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x = y ==> y <= x`) THEN
    ASM_SIMP_TAC[GSYM LIFT_EQ; LIFT_DROP; LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC INTEGRAL_COMBINE_DIVISION_BOTTOMUP THEN
    FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[NORM_ARITH `norm(x) <= y ==> &0 <= y`]] THEN
    MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
    MAP_EVERY EXISTS_TAC [`(:real^M)`; `d:(real^M->bool)->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_BOUND = prove
 (`!f:real^M->real^N g:real^M->real^P s.
        (!x. x IN s ==> norm(f x) <= norm(g x)) /\
        f integrable_on s /\ g absolutely_integrable_on s
        ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I
    [absolutely_integrable_on]) THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`; `(\x. lift(norm((g:real^M->real^P) x)))`;
    `s:real^M->bool`] ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let ABSOLUTELY_INTEGRABLE_INF_1 = prove
 (`!fs s:real^N->bool k:A->bool.
        FINITE k /\ ~(k = {}) /\
        (!i. i IN k ==> (\x. lift(fs x i)) absolutely_integrable_on s)
        ==> (\x. lift(inf (IMAGE (fs x) k))) absolutely_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
  SIMP_TAC[INF_INSERT_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `k:A->bool`] THEN
  ASM_CASES_TAC `k:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[IN_SING; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MIN_1 THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let ABSOLUTELY_INTEGRABLE_SUP_1 = prove
 (`!fs s:real^N->bool k:A->bool.
        FINITE k /\ ~(k = {}) /\
        (!i. i IN k ==> (\x. lift(fs x i)) absolutely_integrable_on s)
        ==> (\x. lift(sup (IMAGE (fs x) k))) absolutely_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
  SIMP_TAC[SUP_INSERT_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `k:A->bool`] THEN
  ASM_CASES_TAC `k:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[IN_SING; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX_1 THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let ABSOLUTELY_INTEGRABLE_CONTINUOUS = prove
 (`!f:real^M->real^N a b.
        f continuous_on interval[a,b]
        ==> f absolutely_integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
  SUBGOAL_THEN `compact(IMAGE (f:real^M->real^N) (interval[a,b]))` MP_TAC THENL
   [ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; COMPACT_INTERVAL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:real^M. lift(B)` THEN
  ASM_SIMP_TAC[INTEGRABLE_CONST; LIFT_DROP; INTEGRABLE_CONTINUOUS]);;

let INTEGRABLE_MIN_CONST_1 = prove
 (`!f s t.
        &0 <= t /\ (!x. x IN s ==> &0 <= f x) /\
        (\x:real^N. lift(f x)) integrable_on s
        ==> (\x. lift(min (f x) t)) integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_ON_ALL_INTERVALS_INTEGRABLE_BOUND THEN
  EXISTS_TAC `\x:real^N. lift(f x)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL
     [`\x:real^N. if x IN s then f x else &0`;
      `(\x. t):real^N->real`;
      `interval[a:real^N,b]`] ABSOLUTELY_INTEGRABLE_MIN_1) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [SIMP_TAC[ABSOLUTELY_INTEGRABLE_CONTINUOUS; CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
      REWRITE_TAC[COND_RAND; LIFT_DROP; LIFT_NUM] THEN
      REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
      ASM_SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      ASM_REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; LIFT_DROP; GSYM drop];
      DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[NORM_REAL; GSYM drop; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC]);;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_UBOUND = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N) ==> f(x)$i <= g(x)$i) /\
        f integrable_on s /\ g absolutely_integrable_on s
        ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(\x. (g:real^M->real^N)(x) - (g(x) - f(x))) absolutely_integrable_on s`
  MP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_REWRITE_TAC[REAL_SUB_LE; VECTOR_SUB_COMPONENT] THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    REWRITE_TAC[VECTOR_ARITH `x - (x - y):real^N = y`; ETA_AX]]);;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_LBOUND = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N) ==> f(x)$i <= g(x)$i) /\
        f absolutely_integrable_on s /\ g integrable_on s
        ==> g absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(\x. (f:real^M->real^N)(x) + (g(x) - f(x))) absolutely_integrable_on s`
  MP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_REWRITE_TAC[REAL_SUB_LE; VECTOR_SUB_COMPONENT] THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    REWRITE_TAC[VECTOR_ARITH `y + (x - y):real^N = x`; ETA_AX]]);;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_DROP_UBOUND = prove
 (`!f:real^M->real^1 g:real^M->real^1 s.
        (!x. x IN s ==> drop(f(x)) <= drop(g(x))) /\
        f integrable_on s /\ g absolutely_integrable_on s
        ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
    ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_UBOUND THEN
  EXISTS_TAC `g:real^M->real^1` THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_REWRITE_TAC[IMP_IMP; FORALL_1; DIMINDEX_1; GSYM drop]);;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_DROP_LBOUND = prove
 (`!f:real^M->real^1 g:real^M->real^1 s.
        (!x. x IN s ==> drop(f(x)) <= drop(g(x))) /\
        f absolutely_integrable_on s /\ g integrable_on s
        ==> g absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
    ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_LBOUND THEN
  EXISTS_TAC `f:real^M->real^1` THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_REWRITE_TAC[IMP_IMP; FORALL_1; DIMINDEX_1; GSYM drop]);;

let ABSOLUTELY_INTEGRABLE_PASTECART_SYM = prove
 (`!f:real^(M,N)finite_sum->real^P s y.
        (\z. f(pastecart (sndcart z) (fstcart z))) absolutely_integrable_on
        (IMAGE (\z. pastecart (sndcart z) (fstcart z)) s) <=>
        f absolutely_integrable_on s`,
  REWRITE_TAC[absolutely_integrable_on; INTEGRABLE_PASTECART_SYM]);;

let [HAS_INTEGRAL_PASTECART_SYM_UNIV; INTEGRAL_PASTECART_SYM_UNIV;
    INTEGRABLE_PASTECART_SYM_UNIV; ABSOLUTELY_INTEGRABLE_PASTECART_SYM_UNIV] =
    (CONJUNCTS o prove)
 (`(!f:real^(M,N)finite_sum->real^P s y.
        ((\z. f(pastecart (sndcart z) (fstcart z))) has_integral y) UNIV <=>
        (f has_integral y) UNIV) /\
   (!f:real^(M,N)finite_sum->real^P s y.
        integral UNIV (\z. f(pastecart (sndcart z) (fstcart z))) =
        integral UNIV f) /\
   (!f:real^(M,N)finite_sum->real^P s y.
        (\z. f(pastecart (sndcart z) (fstcart z))) integrable_on UNIV <=>
        f integrable_on UNIV) /\
   (!f:real^(M,N)finite_sum->real^P s y.
     (\z. f(pastecart (sndcart z) (fstcart z)))
     absolutely_integrable_on UNIV <=>
       f absolutely_integrable_on UNIV)`,
  REPEAT STRIP_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM HAS_INTEGRAL_PASTECART_SYM];
    GEN_REWRITE_TAC RAND_CONV [GSYM INTEGRAL_PASTECART_SYM];
    GEN_REWRITE_TAC RAND_CONV [GSYM INTEGRABLE_PASTECART_SYM];
    GEN_REWRITE_TAC RAND_CONV [GSYM ABSOLUTELY_INTEGRABLE_PASTECART_SYM]] THEN
  TRY AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC[IN_UNIV] THEN
  REWRITE_TAC[EXISTS_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[FORALL_PASTECART] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Relating vector integrals to integrals of components.                     *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMPONENTWISE = prove
 (`!f:real^M->real^N s y.
        (f has_integral y) s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> ((\x. lift((f x)$i)) has_integral (lift(y$i))) s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o ISPEC `\u:real^N. lift(u$i)` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o BINDER_CONV)
     [GSYM BASIS_EXPANSION] THEN
    MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o ISPEC `\v. drop(v) % (basis i:real^N)` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
    SIMP_TAC[o_DEF; LIFT_DROP; LINEAR_VMUL_DROP; LINEAR_ID]]);;

let INTEGRABLE_COMPONENTWISE = prove
 (`!f:real^M->real^N s.
        f integrable_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift((f x)$i)) integrable_on s`,
   REPEAT GEN_TAC THEN REWRITE_TAC[integrable_on] THEN
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [HAS_INTEGRAL_COMPONENTWISE] THEN
   REWRITE_TAC[GSYM LAMBDA_SKOLEM; GSYM EXISTS_LIFT]);;

let LIFT_INTEGRAL_COMPONENT = prove
 (`!f:real^M->real^N.
        f integrable_on s
        ==> lift((integral s f)$k) = integral s (\x. lift((f x)$k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?j. 1 <= j /\ j <= dimindex(:N) /\ !z:real^N. z$k = z$j`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_COMPONENTWISE] THEN
  ASM_SIMP_TAC[]);;

let INTEGRAL_COMPONENT = prove
 (`!f:real^M->real^N.
        f integrable_on s
        ==> (integral s f)$k = drop(integral s (\x. lift((f x)$k)))`,
  SIMP_TAC[GSYM LIFT_INTEGRAL_COMPONENT; LIFT_DROP]);;

let ABSOLUTELY_INTEGRABLE_COMPONENTWISE = prove
 (`!f:real^M->real^N s.
     f absolutely_integrable_on s <=>
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> (\x. lift(f x$i)) absolutely_integrable_on s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[absolutely_integrable_on] THEN
  MATCH_MP_TAC(MESON[]
   `(p <=> !i. a i ==> P i) /\
    (p /\ (!i. a i ==> P i) ==> (q <=> (!i. a i ==> Q i)))
    ==> (p /\ q <=> (!i. a i ==> P i /\ Q i))`) THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM INTEGRABLE_COMPONENTWISE]; ALL_TAC] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [SUBGOAL_THEN
     `(\x. lift((f:real^M->real^N) x$i)) absolutely_integrable_on s`
    MP_TAC THENL [ALL_TAC; SIMP_TAC[absolutely_integrable_on]] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
    EXISTS_TAC `\x. lift(norm((f:real^M->real^N) x))` THEN
    ASM_SIMP_TAC[ABS_DROP; LIFT_DROP; COMPONENT_LE_NORM];
    SUBGOAL_THEN
     `(f:real^M->real^N) absolutely_integrable_on s`
    MP_TAC THENL [ALL_TAC; SIMP_TAC[absolutely_integrable_on]] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
    EXISTS_TAC
     `\x. vsum (1..dimindex(:N))
               (\i. lift(norm(lift((f:real^M->real^N)(x)$i))))` THEN
    ASM_SIMP_TAC[INTEGRABLE_VSUM; IN_NUMSEG; FINITE_NUMSEG] THEN
    SIMP_TAC[DROP_VSUM; FINITE_NUMSEG; o_DEF; LIFT_DROP] THEN
    REWRITE_TAC[NORM_LIFT; NORM_LE_L1]]);;

(* ------------------------------------------------------------------------- *)
(* Dominated convergence.                                                    *)
(* ------------------------------------------------------------------------- *)

let DOMINATED_CONVERGENCE = prove
 (`!f:num->real^M->real^N g h s.
        (!k. (f k) integrable_on s) /\ h integrable_on s /\
        (!k x. x IN s ==> norm(f k x) <= drop(h x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`,
  SUBGOAL_THEN
    `!f:num->real^M->real^1 g h s.
        (!k. (f k) integrable_on s) /\ h integrable_on s /\
        (!k x. x IN s ==> norm(f k x) <= drop(h x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!j. 1 <= j /\ j <= dimindex(:N)
          ==> (\x. lift((g x)$j)) integrable_on s /\
              ((\k. integral s (\x. lift (((f:num->real^M->real^N) k x)$j)))
               --> integral s (\x. lift ((g x:real^N)$j))) sequentially`
    STRIP_ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
          [INTEGRABLE_COMPONENTWISE]) THEN
        ASM_SIMP_TAC[];
        MAP_EVERY X_GEN_TAC [`i:num`; `x:real^M`] THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm((f:num->real^M->real^N) i x)` THEN
        ASM_SIMP_TAC[NORM_LIFT; COMPONENT_LE_NORM];
        X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [LIM_COMPONENTWISE_LIFT] THEN
        ASM_SIMP_TAC[]];
      MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC I [INTEGRABLE_COMPONENTWISE] THEN ASM_SIMP_TAC[];
        DISCH_TAC THEN  ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
        ASM_SIMP_TAC[LIFT_INTEGRAL_COMPONENT]]]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MONO_FORALL (GEN `m:num`
   (ISPECL [`\k:num x:real^M. lift(inf {drop(f j x) | j IN m..(m+k)})`;
            `\x:real^M. lift(inf {drop(f j x) | m:num <= j})`;
            `s:real^M->bool`]
           MONOTONE_CONVERGENCE_DECREASING))) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [X_GEN_TAC `m:num` THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INF_1 THEN
      REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
      EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[];

      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC REAL_LE_INF_SUBSET THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET_NUMSEG] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC LOWER_BOUND_FINITE_SET_REAL THEN
      REWRITE_TAC[FINITE_NUMSEG];

      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      REWRITE_TAC[dist; ABS_DROP; LIFT_DROP; DROP_SUB] THEN
      MP_TAC(SPEC `{drop((f:num->real^M->real^1) j x) | m <= j}` INF) THEN
      ABBREV_TAC `i = inf {drop((f:num->real^M->real^1) j x) | m <= j}` THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[IN_ELIM_THM; EXTENSION; NOT_IN_EMPTY] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [MESON_TAC[LE_REFL]; ALL_TAC] THEN
        EXISTS_TAC `--drop(h(x:real^M))` THEN X_GEN_TAC `j:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `x:real^M`]) THEN
        ASM_REWRITE_TAC[ABS_DROP] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `i + e:real`)) THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> ~(i + e <= i)`] THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN STRIP_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `y < i + e ==> i <= ix /\ ix <= y ==> abs(ix - i) < e`)) THEN
      CONJ_TAC THENL
       [EXPAND_TAC "i" THEN MATCH_MP_TAC REAL_LE_INF_SUBSET THEN
        REWRITE_TAC[IMAGE_EQ_EMPTY; SET_RULE `{x | x IN s} = s`] THEN
        REWRITE_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN CONJ_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN
          REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
          REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      W(MP_TAC o C SPEC INF o rand o lhand o snd) THEN ANTS_TAC THENL
       [REWRITE_TAC[IMAGE_EQ_EMPTY; SET_RULE `{x | x IN s} = s`] THEN
        REWRITE_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
        REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        EXISTS_TAC `i:real` THEN GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
        DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
        ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
      ASM_ARITH_TAC;

      REWRITE_TAC[bounded] THEN
      EXISTS_TAC `drop(integral s (h:real^M->real^1))` THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `p:num` THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INF_1 THEN
        REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
        ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
        EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[ABS_DROP; LIFT_DROP] THEN
      MATCH_MP_TAC REAL_ABS_INF_LE THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      ASM_SIMP_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD; GSYM ABS_DROP]];
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  MP_TAC(MATCH_MP MONO_FORALL (GEN `m:num`
   (ISPECL [`\k:num x:real^M. lift(sup {drop(f j x) | j IN m..(m+k)})`;
            `\x:real^M. lift(sup {drop(f j x) | m:num <= j})`;
            `s:real^M->bool`]
           MONOTONE_CONVERGENCE_INCREASING))) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [X_GEN_TAC `m:num` THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUP_1 THEN
      REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
      EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[];

      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET_NUMSEG] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC UPPER_BOUND_FINITE_SET_REAL THEN
      REWRITE_TAC[FINITE_NUMSEG];

      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      REWRITE_TAC[dist; ABS_DROP; LIFT_DROP; DROP_SUB] THEN
      MP_TAC(SPEC `{drop((f:num->real^M->real^1) j x) | m <= j}` SUP) THEN
      ABBREV_TAC `i = sup {drop((f:num->real^M->real^1) j x) | m <= j}` THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[IN_ELIM_THM; EXTENSION; NOT_IN_EMPTY] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [MESON_TAC[LE_REFL]; ALL_TAC] THEN
        EXISTS_TAC `drop(h(x:real^M))` THEN X_GEN_TAC `j:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `x:real^M`]) THEN
        ASM_REWRITE_TAC[ABS_DROP] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `i - e:real`)) THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> ~(i <= i - e)`] THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN STRIP_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `i - e < y ==> ix <= i /\ y <= ix ==> abs(ix - i) < e`)) THEN
      CONJ_TAC THENL
       [EXPAND_TAC "i" THEN MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN
        REWRITE_TAC[IMAGE_EQ_EMPTY; SET_RULE `{x | x IN s} = s`] THEN
        REWRITE_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN CONJ_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN
          REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
          REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      W(MP_TAC o C SPEC SUP o rand o rand o snd) THEN ANTS_TAC THENL
       [REWRITE_TAC[IMAGE_EQ_EMPTY; SET_RULE `{x | x IN s} = s`] THEN
        REWRITE_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
        REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        EXISTS_TAC `i:real` THEN GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
        DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
        ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
      ASM_ARITH_TAC;

      REWRITE_TAC[bounded] THEN
      EXISTS_TAC `drop(integral s (h:real^M->real^1))` THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `p:num` THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUP_1 THEN
        REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
        ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
        EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[ABS_DROP; LIFT_DROP] THEN
      MATCH_MP_TAC REAL_ABS_SUP_LE THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      ASM_SIMP_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD; GSYM ABS_DROP]];
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`\k:num x:real^M. lift(inf {drop(f j x) | k <= j})`;
    `g:real^M->real^1`;
    `s:real^M->bool`]
           MONOTONE_CONVERGENCE_INCREASING) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INF_SUBSET THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; SET_RULE `{x | x IN s} = s`] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_LE] THEN
      CONJ_TAC THENL [MESON_TAC[LT_REFL]; ALL_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `--drop(h(x:real^M))` THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> --a <= x`) THEN
      ASM_SIMP_TAC[GSYM ABS_DROP];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `e:real` THEN DISCH_TAC THEN
                 MP_TAC(SPEC `e / &2` th)) THEN
      ASM_REWRITE_TAC[REAL_HALF] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN
      REWRITE_TAC[dist; ABS_DROP; DROP_SUB; LIFT_DROP] THEN
      STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INF_ASCLOSE THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[LE_TRANS; REAL_LT_IMP_LE]] THEN
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
      MESON_TAC[LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `drop(integral s (h:real^M->real^1))` THEN
    X_GEN_TAC `p:num` THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[ABS_DROP; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_ABS_INF_LE THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[GSYM ABS_DROP; IN_ELIM_THM] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
    MESON_TAC[LE_REFL];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A"))] THEN
  MP_TAC(ISPECL
   [`\k:num x:real^M. lift(sup {drop(f j x) | k <= j})`;
    `g:real^M->real^1`;
    `s:real^M->bool`]
           MONOTONE_CONVERGENCE_DECREASING) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; SET_RULE `{x | x IN s} = s`] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_LE] THEN
      CONJ_TAC THENL [MESON_TAC[LT_REFL]; ALL_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `drop(h(x:real^M))` THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
      ASM_SIMP_TAC[GSYM ABS_DROP];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `e:real` THEN DISCH_TAC THEN
                 MP_TAC(SPEC `e / &2` th)) THEN
      ASM_REWRITE_TAC[REAL_HALF] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN
      REWRITE_TAC[dist; ABS_DROP; DROP_SUB; LIFT_DROP] THEN
      STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_SUP_ASCLOSE THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[LE_TRANS; REAL_LT_IMP_LE]] THEN
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
      MESON_TAC[LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `drop(integral s (h:real^M->real^1))` THEN
    X_GEN_TAC `p:num` THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[ABS_DROP; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_ABS_SUP_LE THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[GSYM ABS_DROP; IN_ELIM_THM] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
    MESON_TAC[LE_REFL];
    DISCH_THEN(LABEL_TAC "B")] THEN
  ASM_REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REMOVE_THEN "A" (MP_TAC o REWRITE_RULE[LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  REMOVE_THEN "B" (MP_TAC o REWRITE_RULE[LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REMOVE_THEN "N1" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `N1 + N2 <= n ==> N1:num <= n`]; ALL_TAC] THEN
  REMOVE_THEN "N2" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `N1 + N2 <= n ==> N2:num <= n`]; ALL_TAC] THEN
  REWRITE_TAC[dist; ABS_DROP; DROP_SUB; LIFT_DROP] THEN
  MATCH_MP_TAC(REAL_ARITH
   `i0 <= i /\ i <= i1
    ==> abs(i1 - g) < e ==> abs(i0 - g) < e ==> abs(i - g) < e`) THEN
  CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THENL
   [W(MP_TAC o C SPEC INF o rand o lhand o snd) THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
      CONJ_TAC THENL [MESON_TAC[LE_REFL]; ALL_TAC] THEN
      EXISTS_TAC `--drop(h(x:real^M))` THEN GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> --a <= x`) THEN
      REWRITE_TAC[GSYM ABS_DROP] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN REWRITE_TAC[LE_REFL]];
    W(MP_TAC o C SPEC SUP o rand o rand o snd) THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
      CONJ_TAC THENL [MESON_TAC[LE_REFL]; ALL_TAC] THEN
      EXISTS_TAC `drop(h(x:real^M))` THEN GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
      REWRITE_TAC[GSYM ABS_DROP] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN REWRITE_TAC[LE_REFL]]]);;

let DOMINATED_CONVERGENCE_INTEGRABLE = prove
 (`!f:num->real^M->real^N g h s.
         (!k. f k absolutely_integrable_on s) /\
         h integrable_on s /\
         (!k x. x IN s ==> norm(g x) <= drop(h x)) /\
         (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
         ==> g integrable_on s`,
  let lemma = prove
   (`!f:num->real^N->real^1 g h s.
          (!k. f k absolutely_integrable_on s) /\
          h integrable_on s /\
          (!x. x IN s ==> norm(g x) <= drop(h x)) /\
          (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
          ==> g integrable_on s`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^N->real^1) absolutely_integrable_on s`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
      ASM_REWRITE_TAC[DIMINDEX_1; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; IMP_IMP] THEN
      ASM_MESON_TAC[REAL_LE_TRANS; NORM_POS_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\n:num x:real^N.
         lift(min (max (--(drop(h x))) (drop(f n x))) (drop(h x)))`;
      `g:real^N->real^1`;
      `h:real^N->real^1`;
      `s:real^N->bool`] DOMINATED_CONVERGENCE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MIN_1 THEN
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX_1 THEN
      ASM_SIMP_TAC[LIFT_NEG; LIFT_DROP; ETA_AX; ABSOLUTELY_INTEGRABLE_NEG];
      MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN DISCH_TAC THEN
      REWRITE_TAC[LIFT_DROP; ABS_DROP] THEN
      SUBGOAL_THEN `&0 <= drop((h:real^N->real^1) x)` MP_TAC THENL
       [ASM_MESON_TAC[REAL_LE_TRANS; NORM_POS_LE]; REAL_ARITH_TAC];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      UNDISCH_TAC
       `!x. x IN s ==> ((\n. (f:num->real^N->real^1) n x) --> g x)
                          sequentially` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[tendsto] THEN MATCH_MP_TAC MONO_FORALL THEN
      X_GEN_TAC `e:real` THEN ASM_CASES_TAC `&0 < e` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[dist; ABS_DROP; DROP_SUB; LIFT_DROP] THEN
      REAL_ARITH_TAC]) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_COMPONENTWISE;
                   INTEGRABLE_COMPONENTWISE] THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC lemma THEN
  EXISTS_TAC `\i x. lift(((f:num->real^M->real^N) i x)$k)` THEN
  EXISTS_TAC `h:real^M->real^1` THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[COMPONENT_LE_NORM; NORM_LIFT; REAL_LE_TRANS];
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[LIM_COMPONENTWISE_LIFT]) THEN
    RULE_ASSUM_TAC BETA_RULE THEN ASM_SIMP_TAC[]]);;

let DOMINATED_CONVERGENCE_ABSOLUTELY_INTEGRABLE = prove
 (`!f:num->real^M->real^N g h s.
         (!k. f k absolutely_integrable_on s) /\
         h integrable_on s /\
         (!k x. x IN s ==> norm(g x) <= drop(h x)) /\
         (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
         ==> g absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
  EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DOMINATED_CONVERGENCE_INTEGRABLE THEN
  EXISTS_TAC `f:num->real^M->real^N` THEN
  EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[]);;

let DOMINATED_CONVERGENCE_AE = prove
 (`!f:num->real^M->real^N g h s t.
        (!k. (f k) integrable_on s) /\ h integrable_on s /\ negligible t /\
        (!k x. x IN s DIFF t ==> norm(f k x) <= drop(h x)) /\
        (!x. x IN s DIFF t ==> ((\k. f k x) --> g x) sequentially)
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real^M->real^N`; `g:real^M->real^N`;
                 `h:real^M->real^1`; `s DIFF t:real^M->bool`]
        DOMINATED_CONVERGENCE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SPIKE_SET;
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
      TRY ABS_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE_SET]] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A few more properties of negligible sets.                                 *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_ON_UNIV = prove
 (`!s. negligible s <=> (indicator s has_integral vec 0) (:real^N)`,
  GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[NEGLIGIBLE]; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[negligible] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  SUBGOAL_THEN `indicator s integrable_on interval[a:real^N,b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real^N)` THEN ASM_MESON_TAC[SUBSET_UNIV; integrable_on];
    ASM_SIMP_TAC[GSYM INTEGRAL_EQ_HAS_INTEGRAL] THEN
    REWRITE_TAC[GSYM DROP_EQ; GSYM REAL_LE_ANTISYM] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP INTEGRAL_UNIQUE) THEN
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE;
      REWRITE_TAC[DROP_VEC] THEN MATCH_MP_TAC INTEGRAL_DROP_POS] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; DROP_INDICATOR_POS_LE] THEN
    ASM_MESON_TAC[integrable_on]]);;

let NEGLIGIBLE_COUNTABLE_UNIONS = prove
 (`!s:num->real^N->bool.
        (!n. negligible(s n)) ==> negligible(UNIONS {s(n) | n IN (:num)})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. indicator(UNIONS {(s:num->real^N->bool)(m) | m <= n})`;
             `indicator(UNIONS {(s:num->real^N->bool)(m) | m IN (:num)})`;
                 `(:real^N)`] MONOTONE_CONVERGENCE_INCREASING) THEN
  SUBGOAL_THEN
   `!n. negligible(UNIONS {(s:num->real^N->bool)(m) | m <= n})`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LE; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:num. (indicator (UNIONS {s m | m <= n})) integrable_on (:real^N)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[NEGLIGIBLE_ON_UNIV; integrable_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:num. integral (:real^N) (indicator (UNIONS {s m | m <= n})) = vec 0`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[NEGLIGIBLE_ON_UNIV; INTEGRAL_UNIQUE]; ALL_TAC] THEN
  ASM_SIMP_TAC[NEGLIGIBLE_ON_UNIV; LIM_CONST_EQ;
               TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[INTEGRAL_EQ_HAS_INTEGRAL]] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `x:real^N`] THEN DISCH_TAC THEN
    REWRITE_TAC[indicator] THEN
    SUBGOAL_THEN
     `x IN UNIONS {(s:num->real^N->bool) m | m <= k}
      ==> x IN UNIONS {s m | m <= SUC k}`
    MP_TAC THENL
     [SPEC_TAC(`x:real^N`,`x:real^N`) THEN
      REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      REWRITE_TAC[DROP_VEC; REAL_LE_REFL; REAL_POS]];
    X_GEN_TAC `x:real^N` THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; indicator] THEN
    ASM_CASES_TAC `x IN UNIONS {(s:num->real^N->bool) m | m IN (:num)}` THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [UNIONS_GSPEC]) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (RAND_CONV o RAND_CONV)
        [UNIONS_GSPEC]) THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]];
    REWRITE_TAC[SET_RULE `{c | x | x IN UNIV} = {c}`;
                BOUNDED_INSERT; BOUNDED_EMPTY]]);;

let HAS_INTEGRAL_NEGLIGIBLE_EQ = prove
 (`!f:real^M->real^N s.
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N) ==> &0 <= f(x)$i)
        ==> ((f has_integral vec 0) s <=>
             negligible {x | x IN s /\ ~(f x = vec 0)})`,
  let lemma = prove
   (`!f:real^N->real^1 s.
          (!x. x IN s ==> &0 <= drop(f x)) /\ (f has_integral vec 0) s
          ==> negligible {x | x IN s /\ ~(f x = vec 0)}`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC
     `UNIONS {{x | x IN s /\ norm((f:real^N->real^1) x) >= &1 / (&n + &1)} |
              n IN (:num)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[NEGLIGIBLE_ON_UNIV; indicator] THEN
      MATCH_MP_TAC HAS_INTEGRAL_STRADDLE_NULL THEN
      EXISTS_TAC `(\x. if x IN s then (&n + &1) % f(x) else vec 0):
                  real^N->real^1` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[IN_UNIV; IN_ELIM_THM; real_ge] THEN
        X_GEN_TAC `x:real^N` THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[DROP_VEC; DROP_CMUL; REAL_POS] THENL
         [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
          ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
          MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ a <= abs x ==> a <= x`) THEN
          ASM_SIMP_TAC[GSYM ABS_DROP];
          COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC; REAL_POS; DROP_CMUL] THEN
          ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL; REAL_LE_ADD]];
        REWRITE_TAC[HAS_INTEGRAL_RESTRICT_UNIV] THEN
        SUBST1_TAC(VECTOR_ARITH `vec 0:real^1 = (&n + &1) % vec 0`) THEN
        MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[GSYM NORM_POS_LT] THEN ONCE_REWRITE_TAC[REAL_ARCH_INV] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num`
        STRIP_ASSUME_TAC)) THEN
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
      EXISTS_TAC `n - 1` THEN ASM_SIMP_TAC[IN_UNIV; IN_ELIM_THM; real_ge] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_ADD; SUB_ADD; LE_1] THEN
      ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_LT_IMP_LE]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HAS_INTEGRAL_NEGLIGIBLE THEN
    EXISTS_TAC `{x | x IN s /\ ~((f:real^M->real^N) x = vec 0)}` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `UNIONS {{x | x IN s /\ ~(((f:real^M->real^N) x)$k = &0)} |
                      k IN 1..dimindex(:N)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM] THEN MATCH_MP_TAC lemma THEN
    ASM_SIMP_TAC[LIFT_DROP] THEN
    FIRST_X_ASSUM(MP_TAC o ISPEC `\y:real^N. lift(y$k)` o
      MATCH_MP(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
    REWRITE_TAC[o_DEF; VEC_COMPONENT; LIFT_NUM] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[linear] THEN
    SIMP_TAC[LIFT_ADD; VECTOR_ADD_COMPONENT; LIFT_CMUL; VECTOR_MUL_COMPONENT];
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC; CART_EQ; IN_NUMSEG] THEN
    REWRITE_TAC[VEC_COMPONENT; IN_ELIM_THM] THEN MESON_TAC[]]);;

let NEGLIGIBLE_COUNTABLE = prove
 (`!s:real^N->bool. COUNTABLE s ==> negligible s`,
  let lemma = prove
   (`IMAGE f s = UNIONS {{f x} | x IN s}`,
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIONS; IN_SING; IN_ELIM_THM] THEN
    MESON_TAC[IN_SING]) in
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^N` SUBST1_TAC o
    MATCH_MP COUNTABLE_AS_IMAGE) THEN
  ONCE_REWRITE_TAC[lemma] THEN MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
  REWRITE_TAC[NEGLIGIBLE_SING]);;

(* ------------------------------------------------------------------------- *)
(* More basic "almost everywhere" variants of other theorems.                *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMPONENT_LE_AE = prove
 (`!f:real^M->real^N g:real^M->real^N s i j k t.
        1 <= k /\ k <= dimindex(:N) /\ negligible t /\
        (f has_integral i) s /\ (g has_integral j) s /\
        (!x. x IN s DIFF t ==> (f x)$k <= (g x)$k)
        ==> i$k <= j$k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_LE THEN
  EXISTS_TAC `\x. if x IN t then vec 0 else (f:real^M->real^N) x` THEN
  EXISTS_TAC `\x. if x IN t then vec 0 else (g:real^M->real^N) x` THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN EXISTS_TAC `f:real^M->real^N` THEN
    EXISTS_TAC `t:real^M->bool` THEN ASM_SIMP_TAC[IN_DIFF];
    MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN EXISTS_TAC `g:real^M->real^N` THEN
    EXISTS_TAC `t:real^M->bool` THEN ASM_SIMP_TAC[IN_DIFF];
    COND_CASES_TAC THEN ASM_SIMP_TAC[IN_DIFF; REAL_LE_REFL]]);;

let INTEGRAL_COMPONENT_LE_AE = prove
 (`!f:real^M->real^N g:real^M->real^N s k t.
        1 <= k /\ k <= dimindex(:N) /\ negligible t /\
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s DIFF t ==> (f x)$k <= (g x)$k)
        ==> (integral s f)$k <= (integral s g)$k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_LE_AE THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_DROP_LE_AE = prove
 (`!f:real^M->real^1 g:real^M->real^1 s i j t.
        (f has_integral i) s /\ (g has_integral j) s /\
        negligible t /\ (!x. x IN s DIFF t ==> drop(f x) <= drop(g x))
        ==> drop i <= drop j`,
  REWRITE_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_LE_AE THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN ASM_MESON_TAC[]);;

let INTEGRAL_DROP_LE_AE = prove
 (`!f:real^M->real^1 g:real^M->real^1 s t.
        f integrable_on s /\ g integrable_on s /\
        negligible t /\ (!x. x IN s DIFF t ==> drop(f x) <= drop(g x))
        ==> drop(integral s f) <= drop(integral s g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_DROP_LE_AE THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let NONNEGATIVE_ABSOLUTELY_INTEGRABLE_AE = prove
 (`!f:real^M->real^N s t.
        negligible t /\
        (!x i. x IN s DIFF t /\ 1 <= i /\ i <= dimindex(:N)
               ==> &0 <= f(x)$i) /\
        f integrable_on s
        ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
  EXISTS_TAC `\x. if x IN s DIFF t then (f:real^M->real^N) x else vec 0` THEN
  EXISTS_TAC `t:real^M->bool` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_REFL; VEC_COMPONENT]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `t:real^M->bool`] THEN
  ASM_SIMP_TAC[]);;

let INTEGRAL_NORM_BOUND_INTEGRAL_AE = prove
 (`!f:real^M->real^N g s t.
        f integrable_on s /\ g integrable_on s /\
        negligible t /\ (!x. x IN s DIFF t ==> norm(f x) <= drop(g x))
        ==> norm(integral s f) <= drop(integral s g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. if x IN s DIFF t then (f:real^M->real^N) x else vec 0`;
    `\x. if x IN s DIFF t then (g:real^M->real^1) x else vec 0`;
    `s:real^M->bool`]
    INTEGRAL_NORM_BOUND_INTEGRAL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `f:real^M->real^N`;
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `g:real^M->real^1`;
      ASM_MESON_TAC[REAL_LE_REFL; NORM_0; DROP_VEC]] THEN
    EXISTS_TAC `t:real^M->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `t:real^M->bool` THEN
    ASM_SIMP_TAC[]]);;
