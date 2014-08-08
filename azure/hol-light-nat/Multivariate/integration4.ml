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
include Integration3

(* ------------------------------------------------------------------------- *)
(* Beppo Levi theorem.                                                       *)
(* ------------------------------------------------------------------------- *)

let BEPPO_LEVI_INCREASING = prove
 (`!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  !x. x IN (s DIFF k) ==> ((\k. f k x) --> g x) sequentially`,
  SUBGOAL_THEN
   `!f:num->real^N->real^1 s.
        (!k x. x IN s ==> &0 <= drop(f k x)) /\
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  !x. x IN (s DIFF k) ==> ((\k. f k x) --> g x) sequentially`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o ISPECL
     [`\n x:real^N. f(n:num) x - f 0 x:real^1`; `s:real^N->bool`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_SUB; REAL_SUB_LE] THEN
      MP_TAC(ISPEC
        `\m n:num. drop (f m (x:real^N)) <= drop (f n x)`
        TRANSITIVE_STEPWISE_LE) THEN
      REWRITE_TAC[REAL_LE_TRANS; REAL_LE_REFL] THEN ASM_MESON_TAC[LE_0];
      GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_SUB; REAL_SUB_LE] THEN
      ASM_SIMP_TAC[REAL_ARITH `x - a <= y - a <=> x <= y`];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
      ASM_SIMP_TAC[INTEGRAL_SUB; ETA_AX; bounded] THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real`
        (fun th -> EXISTS_TAC `B + norm(integral s (f 0:real^N->real^1))` THEN
                   X_GEN_TAC `k:num` THEN MP_TAC(SPEC `k:num` th))) THEN
      NORM_ARITH_TAC;
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^1` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(\x. g x + f 0 x):real^N->real^1` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN
      REWRITE_TAC[VECTOR_ARITH `a - b - c:real^1 = a - (c + b)`]]] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `g = \i n:num x:real^N. lift(min (drop(f n x) / (&i + &1)) (&1))` THEN
  SUBGOAL_THEN
   `!i n. ((g:num->num->real^N->real^1) i n) integrable_on s`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "g" THEN
    MATCH_MP_TAC INTEGRABLE_MIN_CONST_1 THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_DIV; REAL_LE_ADD] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    ASM_SIMP_TAC[LIFT_CMUL; LIFT_DROP; INTEGRABLE_CMUL; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i:num k:num x:real^N. x IN s ==> drop(g i k x) <= drop(g i (SUC k) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> min x a <= min y a`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &n + &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i:num k:num x:real^N. x IN s ==> norm(g i k x:real^1) <= &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[LIFT_DROP; NORM_REAL; GSYM drop] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs(min x (&1)) <= &1`) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_DIV; REAL_LE_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i:num x:real^N. x IN s ==> ?h:real^1. ((\n. g i n x) --> h) sequentially`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\n. drop(g (i:num) (n:num) (x:real^N))`; `&1`]
     CONVERGENT_BOUNDED_MONOTONE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[GSYM ABS_DROP] THEN DISJ1_TAC THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_LE_TRANS] THEN REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `l:real` (fun th ->
        EXISTS_TAC `lift l` THEN MP_TAC th)) THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; DIST_REAL; GSYM drop; LIFT_DROP]];
    GEN_REWRITE_TAC (LAND_CONV o REDEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `h:num->real^N->real^1` THEN STRIP_TAC THEN
  MP_TAC(GEN `i:num `(ISPECL
   [`g(i:num):num->real^N->real^1`; `h(i:num):real^N->real^1`;
    `s:real^N->bool`] MONOTONE_CONVERGENCE_INCREASING)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MONO_FORALL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[bounded] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:real` THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_UNIV] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC(REAL_ARITH
     `norm a = drop a /\ x <= drop a ==> x <= norm a`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NORM_REAL; GSYM drop; REAL_ABS_REFL] THEN
      MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      EXPAND_TAC "g" THEN REWRITE_TAC[NORM_REAL; GSYM drop; LIFT_DROP] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ x <= y ==> abs(min x (&1)) <= y`) THEN
      ASM_SIMP_TAC[REAL_LE_ADD; REAL_POS; REAL_LE_DIV] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &i + &1`] THEN
      REWRITE_TAC[REAL_ARITH `a <= a * (x + &1) <=> &0 <= a * x`] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]];
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  ABBREV_TAC
   `Z =
    {x:real^N | x IN s /\ ~(?l:real^1. ((\k. f k x) --> l) sequentially)}` THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN EXISTS_TAC `Z:real^N->bool` THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
  CONJ_TAC THENL
   [ALL_TAC; EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[]] THEN
  MP_TAC(ISPECL
   [`h:num->real^N->real^1`;
    `(\x. if x IN Z then vec 1 else vec 0):real^N->real^1`;
    `s:real^N->bool`]
        MONOTONE_CONVERGENCE_DECREASING) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i x:real^N. x IN s ==> drop(h (SUC i) x) <= drop(h i x)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `x:real^N`] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LE) THEN
    EXISTS_TAC `\n. (g:num->num->real^N->real^1) (SUC i) n x` THEN
    EXISTS_TAC `\n. (g:num->num->real^N->real^1) i n x` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> min x a <= min y a`) THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. norm(integral s ((h:num->real^N->real^1) i)) <= B / (&i + &1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC `\k. integral s ((g:num->num->real^N->real^1) i k)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral s (\x. inv(&i + &1) % (f:num->real^N->real^1) n x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_SIMP_TAC[INTEGRABLE_CMUL; ETA_AX] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
      REWRITE_TAC[NORM_REAL; GSYM drop; LIFT_DROP; DROP_CMUL] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ x <= y ==> abs(min x (&1)) <= y`) THEN
      ASM_SIMP_TAC[REAL_LE_ADD; REAL_POS; REAL_LE_DIV] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRAL_CMUL; ETA_AX; DROP_CMUL] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_DIV2_EQ;
                   REAL_ARITH `&0 < &n + &1`] THEN
      MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
      ASM_REWRITE_TAC[GSYM ABS_DROP]];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [ALL_TAC;
      EXISTS_TAC `B:real` THEN X_GEN_TAC `i:num` THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `B / (&i + &1)` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &i + &1`] THEN
      REWRITE_TAC[REAL_ARITH `B <= B * (i + &1) <=> &0 <= i * B`] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE]] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^N) IN Z` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC LIM_EVENTUALLY THEN
      UNDISCH_TAC `(x:real^N) IN Z` THEN EXPAND_TAC "Z" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(GEN `B:real` (ISPECL
        [`\n. drop(f (n:num) (x:real^N))`; `B:real`]
        CONVERGENT_BOUNDED_MONOTONE)) THEN
      REWRITE_TAC[LEFT_FORALL_IMP_THM; LEFT_EXISTS_AND_THM] THEN
      MATCH_MP_TAC(TAUT
       `q /\ ~r /\ (q ==> ~p ==> s)
        ==> (p /\ (q \/ q') ==> r) ==> s`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
        ASM_SIMP_TAC[REAL_LE_REFL; REAL_LE_TRANS] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
        ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
        DISCH_THEN(MP_TAC o SPEC `lift l`) THEN
        REWRITE_TAC[LIM_SEQUENTIALLY] THEN
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[DIST_REAL; GSYM drop; DROP_SUB; LIFT_DROP];
        ALL_TAC] THEN
      DISCH_TAC THEN REWRITE_TAC[NOT_FORALL_THM; EVENTUALLY_SEQUENTIALLY] THEN
      REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; REAL_NOT_LE] THEN
      DISCH_TAC THEN
      EXISTS_TAC `0` THEN  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `(\n. (g:num->num->real^N->real^1) i n x)` THEN
      ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
      MATCH_MP_TAC LIM_EVENTUALLY THEN
      EXPAND_TAC "g" THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&i + &1`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN
      REWRITE_TAC[REAL_ARITH `min a b = b <=> b <= a`] THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &i + &1`; REAL_MUL_LID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `a < abs N ==> &0 <= N /\ N <= n ==> a <= n`)) THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `~((x:real^N) IN Z)` THEN EXPAND_TAC "Z" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `l:real^1` THEN
      DISCH_THEN(MP_TAC o MATCH_MP CONVERGENT_IMP_BOUNDED) THEN
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(ISPEC `e / C:real` REAL_ARCH_INV) THEN
      ASM_SIMP_TAC[REAL_LT_DIV] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `N:num` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN STRIP_TAC THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N) * C` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C / (&i + &1)` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
        ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN
        ASM_ARITH_TAC] THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
      EXISTS_TAC `\n. (g:num->num->real^N->real^1) i n x` THEN
      ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
      EXPAND_TAC "g" THEN REWRITE_TAC[NORM_REAL; GSYM drop; LIFT_DROP] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ x <= a ==> abs(min x (&1)) <= a`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_ADD; REAL_POS] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &i + &1`] THEN
      MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
      ASM_REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP]];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC(MESON[LIM_UNIQUE; TRIVIAL_LIMIT_SEQUENTIALLY]
     `(f --> vec 0) sequentially /\ (i = vec 0 ==> p)
      ==> (f --> i) sequentially ==> p`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LIM_NULL_COMPARISON THEN
      EXISTS_TAC `\i. B / (&i + &1)` THEN
      ASM_SIMP_TAC[ALWAYS_EVENTUALLY] THEN
      REWRITE_TAC[real_div; LIFT_CMUL] THEN
      SUBST1_TAC(VECTOR_ARITH `vec 0:real^1 = B % vec 0`) THEN
      MATCH_MP_TAC LIM_CMUL THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN
      X_GEN_TAC `e:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; GSYM drop; LIFT_DROP; REAL_ABS_INV] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRAL_EQ_HAS_INTEGRAL] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) HAS_INTEGRAL_NEGLIGIBLE_EQ o
        lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
        REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; GSYM drop] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[DROP_VEC; REAL_POS];
        DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
        SIMP_TAC[SUBSET; IN_ELIM_THM; VEC_EQ; ARITH_EQ] THEN
        EXPAND_TAC "Z" THEN SIMP_TAC[IN_ELIM_THM]]]]);;

let BEPPO_LEVI_DECREASING = prove
 (`!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f (SUC k) x) <= drop(f k x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  !x. x IN (s DIFF k) ==> ((\k. f k x) --> g x) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. --((f:num->real^N->real^1) n x)`; `s:real^N->bool`]
        BEPPO_LEVI_INCREASING) THEN
  ASM_SIMP_TAC[INTEGRABLE_NEG; DROP_NEG; ETA_AX; REAL_LE_NEG2] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[bounded] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    ASM_SIMP_TAC[INTEGRAL_NEG; ETA_AX; NORM_NEG];
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `k:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\x. --((g:real^N->real^1) x)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV)
      [GSYM VECTOR_NEG_NEG] THEN
    ASM_SIMP_TAC[LIM_NEG_EQ]]);;

let BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING = prove
 (`!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  (!x. x IN (s DIFF k)
                       ==> ((\k. f k x) --> g x) sequentially) /\
                  g integrable_on s /\
                  ((\k. integral s (f k)) --> integral s g) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BEPPO_LEVI_INCREASING) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^1` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(g:real^N->real^1) integrable_on (s DIFF k) /\
    ((\i. integral (s DIFF k) (f i)) --> integral (s DIFF k) g) sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC MONOTONE_CONVERGENCE_INCREASING THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_conj o concl));
    ALL_TAC] THEN
  (SUBGOAL_THEN
    `!f:real^N->real^1. integral (s DIFF k) f = integral s f /\
                        (f integrable_on (s DIFF k) <=> f integrable_on s)`
    (fun th -> SIMP_TAC[th; IN_DIFF]) THEN
   GEN_TAC THEN CONJ_TAC THEN TRY EQ_TAC THEN
   (MATCH_MP_TAC INTEGRABLE_SPIKE_SET ORELSE
    MATCH_MP_TAC INTEGRAL_SPIKE_SET) THEN
   FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN
     SET_TAC[]));;

let BEPPO_LEVI_MONOTONE_CONVERGENCE_DECREASING = prove
 (`!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f (SUC k) x) <= drop(f k x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  (!x. x IN (s DIFF k)
                       ==> ((\k. f k x) --> g x) sequentially) /\
                  g integrable_on s /\
                  ((\k. integral s (f k)) --> integral s g) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BEPPO_LEVI_DECREASING) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^1` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(g:real^N->real^1) integrable_on (s DIFF k) /\
    ((\i. integral (s DIFF k) (f i)) --> integral (s DIFF k) g) sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC MONOTONE_CONVERGENCE_DECREASING THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_conj o concl));
    ALL_TAC] THEN
  (SUBGOAL_THEN
    `!f:real^N->real^1. integral (s DIFF k) f = integral s f /\
                        (f integrable_on (s DIFF k) <=> f integrable_on s)`
    (fun th -> SIMP_TAC[th; IN_DIFF]) THEN
   GEN_TAC THEN CONJ_TAC THEN TRY EQ_TAC THEN
   (MATCH_MP_TAC INTEGRABLE_SPIKE_SET ORELSE
    MATCH_MP_TAC INTEGRAL_SPIKE_SET) THEN
   FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN
     SET_TAC[]));;

let BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING_AE = prove
 (`!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k. ?t. negligible t /\
                 !x. x IN s DIFF t ==> drop(f k x) <= drop(f (SUC k) x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  (!x. x IN (s DIFF k)
                       ==> ((\k. f k x) --> g x) sequentially) /\
                  g integrable_on s /\
                  ((\k. integral s (f k)) --> integral s g) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\n x. if x IN UNIONS {t k | k IN (:num)} then vec 0
           else (f:num->real^N->real^1) n x`; `s:real^N->bool`]
        BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING) THEN
  SUBGOAL_THEN
   `negligible(UNIONS {t k | k IN (:num)}:real^N->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[NEGLIGIBLE_COUNTABLE_UNIONS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `(f:num->real^N->real^1) k` THEN
      EXISTS_TAC `UNIONS {t k | k IN (:num)}:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF];
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        BOUNDED_SUBSET)) THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> f x = g x)
        ==> {f x | x IN s} SUBSET {g x | x IN s}`) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC `UNIONS {t k | k IN (:num)}:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^1` THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u UNION UNIONS {t k | k IN (:num)}:real^N->bool` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[IN_DIFF];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
         `(f --> l) sequentially ==> f = g ==> (g --> l) sequentially`)) THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC `UNIONS {t k | k IN (:num)}:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF]]]);;

let BEPPO_LEVI_MONOTONE_CONVERGENCE_DECREASING_AE = prove
 (`!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k. ?t. negligible t /\
                 !x. x IN s DIFF t ==> drop(f (SUC k) x) <= drop(f k x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  (!x. x IN (s DIFF k)
                       ==> ((\k. f k x) --> g x) sequentially) /\
                  g integrable_on s /\
                  ((\k. integral s (f k)) --> integral s g) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\n x. if x IN UNIONS {t k | k IN (:num)} then vec 0
           else (f:num->real^N->real^1) n x`; `s:real^N->bool`]
        BEPPO_LEVI_MONOTONE_CONVERGENCE_DECREASING) THEN
  SUBGOAL_THEN
   `negligible(UNIONS {t k | k IN (:num)}:real^N->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[NEGLIGIBLE_COUNTABLE_UNIONS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `(f:num->real^N->real^1) k` THEN
      EXISTS_TAC `UNIONS {t k | k IN (:num)}:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF];
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        BOUNDED_SUBSET)) THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> f x = g x)
        ==> {f x | x IN s} SUBSET {g x | x IN s}`) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC `UNIONS {t k | k IN (:num)}:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^1` THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u UNION UNIONS {t k | k IN (:num)}:real^N->bool` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[IN_DIFF];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
         `(f --> l) sequentially ==> f = g ==> (g --> l) sequentially`)) THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC `UNIONS {t k | k IN (:num)}:real^N->bool` THEN
      ASM_SIMP_TAC[IN_DIFF]]]);;

(* ------------------------------------------------------------------------- *)
(* Fatou's lemma and Lieb's extension.                                       *)
(* ------------------------------------------------------------------------- *)

let FATOU = prove
 (`!f:num->real^N->real^1 g s t B.
        negligible t /\
        (!n. (f n) integrable_on s) /\
        (!n x. x IN s DIFF t ==> &0 <= drop(f n x)) /\
        (!x. x IN s DIFF t ==> ((\n. f n x) --> g x) sequentially) /\
        (!n. drop(integral s (f n)) <= B)
        ==> g integrable_on s /\
            &0 <= drop(integral s g) /\ drop(integral s g) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `h = \n x. lift(inf {drop((f:num->real^N->real^1) j x) | n <= j})` THEN
  MP_TAC(MATCH_MP MONO_FORALL (GEN `m:num`
   (ISPECL [`\k:num x:real^N. lift(inf {drop(f j x) | j IN m..(m+k)})`;
            `(h:num->real^N->real^1) m`;
            `s:real^N->bool`; `t:real^N->bool`]
           MONOTONE_CONVERGENCE_DECREASING_AE))) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [X_GEN_TAC `m:num` THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INF_1 THEN
      REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE_AE THEN
      EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      ASM_REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; GSYM drop];
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
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      REWRITE_TAC[dist; ABS_DROP; LIFT_DROP; DROP_SUB] THEN
      MP_TAC(SPEC `{drop((f:num->real^N->real^1) j x) | m <= j}` INF) THEN
      ABBREV_TAC `i = inf {drop((f:num->real^N->real^1) j x) | m <= j}` THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[IN_ELIM_THM; EXTENSION; NOT_IN_EMPTY] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `i + e:real`)) THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> ~(i + e <= i)`] THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
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
      REWRITE_TAC[bounded] THEN EXISTS_TAC `B:real` THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; NORM_REAL; GSYM drop] THEN
      X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= b ==> abs(x) <= b`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRAL_DROP_POS_AE THEN
        EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
        CONJ_TAC THENL
         [ALL_TAC;
          REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INF THEN
          ASM_SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
          REWRITE_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD]];
        TRANS_TAC REAL_LE_TRANS
          `drop (integral s ((f:num->real^N->real^1) m))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ALL_TAC;
          SIMP_TAC[REAL_INF_LE_FINITE; LIFT_DROP; SIMPLE_IMAGE;
                   FINITE_IMAGE; IMAGE_EQ_EMPTY; FINITE_NUMSEG; IN_NUMSEG;
                   NUMSEG_EMPTY; NOT_LT; LE_ADD; EXISTS_IN_IMAGE] THEN
          MESON_TAC[REAL_LE_REFL; LE_REFL; LE_ADD]]] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INF_1 THEN
      REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE_AE THEN
      EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      ASM_REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; GSYM drop]];
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`h:num->real^N->real^1`; `g:real^N->real^1`;
                 `s:real^N->bool`; `t:real^N->bool`]
    MONOTONE_CONVERGENCE_INCREASING_AE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n. &0 <= drop(integral s ((h:num->real^N->real^1) n)) /\
        drop(integral s ((h:num->real^N->real^1) n)) <= B`
  MP_TAC THENL
   [X_GEN_TAC `m:num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS_AE THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
      EXPAND_TAC "h" THEN REWRITE_TAC[LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INF THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      MESON_TAC[LE_REFL];
      TRANS_TAC REAL_LE_TRANS
        `drop (integral s ((f:num->real^N->real^1) m))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[LIFT_DROP] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM INF_SING] THEN
      MATCH_MP_TAC  REAL_LE_INF_SUBSET THEN
      REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET; FORALL_IN_GSPEC] THEN
      CONJ_TAC THENL [REWRITE_TAC[IN_ELIM_THM]; ASM_MESON_TAC[]] THEN
      MESON_TAC[LE_REFL; REAL_LE_REFL]];
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC REAL_LE_INF_SUBSET THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_LE] THEN
      REPEAT CONJ_TAC THENL
       [MESON_TAC[LT_REFL];
        MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
        ASM_MESON_TAC[]];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_TAC THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
      ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `N:num` THEN REWRITE_TAC[DIST_REAL; GSYM drop] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 < e /\ g - e / &2 <= h /\ h <= g + e / &2 ==> abs(h - g) < e`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "h" THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC REAL_INF_BOUNDS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      REWRITE_TAC[SET_RULE `{f n | P n} = {} <=> !n. ~P n`] THEN
      CONJ_TAC THENL [MESON_TAC[LE_REFL]; GEN_TAC THEN DISCH_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(h - g) < e / &2 ==> g - e / &2 <= h /\ h <= g + e / &2`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[LE_TRANS];
      REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN EXISTS_TAC `B:real` THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_REAL; GSYM drop] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= b ==> abs x <= b`) THEN
      ASM_REWRITE_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND);
      MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_UBOUND)] THEN
    EXISTS_TAC `\n. integral s ((h:num->real^N->real^1) n)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE]]);;

let LIEB = prove
 (`!f:num->real^M->real^N g s t.
     (!n. f n absolutely_integrable_on s) /\ g absolutely_integrable_on s /\
     negligible t /\ (!x. x IN s DIFF t ==> ((\n. f n x) --> g x) sequentially)
     ==> ((\n. integral s (\x. lift(norm(f n x - g x))) -
               (integral s (\x. lift(norm(f n x))) -
                integral s (\x. lift(norm(g x)))))
          --> vec 0) sequentially`,
  (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
   [GSYM INTEGRAL_SUB; ABSOLUTELY_INTEGRABLE_SUB; ETA_AX;
    ABSOLUTELY_INTEGRABLE_NORM; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n x. lift(norm((f:num->real^M->real^N) n x - g x) -
                (norm(f n x) - norm(g x)))`;
    `(\x. vec 0):real^M->real^1`;
    `\x. &2 % lift(norm((g:real^M->real^N) x))`;
    `s:real^M->bool`; `t:real^M->bool`]
   DOMINATED_CONVERGENCE_AE) THEN
  REWRITE_TAC[LIFT_SUB; DROP_CMUL; INTEGRAL_0; INTEGRABLE_0] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
   [GSYM INTEGRAL_SUB; ABSOLUTELY_INTEGRABLE_SUB; ETA_AX; INTEGRABLE_CMUL;
    ABSOLUTELY_INTEGRABLE_NORM; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; LIFT_DROP] THEN CONV_TAC NORM_ARITH;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_NULL_SUB THEN
    ASM_SIMP_TAC[GSYM LIM_NULL_NORM; GSYM LIM_NULL; LIM_NORM]]);;

(* ------------------------------------------------------------------------- *)
(* Fundamental theorem of calculus, starting with strong forms.              *)
(* ------------------------------------------------------------------------- *)

let FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG = prove
 (`!f:real^1->real^N f' s a b.
        COUNTABLE s /\
        drop a <= drop b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s
             ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  EXISTS_TAC `(\x. if x IN s then vec 0 else f' x):real^1->real^N` THEN
  EXISTS_TAC `s:real^1->bool` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_COUNTABLE; IN_DIFF] THEN
  SUBGOAL_THEN
   `?f t. s = IMAGE (f:num->real^1) t /\
          (!m n. m IN t /\ n IN t /\ f m = f n ==> m = n)`
  MP_TAC THENL
   [ASM_CASES_TAC `FINITE(s:real^1->bool)` THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPEC `s:real^1->bool` COUNTABLE_AS_INJECTIVE_IMAGE) THEN
      ASM_REWRITE_TAC[INFINITE] THEN MESON_TAC[IN_UNIV]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; INJECTIVE_ON_LEFT_INVERSE] THEN
    MAP_EVERY X_GEN_TAC [`r:num->real^1`; `t:num->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:real^1->num`)] THEN
  REWRITE_TAC[HAS_INTEGRAL_FACTOR_CONTENT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!x. ?d. &0 < d /\
            (x IN interval[a,b]
             ==> (x IN IMAGE (r:num->real^1) t
                  ==> !y. norm(y - x) < d /\ y IN interval[a,b]
                          ==> norm(f y - f x)
                              <= e / &2 pow (4 + n x) * norm(b - a)) /\
                 (~(x IN IMAGE r t)
                  ==> !y. norm(y - x) < d /\ y IN interval[a,b]
                          ==> norm(f y - f x - drop(y - x) % f' x:real^N)
                                <= e / &2 * norm(y - x)))`
  MP_TAC THENL
   [X_GEN_TAC `x:real^1` THEN
    ASM_CASES_TAC `(x:real^1) IN interval[a,b]` THENL
     [ALL_TAC; EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01]] THEN
    ASM_CASES_TAC `x IN IMAGE (r:num->real^1) t` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
       `a <= b ==> a = b \/ a < b`)) THEN
      REWRITE_TAC[DROP_EQ] THEN STRIP_TAC THENL
       [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
        UNDISCH_TAC `(x:real^1) IN interval[a,b]` THEN
        ASM_SIMP_TAC[INTERVAL_SING; IN_SING; VECTOR_SUB_REFL; NORM_0] THEN
        REAL_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_on]) THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[dist] THEN
        DISCH_THEN(MP_TAC o SPEC
         `e / &2 pow (4 + n(x:real^1)) * norm(b - a:real^1)`) THEN
        ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; NORM_POS_LT; VECTOR_SUB_EQ;
                     REAL_LT_POW2; GSYM DROP_EQ; REAL_LT_IMP_NE] THEN
        MESON_TAC[REAL_LT_IMP_LE]];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
      ASM_REWRITE_TAC[IN_DIFF; has_vector_derivative;
                      HAS_DERIVATIVE_WITHIN_ALT] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &2` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[REAL_HALF] THEN MESON_TAC[]];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM; IMP_IMP;
                TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
    X_GEN_TAC `d:real^1->real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "E") (LABEL_TAC "U"))] THEN
  EXISTS_TAC `\x. ball(x:real^1,d(x))` THEN
  ASM_SIMP_TAC[GAUGE_BALL_DEPENDENT] THEN
  X_GEN_TAC `p:(real^1#(real^1->bool))->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `p:(real^1#(real^1->bool))->bool`;
                 `a:real^1`; `b:real^1`]
                ADDITIVE_TAGGED_DIVISION_1) THEN
  ASM_SIMP_TAC[CONTENT_1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM VSUM_SUB; LAMBDA_PAIR_THM] THEN
  SUBGOAL_THEN
   `p:(real^1#(real^1->bool))->bool =
    {(x,k) | (x,k) IN p /\ x IN IMAGE r (t:num->bool)} UNION
    {(x,k) | (x,k) IN p /\ ~(x IN IMAGE r (t:num->bool))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_UNION] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) VSUM_UNION o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. x IN s ==> ~(x IN t)`] THEN
    SIMP_TAC[FORALL_IN_GSPEC; IN_ELIM_PAIR_THM] THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `p:(real^1#(real^1->bool))->bool` THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_PAIR_THM];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `(!P. FINITE {(x:real^1,k:real^1->bool) | (x,k) IN p /\ P x k}) /\
    (!P x. FINITE {(x:real^1,k:real^1->bool) |k| (x,k) IN p /\ P x k})`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `p:real^1#(real^1->bool)->bool` THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_GSPEC];
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x:real^N) <= e / &2 * a /\ norm(y) <= e / &2 * a
    ==> norm(x + y) <= e * a`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `norm(vsum {(x,k) | (x,k) IN p /\ x IN IMAGE (r:num->real^1) t /\
                         ~(content k = &0)}
                (\(x,k). --(f(interval_upperbound k) -
                            (f:real^1->real^N)(interval_lowerbound k))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      MATCH_MP_TAC VSUM_EQ_SUPERSET THEN
      ASM_REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      SIMP_TAC[VECTOR_ARITH `a % vec 0 - x:real^N = --x`] THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^1. k = interval[u,v] /\ x IN interval[u,v]`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      ASM_REWRITE_TAC[CONTENT_EQ_0_1] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
      DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN
      SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1;
               INTERVAL_EQ_EMPTY; REAL_NOT_LE; REAL_NOT_LT] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(VECTOR_ARITH
       `x:real^N = y ==> --(x - y) = vec 0`) THEN
      AP_TERM_TAC THEN ASM_REWRITE_TAC[GSYM DROP_EQ; GSYM REAL_LE_ANTISYM];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `sum {(x,k:real^1->bool) | (x,k) IN p /\ x IN IMAGE (r:num->real^1) t /\
                                ~(content k = &0)}
          ((\(x,k). e / &2 pow (3 + n x) * norm (b - a:real^1)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN
      ASM_REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^1. k = interval[u,v] /\ x IN interval[u,v]`
      MP_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN
        (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
      SIMP_TAC[CONTENT_EQ_0_1; REAL_NOT_LE; REAL_LT_IMP_LE; IN_INTERVAL_1;
               INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
      REPEAT STRIP_TAC THEN
      REMOVE_THEN "E" (MP_TAC o SPEC `x:real^1`) THEN ANTS_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF; SUBSET]; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        MP_TAC(ISPEC `u:real^1` th) THEN MP_TAC(ISPEC `v:real^1` th)) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^1`; `interval[u:real^1,v]`]) THEN
      ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN(fun th ->
        MP_TAC(ISPEC `u:real^1` th) THEN MP_TAC(ISPEC `v:real^1` th)) THEN
      ASM_REWRITE_TAC[dist; ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_SUB] THEN DISCH_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `interval[u:real^1,v] SUBSET interval[a,b]` ASSUME_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      REPEAT(ANTS_TAC THENL
       [ASM_MESON_TAC[ENDS_IN_INTERVAL; SUBSET; INTERVAL_NE_EMPTY_1;
                      REAL_LT_IMP_LE];
        ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`]]) THEN
      REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL] THEN NORM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`FST:real^1#(real^1->bool)->real^1`;
      `\(x:real^1,k:real^1->bool). e / &2 pow (3 + n x) * norm (b - a:real^1)`;
      `{(x,k:real^1->bool) | (x,k) IN p /\ x IN IMAGE (r:num->real^1) t /\
                                ~(content k = &0)}`;
      `IMAGE (r:num->real^1) t`
     ] SUM_GROUP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `sum (IMAGE (r:num->real^1) t)
          (\x. sum {(x,k:real^1->bool) |k|
                    (x,k) IN p /\ ~(content k = &0)}
                   (\yk. e / &2 pow (3 + n x) * norm(b - a:real^1)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_EQ_SUPERSET THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IMP_CONJ] THEN
      REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST] THEN
    REWRITE_TAC[SUM_RMUL; NORM_1; DROP_SUB; REAL_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[real_abs; REAL_SUB_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_SUB_LE; REAL_POW_ADD; real_div; REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `p * e * inv(&2 pow 3) * n = e / &8 * (p * n)`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; SUM_LMUL; REAL_ARITH
     `e / &8 * x <= e * inv(&2) <=> e * x <= e * &4`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `sum (IMAGE (r:num->real^1) t INTER
           IMAGE (FST:real^1#(real^1->bool)->real^1) p)
          (\x. &(CARD {(x,k:real^1->bool) | k |
                      (x,k) IN p /\ ~(content k = &0)}) *
               inv(&2 pow n x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_SUPERSET THEN
      REWRITE_TAC[INTER_SUBSET; IMP_CONJ; FORALL_IN_IMAGE] THEN
      SIMP_TAC[IN_INTER; FUN_IN_IMAGE] THEN
      REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN
      DISJ1_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD s = 0`) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `sum (IMAGE (r:num->real^1) t INTER
           IMAGE (FST:real^1#(real^1->bool)->real^1) p)
          (\x. &2 / &2 pow (n x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INTER] THEN
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS; REAL_OF_NUM_LE] THEN
      GEN_REWRITE_TAC RAND_CONV [ARITH_RULE `2 = 2 EXP 1`] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM DIMINDEX_1] THEN
      MATCH_MP_TAC TAGGED_PARTIAL_DIVISION_COMMON_TAGS THEN
      ASM_MESON_TAC[tagged_division_of];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; SUM_LMUL; REAL_ARITH `&2 * x <= &4 <=> x <= &2`;
                REAL_INV_POW] THEN
    SUBGOAL_THEN
     `(\x:real^1. inv (&2) pow n x) = (\n. inv(&2) pow n) o n`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (rand o rand) SUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN
     `?m. IMAGE (n:real^1->num)
                (IMAGE (r:num->real^1) t INTER
                IMAGE (FST:real^1#(real^1->bool)->real^1) p) SUBSET 0..m`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_NUMSEG; LE_0] THEN
      MATCH_MP_TAC UPPER_BOUND_FINITE_SET THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INTER];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..m) (\n. inv(&2) pow n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INTER; FINITE_NUMSEG] THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN ASM SET_TAC[];
      REWRITE_TAC[SUM_GP; LT; SUB_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_ARITH `(&1 - x) / (&1 / &2) <= &2 <=> &0 <= x`] THEN
      MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    MP_TAC(ISPECL [`\x:real^1. x`; `p:(real^1#(real^1->bool))->bool`;
                   `a:real^1`; `b:real^1`]
                  ADDITIVE_TAGGED_DIVISION_1) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
    ASM_SIMP_TAC[DROP_VSUM; DROP_SUB] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum {(x:real^1,k:real^1->bool) |
           (x,k) IN p /\ ~(x IN IMAGE r (t:num->bool))}
          (\x. e / &2 * (drop o
            (\(x,k). interval_upperbound k - interval_lowerbound k)) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
      SIMP_TAC[o_DEF] THEN
      REWRITE_TAC[NORM_ARITH `norm(a - (b - c):real^N) = norm(b - c - a)`] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?u v:real^1. k = interval[u,v] /\ x IN interval[u,v]`
      MP_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN
       (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
      REWRITE_TAC[IN_INTERVAL_1] THEN DISCH_THEN(fun th ->
        ASSUME_TAC th THEN MP_TAC(MATCH_MP REAL_LE_TRANS th)) THEN
      SIMP_TAC[CONTENT_1; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
      DISCH_TAC THEN REMOVE_THEN "U" (MP_TAC o SPEC `x:real^1`) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `interval[u:real^1,v] SUBSET interval[a,b]` ASSUME_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; IN_INTERVAL_1]; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        MP_TAC(ISPEC `u:real^1` th) THEN MP_TAC(ISPEC `v:real^1` th)) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^1`; `interval[u:real^1,v]`]) THEN
      ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN(fun th ->
        MP_TAC(ISPEC `u:real^1` th) THEN MP_TAC(ISPEC `v:real^1` th)) THEN
      ASM_REWRITE_TAC[dist; ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_SUB] THEN DISCH_TAC THEN DISCH_TAC THEN
      REPEAT(ANTS_TAC THENL
       [ASM_MESON_TAC[ENDS_IN_INTERVAL; SUBSET; INTERVAL_NE_EMPTY_1;
                      REAL_LT_IMP_LE];
        ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`]]) THEN
      REWRITE_TAC[NORM_1; DROP_SUB] THEN
      ASM_SIMP_TAC[REAL_ARITH `a <= b ==> abs(a - b) = b - a`;
                   REAL_ARITH `b <= a ==> abs(a - b) = a - b`] THEN
      REWRITE_TAC[REAL_SUB_LDISTRIB] THEN MATCH_MP_TAC(NORM_ARITH
       `x - y:real^N = z ==> norm(x) <= c - b
                   ==> norm(y) <= b - a ==> norm(z) <= c - a`) THEN
      VECTOR_ARITH_TAC;
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[FORALL_PAIR_THM]] THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?u v:real^1. k = interval[u,v] /\ x IN interval[u,v]`
      MP_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN
       (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
      REWRITE_TAC[IN_INTERVAL_1; o_THM] THEN
      DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN
      SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[DROP_SUB] THEN ASM_REAL_ARITH_TAC]]);;

let FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG = prove
 (`!f:real^1->real^N f' s a b.
        COUNTABLE s /\
        drop a <= drop b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) DIFF s
             ==> (f has_vector_derivative f'(x)) (at x))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG THEN
  EXISTS_TAC `(a:real^1) INSERT (b:real^1) INSERT s` THEN
  ASM_REWRITE_TAC[COUNTABLE_INSERT; IN_INTERVAL_1; IN_DIFF] THEN
  REWRITE_TAC[DE_MORGAN_THM; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; IN_DIFF; IN_INSERT] THEN
  ASM_REWRITE_TAC[REAL_LT_LE; DROP_EQ]);;

let FUNDAMENTAL_THEOREM_OF_CALCULUS = prove
 (`!f:real^1->real^N f' a b.
        drop a <= drop b /\
        (!x. x IN interval[a,b]
             ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG THEN
  EXISTS_TAC `{}:real^1->bool` THEN
  ASM_REWRITE_TAC[COUNTABLE_EMPTY; DIFF_EMPTY] THEN
  MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[differentiable_on] THEN
  ASM_MESON_TAC[has_vector_derivative; differentiable]);;

let FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR = prove
 (`!f:real^1->real^N f' a b.
        drop a <= drop b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b)
             ==> (f has_vector_derivative f'(x)) (at x))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG THEN
  EXISTS_TAC `{}:real^1->bool` THEN
  ASM_REWRITE_TAC[COUNTABLE_EMPTY; DIFF_EMPTY]);;

let ANTIDERIVATIVE_INTEGRAL_CONTINUOUS = prove
 (`!f:real^1->real^N a b.
     (f continuous_on interval[a,b])
     ==> ?g. !u v. u IN interval[a,b] /\ v IN interval[a,b] /\ drop u <= drop v
                   ==> (f has_integral (g(v) - g(u))) (interval[u,v])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ANTIDERIVATIVE_CONTINUOUS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^1->real^N` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^1` THEN
  STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `interval[a:real^1,b]` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[SUBSET_INTERVAL_1; IN_INTERVAL_1] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* This doesn't directly involve integration, but that gives an easy proof.  *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_INTERVAL = prove
 (`!f:real^1->real^N a b k y.
        COUNTABLE k /\ f continuous_on interval[a,b] /\ f a = y /\
        (!x. x IN (interval[a,b] DIFF k)
             ==> (f has_derivative (\h. vec 0)) (at x within interval[a,b]))
        ==> !x. x IN interval[a,b] ==> f x = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC(ISPEC `(\x. vec 0):real^1->real^N` HAS_INTEGRAL_UNIQUE) THEN
  EXISTS_TAC `interval[a:real^1,x]` THEN
  REWRITE_TAC[HAS_INTEGRAL_0] THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG THEN
  EXISTS_TAC `k:real^1->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[a:real^1,b]` THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^1`) THEN ANTS_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN
      SIMP_TAC[IN_DIFF; IN_INTERVAL_1] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      HAS_DERIVATIVE_WITHIN_SUBSET)) THEN
    DISCH_THEN(MP_TAC o SPEC `interval(a:real^1,b)`) THEN
    REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN
    REWRITE_TAC[has_vector_derivative; VECTOR_MUL_RZERO] THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_OPEN THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SIMP_TAC[OPEN_INTERVAL; IN_INTERVAL_1; IN_DIFF] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Generalize a bit to any convex set.                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_CONVEX = prove
 (`!f:real^M->real^N s k c y.
      convex s /\ COUNTABLE k /\ f continuous_on s /\ c IN s /\ f c = y /\
      (!x. x IN (s DIFF k) ==> (f has_derivative (\h. vec 0)) (at x within s))
      ==> !x. x IN s ==> f x = y`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `z:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:real^M = y` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(f:real^M->real^N) o (\t. (&1 - drop t) % x + drop t % y)`;
                 `vec 0:real^1`; `vec 1:real^1`;
                 `{t | ((&1 - drop t) % (x:real^M) + drop t % y) IN k}`;
                 `(f:real^M->real^N) x`]
                HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_INTERVAL) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `vec 1:real^1`) THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; REAL_SUB_0; DROP_EQ;
    VECTOR_ARITH `(&1 - t) % x + t % y = (&1 - u) % x + u % y <=>
                  (t - u) % (x - y) = vec 0`];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
      REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID; LIFT_SUB] THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; GSYM FORALL_DROP] THEN
      REWRITE_TAC[DROP_VEC] THEN ASM_MESON_TAC[CONVEX_ALT]];
    AP_TERM_TAC THEN REWRITE_TAC[DROP_VEC] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\h. vec 0) = ((\h. vec 0):real^M->real^N) o
                               (\t. drop t % (y - x))`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `t % (y - x) = ((&0 - t) % x) + t % y`] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
    REWRITE_TAC[GSYM DROP_NEG; GSYM DROP_VEC; GSYM DROP_SUB] THEN
    SIMP_TAC[HAS_DERIVATIVE_VMUL_DROP; HAS_DERIVATIVE_ID] THEN
    REWRITE_TAC[DROP_SUB; VECTOR_SUB_RDISTRIB] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; DROP_VEC; HAS_DERIVATIVE_CONST] THEN
    SIMP_TAC[HAS_DERIVATIVE_VMUL_DROP; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `s:real^M->bool` THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM FORALL_DROP; DROP_VEC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[CONVEX_ALT]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_DIFF]) THEN
  SIMP_TAC[IN_ELIM_THM; IN_DIFF] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM FORALL_DROP; DROP_VEC] THEN
  ASM_MESON_TAC[CONVEX_ALT]);;

(* ------------------------------------------------------------------------- *)
(* Also to any open connected set with finite set of exceptions. Could       *)
(* generalize to locally convex set with limpt-free set of exceptions.       *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_CONNECTED = prove
 (`!f:real^M->real^N s k c y.
      connected s /\ open s /\ COUNTABLE k /\ f continuous_on s /\
      c IN s /\ f c = y /\
      (!x. x IN (s DIFF k) ==> (f has_derivative (\h. vec 0)) (at x within s))
      ==> !x. x IN s ==> f x = y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOPEN]) THEN
  DISCH_THEN(MP_TAC o SPEC
   `{x | x IN s /\ (f:real^M->real^N) x IN {y}}`) THEN
  ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN CONJ_TAC THEN
  ASM_SIMP_TAC[CONTINUOUS_CLOSED_IN_PREIMAGE; CLOSED_SING] THEN
  MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  UNDISCH_TAC `open(s:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `u:real^M` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_CONVEX THEN
  MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `u:real^M`] THEN
  ASM_REWRITE_TAC[CONVEX_BALL; IN_DIFF; CENTRE_IN_BALL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[IN_DIFF]);;

(* ------------------------------------------------------------------------- *)
(* Integration by parts.                                                     *)
(* ------------------------------------------------------------------------- *)

let INTEGRATION_BY_PARTS = prove
 (`!(bop:real^M->real^N->real^P) f g f' g' a b c y.
        bilinear bop /\ drop a <= drop b /\ COUNTABLE c /\
        (\x. bop (f x) (g x)) continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) DIFF c
             ==> (f has_vector_derivative f'(x)) (at x) /\
                 (g has_vector_derivative g'(x)) (at x)) /\
        ((\x. bop (f x) (g' x)) has_integral
         ((bop (f b) (g b) - bop (f a) (g a)) - y))
            (interval[a,b])
        ==> ((\x. bop (f' x) (g x)) has_integral y) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^1. (bop:real^M->real^N->real^P) (f x) (g x)`;
                 `\x:real^1. (bop:real^M->real^N->real^P) (f x) (g' x) +
                             (bop:real^M->real^N->real^P) (f' x) (g x)`;
                 `c:real^1->bool`; `a:real^1`; `b:real^1`]
    FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG) THEN
  ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_BILINEAR_AT] THEN
  FIRST_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
        DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB)) THEN
  REWRITE_TAC[VECTOR_ARITH `b - a - (b - a - y):real^N = y`; VECTOR_ADD_SUB]);;

let INTEGRATION_BY_PARTS_SIMPLE = prove
 (`!(bop:real^M->real^N->real^P) f g f' g' a b y.
        bilinear bop /\ drop a <= drop b /\
        (!x. x IN interval[a,b]
             ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]) /\
                 (g has_vector_derivative g'(x)) (at x within interval[a,b])) /\
        ((\x. bop (f x) (g' x)) has_integral
         ((bop (f b) (g b) - bop (f a) (g a)) - y))
            (interval[a,b])
        ==> ((\x. bop (f' x) (g x)) has_integral y) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^1. (bop:real^M->real^N->real^P) (f x) (g x)`;
                 `\x:real^1. (bop:real^M->real^N->real^P) (f x) (g' x) +
                             (bop:real^M->real^N->real^P) (f' x) (g x)`;
                 `a:real^1`; `b:real^1`]
    FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN] THEN
  FIRST_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
        DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB)) THEN
  REWRITE_TAC[VECTOR_ARITH `b - a - (b - a - y):real^N = y`; VECTOR_ADD_SUB]);;

let INTEGRABLE_BY_PARTS = prove
 (`!(bop:real^M->real^N->real^P) f g f' g' a b c.
        bilinear bop /\ COUNTABLE c /\
        (\x. bop (f x) (g x)) continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) DIFF c
             ==> (f has_vector_derivative f'(x)) (at x) /\
                 (g has_vector_derivative g'(x)) (at x)) /\
        (\x. bop (f x) (g' x)) integrable_on interval[a,b]
        ==> (\x. bop (f' x) (g x)) integrable_on interval[a,b]`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `drop b <= drop a \/ drop a <= drop b`) THENL
   [DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC INTEGRABLE_ON_NULL THEN
    ASM_REWRITE_TAC[CONTENT_EQ_0_1];
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[integrable_on] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^P` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(bop ((f:real^1->real^M) b) ((g:real^1->real^N) b) -
                 bop (f a) (g a)) - (y:real^P)` THEN
    MATCH_MP_TAC INTEGRATION_BY_PARTS THEN MAP_EVERY EXISTS_TAC
     [`f:real^1->real^M`; `g':real^1->real^N`; `c:real^1->bool`] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `b - a - ((b - a) - y):real^N = y`]]);;

let INTEGRABLE_BY_PARTS_EQ = prove
 (`!(bop:real^M->real^N->real^P) f g f' g' a b c.
        bilinear bop /\ COUNTABLE c /\
        (\x. bop (f x) (g x)) continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) DIFF c
             ==> (f has_vector_derivative f'(x)) (at x) /\
                 (g has_vector_derivative g'(x)) (at x))
        ==> ((\x. bop (f x) (g' x)) integrable_on interval[a,b] <=>
             (\x. bop (f' x) (g x)) integrable_on interval[a,b])`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_BY_PARTS]; DISCH_TAC] THEN
  MP_TAC(ISPEC `\x y. (bop:real^M->real^N->real^P) y x`
        INTEGRABLE_BY_PARTS) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  UNDISCH_TAC `bilinear(bop:real^M->real^N->real^P)` THEN
  REWRITE_TAC[bilinear] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Equiintegrability. The definition here only really makes sense for an     *)
(* elementary set. We just use compact intervals in applications below.      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("equiintegrable_on",(12,"right"));;

let equiintegrable_on = new_definition
  `fs equiintegrable_on i <=>
        (!f:real^M->real^N. f IN fs ==> f integrable_on i) /\
        (!e. &0 < e
             ==> ?d. gauge d /\
                    !f p. f IN fs /\ p tagged_division_of i /\ d fine p
                        ==> norm(vsum p (\(x,k). content(k) % f(x)) -
                                 integral i f) < e)`;;

let EQUIINTEGRABLE_ON_SING = prove
 (`!f:real^M->real^N a b.
        {f} equiintegrable_on interval[a,b] <=>
        f integrable_on interval[a,b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[equiintegrable_on] THEN
  REWRITE_TAC[IN_SING; FORALL_UNWIND_THM2] THEN
  ASM_CASES_TAC `(f:real^M->real^N) integrable_on interval[a,b]` THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  REWRITE_TAC[has_integral; IMP_IMP]);;

(* ------------------------------------------------------------------------- *)
(* Basic combining theorems for the interval of integration.                 *)
(* ------------------------------------------------------------------------- *)

let EQUIINTEGRABLE_ON_NULL = prove
 (`!fs:(real^M->real^N)->bool a b.
     content(interval[a,b]) = &0 ==> fs equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[equiintegrable_on] THEN
  ASM_SIMP_TAC[INTEGRABLE_ON_NULL] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `\x:real^M. ball(x,&1)` THEN REWRITE_TAC[GAUGE_TRIVIAL] THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP (REWRITE_RULE[IMP_CONJ]
                                           VSUM_CONTENT_NULL) th]) THEN
  ASM_SIMP_TAC[INTEGRAL_NULL; VECTOR_SUB_REFL; NORM_0]);;

let EQUIINTEGRABLE_ON_SPLIT = prove
 (`!fs:(real^M->real^N)->bool k a b c.
      fs equiintegrable_on (interval[a,b] INTER {x | x$k <= c}) /\
      fs equiintegrable_on (interval[a,b] INTER {x | x$k >= c}) /\
      1 <= k /\ k <= dimindex(:M)
      ==> fs equiintegrable_on (interval[a,b])`,
  let lemma1 = prove
   (`(!x k. (x,k) IN {x,f k | P x k} ==> Q x k) <=>
     (!x k. P x k ==> Q x (f k))`,
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    SET_TAC[]) in
  let lemma2 = prove
   (`!f:B->B s:(A#B)->bool.
      FINITE s ==> FINITE {x,f k | (x,k) IN s /\ P x k}`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\(x:A,k:B). x,(f k:B)) s` THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; lemma1; IN_IMAGE] THEN
    REWRITE_TAC[EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]) in
  let lemma3 = prove
   (`!f:real^M->real^N g:(real^M->bool)->(real^M->bool) p.
     FINITE p
     ==> vsum {x,g k |x,k| (x,k) IN p /\ ~(g k = {})}
              (\(x,k). content k % f x) =
         vsum (IMAGE (\(x,k). x,g k) p) (\(x,k). content k % f x)`,
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    ASM_SIMP_TAC[FINITE_IMAGE; lemma2] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FORALL_PAIR_THM; SUBSET; IN_IMAGE; EXISTS_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ; VECTOR_MUL_EQ_0] THEN
    MESON_TAC[CONTENT_EMPTY]) in
  let lemma4 = prove
   (`(\(x,l). content (g l) % f x) =
     (\(x,l). content l % f x) o (\(x,l). x,g l)`,
    REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM]) in
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `1 <= k /\ k <= dimindex(:M)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[equiintegrable_on] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b ==> c) /\ (a /\ b /\ c ==> a' /\ b' ==> c')
    ==> (a /\ a') /\ (b /\ b') ==> c /\ c'`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[integrable_on] THEN ASM MESON_TAC[HAS_INTEGRAL_SPLIT];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!f:real^M->real^N.
        f IN fs
        ==> integral (interval[a,b]) f =
                integral (interval [a,b] INTER {x | x$k <= c}) f +
                integral (interval [a,b] INTER {x | x$k >= c}) f`
   (fun th -> SIMP_TAC[th])
  THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC HAS_INTEGRAL_SPLIT THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `c:real`] THEN
    ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 (MP_TAC o SPEC `e / &2`) STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "I2"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "I1"))) THEN
  EXISTS_TAC `\x. if x$k = c then (d1(x:real^M) INTER d2(x)):real^M->bool
                  else ball(x,abs(x$k - c)) INTER d1(x) INTER d2(x)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[gauge] THEN GEN_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gauge]) THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[OPEN_INTER; IN_INTER; OPEN_BALL; IN_BALL] THEN
    ASM_REWRITE_TAC[DIST_REFL; GSYM REAL_ABS_NZ; REAL_SUB_0];
    ALL_TAC] THEN
  X_GEN_TAC `f:real^M->real^N` THEN
  X_GEN_TAC `p:(real^M#(real^M->bool))->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(!x:real^M kk. (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k <= c} = {})
                    ==> x$k <= c) /\
     (!x:real^M kk. (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k >= c} = {})
                    ==> x$k >= c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `kk:real^M->bool` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL; real_ge] THEN DISCH_THEN
     (MP_TAC o MATCH_MP (SET_RULE `k SUBSET (a INTER b) ==> k SUBSET a`)) THEN
    REWRITE_TAC[SUBSET; IN_BALL; dist] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M` MP_TAC) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M`) THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[REAL_NOT_LE; REAL_NOT_LT] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((x - u:real^M)$k)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "I2" (MP_TAC o SPEC
   `{(x:real^M,kk INTER {x:real^M | x$k >= c}) |x,kk|
     (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k >= c} = {})}` o
   SPEC `f:real^M->real^N`) THEN
  REMOVE_THEN "I1" (MP_TAC o SPEC
   `{(x:real^M,kk INTER {x:real^M | x$k <= c}) |x,kk|
     (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k <= c} = {})}` o
   SPEC `f:real^M->real^N`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
   `(a /\ b) /\ (a' /\ b' ==> c) ==> (a ==> a') ==> (b ==> b') ==> c`) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    REWRITE_TAC[TAGGED_DIVISION_OF] THEN
    REPEAT(MATCH_MP_TAC(TAUT
     `(a ==> (a' /\ a'')) /\ (b ==> (b' /\ d) /\ (b'' /\ e))
      ==> a /\ b ==> ((a' /\ b') /\ d) /\ ((a'' /\ b'') /\ e)`) THEN
      CONJ_TAC) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[lemma1] THEN REWRITE_TAC[IMP_IMP] THENL
     [SIMP_TAC[lemma2];
      REWRITE_TAC[AND_FORALL_THM] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `kk:real^M->bool` THEN
      DISCH_THEN(fun th -> CONJ_TAC THEN STRIP_TAC THEN MP_TAC th) THEN
      (ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
        [SIMP_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
      (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
      ASM_MESON_TAC[INTERVAL_SPLIT];
      DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
      (REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
       DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_SIMP_TAC[] THEN
       REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
       DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_SIMP_TAC[] THEN
       ANTS_TAC THENL [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
       MATCH_MP_TAC(SET_RULE
        `s SUBSET s' /\ t SUBSET t'
         ==> s' INTER t' = {} ==> s INTER t = {}`) THEN
       CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]);
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(a ==> b /\ c) /\ d /\ e
                       ==> (a ==> (b /\ d) /\ (c /\ e))`) THEN
    CONJ_TAC THENL
     [DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[INTER_UNIONS] THEN
      ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_UNIONS] THEN
      X_GEN_TAC `x:real^M` THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `kk:real^M->bool` THEN
      REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[NOT_IN_EMPTY];
      ALL_TAC] THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
    REWRITE_TAC[fine; lemma1] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `x < e / &2 /\ y < e / &2 ==> x + y < e`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP NORM_TRIANGLE_LT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a - i) + (b - j) = c - (i + j) <=> a + b = c:real^N`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
 MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum p (\(x,l). content (l INTER {x:real^M | x$k <= c}) %
                     (f:real^M->real^N) x) +
    vsum p (\(x,l). content (l INTER {x:real^M | x$k >= c}) %
                     (f:real^M->real^N) x)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[GSYM VSUM_ADD] THEN MATCH_MP_TAC VSUM_EQ THEN
    REWRITE_TAC[FORALL_PAIR_THM; GSYM VECTOR_ADD_RDISTRIB] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN
    DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `l:real^M->bool`] o
               el 1 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM CONTENT_SPLIT]] THEN
  ASM_SIMP_TAC[lemma3] THEN BINOP_TAC THEN
  (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [lemma4] THEN
   MATCH_MP_TAC VSUM_IMAGE_NONZERO THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
   REWRITE_TAC[PAIR_EQ] THEN
   ASM_MESON_TAC[TAGGED_DIVISION_SPLIT_LEFT_INJ; VECTOR_MUL_LZERO;
                 TAGGED_DIVISION_SPLIT_RIGHT_INJ]));;

let EQUIINTEGRABLE_DIVISION = prove
 (`!fs:(real^M->real^N)->bool d a b.
        d division_of interval[a,b]
        ==> (fs equiintegrable_on interval[a,b] <=>
             !i. i IN d ==> fs equiintegrable_on i)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC OPERATIVE_DIVISION_AND THEN
  ASM_REWRITE_TAC[operative; NEUTRAL_AND] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[equiintegrable_on; INTEGRABLE_ON_NULL] THEN
    GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `\x:real^M. ball(x,&1)` THEN
    ASM_SIMP_TAC[GAUGE_TRIVIAL; INTEGRAL_NULL; VECTOR_SUB_RZERO] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
     `&0 < e ==> x = vec 0 ==> norm x < e`)) THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TAGGED_DIVISION_OF]) THEN
    ASM_MESON_TAC[CONTENT_EQ_0_INTERIOR; SUBSET_INTERIOR;
                  SET_RULE `s = {} <=> s SUBSET {}`];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `c:real`; `k:num`] THEN
  STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[EQUIINTEGRABLE_ON_SPLIT]] THEN
  ASM_SIMP_TAC[INTEGRABLE_SPLIT; equiintegrable_on] THEN
  STRIP_TAC THEN CONJ_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  (FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
   ASM_CASES_TAC `gauge(d:real^M->real^M->bool)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `f:real^M->real^N` THEN
   ASM_CASES_TAC `(f:real^M->real^N) IN fs` THEN ASM_REWRITE_TAC[] THEN
   DISCH_TAC THEN
   MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`;
                  `d:real^M->real^M->bool`; `e / &2`]
         HENSTOCK_LEMMA_PART1) THEN ASM_SIMP_TAC[REAL_HALF] THEN
   MATCH_MP_TAC MONO_FORALL THEN
   X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN
   DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TAGGED_PARTIAL_DIVISION_OF_SUBSET THEN
     RULE_ASSUM_TAC(REWRITE_RULE[tagged_division_of]) THEN
     ASM_MESON_TAC[INTER_SUBSET];
     ALL_TAC] THEN
   MATCH_MP_TAC(NORM_ARITH
    `&0 < e /\ x:real^N = y ==> norm(x) <= e / &2 ==> norm(y) < e`) THEN
   ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
   W(MP_TAC o PART_MATCH (lhand o rand)
     INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN o rand o rand o snd) THEN
   ASM_SIMP_TAC[GSYM INTERVAL_SPLIT; INTEGRABLE_SPLIT] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
   ASM_SIMP_TAC[GSYM VSUM_SUB] THEN MATCH_MP_TAC VSUM_EQ THEN
   REWRITE_TAC[FORALL_PAIR_THM]));;

(* ------------------------------------------------------------------------- *)
(* Main limit theorem for an equiintegrable sequence.                        *)
(* ------------------------------------------------------------------------- *)

let EQUIINTEGRABLE_LIMIT = prove
 (`!f g:real^M->real^N a b.
        {f n | n IN (:num)} equiintegrable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> ((\n. f n x) --> g x) sequentially)
        ==> g integrable_on interval[a,b] /\
            ((\n. integral(interval[a,b]) (f n)) --> integral(interval[a,b]) g)
            sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^M,b]) = &0` THEN
  ASM_SIMP_TAC[INTEGRABLE_ON_NULL; INTEGRAL_NULL; LIM_CONST] THEN
  SUBGOAL_THEN `cauchy (\n. integral(interval[a,b]) (f n :real^M->real^N))`
  MP_TAC THENL
   [REWRITE_TAC[cauchy] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [equiintegrable_on]) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC; IN_UNIV] THEN
    DISCH_TAC THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FINE_DIVISION_EXISTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `b:real^M`]) THEN
    DISCH_THEN(X_CHOOSE_THEN `p:(real^M#(real^M->bool))->bool`
        STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPECL
     [`n:num`; `p:(real^M#(real^M->bool))->bool`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN SUBGOAL_THEN
     `cauchy (\n. vsum p (\(x,k:real^M->bool).
               content k % (f:num->real^M->real^N) n x))`
    MP_TAC THENL
     [MATCH_MP_TAC CONVERGENT_IMP_CAUCHY THEN
      EXISTS_TAC `vsum p (\(x,k:real^M->bool).
          content k % (g:real^M->real^N) x)` THEN
      MATCH_MP_TAC
       (REWRITE_RULE[LAMBDA_PAIR_THM]
        (REWRITE_RULE[FORALL_PAIR_THM]
         (ISPECL [`sequentially`; `\(x:real^M,k:real^M->bool) (n:num).
                  content k % (f n x:real^N)`] LIM_VSUM))) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
      MATCH_MP_TAC LIM_CMUL THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
      ASM_SIMP_TAC[SUBSET] THEN ASM_MESON_TAC[];
      REWRITE_TAC[cauchy] THEN DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; GE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `m:num` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
      ASM_CASES_TAC `N:num <= m /\ N <= n` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(sm - gm:real^N) < e / &3 /\ norm(sn - gn) < e / &3
        ==> dist(sm,sn) < e / &3 ==> dist(gm,gn) < e`) THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY] THEN
    DISCH_THEN(X_CHOOSE_TAC `l:real^N`) THEN
    SUBGOAL_THEN `((g:real^M->real^N) has_integral l) (interval[a,b])`
     (fun th -> ASM_MESON_TAC[th; integrable_on; INTEGRAL_UNIQUE]) THEN
    REWRITE_TAC[has_integral] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [equiintegrable_on]) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC; IN_UNIV] THEN
    DISCH_TAC THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:(real^M#(real^M->bool))->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC `\n:num. vsum p (\(x,k:real^M->bool). content k % f n x) -
                       integral (interval [a,b]) (f n :real^M->real^N)` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[EVENTUALLY_TRUE] THEN
    MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    MATCH_MP_TAC
     (REWRITE_RULE[LAMBDA_PAIR_THM]
      (REWRITE_RULE[FORALL_PAIR_THM]
       (ISPECL [`sequentially`; `\(x:real^M,k:real^M->bool) (n:num).
                content k % (f n x:real^N)`] LIM_VSUM))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
    MATCH_MP_TAC LIM_CMUL THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    ASM_SIMP_TAC[SUBSET] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for the set of equiintegrable functions.               *)
(* ------------------------------------------------------------------------- *)

let EQUIINTEGRABLE_SUBSET = prove
 (`!fs gs s.
   fs equiintegrable_on s /\ gs SUBSET fs ==> gs equiintegrable_on s`,
  REWRITE_TAC[equiintegrable_on; SUBSET] THEN MESON_TAC[]);;

let EQUIINTEGRABLE_UNION = prove
 (`!fs:(real^M->real^N)->bool gs s.
        fs equiintegrable_on s /\ gs equiintegrable_on s
        ==> (fs UNION gs) equiintegrable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[equiintegrable_on; IN_UNION] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `e:real`)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. (d1:real^M->real^M->bool) x INTER d2 x` THEN
  ASM_SIMP_TAC[GAUGE_INTER; FINE_INTER] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let EQUIINTEGRABLE_EQ = prove
 (`!fs gs:(real^M->real^N)->bool s.
        fs equiintegrable_on s /\
        (!g. g IN gs ==> ?f. f IN fs /\ (!x. x IN s ==> f x = g x))
        ==> gs equiintegrable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[equiintegrable_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "*")) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `g:real^M->real^N` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `g:real^M->real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `f:real^M->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:real^M->real^N`) THEN
    ASM_MESON_TAC[INTEGRABLE_SPIKE; IN_DIFF; NEGLIGIBLE_EMPTY];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC
     [`g:real^M->real^N`;`p:(real^M#(real^M->bool))->bool`] THEN
    STRIP_TAC THEN REMOVE_THEN "*" (MP_TAC o SPEC `g:real^M->real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `f:real^M->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`f:real^M->real^N`;`p:(real^M#(real^M->bool))->bool`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
     `x:real^N = y /\ a = b ==> norm(x - a) < e ==> norm(y - b) < e`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[TAGGED_DIVISION_OF; SUBSET]) THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[INTEGRAL_EQ]]]);;

let EQUIINTEGRABLE_CMUL = prove
 (`!fs:(real^M->real^N)->bool s k.
        fs equiintegrable_on s
        ==> {(\x. c % f x) | abs(c) <= k /\ f IN fs} equiintegrable_on s`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[equiintegrable_on; INTEGRABLE_CMUL; FORALL_IN_GSPEC] THEN
  STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[RIGHT_IMP_FORALL_THM; INTEGRAL_CMUL; IMP_IMP] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (abs(k) + &1)`) THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO;
               REAL_ARITH `&0 < abs(k) + &1`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `f:real^M->real^N`;
                       `p:(real^M#(real^M->bool))->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
   SPECL [`f:real^M->real^N`; `p:(real^M#(real^M->bool))->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x <= c * y ==> x <= y * (c + &1)`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC(REAL_ARITH
   `!c. x = c * y /\ c *  y <= k * y ==> x <= k * y`) THEN
  EXISTS_TAC `abs c:real` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM NORM_MUL; GSYM VSUM_LMUL; VECTOR_SUB_LDISTRIB] THEN
    REWRITE_TAC[LAMBDA_PAIR_THM; VECTOR_MUL_ASSOC; REAL_MUL_SYM];
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REAL_ARITH_TAC]);;

let EQUIINTEGRABLE_ADD = prove
 (`!fs:(real^M->real^N)->bool gs s.
        fs equiintegrable_on s /\ gs equiintegrable_on s
        ==> {(\x. f x + g x) | f IN fs /\ g IN gs} equiintegrable_on s`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[equiintegrable_on; INTEGRABLE_ADD; FORALL_IN_GSPEC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "f"))
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g"))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[RIGHT_IMP_FORALL_THM; INTEGRAL_ADD; IMP_IMP] THEN
  REMOVE_THEN "g" (MP_TAC o SPEC `e / &2`) THEN
  REMOVE_THEN "f" (MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "f"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g"))) THEN
  EXISTS_TAC `\x. (d1:real^M->real^M->bool) x INTER d2 x` THEN
  ASM_SIMP_TAC[GAUGE_INTER; FINE_INTER] THEN
  MAP_EVERY X_GEN_TAC [`f:real^M->real^N`; `g:real^M->real^N`;
                       `p:(real^M#(real^M->bool))->bool`] THEN STRIP_TAC THEN
  REMOVE_THEN "g" (MP_TAC o SPECL
   [`g:real^M->real^N`; `p:(real^M#(real^M->bool))->bool`]) THEN
  REMOVE_THEN "f" (MP_TAC o SPECL
   [`f:real^M->real^N`; `p:(real^M#(real^M->bool))->bool`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(NORM_ARITH
   `s + s' = t
    ==> norm(s - i) < e / &2 ==> norm(s' - i') < e / &2
        ==> norm(t - (i + i')) < e`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM VSUM_ADD] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM; VECTOR_ADD_LDISTRIB]);;

let EQUIINTEGRABLE_NEG = prove
 (`!fs:(real^M->real^N)->bool s.
        fs equiintegrable_on s
        ==> {(\x. --(f x)) | f IN fs} equiintegrable_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `&1` o MATCH_MP EQUIINTEGRABLE_CMUL) THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `f:real^M->real^N` THEN DISCH_TAC THEN EXISTS_TAC `-- &1` THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID] THEN REAL_ARITH_TAC);;

let EQUIINTEGRABLE_SUB = prove
 (`!fs:(real^M->real^N)->bool gs s.
        fs equiintegrable_on s /\ gs equiintegrable_on s
        ==> {(\x. f x - g x) | f IN fs /\ g IN gs} equiintegrable_on s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   MP_TAC (MP_TAC o MATCH_MP EQUIINTEGRABLE_NEG)) THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_ADD) THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^M->real^N`; `g:real^M->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `f:real^M->real^N` THEN
  EXISTS_TAC `\x. --((g:real^M->real^N) x)` THEN
  ASM_REWRITE_TAC[VECTOR_SUB] THEN EXISTS_TAC `g:real^M->real^N` THEN
  ASM_REWRITE_TAC[]);;

let EQUIINTEGRABLE_SUM = prove
 (`!fs:(real^M->real^N)->bool a b.
        fs equiintegrable_on interval[a,b]
        ==> {(\x. vsum t (\i. c i % f i x)) |
               FINITE t /\
               (!i:A. i IN t ==> &0 <= c i /\ (f i) IN fs) /\
               sum t c = &1}
            equiintegrable_on interval[a,b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[equiintegrable_on] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; RIGHT_IMP_FORALL_THM] THEN
  STRIP_TAC THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [INTEGRABLE_CMUL; INTEGRABLE_VSUM; ETA_AX; INTEGRAL_VSUM] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC
   [`t:A->bool`; `c:A->real`; `f:A->real^M->real^N`;
    `p:(real^M#(real^M->bool))->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!i:A. i IN t
          ==> integral (interval[a,b]) (\x:real^M. c i % f i x:real^N) =
              vsum p (\(x:real^M,k).
                       integral (k:real^M->bool) (\x:real^M. c i % f i x))`
   (fun th -> SIMP_TAC[th])
  THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL; ETA_AX];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  SUBGOAL_THEN
   `vsum p (\(x,k:real^M->bool). content k % vsum t (\i. c i % f i x)) =
    vsum t (\i. c i %
                vsum p (\(x,k). content k % (f:A->real^M->real^N) i x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VSUM_LMUL] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_SWAP o
      rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sum t (\i:A. c i * e / &2)` THEN CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SUM_RMUL; ETA_AX; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC[GSYM VSUM_SUB] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM VSUM_LMUL; GSYM VSUM_SUB] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM] THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`(f:A->real^M->real^N) i`; `p:(real^M#(real^M->bool))->bool`]) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  DISCH_THEN(MP_TAC o SPEC `abs((c:A->real) i)` o
    MATCH_MP(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_LMUL)) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; GSYM NORM_MUL] THEN
  ASM_SIMP_TAC[GSYM VSUM_LMUL; VECTOR_SUB_LDISTRIB; real_abs] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= a ==> y <= a`) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `integral (interval[a,b]) ((f:A->real^M->real^N) i) =
    vsum p (\(x:real^M,k). integral (k:real^M->bool) (f i))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VSUM_LMUL; GSYM VSUM_SUB] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_CMUL THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAGGED_DIVISION_OF]) THEN
  ASM_MESON_TAC[INTEGRABLE_SUBINTERVAL]);;

let EQUIINTEGRABLE_UNIFORM_LIMIT = prove
 (`!fs:(real^M->real^N)->bool a b.
        fs equiintegrable_on interval[a,b]
        ==> {g | !e. &0 < e
                     ==> ?f. f IN fs /\
                             !x. x IN interval[a,b] ==> norm(g x - f x) < e}
            equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [equiintegrable_on]) THEN
  REWRITE_TAC[equiintegrable_on; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_UNIFORM_LIMIT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC
   [`g:real^M->real^N`;`p:(real^M#(real^M->bool))->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  SUBGOAL_THEN `(g:real^M->real^N) integrable_on interval[a,b]`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_UNIFORM_LIMIT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:num->real^M->real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN interval[a,b]
        ==> ((\n. f n x) --> (g:real^M->real^N) x) sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `k:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `k:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_ARITH `dist(a:real^N,b) = norm(b - a)`] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num->real^M->real^N`; `g:real^M->real^N`;
                 `a:real^M`; `b:real^M`] EQUIINTEGRABLE_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUIINTEGRABLE_SUBSET THEN
    EXISTS_TAC `fs:(real^M->real^N)->bool` THEN ASM SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))] THEN
  SUBGOAL_THEN
   `((\n. vsum p (\(x,k:real^M->bool).
                    content k % (f:num->real^M->real^N) n x)) -->
     vsum p (\(x,k). content k % g x)) sequentially`
   (LABEL_TAC "+")
  THENL
   [MATCH_MP_TAC
       (REWRITE_RULE[LAMBDA_PAIR_THM]
        (REWRITE_RULE[FORALL_PAIR_THM]
         (ISPECL [`sequentially`; `\(x:real^M,k:real^M->bool) (n:num).
                  content k % (f n x:real^N)`] LIM_VSUM))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
    MATCH_MP_TAC LIM_CMUL THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    ASM_SIMP_TAC[SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC o REWRITE_RULE[LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[dist]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "*")) THEN
  REMOVE_THEN "+" (MP_TAC o REWRITE_RULE[LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[dist]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "+")) THEN
  SUBGOAL_THEN `?n:num. N1 <= n /\ N2 <= n` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `N1 + N2:num` THEN ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `n:num`) THEN
  REMOVE_THEN "+" (MP_TAC o SPEC `n:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(f:num->real^M->real^N) n`;`p:(real^M#(real^M->bool))->bool`]) THEN
  ASM_REWRITE_TAC[] THEN NORM_ARITH_TAC);;

let EQUIINTEGRABLE_REFLECT = prove
 (`!fs:(real^M->real^N)->bool a b.
        fs equiintegrable_on interval[a,b]
        ==> {(\x. f(--x)) | f IN fs} equiintegrable_on interval[--b,--a]`,
  let lemma = prove
   (`(!x k. (x,k) IN IMAGE (\(x,k). f x k,g x k) s ==> Q x k) <=>
     (!x k. (x,k) IN s ==> Q (f x k) (g x k))`,
    REWRITE_TAC[IN_IMAGE; PAIR_EQ; EXISTS_PAIR_THM] THEN SET_TAC[]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[equiintegrable_on] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_GSPEC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[INTEGRABLE_REFLECT; INTEGRAL_REFLECT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. IMAGE (--) ((d:real^M->real^M->bool) (--x))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [gauge]) THEN
    SIMP_TAC[gauge; OPEN_NEGATIONS] THEN DISCH_TAC THEN
    GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_NEG_NEG] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `f:real^M->real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:real^M->real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE (\(x,k). (--x:real^M,IMAGE (--) (k:real^M->bool))) p`) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    REWRITE_TAC[TAGGED_DIVISION_OF] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; lemma] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        ONCE_REWRITE_TAC[GSYM IN_INTERVAL_REFLECT] THEN
        ASM_SIMP_TAC[VECTOR_NEG_NEG; GSYM SUBSET] THEN ASM_MESON_TAC[];
        REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
        REWRITE_TAC[VECTOR_ARITH `x:real^N = --y <=> --x = y`] THEN
        ONCE_REWRITE_TAC[GSYM IN_INTERVAL_REFLECT] THEN
        REWRITE_TAC[UNWIND_THM1] THEN
        SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
         (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
        THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
        ASM_MESON_TAC[VECTOR_NEG_NEG]];
      MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`y:real^M`; `l:real^M->bool`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`x:real^M`; `k:real^M->bool`;
        `y:real^M`; `l:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_IMP THEN
      CONJ_TAC THENL [MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
      REWRITE_TAC[INTERIOR_NEGATIONS] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. f(f x) = x)
        ==> s INTER t = {} ==> IMAGE f s INTER IMAGE f t = {}`) THEN
      REWRITE_TAC[VECTOR_NEG_NEG];
      GEN_REWRITE_TAC I [EXTENSION] THEN
      ONCE_REWRITE_TAC[GSYM IN_INTERVAL_REFLECT] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN X_GEN_TAC `y:real^M` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      MATCH_MP_TAC(MESON[]
       `!f. (!x. f(f x) = x) /\ (!x. P x <=> Q(f x))
            ==> ((?x. P x) <=> (?x. Q x))`) THEN
      EXISTS_TAC `IMAGE ((--):real^M->real^M)` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_NEG_NEG; IMAGE_ID];
        ALL_TAC] THEN
      X_GEN_TAC `t:real^M->bool` THEN BINOP_TAC THENL
       [REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ] THEN
        SUBGOAL_THEN `!k:real^M->bool. IMAGE (--) (IMAGE (--) k) = k`
        MP_TAC THENL
         [REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_NEG_NEG; IMAGE_ID];
          MESON_TAC[]];
        MATCH_MP_TAC(SET_RULE
         `(!x. f(f x) = x) ==> (y IN s <=> f y IN IMAGE f s)`) THEN
        REWRITE_TAC[VECTOR_NEG_NEG]]];
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      REWRITE_TAC[fine; lemma] THEN
      REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. f(f x) = x) ==> k SUBSET IMAGE f s ==> IMAGE f k SUBSET s`) THEN
      REWRITE_TAC[VECTOR_NEG_NEG];
      ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH
     `x:real^N = y ==> norm(x - i) < e ==> norm(y - i) < e`) THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhs o snd) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC(MESON[]
       `(!x. f(f x) = x)
        ==> !x y. x IN p /\ y IN p /\ f x = f y ==> x = y`) THEN
      REWRITE_TAC[FORALL_PAIR_THM; GSYM IMAGE_o; o_DEF; VECTOR_NEG_NEG;
                  IMAGE_ID];
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
      REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
       (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `(--):real^M->real^M = (\x. --(&1) % x + vec 0)` SUBST1_TAC
      THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[CONTENT_IMAGE_AFFINITY_INTERVAL; REAL_ABS_NEG] THEN
      REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; REAL_ABS_NUM]]]);;

(* ------------------------------------------------------------------------- *)
(* Some technical lemmas about minimizing a "flat" part of a sum over a      *)
(* division, followed by subinterval resictions for equiintegrable family.   *)
(* ------------------------------------------------------------------------- *)

let SUM_CONTENT_AREA_OVER_THIN_DIVISION = prove
 (`!d a b:real^M s i c.
        d division_of s /\ s SUBSET interval[a,b] /\
        1 <= i /\ i <= dimindex(:M) /\ a$i <= c /\ c <= b$i /\
        (!k. k IN d ==> ~(k INTER {x | x$i = c} = {}))
        ==> (b$i - a$i) *
            sum d (\k. content k /
                       (interval_upperbound k$i - interval_lowerbound k$i))
            <= &2 * content(interval[a,b])`,
  let lemma0 = prove
   (`!k:real^M->bool i.
          1 <= i /\ i <= dimindex(:M)
          ==> content k / (interval_upperbound k$i - interval_lowerbound k$i) =
              if content k = &0 then &0
              else product ((1..dimindex(:M)) DELETE i)
                           (\j. interval_upperbound k$j -
                                interval_lowerbound k$j)`,
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
    REWRITE_TAC[content] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[CONTENT_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN
     `1..dimindex(:M) = i INSERT ((1..dimindex(:M)) DELETE i)`
    MP_TAC THENL
     [REWRITE_TAC[SET_RULE `s = x INSERT (s DELETE x) <=> x IN s`] THEN
      ASM_REWRITE_TAC[IN_NUMSEG];
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [th])] THEN
    ASM_SIMP_TAC[PRODUCT_CLAUSES; IN_NUMSEG; FINITE_DELETE; FINITE_NUMSEG;
                 IN_DELETE] THEN
    MATCH_MP_TAC(REAL_FIELD `~(y = &0) ==> (y * x) * inv y = x`) THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~(content(k:real^M->bool) = &0)` THEN
    ASM_REWRITE_TAC[content; PRODUCT_EQ_0_NUMSEG] THEN ASM_MESON_TAC[])
  and lemma1 = prove
   (`!d a b:real^M s i.
          d division_of s /\ s SUBSET interval[a,b] /\
          1 <= i /\ i <= dimindex(:M) /\
          ((!k. k IN d
                ==> ~(content k = &0) /\ ~(k INTER {x | x$i = a$i} = {})) \/
           (!k. k IN d
                ==> ~(content k = &0) /\ ~(k INTER {x | x$i = b$i} = {})))
          ==> (b$i - a$i) *
              sum d (\k. content k /
                         (interval_upperbound k$i - interval_lowerbound k$i))
              <= content(interval[a,b])`,
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    ABBREV_TAC
     `extend =
      \k:real^M->bool. interval
           [(lambda j. if j = i then (a:real^M)$i
                       else interval_lowerbound k$j):real^M,
            (lambda j. if j = i then (b:real^M)$i
                       else interval_upperbound k$j)]` THEN
    SUBGOAL_THEN `!k. k IN d ==> k SUBSET interval[a:real^M,b]`
    ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[division_of]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!k:real^M->bool. k IN d ==> ~(k = {})` ASSUME_TAC THENL
     [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(!k. k IN d ==> ~((extend:(real^M->bool)->(real^M->bool)) k = {})) /\
      (!k. k IN d ==> extend k SUBSET interval[a,b])`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
      CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN
      (DISCH_TAC THEN EXPAND_TAC "extend" THEN
       SUBGOAL_THEN `interval[u:real^M,v] SUBSET interval[a,b]` MP_TAC THENL
        [ASM_SIMP_TAC[]; ALL_TAC] THEN
       SUBGOAL_THEN `~(interval[u:real^M,v] = {})` MP_TAC THENL
        [ASM_SIMP_TAC[]; ALL_TAC] THEN
       SIMP_TAC[SUBSET_INTERVAL; INTERVAL_NE_EMPTY; LAMBDA_BETA;
                INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND] THEN
       MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL]);
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!k1 k2. k1 IN d /\ k2 IN d /\ ~(k1 = k2)
              ==> interior((extend:(real^M->bool)->(real^M->bool)) k1) INTER
                  interior(extend k2) = {}`
    ASSUME_TAC THENL
     [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
      MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`w:real^M`; `z:real^M`] THEN DISCH_TAC THEN
      DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN DISCH_THEN(MP_TAC o SPECL
       [`interval[u:real^M,v]`; `interval[w:real^M,z]`]) THEN
      ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXPAND_TAC "extend" THEN
      SIMP_TAC[INTERIOR_CLOSED_INTERVAL; IN_INTERVAL; LAMBDA_BETA] THEN
      SUBGOAL_THEN `~(interval[u:real^M,v] = {}) /\
                    ~(interval[w:real^M,z] = {})`
      MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SIMP_TAC[SUBSET_INTERVAL; INTERVAL_NE_EMPTY; LAMBDA_BETA;
               INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND] THEN
      STRIP_TAC THEN DISCH_THEN(X_CHOOSE_THEN `x:real^M` MP_TAC) THEN
      MP_TAC(MESON[]
       `(!P. (!j:num. P j) <=> P i /\ (!j. ~(j = i) ==> P j))`) THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC
       (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
      ASM_SIMP_TAC[IMP_IMP] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN
       (fun th -> MP_TAC(SPEC `interval[u:real^M,v]` th) THEN
                  MP_TAC(SPEC `interval[w:real^M,z]` th))) THEN
      ASM_REWRITE_TAC[CONTENT_EQ_0_INTERIOR; INTERIOR_CLOSED_INTERVAL] THEN
      REWRITE_TAC[IMP_CONJ; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      REWRITE_TAC[IN_INTERVAL; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `q:real^M` THEN STRIP_TAC THEN
      X_GEN_TAC `r:real^M` THEN STRIP_TAC THEN
      X_GEN_TAC `s:real^M` THEN STRIP_TAC THEN
      X_GEN_TAC `t:real^M` THEN STRIP_TAC THENL
       [EXISTS_TAC `(lambda j. if j = i then min ((q:real^M)$i) ((s:real^M)$i)
                               else (x:real^M)$j):real^M`;
        EXISTS_TAC `(lambda j. if j = i then max ((q:real^M)$i) ((s:real^M)$i)
                               else (x:real^M)$j):real^M`] THEN
      (SIMP_TAC[AND_FORALL_THM; LAMBDA_BETA] THEN X_GEN_TAC `j:num` THEN
       ASM_CASES_TAC `j:num = i` THEN ASM_SIMP_TAC[] THEN
       UNDISCH_THEN `j:num = i` SUBST_ALL_TAC THEN
       SUBGOAL_THEN `interval[u:real^M,v] SUBSET interval[a,b] /\
                     interval[w:real^M,z] SUBSET interval[a,b]`
       MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
       SUBGOAL_THEN `~(interval[u:real^M,v] = {}) /\
                     ~(interval[w:real^M,z] = {})`
       MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
       SIMP_TAC[INTERVAL_NE_EMPTY; SUBSET_INTERVAL] THEN
       REPEAT STRIP_TAC THEN
       REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN ASM_REWRITE_TAC[] THEN
       ASM_REAL_ARITH_TAC);
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `sum (IMAGE (extend:(real^M->bool)->(real^M->bool)) d) content` THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE_NONZERO o rand o snd) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MAP_EVERY X_GEN_TAC [`k1:real^M->bool`; `k2:real^M->bool`] THEN
        STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
         [`k1:real^M->bool`; `k2:real^M->bool`]) THEN
        ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
        EXPAND_TAC "extend" THEN REWRITE_TAC[CONTENT_EQ_0_INTERIOR];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
        MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
        MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN DISCH_TAC THEN
        ASM_CASES_TAC `content(interval[u:real^M,v]) = &0` THENL
         [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; o_THM] THEN
          EXPAND_TAC "extend" THEN REWRITE_TAC[CONTENT_POS_LE];
          ALL_TAC] THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTENT_LT_NZ]) THEN
        DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
        REWRITE_TAC[CONTENT_POS_LT_EQ] THEN STRIP_TAC THEN
        ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND;
                     REAL_LT_IMP_LE; real_div; REAL_MUL_ASSOC] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN
        SUBGOAL_THEN
         `~((extend:(real^M->bool)->(real^M->bool)) (interval[u,v]) = {})`
        MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "extend" THEN ASM_SIMP_TAC[content; o_THM] THEN
        ASM_SIMP_TAC[INTERVAL_NE_EMPTY; INTERVAL_LOWERBOUND;
                     INTERVAL_UPPERBOUND; REAL_LT_IMP_LE] THEN
        DISCH_THEN(K ALL_TAC) THEN
        SUBGOAL_THEN
         `1..dimindex(:M) = i INSERT ((1..dimindex(:M)) DELETE i)`
        SUBST1_TAC THENL
         [MATCH_MP_TAC(SET_RULE `x IN s ==> s = x INSERT (s DELETE x)`) THEN
          ASM_REWRITE_TAC[IN_NUMSEG];
          ALL_TAC] THEN
        SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG; FINITE_DELETE] THEN
        ASM_SIMP_TAC[IN_DELETE; IN_NUMSEG; LAMBDA_BETA] THEN
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC(REAL_RING
          `x:real = y ==> ab * uv * x = (ab * y) * uv`) THEN
        MATCH_MP_TAC PRODUCT_EQ THEN
        SIMP_TAC[IN_DELETE; IN_NUMSEG; LAMBDA_BETA]];
      MATCH_MP_TAC SUBADDITIVE_CONTENT_DIVISION THEN EXISTS_TAC
       `UNIONS (IMAGE (extend:(real^M->bool)->(real^M->bool)) d)` THEN
      ASM_SIMP_TAC[UNIONS_SUBSET; division_of; FINITE_IMAGE] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
      REPEAT CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN
      DISCH_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]] THEN
        EXPAND_TAC "extend" THEN REWRITE_TAC[] THEN MESON_TAC[];
        ASM_MESON_TAC[];
        ASM_SIMP_TAC[]]]) in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^M,b]) = &0` THENL
   [MATCH_MP_TAC(REAL_ARITH `x = &0 /\ &0 <= y ==> x <= &2 * y`) THEN
    REWRITE_TAC[CONTENT_POS_LE; REAL_ENTIRE] THEN DISJ2_TAC THEN
    MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `k:real^M->bool` THEN
    DISCH_TAC THEN REWRITE_TAC[real_div; REAL_ENTIRE] THEN DISJ1_TAC THEN
    MATCH_MP_TAC CONTENT_0_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`a:real^M`; `b:real^M`] THEN
    ASM_MESON_TAC[division_of; SUBSET_TRANS];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTENT_LT_NZ]) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[CONTENT_POS_LT_EQ] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  MP_TAC(ISPECL
   [`{k | k IN {l INTER {x | x$i <= c} | l |
                l IN d /\ ~(l INTER {x:real^M | x$i <= c} = {})} /\
          ~(content k = &0)}`;
    `a:real^M`;
    `(lambda j. if j = i then c else (b:real^M)$j):real^M`;
    `UNIONS {k | k IN {l INTER {x | x$i <= c} | l |
                       l IN d /\ ~(l INTER {x:real^M | x$i <= c} = {})} /\
                 ~(content k = &0)}`;
    `i:num`] lemma1) THEN
  MP_TAC(ISPECL
   [`{k | k IN {l INTER {x | x$i >= c} | l |
                l IN d /\ ~(l INTER {x:real^M | x$i >= c} = {})} /\
          ~(content k = &0)}`;
    `(lambda j. if j = i then c else (a:real^M)$j):real^M`;
    `b:real^M`;
    `UNIONS {k | k IN {l INTER {x | x$i >= c} | l |
                       l IN d /\ ~(l INTER {x:real^M | x$i >= c} = {})} /\
                 ~(content k = &0)}`;
    `i:num`] lemma1) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
   `(p1 /\ p2) /\ (q1 /\ q2 ==> r) ==> (p2 ==> q2) ==> (p1 ==> q1) ==> r`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN
    (REPEAT CONJ_TAC THENL
     [REWRITE_TAC[division_of] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
        MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_RESTRICT THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      CONJ_TAC THENL
       [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
        MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN
        REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [REWRITE_TAC[IN_ELIM_THM; SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[];
          ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MESON_TAC[]];
        X_GEN_TAC `k:real^M->bool` THEN REPEAT DISCH_TAC THEN
        X_GEN_TAC `l:real^M->bool` THEN REPEAT DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
        DISCH_THEN(MP_TAC o SPECL [`k:real^M->bool`; `l:real^M->bool`] o
          el 2 o CONJUNCTS) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE
         `s SUBSET s' /\ t SUBSET t'
          ==> s' INTER t' = {} ==> s INTER t = {}`) THEN
        CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IMP_CONJ] THEN
      X_GEN_TAC `k:real^M->bool` THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `k SUBSET interval[a:real^M,b]` MP_TAC THENL
       [ASM_MESON_TAC[division_of; SUBSET_TRANS]; ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE
       `i INTER h SUBSET j ==> k SUBSET i ==> k INTER h SUBSET j`) THEN
      ASM_SIMP_TAC[INTERVAL_SPLIT; SUBSET_INTERVAL; LAMBDA_BETA] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
      REAL_ARITH_TAC;
      ALL_TAC])
    THENL [DISJ2_TAC; DISJ1_TAC] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; real_ge] THEN ASM SET_TAC[REAL_LE_REFL];
    ASM_SIMP_TAC[LAMBDA_BETA]] THEN
  SUBGOAL_THEN
   `sum {k | k IN
             { l INTER {x | x$i <= c} | l |
               l IN d /\ ~(l INTER {x:real^M | x$i <= c} = {})} /\
             ~(content k = &0)}
        (\k. content k /
             (interval_upperbound k$i - interval_lowerbound k$i)) =
    sum d ((\k. content k /
             (interval_upperbound k$i - interval_lowerbound k$i)) o
           (\k. k INTER {x | x$i <= c})) /\
    sum {k | k IN
             { l INTER {x | x$i >= c} | l |
               l IN d /\ ~(l INTER {x:real^M | x$i >= c} = {})} /\
             ~(content k = &0)}
        (\k. content k /
             (interval_upperbound k$i - interval_lowerbound k$i)) =
    sum d ((\k. content k /
             (interval_upperbound k$i - interval_lowerbound k$i)) o
           (\k. k INTER {x | x$i >= c}))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN
    (W(MP_TAC o PART_MATCH (rand o rand) SUM_IMAGE_NONZERO o rand o snd) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
      [MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `l:real^M->bool`] THEN
       STRIP_TAC THEN
       REWRITE_TAC[real_div; REAL_ENTIRE] THEN DISJ1_TAC THEN
       (MATCH_MP_TAC DIVISION_SPLIT_LEFT_INJ ORELSE
        MATCH_MP_TAC DIVISION_SPLIT_RIGHT_INJ) THEN ASM_MESON_TAC[];
       DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
       MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
       GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
        `x IN IMAGE f d /\
         ~(x IN {x | x IN {f y |y| y IN d /\ ~(f y = a)} /\ ~P x})
         ==> (!y. f y = a ==> P(f y)) ==> P x`)) THEN
       SIMP_TAC[CONTENT_EMPTY; real_div; REAL_MUL_LZERO]]);
     ALL_TAC] THEN
  MAP_EVERY (fun (t,tac) ->
    ASM_CASES_TAC t THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_THEN(MP_TAC o tac) THEN
      MATCH_MP_TAC(REAL_ARITH `x = y /\ a <= b ==> x <= a ==> y <= b`) THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
        X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
        PURE_REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
        REWRITE_TAC[real_ge; SET_RULE
         `k INTER {x | P x} = k <=> (!x. x IN k ==> P x)`] THEN
        X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        SUBGOAL_THEN `x IN interval[a:real^M,b]` MP_TAC THENL
         [ASM_MESON_TAC[SUBSET; division_of]; ALL_TAC] THEN
        ASM_SIMP_TAC[IN_INTERVAL];
        MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x <= y ==> x <= &2 * y`) THEN
        REWRITE_TAC[CONTENT_POS_LE] THEN MATCH_MP_TAC CONTENT_SUBSET THEN
        SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN
        MESON_TAC[REAL_LE_REFL]];
      ALL_TAC])
    [`c = (a:real^M)$i`,CONJUNCT2; `c = (b:real^M)$i`,CONJUNCT1] THEN
  SUBGOAL_THEN `(a:real^M)$i < c /\ c < (b:real^M)$i` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_ARITH `(x * &2) / y = &2 * x / y`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `s <= s1 + s2 /\ c1 = c /\ c2 = c
    ==> s1 <= c1 /\ s2 <= c2 ==> s <= &2 * c`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_SIMP_TAC[lemma0] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `~(interval[u:real^M,v] = {}) /\ interval[u,v] SUBSET interval[a,b]`
    MP_TAC THENL [ASM_MESON_TAC[division_of; SUBSET_TRANS]; ALL_TAC] THEN
    SIMP_TAC[INTERVAL_NE_EMPTY; SUBSET_INTERVAL; IMP_CONJ] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ c1 + c2 = c /\
      (~(c1 = &0) ==> x1 = x) /\ (~(c2 = &0) ==> x2 = x)
      ==> (if c = &0 then &0 else x) <=
          (if c1 = &0 then &0 else x1) +
          (if c2 = &0 then &0 else x2)`) THEN
    ASM_SIMP_TAC[GSYM CONTENT_SPLIT] THEN
    ASM_SIMP_TAC[INTERVAL_SPLIT; CONTENT_POS_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN
      ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG; IN_DELETE; IN_NUMSEG;
                   INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; REAL_SUB_LE];
      REWRITE_TAC[CONTENT_EQ_0; REAL_NOT_LE; MESON[]
       `~(?i. P i /\ Q i /\ R i) <=> (!i. P i /\ Q i ==> ~R i)`] THEN
      SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; REAL_LT_IMP_LE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
      ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; IN_DELETE;
                   IN_NUMSEG; LAMBDA_BETA]];
    SUBGOAL_THEN
     `~(interval[a,b] = {}) /\
      ~(interval[a:real^M,(lambda j. if j = i then c else b$j)] = {}) /\
      ~(interval[(lambda j. if j = i then c else a$j):real^M,b] = {})`
    MP_TAC THENL
     [SIMP_TAC[INTERVAL_NE_EMPTY; LAMBDA_BETA] THEN
      ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
      ALL_TAC] THEN
    SIMP_TAC[content] THEN
    SIMP_TAC[INTERVAL_NE_EMPTY; INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `1..dimindex(:M) = i INSERT ((1..dimindex(:M)) DELETE i)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `x IN s ==> s = x INSERT (s DELETE x)`) THEN
      ASM_REWRITE_TAC[IN_NUMSEG];
      ALL_TAC] THEN
    SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG; FINITE_DELETE] THEN
    ASM_SIMP_TAC[IN_DELETE; IN_NUMSEG; LAMBDA_BETA] THEN
    CONJ_TAC THEN MATCH_MP_TAC(REAL_FIELD
     `y < x /\ z < w /\ a = b
      ==> ((x - y) * a) / (x - y) = ((w - z) * b) / (w - z)`) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC PRODUCT_EQ THEN
    SIMP_TAC[IN_DELETE; IN_NUMSEG; LAMBDA_BETA]]);;

let BOUNDED_EQUIINTEGRAL_OVER_THIN_TAGGED_PARTIAL_DIVISION = prove
 (`!fs f:real^M->real^N a b e.
    fs equiintegrable_on interval[a,b] /\ f IN fs /\
    (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x)) /\
    &0 < e
    ==> ?d. gauge d /\
            !c i p h. c IN interval[a,b] /\ 1 <= i /\ i <= dimindex(:M) /\
                      p tagged_partial_division_of interval[a,b] /\
                      d fine p /\
                      h IN fs /\
                      (!x k. (x,k) IN p ==> ~(k INTER {x | x$i = c$i} = {}))
                      ==> sum p(\(x,k). norm(integral k h)) < e`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^M,b]) = &0` THENL
   [EXISTS_TAC `\x:real^M. ball(x,&1)` THEN REWRITE_TAC[GAUGE_TRIVIAL] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `&0 < e ==> x = &0 ==> x < e`)) THEN
    MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    GEN_TAC THEN X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?u v:real^M. k = interval[u,v] /\ interval[u,v] SUBSET interval[a,b]`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
    ASM_REWRITE_TAC[NORM_EQ_0] THEN MATCH_MP_TAC INTEGRAL_NULL THEN
    ASM_MESON_TAC[CONTENT_0_SUBSET];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTENT_LT_NZ]) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[CONTENT_POS_LT_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. gauge d /\
        !p h. p tagged_partial_division_of interval [a,b] /\
              d fine p /\ (h:real^M->real^N) IN fs
              ==> sum p (\(x,k). norm(content k % h x - integral k h)) <
                  e / &2`
   (X_CHOOSE_THEN `g0:real^M->real^M->bool` STRIP_ASSUME_TAC)
  THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [equiintegrable_on]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC
      `e / &5 / (&(dimindex(:N)) + &1)`)) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &5 /\ &0 < &n + &1`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC
     [`p:(real^M#(real^M->bool))->bool`; `h:real^M->real^N`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`h:real^M->real^N`; `a:real^M`; `b:real^M`;
           `g:real^M->real^M->bool`; `e / &5 / (&(dimindex(:N)) + &1)`]
        HENSTOCK_LEMMA_PART2) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &5 /\ &0 < &n + &1`] THEN
    DISCH_THEN(MP_TAC o SPEC `p:(real^M#(real^M->bool))->bool`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `a < b ==> x <= a ==> x < b`) THEN
    REWRITE_TAC[REAL_ARITH `&2 * d * e / &5 / (d + &1) =
                            (e * &2 / &5 * d) / (d + &1)`] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ &0 < e * d ==> e * &2 / &5 * d < e / &2 * (d + &1)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1];
    ALL_TAC] THEN
  ABBREV_TAC
   `g:real^M->real^M->bool =
       \x. g0(x) INTER
           ball(x,(e / &8 / (norm(f x:real^N) + &1)) *
                  inf(IMAGE (\m. b$m - a$m) (1..dimindex(:M))) /
                  content(interval[a:real^M,b]))` THEN
  SUBGOAL_THEN `gauge(g:real^M->real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC GAUGE_INTER THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[gauge; OPEN_BALL; CENTRE_IN_BALL] THEN
    X_GEN_TAC `x:real^M` THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_DIV; NORM_ARITH
     `&0 < &8 /\ &0 < norm(x:real^N) + &1`] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) REAL_LT_INF_FINITE o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FINITE_RESTRICT] THEN
      SIMP_TAC[IMAGE_EQ_EMPTY; NUMSEG_EMPTY;
               GSYM NOT_LE; DIMINDEX_GE_1] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_NUMSEG] THEN
      MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[REAL_SUB_LT; IN_NUMSEG; GSYM REAL_ABS_NZ; REAL_SUB_0;
                   IN_ELIM_THM]];
    ALL_TAC] THEN
  EXISTS_TAC `g:real^M->real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`c:real^M`; `i:num`; `p:(real^M#(real^M->bool))->bool`;
    `h:real^M->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `interval[c:real^M,b] SUBSET interval[a,b]`
  ASSUME_TAC THENL
   [UNDISCH_TAC `c IN interval[a:real^M,b]` THEN
    SIMP_TAC[IN_INTERVAL; SUBSET_INTERVAL; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(p:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
  MP_TAC(ASSUME `(g:real^M->real^M->bool) fine p`) THEN
  EXPAND_TAC "g" THEN REWRITE_TAC[FINE_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F")) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:(real^M#(real^M->bool))->bool`) THEN
  DISCH_THEN(MP_TAC o SPEC `h:real^M->real^N`) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_OF_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x - y <= e / &2 ==> y < e / &2 ==> x < e`) THEN
  ASM_SIMP_TAC[GSYM SUM_SUB] THEN
  ONCE_REWRITE_TAC[LAMBDA_PAIR_THM] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum p (\(x:real^M,k:real^M->bool). norm(content k % h x:real^N))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    REWRITE_TAC[NORM_ARITH `norm y - norm(x - y:real^N) <= norm x`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum p (\(x:real^M,k).
                   e / &4 * (b$i - a$i) / content(interval[a:real^M,b]) *
                   content(k:real^M->bool) /
                   (interval_upperbound k$i - interval_lowerbound k$i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `content(k:real^M->bool) = &0` THENL
     [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO; NORM_0;
                      REAL_MUL_RZERO; REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a * b * content k / d = content k * (a * b) / d`;
                NORM_MUL] THEN
    SUBGOAL_THEN `&0 < content(k:real^M->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONTENT_LT_NZ; tagged_partial_division_of]; ALL_TAC] THEN
    ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_LE_LMUL_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `x + &1 <= y ==> x <= y`) THEN
    SUBGOAL_THEN `?u v. k = interval[u:real^M,v]` MP_TAC THENL
     [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`u:real^M`; `v:real^M`] CONTENT_POS_LT_EQ) THEN
    ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; REAL_LT_IMP_LE] THEN
    DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) REAL_LE_RDIV_EQ o snd) THEN
    ASM_SIMP_TAC[REAL_SUB_LT] THEN DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_ARITH `&0 < norm(x:real^N) + &1`] THEN
    REMOVE_THEN "F" MP_TAC THEN REWRITE_TAC[fine] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `interval[u:real^M,v]`]) THEN
    ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `v:real^M` th) THEN
                         MP_TAC(SPEC `u:real^M` th)) THEN
    ASM_SIMP_TAC[INTERVAL_NE_EMPTY; REAL_LT_IMP_LE; ENDS_IN_INTERVAL] THEN
    REWRITE_TAC[IN_BALL; IMP_IMP] THEN
    MATCH_MP_TAC(NORM_ARITH
     `abs(vi - ui) <= norm(v - u:real^N) /\ &2 * a <= b
      ==> dist(x,u) < a /\ dist(x,v) < a ==> vi - ui <= b`) THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM] THEN
    REWRITE_TAC[REAL_ARITH `&2 * e / &8 / x * y = e / &4 * y / x`] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * inv b * inv c:real = (a / c) / b`] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `abs x <= e ==> x <= e`) THEN
    REWRITE_TAC[real_div; REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
      SIMP_TAC[REAL_INF_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY; FINITE_NUMSEG;
               NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1; REAL_LE_INF_FINITE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_NUMSEG] THEN
      ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; REAL_LE_REFL; REAL_SUB_LE;
                   REAL_LT_IMP_LE] THEN
      ASM_MESON_TAC[REAL_LE_REFL];
      REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONJ_TAC THENL [NORM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + &1 <= abs(y + &1)`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[tagged_partial_division_of; SUBSET]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP TAGGED_PARTIAL_DIVISION_OF_UNION_SELF) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    SUM_OVER_TAGGED_DIVISION_LEMMA)) THEN
  DISCH_THEN(fun th ->
    W(MP_TAC o PART_MATCH (lhs o rand) th o lhand o snd)) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[SUM_LMUL; REAL_ARITH
   `e / &4 * ba / c * s <= e / &2 <=> e * (ba * s) / c <= e * &2`] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC SUM_CONTENT_AREA_OVER_THIN_DIVISION THEN
  EXISTS_TAC `UNIONS(IMAGE SND (p:(real^M#(real^M->bool))->bool))` THEN
  EXISTS_TAC `(c:real^M)$i` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN ASM_SIMP_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DIVISION_OF_TAGGED_DIVISION THEN
    ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_OF_UNION_SELF];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    ASM_MESON_TAC[tagged_partial_division_of];
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM]]);;

let EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LE = prove
 (`!fs f:real^M->real^N a b.
        fs equiintegrable_on interval[a,b] /\ f IN fs /\
        (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x))
        ==> { (\x. if x$i <= c then h x else vec 0) |
              i IN 1..dimindex(:M) /\ c IN (:real) /\ h IN fs }
            equiintegrable_on interval[a,b]`,
  let lemma = prove
   (`(!x k. (x,k) IN IMAGE (\(x,k). f x k,g x k) s ==> Q x k) <=>
     (!x k. (x,k) IN s ==> Q (f x k) (g x k))`,
    REWRITE_TAC[IN_IMAGE; PAIR_EQ; EXISTS_PAIR_THM] THEN SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^M,b]) = &0` THEN
  ASM_SIMP_TAC[EQUIINTEGRABLE_ON_NULL] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTENT_LT_NZ]) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[CONTENT_POS_LT_EQ] THEN STRIP_TAC THEN
  REWRITE_TAC[equiintegrable_on] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_UNIV; IMP_IMP; GSYM CONJ_ASSOC; RIGHT_IMP_FORALL_THM;
              IN_NUMSEG] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[equiintegrable_on]) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[SET_RULE `x$i <= c <=> x IN {x:real^N | x$i <= c}`] THEN
    REWRITE_TAC[INTEGRABLE_RESTRICT_INTER] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN SIMP_TAC[INTERVAL_SPLIT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `interval[a:real^M,b]` THEN ASM_SIMP_TAC[] THEN
    SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA; REAL_LE_REFL] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`fs:(real^M->real^N)->bool`; `f:real^M->real^N`;
                 `a:real^M`; `b:real^M`; `e / &12`]
        BOUNDED_EQUIINTEGRAL_OVER_THIN_TAGGED_PARTIAL_DIVISION) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &12`] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?d. gauge d /\
        !p h. p tagged_partial_division_of interval [a,b] /\
              d fine p /\ (h:real^M->real^N) IN fs
              ==> sum p (\(x,k). norm(content k % h x - integral k h)) <
                  e / &3`
   (X_CHOOSE_THEN `g1:real^M->real^M->bool` STRIP_ASSUME_TAC)
  THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[equiintegrable_on]) THEN
    DISCH_THEN(MP_TAC o SPEC `e / &7 / (&(dimindex(:N)) + &1)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &7 /\ &0 < &n + &1`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `d:real^M->real^M->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC
     [`p:(real^M#(real^M->bool))->bool`; `h:real^M->real^N`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`h:real^M->real^N`; `a:real^M`; `b:real^M`;
           `d:real^M->real^M->bool`; `e / &7 / (&(dimindex(:N)) + &1)`]
        HENSTOCK_LEMMA_PART2) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &7 /\ &0 < &n + &1`] THEN
    DISCH_THEN(MP_TAC o SPEC `p:(real^M#(real^M->bool))->bool`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `a < b ==> x <= a ==> x < b`) THEN
    REWRITE_TAC[REAL_ARITH `&2 * d * e / &7 / (d + &1) =
                            (e * &2 / &7 * d) / (d + &1)`] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ &0 < e * d ==> e * &2 / &7 * d < e / &3 * (d + &1)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1];
    ALL_TAC] THEN
  EXISTS_TAC `\x. (g0:real^M->real^M->bool) x INTER g1 x` THEN
  ASM_SIMP_TAC[GAUGE_INTER; FINE_INTER] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `1 <= i` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i <= dimindex(:M)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(MESON[]
   `!P. ((!c. (a:real^M)$i <= c /\ c <= (b:real^M)$i ==> P c) ==> (!c. P c)) /\
        (!c. (a:real^M)$i <= c /\ c <= (b:real^M)$i ==> P c)
        ==> !c. P c`) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [DISCH_THEN(LABEL_TAC "*") THEN
    X_GEN_TAC `c:real` THEN
    ASM_CASES_TAC `(a:real^M)$i <= c /\ c <= (b:real^M)$i` THENL
     [REMOVE_THEN "*" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `(b:real^M)$i`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `h:real^M->real^N` THEN
    MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
    REWRITE_TAC[REAL_NOT_LE] THEN STRIP_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC(NORM_ARITH
       `x:real^N = vec 0 /\ y = vec 0 /\ &0 < e ==> norm(x - y) < e`) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
        SUBGOAL_THEN `(x:real^M) IN interval[a,b]` MP_TAC THENL
         [ASM_MESON_TAC[TAGGED_DIVISION_OF; SUBSET]; ALL_TAC] THEN
        REWRITE_TAC[IN_INTERVAL] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `integral(interval[a,b]) ((\x. vec 0):real^M->real^N)` THEN
        CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[INTEGRAL_0]] THEN
        MATCH_MP_TAC INTEGRAL_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(NORM_ARITH
       `x:real^N = y /\ w = z ==> norm(x - w) < e ==> norm(y - z) < e`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
        SUBGOAL_THEN `(x:real^M) IN interval[a,b]` MP_TAC THENL
         [ASM_MESON_TAC[TAGGED_DIVISION_OF; SUBSET]; ALL_TAC] THEN
        REWRITE_TAC[IN_INTERVAL] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC INTEGRAL_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  X_GEN_TAC `c:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`h:real^M->real^N`;
                  `p:(real^M#(real^M->bool))->bool`] THEN STRIP_TAC THEN
  ABBREV_TAC
   `q:(real^M#(real^M->bool))->bool =
        {(x,k) | (x,k) IN p /\ ~(k INTER {x | x$i <= c} = {})}` THEN
  MP_TAC(ISPECL
   [`\x. if x$i <= c then (h:real^M->real^N) x else vec 0`;
    `a:real^M`; `b:real^M`; `p:(real^M#(real^M->bool))->bool`]
        INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `FINITE(p:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
  SUBGOAL_THEN `q SUBSET (p:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN SIMP_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(q:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VSUM_SUB] THEN ONCE_REWRITE_TAC[LAMBDA_PAIR_THM] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `q tagged_partial_division_of interval[a:real^M,b] /\
                g0 fine q /\ g1 fine q`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_SUBSET; tagged_division_of;
                  FINE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `!q. vsum p s = vsum q s /\ norm(vsum q s) < e
                            ==> norm(vsum p s:real^N) < e`) THEN
  EXISTS_TAC `q:(real^M#(real^M->bool))->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    EXPAND_TAC "q" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^M) IN k` ASSUME_TAC THENL
     [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    REWRITE_TAC[IN_INTER; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    REWRITE_TAC[VECTOR_NEG_EQ_0; VECTOR_SUB_LZERO] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral k ((\x. vec 0):real^M->real^N)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[INTEGRAL_0]] THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(vsum q (\(x,k). content k % h x - integral k (h:real^M->real^N)))
        < e / &3`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sum q
      (\(x,k). norm(content k % h x - integral k (h:real^M->real^N)))` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM; REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x - y:real^N) <= &2 * e / &3
    ==> norm(x) < e / &3 ==> norm(y) < e`) THEN
  ASM_SIMP_TAC[GSYM VSUM_SUB] THEN ONCE_REWRITE_TAC[LAMBDA_PAIR_THM] THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC
   `r:(real^M#(real^M->bool))->bool =
        {(x,k) | (x,k) IN q /\ ~(k SUBSET {x | x$i <= c})}` THEN
  SUBGOAL_THEN `r SUBSET (q:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN SIMP_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(r:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `r tagged_partial_division_of interval[a:real^M,b] /\
                g0 fine r /\ g1 fine r`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_SUBSET; FINE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `!r. vsum q s = vsum r s /\ norm(vsum r s) <= e
                            ==> norm(vsum q s:real^N) <= e`) THEN
  EXISTS_TAC `r:(real^M#(real^M->bool))->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    EXPAND_TAC "r" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^M) IN k` ASSUME_TAC THENL
     [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `c - i - (c - j):real^N = j - i`] THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  ONCE_REWRITE_TAC[LAMBDA_PAIR_THM] THEN REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC
   [`s:(real^M#(real^M->bool))->bool =
        {(x,k) | (x,k) IN r /\ x IN {x | x$i <= c}}`;
    `t:(real^M#(real^M->bool))->bool =
        {(x,k) | (x,k) IN r /\ ~(x IN {x | x$i <= c})}`] THEN
  SUBGOAL_THEN
   `(s:(real^M#(real^M->bool))->bool) SUBSET r /\
    (t:(real^M#(real^M->bool))->bool) SUBSET r`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "t"] THEN
    SIMP_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(s:(real^M#(real^M->bool))->bool) /\
    FINITE(t:(real^M#(real^M->bool))->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (s:(real^M#(real^M->bool))->bool) t` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "t"] THEN
    REWRITE_TAC[EXTENSION; DISJOINT; IN_INTER; FORALL_PAIR_THM;
                IN_ELIM_PAIR_THM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r:(real^M#(real^M->bool))->bool = s UNION t` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "t"] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `sum s (\(x:real^M,k). norm
          (integral k (h:real^M->real^N) -
           integral k (\x. if x$i <= c then h x else vec 0))) +
    sum t (\(x:real^M,k). norm
          ((content k % (h:real^M->real^N) x - integral k h) +
           integral k (\x. if x$i <= c then h x else vec 0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN BINOP_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
    MAP_EVERY EXPAND_TAC ["s"; "t"] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC(NORM_ARITH `a:real^N = --b ==> norm a = norm b`) THEN
      VECTOR_ARITH_TAC;
      AP_TERM_TAC THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s tagged_partial_division_of interval[a:real^M,b] /\
                t tagged_partial_division_of interval[a:real^M,b] /\
                g0 fine s /\ g1 fine s /\ g0 fine t /\ g1 fine t`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_SUBSET; FINE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `(sum s (\(x:real^M,k). norm(integral k (h:real^M->real^N))) +
     sum (IMAGE (\(x,k). (x,k INTER {x | x$i <= c})) s)
         (\(x:real^M,k). norm(integral k (h:real^M->real^N)))) +
    (sum t (\(x:real^M,k). norm(content k % h x - integral k h)) +
     sum t (\(x:real^M,k). norm(integral k (h:real^M->real^N))) +
     sum (IMAGE (\(x,k). (x,k INTER {x | x$i >= c})) t)
         (\(x:real^M,k). norm(integral k (h:real^M->real^N))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_NONZERO o
        rand o rand o snd) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC
         [`x:real^M`; `k:real^M->bool`; `y:real^M`; `l:real^M->bool`] THEN
        ASM_CASES_TAC `x:real^M = y` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
        REPEAT STRIP_TAC THEN MP_TAC(ISPECL
         [`s:real^M#(real^M->bool)->bool`;
          `UNIONS(IMAGE SND (s:real^M#(real^M->bool)->bool))`;
          `x:real^M`; `k:real^M->bool`;
          `y:real^M`; `l:real^M->bool`; `i:num`; `c:real`]
         TAGGED_DIVISION_SPLIT_LEFT_INJ) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_OF_UNION_SELF]; ALL_TAC] THEN
        REWRITE_TAC[NORM_EQ_0] THEN
        SUBGOAL_THEN `?u v:real^M. l = interval[u,v]`
         (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
        THENL [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
        ASM_SIMP_TAC[INTERVAL_SPLIT; INTEGRAL_NULL];
        DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
        ASM_REWRITE_TAC[o_THM; FORALL_PAIR_THM] THEN
        ONCE_REWRITE_TAC[SET_RULE
         `x$i <= c <=> x IN {x:real^M | x$i <= c}`] THEN
        REWRITE_TAC[INTEGRAL_RESTRICT_INTER] THEN
        REWRITE_TAC[IN_ELIM_THM; INTER_COMM] THEN
        REWRITE_TAC[NORM_ARITH `norm(a - b:real^N) <= norm a + norm b`]];
      W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_NONZERO o
        rand o rand o rand o snd) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC
         [`x:real^M`; `k:real^M->bool`; `y:real^M`; `l:real^M->bool`] THEN
        ASM_CASES_TAC `x:real^M = y` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
        REPEAT STRIP_TAC THEN MP_TAC(ISPECL
         [`t:real^M#(real^M->bool)->bool`;
          `UNIONS(IMAGE SND (t:real^M#(real^M->bool)->bool))`;
          `x:real^M`; `k:real^M->bool`;
          `y:real^M`; `l:real^M->bool`; `i:num`; `c:real`]
         TAGGED_DIVISION_SPLIT_RIGHT_INJ) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_OF_UNION_SELF]; ALL_TAC] THEN
        REWRITE_TAC[NORM_EQ_0] THEN
        SUBGOAL_THEN `?u v:real^M. l = interval[u,v]`
         (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
        THENL [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
        ASM_SIMP_TAC[INTERVAL_SPLIT; INTEGRAL_NULL];
        DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
        ASM_REWRITE_TAC[o_THM; FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
        MATCH_MP_TAC(NORM_ARITH
         `i = i1 + i2
          ==> norm(c + i1:real^N) <= norm(c) + norm(i) + norm(i2)`) THEN
        ONCE_REWRITE_TAC[SET_RULE
         `x$i <= c <=> x IN {x:real^M | x$i <= c}`] THEN
        REWRITE_TAC[INTEGRAL_RESTRICT_INTER] THEN
        ONCE_REWRITE_TAC[SET_RULE `{x | P x} INTER s = s INTER {x | P x}`] THEN
        SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
         (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
        THENL [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
        ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MATCH_MP_TAC INTEGRAL_SPLIT THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `interval[a:real^M,b]` THEN
        ASM_SIMP_TAC[] THEN ASM_MESON_TAC[tagged_partial_division_of]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^M k. (x,k) IN r ==> ~(k INTER {x:real^M | x$i = c} = {})`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MAP_EVERY EXPAND_TAC ["r"; "q"] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; SUBSET; EXTENSION; NOT_FORALL_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY; IN_INTER; NOT_IMP] THEN
    DISCH_TAC THEN MATCH_MP_TAC CONNECTED_IVT_COMPONENT THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_TOTAL]] THEN
    SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
     (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
    MATCH_MP_TAC CONVEX_CONNECTED THEN REWRITE_TAC[CONVEX_INTERVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= e / &6 /\ y <= e / &2 ==> x + y <= &2 * e / &3`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `x < e / &12 /\ y < e / &12 ==> x + y <= e / &6`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(lambda j. if j = i then c else (a:real^M)$j):real^M` THEN
    EXISTS_TAC `i:num` THEN ASM_SIMP_TAC[LAMBDA_BETA; IN_INTERVAL] THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
        EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
        ASM_MESON_TAC[]];
      REPEAT CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
        UNDISCH_TAC `s tagged_partial_division_of interval[a:real^M,b]`;
        UNDISCH_TAC `(g0:real^M->real^M->bool) fine s` THEN
        REWRITE_TAC[fine; FORALL_IN_IMAGE; lemma] THEN SET_TAC[];
        REWRITE_TAC[lemma] THEN
        REPEAT GEN_TAC THEN EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_TAC THEN MATCH_MP_TAC(SET_RULE
        `~(k INTER t = {}) /\ t SUBSET s ==> ~((k INTER s) INTER t = {})`) THEN
        SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_LE_REFL] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]];
    MATCH_MP_TAC(REAL_ARITH
     `x < e / &3 /\ y < e / &12 /\ z < e / &12 ==> x + y + z <= e / &2`) THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(lambda j. if j = i then c else (a:real^M)$j):real^M` THEN
    EXISTS_TAC `i:num` THEN ASM_SIMP_TAC[LAMBDA_BETA; IN_INTERVAL] THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
        EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
        ASM_MESON_TAC[]];
      REPEAT CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
        UNDISCH_TAC `t tagged_partial_division_of interval[a:real^M,b]`;
        UNDISCH_TAC `(g0:real^M->real^M->bool) fine t` THEN
        REWRITE_TAC[fine; FORALL_IN_IMAGE; lemma] THEN SET_TAC[];
        REWRITE_TAC[lemma] THEN
        REPEAT GEN_TAC THEN EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_TAC THEN MATCH_MP_TAC(SET_RULE
        `~(k INTER t = {}) /\ t SUBSET s ==> ~((k INTER s) INTER t = {})`) THEN
        SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_LE_REFL; real_ge] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]]] THEN
  REWRITE_TAC[tagged_partial_division_of] THEN
  (MATCH_MP_TAC MONO_AND THEN SIMP_TAC[FINITE_IMAGE] THEN
   MATCH_MP_TAC MONO_AND THEN
   REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_GSPEC] THEN
   REWRITE_TAC[lemma] THEN CONJ_TAC THEN
   MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
   MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:real^M->bool` THEN
   DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THENL
    [MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
      [SIMP_TAC[real_ge; IN_INTER; IN_ELIM_THM] THEN ASM SET_TAC[REAL_LE_TOTAL];
       MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
        [SET_TAC[];
         STRIP_TAC THEN ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MESON_TAC[]]];
     REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
     MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
     MATCH_MP_TAC MONO_IMP THEN SIMP_TAC[PAIR_EQ; CONTRAPOS_THM] THEN
     MATCH_MP_TAC(SET_RULE
      `s SUBSET s' /\ t SUBSET t'
       ==> s' INTER t' = {} ==> s INTER t = {}`) THEN CONJ_TAC THEN
     MATCH_MP_TAC SUBSET_INTERIOR THEN REWRITE_TAC[INTER_SUBSET]]));;

let EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GE = prove
 (`!fs f:real^M->real^N a b.
        fs equiintegrable_on interval[a,b] /\ f IN fs /\
        (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x))
        ==> { (\x. if x$i >= c then h x else vec 0) |
              i IN 1..dimindex(:M) /\ c IN (:real) /\ h IN fs }
            equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{\x. (f:real^M->real^N) (--x) | f IN fs}`;
    `\x. (f:real^M->real^N)(--x)`;
    `--b:real^M`; `--a:real^M`]
        EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LE) THEN
  ASM_SIMP_TAC[EQUIINTEGRABLE_REFLECT] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    ONCE_REWRITE_TAC[GSYM IN_INTERVAL_REFLECT] THEN
    ASM_SIMP_TAC[VECTOR_NEG_NEG] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IN_IMAGE] THEN
    EXISTS_TAC `f:real^M->real^N` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_REFLECT) THEN
    REWRITE_TAC[VECTOR_NEG_NEG] THEN MATCH_MP_TAC
     (REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `c:real`; `h:real^M->real^N`] THEN
    STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC
     `(\x. if (--x)$i >= c then (h:real^M->real^N)(--x) else vec 0)` THEN
    REWRITE_TAC[VECTOR_NEG_NEG] THEN MAP_EVERY EXISTS_TAC
     [`i:num`; `--c:real`; `\x. (h:real^M->real^N)(--x)`] THEN
    ASM_REWRITE_TAC[IN_UNIV; VECTOR_NEG_COMPONENT] THEN
    REWRITE_TAC[REAL_ARITH `--x >= c <=> x <= --c`] THEN
    EXISTS_TAC `h:real^M->real^N` THEN ASM_REWRITE_TAC[]]);;

let EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LT = prove
 (`!fs f:real^M->real^N a b.
        fs equiintegrable_on interval[a,b] /\ f IN fs /\
        (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x))
        ==> { (\x. if x$i < c then h x else vec 0) |
              i IN 1..dimindex(:M) /\ c IN (:real) /\ h IN fs }
            equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`fs:(real^M->real^N)->bool`; `f:real^M->real^N`;
                 `a:real^M`; `b:real^M`]
    EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GE) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC
   `(fs:(real^M->real^N)->bool) equiintegrable_on interval[a,b]` THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_SUB) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `c:real`; `h:real^M->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `h:real^M->real^N` THEN
  EXISTS_TAC `\x. if x$i >= c then (h:real^M->real^N) x else vec 0` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i:num`; `c:real`; `h:real^M->real^N`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FUN_EQ_THM; real_ge; GSYM REAL_NOT_LT] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC]);;

let EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GT = prove
 (`!fs f:real^M->real^N a b.
        fs equiintegrable_on interval[a,b] /\ f IN fs /\
        (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x))
        ==> { (\x. if x$i > c then h x else vec 0) |
              i IN 1..dimindex(:M) /\ c IN (:real) /\ h IN fs }
            equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`fs:(real^M->real^N)->bool`; `f:real^M->real^N`;
                 `a:real^M`; `b:real^M`]
    EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LE) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC
   `(fs:(real^M->real^N)->bool) equiintegrable_on interval[a,b]` THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_SUB) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `c:real`; `h:real^M->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `h:real^M->real^N` THEN
  EXISTS_TAC `\x. if x$i <= c then (h:real^M->real^N) x else vec 0` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i:num`; `c:real`; `h:real^M->real^N`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FUN_EQ_THM; real_gt; GSYM REAL_NOT_LE] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC]);;

let EQUIINTEGRABLE_OPEN_INTERVAL_RESTRICTIONS = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> { (\x. if x IN interval(c,d) then f x else vec 0) |
              c IN (:real^M) /\ d IN (:real^M) }
            equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:M)
        ==> f INSERT
            { (\x. if !i. 1 <= i /\ i <= n ==> c$i < x$i /\ x$i < d$i
                   then (f:real^M->real^N) x else vec 0) |
              c IN (:real^M) /\ d IN (:real^M) }
            equiintegrable_on interval[a,b]`
  MP_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC[ARITH_RULE `~(1 <= i /\ i <= 0)`] THEN
    ASM_REWRITE_TAC[ETA_AX; EQUIINTEGRABLE_ON_SING; SET_RULE
     `f INSERT {f |c,d| c IN UNIV /\ d IN UNIV} = {f}`] THEN
    X_GEN_TAC `n:num` THEN ASM_CASES_TAC `SUC n <= dimindex(:M)` THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `f:real^M->real^N` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ]
          EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LT)) THEN
    REWRITE_TAC[IN_INSERT] THEN ANTS_TAC THENL
     [REWRITE_TAC[TAUT
       `a \/ b ==> c ==> d <=> (a ==> c ==> d) /\ (b ==> c ==> d)`] THEN
      SIMP_TAC[REAL_LE_REFL; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[NORM_0; REAL_LE_REFL; NORM_POS_LE];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM EQUIINTEGRABLE_ON_SING]) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_UNION) THEN
    DISCH_THEN(MP_TAC o SPEC `f:real^M->real^N` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ]
          EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GT)) THEN
    ASM_REWRITE_TAC[IN_UNION; IN_SING] THEN ANTS_TAC THENL
     [REWRITE_TAC[TAUT
       `a \/ b ==> c ==> d <=> (a ==> c ==> d) /\ (b ==> c ==> d)`] THEN
      SIMP_TAC[REAL_LE_REFL; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; LEFT_OR_DISTRIB] THEN
      REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
      SIMP_TAC[REAL_LE_REFL; RIGHT_FORALL_IMP_THM]  THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC;
                  FORALL_AND_THM] THEN
      SIMP_TAC[IN_UNIV] THEN
      REPEAT STRIP_TAC THEN
      REPEAT(COND_CASES_TAC THEN
             ASM_SIMP_TAC[NORM_0; REAL_LE_REFL; NORM_POS_LE]);
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM EQUIINTEGRABLE_ON_SING]) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_UNION) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    MATCH_MP_TAC(SET_RULE
      `s SUBSET t ==> (x INSERT s) SUBSET ({x} UNION t)`) THEN
    REWRITE_TAC[SUBSET; real_gt; FORALL_IN_GSPEC; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`c:real^M`; `d:real^M`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `SUC n` THEN
    ASM_REWRITE_TAC[IN_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    EXISTS_TAC `(c:real^M)$(SUC n)` THEN
    MATCH_MP_TAC(MESON[]
     `(?i c k. P i c k /\ Q (g i c k))
      ==> ?h. (h = f \/ ?i c k. P i c k /\ h = g i c k) /\ Q h`) THEN
    EXISTS_TAC `SUC n` THEN
    ASM_REWRITE_TAC[IN_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    EXISTS_TAC `(d:real^M)$(SUC n)` THEN
    EXISTS_TAC
     `\x. if !i. 1 <= i /\ i <= n ==> (c:real^M)$i < x$i /\ x$i < (d:real^M)$i
          then (f:real^M->real^N) x else vec 0` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`c:real^M`; `d:real^M`] THEN REWRITE_TAC[];
      REWRITE_TAC[FUN_EQ_THM; LE] THEN
      ASM_MESON_TAC[ARITH_RULE `1 <= SUC n`]];
    DISCH_THEN(MP_TAC o SPEC `dimindex(:M)`) THEN
    REWRITE_TAC[IN_INTERVAL; LE_REFL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    SET_TAC[]]);;

let EQUIINTEGRABLE_CLOSED_INTERVAL_RESTRICTIONS = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> { (\x. if x IN interval[c,d] then f x else vec 0) |
              c IN (:real^M) /\ d IN (:real^M) }
            equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:M)
        ==> f INSERT
            { (\x. if !i. 1 <= i /\ i <= n ==> c$i <= x$i /\ x$i <= d$i
                   then (f:real^M->real^N) x else vec 0) |
              c IN (:real^M) /\ d IN (:real^M) }
            equiintegrable_on interval[a,b]`
  MP_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC[ARITH_RULE `~(1 <= i /\ i <= 0)`] THEN
    ASM_REWRITE_TAC[ETA_AX; EQUIINTEGRABLE_ON_SING; SET_RULE
     `f INSERT {f |c,d| c IN UNIV /\ d IN UNIV} = {f}`] THEN
    X_GEN_TAC `n:num` THEN ASM_CASES_TAC `SUC n <= dimindex(:M)` THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `f:real^M->real^N` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ]
          EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LE)) THEN
    REWRITE_TAC[IN_INSERT] THEN ANTS_TAC THENL
     [REWRITE_TAC[TAUT
       `a \/ b ==> c ==> d <=> (a ==> c ==> d) /\ (b ==> c ==> d)`] THEN
      SIMP_TAC[REAL_LE_REFL; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[NORM_0; REAL_LE_REFL; NORM_POS_LE];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM EQUIINTEGRABLE_ON_SING]) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_UNION) THEN
    DISCH_THEN(MP_TAC o SPEC `f:real^M->real^N` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ]
          EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GE)) THEN
    ASM_REWRITE_TAC[IN_UNION; IN_SING] THEN ANTS_TAC THENL
     [REWRITE_TAC[TAUT
       `a \/ b ==> c ==> d <=> (a ==> c ==> d) /\ (b ==> c ==> d)`] THEN
      SIMP_TAC[REAL_LE_REFL; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; LEFT_OR_DISTRIB] THEN
      REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
      SIMP_TAC[REAL_LE_REFL; RIGHT_FORALL_IMP_THM]  THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC;
                  FORALL_AND_THM] THEN
      SIMP_TAC[IN_UNIV] THEN
      REPEAT STRIP_TAC THEN
      REPEAT(COND_CASES_TAC THEN
             ASM_SIMP_TAC[NORM_0; REAL_LE_REFL; NORM_POS_LE]);
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM EQUIINTEGRABLE_ON_SING]) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_UNION) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    MATCH_MP_TAC(SET_RULE
      `s SUBSET t ==> (x INSERT s) SUBSET ({x} UNION t)`) THEN
    REWRITE_TAC[SUBSET; real_ge; FORALL_IN_GSPEC; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`c:real^M`; `d:real^M`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `SUC n` THEN
    ASM_REWRITE_TAC[IN_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    EXISTS_TAC `(c:real^M)$(SUC n)` THEN
    MATCH_MP_TAC(MESON[]
     `(?i c k. P i c k /\ Q (g i c k))
      ==> ?h. (h = f \/ ?i c k. P i c k /\ h = g i c k) /\ Q h`) THEN
    EXISTS_TAC `SUC n` THEN
    ASM_REWRITE_TAC[IN_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    EXISTS_TAC `(d:real^M)$(SUC n)` THEN
    EXISTS_TAC
     `\x. if !i. 1 <= i /\ i <= n ==> (c:real^M)$i <= x$i /\ x$i <= (d:real^M)$i
          then (f:real^M->real^N) x else vec 0` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`c:real^M`; `d:real^M`] THEN REWRITE_TAC[];
      REWRITE_TAC[FUN_EQ_THM; LE] THEN
      ASM_MESON_TAC[ARITH_RULE `1 <= SUC n`]];
    DISCH_THEN(MP_TAC o SPEC `dimindex(:M)`) THEN
    REWRITE_TAC[IN_INTERVAL; LE_REFL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of the indefinite integral.                                    *)
(* ------------------------------------------------------------------------- *)

let INDEFINITE_INTEGRAL_CONTINUOUS = prove
 (`!f:real^M->real^N a b c d e.
        f integrable_on interval[a,b] /\
        c IN interval[a,b] /\ d IN interval[a,b] /\ &0 < e
        ==> ?k. &0 < k /\
                !c' d'. c' IN interval[a,b] /\
                        d' IN interval[a,b] /\
                        norm(c' - c) <= k /\ norm(d' - d) <= k
                        ==> norm(integral(interval[c',d']) f -
                                 integral(interval[c,d]) f) < e`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(?k. P k /\ Q k) <=> ~(!k. P k ==> ~Q k)`] THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  PURE_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`; SKOLEM_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_NOT_LT; GSYM CONJ_ASSOC] THEN
  MAP_EVERY X_GEN_TAC [`u:num->real^M`; `v:num->real^M`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  ABBREV_TAC
   `k:real^M->bool =
    UNIONS (IMAGE (\i. {x | x$i = (c:real^M)$i} UNION {x | x$i = (d:real^M)$i})
                  (1..dimindex(:M)))` THEN
  SUBGOAL_THEN `negligible(k:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[NEGLIGIBLE_UNION; NEGLIGIBLE_STANDARD_HYPERPLANE];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n:num x. if x IN interval[u n,v n] then
                 if x IN k then vec 0 else (f:real^M->real^N) x
               else vec 0`;
    `\x. if x IN interval[c,d] then
            if x IN k then vec 0 else (f:real^M->real^N) x
         else vec 0`;
    `a:real^M`; `b:real^M`] EQUIINTEGRABLE_LIMIT) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\x. if x IN k then vec 0 else (f:real^M->real^N) x)
      integrable_on interval[a,b]`
    MP_TAC THENL
     [UNDISCH_TAC `(f:real^M->real^N) integrable_on interval[a,b]` THEN
      MATCH_MP_TAC INTEGRABLE_SPIKE THEN EXISTS_TAC `k:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
      EQUIINTEGRABLE_CLOSED_INTERVAL_RESTRICTIONS) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `n:num` THEN MAP_EVERY EXISTS_TAC
     [`(u:num->real^M) n`; `(v:num->real^M) n`] THEN
    REWRITE_TAC[];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^M) IN k` THEN
    ASM_REWRITE_TAC[COND_ID; LIM_CONST] THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `inf (IMAGE (\i. min (abs((x:real^M)$i - (c:real^M)$i))
                                     (abs((x:real^M)$i - (d:real^M)$i)))
                            (1..dimindex(:M)))` REAL_ARCH_INV) THEN
    SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
             FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; REAL_LT_MIN; IN_NUMSEG] THEN
    UNDISCH_TAC `~((x:real^M) IN k)` THEN EXPAND_TAC "k" THEN
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    REWRITE_TAC[IN_NUMSEG; SET_RULE
     `~(p /\ x IN (s UNION t)) <=> p ==> ~(x IN s) /\ ~(x IN t)`] THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_ARITH `&0 < abs(x - y) <=> ~(x = y)`] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `x IN interval[(u:num->real^M) n,v n] <=> x IN interval[c,d]`
     (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_INTERVAL] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `1 <= i /\ i <= dimindex(:M)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!N n. abs(u - c) <= n /\ abs(v - d) <= n /\
            N < abs(x - c) /\ N < abs(x - d) /\ n <= N
      ==> (u <= x /\ x <= v <=> c <= x /\ x <= d)`) THEN
    MAP_EVERY EXISTS_TAC [`inv(&N)`; `inv(&n + &1)`] THEN
    ASM_SIMP_TAC[] THEN REPEAT (CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_LE_TRANS; COMPONENT_LE_NORM; VECTOR_SUB_COMPONENT];
      ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[INTEGRAL_RESTRICT_INTER] THEN
    SUBGOAL_THEN
     `interval[c:real^M,d] INTER interval[a,b] = interval[c,d] /\
      !n:num. interval[u n,v n] INTER interval[a,b] = interval[u n,v n]`
     (fun th -> SIMP_TAC[th])
    THENL
     [REWRITE_TAC[SET_RULE `s INTER t = s <=> s SUBSET t`] THEN
      REWRITE_TAC[SUBSET_INTERVAL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
    REWRITE_TAC[LE_REFL; REAL_NOT_LT] THEN
    FIRST_ASSUM(fun th -> MP_TAC(SPEC `N:num` th) THEN MATCH_MP_TAC
    (NORM_ARITH `x = a /\ y = b ==> e <= norm(x - y) ==> e <= dist(a,b)`)) THEN
    CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[IN_DIFF]]);;

let INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
         ==> (\x. integral (interval[a,x]) f) continuous_on interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[continuous_within] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`;
                 `a:real^M`; `x:real^M`; `e:real`]
        INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[dist]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[ENDS_IN_INTERVAL; VECTOR_SUB_REFL; NORM_0; REAL_LT_IMP_LE] THEN
  ASM SET_TAC[]);;

let INDEFINITE_INTEGRAL_CONTINUOUS_LEFT = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> (\x. integral(interval[x,b]) f) continuous_on interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[continuous_within] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`;
                 `x:real^M`; `b:real^M`; `e:real`]
        INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[dist]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[ENDS_IN_INTERVAL; VECTOR_SUB_REFL; NORM_0; REAL_LT_IMP_LE] THEN
  ASM SET_TAC[]);;

let INDEFINITE_INTEGRAL_UNIFORMLY_CONTINUOUS = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> (\y. integral (interval[fstcart y,sndcart y]) f)
            uniformly_continuous_on interval[pastecart a a,pastecart b b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN
  REWRITE_TAC[COMPACT_INTERVAL; continuous_on] THEN
  REWRITE_TAC[FORALL_PASTECART; GSYM PCROSS_INTERVAL; PCROSS] THEN
  REWRITE_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`c:real^M`; `d:real^M`] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC(ISPECL
   [`f:real^M->real^N`; `a:real^M`; `b:real^M`; `c:real^M`; `d:real^M`;
    `e:real`] INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[dist] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `k:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[PASTECART_SUB] THEN
  ASM_MESON_TAC[NORM_LE_PASTECART; REAL_LT_IMP_LE; REAL_LE_TRANS]);;

let INDEFINITE_INTEGRAL_UNIFORMLY_CONTINUOUS_EXPLICIT = prove
 (`!f:real^M->real^N a b e.
        f integrable_on interval[a,b] /\ &0 < e
        ==> ?k. &0 < k /\
                !c d c' d'. c IN interval[a,b] /\ d IN interval[a,b] /\
                            c' IN interval[a,b] /\ d' IN interval[a,b] /\
                            norm (c' - c) <= k /\ norm (d' - d) <= k
                            ==> norm(integral(interval[c',d']) f -
                                     integral(interval[c,d]) f) < e`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`f:real^M->real^N`; `a:real^M`; `b:real^M`]
    INDEFINITE_INTEGRAL_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k / &3` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^M`; `c':real^M`; `d:real^M`; `d':real^M`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`pastecart (c:real^M) (c':real^M)`;
    `pastecart (d:real^M) (d':real^M)`]) THEN
  REWRITE_TAC[GSYM PCROSS_INTERVAL; PCROSS] THEN
  REWRITE_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_REWRITE_TAC[dist; PASTECART_SUB] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[NORM_PASTECART_LE; REAL_LET_TRANS;
    REAL_ARITH `&0 < k /\ x <= k / &3 /\ y <= k / &3 ==> x + y < k`]);;

let BOUNDED_INTEGRALS_OVER_SUBINTERVALS = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> bounded { integral (interval[c,d]) f |
                      interval[c,d] SUBSET interval[a,b]}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP
    INDEFINITE_INTEGRAL_UNIFORMLY_CONTINUOUS) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    BOUNDED_UNIFORMLY_CONTINUOUS_IMAGE)) THEN
  REWRITE_TAC[BOUNDED_INTERVAL] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[FORALL_PASTECART; GSYM PCROSS_INTERVAL; PASTECART_IN_PCROSS] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SIMP_TAC[INTERVAL_SUBSET_IS_INTERVAL; IS_INTERVAL_INTERVAL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_SIMP_TAC[INTEGRAL_EMPTY; NORM_0; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* Substitution.                                                             *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_SUBSTITUTION_STRONG = prove
 (`!f:real^1->real^N g g' a b c d k.
        COUNTABLE k /\
        f integrable_on interval[c,d] /\
        g continuous_on interval[a,b] /\
        IMAGE g (interval[a,b]) SUBSET interval[c,d] /\
        (!x. x IN interval[a,b] DIFF k
                  ==> (g has_vector_derivative g'(x))
                       (at x within interval[a,b]) /\
                      f continuous
                        (at(g x)) within interval[c,d]) /\
        drop a <= drop b /\ drop c <= drop d /\ drop(g a) <= drop(g b)
        ==> ((\x. drop(g' x) % f(g x)) has_integral
             integral (interval[g a,g b]) f) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ff = \x. integral (interval[c,x]) (f:real^1->real^N)` THEN
  MP_TAC(ISPECL
   [`(ff:real^1->real^N) o (g:real^1->real^1)`;
    `\x:real^1.  drop(g' x) % (f:real^1->real^N)(g x)`;

     `k:real^1->bool`; `a:real^1`; `b:real^1`]
   FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[c:real^1,d]` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "ff" THEN
      MATCH_MP_TAC INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
        INTERVAL_OPEN_SUBSET_CLOSED)) THEN
      SUBGOAL_THEN `(ff o g has_vector_derivative
                     drop(g' x) % (f:real^1->real^N)(g x))
                    (at x within interval[a,b])`
      MP_TAC THENL
       [MATCH_MP_TAC VECTOR_DIFF_CHAIN_WITHIN THEN ASM_SIMP_TAC[IN_DIFF] THEN
        MP_TAC(ISPECL [`f:real^1->real^N`; `c:real^1`; `d:real^1`;
                       `(g:real^1->real^1) x`]
          INTEGRAL_HAS_VECTOR_DERIVATIVE_POINTWISE) THEN
        ASM_SIMP_TAC[CONTINUOUS_AT_WITHIN; IN_DIFF] THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET];
        REWRITE_TAC[has_vector_derivative; has_derivative] THEN
        ASM_SIMP_TAC[LIM_WITHIN_INTERIOR; INTERIOR_INTERVAL;
                     NETLIMIT_WITHIN_INTERIOR; NETLIMIT_AT]]];
    EXPAND_TAC "ff" THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC(VECTOR_ARITH
     `z + w:real^N = y ==> y - z = w`) THEN
    MATCH_MP_TAC INTEGRAL_COMBINE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        INTEGRABLE_SUBINTERVAL))] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTERVAL_1; SUBSET] THEN
    ASM_MESON_TAC[REAL_LE_REFL; REAL_LE_TRANS]]);;
