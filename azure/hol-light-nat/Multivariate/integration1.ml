(* ========================================================================= *)
(* Kurzweil-Henstock gauge integration in many dimensions.                   *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

open Hol_core
open Products
open Floor
open Card
open Determinants
open Vectors
open Topology
open Convex
open Paths
open Polytope
open Dimension
open Derivatives

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Some useful lemmas about intervals.                                       *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_SUBSET_UNION_INTERVALS = prove
 (`!s i j. (?a b:real^N. i = interval[a,b]) /\ (?c d. j = interval[c,d]) /\
           ~(interior j = {}) /\
           i SUBSET j UNION s /\
           interior(i) INTER interior(j) = {}
           ==> interior i SUBSET interior s`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  MATCH_MP_TAC INTERIOR_MAXIMAL THEN REWRITE_TAC[OPEN_INTERIOR] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERIOR_CLOSED_INTERVAL]) THEN
  SUBGOAL_THEN `interval(a:real^N,b) INTER interval[c,d] = {}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTER_INTERVAL_MIXED_EQ_EMPTY];
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]]);;

let INTER_INTERIOR_UNIONS_INTERVALS = prove
 (`!s f. FINITE f /\ open s /\
         (!t. t IN f ==> ?a b:real^N. t = interval[a,b]) /\
         (!t. t IN f ==> s INTER (interior t) = {})
         ==> s INTER interior(UNIONS f) = {}`,
  ONCE_REWRITE_TAC[TAUT
    `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> ~e ==> ~d`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; GSYM MEMBER_NOT_EMPTY] THEN
  SIMP_TAC[OPEN_CONTAINS_BALL_EQ; OPEN_INTER; OPEN_INTERIOR] THEN
  SIMP_TAC[OPEN_SUBSET_INTERIOR; OPEN_BALL; SUBSET_INTER] THEN
  REWRITE_TAC[GSYM SUBSET_INTER] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_0; INTER_EMPTY; SUBSET_EMPTY] THEN
    MESON_TAC[CENTRE_IN_BALL; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:real^N->bool`; `f:(real^N->bool)->bool`] THEN
  DISCH_TAC THEN
  REWRITE_TAC[UNIONS_INSERT; IN_INSERT] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; FORALL_AND_THM; EXISTS_OR_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `i:real^N->bool`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
   `(r ==> s \/ p) ==> (p ==> q) ==> r ==> s \/ q`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN interval[a,b]` THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `?d. &0 < d /\ ball(x,d) SUBSET ((:real^N) DIFF interval[a,b])`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[closed; OPEN_CONTAINS_BALL; CLOSED_INTERVAL;
                    IN_DIFF; IN_UNIV];
      ALL_TAC] THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^N`; `min d e`] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; SUBSET] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET])) THEN
    SIMP_TAC[IN_BALL; REAL_LT_MIN; IN_DIFF; IN_INTER; IN_UNIV; IN_UNION] THEN
    ASM_MESON_TAC[]] THEN
  ASM_CASES_TAC `(x:real^N) IN interval(a,b)` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN
     `?d. &0 < d /\ ball(x:real^N,d) SUBSET interval(a,b)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_CONTAINS_BALL; OPEN_INTERVAL]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`x:real^N`; `min d e`] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; SUBSET] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET])) THEN
    SIMP_TAC[IN_BALL; REAL_LT_MIN; IN_DIFF; IN_INTER; IN_UNIV; IN_UNION] THEN
    ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_INTERVAL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN ASM_SIMP_TAC[REAL_LT_LE] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[GSYM REAL_LT_LE; DE_MORGAN_THM] THEN
  STRIP_TAC THEN DISJ2_TAC THENL
   [EXISTS_TAC `x + --e / &2 % basis k :real^N`;
    EXISTS_TAC `x + e / &2 % basis k :real^N`] THEN
  EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `b1 SUBSET k INTER (i UNION s)
    ==> b2 SUBSET b1 /\ b2 INTER i = {}
        ==> b2 SUBSET k INTER s`)) THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; IN_BALL] THEN
     GEN_TAC THEN MATCH_MP_TAC(NORM_ARITH `norm(d) = e / &2 ==>
        dist(x + d,y) < e / &2 ==> dist(x,y) < e`) THEN
     ASM_SIMP_TAC[NORM_MUL; NORM_BASIS] THEN UNDISCH_TAC `&0 < e` THEN
     REAL_ARITH_TAC;
     ALL_TAC]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERVAL; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_BALL; dist] THEN
  REWRITE_TAC[TAUT `~(a /\ b) <=> a ==> ~b`] THEN
  W(MP_TAC o C ISPEC COMPONENT_LE_NORM o rand o lhand o lhand o snd) THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `x <= y /\ y < e ==> x < e`)) THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o SPEC `k:num`) THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* This lemma about iterations comes up in a few places.                     *)
(* ------------------------------------------------------------------------- *)

let ITERATE_NONZERO_IMAGE_LEMMA = prove
 (`!op s f g a.
      monoidal op /\ FINITE s /\
      g(a) = neutral op /\
      (!x y. x IN s /\ y IN s /\ f x = f y /\ ~(x = y) ==> g(f x) = neutral op)
      ==> iterate op {f x | x | x IN s /\ ~(f x = a)} g =
          iterate op s (g o f)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[support] THEN
  ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                             IMAGE f {x | x IN s /\ ~(f x = a)}`] THEN
  W(fun (asl,w) -> FIRST_ASSUM(fun th ->
   MP_TAC(PART_MATCH (rand o rand)
       (MATCH_MP ITERATE_IMAGE th) (rand w)))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_SUPERSET) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; SUBSET] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; o_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Bounds on intervals where they exist.                                     *)
(* ------------------------------------------------------------------------- *)

let interval_upperbound = new_definition
  `(interval_upperbound:(real^M->bool)->real^M) s =
        lambda i. sup {a | ?x. x IN s /\ (x$i = a)}`;;

let interval_lowerbound = new_definition
  `(interval_lowerbound:(real^M->bool)->real^M) s =
        lambda i. inf {a | ?x. x IN s /\ (x$i = a)}`;;

let INTERVAL_UPPERBOUND = prove
 (`!a b:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i)
                ==> interval_upperbound(interval[a,b]) = b`,
  SIMP_TAC[interval_upperbound; CART_EQ; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_UNIQUE THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL] THEN ASM_MESON_TAC[REAL_LE_REFL]);;

let INTERVAL_LOWERBOUND = prove
 (`!a b:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i)
                ==> interval_lowerbound(interval[a,b]) = a`,
  SIMP_TAC[interval_lowerbound; CART_EQ; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INF_UNIQUE THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL] THEN ASM_MESON_TAC[REAL_LE_REFL]);;

let INTERVAL_UPPERBOUND_1 = prove
 (`!a b. drop a <= drop b ==> interval_upperbound(interval[a,b]) = b`,
  SIMP_TAC[INTERVAL_UPPERBOUND; DIMINDEX_1; FORALL_1; drop]);;

let INTERVAL_LOWERBOUND_1 = prove
 (`!a b. drop a <= drop b ==> interval_lowerbound(interval[a,b]) = a`,
  SIMP_TAC[INTERVAL_LOWERBOUND; DIMINDEX_1; FORALL_1; drop]);;

let INTERVAL_LOWERBOUND_NONEMPTY = prove
 (`!a b:real^N.
    ~(interval[a,b] = {}) ==> interval_lowerbound(interval[a,b]) = a`,
  SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_NE_EMPTY]);;

let INTERVAL_UPPERBOUND_NONEMPTY = prove
 (`!a b:real^N.
    ~(interval[a,b] = {}) ==> interval_upperbound(interval[a,b]) = b`,
  SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_NE_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Content (length, area, volume...) of an interval.                         *)
(* ------------------------------------------------------------------------- *)

let content = new_definition
   `content(s:real^M->bool) =
       if s = {} then &0 else
       product(1..dimindex(:M))
              (\i. (interval_upperbound s)$i - (interval_lowerbound s)$i)`;;

let CONTENT_CLOSED_INTERVAL = prove
 (`!a b:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i)
                ==> content(interval[a,b]) =
                        product(1..dimindex(:N)) (\i. b$i - a$i)`,
  SIMP_TAC[content; INTERVAL_UPPERBOUND; INTERVAL_EQ_EMPTY;
           INTERVAL_LOWERBOUND] THEN
  MESON_TAC[REAL_NOT_LT]);;

let CONTENT_1 = prove
 (`!a b. drop a <= drop b ==> content(interval[a,b]) = drop b - drop a`,
  SIMP_TAC[CONTENT_CLOSED_INTERVAL; FORALL_1; drop; DIMINDEX_1] THEN
  REWRITE_TAC[PRODUCT_SING_NUMSEG]);;

let CONTENT_UNIT = prove
 (`content(interval[vec 0:real^N,vec 1]) = &1`,
  REWRITE_TAC[content] THEN COND_CASES_TAC THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[INTERVAL_NE_EMPTY; VEC_COMPONENT; REAL_POS];
    MATCH_MP_TAC PRODUCT_EQ_1 THEN
    SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND;
             VEC_COMPONENT; REAL_POS; IN_NUMSEG; REAL_SUB_RZERO]]);;

let CONTENT_UNIT_1 = prove
 (`content(interval[vec 0:real^1,vec 1]) = &1`,
  MATCH_ACCEPT_TAC CONTENT_UNIT);;

let CONTENT_POS_LE = prove
 (`!a b:real^N. &0 <= content(interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[content] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; REAL_SUB_LE]);;

let CONTENT_POS_LT = prove
 (`!a b:real^N.
        (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i)
        ==> &0 < content(interval[a,b])`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CONTENT_CLOSED_INTERVAL; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; REAL_SUB_LT;
               REAL_LT_IMP_LE]);;

let CONTENT_POS_LT_1 = prove
 (`!a b. drop a < drop b ==> &0 < content(interval[a,b])`,
  SIMP_TAC[CONTENT_POS_LT; FORALL_1; DIMINDEX_1; GSYM drop]);;

let CONTENT_EQ_0_GEN = prove
 (`!s:real^N->bool.
     bounded s
     ==> (content s = &0 <=>
          ?i a. 1 <= i /\ i <= dimindex(:N) /\ !x. x IN s ==> x$i = a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[content] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THENL
   [MESON_TAC[DIMINDEX_GE_1; LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[PRODUCT_EQ_0_NUMSEG; REAL_SUB_0] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `k:num` THEN
  ASM_CASES_TAC `1 <= k` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[interval_upperbound; interval_lowerbound; LAMBDA_BETA] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) REAL_SUP_EQ_INF o lhs o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS];
    DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[]]);;

let CONTENT_EQ_0 = prove
 (`!a b:real^N.
        content(interval[a,b]) = &0 <=>
        ?i. 1 <= i /\ i <= dimindex(:N) /\ b$i <= a$i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[content; INTERVAL_EQ_EMPTY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[PRODUCT_EQ_0_NUMSEG; REAL_SUB_0] THEN
  AP_TERM_TAC THEN ABS_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN
  SIMP_TAC[REAL_NOT_LT; INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND] THEN
  MESON_TAC[REAL_NOT_LE; REAL_LE_LT]);;

let CONTENT_0_SUBSET_GEN = prove
 (`!s t:real^N->bool.
      s SUBSET t /\ bounded t /\ content t = &0 ==> content s = &0`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `bounded(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONTENT_EQ_0_GEN] THEN ASM SET_TAC[]);;

let CONTENT_0_SUBSET = prove
 (`!s a b:real^N.
        s SUBSET interval[a,b] /\ content(interval[a,b]) = &0
        ==> content s = &0`,
  MESON_TAC[CONTENT_0_SUBSET_GEN; BOUNDED_INTERVAL]);;

let CONTENT_CLOSED_INTERVAL_CASES = prove
 (`!a b:real^N.
        content(interval[a,b]) =
                if !i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i
                then product(1..dimindex(:N)) (\i. b$i - a$i)
                else &0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CONTENT_EQ_0; CONTENT_CLOSED_INTERVAL] THEN
  ASM_MESON_TAC[REAL_LE_TOTAL]);;

let CONTENT_EQ_0_INTERIOR = prove
 (`!a b:real^N.
        content(interval[a,b]) = &0 <=> interior(interval[a,b]) = {}`,
  REWRITE_TAC[CONTENT_EQ_0; INTERIOR_CLOSED_INTERVAL; INTERVAL_EQ_EMPTY]);;

let CONTENT_EQ_0_1 = prove
 (`!a b:real^1.
        content(interval[a,b]) = &0 <=> drop b <= drop a`,
  REWRITE_TAC[CONTENT_EQ_0; drop; DIMINDEX_1; CONJ_ASSOC; LE_ANTISYM] THEN
  MESON_TAC[]);;

let CONTENT_POS_LT_EQ = prove
 (`!a b:real^N.
        &0 < content(interval[a,b]) <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[CONTENT_POS_LT] THEN
  REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
  REWRITE_TAC[CONTENT_POS_LE; CONTENT_EQ_0] THEN MESON_TAC[REAL_NOT_LE]);;

let CONTENT_EMPTY = prove
 (`content {} = &0`,
  REWRITE_TAC[content]);;

let CONTENT_SUBSET = prove
 (`!a b c d:real^N.
        interval[a,b] SUBSET interval[c,d]
        ==> content(interval[a,b]) <= content(interval[c,d])`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [content] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CONTENT_POS_LE] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
  REWRITE_TAC[IN_INTERVAL] THEN DISCH_THEN(fun th ->
    MP_TAC(SPEC `a:real^N` th) THEN MP_TAC(SPEC `b:real^N` th)) THEN
  ASM_SIMP_TAC[REAL_LE_REFL; content] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `(if b then c else d) = (if ~b then d else c)`] THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY] THEN COND_CASES_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_LE_TRANS]] THEN
  MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let CONTENT_LT_NZ = prove
 (`!a b. &0 < content(interval[a,b]) <=> ~(content(interval[a,b]) = &0)`,
  REWRITE_TAC[CONTENT_POS_LT_EQ; CONTENT_EQ_0] THEN MESON_TAC[REAL_NOT_LE]);;

let INTERVAL_BOUNDS_NULL_1 = prove
 (`!a b:real^1.
        content(interval[a,b]) = &0
        ==> interval_upperbound(interval[a,b]) =
            interval_lowerbound(interval[a,b])`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `interval[a:real^1,b] = {}` THENL
   [ASM_REWRITE_TAC[interval_upperbound; interval_lowerbound] THEN
    REWRITE_TAC[sup; inf; NOT_IN_EMPTY; EMPTY_GSPEC] THEN DISCH_TAC THEN
    REPLICATE_TAC 2 (AP_TERM_TAC THEN ABS_TAC) THEN
    MESON_TAC[REAL_ARITH `~(x <= x - &1) /\ ~(x + &1 <= x)`];
    RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
    ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1] THEN
    REWRITE_TAC[CONTENT_EQ_0_1; GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC]);;

let INTERVAL_BOUNDS_EMPTY_1 = prove
 (`interval_upperbound({}:real^1->bool) =
   interval_lowerbound({}:real^1->bool)`,
  MESON_TAC[INTERVAL_BOUNDS_NULL_1; CONTENT_EMPTY; EMPTY_AS_INTERVAL]);;

let CONTENT_PASTECART = prove
 (`!a b:real^M c d:real^N.
        content(interval[pastecart a c,pastecart b d]) =
        content(interval[a,b]) * content(interval[c,d])`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CONTENT_CLOSED_INTERVAL_CASES; LAMBDA_BETA] THEN
  MATCH_MP_TAC(MESON[REAL_MUL_LZERO; REAL_MUL_RZERO]
   `(p <=> p1 /\ p2) /\ z = x * y
    ==> (if p then z else &0) =
        (if p1 then x else &0) * (if p2 then y else &0)`) THEN
  CONJ_TAC THENL
   [EQ_TAC THEN DISCH_TAC THEN TRY CONJ_TAC THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      ASM_SIMP_TAC[pastecart; LAMBDA_BETA; DIMINDEX_FINITE_SUM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `i + dimindex(:M)`) THEN
      ASM_SIMP_TAC[pastecart; LAMBDA_BETA; DIMINDEX_FINITE_SUM] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ADD_SUB]] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_SUM]) THEN
      ASM_CASES_TAC `i <= dimindex(:M)` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o CONJUNCT1);
        FIRST_X_ASSUM(MP_TAC o SPEC `i - dimindex(:M)` o CONJUNCT2)] THEN
      ASM_SIMP_TAC[pastecart; LAMBDA_BETA; DIMINDEX_FINITE_SUM;
                   ARITH_RULE `i:num <= m ==> i <= m + n`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    SIMP_TAC[DIMINDEX_FINITE_SUM; ARITH_RULE `1 <= n + 1`;
             PRODUCT_ADD_SPLIT] THEN
    BINOP_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[PRODUCT_OFFSET]] THEN
    MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
    SIMP_TAC[pastecart; LAMBDA_BETA; DIMINDEX_FINITE_SUM; ADD_SUB;
             ARITH_RULE `i:num <= m ==> i <= m + n`;
             ARITH_RULE `i:num <= n ==> i + m <= m + n`] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The notion of a gauge --- simply an open set containing the point.        *)
(* ------------------------------------------------------------------------- *)

let gauge = new_definition
  `gauge d <=> !x. x IN d(x) /\ open(d(x))`;;

let GAUGE_BALL_DEPENDENT = prove
 (`!e. (!x. &0 < e(x)) ==> gauge(\x. ball(x,e(x)))`,
  SIMP_TAC[gauge; OPEN_BALL; IN_BALL; DIST_REFL]);;

let GAUGE_BALL = prove
 (`!e. &0 < e ==> gauge (\x. ball(x,e))`,
  SIMP_TAC[gauge; OPEN_BALL; IN_BALL; DIST_REFL]);;

let GAUGE_TRIVIAL = prove
 (`gauge (\x. ball(x,&1))`,
  SIMP_TAC[GAUGE_BALL; REAL_LT_01]);;

let GAUGE_INTER = prove
 (`!d1 d2. gauge d1 /\ gauge d2 ==> gauge (\x. (d1 x) INTER (d2 x))`,
  SIMP_TAC[gauge; IN_INTER; OPEN_INTER]);;

let GAUGE_INTERS = prove
 (`!s. FINITE s /\ (!d. d IN s ==> gauge (f d))
       ==> gauge(\x. INTERS {f d x | d IN s})`,
  REWRITE_TAC[gauge; IN_INTERS] THEN
  REWRITE_TAC[SET_RULE `{f d x | d IN s} = IMAGE (\d. f d x) s`] THEN
  SIMP_TAC[FORALL_IN_IMAGE; OPEN_INTERS; FINITE_IMAGE]);;

let GAUGE_EXISTENCE_LEMMA = prove
 (`(!x. ?d. p x ==> &0 < d /\ q d x) <=>
   (!x. ?d. &0 < d /\ (p x ==> q d x))`,
  MESON_TAC[REAL_LT_01]);;

(* ------------------------------------------------------------------------- *)
(* Divisions.                                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("division_of",(12,"right"));;

let division_of = new_definition
 `s division_of i <=>
        FINITE s /\
        (!k. k IN s
             ==> k SUBSET i /\ ~(k = {}) /\ ?a b. k = interval[a,b]) /\
        (!k1 k2. k1 IN s /\ k2 IN s /\ ~(k1 = k2)
                 ==> interior(k1) INTER interior(k2) = {}) /\
        (UNIONS s = i)`;;

let DIVISION_OF = prove
 (`s division_of i <=>
        FINITE s /\
        (!k. k IN s ==> ~(k = {}) /\ ?a b. k = interval[a,b]) /\
        (!k1 k2. k1 IN s /\ k2 IN s /\ ~(k1 = k2)
                 ==> interior(k1) INTER interior(k2) = {}) /\
        UNIONS s = i`,
  REWRITE_TAC[division_of] THEN SET_TAC[]);;

let DIVISION_OF_FINITE = prove
 (`!s i. s division_of i ==> FINITE s`,
  MESON_TAC[division_of]);;

let DIVISION_OF_SELF = prove
 (`!a b. ~(interval[a,b] = {}) ==> {interval[a,b]} division_of interval[a,b]`,
  REWRITE_TAC[division_of; FINITE_INSERT; FINITE_RULES; IN_SING; UNIONS_1] THEN
  MESON_TAC[SUBSET_REFL]);;

let DIVISION_OF_TRIVIAL = prove
 (`!s. s division_of {} <=> s = {}`,
  REWRITE_TAC[division_of; SUBSET_EMPTY; CONJ_ASSOC] THEN
  REWRITE_TAC[TAUT `~(p /\ ~p)`; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
  REWRITE_TAC[AC CONJ_ACI `((a /\ b) /\ c) /\ d <=> b /\ a /\ c /\ d`] THEN
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(a ==> b) ==> (a /\ b <=> a)`) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FINITE_RULES; UNIONS_0; NOT_IN_EMPTY]);;

let EMPTY_DIVISION_OF = prove
 (`!s. {} division_of s <=> s = {}`,
  REWRITE_TAC[division_of; UNIONS_0; FINITE_EMPTY; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let DIVISION_OF_SING = prove
 (`!s a. s division_of interval[a,a] <=> s = {interval[a,a]}`,
  let lemma = prove
   (`s SUBSET {{a}} /\ p /\ UNIONS s = {a} <=> s = {{a}} /\ p`,
    EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SET_RULE `UNIONS {a} = a`] THEN ASM SET_TAC[]) in
  REWRITE_TAC[division_of; INTERVAL_SING] THEN
  REWRITE_TAC[SET_RULE `k SUBSET {a} /\ ~(k = {}) /\ p <=> k = {a} /\ p`] THEN
  REWRITE_TAC[GSYM INTERVAL_SING] THEN
  REWRITE_TAC[MESON[] `(k = interval[a,b] /\ ?c d. k = interval[c,d]) <=>
                       (k = interval[a,b])`] THEN
  REWRITE_TAC[SET_RULE `(!k. k IN s ==> k = a) <=> s SUBSET {a}`] THEN
  REWRITE_TAC[INTERVAL_SING; lemma] THEN MESON_TAC[FINITE_RULES; IN_SING]);;

let ELEMENTARY_EMPTY = prove
 (`?p. p division_of {}`,
  REWRITE_TAC[DIVISION_OF_TRIVIAL; EXISTS_REFL]);;

let ELEMENTARY_INTERVAL = prove
 (`!a b. ?p. p division_of interval[a,b]`,
  MESON_TAC[DIVISION_OF_TRIVIAL; DIVISION_OF_SELF]);;

let DIVISION_CONTAINS = prove
 (`!s i. s division_of i ==> !x. x IN i ==> ?k. x IN k /\ k IN s`,
  REWRITE_TAC[division_of; EXTENSION; IN_UNIONS] THEN MESON_TAC[]);;

let FORALL_IN_DIVISION = prove
 (`!P d i. d division_of i
           ==> ((!x. x IN d ==> P x) <=>
               (!a b. interval[a,b] IN d ==> P(interval[a,b])))`,
  REWRITE_TAC[division_of] THEN MESON_TAC[]);;

let FORALL_IN_DIVISION_NONEMPTY = prove
 (`!P d i.
         d division_of i
         ==> ((!x. x IN d ==> P x) <=>
              (!a b. interval [a,b] IN d /\ ~(interval[a,b] = {})
                     ==> P (interval [a,b])))`,
  REWRITE_TAC[division_of] THEN MESON_TAC[]);;

let DIVISION_OF_SUBSET = prove
 (`!p q:(real^N->bool)->bool.
        p division_of (UNIONS p) /\ q SUBSET p ==> q division_of (UNIONS q)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[division_of] THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ASM SET_TAC[]; ASM SET_TAC[]]);;

let DIVISION_OF_UNION_SELF = prove
 (`!p s. p division_of s ==> p division_of (UNIONS p)`,
  REWRITE_TAC[division_of] THEN MESON_TAC[]);;

let DIVISION_OF_CONTENT_0 = prove
 (`!a b d. content(interval[a,b]) = &0 /\ d division_of interval[a,b]
           ==> !k. k IN d ==> content k = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; CONTENT_POS_LE] THEN
  ASM_MESON_TAC[CONTENT_SUBSET; division_of]);;

let DIVISION_INTER = prove
 (`!s1 s2:real^N->bool p1 p2.
        p1 division_of s1 /\
        p2 division_of s2
        ==> {k1 INTER k2 | k1 IN p1 /\ k2 IN p2 /\ ~(k1 INTER k2 = {})}
            division_of (s1 INTER s2)`,
  let lemma = prove
   (`{k1 INTER k2 | k1 IN p1 /\ k2 IN p2 /\ ~(k1 INTER k2 = {})} =
        {s | s IN IMAGE (\(k1,k2). k1 INTER k2) (p1 CROSS p2) /\
             ~(s = {})}`,
    REWRITE_TAC[EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM; IN_CROSS] THEN
    MESON_TAC[]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_OF] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[lemma; FINITE_RESTRICT; FINITE_CROSS; FINITE_IMAGE] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[INTER_INTERVAL];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `(interior x1 INTER interior x2 = {} \/
       interior y1 INTER interior y2 = {}) /\
      interior(x1 INTER y1) SUBSET interior(x1) /\
      interior(x1 INTER y1) SUBSET interior(y1) /\
      interior(x2 INTER y2) SUBSET interior(x2) /\
      interior(x2 INTER y2) SUBSET interior(y2)
      ==> interior(x1 INTER y1) INTER interior(x2 INTER y2) = {}`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[];
    REWRITE_TAC[SET_RULE `UNIONS {x | x IN s /\ ~(x = {})} = UNIONS s`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS; IN_INTER] THEN
    MESON_TAC[IN_INTER]]);;

let DIVISION_INTER_1 = prove
 (`!d i a b:real^N.
        d division_of i /\ interval[a,b] SUBSET i
        ==> { interval[a,b] INTER k | k |
                 k IN d /\ ~(interval[a,b] INTER k = {}) }
            division_of interval[a,b]`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval[a:real^N,b] = {}` THEN
  ASM_REWRITE_TAC[INTER_EMPTY; SET_RULE `{{} | F} = {}`;
                  DIVISION_OF_TRIVIAL] THEN
  MP_TAC(ISPECL [`interval[a:real^N,b]`; `i:real^N->bool`;
                 `{interval[a:real^N,b]}`; `d:(real^N->bool)->bool`]
                DIVISION_INTER) THEN
  ASM_SIMP_TAC[DIVISION_OF_SELF; SET_RULE `s SUBSET t ==> s INTER t = s`] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let ELEMENTARY_INTER = prove
 (`!s t. (?p. p division_of s) /\ (?p. p division_of t)
         ==> ?p. p division_of (s INTER t)`,
  MESON_TAC[DIVISION_INTER]);;

let ELEMENTARY_INTERS = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\ ~(f = {}) /\
        (!s. s IN f ==> ?p. p division_of s)
        ==> ?p. p division_of (INTERS f)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INTERS_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s:(real^N->bool)->bool`] THEN
  ASM_CASES_TAC `s:(real^N->bool)->bool = {}` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[INTERS_0; INTER_UNIV; IN_SING] THEN MESON_TAC[];
    REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ELEMENTARY_INTER THEN ASM_MESON_TAC[]]);;

let DIVISION_DISJOINT_UNION = prove
 (`!s1 s2:real^N->bool p1 p2.
        p1 division_of s1 /\
        p2 division_of s2 /\
        interior s1 INTER interior s2 = {}
        ==> (p1 UNION p2) division_of (s1 UNION s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[division_of] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FINITE_UNION; IN_UNION; EXISTS_OR_THM; SET_RULE
   `UNIONS {x | P x \/ Q x} = UNIONS {x | P x} UNION UNIONS {x | Q x}`] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REPEAT STRIP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC; ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC(SET_RULE
   `!s' t'. s SUBSET s' /\ t SUBSET t' /\ s' INTER t' = {}
            ==> s INTER t = {}`)
  THENL
   [MAP_EVERY EXISTS_TAC
     [`interior s1:real^N->bool`; `interior s2:real^N->bool`];
    MAP_EVERY EXISTS_TAC
     [`interior s2:real^N->bool`; `interior s1:real^N->bool`]] THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SUBSET_INTERIOR) THEN
  ASM SET_TAC[]);;

let PARTIAL_DIVISION_EXTEND_1 = prove
 (`!a b c d:real^N.
        interval[c,d] SUBSET interval[a,b] /\ ~(interval[c,d] = {})
        ==> ?p. p division_of interval[a,b] /\
                interval[c,d] IN p`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [INTERVAL_NE_EMPTY])) THEN
  EXISTS_TAC
   `{interval
      [(lambda i. if i < l then (c:real^N)$i else (a:real^N)$i):real^N,
       (lambda i. if i < l then d$i else if i = l then c$l else b$i)] |
       l IN 1..(dimindex(:N)+1)} UNION
    {interval
      [(lambda i. if i < l then c$i else if i = l then d$l else a$i),
       (lambda i. if i < l then (d:real^N)$i else (b:real^N)$i):real^N] |
       l IN 1..(dimindex(:N)+1)}` THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `dimindex(:N)+1` THEN
    REWRITE_TAC[IN_NUMSEG; LE_REFL; ARITH_RULE `1 <= n + 1`] THEN
    AP_TERM_TAC THEN SIMP_TAC[CONS_11; PAIR_EQ; CART_EQ; LAMBDA_BETA] THEN
    SIMP_TAC[ARITH_RULE `i <= n ==> i < n + 1`];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_INTERVAL]) THEN
  ASM_REWRITE_TAC[DIVISION_OF] THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE] THEN
    SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_NUMSEG];
    REWRITE_TAC[IN_UNION; TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_AND_THM; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[IN_NUMSEG; INTERVAL_NE_EMPTY; LAMBDA_BETA] THEN
    CONJ_TAC THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    (CONJ_TAC THENL [ALL_TAC; MESON_TAC[]]) THEN
    REPEAT STRIP_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    REWRITE_TAC[IN_UNION; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[SET_RULE
      `(!y. y IN {f x | x IN s} \/ y IN {g x | x IN s} ==> P y) <=>
       (!x. x IN s ==> P(f x) /\ P(g x))`] THEN
    REWRITE_TAC[AND_FORALL_THM; IN_NUMSEG] THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
    MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC[TAUT `a ==> b ==> c <=> b ==> a ==> c`] THEN
      REWRITE_TAC[INTER_ACI; CONJ_ACI] THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`l:num`; `m:num`] THEN
    DISCH_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[TAUT `(~p ==> q) <=> (~q ==> p)`] THEN
     REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
    REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x. ~(x IN s /\ x IN t)`] THEN
    ASM_SIMP_TAC[IN_NUMSEG; INTERVAL_NE_EMPTY; LAMBDA_BETA; IN_INTERVAL;
                 INTERIOR_CLOSED_INTERVAL] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
    REWRITE_TAC[NOT_FORALL_THM] THEN REPEAT CONJ_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (LABEL_TAC "*")) THEN
    AP_TERM_TAC THEN SIMP_TAC[CONS_11; PAIR_EQ; CART_EQ; LAMBDA_BETA] THENL
     (let tac1 =
        UNDISCH_TAC `l:num <= m` THEN GEN_REWRITE_TAC LAND_CONV [LE_LT] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REMOVE_THEN "*" (MP_TAC o SPEC `l:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[LT_REFL] THEN REAL_ARITH_TAC
      and tac2 =
        UNDISCH_TAC `l:num <= m` THEN GEN_REWRITE_TAC LAND_CONV [LE_LT] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
         [REMOVE_THEN "*" (MP_TAC o SPEC `l:num`) THEN ANTS_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_REWRITE_TAC[LT_REFL] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
        CONJ_TAC THEN X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i:num = l` THEN
        ASM_REWRITE_TAC[LT_REFL] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
        DISCH_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `l:num`)) THEN
        ASM_REWRITE_TAC[LT_REFL] THEN REAL_ARITH_TAC in
      [tac1; tac2; tac2; tac1]);
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[IMP_CONJ; SUBSET; FORALL_IN_UNIONS; SIMPLE_IMAGE] THEN
      REWRITE_TAC[IN_UNIONS; IN_INSERT; IN_UNION; FORALL_IN_IMAGE;
        RIGHT_FORALL_IMP_THM; FORALL_AND_THM;
        TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
      ASM_SIMP_TAC[IN_INTERVAL; IN_NUMSEG; LAMBDA_BETA] THEN
      REPEAT CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      ASM_MESON_TAC[REAL_LE_TRANS];
      ALL_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `a IN s ==> (c DIFF a) SUBSET UNIONS s ==> c SUBSET UNIONS s`)) THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_INTERVAL] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC[TAUT `a ==> ~(b /\ ~c) <=> a /\ b ==> c`] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS; SIMPLE_IMAGE; EXISTS_IN_IMAGE; IN_UNION;
                EXISTS_OR_THM; RIGHT_OR_DISTRIB] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN EXISTS_TAC `l:num` THEN
    ASM_SIMP_TAC[IN_NUMSEG; IN_INTERVAL; LAMBDA_BETA;
                 ARITH_RULE `x <= n ==> x <= n + 1`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
    MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[REAL_NOT_LE] THEN
    REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]]);;

let PARTIAL_DIVISION_EXTEND_INTERVAL = prove
 (`!p a b:real^N.
        p division_of (UNIONS p) /\ (UNIONS p) SUBSET interval[a,b]
        ==> ?q. p SUBSET q /\ q division_of interval[a,b]`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET] THENL
   [MESON_TAC[ELEMENTARY_INTERVAL]; STRIP_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  SUBGOAL_THEN `!k:real^N->bool. k IN p ==> ?q. q division_of interval[a,b] /\
                                                k IN q`
  MP_TAC THENL
   [X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MP_TAC o SPEC `k:real^N->bool` o el 1 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC PARTIAL_DIVISION_EXTEND_1 THEN ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:(real^N->bool)->(real^N->bool)->bool`) THEN
  SUBGOAL_THEN
   `?d. d division_of INTERS {UNIONS(q i DELETE i) | (i:real^N->bool) IN p}`
  MP_TAC THENL
   [MATCH_MP_TAC ELEMENTARY_INTERS THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[IMAGE_EQ_EMPTY; FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `k:real^N->bool` THEN
    DISCH_TAC THEN EXISTS_TAC `(q k) DELETE (k:real^N->bool)` THEN
    MATCH_MP_TAC DIVISION_OF_SUBSET THEN
    EXISTS_TAC `(q:(real^N->bool)->(real^N->bool)->bool) k` THEN
    REWRITE_TAC[DELETE_SUBSET] THEN ASM_MESON_TAC[division_of];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `d:(real^N->bool)->bool`) THEN
  EXISTS_TAC `(d UNION p):(real^N->bool)->bool` THEN
  REWRITE_TAC[SUBSET_UNION] THEN
  SUBGOAL_THEN `interval[a:real^N,b] =
                INTERS {UNIONS (q i DELETE i) | i IN p} UNION
                UNIONS p`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC(SET_RULE
     `~(s = {}) /\
      (!i. i IN s ==> f i UNION i = t)
     ==> t = INTERS (IMAGE f s) UNION (UNIONS s)`) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `UNIONS k = s /\ i IN k ==> UNIONS (k DELETE i) UNION i = s`) THEN
    ASM_MESON_TAC[division_of];
    ALL_TAC] THEN
  MATCH_MP_TAC DIVISION_DISJOINT_UNION THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `!s. u SUBSET s /\ s INTER t = {} ==> u INTER t = {}`) THEN
  EXISTS_TAC `interior(UNIONS(q k DELETE (k:real^N->bool)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN
    MATCH_MP_TAC(SET_RULE `x IN s ==> INTERS s SUBSET x`) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN
  MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
  REWRITE_TAC[OPEN_INTERIOR; FINITE_DELETE; IN_DELETE] THEN
  ASM_MESON_TAC[division_of]);;

let ELEMENTARY_BOUNDED = prove
 (`!s. (?p. p division_of s) ==> bounded s`,
  REWRITE_TAC[division_of] THEN
  ASM_MESON_TAC[BOUNDED_UNIONS; BOUNDED_INTERVAL]);;

let ELEMENTARY_SUBSET_INTERVAL = prove
 (`!s. (?p. p division_of s) ==> ?a b. s SUBSET interval[a,b]`,
  MESON_TAC[ELEMENTARY_BOUNDED; BOUNDED_SUBSET_CLOSED_INTERVAL]);;

let DIVISION_UNION_INTERVALS_EXISTS = prove
 (`!a b c d:real^N.
        ~(interval[a,b] = {})
        ==> ?p. (interval[a,b] INSERT p) division_of
                (interval[a,b] UNION interval[c,d])`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval[c:real^N,d] = {}` THENL
   [ASM_REWRITE_TAC[UNION_EMPTY] THEN ASM_MESON_TAC[DIVISION_OF_SELF];
    ALL_TAC] THEN
  ASM_CASES_TAC `interval[a:real^N,b] INTER interval[c,d] = {}` THENL
   [EXISTS_TAC `{interval[c:real^N,d]}` THEN
    ONCE_REWRITE_TAC[SET_RULE `{a,b} = {a} UNION {b}`] THEN
    MATCH_MP_TAC DIVISION_DISJOINT_UNION THEN
    ASM_SIMP_TAC[DIVISION_OF_SELF] THEN
    MATCH_MP_TAC(SET_RULE
     `interior s SUBSET s /\ interior t SUBSET t /\ s INTER t = {}
      ==> interior s INTER interior t = {}`) THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?u v:real^N. interval[a,b] INTER interval[c,d] = interval[u,v]`
  STRIP_ASSUME_TAC THENL [MESON_TAC[INTER_INTERVAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^N`; `d:real^N`; `u:real^N`; `v:real^N`]
                PARTIAL_DIVISION_EXTEND_1) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[INTER_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p DELETE interval[u:real^N,v]` THEN
  SUBGOAL_THEN `interval[a:real^N,b] UNION interval[c,d] =
                interval[a,b] UNION UNIONS(p DELETE interval[u,v])`
  SUBST1_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o last o CONJUNCTS o
                GEN_REWRITE_RULE I [division_of]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SET_RULE `x INSERT s = {x} UNION s`] THEN
  MATCH_MP_TAC DIVISION_DISJOINT_UNION THEN
  ASM_SIMP_TAC[DIVISION_OF_SELF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIVISION_OF_SUBSET THEN
    EXISTS_TAC `p:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[DIVISION_OF_UNION_SELF; DELETE_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INTERIOR_INTER] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `interior(interval[u:real^N,v] INTER
              UNIONS (p DELETE interval[u,v]))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
     `!cd. p SUBSET cd /\ uv = ab INTER cd
           ==> (ab INTER p = uv INTER p)`) THEN
    EXISTS_TAC `interval[c:real^N,d]` THEN
    ASM_REWRITE_TAC[UNIONS_SUBSET; IN_DELETE] THEN
    ASM_MESON_TAC[division_of];
    REWRITE_TAC[INTERIOR_INTER] THEN
    MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
    REWRITE_TAC[IN_DELETE; OPEN_INTERIOR; FINITE_DELETE] THEN
    ASM_MESON_TAC[division_of]]);;

let DIVISION_OF_UNIONS = prove
 (`!f. FINITE f /\
       (!p. p IN f ==> p division_of (UNIONS p)) /\
       (!k1 k2. k1 IN UNIONS f /\ k2 IN UNIONS f /\ ~(k1 = k2)
                ==> interior k1 INTER interior k2 = {})
       ==> (UNIONS f) division_of UNIONS(UNIONS f)`,
  REWRITE_TAC[division_of] THEN
  SIMP_TAC[FINITE_UNIONS] THEN REWRITE_TAC[FORALL_IN_UNIONS] THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o el 1 o CONJUNCTS) THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN SET_TAC[]);;

let ELEMENTARY_UNION_INTERVAL_STRONG = prove
 (`!p a b:real^N.
        p division_of (UNIONS p)
        ==> ?q. p SUBSET q /\ q division_of (interval[a,b] UNION UNIONS p)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[UNIONS_0; UNION_EMPTY; EMPTY_SUBSET] THEN
    MESON_TAC[ELEMENTARY_INTERVAL];
    ALL_TAC] THEN
  ASM_CASES_TAC `interval[a:real^N,b] = {}` THEN
  ASM_REWRITE_TAC[UNION_EMPTY] THENL [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  ASM_CASES_TAC `interior(interval[a:real^N,b]) = {}` THENL
   [EXISTS_TAC `interval[a:real^N,b] INSERT p` THEN
    REWRITE_TAC[division_of] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    SIMP_TAC[FINITE_INSERT; UNIONS_INSERT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `interval[a:real^N,b] SUBSET UNIONS p` THENL
   [ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s UNION t = t`] THEN
    ASM_MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k:real^N->bool. k IN p
                     ==> ?q. ~(k IN q) /\ ~(q = {}) /\
                             (k INSERT q) division_of (interval[a,b] UNION k)`
  MP_TAC THENL
   [X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MP_TAC o SPEC `k:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:real^N`; `d:real^N`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    ONCE_REWRITE_TAC[UNION_COMM] THEN
    MP_TAC(ISPECL [`c:real^N`; `d:real^N`; `a:real^N`; `b:real^N`]
        DIVISION_UNION_INTERVALS_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `q:(real^N->bool)->bool`) THEN
    EXISTS_TAC `q DELETE interval[c:real^N,d]` THEN
    ASM_REWRITE_TAC[IN_DELETE; SET_RULE
     `x INSERT (q DELETE x) = x INSERT q`] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `(interval[c:real^N,d] INSERT q) division_of
                 (interval [c,d] UNION interval [a,b])` THEN
    ASM_SIMP_TAC[SET_RULE `s DELETE x = {} ==> x INSERT s = {x}`] THEN
    REWRITE_TAC[division_of; UNIONS_1] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:(real^N->bool)->(real^N->bool)->bool`) THEN
  MP_TAC(ISPEC `IMAGE (UNIONS o (q:(real^N->bool)->(real^N->bool)->bool)) p`
    ELEMENTARY_INTERS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `(q:(real^N->bool)->(real^N->bool)->bool) k` THEN
    REWRITE_TAC[o_THM] THEN MATCH_MP_TAC DIVISION_OF_SUBSET THEN
    EXISTS_TAC `(k:real^N->bool) INSERT q k` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_UNION_SELF]; SET_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `r:(real^N->bool)->bool`)] THEN
  EXISTS_TAC `p UNION r:(real^N->bool)->bool` THEN SIMP_TAC[SUBSET_UNION] THEN
  SUBGOAL_THEN
   `interval[a:real^N,b] UNION UNIONS p =
    UNIONS p UNION INTERS(IMAGE (UNIONS o q) p)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[IN_UNION] THEN
    ASM_CASES_TAC `(y:real^N) IN UNIONS p` THEN ASM_REWRITE_TAC[IN_INTERS] THEN
    REWRITE_TAC[FORALL_IN_UNIONS; IMP_CONJ; FORALL_IN_IMAGE;
                RIGHT_FORALL_IMP_THM] THEN
    SUBGOAL_THEN
     `!k. k IN p ==> UNIONS(k INSERT q k) = interval[a:real^N,b] UNION k`
    MP_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    REWRITE_TAC[UNIONS_INSERT; o_THM] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM; IN_UNION] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    UNDISCH_TAC `~((y:real^N) IN UNIONS p)` THEN
    SIMP_TAC[IN_UNIONS; NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
    ASM_CASES_TAC `(y:real^N) IN interval[a,b]` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIVISION_DISJOINT_UNION THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
  MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INTERIOR_FINITE_INTERS; FINITE_IMAGE] THEN
  MATCH_MP_TAC(SET_RULE `(?x. x IN p /\ f x INTER s = {})
                        ==> INTERS (IMAGE f p) INTER s = {}`) THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; o_THM] THEN EXISTS_TAC `k:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN
  MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[division_of; FINITE_INSERT; IN_INSERT];
    ASM_MESON_TAC[division_of; FINITE_INSERT; IN_INSERT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool`) THEN
  ASM_REWRITE_TAC[division_of; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let ELEMENTARY_UNION_INTERVAL = prove
 (`!p a b:real^N.
        p division_of (UNIONS p)
        ==> ?q. q division_of (interval[a,b] UNION UNIONS p)`,
  MESON_TAC[ELEMENTARY_UNION_INTERVAL_STRONG]);;

let ELEMENTARY_UNIONS_INTERVALS = prove
 (`!f. FINITE f /\
       (!s. s IN f ==> ?a b:real^N. s = interval[a,b])
       ==> (?p. p division_of (UNIONS f))`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; ELEMENTARY_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `p:(real^N->bool)->bool`) THEN
  SUBGOAL_THEN `UNIONS f:real^N->bool = UNIONS p` SUBST1_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  MATCH_MP_TAC ELEMENTARY_UNION_INTERVAL THEN ASM_MESON_TAC[division_of]);;

let ELEMENTARY_UNION = prove
 (`!s t:real^N->bool.
        (?p. p division_of s) /\ (?p. p division_of t)
        ==> (?p. p division_of (s UNION t))`,
  REPEAT GEN_TAC THEN DISCH_THEN
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `p1:(real^N->bool)->bool`)
                    (X_CHOOSE_TAC `p2:(real^N->bool)->bool`)) THEN
  SUBGOAL_THEN `s UNION t :real^N->bool = UNIONS p1 UNION UNIONS p2`
  SUBST1_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `UNIONS p1 UNION UNIONS p2 = UNIONS(p1 UNION p2)`] THEN
  MATCH_MP_TAC ELEMENTARY_UNIONS_INTERVALS THEN
  REWRITE_TAC[IN_UNION; FINITE_UNION] THEN
  ASM_MESON_TAC[division_of]);;

let PARTIAL_DIVISION_EXTEND = prove
 (`!p q s t:real^N->bool.
        p division_of s /\ q division_of t /\ s SUBSET t
        ==> ?r. p SUBSET r /\ r division_of t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a b:real^N. t SUBSET interval[a,b]` MP_TAC THENL
   [ASM_MESON_TAC[ELEMENTARY_SUBSET_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?r1. p SUBSET r1 /\ r1 division_of interval[a:real^N,b]`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC PARTIAL_DIVISION_EXTEND_INTERVAL THEN
    ASM_MESON_TAC[division_of; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r2:(real^N->bool)->bool.
        r2 division_of (UNIONS(r1 DIFF p)) INTER (UNIONS q)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ELEMENTARY_INTER THEN
    ASM_MESON_TAC[FINITE_DIFF; IN_DIFF; division_of;
                  ELEMENTARY_UNIONS_INTERVALS];
    ALL_TAC] THEN
  EXISTS_TAC `p UNION r2:(real^N->bool)->bool` THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `t:real^N->bool = UNIONS p UNION (UNIONS(r1 DIFF p) INTER UNIONS q)`
  SUBST1_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o last o CONJUNCTS o
                GEN_REWRITE_RULE I [division_of])) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[];
    MATCH_MP_TAC DIVISION_DISJOINT_UNION THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!t'. t SUBSET t' /\ s INTER t' = {} ==> s INTER t = {}`) THEN
    EXISTS_TAC `interior(UNIONS(r1 DIFF p)):real^N->bool` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
           REWRITE_TAC[OPEN_INTERIOR] THEN
           REPEAT(CONJ_TAC THENL
            [ASM_MESON_TAC[IN_DIFF; FINITE_DIFF; division_of]; ALL_TAC]) THEN
           REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
           ONCE_REWRITE_TAC[INTER_COMM]) THEN
    ASM_MESON_TAC[division_of; SUBSET]]);;

let INTERVAL_SUBDIVISION = prove
 (`!a b c:real^N.
        c IN interval[a,b]
        ==> IMAGE (\s. interval[(lambda i. if i IN s then c$i else a$i),
                                (lambda i. if i IN s then b$i else c$i)])
                  {s | s SUBSET 1..dimindex(:N)}
            division_of interval[a,b]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
  REWRITE_TAC[DIVISION_OF] THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_POWERSET; FINITE_NUMSEG] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; SUBSET_INTERVAL; INTERVAL_NE_EMPTY] THEN
  REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[LAMBDA_BETA] THEN ASM_MESON_TAC[REAL_LE_TRANS];
    X_GEN_TAC `s:num->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `s':num->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[SET_RULE
     `(~p ==> s INTER t = {}) <=> (!x. x IN s /\ x IN t ==> p)`] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTERVAL; AND_FORALL_THM] THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
    SIMP_TAC[LAMBDA_BETA] THEN
    ASM_CASES_TAC `s':num->bool = s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `~(s' = s) ==> ?x. x IN s' /\ ~(x IN s) \/ x IN s /\ ~(x IN s')`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; IN_NUMSEG]; REAL_ARITH_TAC]);
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
    GEN_REWRITE_TAC I [SUBSET] THENL
     [REWRITE_TAC[FORALL_IN_UNIONS] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM; GSYM SUBSET] THEN
      SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN
      ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; EXISTS_IN_GSPEC] THEN EXISTS_TAC
       `{i | i IN 1..dimindex(:N) /\ (c:real^N)$i <= (x:real^N)$i}` THEN
      CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[IN_INTERVAL]] THEN
      SIMP_TAC[LAMBDA_BETA; IN_ELIM_THM; IN_NUMSEG] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
      ASM_MESON_TAC[REAL_LE_TOTAL]]]);;

let DIVISION_OF_NONTRIVIAL = prove
 (`!s a b:real^N.
        s division_of interval[a,b] /\ ~(content(interval[a,b]) = &0)
        ==> {k | k IN s /\ ~(content k = &0)} division_of interval[a,b]`,
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `CARD(s:(real^N->bool)->bool)` THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `{k:real^N->bool | k IN s /\ ~(content k = &0)} = s` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [EXTENSION]) THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ ~b <=> a) <=> a /\ b`] THEN
  X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (k:real^N->bool)`) THEN
  ASM_SIMP_TAC[CARD_DELETE; ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM SET_TAC[]] THEN
  REWRITE_TAC[DIVISION_OF] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [division_of]) THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(k:real^N->bool) IN s`)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `d:real^N`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MATCH_MP_TAC(SET_RULE
    `UNIONS s = i /\ k SUBSET UNIONS(s DELETE k)
     ==> UNIONS(s DELETE k) = i`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[CLOSED_LIMPT; SUBSET]
   `closed s /\ (!x. x IN k ==> x limit_point_of s) ==> k SUBSET s`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    ASM_MESON_TAC[CLOSED_INTERVAL];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN REWRITE_TAC[dist] THEN
  SUBGOAL_THEN `?y:real^N. y IN UNIONS s /\ ~(y IN interval[c,d]) /\
                           ~(y = x) /\ norm(y - x) < e`
  MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`~(content(interval[a:real^N,b]) = &0)`;
    `content(interval[c:real^N,d]) = &0`] THEN
  REWRITE_TAC[CONTENT_EQ_0; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(interval[c:real^N,d] = {})` THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[REAL_NOT_LT] THEN
  ASM_SIMP_TAC[REAL_ARITH `a <= b ==> (b <= a <=> a = b)`] THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  UNDISCH_TAC `interval[c:real^N,d] SUBSET interval[a,b]` THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ASSUME `(x:real^N) IN interval[c,d]`) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `d = c ==> (c <= x /\ x <= d <=> x = c)`] THEN
  DISCH_TAC THEN
  MP_TAC(ASSUME `(x:real^N) IN interval[a,b]`) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC
   `(lambda j. if j = i then
                 if (c:real^N)$i <= ((a:real^N)$i + (b:real^N)$i) / &2
                 then c$i + min e (b$i - c$i) / &2
                 else c$i - min e (c$i - a$i) / &2
               else (x:real^N)$j):real^N` THEN
  SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; CART_EQ] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    UNDISCH_TAC `(x:real^N) IN interval[a,b]` THEN
    REWRITE_TAC[IN_INTERVAL] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[vector_norm; dot] THEN
    SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT; GSYM REAL_POW_2] THEN
    REWRITE_TAC[REAL_ARITH
     `((if p then x else y) - y) pow 2 = if p then (x - y) pow 2 else &0`] THEN
    ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG; POW_2_SQRT_ABS] THEN
    ASM_REAL_ARITH_TAC]);;

let DIVISION_OF_AFFINITY = prove
 (`!d s:real^N->bool m c.
    IMAGE (IMAGE (\x. m % x + c)) d division_of (IMAGE (\x. m % x + c) s) <=>
    if m = &0 then if s = {} then d = {}
                   else ~(d = {}) /\ !k. k IN d ==> ~(k = {})
    else d division_of s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; DIVISION_OF_TRIVIAL; IMAGE_EQ_EMPTY] THEN
    ASM_CASES_TAC `d:(real^N->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_DIVISION_OF; UNIONS_0;
                    IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
    ASM_SIMP_TAC[SET_RULE `~(s = {}) ==> IMAGE (\x. c) s = {c}`] THEN
    ASM_CASES_TAC `!k:real^N->bool. k IN d ==> ~(k = {})` THEN
    ASM_REWRITE_TAC[division_of] THENL
     [ALL_TAC;
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[IMAGE_EQ_EMPTY]] THEN
    SUBGOAL_THEN
     `IMAGE (IMAGE ((\x. c):real^N->real^N)) d = {{c}}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_IMAGE; IN_SING] THEN ASM SET_TAC[];
      SIMP_TAC[UNIONS_1; FINITE_SING; IN_SING; IMP_CONJ] THEN
      REWRITE_TAC[SUBSET_REFL; NOT_INSERT_EMPTY] THEN
      MESON_TAC[INTERVAL_SING]];
    REWRITE_TAC[division_of] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; GSYM INTERIOR_INTER] THEN
    ASM_SIMP_TAC[FINITE_IMAGE_INJ_EQ; GSYM IMAGE_UNIONS;
         VECTOR_ARITH `x + a:real^N = y + a <=> x = y`;
             VECTOR_MUL_LCANCEL;
     SET_RULE `(!x y. f x = f y <=> x = y)
               ==> (IMAGE f s SUBSET IMAGE f t <=> s SUBSET t) /\
                   (IMAGE f s = IMAGE f t <=> s = t) /\
                   (IMAGE f s INTER IMAGE f t = IMAGE f (s INTER t))`] THEN
    AP_TERM_TAC THEN BINOP_TAC THENL
     [AP_TERM_TAC THEN ABS_TAC THEN REPLICATE_TAC 3 AP_TERM_TAC THEN
      EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[IMAGE_AFFINITY_INTERVAL] THENL [ALL_TAC; MESON_TAC[]] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM
       `IMAGE (\x:real^N. inv m % x + --(inv m % c))`) THEN
      ASM_SIMP_TAC[GSYM IMAGE_o; AFFINITY_INVERSES] THEN
      ASM_REWRITE_TAC[IMAGE_I; IMAGE_AFFINITY_INTERVAL] THEN MESON_TAC[];
      SUBGOAL_THEN `(\x:real^N. m % x + c) = (\x. c + x) o (\x. m % x)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN VECTOR_ARITH_TAC;
        REWRITE_TAC[IMAGE_o; INTERIOR_TRANSLATION] THEN
        ASM_SIMP_TAC[INTERIOR_INJECTIVE_LINEAR_IMAGE; LINEAR_SCALING;
                     VECTOR_MUL_LCANCEL; IMAGE_EQ_EMPTY]]]]);;

let DIVISION_OF_TRANSLATION = prove
 (`!d s:real^N->bool.
        IMAGE (IMAGE (\x. a + x)) d division_of (IMAGE (\x. a + x) s) <=>
        d division_of s`,
  ONCE_REWRITE_TAC[VECTOR_ARITH `a + x:real^N = &1 % x + a`] THEN
  REWRITE_TAC[DIVISION_OF_AFFINITY] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let DIVISION_OF_REFLECT = prove
 (`!d s:real^N->bool.
        IMAGE (IMAGE (--)) d division_of IMAGE (--) s <=>
        d division_of s`,
  REPEAT GEN_TAC THEN SUBGOAL_THEN `(--) = \x:real^N. --(&1) % x + vec 0`
  SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
   REWRITE_TAC[DIVISION_OF_AFFINITY] THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let ELEMENTARY_COMPACT = prove
 (`!s. (?d. d division_of s) ==> compact s`,
  REWRITE_TAC[division_of] THEN
  MESON_TAC[COMPACT_UNIONS; COMPACT_INTERVAL]);;

let OPEN_COUNTABLE_LIMIT_ELEMENTARY = prove
 (`!s:real^N->bool.
        open s
        ==> ?f. (!n. ?d. d division_of f n) /\
                (!n. f n SUBSET f(SUC n)) /\
                UNIONS {f n | n IN (:num)} = s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [EXISTS_TAC `(\n. {}):num->real^N->bool` THEN
    REWRITE_TAC[ELEMENTARY_EMPTY; EMPTY_SUBSET; UNIONS_GSPEC] THEN
    ASM SET_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_COUNTABLE_UNION_CLOSED_INTERVALS) THEN
    DISCH_THEN(X_CHOOSE_THEN `D:(real^N->bool)->bool` MP_TAC) THEN
    ASM_CASES_TAC `D:(real^N->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[UNIONS_0] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)] THEN
  MP_TAC(ISPEC `D:(real^N->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:num->real^N->bool` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN STRIP_TAC THEN
  EXISTS_TAC `\n. UNIONS {(f:num->real^N->bool) m | m <= n}` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC ELEMENTARY_UNIONS_INTERVALS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LE] THEN ASM SET_TAC[];
    GEN_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[UNIONS_GSPEC; UNIONS_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; EXTENSION] THEN
    MESON_TAC[LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Tagged (partial) divisions.                                               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("tagged_partial_division_of",(12,"right"));;
parse_as_infix("tagged_division_of",(12,"right"));;

let tagged_partial_division_of = new_definition
  `s tagged_partial_division_of i <=>
        FINITE s /\
        (!x k. (x,k) IN s
               ==> x IN k /\ k SUBSET i /\ ?a b. k = interval[a,b]) /\
        (!x1 k1 x2 k2. (x1,k1) IN s /\ (x2,k2) IN s /\ ~((x1,k1) = (x2,k2))
                       ==> (interior(k1) INTER interior(k2) = {}))`;;

let tagged_division_of = new_definition
  `s tagged_division_of i <=>
        s tagged_partial_division_of i /\ (UNIONS {k | ?x. (x,k) IN s} = i)`;;

let TAGGED_DIVISION_OF_FINITE = prove
 (`!s i. s tagged_division_of i ==> FINITE s`,
  SIMP_TAC[tagged_division_of; tagged_partial_division_of]);;

let TAGGED_DIVISION_OF = prove
 (`s tagged_division_of i <=>
        FINITE s /\
        (!x k. (x,k) IN s
               ==> x IN k /\ k SUBSET i /\ ?a b. k = interval[a,b]) /\
        (!x1 k1 x2 k2. (x1,k1) IN s /\ (x2,k2) IN s /\ ~((x1,k1) = (x2,k2))
                       ==> (interior(k1) INTER interior(k2) = {})) /\
        (UNIONS {k | ?x. (x,k) IN s} = i)`,
  REWRITE_TAC[tagged_division_of; tagged_partial_division_of; CONJ_ASSOC]);;

let DIVISION_OF_TAGGED_DIVISION = prove
 (`!s i. s tagged_division_of i ==> (IMAGE SND s) division_of i`,
  REWRITE_TAC[TAGGED_DIVISION_OF; division_of] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; FORALL_PAIR_THM; PAIR_EQ] THEN
  REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_UNIONS] THEN
    REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN MESON_TAC[]]);;

let PARTIAL_DIVISION_OF_TAGGED_DIVISION = prove
 (`!s i. s tagged_partial_division_of i
         ==> (IMAGE SND s) division_of UNIONS(IMAGE SND s)`,
  REWRITE_TAC[tagged_partial_division_of; division_of] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; DE_MORGAN_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_IMAGE];
    ALL_TAC;
    ASM_MESON_TAC[]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[MEMBER_NOT_EMPTY]] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE; EXISTS_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV UNWIND_CONV) THEN ASM SET_TAC[]);;

let TAGGED_PARTIAL_DIVISION_SUBSET = prove
 (`!s t i. s tagged_partial_division_of i /\ t SUBSET s
           ==> t tagged_partial_division_of i`,
  REWRITE_TAC[tagged_partial_division_of] THEN
  MESON_TAC[FINITE_SUBSET; SUBSET]);;

let VSUM_OVER_TAGGED_PARTIAL_DIVISION_LEMMA = prove
 (`!d:(real^M->bool)->real^N p i.
        p tagged_partial_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = vec 0)
        ==> vsum p (\(x,k). d k) = vsum (IMAGE SND p) d`,
  REWRITE_TAC[CONTENT_EQ_0_INTERIOR] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\(x:real^M,k:real^M->bool). d k:real^N) = d o SND`
  SUBST1_TAC THENL [SIMP_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_IMAGE_NONZERO THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [tagged_partial_division_of]) THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:real^M->bool` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:real^M` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k':real^M->bool` THEN
  ASM_CASES_TAC `k':real^M->bool = k` THEN
  ASM_REWRITE_TAC[PAIR_EQ; INTER_ACI] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[]);;

let VSUM_OVER_TAGGED_DIVISION_LEMMA = prove
 (`!d:(real^M->bool)->real^N p i.
        p tagged_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = vec 0)
        ==> vsum p (\(x,k). d k) = vsum (IMAGE SND p) d`,
  REWRITE_TAC[tagged_division_of] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VSUM_OVER_TAGGED_PARTIAL_DIVISION_LEMMA THEN
  EXISTS_TAC `i:real^M->bool` THEN ASM_REWRITE_TAC[]);;

let SUM_OVER_TAGGED_PARTIAL_DIVISION_LEMMA = prove
 (`!d:(real^N->bool)->real p i.
        p tagged_partial_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = &0)
        ==> sum p (\(x,k). d k) = sum (IMAGE SND p) d`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    REWRITE_RULE[tagged_partial_division_of]) THEN
  ONCE_REWRITE_TAC[GSYM LIFT_EQ] THEN
  ASM_SIMP_TAC[LIFT_SUM; FINITE_IMAGE; o_DEF; LAMBDA_PAIR_THM] THEN
  MATCH_MP_TAC VSUM_OVER_TAGGED_PARTIAL_DIVISION_LEMMA THEN
  ASM_SIMP_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN ASM_MESON_TAC[]);;

let SUM_OVER_TAGGED_DIVISION_LEMMA = prove
 (`!d:(real^N->bool)->real p i.
        p tagged_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = &0)
        ==> sum p (\(x,k). d k) = sum (IMAGE SND p) d`,
  REWRITE_TAC[tagged_division_of] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUM_OVER_TAGGED_PARTIAL_DIVISION_LEMMA THEN
  EXISTS_TAC `i:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let TAG_IN_INTERVAL = prove
 (`!p i k. p tagged_division_of i /\ (x,k) IN p ==> x IN i`,
  REWRITE_TAC[TAGGED_DIVISION_OF] THEN SET_TAC[]);;

let TAGGED_DIVISION_OF_EMPTY = prove
 (`{} tagged_division_of {}`,
  REWRITE_TAC[tagged_division_of; tagged_partial_division_of] THEN
  REWRITE_TAC[FINITE_RULES; EXTENSION; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM]);;

let TAGGED_PARTIAL_DIVISION_OF_TRIVIAL = prove
 (`!p. p tagged_partial_division_of {} <=> p = {}`,
  REWRITE_TAC[tagged_partial_division_of; SUBSET_EMPTY; CONJ_ASSOC] THEN
  REWRITE_TAC[SET_RULE `x IN k /\ k = {} <=> F`] THEN
  REWRITE_TAC[GSYM FORALL_PAIR_THM; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
  REWRITE_TAC[AC CONJ_ACI `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(a ==> b) ==> (a /\ b <=> a)`) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FINITE_RULES; UNIONS_0; NOT_IN_EMPTY]);;

let TAGGED_DIVISION_OF_TRIVIAL = prove
 (`!p. p tagged_division_of {} <=> p = {}`,
  REWRITE_TAC[tagged_division_of; TAGGED_PARTIAL_DIVISION_OF_TRIVIAL] THEN
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(a ==> b) ==> (a /\ b <=> a)`) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NOT_IN_EMPTY] THEN SET_TAC[]);;

let TAGGED_DIVISION_OF_SELF = prove
 (`!x a b. x IN interval[a,b]
           ==> {(x,interval[a,b])} tagged_division_of interval[a,b]`,
  REWRITE_TAC[TAGGED_DIVISION_OF; FINITE_INSERT; FINITE_RULES; IN_SING] THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SUBSET_REFL; UNWIND_THM2; SET_RULE `{k | k = a} = {a}`] THEN
  REWRITE_TAC[UNIONS_1] THEN ASM_MESON_TAC[]);;

let TAGGED_DIVISION_UNION = prove
 (`!s1 s2:real^N->bool p1 p2.
        p1 tagged_division_of s1 /\
        p2 tagged_division_of s2 /\
        interior s1 INTER interior s2 = {}
        ==> (p1 UNION p2) tagged_division_of (s1 UNION s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TAGGED_DIVISION_OF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FINITE_UNION; IN_UNION; EXISTS_OR_THM; SET_RULE
   `UNIONS {x | P x \/ Q x} = UNIONS {x | P x} UNION UNIONS {x | Q x}`] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC;
    ONCE_REWRITE_TAC[INTER_COMM]; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC(SET_RULE
   `!s' t'. s SUBSET s' /\ t SUBSET t' /\ s' INTER t' = {}
            ==> s INTER t = {}`) THEN
  MAP_EVERY EXISTS_TAC
   [`interior s1:real^N->bool`; `interior s2:real^N->bool`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
  ASM_MESON_TAC[]);;

let TAGGED_DIVISION_UNIONS = prove
 (`!iset pfn. FINITE iset /\
              (!i:real^M->bool. i IN iset ==> pfn(i) tagged_division_of i) /\
              (!i1 i2. i1 IN iset /\ i2 IN iset /\ ~(i1 = i2)
                       ==> (interior(i1) INTER interior(i2) = {}))
              ==> UNIONS(IMAGE pfn iset) tagged_division_of (UNIONS iset)`,
  let lemma1 = prove
    (`(?t. (?x. (t = f x) /\ P x) /\ Q t) <=> ?x. P x /\ Q(f x)`,
     MESON_TAC[])
  and lemma2 = prove
   (`!s1 t1 s2 t2. s1 SUBSET t1 /\ s2 SUBSET t2 /\ (t1 INTER t2 = {})
                   ==> (s1 INTER s2 = {})`,
    SET_TAC[]) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[EXTENSION] tagged_division_of] THEN
  REWRITE_TAC[tagged_partial_division_of; IN_UNIONS; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS; IN_IMAGE] THEN
  SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC; ASM_MESON_TAC[]] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[lemma1] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`i1:real^M->bool`; `i2:real^M->bool`] THEN
  ASM_CASES_TAC `i1 = i2:real^M->bool` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma2 THEN
  MAP_EVERY EXISTS_TAC
   [`interior(i1:real^M->bool)`; `interior(i2:real^M->bool)`] THEN
  ASM_MESON_TAC[SUBSET; SUBSET_INTERIOR]);;

let TAGGED_PARTIAL_DIVISION_OF_UNION_SELF = prove
 (`!p s. p tagged_partial_division_of s
         ==> p tagged_division_of (UNIONS(IMAGE SND p))`,
  SIMP_TAC[tagged_partial_division_of; TAGGED_DIVISION_OF] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE; EXISTS_PAIR_THM] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM] THEN MESON_TAC[]]);;

let TAGGED_DIVISION_OF_UNION_SELF = prove
 (`!p s. p tagged_division_of s
         ==> p tagged_division_of (UNIONS(IMAGE SND p))`,
  SIMP_TAC[TAGGED_DIVISION_OF] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(c ==> a /\ b) /\ c ==> a /\ b /\ c`) THEN CONJ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM] THEN MESON_TAC[]]);;

let TAGGED_DIVISION_UNION_IMAGE_SND = prove
 (`!p s. p tagged_division_of s ==> s = UNIONS(IMAGE SND p)`,
  MESON_TAC[TAGGED_PARTIAL_DIVISION_OF_UNION_SELF; tagged_division_of]);;

let TAGGED_DIVISION_OF_ALT = prove
 (`!p s. p tagged_division_of s <=>
         p tagged_partial_division_of s /\
         (!x. x IN s ==> ?t k. (t,k) IN p /\ x IN k)`,
  REWRITE_TAC[tagged_division_of; GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; IN_ELIM_THM] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_PAIR_THM; IN_ELIM_THM] THEN
  REWRITE_TAC[tagged_partial_division_of; SUBSET] THEN MESON_TAC[]);;

let TAGGED_DIVISION_OF_ANOTHER = prove
 (`!p s s'.
        p tagged_partial_division_of s' /\
        (!t k. (t,k) IN p ==> k SUBSET s) /\
        (!x. x IN s ==> ?t k. (t,k) IN p /\ x IN k)
        ==> p tagged_division_of s`,
  REWRITE_TAC[TAGGED_DIVISION_OF_ALT; tagged_partial_division_of] THEN
  SET_TAC[]);;

let TAGGED_PARTIAL_DIVISION_OF_SUBSET = prove
 (`!p s t. p tagged_partial_division_of s /\ s SUBSET t
           ==> p tagged_partial_division_of t`,
  REWRITE_TAC[tagged_partial_division_of] THEN SET_TAC[]);;

let TAGGED_DIVISION_OF_NONTRIVIAL = prove
 (`!s a b:real^N.
        s tagged_division_of interval[a,b] /\ ~(content(interval[a,b]) = &0)
        ==> {(x,k) | (x,k) IN s /\ ~(content k = &0)}
            tagged_division_of interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TAGGED_DIVISION_OF_ALT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TAGGED_PARTIAL_DIVISION_SUBSET THEN
    EXISTS_TAC `s:(real^N#(real^N->bool))->bool` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[tagged_division_of]) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_OF_TAGGED_DIVISION) THEN
    DISCH_THEN(MP_TAC o
     MATCH_MP(REWRITE_RULE[IMP_CONJ] DIVISION_OF_NONTRIVIAL)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[division_of] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_THM;
                GSYM CONJ_ASSOC] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Fine-ness of a partition w.r.t. a gauge.                                  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("fine",(12,"right"));;

let fine = new_definition
  `d fine s <=> !x k. (x,k) IN s ==> k SUBSET d(x)`;;

let FINE_INTER = prove
 (`!p d1 d2. (\x. d1(x) INTER d2(x)) fine p <=> d1 fine p /\ d2 fine p`,
  let lemma = prove
   (`s SUBSET (t INTER u) <=> s SUBSET t /\ s SUBSET u`,SET_TAC[]) in
  REWRITE_TAC[fine; IN_INTER; lemma] THEN MESON_TAC[]);;

let FINE_INTERS = prove
 (`!f s p. (\x. INTERS {f d x | d IN s}) fine p <=>
           !d. d IN s ==> (f d) fine p`,
  REWRITE_TAC[fine; SET_RULE `s SUBSET INTERS u <=> !t. t IN u ==> s SUBSET t`;
              IN_ELIM_THM] THEN MESON_TAC[]);;

let FINE_UNION = prove
 (`!d p1 p2. d fine p1 /\ d fine p2 ==> d fine (p1 UNION p2)`,
  REWRITE_TAC[fine; IN_UNION] THEN MESON_TAC[]);;

let FINE_UNIONS = prove
 (`!d ps. (!p. p IN ps ==> d fine p) ==> d fine (UNIONS ps)`,
  REWRITE_TAC[fine; IN_UNIONS] THEN MESON_TAC[]);;

let FINE_SUBSET = prove
 (`!d p q. p SUBSET q /\ d fine q ==> d fine p`,
  REWRITE_TAC[fine; SUBSET] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Gauge integral. Define on compact intervals first, then use a limit.      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_integral_compact_interval",(12,"right"));;
parse_as_infix("has_integral",(12,"right"));;
parse_as_infix("integrable_on",(12,"right"));;

let has_integral_compact_interval = new_definition
  `(f has_integral_compact_interval y) i <=>
        !e. &0 < e
            ==> ?d. gauge d /\
                    !p. p tagged_division_of i /\ d fine p
                        ==> norm(vsum p (\(x,k). content(k) % f(x)) - y) < e`;;

let has_integral_def = new_definition
  `(f has_integral y) i <=>
        if ?a b. i = interval[a,b] then (f has_integral_compact_interval y) i
        else !e. &0 < e
                 ==> ?B. &0 < B /\
                         !a b. ball(vec 0,B) SUBSET interval[a,b]
                               ==> ?z. ((\x. if x IN i then f(x) else vec 0)
                                        has_integral_compact_interval z)
                                        (interval[a,b]) /\
                                       norm(z - y) < e`;;

let has_integral = prove
 (`(f has_integral y) (interval[a,b]) <=>
        !e. &0 < e
            ==> ?d. gauge d /\
                    !p. p tagged_division_of interval[a,b] /\ d fine p
                        ==> norm(vsum p (\(x,k). content(k) % f(x)) - y) < e`,
  REWRITE_TAC[has_integral_def; has_integral_compact_interval] THEN
  MESON_TAC[]);;

let has_integral_alt = prove
 (`(f has_integral y) i <=>
        if ?a b. i = interval[a,b] then (f has_integral y) i
        else !e. &0 < e
                 ==> ?B. &0 < B /\
                         !a b. ball(vec 0,B) SUBSET interval[a,b]
                               ==> ?z. ((\x. if x IN i then f(x) else vec 0)
                                        has_integral z) (interval[a,b]) /\
                                       norm(z - y) < e`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [has_integral_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [POP_ASSUM(REPEAT_TCL CHOOSE_THEN SUBST1_TAC); ALL_TAC] THEN
  REWRITE_TAC[has_integral_compact_interval; has_integral]);;

let integrable_on = new_definition
 `f integrable_on i <=> ?y. (f has_integral y) i`;;

let integral = new_definition
 `integral i f = @y. (f has_integral y) i`;;

let INTEGRABLE_INTEGRAL = prove
 (`!f i. f integrable_on i ==> (f has_integral (integral i f)) i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable_on; integral] THEN
  CONV_TAC(RAND_CONV SELECT_CONV) THEN REWRITE_TAC[]);;

let HAS_INTEGRAL_INTEGRABLE = prove
 (`!f i s. (f has_integral i) s ==> f integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[]);;

let HAS_INTEGRAL_INTEGRAL = prove
 (`!f s. f integrable_on s <=> (f has_integral (integral s f)) s`,
  MESON_TAC[INTEGRABLE_INTEGRAL; HAS_INTEGRAL_INTEGRABLE]);;

let VSUM_CONTENT_NULL = prove
 (`!f:real^M->real^N a b p.
        content(interval[a,b]) = &0 /\
        p tagged_division_of interval[a,b]
        ==> vsum p (\(x,k). content k % f x) = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ_0 THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:real^M`; `k:real^M->bool`] THEN
  DISCH_TAC THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPECL [`p:real^M`; `k:real^M->bool`]) THEN
  ASM_MESON_TAC[CONTENT_SUBSET; CONTENT_POS_LE; REAL_ARITH
   `&0 <= x /\ x <= y /\ y = &0 ==> x = &0`]);;

(* ------------------------------------------------------------------------- *)
(* Some basic combining lemmas.                                              *)
(* ------------------------------------------------------------------------- *)

let TAGGED_DIVISION_UNIONS_EXISTS = prove
 (`!d iset i:real^M->bool.
        FINITE iset /\
        (!i. i IN iset ==> ?p. p tagged_division_of i /\ d fine p) /\
        (!i1 i2. i1 IN iset /\ i2 IN iset /\ ~(i1 = i2)
                 ==> (interior(i1) INTER interior(i2) = {})) /\
        (UNIONS iset = i)
        ==> ?p. p tagged_division_of i /\ d fine p`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  EXISTS_TAC `UNIONS (IMAGE(p:(real^M->bool)->((real^M#(real^M->bool))->bool))
                      iset)` THEN
  ASM_SIMP_TAC[TAGGED_DIVISION_UNIONS] THEN
  ASM_MESON_TAC[FINE_UNIONS; IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* The set we're concerned with must be closed.                              *)
(* ------------------------------------------------------------------------- *)

let DIVISION_OF_CLOSED = prove
 (`!s i. s division_of i ==> closed i`,
  REWRITE_TAC[division_of] THEN MESON_TAC[CLOSED_UNIONS; CLOSED_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* General bisection principle for intervals; might be useful elsewhere.     *)
(* ------------------------------------------------------------------------- *)

let INTERVAL_BISECTION_STEP = prove
 (`!P. P {} /\
       (!s t. P s /\ P t /\ interior(s) INTER interior(t) = {}
              ==> P(s UNION t))
       ==> !a b:real^N.
                ~(P(interval[a,b]))
                ==> ?c d. ~(P(interval[c,d])) /\
                          !i. 1 <= i /\ i <= dimindex(:N)
                              ==> a$i <= c$i /\ c$i <= d$i /\ d$i <= b$i /\
                                  &2 * (d$i - c$i) <= b$i - a$i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `!i. 1 <= i /\ i <= dimindex(:N)
                     ==> (a:real^N)$i <= (b:real^N)$i` THENL
   [ALL_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INTERVAL_NE_EMPTY]) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!f. FINITE f /\
        (!s:real^N->bool. s IN f ==> P s) /\
        (!s:real^N->bool. s IN f ==> ?a b. s = interval[a,b]) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t)
               ==> interior(s) INTER interior(t) = {})
        ==> P(UNIONS f)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[UNIONS_0; UNIONS_INSERT; NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
    REWRITE_TAC[IMP_IMP] THEN REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
      FIRST_X_ASSUM MATCH_MP_TAC THEN STRIP_ASSUME_TAC th) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `{ interval[c,d] |
      !i. 1 <= i /\ i <= dimindex(:N)
          ==> ((c:real^N)$i = (a:real^N)$i) /\ (d$i = (a$i + b$i) / &2) \/
              (c$i = (a$i + b$i) / &2) /\ ((d:real^N)$i = (b:real^N)$i)}`) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `IMAGE (\s. closed_interval
       [(lambda i. if i IN s then (a:real^N)$i else (a$i + b$i) / &2):real^N,
        (lambda i. if i IN s then (a$i + b$i) / &2 else (b:real^N)$i)])
         {s | s SUBSET (1..dimindex(:N))}` THEN
    CONJ_TAC THENL
     [SIMP_TAC[FINITE_POWERSET; FINITE_IMAGE; FINITE_NUMSEG]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `k:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N` (X_CHOOSE_THEN `d:real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
    EXISTS_TAC `{i | 1 <= i /\ i <= dimindex(:N) /\
                     ((c:real^N)$i = (a:real^N)$i)}` THEN
    CONJ_TAC THENL [ALL_TAC; SIMP_TAC[IN_ELIM_THM; IN_NUMSEG]] THEN
    AP_TERM_TAC THEN REWRITE_TAC[CONS_11; PAIR_EQ] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; IN_ELIM_THM] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN `i:num` o SPEC `i:num`)) THEN
    REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> (a ==> b /\ c)`] THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN ANTS_TAC THENL
   [UNDISCH_TAC `~P(interval[a:real^N,b])` THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
    GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
    REWRITE_TAC[UNWIND_THM2; IN_INTERVAL] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> (a ==> b /\ c)`] THEN
    REWRITE_TAC[GSYM LAMBDA_SKOLEM] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))`) THEN
    STRIP_TAC THEN
    ONCE_REWRITE_TAC[TAUT `(a \/ b) /\ c <=> ~(a ==> ~c) \/ ~(b ==> ~c)`] THEN
    SIMP_TAC[] THEN
    REWRITE_TAC[TAUT `~(a ==> ~b) <=> a /\ b`; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[EXISTS_OR_THM; RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC[LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  MATCH_MP_TAC(TAUT `b /\ (~a ==> e) /\ c ==> ~(a /\ b /\ c) ==> e`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
    DISCH_THEN(fun th -> REPEAT DISCH_TAC THEN MP_TAC th) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IMP_IMP; INTERIOR_CLOSED_INTERVAL] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`c1:real^N`; `d1:real^N`; `c2:real^N`; `d2:real^N`] THEN
  ASM_CASES_TAC `(c1 = c2:real^N) /\ (d1 = d2:real^N)` THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN MP_TAC th) THEN
  REWRITE_TAC[IMP_IMP] THEN
  UNDISCH_TAC `~((c1 = c2:real^N) /\ (d1 = d2:real^N))` THEN
  REWRITE_TAC[CART_EQ; INTERIOR_CLOSED_INTERVAL] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> (a ==> b /\ c)`] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (fun th ->
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN MP_TAC th)) THEN
  REWRITE_TAC[NOT_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[EXTENSION; IN_INTERVAL; NOT_IN_EMPTY; IN_INTER] THEN
  SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_EQ_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[
    REAL_ARITH `~((a * &2 = a + b) /\ (a + b = b * &2)) <=> ~(a = b)`;
    REAL_ARITH `~((a + b = a * &2) /\ (b * &2 = a + b)) <=> ~(a = b)`] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `x:real^N` THEN MP_TAC th) THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> (a ==> b /\ c)`] THEN
  ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let INTERVAL_BISECTION = prove
 (`!P. P {} /\
       (!s t. P s /\ P t /\ interior(s) INTER interior(t) = {}
              ==> P(s UNION t))
       ==> !a b:real^N.
                ~(P(interval[a,b]))
                ==> ?x. x IN interval[a,b] /\
                        !e. &0 < e
                            ==> ?c d. x IN interval[c,d] /\
                                      interval[c,d] SUBSET ball(x,e) /\
                                      interval[c,d] SUBSET interval[a,b] /\
                                      ~P(interval[c,d])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?A B. (A(0) = a:real^N) /\ (B(0) = b) /\
          !n. ~(P(interval[A(SUC n),B(SUC n)])) /\
              !i. 1 <= i /\ i <= dimindex(:N)
                       ==> A(n)$i <= A(SUC n)$i /\
                           A(SUC n)$i <= B(SUC n)$i /\
                           B(SUC n)$i <= B(n)$i /\
                           &2 * (B(SUC n)$i - A(SUC n)$i) <= B(n)$i - A(n)$i`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `P:(real^N->bool)->bool` INTERVAL_BISECTION_STEP) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real^N->real^N->real^N`
     (X_CHOOSE_THEN `D:real^N->real^N->real^N` ASSUME_TAC)) THEN
    MP_TAC(prove_recursive_functions_exist num_RECURSION
     `(E 0 = a:real^N,b:real^N) /\
      (!n. E(SUC n) = C (FST(E n)) (SND(E n)),
                      D (FST(E n)) (SND(E n)))`) THEN
    DISCH_THEN(X_CHOOSE_THEN `E:num->real^N#real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\n. FST((E:num->real^N#real^N) n)` THEN
    EXISTS_TAC `\n. SND((E:num->real^N#real^N) n)` THEN
    ASM_REWRITE_TAC[] THEN INDUCT_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?n:num. !x y. x IN interval[A(n),B(n)] /\ y IN interval[A(n),B(n)]
                          ==> dist(x,y:real^N) < e`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC(SPEC
     `sum(1..dimindex(:N)) (\i. (b:real^N)$i - (a:real^N)$i) / e`
     REAL_ARCH_POW2) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N))(\i. abs((x - y:real^N)$i))` THEN
    REWRITE_TAC[dist; NORM_LE_L1] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N))
                   (\i. (B:num->real^N)(n)$i - (A:num->real^N)(n)$i)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a <= x /\ x <= b /\ a <= y /\ y <= b
                               ==> abs(x - y) <= b - a`) THEN
      UNDISCH_TAC `x IN interval[(A:num->real^N) n,B n]` THEN
      UNDISCH_TAC `y IN interval[(A:num->real^N) n,B n]` THEN
      REWRITE_TAC[IN_INTERVAL] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
     `sum(1..dimindex(:N)) (\i. (b:real^N)$i - (a:real^N)$i) /
      &2 pow n` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ]] THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    SPEC_TAC(`n:num`,`m:num`) THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[real_pow; REAL_DIV_1; REAL_LE_REFL] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    ASM_MESON_TAC[REAL_LE_TRANS; REAL_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. !n:num. a IN interval[A(n),B(n)]` MP_TAC THENL
   [MATCH_MP_TAC DECREASING_CLOSED_NEST THEN
    ASM_REWRITE_TAC[CLOSED_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[INTERVAL_EQ_EMPTY] THEN
      ASM_MESON_TAC[REAL_NOT_LT; REAL_LE_TRANS];
      ALL_TAC] THEN
    REWRITE_TAC[LE_EXISTS] THEN SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `m:num` THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[GSYM LEFT_IMP_EXISTS_THM; EXISTS_REFL] THEN
    INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUBSET_REFL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interval[A(m + d:num):real^N,B(m + d)]` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL] THEN ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x0:real^N` THEN
  DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MAP_EVERY EXISTS_TAC [`(A:num->real^N) n`; `(B:num->real^N) n`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_MESON_TAC[];
    ALL_TAC;
    SPEC_TAC(`n:num`,`p:num`) THEN INDUCT_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!m n. m <= n ==> interval[(A:num->real^N) n,B n] SUBSET interval[A m,B m]`
   (fun th -> ASM_MESON_TAC[SUBSET; LE_0; th]) THEN
  MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
  REPEAT(CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[SUBSET_INTERVAL] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cousin's lemma.                                                           *)
(* ------------------------------------------------------------------------- *)

let FINE_DIVISION_EXISTS = prove
 (`!g a b:real^M.
        gauge g ==> ?p. p tagged_division_of (interval[a,b]) /\ g fine p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\s:real^M->bool. ?p. p tagged_division_of s /\ g fine p`
        INTERVAL_BISECTION) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MESON_TAC[TAGGED_DIVISION_UNION; FINE_UNION;
              TAGGED_DIVISION_OF_EMPTY; fine; NOT_IN_EMPTY];
    DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `b:real^M`])] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^M` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^M` o REWRITE_RULE[gauge]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL; NOT_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:real^M`; `d:real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{(x:real^M,interval[c:real^M,d])}`) THEN
  ASM_SIMP_TAC[TAGGED_DIVISION_OF_SELF] THEN
  REWRITE_TAC[fine; IN_SING; PAIR_EQ] THEN ASM_MESON_TAC[SUBSET_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Basic theorems about integrals.                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_UNIQUE = prove
 (`!f:real^M->real^N i k1 k2.
        (f has_integral k1) i /\ (f has_integral k2) i ==> k1 = k2`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!f:real^M->real^N a b k1 k2.
       (f has_integral k1) (interval[a,b]) /\
       (f has_integral k2) (interval[a,b])
       ==> k1 = k2`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[has_integral] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    REWRITE_TAC[GSYM NORM_POS_LT] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `norm(k1 - k2 :real^N) / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `d1:real^M->real^M->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `d2:real^M->real^M->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPEC `\x. ((d1:real^M->real^M->bool) x) INTER (d2 x)`
                 FINE_DIVISION_EXISTS) THEN
    ASM_SIMP_TAC[GAUGE_INTER] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `b:real^M`]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_forall o concl))) THEN
    REWRITE_TAC[] THEN REWRITE_TAC[IMP_IMP; NOT_EXISTS_THM] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    GEN_TAC THEN
    MATCH_MP_TAC(TAUT
     `(f0 ==> f1 /\ f2) /\ ~(n1 /\ n2)
      ==> (t /\ f1 ==> n1) /\ (t /\ f2 ==> n2) ==> ~(t /\ f0)`) THEN
    CONJ_TAC THENL [SIMP_TAC[fine; SUBSET_INTER]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `c <= a + b ==> ~(a < c / &2 /\ b < c / &2)`) THEN
    MESON_TAC[NORM_SUB; NORM_TRIANGLE; VECTOR_ARITH
     `k1 - k2:real^N = (k1 - x) + (x - k2)`];
    ALL_TAC] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[has_integral_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(NORM_ARITH
   `~(&0 < norm(x - y)) ==> x = y`) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (MP_TAC o SPEC `norm(k1 - k2:real^N) / &2`)) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC
   `ball(vec 0,B1) UNION ball(vec 0:real^M,B2)`
   BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[BOUNDED_UNION; BOUNDED_BALL; UNION_SUBSET; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  DISCH_THEN(CONJUNCTS_THEN(ANTE_RES_THEN MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `w:real^N = z:real^N` SUBST_ALL_TAC THEN
  ASM_MESON_TAC[NORM_ARITH
   `~(norm(z - k1) < norm(k1 - k2) / &2 /\
      norm(z - k2) < norm(k1 - k2) / &2)`]);;

let INTEGRAL_UNIQUE = prove
 (`!f y k.
      (f has_integral y) k ==> integral k f = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integral] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[HAS_INTEGRAL_UNIQUE]);;

let HAS_INTEGRAL_INTEGRABLE_INTEGRAL = prove
 (`!f:real^M->real^N i s.
        (f has_integral i) s <=> f integrable_on s /\ integral s f = i`,
  MESON_TAC[INTEGRABLE_INTEGRAL; INTEGRAL_UNIQUE; integrable_on]);;

let INTEGRAL_EQ_HAS_INTEGRAL = prove
 (`!s f y. f integrable_on s ==> (integral s f = y <=> (f has_integral y) s)`,
  MESON_TAC[INTEGRABLE_INTEGRAL; INTEGRAL_UNIQUE]);;

let HAS_INTEGRAL_IS_0 = prove
 (`!f:real^M->real^N s.
        (!x. x IN s ==> (f(x) = vec 0)) ==> (f has_integral vec 0) s`,
  SUBGOAL_THEN
   `!f:real^M->real^N a b.
        (!x. x IN interval[a,b] ==> (f(x) = vec 0))
        ==> (f has_integral vec 0) (interval[a,b])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[has_integral] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `\x:real^M. ball(x,&1)` THEN
    SIMP_TAC[gauge; OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
    UNDISCH_TAC `&0 < e` THEN MATCH_MP_TAC(TAUT `(a <=> b) ==> b ==> a`) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ; VECTOR_ADD_LID] THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    X_GEN_TAC `x:real^M` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN interval[a,b]`
     (fun th -> ASM_SIMP_TAC[th; VECTOR_MUL_RZERO]) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [tagged_division_of]) THEN
    REWRITE_TAC[tagged_partial_division_of; SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[has_integral_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `vec 0:real^N` THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let HAS_INTEGRAL_0 = prove
 (`!s. ((\x. vec 0) has_integral vec 0) s`,
  SIMP_TAC[HAS_INTEGRAL_IS_0]);;

let HAS_INTEGRAL_0_EQ = prove
 (`!i s. ((\x. vec 0) has_integral i) s <=> i = vec 0`,
  MESON_TAC[HAS_INTEGRAL_UNIQUE; HAS_INTEGRAL_0]);;

let HAS_INTEGRAL_LINEAR = prove
 (`!f:real^M->real^N y s h:real^N->real^P.
        (f has_integral y) s /\ linear h ==> ((h o f) has_integral h(y)) s`,
  SUBGOAL_THEN
    `!f:real^M->real^N y a b h:real^N->real^P.
          (f has_integral y) (interval[a,b]) /\ linear h
          ==> ((h o f) has_integral h(y)) (interval[a,b])`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[has_integral] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_BOUNDED_POS) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real / B`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real^M#(real^M->bool)->bool`) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
    FIRST_ASSUM(fun th -> W(fun (asl,w) ->
      MP_TAC(PART_MATCH rand th (rand w)))) THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> y <= e ==> x <= e`) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[LINEAR_SUB; LINEAR_VSUM; o_DEF; LAMBDA_PAIR_THM;
                 LINEAR_CMUL; REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[has_integral_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o MATCH_MP
    LINEAR_BOUNDED_POS) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / B:real`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:real` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(h:real^N->real^P) z` THEN
  SUBGOAL_THEN
   `(\x. if x IN s then ((h:real^N->real^P) o (f:real^M->real^N)) x else vec 0)
    = h o (\x. if x IN s then f x else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM LINEAR_SUB] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B * norm(z - y:real^N)` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]);;

let HAS_INTEGRAL_CMUL = prove
 (`!(f:real^M->real^N) k s c.
        (f has_integral k) s
        ==> ((\x. c % f(x)) has_integral (c % k)) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
   (REWRITE_RULE[o_DEF] HAS_INTEGRAL_LINEAR) THEN
  ASM_REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let HAS_INTEGRAL_NEG = prove
 (`!f k s. (f has_integral k) s ==> ((\x. --(f x)) has_integral (--k)) s`,
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN REWRITE_TAC[HAS_INTEGRAL_CMUL]);;

let HAS_INTEGRAL_ADD = prove
 (`!f:real^M->real^N g s.
        (f has_integral k) s /\ (g has_integral l) s
        ==> ((\x. f(x) + g(x)) has_integral (k + l)) s`,
  SUBGOAL_THEN
   `!f:real^M->real^N g k l a b.
        (f has_integral k) (interval[a,b]) /\
        (g has_integral l) (interval[a,b])
        ==> ((\x. f(x) + g(x)) has_integral (k + l)) (interval[a,b])`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[has_integral; AND_FORALL_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `d1:real^M->real^M->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `d2:real^M->real^M->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `\x. ((d1:real^M->real^M->bool) x) INTER (d2 x)` THEN
    ASM_SIMP_TAC[GAUGE_INTER] THEN
    REWRITE_TAC[tagged_division_of; tagged_partial_division_of] THEN
    SIMP_TAC[VSUM_ADD; VECTOR_ADD_LDISTRIB; LAMBDA_PAIR] THEN
    REWRITE_TAC[GSYM LAMBDA_PAIR] THEN
    REWRITE_TAC[GSYM tagged_partial_division_of] THEN
    REWRITE_TAC[GSYM tagged_division_of; FINE_INTER] THEN
    SIMP_TAC[VECTOR_ARITH `(a + b) - (c + d) = (a - c) + (b - d):real^N`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NORM_TRIANGLE_LT THEN
    MATCH_MP_TAC(REAL_ARITH `x < e / &2 /\ y < e / &2 ==> x + y < e`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[has_integral_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (MP_TAC o SPEC `e / &2`)) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `max B1 B2:real` THEN ASM_REWRITE_TAC[REAL_LT_MAX] THEN
  REWRITE_TAC[BALL_MAX_UNION; UNION_SUBSET] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  DISCH_THEN(CONJUNCTS_THEN(ANTE_RES_THEN MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w + z:real^N` THEN
  SUBGOAL_THEN
    `(\x. if x IN s then (f:real^M->real^N) x + g x else vec 0) =
     (\x. (if x IN s then f x else vec 0) + (if x IN s then g x else vec 0))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LE])) THEN
  NORM_ARITH_TAC);;

let HAS_INTEGRAL_SUB = prove
 (`!f:real^M->real^N g s.
        (f has_integral k) s /\ (g has_integral l) s
        ==> ((\x. f(x) - g(x)) has_integral (k - l)) s`,
  SIMP_TAC[VECTOR_SUB; HAS_INTEGRAL_NEG; HAS_INTEGRAL_ADD]);;

let INTEGRAL_0 = prove
 (`!s. integral s (\x. vec 0) = vec 0`,
  MESON_TAC[INTEGRAL_UNIQUE; HAS_INTEGRAL_0]);;

let INTEGRAL_ADD = prove
 (`!f:real^M->real^N g k l s.
        f integrable_on s /\ g integrable_on s
        ==> integral s (\x. f x + g x) = integral s f + integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_ADD THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

let INTEGRAL_CMUL = prove
 (`!f:real^M->real^N c s.
        f integrable_on s ==> integral s (\x. c % f(x)) = c % integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

let INTEGRAL_NEG = prove
 (`!f:real^M->real^N s.
        f integrable_on s ==> integral s (\x. --f(x)) = --integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_NEG THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

let INTEGRAL_SUB = prove
 (`!f:real^M->real^N g k l s.
        f integrable_on s /\ g integrable_on s
        ==> integral s (\x. f x - g x) = integral s f - integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_SUB THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

let INTEGRABLE_0 = prove
 (`!s. (\x. vec 0) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_0]);;

let INTEGRABLE_ADD = prove
 (`!f:real^M->real^N g s.
        f integrable_on s /\ g integrable_on s
        ==> (\x. f x + g x) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_ADD]);;

let INTEGRABLE_CMUL = prove
 (`!f:real^M->real^N c s.
        f integrable_on s ==> (\x. c % f(x)) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_CMUL]);;

let INTEGRABLE_CMUL_EQ = prove
 (`!f:real^M->real^N s c.
      (\x. c % f x) integrable_on s <=> c = &0 \/ f integrable_on s`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; VECTOR_MUL_LZERO; INTEGRABLE_0] THEN
  ASM_CASES_TAC `c = &0` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv c:real` o MATCH_MP INTEGRABLE_CMUL) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_LID; REAL_MUL_LINV; ETA_AX]);;

let INTEGRABLE_NEG = prove
 (`!f:real^M->real^N s.
        f integrable_on s ==> (\x. --f(x)) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_NEG]);;

let INTEGRABLE_SUB = prove
 (`!f:real^M->real^N g s.
        f integrable_on s /\ g integrable_on s
        ==> (\x. f x - g x) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_SUB]);;

let INTEGRABLE_LINEAR = prove
 (`!f h s. f integrable_on s /\ linear h ==> (h o f) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_LINEAR]);;

let INTEGRAL_LINEAR = prove
 (`!f:real^M->real^N s h:real^N->real^P.
        f integrable_on s /\ linear h
        ==> integral s (h o f) = h(integral s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`(h:real^N->real^P) o (f:real^M->real^N)`; `s:real^M->bool`] THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC HAS_INTEGRAL_LINEAR] THEN
  ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; INTEGRABLE_LINEAR]);;

let HAS_INTEGRAL_VSUM = prove
 (`!f:A->real^M->real^N s t.
        FINITE t /\
        (!a. a IN t ==> ((f a) has_integral (i a)) s)
        ==> ((\x. vsum t (\a. f a x)) has_integral (vsum t i)) s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; HAS_INTEGRAL_0; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_ADD THEN
  ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let INTEGRAL_VSUM = prove
 (`!f:A->real^M->real^N s t.
        FINITE t /\
        (!a. a IN t ==> (f a) integrable_on s)
        ==> integral s (\x. vsum t (\a. f a x)) =
                vsum t (\a. integral s (f a))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

let INTEGRABLE_VSUM = prove
 (`!f:A->real^M->real^N s t.
        FINITE t /\
        (!a. a IN t ==> (f a) integrable_on s)
        ==>  (\x. vsum t (\a. f a x)) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_VSUM]);;

let HAS_INTEGRAL_EQ = prove
 (`!f:real^M->real^N g k s.
        (!x. x IN s ==> (f(x) = g(x))) /\
        (f has_integral k) s
        ==> (g has_integral k) s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP HAS_INTEGRAL_IS_0) MP_TAC) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN
  SIMP_TAC[VECTOR_ARITH `x - (x - y:real^N) = y`; ETA_AX; VECTOR_SUB_RZERO]);;

let INTEGRABLE_EQ = prove
 (`!f:real^M->real^N g s.
        (!x. x IN s ==> (f(x) = g(x))) /\
        f integrable_on s
        ==> g integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_EQ]);;

let HAS_INTEGRAL_EQ_EQ = prove
 (`!f:real^M->real^N g k s.
        (!x. x IN s ==> (f(x) = g(x)))
        ==> ((f has_integral k) s <=> (g has_integral k) s)`,
  MESON_TAC[HAS_INTEGRAL_EQ]);;

let HAS_INTEGRAL_NULL = prove
 (`!f:real^M->real^N a b.
    content(interval[a,b]) = &0 ==> (f has_integral vec 0) (interval[a,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_integral] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `\x:real^M. ball(x,&1)` THEN REWRITE_TAC[GAUGE_TRIVIAL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 /\ &0 < e ==> x < e`) THEN
  ASM_REWRITE_TAC[NORM_EQ_0] THEN ASM_MESON_TAC[VSUM_CONTENT_NULL]);;

let HAS_INTEGRAL_NULL_EQ = prove
 (`!f a b i. content(interval[a,b]) = &0
             ==> ((f has_integral i) (interval[a,b]) <=> i = vec 0)`,
  ASM_MESON_TAC[INTEGRAL_UNIQUE; HAS_INTEGRAL_NULL]);;

let INTEGRAL_NULL = prove
 (`!f a b. content(interval[a,b]) = &0
           ==> integral(interval[a,b]) f = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  ASM_MESON_TAC[HAS_INTEGRAL_NULL]);;

let INTEGRABLE_ON_NULL = prove
 (`!f a b. content(interval[a,b]) = &0
           ==> f integrable_on interval[a,b]`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_NULL]);;

let HAS_INTEGRAL_EMPTY = prove
 (`!f. (f has_integral vec 0) {}`,
  MESON_TAC[HAS_INTEGRAL_NULL; CONTENT_EMPTY; EMPTY_AS_INTERVAL]);;

let HAS_INTEGRAL_EMPTY_EQ = prove
 (`!f i. (f has_integral i) {} <=> i = vec 0`,
  MESON_TAC[HAS_INTEGRAL_UNIQUE; HAS_INTEGRAL_EMPTY]);;

let INTEGRABLE_ON_EMPTY = prove
 (`!f. f integrable_on {}`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_EMPTY]);;

let INTEGRAL_EMPTY = prove
 (`!f. integral {} f = vec 0`,
  MESON_TAC[EMPTY_AS_INTERVAL; INTEGRAL_UNIQUE; HAS_INTEGRAL_EMPTY]);;

let HAS_INTEGRAL_REFL = prove
 (`!f a. (f has_integral vec 0) (interval[a,a])`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_NULL THEN
  SIMP_TAC[INTERVAL_SING; INTERIOR_CLOSED_INTERVAL; CONTENT_EQ_0_INTERIOR]);;

let INTEGRABLE_ON_REFL = prove
 (`!f a. f integrable_on interval[a,a]`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_REFL]);;

let INTEGRAL_REFL = prove
 (`!f a. integral (interval[a,a]) f = vec 0`,
  MESON_TAC[INTEGRAL_UNIQUE; HAS_INTEGRAL_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Cauchy-type criterion for integrability.                                  *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_CAUCHY = prove
 (`!f:real^M->real^N a b.
    f integrable_on interval[a,b] <=>
        !e. &0 < e
            ==> ?d. gauge d /\
                    !p1 p2. p1 tagged_division_of interval[a,b] /\ d fine p1 /\
                            p2 tagged_division_of interval[a,b] /\ d fine p2
                            ==> norm(vsum p1 (\(x,k). content k % f x) -
                                     vsum p2 (\(x,k). content k % f x)) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable_on; has_integral] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^N` (MP_TAC o SPEC `e / &2`)) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `d:real^M->real^M->bool` THEN
    REWRITE_TAC[GSYM dist] THEN MESON_TAC[DIST_TRIANGLE_HALF_L];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real^M->real^M->bool` MP_TAC) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
  MP_TAC(GEN `n:num`
   (ISPECL [`\x. INTERS {(d:num->real^M->real^M->bool) i x | i IN 0..n}`;
            `a:real^M`; `b:real^M`]
     FINE_DIVISION_EXISTS)) THEN
  ASM_SIMP_TAC[GAUGE_INTERS; FINE_INTERS; FINITE_NUMSEG; SKOLEM_THM] THEN
  REWRITE_TAC[IN_NUMSEG; LE_0; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->(real^M#(real^M->bool))->bool`
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `cauchy (\n. vsum (p n)
                   (\(x,k:real^M->bool). content k % (f:real^M->real^N) x))`
  MP_TAC THENL
   [REWRITE_TAC[cauchy] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
     [MESON_TAC[DIST_SYM]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN REWRITE_TAC[GE] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&m + &1)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[dist] THEN ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY; LIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[dist] THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e / &2` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC
   `(d:num->real^M->real^M->bool) (N1 + N2)` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `q:(real^M#(real^M->bool))->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM dist] THEN MATCH_MP_TAC DIST_TRIANGLE_HALF_L THEN
  EXISTS_TAC `vsum (p(N1+N2:num))
                  (\(x,k:real^M->bool). content k % (f:real^M->real^N) x)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[dist] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `inv(&(N1 + N2) + &1)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N1)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Additivity of integral on abutting intervals.                             *)
(* ------------------------------------------------------------------------- *)

let INTERVAL_SPLIT = prove
 (`!a b:real^N c k.
    1 <= k /\ k <= dimindex(:N)
    ==> interval[a,b] INTER {x | x$k <= c} =
        interval[a,(lambda i. if i = k then min (b$k) c else b$i)] /\
        interval[a,b] INTER {x | x$k >= c} =
        interval[(lambda i. if i = k then max (a$k) c else a$i),b]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTERVAL; IN_INTER; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN X_GEN_TAC `y:real^N` THEN
  MATCH_MP_TAC(TAUT `(c ==> b) /\ (c ==> a) /\ (a /\ b ==> c)
                     ==> (a /\ b <=> c)`) THEN
  (CONJ_TAC THENL
    [ASM_MESON_TAC[REAL_MAX_LE; REAL_LE_MIN; real_ge];  ALL_TAC]) THEN
  REWRITE_TAC[LEFT_AND_FORALL_THM; real_ge] THEN CONJ_TAC THEN
  MATCH_MP_TAC MONO_FORALL THEN ASM_MESON_TAC[REAL_MAX_LE; REAL_LE_MIN]);;

let CONTENT_SPLIT = prove
 (`!a b:real^N k.
    1 <= k /\ k <= dimindex(:N)
    ==> content(interval[a,b]) =
        content(interval[a,b] INTER {x | x$k <= c}) +
        content(interval[a,b] INTER {x | x$k >= c})`,
  SIMP_TAC[INTERVAL_SPLIT; CONTENT_CLOSED_INTERVAL_CASES; LAMBDA_BETA] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ARITH
   `((a <= if p then b else c) <=> (p ==> a <= b) /\ (~p ==> a <= c)) /\
    ((if p then b else c) <= a <=> (p ==> b <= a) /\ (~p ==> c <= a))`] THEN
  REWRITE_TAC[REAL_LE_MIN; REAL_MAX_LE] THEN
  REWRITE_TAC[MESON[] `(i = k ==> p i k) <=> (i = k ==> p i i)`] THEN
  REWRITE_TAC[TAUT `(p ==> a /\ b) /\ (~p ==> a) <=> a /\ (p ==> b)`] THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `!i. 1 <= i /\ i <= dimindex(:N) ==> (a:real^N)$i <= (b:real^N)$i` THEN
  ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  REWRITE_TAC[MESON[] `(!i. P i ==> i = k ==> Q i) <=> (P k ==> Q k)`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `min b c = if c <= b then c else b`;
              REAL_ARITH `max a c = if a <= c then c else a`] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID]) THEN
  REWRITE_TAC[MESON[] `(if i = k then a k else a i) = a i`] THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_TOTAL]] THEN
  SUBGOAL_THEN `1..dimindex(:N) = k INSERT ((1..dimindex(:N)) DELETE k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_NUMSEG] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG; IN_DELETE] THEN
  MATCH_MP_TAC(REAL_RING
   `p'' = p /\ p':real = p
    ==> (b - a) * p = (c - a) * p' + (b - c) * p''`) THEN
  CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN SIMP_TAC[IN_DELETE]);;

let DIVISION_SPLIT_LEFT_INJ,DIVISION_SPLIT_RIGHT_INJ = (CONJ_PAIR o prove)
 (`(!d i k1 k2 k c.
        d division_of i /\ 1 <= k /\ k <= dimindex(:N) /\
        k1 IN d /\ k2 IN d /\ ~(k1 = k2) /\
        k1 INTER {x | x$k <= c} = k2 INTER {x | x$k <= c}
        ==> content(k1 INTER {x:real^N | x$k <= c}) = &0) /\
   (!d i k1 k2 k c.
        d division_of i /\ 1 <= k /\ k <= dimindex(:N) /\
        k1 IN d /\ k2 IN d /\ ~(k1 = k2) /\
        k1 INTER {x | x$k >= c} = k2 INTER {x | x$k >= c}
        ==> content(k1 INTER {x:real^N | x$k >= c}) = &0)`,
  let lemma = prove
   (`!a b:real^N c k.
      1 <= k /\ k <= dimindex(:N)
      ==> (content(interval[a,b] INTER {x | x$k <= c}) = &0 <=>
           interior(interval[a,b] INTER {x | x$k <= c}) = {}) /\
          (content(interval[a,b] INTER {x | x$k >= c}) = &0 <=>
           interior(interval[a,b] INTER {x | x$k >= c}) = {})`,
    SIMP_TAC[INTERVAL_SPLIT; CONTENT_EQ_0_INTERIOR]) in
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONTENT_EQ_0_INTERIOR] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o CONJUNCT1) o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`k1:real^N->bool`; `k2:real^N->bool`]) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `k2:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `v:real^N`
    SUBST_ALL_TAC)) THEN
  ASM_SIMP_TAC[lemma] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `s INTER t = {}
    ==> u SUBSET s /\ u SUBSET t ==> u = {}`)) THEN
  CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[]);;

let TAGGED_DIVISION_SPLIT_LEFT_INJ = prove
 (`!d i x1 k1 x2 k2 k c.
        d tagged_division_of i /\ 1 <= k /\ k <= dimindex(:N) /\
        (x1,k1) IN d /\ (x2,k2) IN d /\ ~(k1 = k2) /\
        k1 INTER {x | x$k <= c} = k2 INTER {x | x$k <= c}
        ==> content(k1 INTER {x:real^N | x$k <= c}) = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_TAGGED_DIVISION) THEN
  MATCH_MP_TAC DIVISION_SPLIT_LEFT_INJ THEN
  EXISTS_TAC `IMAGE SND (d:(real^N#(real^N->bool))->bool)` THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[SND]);;

let TAGGED_DIVISION_SPLIT_RIGHT_INJ = prove
 (`!d i x1 k1 x2 k2 k c.
        d tagged_division_of i /\ 1 <= k /\ k <= dimindex(:N) /\
        (x1,k1) IN d /\ (x2,k2) IN d /\ ~(k1 = k2) /\
        k1 INTER {x | x$k >= c} = k2 INTER {x | x$k >= c}
        ==> content(k1 INTER {x:real^N | x$k >= c}) = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_TAGGED_DIVISION) THEN
  MATCH_MP_TAC DIVISION_SPLIT_RIGHT_INJ THEN
  EXISTS_TAC `IMAGE SND (d:(real^N#(real^N->bool))->bool)` THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[SND]);;

let DIVISION_SPLIT = prove
 (`!p a b:real^N k c.
     p division_of interval[a,b] /\ 1 <= k /\ k <= dimindex(:N)
     ==> {l INTER {x | x$k <= c} |l| l IN p /\ ~(l INTER {x | x$k <= c} = {})}
         division_of (interval[a,b] INTER {x | x$k <= c}) /\
         {l INTER {x | x$k >= c} |l| l IN p /\ ~(l INTER {x | x$k >= c} = {})}
         division_of (interval[a,b] INTER {x | x$k >= c})`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  SIMP_TAC[division_of; FINITE_IMAGE] THEN
  SIMP_TAC[SET_RULE `(!x. x IN {f x | P x} ==> Q x) <=> (!x. P x ==> Q (f x))`;
           MESON[] `(!x y. x IN s /\ y IN t /\ Q x y ==> P x y) <=>
                    (!x. x IN s ==> !y. y IN t ==> Q x y ==> P x y)`;
           RIGHT_FORALL_IMP_THM] THEN
  REPEAT(MATCH_MP_TAC(TAUT
   `(a ==> a' /\ a'') /\ (b ==> b' /\ b'')
      ==> a /\ b ==> (a' /\ b') /\ (a'' /\ b'')`) THEN CONJ_TAC)
  THENL
   [ONCE_REWRITE_TAC[SET_RULE
    `{f x |x| x IN s /\ ~(f x = {})} = {y | y IN IMAGE f s /\ ~(y = {})}`] THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_IMAGE];
    REWRITE_TAC[AND_FORALL_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `l:real^N->bool` THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN STRIP_TAC THEN MP_TAC th) THEN
    (ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_AND THEN
     CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
     STRIP_TAC THEN ASM_MESON_TAC[INTERVAL_SPLIT]);
    DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
    (REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
     DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_SIMP_TAC[] THEN
     REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
     DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_SIMP_TAC[] THEN
     DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_SIMP_TAC[] THEN
     ANTS_TAC THENL [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
     MATCH_MP_TAC(SET_RULE
      `s SUBSET s' /\ t SUBSET t'
       ==> s' INTER t' = {} ==> s INTER t = {}`) THEN
     CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]);
   DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[INTER_UNIONS] THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_UNIONS] THEN
   CONJ_TAC THEN GEN_TAC THEN AP_TERM_TAC THEN
   GEN_REWRITE_TAC I [FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[NOT_IN_EMPTY]]);;

let HAS_INTEGRAL_SPLIT = prove
 (`!f:real^M->real^N k a b c.
      (f has_integral i) (interval[a,b] INTER {x | x$k <= c}) /\
      (f has_integral j) (interval[a,b] INTER {x | x$k >= c}) /\
      1 <= k /\ k <= dimindex(:M)
      ==> (f has_integral (i + j)) (interval[a,b])`,
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
  ASM_SIMP_TAC[INTERVAL_SPLIT] THEN REWRITE_TAC[has_integral] THEN
  ASM_SIMP_TAC[GSYM INTERVAL_SPLIT] THEN FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
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
     (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k >= c} = {})}`) THEN
  REMOVE_THEN "I1" (MP_TAC o SPEC
   `{(x:real^M,kk INTER {x:real^M | x$k <= c}) |x,kk|
     (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k <= c} = {})}`) THEN
  MATCH_MP_TAC(TAUT
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

(* ------------------------------------------------------------------------- *)
(* A sort of converse, integrability on subintervals.                        *)
(* ------------------------------------------------------------------------- *)

let TAGGED_DIVISION_UNION_INTERVAL = prove
 (`!a b:real^N p1 p2 c k.
        1 <= k /\ k <= dimindex(:N) /\
        p1 tagged_division_of (interval[a,b] INTER {x | x$k <= c}) /\
        p2 tagged_division_of (interval[a,b] INTER {x | x$k >= c})
        ==> (p1 UNION p2) tagged_division_of (interval[a,b])`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `interval[a,b] = (interval[a,b] INTER {x:real^N | x$k <= c}) UNION
                    (interval[a,b] INTER {x:real^N | x$k >= c})`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(t UNION u = UNIV) ==> s = (s INTER t) UNION (s INTER u)`) THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC TAGGED_DIVISION_UNION THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT; INTERIOR_CLOSED_INTERVAL] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_INTERVAL] THEN
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `k:num`)) THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let HAS_INTEGRAL_SEPARATE_SIDES = prove
 (`!f:real^M->real^N i a b k.
        (f has_integral i) (interval[a,b]) /\
        1 <= k /\ k <= dimindex(:M)
        ==> !e. &0 < e
                ==> ?d. gauge d /\
                        !p1 p2. p1 tagged_division_of
                                     (interval[a,b] INTER {x | x$k <= c}) /\
                                d fine p1 /\
                                p2 tagged_division_of
                                     (interval[a,b] INTER {x | x$k >= c}) /\
                                d fine p2
                                ==> norm((vsum p1 (\(x,k). content k % f x) +
                                          vsum p2 (\(x,k). content k % f x)) -
                                         i) < e`,
  REWRITE_TAC[has_integral] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum p1 (\(x,k). content k % f x) + vsum p2 (\(x,k). content k % f x) =
    vsum (p1 UNION p2) (\(x,k:real^M->bool). content k % (f:real^M->real^N) x)`
  SUBST1_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[TAGGED_DIVISION_UNION_INTERVAL; FINE_UNION]] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_UNION_NONZERO THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I
   [TAGGED_DIVISION_OF])) THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN
  REWRITE_TAC[IN_INTER; VECTOR_MUL_EQ_0] THEN STRIP_TAC THEN DISJ1_TAC THEN
  SUBGOAL_THEN
   `(?a b:real^M. l = interval[a,b]) /\
    l SUBSET (interval[a,b] INTER {x | x$k <= c}) /\
    l SUBSET (interval[a,b] INTER {x | x$k >= c})`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[SET_RULE
   `s SUBSET t /\ s SUBSET u <=> s SUBSET (t INTER u)`] THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT; INTER_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUBSET_INTERIOR) THEN
  REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; CONTENT_EQ_0_INTERIOR] THEN
  MATCH_MP_TAC(SET_RULE `t = {} ==> s SUBSET t ==> s = {}`) THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY] THEN EXISTS_TAC `k:num` THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let INTEGRABLE_SPLIT = prove
 (`!f:real^M->real^N a b.
        f integrable_on (interval[a,b]) /\ 1 <= k /\ k <= dimindex(:M)
        ==> f integrable_on (interval[a,b] INTER {x | x$k <= c}) /\
            f integrable_on (interval[a,b] INTER {x | x$k >= c})`,
  let lemma = prove
   (`b - a = c
     ==> norm(a:real^N) < e / &2 ==> norm(b) < e / &2 ==> norm(c) < e`,
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM dist] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC DIST_TRIANGLE_HALF_L THEN
    EXISTS_TAC `vec 0:real^N` THEN
    ASM_REWRITE_TAC[dist; VECTOR_SUB_LZERO; VECTOR_SUB_RZERO; NORM_NEG]) in
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [integrable_on] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONJ_TAC THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT; INTEGRABLE_CAUCHY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `e / &2` o
    MATCH_MP HAS_INTEGRAL_SEPARATE_SIDES) THEN
  MAP_EVERY ABBREV_TAC
   [`b' = (lambda i. if i = k then min ((b:real^M)$k) c else b$i):real^M`;
    `a' = (lambda i. if i = k then max ((a:real^M)$k) c else a$i):real^M`] THEN
  ASM_SIMP_TAC[REAL_HALF; INTERVAL_SPLIT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FINE_DIVISION_EXISTS) THENL
   [DISCH_THEN(MP_TAC o SPECL [`a':real^M`; `b:real^M`]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[SWAP_FORALL_THM]);
    DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `b':real^M`])] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^M#(real^M->bool))->bool`
    STRIP_ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`p:(real^M#(real^M->bool))->bool`;
                  `p1:(real^M#(real^M->bool))->bool`] th) THEN
    MP_TAC(SPECL [`p:(real^M#(real^M->bool))->bool`;
                  `p2:(real^M#(real^M->bool))->bool`] th)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC lemma THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Generalized notion of additivity.                                         *)
(* ------------------------------------------------------------------------- *)

let operative = new_definition
 `operative op (f:(real^N->bool)->A) <=>
    (!a b. content(interval[a,b]) = &0 ==> f(interval[a,b]) = neutral(op)) /\
    (!a b c k. 1 <= k /\ k <= dimindex(:N)
               ==> f(interval[a,b]) =
                   op (f(interval[a,b] INTER {x | x$k <= c}))
                      (f(interval[a,b] INTER {x | x$k >= c})))`;;

let OPERATIVE_TRIVIAL = prove
 (`!op f a b.
        operative op f /\ content(interval[a,b]) = &0
        ==> f(interval[a,b]) = neutral op`,
  REWRITE_TAC[operative] THEN MESON_TAC[]);;

let PROPERTY_EMPTY_INTERVAL = prove
 (`!P. (!a b:real^N. content(interval[a,b]) = &0 ==> P(interval[a,b]))
       ==> P {}`,
  MESON_TAC[EMPTY_AS_INTERVAL; CONTENT_EMPTY]);;

let OPERATIVE_EMPTY = prove
 (`!op f:(real^N->bool)->A. operative op f ==> f {} = neutral op`,
  REPEAT GEN_TAC THEN REWRITE_TAC[operative] THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP PROPERTY_EMPTY_INTERVAL o CONJUNCT1));;

(* ------------------------------------------------------------------------- *)
(* Using additivity of lifted function to encode definedness.                *)
(* ------------------------------------------------------------------------- *)

let FORALL_OPTION = prove
 (`(!x. P x) <=> P NONE /\ !x. P(SOME x)`,
  MESON_TAC[cases "option"]);;

let EXISTS_OPTION = prove
 (`(?x. P x) <=> P NONE \/ ?x. P(SOME x)`,
  MESON_TAC[cases "option"]);;

let lifted = define
 `(lifted op NONE _ = NONE) /\
  (lifted op _ NONE = NONE) /\
  (lifted op (SOME x) (SOME y) = SOME(op x y))`;;

let NEUTRAL_LIFTED = prove
 (`!op. monoidal op ==> neutral(lifted op) = SOME(neutral op)`,
  REWRITE_TAC[neutral; monoidal] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[FORALL_OPTION; lifted; distinctness "option";
              injectivity "option"] THEN
  ASM_MESON_TAC[]);;

let MONOIDAL_LIFTED = prove
 (`!op. monoidal op ==> monoidal(lifted op)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NEUTRAL_LIFTED; monoidal] THEN
  REWRITE_TAC[FORALL_OPTION; lifted; distinctness "option";
              injectivity "option"] THEN
  ASM_MESON_TAC[monoidal]);;

let ITERATE_SOME = prove
 (`!op. monoidal op
        ==> !f s. FINITE s
                  ==> iterate (lifted op) s (\x. SOME(f x)) =
                      SOME(iterate op s f)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_LIFTED; NEUTRAL_LIFTED] THEN
  REWRITE_TAC[lifted]);;

(* ------------------------------------------------------------------------- *)
(* Two key instances of additivity.                                          *)
(* ------------------------------------------------------------------------- *)

let OPERATIVE_CONTENT = prove
 (`operative(+) content`,
  REWRITE_TAC[operative; NEUTRAL_REAL_ADD; CONTENT_SPLIT]);;

let OPERATIVE_INTEGRAL = prove
 (`!f:real^M->real^N.
       operative(lifted(+))
         (\i. if f integrable_on i then SOME(integral i f) else NONE)`,
  SIMP_TAC[operative; NEUTRAL_LIFTED; MONOIDAL_VECTOR_ADD] THEN
  REWRITE_TAC[NEUTRAL_VECTOR_ADD] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[lifted; distinctness "option"; injectivity "option"] THENL
   [REWRITE_TAC[integral] THEN ASM_MESON_TAC[HAS_INTEGRAL_NULL_EQ];
    RULE_ASSUM_TAC(REWRITE_RULE[integrable_on]) THEN
    ASM_MESON_TAC[HAS_INTEGRAL_NULL];
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL)) THEN
    ASM_MESON_TAC[HAS_INTEGRAL_SPLIT; HAS_INTEGRAL_UNIQUE];
    ASM_MESON_TAC[INTEGRABLE_SPLIT; integrable_on];
    ASM_MESON_TAC[INTEGRABLE_SPLIT];
    ASM_MESON_TAC[INTEGRABLE_SPLIT];
    RULE_ASSUM_TAC(REWRITE_RULE[integrable_on]) THEN
    ASM_MESON_TAC[HAS_INTEGRAL_SPLIT]]);;

(* ------------------------------------------------------------------------- *)
(* Points of division of a partition.                                        *)
(* ------------------------------------------------------------------------- *)

let division_points = new_definition
 `division_points (k:real^N->bool) (d:(real^N->bool)->bool) =
    {j,x | 1 <= j /\ j <= dimindex(:N) /\
           (interval_lowerbound k)$j < x /\ x < (interval_upperbound k)$j /\
           ?i. i IN d /\
               ((interval_lowerbound i)$j = x \/
                (interval_upperbound i)$j = x)}`;;

let DIVISION_POINTS_FINITE = prove
 (`!d i:real^N->bool. d division_of i ==> FINITE(division_points i d)`,
  REWRITE_TAC[division_of; division_points] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONJ_ASSOC; GSYM IN_NUMSEG] THEN
  REWRITE_TAC[IN; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IN] FINITE_PRODUCT_DEPENDENT) THEN
  REWRITE_TAC[ETA_AX; FINITE_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN GEN_REWRITE_TAC LAND_CONV [GSYM IN] THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
   `IMAGE (\i:real^N->bool. (interval_lowerbound i)$j) d UNION
    IMAGE (\i:real^N->bool. (interval_upperbound i)$j) d` THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[IN]);;

let DIVISION_POINTS_SUBSET = prove
 (`!a b:real^N c d k.
        d division_of interval[a,b] /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i) /\
        1 <= k /\ k <= dimindex(:N) /\ a$k < c /\ c < b$k
        ==> division_points (interval[a,b] INTER {x | x$k <= c})
                            {l INTER {x | x$k <= c} | l |
                             l IN d /\ ~(l INTER {x | x$k <= c} = {})}
            SUBSET division_points (interval[a,b]) d /\
            division_points (interval[a,b] INTER {x | x$k >= c})
                            {l INTER {x | x$k >= c} | l |
                             l IN d /\ ~(l INTER {x | x$k >= c} = {})}
            SUBSET division_points (interval[a,b]) d`,
  REPEAT STRIP_TAC THEN
  (REWRITE_TAC[SUBSET; division_points; FORALL_PAIR_THM] THEN
   MAP_EVERY X_GEN_TAC [`j:num`; `x:real`] THEN
   REWRITE_TAC[IN_ELIM_PAIR_THM] THEN REWRITE_TAC[IN_ELIM_THM] THEN
   ASM_SIMP_TAC[INTERVAL_SPLIT; INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND;
                REAL_LT_IMP_LE] THEN
   ASM_SIMP_TAC[REAL_ARITH `a < c ==> max a c = c`;
                REAL_ARITH `c < b ==> min b c = c`] THEN
   REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; LAMBDA_BETA;
     REAL_LT_IMP_LE; COND_ID;
     TAUT `(a <= if p then x else y) <=> (if p then a <= x else a <= y)`;
     TAUT `(if p then x else y) <= a <=> (if p then x <= a else y <= a)`] THEN
   REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
    [DISCH_THEN(K ALL_TAC) THEN REPEAT(POP_ASSUM MP_TAC) THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
   REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
   MATCH_MP_TAC MONO_EXISTS THEN
   ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
   REWRITE_TAC[UNWIND_THM2] THEN SIMP_TAC[GSYM CONJ_ASSOC] THEN
   ONCE_REWRITE_TAC[IMP_CONJ] THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
   MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
   ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
   SUBGOAL_THEN
    `!i. 1 <= i /\ i <= dimindex(:N) ==> (u:real^N)$i <= (v:real^N)$i`
   ASSUME_TAC THENL
    [REWRITE_TAC[GSYM INTERVAL_NE_EMPTY] THEN ASM_MESON_TAC[division_of];
     ALL_TAC] THEN
   REWRITE_TAC[INTERVAL_NE_EMPTY] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND] THEN
   ASM_SIMP_TAC[LAMBDA_BETA] THEN REPEAT(POP_ASSUM MP_TAC) THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC));;

let DIVISION_POINTS_PSUBSET = prove
 (`!a b:real^N c d k.
        d division_of interval[a,b] /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i) /\
        1 <= k /\ k <= dimindex(:N) /\ a$k < c /\ c < b$k /\
        (?l. l IN d /\
             (interval_lowerbound l$k = c \/ interval_upperbound l$k = c))
        ==> division_points (interval[a,b] INTER {x | x$k <= c})
                            {l INTER {x | x$k <= c} | l |
                             l IN d /\ ~(l INTER {x | x$k <= c} = {})}
            PSUBSET division_points (interval[a,b]) d /\
            division_points (interval[a,b] INTER {x | x$k >= c})
                            {l INTER {x | x$k >= c} | l |
                             l IN d /\ ~(l INTER {x | x$k >= c} = {})}
            PSUBSET division_points (interval[a,b]) d`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[PSUBSET_MEMBER; DIVISION_POINTS_SUBSET] THENL
   [EXISTS_TAC `k,(interval_lowerbound l:real^N)$k`;
    EXISTS_TAC `k,(interval_lowerbound l:real^N)$k`;
    EXISTS_TAC `k,(interval_upperbound l:real^N)$k`;
    EXISTS_TAC `k,(interval_upperbound l:real^N)$k`] THEN
  ASM_REWRITE_TAC[division_points; IN_ELIM_PAIR_THM] THEN
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND; REAL_LT_IMP_LE] THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT; INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND;
               REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_ARITH `a < c ==> max a c = c`;
               REAL_ARITH `c < b ==> min b c = c`] THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; LAMBDA_BETA;
    REAL_LT_IMP_LE; COND_ID;
    TAUT `(a <= if p then x else y) <=> (if p then a <= x else a <= y)`;
    TAUT `(if p then x else y) <= a <=> (if p then x <= a else y <= a)`] THEN
  REWRITE_TAC[REAL_LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Preservation by divisions and tagged divisions.                           *)
(* ------------------------------------------------------------------------- *)

let OPERATIVE_DIVISION = prove
 (`!op d a b f:(real^N->bool)->A.
    monoidal op /\ operative op f /\ d division_of interval[a,b]
    ==> iterate(op) d f = f(interval[a,b])`,
  REPEAT GEN_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN WF_INDUCT_TAC
   `CARD (division_points (interval[a,b]:real^N->bool) d)` THEN
  POP_ASSUM(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `content(interval[a:real^N,b]) = &0` THENL
   [SUBGOAL_THEN `iterate op d (f:(real^N->bool)->A) = neutral op`
     (fun th -> ASM_MESON_TAC[th; operative]) THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
     ITERATE_EQ_NEUTRAL) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    ASM_MESON_TAC[operative; DIVISION_OF_CONTENT_0];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTENT_LT_NZ]) THEN
  REWRITE_TAC[CONTENT_POS_LT_EQ] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_CASES_TAC `division_points (interval[a,b]:real^N->bool) d = {}` THENL
   [DISCH_THEN(K ALL_TAC) THEN
    SUBGOAL_THEN
     `!i. i IN d
          ==> ?u v:real^N. i = interval[u,v] /\
                           !j. 1 <= j /\ j <= dimindex(:N)
                               ==> u$j = (a:real^N)$j /\ v$j = a$j \/
                                   u$j = (b:real^N)$j /\ v$j = b$j \/
                                   u$j = a$j /\ v$j = b$j`
    (LABEL_TAC "*") THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
      MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `interval[u:real^N,v]` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[INTERVAL_NE_EMPTY] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (ASSUME_TAC o CONJUNCT1)) THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `a <= u /\ u <= v /\ v <= b /\ ~(a < u /\ u < b \/ a < v /\ v < b)
        ==> u = a /\ v = a \/ u = b /\ v = b \/ u = a /\ v = b`) THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
      REWRITE_TAC[division_points; NOT_IN_EMPTY; FORALL_PAIR_THM] THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `interval[u:real^N,v]`) THEN
      ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND;
                   REAL_LT_IMP_LE] THEN
      DISCH_THEN(fun th ->
        MP_TAC(SPEC `(u:real^N)$j` th) THEN
        MP_TAC(SPEC `(v:real^N)$j` th)) THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `interval[a:real^N,b] IN d` MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      REWRITE_TAC[EXTENSION; IN_INTERVAL; IN_UNIONS] THEN
      DISCH_THEN(MP_TAC o SPEC `inv(&2) % (a + b:real^N)`) THEN
      MATCH_MP_TAC(TAUT `b /\ (a ==> c) ==> (a <=> b) ==> c`) THEN
      CONJ_TAC THENL
       [SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:real^N->bool`
       (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `i:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
      SIMP_TAC[IN_INTERVAL; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
      REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
      ASM_SIMP_TAC[REAL_ARITH
       `a < b
        ==> ((u = a /\ v = a \/ u = b /\ v = b \/ u = a /\ v = b) /\
             u <= inv(&2) * (a + b) /\ inv(&2) * (a +  b) <= v <=>
             u = a /\ v = b)`] THEN
      ASM_MESON_TAC[CART_EQ];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (SET_RULE
     `a IN d ==> d = a INSERT (d DELETE a)`)) THEN
    ASM_SIMP_TAC[ITERATE_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
    SUBGOAL_THEN
     `iterate op (d DELETE interval[a,b]) (f:(real^N->bool)->A) = neutral op`
     (fun th -> ASM_MESON_TAC[th; monoidal]) THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
     ITERATE_EQ_NEUTRAL) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `l:real^N->bool` THEN
    REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    SUBGOAL_THEN `content(l:real^N->bool) = &0`
     (fun th -> ASM_MESON_TAC[th; operative]) THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `l:real^N->bool`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    UNDISCH_TAC `~(interval[u:real^N,v] = interval[a,b])` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> AP_TERM_TAC THEN MP_TAC th) THEN
    REWRITE_TAC[CONS_11; PAIR_EQ; CART_EQ; CONTENT_EQ_0] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [TAUT `a ==> b <=> ~a \/ b`] THEN
    REWRITE_TAC[NOT_FORALL_THM; OR_EXISTS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM; AND_FORALL_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `1 <= j /\ j <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [division_points] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`whatever:num#real`; `k:num`; `c:real`] THEN
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND; REAL_LT_IMP_LE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real`; `d:(real^N->bool)->bool`;
        `k:num`] DIVISION_POINTS_PSUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN
   (MP_TAC o MATCH_MP (REWRITE_RULE [IMP_CONJ] CARD_PSUBSET))) THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `k:num`;
                 `c:real`]
      DIVISION_SPLIT) THEN
  ASM_SIMP_TAC[DIVISION_POINTS_FINITE] THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
  ASM_SIMP_TAC[REAL_ARITH `a < c ==> max a c = c`;
               REAL_ARITH `c < b ==> min b c = c`] THEN
  MAP_EVERY ABBREV_TAC
   [`d1:(real^N->bool)->bool =
     {l INTER {x | x$k <= c} | l | l IN d /\ ~(l INTER {x | x$k <= c} = {})}`;
    `d2:(real^N->bool)->bool =
     {l INTER {x | x$k >= c} | l | l IN d /\ ~(l INTER {x | x$k >= c} = {})}`;
    `cb:real^N = (lambda i. if i = k then c else (b:real^N)$i)`;
    `ca:real^N = (lambda i. if i = k then c else (a:real^N)$i)`] THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN DISCH_THEN(fun th ->
   MP_TAC(SPECL [`a:real^N`; `cb:real^N`; `d1:(real^N->bool)->bool`] th) THEN
   MP_TAC(SPECL [`ca:real^N`; `b:real^N`; `d2:(real^N->bool)->bool`] th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `op (iterate op d1 (f:(real^N->bool)->A))
                 (iterate op d2 (f:(real^N->bool)->A))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [operative]) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `c:real`; `k:num`]) THEN
    ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
    ASM_SIMP_TAC[REAL_ARITH `a < c ==> max a c = c`;
                 REAL_ARITH `c < b ==> min b c = c`];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `op (iterate op d (\l. f(l INTER {x | x$k <= c}):A))
       (iterate op d (\l. f(l INTER {x:real^N | x$k >= c})))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[GSYM ITERATE_OP] THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
     ITERATE_EQ) THEN
    ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION
     (ASSUME `d division_of interval[a:real^N,b]`)] THEN
    ASM_MESON_TAC[operative]] THEN
  MAP_EVERY EXPAND_TAC ["d1"; "d2"] THEN BINOP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  MATCH_MP_TAC ITERATE_NONZERO_IMAGE_LEMMA THEN ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[OPERATIVE_EMPTY]; ALL_TAC] THEN
   MAP_EVERY X_GEN_TAC [`l:real^N->bool`; `m:real^N->bool`] THEN STRIP_TAC THEN
   MATCH_MP_TAC(MESON[OPERATIVE_TRIVIAL]
    `operative op f /\ (?a b. l = interval[a,b]) /\ content l = &0
     ==> f l = neutral op`) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [ALL_TAC; ASM_MESON_TAC[DIVISION_SPLIT_LEFT_INJ;
                                 DIVISION_SPLIT_RIGHT_INJ]] THEN
   SUBGOAL_THEN `?a b:real^N. m = interval[a,b]` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
   ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MESON_TAC[]));;

let OPERATIVE_TAGGED_DIVISION = prove
 (`!op d a b f:(real^N->bool)->A.
    monoidal op /\ operative op f /\ d tagged_division_of interval[a,b]
    ==> iterate(op) d (\(x,l). f l) = f(interval[a,b])`,
  let lemma = prove
   (`(\(x,l). f l) = (f o SND)`,
    REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `iterate op (IMAGE SND (d:(real^N#(real^N->bool)->bool))) f :A` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[DIVISION_OF_TAGGED_DIVISION; OPERATIVE_DIVISION]] THEN
  REWRITE_TAC[lemma] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
               ITERATE_IMAGE_NONZERO) THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF_FINITE]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT1 o CONJUNCT2)) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[INTER_ACI] THEN
  ASM_MESON_TAC[CONTENT_EQ_0_INTERIOR; OPERATIVE_TRIVIAL;
                TAGGED_DIVISION_OF]);;

(* ------------------------------------------------------------------------- *)
(* Additivity of content.                                                    *)
(* ------------------------------------------------------------------------- *)

let ADDITIVE_CONTENT_DIVISION = prove
 (`!d a b:real^N.
    d division_of interval[a,b]
    ==> sum d content = content(interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
   (MATCH_MP
     (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                  OPERATIVE_DIVISION)
     (CONJ MONOIDAL_REAL_ADD OPERATIVE_CONTENT))) THEN
  REWRITE_TAC[sum]);;

let ADDITIVE_CONTENT_TAGGED_DIVISION = prove
 (`!d a b:real^N.
    d tagged_division_of interval[a,b]
    ==> sum d (\(x,l). content l) = content(interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
   (MATCH_MP
     (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                  OPERATIVE_TAGGED_DIVISION)
     (CONJ MONOIDAL_REAL_ADD OPERATIVE_CONTENT))) THEN
  REWRITE_TAC[sum]);;

let SUBADDITIVE_CONTENT_DIVISION = prove
 (`!d s a b:real^M.
        d division_of s /\ s SUBSET interval[a,b]
        ==> sum d content <= content(interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(real^M->bool)->bool`; `a:real^M`; `b:real^M`]
        PARTIAL_DIVISION_EXTEND_INTERVAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET] THEN
    ASM_MESON_TAC[division_of; DIVISION_OF_UNION_SELF; SUBSET_TRANS];
    DISCH_THEN(X_CHOOSE_THEN `p:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (p:(real^M->bool)->bool) content` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_MESON_TAC[division_of; CONTENT_POS_LE; IN_DIFF];
      ASM_MESON_TAC[ADDITIVE_CONTENT_DIVISION; REAL_LE_REFL]]]);;
