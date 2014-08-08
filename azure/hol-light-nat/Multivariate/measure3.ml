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
include Measure2

(* ------------------------------------------------------------------------- *)
(* Negligibility of a Lipschitz image of a negligible set.                   *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE = prove
 (`!f:real^M->real^N s.
        dimindex(:M) <= dimindex(:N) /\ negligible s /\
        (!x. x IN s
             ==> ?t b. open t /\ x IN t /\
                       !y. y IN s INTER t
                           ==> norm(f y - f x) <= b * norm(y - x))
        ==> negligible(IMAGE f s)`,
  let lemma = prove
   (`!f:real^M->real^N s B.
        dimindex(:M) <= dimindex(:N) /\ bounded s /\ negligible s /\ &0 < B /\
        (!x. x IN s
             ==> ?t. open t /\ x IN t /\
                     !y. y IN s INTER t
                         ==> norm(f y - f x) <= B * norm(y - x))
        ==> negligible(IMAGE f s)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[NEGLIGIBLE_OUTER] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^M->bool`;
                   `e / &2 / (&2 * B * &(dimindex(:M))) pow (dimindex(:N))`]
      MEASURABLE_OUTER_OPEN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[NEGLIGIBLE_IMP_MEASURABLE] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_HALF] THEN
      MATCH_MP_TAC REAL_POW_LT THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[DIMINDEX_GE_1; REAL_OF_NUM_LT; ARITH; LE_1];
      ALL_TAC] THEN
    ASM_SIMP_TAC[NEGLIGIBLE_IMP_MEASURABLE; REAL_HALF; MEASURE_EQ_0] THEN
    REWRITE_TAC[REAL_ADD_LID] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!x. ?r. &0 < r /\ r <= &1 / &2 /\
              (x IN s
               ==> !y. norm(y - x:real^M) < r
                       ==> y IN t /\
                           (y IN s
                            ==> norm(f y - f x:real^N) <= B * norm(y - x)))`
    MP_TAC THENL
     [X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `(x:real^M) IN s` THEN
      ASM_REWRITE_TAC[] THENL
       [ALL_TAC; EXISTS_TAC `&1 / &4` THEN REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPEC `t INTER u :real^M->bool` open_def) THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_INTER; dist]] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min (&1 / &2) r` THEN
      ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
      REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
      X_GEN_TAC `r:real^M->real` THEN STRIP_TAC] THEN
    SUBGOAL_THEN
     `?c. s SUBSET interval[--(vec c):real^M,vec c] /\
          ~(interval(--(vec c):real^M,vec c) = {})`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `abs c + &1` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      DISCH_TAC THEN REWRITE_TAC[SUBSET; INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[IN_INTERVAL; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
      STRIP_TAC THEN REWRITE_TAC[REAL_BOUNDS_LE] THEN W(MP_TAC o
        PART_MATCH lhand COMPONENT_LE_NORM o lhand o snd) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`--(vec c):real^M`; `(vec c):real^M`; `s:real^M->bool`;
                   `\x:real^M. ball(x,r x)`] COVERING_LEMMA) THEN
    ASM_REWRITE_TAC[gauge; OPEN_BALL; CENTRE_IN_BALL] THEN

    REWRITE_TAC[VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!k. k IN D
          ==> ?u v z. k = interval[u,v] /\ ~(interval(u,v) = {}) /\
                      z IN s /\ z IN interval[u,v] /\
                      interval[u:real^M,v] SUBSET ball(z,r z)`
    MP_TAC THENL
     [X_GEN_TAC `d:real^M->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^M. d = interval[u,v]` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^M` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^M` THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[SUBSET; INTERIOR_CLOSED_INTERVAL; IN_INTER];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`u:(real^M->bool)->real^M`; `v:(real^M->bool)->real^M`;
      `z:(real^M->bool)->real^M`] THEN
    DISCH_THEN(LABEL_TAC "*") THEN EXISTS_TAC
     `UNIONS(IMAGE (\d:real^M->bool.
         interval[(f:real^M->real^N)(z d) -
      (B * &(dimindex(:M)) *
      ((v(d):real^M)$1 - (u(d):real^M)$1)) % vec 1:real^N,
                  f(z d) +
                  (B * &(dimindex(:M)) * (v(d)$1 - u(d)$1)) % vec 1]) D)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^M) IN UNIONS D` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET]; REWRITE_TAC[UNIONS_IMAGE]] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `d:real^M->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:real^M) IN ball(z(d:real^M->bool),r(z d))` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET]; REWRITE_TAC[IN_BALL; dist]] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `y IN t /\
        norm((f:real^M->real^N) y - f(z d)) <= B * norm(y - z(d:real^M->bool))`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INTERVAL] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT] THEN
      REWRITE_TAC[REAL_ARITH
       `z - b <= y /\ y <= z + b <=> abs(y - z) <= b`] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN W(MP_TAC o
        PART_MATCH lhand COMPONENT_LE_NORM o lhand o snd) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      REWRITE_TAC[VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          REAL_LE_TRANS)) THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
      W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
       [GSYM CARD_NUMSEG_1] THEN
      SIMP_TAC[GSYM SUM_CONST; FINITE_NUMSEG] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `((v:(real^M->bool)->real^M) d - u d)$j` THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `y IN interval[(u:(real^M->bool)->real^M) d,v d] /\
                      (z d) IN interval[u d,v d]`
        MP_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[IN_INTERVAL]] THEN
        DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `j:num`)) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN FIRST_X_ASSUM(MP_TAC o SPECL
         [`(u:(real^M->bool)->real^M) d`; `(v:(real^M->bool)->real^M) d`]) THEN
        ASM_MESON_TAC[DIMINDEX_GE_1; LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[]
     `(x <= e / &2 ==> x < e) /\ P /\ x <= e / &2 ==> P /\ x < e`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_GEN THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE; MEASURABLE_INTERVAL] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
    X_GEN_TAC `D':(real^M->bool)->bool` THEN STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_LE o lhand o snd) THEN
    ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_INTERVAL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * B * &(dimindex(:M))) pow (dimindex(:N)) *
                sum D' (\d:real^M->bool. measure d)` THEN
    SUBGOAL_THEN `FINITE(D':(real^M->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
      ASM_REWRITE_TAC[MEASURE_INTERVAL] THEN X_GEN_TAC `d:real^M->bool` THEN
      DISCH_TAC THEN REWRITE_TAC[CONTENT_CLOSED_INTERVAL_CASES] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; REAL_ARITH
       `(a - x <= a + x <=> &0 <= x) /\ (a + x) - (a - x) = &2 * x`] THEN
      REWRITE_TAC[VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_LE_MUL_EQ; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1] THEN
      SUBGOAL_THEN `d = interval[u d:real^M,v d]`
       (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])
      THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
      SUBGOAL_THEN
       `!i. 1 <= i /\ i <= dimindex(:M)
            ==> ((u:(real^M->bool)->real^M) d)$i <= (v d:real^M)$i`
      MP_TAC THENL
       [ASM_MESON_TAC[SUBSET; INTERVAL_NE_EMPTY; REAL_LT_IMP_LE]; ALL_TAC] THEN
      SIMP_TAC[REAL_SUB_LE; DIMINDEX_GE_1; LE_REFL] THEN DISCH_TAC THEN
      REWRITE_TAC[PRODUCT_CONST_NUMSEG; REAL_POW_MUL] THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH;
                   GSYM REAL_MUL_ASSOC; ADD_SUB; DIMINDEX_GE_1; LE_1] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `((v d:real^M)$1 - ((u:(real^M->bool)->real^M) d)$1)
                  pow (dimindex(:M))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO_INV THEN
        ASM_SIMP_TAC[REAL_SUB_LE; DIMINDEX_GE_1; LE_REFL] THEN
        REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
        MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN W(MP_TAC o
          PART_MATCH lhand COMPONENT_LE_NORM o lhand o snd) THEN
        REWRITE_TAC[DIMINDEX_GE_1; LE_REFL] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
        MATCH_MP_TAC(NORM_ARITH
         `!z r. norm(z - u) < r /\ norm(z - v) < r /\ r <= &1 / &2
                ==> norm(v - u:real^M) <= &1`) THEN
        MAP_EVERY EXISTS_TAC
         [`(z:(real^M->bool)->real^M) d`;
          `r((z:(real^M->bool)->real^M) d):real`] THEN
        ASM_REWRITE_TAC[GSYM dist; GSYM IN_BALL] THEN
        SUBGOAL_THEN
         `(u:(real^M->bool)->real^M) d IN interval[u d,v d] /\
          (v:(real^M->bool)->real^M) d IN interval[u d,v d]`
        MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET]] THEN
        ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY];
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
        SIMP_TAC[GSYM PRODUCT_CONST; FINITE_NUMSEG] THEN
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`(u:(real^M->bool)->real^M) d`; `(v:(real^M->bool)->real^M) d`]) THEN
        ASM_MESON_TAC[DIMINDEX_GE_1; LE_REFL; SUBSET]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&2 * B * &(dimindex(:M))) pow dimindex(:N) *
                  measure(t:real^M->bool)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_IMP_LE; ALL_TAC];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        W(MP_TAC o PART_MATCH (rand o rand) REAL_LT_RDIV_EQ o snd)] THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; LE_1; DIMINDEX_GE_1;
                   REAL_ARITH `&0 < &2 * B <=> &0 < B`; REAL_OF_NUM_LT] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `measure(UNIONS D':real^M->bool)` THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`D':(real^M->bool)->bool`; `UNIONS D':real^M->bool`]
          MEASURE_ELEMENTARY) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[division_of] THEN
          CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET]] THEN
          GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
           [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET; INTERIOR_EMPTY]];
          DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
          MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[MEASURE_INTERVAL; SUBSET]];
        MATCH_MP_TAC MEASURE_SUBSET THEN CONJ_TAC THENL
         [MATCH_MP_TAC MEASURABLE_UNIONS THEN
          ASM_MESON_TAC[MEASURABLE_INTERVAL; SUBSET];
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `UNIONS D:real^M->bool` THEN
          ASM_SIMP_TAC[SUBSET_UNIONS] THEN
          REWRITE_TAC[SUBSET; FORALL_IN_UNIONS] THEN
          X_GEN_TAC `d:real^M->bool` THEN
          REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
          DISCH_TAC THEN REWRITE_TAC[GSYM SUBSET] THEN
          SUBGOAL_THEN `d SUBSET ball(z d:real^M,r(z d))` MP_TAC THENL
           [ASM_MESON_TAC[];
            REWRITE_TAC[SUBSET; IN_BALL; dist] THEN
            ASM_MESON_TAC[NORM_SUB]]]]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `s = UNIONS
    {{x | x IN s /\ norm(x:real^M) <= &n /\
          ?t. open t /\ x IN t /\
              !y. y IN s INTER t
                  ==> norm(f y - f x:real^N) <= (&n + &1) * norm(y - x)} |
     n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:real^M` THEN
    ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `t:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `max (norm(x:real^M)) b` REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[REAL_MAX_LE] THEN
    X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `b * norm(y - x:real^M)` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IMAGE_UNIONS] THEN
    MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[GSYM IMAGE_o; COUNTABLE_IMAGE; NUM_COUNTABLE] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_UNIV] THEN
    MATCH_MP_TAC lemma THEN EXISTS_TAC `&n + &1` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `cball(vec 0:real^M,&n)` THEN
      SIMP_TAC[BOUNDED_CBALL; SUBSET; IN_CBALL_0; IN_ELIM_THM];
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN MESON_TAC[]]]);;

let NEGLIGIBLE_LIPSCHITZ_IMAGE_UNIV = prove
 (`!f:real^N->real^N s B.
        negligible s /\ (!x y. norm(f x - f y) <= B * norm(x - y))
        ==> negligible(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE THEN
  ASM_REWRITE_TAC[LE_REFL] THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`interval(a - vec 1:real^N,a + vec 1)`; `B:real`] THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL] THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE = prove
 (`!f:real^M->real^N s.
        dimindex(:M) <= dimindex(:N) /\ negligible s /\ f differentiable_on s
        ==> negligible(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [differentiable_on]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_REWRITE_TAC[differentiable; HAS_DERIVATIVE_WITHIN_ALT] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LINEAR_BOUNDED_POS) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(x:real^M,d)` THEN EXISTS_TAC `B + &1` THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  REWRITE_TAC[IN_BALL; dist; REAL_ADD_RDISTRIB] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(NORM_ARITH
   `!d. norm(y - x - d:real^N) <= z /\ norm(d) <= b
        ==> norm(y - x) <= b + z`) THEN
  EXISTS_TAC `(f':real^M->real^N)(y - x)` THEN
  ASM_MESON_TAC[NORM_SUB]);;

let NEGLIGIBLE_DIFFERENTIABLE_IMAGE_LOWDIM = prove
 (`!f:real^M->real^N s.
        dimindex(:M) < dimindex(:N) /\ f differentiable_on s
        ==> negligible(IMAGE f s)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP
   (ARITH_RULE `m < n ==> !x:num. x <= m ==> x <= n`)) THEN
  SUBGOAL_THEN
   `(f:real^M->real^N) =
    (f o ((\x. lambda i. x$i):real^N->real^M)) o
    ((\x. lambda i. if i <= dimindex(:M) then x$i else &0):real^M->real^N)`
  SUBST1_TAC THENL
   [SIMP_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA];
    ONCE_REWRITE_TAC[IMAGE_o] THEN
    MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE THEN
    REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{y:real^N | y$(dimindex(:N)) = &0}` THEN
      SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE; LE_REFL; DIMINDEX_GE_1] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[LAMBDA_BETA; LE_REFL; DIMINDEX_GE_1] THEN
      ASM_REWRITE_TAC[GSYM NOT_LT];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [differentiable_on]) THEN
      REWRITE_TAC[differentiable_on; FORALL_IN_IMAGE] THEN STRIP_TAC THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_WITHIN THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_LINEAR THEN
        SIMP_TAC[linear; LAMBDA_BETA; CART_EQ;
                 VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT];
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN BINOP_TAC THENL
         [AP_TERM_TAC;
          MATCH_MP_TAC(SET_RULE
           `(!x. f(g x) = x) ==> s = IMAGE f (IMAGE g s)`)] THEN
        ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA]]]]);;

(* ------------------------------------------------------------------------- *)
(* Simplest case of Sard's theorem (we don't need continuity of derivative). *)
(* ------------------------------------------------------------------------- *)

let BABY_SARD = prove
 (`!f:real^M->real^N f' s.
        dimindex(:M) <= dimindex(:N) /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x within s) /\
                 rank(matrix(f' x)) < dimindex(:N))
        ==> negligible(IMAGE f s)`,
  let lemma = prove
   (`!p w e m.
      dim p < dimindex(:N) /\ &0 <= m /\ &0 <= e
      ==> ?s. measurable s /\
              {z:real^N | norm(z - w) <= m /\
                          ?t. t IN p /\ norm(z - w - t) <= e}
              SUBSET s /\
              measure s <= (&2 * e) * (&2 * m) pow (dimindex(:N) - 1)`,
    REPEAT GEN_TAC THEN GEN_GEOM_ORIGIN_TAC `w:real^N` ["t"; "p"] THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LOWDIM_SUBSET_HYPERPLANE) THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `a:real^N` THEN GEOM_BASIS_MULTIPLE_TAC 1 `a:real^N` THEN
    X_GEN_TAC `a:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC `a = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC
     `interval[--(lambda i. if i = 1 then e else m):real^N,
               (lambda i. if i = 1 then e else m)]` THEN
    REWRITE_TAC[MEASURABLE_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL] THEN
      SIMP_TAC[VECTOR_NEG_COMPONENT; LAMBDA_BETA] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
      REWRITE_TAC[REAL_BOUNDS_LE] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      COND_CASES_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
      ASM_SIMP_TAC[SPAN_SUPERSET; IN_ELIM_THM; DOT_BASIS; DOT_LMUL;
                   DIMINDEX_GE_1; LE_REFL; REAL_ENTIRE; REAL_LT_IMP_NZ] THEN
      MP_TAC(ISPECL [`x - y:real^N`; `1`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; ARITH; DIMINDEX_GE_1] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
      SIMP_TAC[VECTOR_NEG_COMPONENT; LAMBDA_BETA] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS] THEN
      REWRITE_TAC[REAL_ARITH `x - --x = &2 * x`] THEN
      SIMP_TAC[PRODUCT_CLAUSES_LEFT; DIMINDEX_GE_1] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN
      SIMP_TAC[ARITH; ARITH_RULE `2 <= n ==> ~(n = 1)`] THEN
      SIMP_TAC[PRODUCT_CONST_NUMSEG; DIMINDEX_GE_1; REAL_LE_REFL; ARITH_RULE
       `1 <= n ==> (n + 1) - 2 = n - 1`]]) in
  let semma = prove
   (`!f:real^M->real^N f' s B.
          dimindex(:M) <= dimindex(:N) /\ &0 < B /\ bounded s /\
          (!x. x IN s ==> (f has_derivative f' x) (at x within s) /\
                         rank(matrix(f' x)) < dimindex(:N) /\ onorm(f' x) <= B)
          ==> negligible(IMAGE f s)`,
    REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `!x. x IN s ==> linear((f':real^M->real^M->real^N) x)`
    ASSUME_TAC THENL [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?c. s SUBSET interval(--(vec c):real^M,vec c) /\
            ~(interval(--(vec c):real^M,vec c) = {})`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `abs c + &1` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      DISCH_TAC THEN REWRITE_TAC[SUBSET; INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[IN_INTERVAL; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
      STRIP_TAC THEN REWRITE_TAC[REAL_BOUNDS_LT] THEN W(MP_TAC o
        PART_MATCH lhand COMPONENT_LE_NORM o lhand o snd) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INTERVAL_NE_EMPTY]) THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN
    REWRITE_TAC[VEC_COMPONENT; DIMINDEX_GE_1;
                LE_REFL; VECTOR_NEG_COMPONENT] THEN
    REWRITE_TAC[REAL_ARITH `--x < x <=> &0 < &2 * x`; REAL_OF_NUM_MUL] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `?d. &0 < d /\ d <= B /\
          (d * &2) * (&4 * B) pow (dimindex(:N) - 1) <=
          e / &(2 * c) pow dimindex(:M) / &(dimindex(:M)) pow dimindex(:M)`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC
       `min B (e / &(2 * c) pow dimindex(:M) /
               &(dimindex(:M)) pow dimindex(:M) /
               (&4 * B) pow (dimindex(:N) - 1) / &2)` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; REAL_ARITH `min x y <= x`] THEN
      CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; DIMINDEX_GE_1; LE_1;
                     REAL_ARITH `&0 < &4 * B <=> &0 < B`; ARITH];
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_POW_LT;
                     REAL_ARITH `&0 < &4 * B <=> &0 < B`; ARITH] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. ?r. &0 < r /\ r <= &1 / &2 /\
              (x IN s
               ==> !y. y IN s /\ norm(y - x) < r
                       ==> norm((f:real^M->real^N) y - f x - f' x (y - x)) <=
                           d * norm(y - x))`
    MP_TAC THENL
     [X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `(x:real^M) IN s` THEN
      ASM_REWRITE_TAC[] THENL
       [ALL_TAC; EXISTS_TAC `&1 / &4` THEN REAL_ARITH_TAC] THEN
      UNDISCH_THEN
       `!x. x IN s ==> ((f:real^M->real^N) has_derivative f' x) (at x within s)`
       (MP_TAC o REWRITE_RULE[HAS_DERIVATIVE_WITHIN_ALT]) THEN
      ASM_SIMP_TAC[RIGHT_IMP_FORALL_THM] THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `d:real`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min r (&1 / &2)` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_MESON_TAC[];
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
      X_GEN_TAC `r:real^M->real` THEN REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
      REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(LABEL_TAC "*")] THEN
    MP_TAC(ISPECL [`--(vec c):real^M`; `(vec c):real^M`; `s:real^M->bool`;
                   `\x:real^M. ball(x,r x)`] COVERING_LEMMA) THEN
    ASM_REWRITE_TAC[gauge; OPEN_BALL; CENTRE_IN_BALL] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS; INTERVAL_OPEN_SUBSET_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!k:real^M->bool.
          k IN D
          ==> ?t. measurable(t) /\
                  IMAGE (f:real^M->real^N) (k INTER s) SUBSET t /\
                  measure t <= e / &(2 * c) pow (dimindex(:M)) * measure(k)`
    MP_TAC THENL
     [X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
       (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?x:real^M. x IN (s INTER interval[u,v]) /\
                               interval[u,v] SUBSET ball(x,r x)`
      MP_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[IN_INTER]] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`IMAGE ((f':real^M->real^M->real^N) x) (:real^M)`;
               `(f:real^M->real^N) x`;
                 `d * norm(v - u:real^M)`;
                 `(&2 * B) * norm(v - u:real^M)`]
          lemma) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; NORM_POS_LE; REAL_LT_IMP_LE] THEN
        MP_TAC(ISPEC `matrix ((f':real^M->real^M->real^N) x)`
          RANK_DIM_IM) THEN
        ASM_SIMP_TAC[MATRIX_WORKS] THEN REWRITE_TAC[ETA_AX] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN
      REPEAT(MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
        REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `y:real^M` THEN
        REWRITE_TAC[IN_INTER; EXISTS_IN_IMAGE; IN_UNIV] THEN
        STRIP_TAC THEN REMOVE_THEN "*"
         (MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC[IN_BALL; SUBSET; NORM_SUB; dist]; ALL_TAC] THEN
        DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
         [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC(NORM_ARITH
           `norm(z) <= B /\ d <= B
            ==> norm(y - x - z:real^N) <= d
                ==> norm(y - x) <= &2 * B`) THEN
          CONJ_TAC THENL
           [MP_TAC(ISPEC `(f':real^M->real^M->real^N) x` ONORM) THEN
            ASM_SIMP_TAC[] THEN
            DISCH_THEN(MP_TAC o SPEC `y - x:real^M` o CONJUNCT1) THEN
            MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
            MATCH_MP_TAC REAL_LE_MUL2 THEN
            ASM_SIMP_TAC[ONORM_POS_LE; NORM_POS_LE];
            MATCH_MP_TAC REAL_LE_MUL2 THEN
            ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE]];
          DISCH_THEN(fun th -> EXISTS_TAC `y - x:real^M` THEN MP_TAC th) THEN
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
          ASM_SIMP_TAC[REAL_LE_LMUL_EQ]] THEN
        MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL])) THEN
        REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
        MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
        REWRITE_TAC[REAL_ARITH `&2 * (&2 * B) * n = (&4 * B) * n`] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_POW_MUL] THEN
        SIMP_TAC[REAL_ARITH `(&2 * d * n) * a * b = d * &2 * a * (n * b)`] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
        SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> SUC(n - 1) = n`] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `e / &(2 * c) pow (dimindex(:M)) /
                    (&(dimindex(:M)) pow dimindex(:M)) *
                    norm(v - u:real^M) pow dimindex(:N)` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          ASM_SIMP_TAC[NORM_POS_LE; REAL_POW_LE];
          ALL_TAC] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [real_div] THEN
        REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_LT_IMP_LE] THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
        SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT;
                 LE_1; DIMINDEX_GE_1] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm(v - u:real^M) pow dimindex(:M)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
          SUBGOAL_THEN `u IN ball(x:real^M,r x) /\ v IN ball(x,r x)` MP_TAC
          THENL
           [ASM_MESON_TAC[SUBSET; ENDS_IN_INTERVAL; INTERIOR_EMPTY];
            REWRITE_TAC[IN_BALL] THEN
            SUBGOAL_THEN `(r:real^M->real) x <= &1 / &2` MP_TAC THENL
              [ASM_REWRITE_TAC[]; CONV_TAC NORM_ARITH]];
          REMOVE_THEN "*" (K ALL_TAC) THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^M`; `v:real^M`]) THEN
          ASM_REWRITE_TAC[REAL_ARITH `x - --x = &2 * x`] THEN
          REWRITE_TAC[LEFT_IMP_EXISTS_THM; REAL_OF_NUM_MUL] THEN
          X_GEN_TAC `p:num` THEN DISCH_TAC THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `(sum(1..dimindex(:M)) (\i. abs((v - u:real^M)$i)))
                      pow (dimindex(:M))` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_POW_LE2 THEN SIMP_TAC[NORM_POS_LE; NORM_LE_L1];
            REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
            GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
             [GSYM REAL_SUB_LE] THEN
            ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_LT_POW2] THEN
            ASM_SIMP_TAC[SUM_CONST_NUMSEG; PRODUCT_CONST_NUMSEG;
                         VECTOR_SUB_COMPONENT; ADD_SUB] THEN
            REWRITE_TAC[REAL_POW_MUL; REAL_MUL_SYM] THEN
            MATCH_MP_TAC REAL_EQ_IMP_LE THEN BINOP_TAC THEN REWRITE_TAC[] THEN
            AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[REAL_ABS_REFL] THEN
            ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_LT_POW2]]]];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `g:(real^M->bool)->(real^N->bool)` THEN DISCH_TAC THEN
      EXISTS_TAC `UNIONS (IMAGE (g:(real^M->bool)->(real^N->bool)) D)` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
      ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
      ONCE_REWRITE_TAC[CONJ_SYM] THEN
      REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
      X_GEN_TAC `D':(real^M->bool)->bool` THEN STRIP_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE_IMAGE o
        lhand o snd) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `sum D' (\k:real^M->bool.
                  e / &(2 * c) pow (dimindex(:M)) * measure k)` THEN CONJ_TAC
      THENL [MATCH_MP_TAC SUM_LE THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[SUM_LMUL] THEN
      REWRITE_TAC[REAL_ARITH `e / b * x:real = (e * x) / b`] THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_LE_LDIV_EQ; REAL_LE_LMUL_EQ] THEN
      MP_TAC(ISPECL [`D':(real^M->bool)->bool`; `UNIONS D':real^M->bool`]
              MEASURE_ELEMENTARY) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[division_of] THEN
        CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET]] THEN
        GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
         [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET; INTERIOR_EMPTY]];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `y = z /\ x <= e ==> x = y ==> z <= e`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[MEASURE_INTERVAL; SUBSET];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `measure(interval[--(vec c):real^M,vec c])` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURE_SUBSET THEN REWRITE_TAC[MEASURABLE_INTERVAL] THEN
        CONJ_TAC THENL [MATCH_MP_TAC MEASURABLE_UNIONS; ASM SET_TAC[]] THEN
        ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL];
        SIMP_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
        REWRITE_TAC[VEC_COMPONENT; VECTOR_NEG_COMPONENT; REAL_ARITH
         `x - --x = &2 * x /\ (--x <= x <=> &0 <= &2 * x)`] THEN
        ASM_SIMP_TAC[REAL_OF_NUM_MUL; REAL_LT_IMP_LE] THEN
        REWRITE_TAC[PRODUCT_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `s = UNIONS
    {{x | x IN s /\ norm(x:real^M) <= &n /\
          onorm((f':real^M->real^M->real^N) x) <= &n} |
     n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:real^M` THEN
    ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_MAX_LE; REAL_ARCH_SIMPLE];
    REWRITE_TAC[IMAGE_UNIONS] THEN
    MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[GSYM IMAGE_o; COUNTABLE_IMAGE; NUM_COUNTABLE] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_UNIV] THEN
    MATCH_MP_TAC semma THEN
    MAP_EVERY EXISTS_TAC [`f':real^M->real^M->real^N`; `&n + &1:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `cball(vec 0:real^M,&n)` THEN
      SIMP_TAC[BOUNDED_CBALL; SUBSET; IN_CBALL_0; IN_ELIM_THM];
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_ARITH `x <= n ==> x <= n + &1`] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_DERIVATIVE_WITHIN_SUBSET)) THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Also negligibility of BV low-dimensional image.                           *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_IMAGE_BOUNDED_VARIATION_INTERVAL = prove
 (`!f:real^1->real^N a b.
        2 <= dimindex(:N) /\ f has_bounded_variation_on interval[a,b]
        ==> negligible(IMAGE f (interval[a,b]))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HAS_BOUNDED_VECTOR_VARIATION_RIGHT_LIMIT)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HAS_BOUNDED_VECTOR_VARIATION_LEFT_LIMIT)) THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `l:real^1->real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `r:real^1->real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN X_GEN_TAC `ee:real` THEN DISCH_TAC THEN
  ABBREV_TAC
   `e = min (&1) (ee /
     (&2 pow (dimindex(:N)) *
      vector_variation (interval[a,b]) (f:real^1->real^N) + &1))` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < min (&1) x`) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[VECTOR_VARIATION_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. ?d. &0 < d /\
            (c IN interval[a,b]
             ==> (!x. x IN interval[a,c] /\ ~(x = c) /\ dist(x,c) < d
                      ==> dist((f:real^1->real^N) x,l c) < e) /\
                 (!x. x IN interval[c,b] /\ ~(x = c) /\ dist(x,c) < d
                      ==> dist(f x,r c) < e))`
  MP_TAC THENL
   [X_GEN_TAC `c:real^1` THEN ASM_CASES_TAC `(c:real^1) IN interval[a,b]` THENL
     [ALL_TAC; EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01]] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `c:real^1`)) THEN
    ASM_REWRITE_TAC[LIM_WITHIN; IMP_IMP; AND_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[GSYM DIST_NZ] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `min d1 d2:real` THEN ASM_SIMP_TAC[REAL_LT_MIN];
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:real^1->real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))] THEN
  MP_TAC(ISPECL [`\x:real^1. ball(x,d x)`; `a:real^1`; `b:real^1`]
    FINE_DIVISION_EXISTS) THEN
  ASM_REWRITE_TAC[fine; gauge; OPEN_BALL; CENTRE_IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `p:(real^1#(real^1->bool))->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  EXISTS_TAC
   `UNIONS(IMAGE (\(c,k).
       (f c) INSERT
       (cball((l:real^1->real^N) c,
              min e (vector_variation (interval[interval_lowerbound k,c])
                                      (f:real^1->real^N))) UNION
        cball((r:real^1->real^N) c,
              min e (vector_variation (interval[c,interval_upperbound k])
                                      (f:real^1->real^N))))) p)` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP TAGGED_DIVISION_UNION_IMAGE_SND) THEN
    REWRITE_TAC[IMAGE_UNIONS; GSYM IMAGE_o] THEN
    MATCH_MP_TAC UNIONS_MONO_IMAGE THEN
    REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:real^1`; `k:real^1->bool`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `?u v:real^1. k = interval[u,v]`
     (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
    SUBGOAL_THEN `drop u <= drop v` ASSUME_TAC THENL
     [ASM_MESON_TAC[TAGGED_DIVISION_OF; INTERVAL_NE_EMPTY_1; NOT_IN_EMPTY];
      ASM_SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^1`; `interval[u:real^1,v]`]) THEN
    ASM_REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_CBALL] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_INSERT; IN_UNION] THEN ASM_CASES_TAC `x:real^1 = c` THEN
    ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    SIMP_TAC[IN_CBALL; REAL_LE_MIN] THEN ASM_CASES_TAC `drop x <= drop c` THENL
     [DISJ1_TAC THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[DIST_SYM] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        REMOVE_THEN "*" (MP_TAC o SPEC `c:real^1`) THEN ANTS_TAC THENL
         [ASM_MESON_TAC[TAGGED_DIVISION_OF; SUBSET]; ALL_TAC] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GSYM(ONCE_REWRITE_RULE[DIST_SYM] IN_BALL)] THEN
        ASM_MESON_TAC[IN_INTERVAL_1; SUBSET; TAGGED_DIVISION_OF];
        ALL_TAC] THEN
      SUBGOAL_THEN `drop a <= drop u /\ drop x < drop c /\
                    drop c <= drop v /\ drop v <= drop b`
      STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_LT_LE; DROP_EQ] THEN
        ASM_MESON_TAC[IN_INTERVAL_1; SUBSET; TAGGED_DIVISION_OF;
                      REAL_LE_TOTAL];
        ALL_TAC] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[NORM_SUB] dist] THEN
      MATCH_MP_TAC
       (REWRITE_RULE[LIFT_DROP; FORALL_LIFT]
          (ISPEC `at c within interval [u:real^1,c]` LIM_DROP_UBOUND)) THEN
      EXISTS_TAC `\y:real^1. lift(norm(f x - f y:real^N))` THEN
      REWRITE_TAC[TRIVIAL_LIMIT_WITHIN; LIFT_DROP] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC LIM_NORM THEN MATCH_MP_TAC LIM_SUB THEN
        ASM_SIMP_TAC[IN_INTERVAL_1; LIM_CONST] THEN
        MATCH_MP_TAC LIM_WITHIN_SUBSET THEN
        EXISTS_TAC `interval[a:real^1,c]` THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
          ASM_REAL_ARITH_TAC;
          REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC];
        W(MP_TAC o PART_MATCH (lhs o rand) LIMPT_OF_CONVEX o snd) THEN
        ANTS_TAC THENL
         [SIMP_TAC[CONVEX_INTERVAL; ENDS_IN_INTERVAL;
                   INTERVAL_NE_EMPTY_1] THEN
          ASM_REAL_ARITH_TAC;
          DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(SET_RULE
           `(?y. ~(y = x) /\ y IN s) ==> ~(s = {x})`) THEN
          EXISTS_TAC `u:real^1` THEN
          REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[EVENTUALLY_WITHIN] THEN EXISTS_TAC `&1` THEN
        REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `y:real^1` THEN
        REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
        MATCH_MP_TAC VECTOR_VARIATION_GE_NORM_FUNCTION THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
          REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(CONJUNCT1(SPEC_ALL
           (REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] CONVEX_INTERVAL))) THEN
          REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC]];
      DISJ2_TAC THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[DIST_SYM] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        REMOVE_THEN "*" (MP_TAC o SPEC `c:real^1`) THEN ANTS_TAC THENL
         [ASM_MESON_TAC[TAGGED_DIVISION_OF; SUBSET]; ALL_TAC] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GSYM(ONCE_REWRITE_RULE[DIST_SYM] IN_BALL)] THEN
        ASM_MESON_TAC[IN_INTERVAL_1; SUBSET; TAGGED_DIVISION_OF;
                      REAL_LE_TOTAL];
        ALL_TAC] THEN
      SUBGOAL_THEN `drop a <= drop c /\ drop c < drop x /\
                    drop x <= drop v /\ drop v <= drop b`
      STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
        ASM_MESON_TAC[IN_INTERVAL_1; SUBSET; TAGGED_DIVISION_OF;
                      REAL_LE_TOTAL];
        ALL_TAC] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[NORM_SUB] dist] THEN
      MATCH_MP_TAC
       (REWRITE_RULE[LIFT_DROP; FORALL_LIFT]
          (ISPEC `at c within interval [c:real^1,v]` LIM_DROP_UBOUND)) THEN
      EXISTS_TAC `\y:real^1. lift(norm(f x - f y:real^N))` THEN
      REWRITE_TAC[TRIVIAL_LIMIT_WITHIN; LIFT_DROP] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC LIM_NORM THEN MATCH_MP_TAC LIM_SUB THEN
        ASM_SIMP_TAC[IN_INTERVAL_1; LIM_CONST] THEN
        MATCH_MP_TAC LIM_WITHIN_SUBSET THEN
        EXISTS_TAC `interval[c:real^1,b]` THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
          ASM_REAL_ARITH_TAC;
          REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC];
        W(MP_TAC o PART_MATCH (lhs o rand) LIMPT_OF_CONVEX o snd) THEN
        ANTS_TAC THENL
         [SIMP_TAC[CONVEX_INTERVAL; ENDS_IN_INTERVAL;
                   INTERVAL_NE_EMPTY_1] THEN
          ASM_REAL_ARITH_TAC;
          DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(SET_RULE
           `(?y. ~(y = x) /\ y IN s) ==> ~(s = {x})`) THEN
          EXISTS_TAC `v:real^1` THEN
          REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[EVENTUALLY_WITHIN] THEN EXISTS_TAC `&1` THEN
        REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `y:real^1` THEN
        REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
        MATCH_MP_TAC VECTOR_VARIATION_GE_NORM_FUNCTION THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
          REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(CONJUNCT1(SPEC_ALL
           (REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] CONVEX_INTERVAL))) THEN
          REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC]]];
    MATCH_MP_TAC MEASURABLE_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    SIMP_TAC[MEASURABLE_CBALL; MEASURABLE_UNION; MEASURABLE_INSERT];
    W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE_IMAGE o
      lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
      SIMP_TAC[MEASURABLE_CBALL; MEASURABLE_UNION; MEASURABLE_INSERT];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)] THEN
    ONCE_REWRITE_TAC[LAMBDA_PAIR_THM] THEN REWRITE_TAC[MEASURE_INSERT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&2 pow (dimindex(:N)) *
      e * sum p (\(x:real^1,k). vector_variation k (f:real^1->real^N))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
      ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`c:real^1`; `k:real^1->bool`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^1. k = interval[u,v]`
       (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      SUBGOAL_THEN `drop u <= drop v` ASSUME_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF; INTERVAL_NE_EMPTY_1; NOT_IN_EMPTY];
        ASM_SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1]] THEN
      SUBGOAL_THEN
       `(f:real^1->real^N) has_bounded_variation_on interval[u,c] /\
        (f:real^1->real^N) has_bounded_variation_on interval[c,v]`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (REWRITE_RULE[IMP_CONJ] HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interval[u:real^1,v]` THEN
        (CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[TAGGED_DIVISION_OF]]) THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; REAL_LE_REFL] THEN
        REWRITE_TAC[GSYM IN_INTERVAL_1] THEN ASM_MESON_TAC[TAGGED_DIVISION_OF];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `vector_variation (interval [u,v]) (f:real^1->real^N) =
        vector_variation (interval [u,c]) f +
        vector_variation (interval [c,v]) f`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC VECTOR_VARIATION_COMBINE THEN
        ASM_REWRITE_TAC[CONJ_ASSOC; GSYM IN_INTERVAL_1] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
        ASM_MESON_TAC[TAGGED_DIVISION_OF; HAS_BOUNDED_VARIATION_ON_SUBSET];
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNION_LE o lhand o snd) THEN
      REWRITE_TAC[MEASURABLE_CBALL; REAL_ADD_LDISTRIB] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand)
        MEASURE_CBALL_BOUND o lhand o snd) THEN
      ASM_SIMP_TAC[REAL_LE_MIN; REAL_LT_IMP_LE; VECTOR_VARIATION_POS_LE] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
      (SUBGOAL_THEN `dimindex(:N) = (dimindex(:N) - 1) + 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[REAL_POW_ADD; REAL_POW_1]]) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_LE_MIN; REAL_LT_IMP_LE; VECTOR_VARIATION_POS_LE;
                   REAL_POW_LE; REAL_ARITH `min e v <= v`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(e:real) pow (dimindex(:N) - 1)` THEN
      (CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN
        ASM_SIMP_TAC[REAL_LE_MIN; REAL_LT_IMP_LE; VECTOR_VARIATION_POS_LE] THEN
        REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO_INV THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN EXPAND_TAC "e" THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_ARITH_TAC]]);
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
       `&2 pow dimindex (:N) *
        (ee / (&2 pow (dimindex(:N)) *
            vector_variation (interval[a,b]) (f:real^1->real^N) + &1)) *
        sum p (\(x:real^1,k). vector_variation k f)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POS; REAL_POW_LE] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [EXPAND_TAC "e" THEN REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
        ASM_MESON_TAC[HAS_BOUNDED_VARIATION_ON_SUBSET; TAGGED_DIVISION_OF;
                      VECTOR_VARIATION_POS_LE];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `a * b / c * d:real = (b * a * d) / c`] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) REAL_LE_LDIV_EQ o snd) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE; VECTOR_VARIATION_POS_LE;
                   REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= y + &1`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          SUM_OVER_TAGGED_DIVISION_LEMMA)) THEN DISCH_THEN(fun th ->
      W(MP_TAC o PART_MATCH (lhs o rand) th o lhand o snd)) THEN
      SIMP_TAC[VECTOR_VARIATION_ON_NULL; BOUNDED_INTERVAL] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      MATCH_MP_TAC VECTOR_VARIATION_ON_DIVISION THEN
      ASM_SIMP_TAC[DIVISION_OF_TAGGED_DIVISION]]]);;

let NEGLIGIBLE_RECTIFIABLE_PATH_IMAGE = prove
 (`!g:real^1->real^N.
        2 <= dimindex(:N) /\ rectifiable_path g ==> negligible(path_image g)`,
  REWRITE_TAC[rectifiable_path; path_image] THEN
  SIMP_TAC[NEGLIGIBLE_IMAGE_BOUNDED_VARIATION_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* Properties of Lebesgue measurable sets.                                   *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_IMP_LEBESGUE_MEASURABLE = prove
 (`!s:real^N->bool. measurable s ==> lebesgue_measurable s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lebesgue_measurable] THEN
  MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
  ASM_REWRITE_TAC[indicator; GSYM MEASURABLE_INTEGRABLE]);;

let NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE = prove
 (`!s:real^N->bool. negligible s ==> lebesgue_measurable s`,
  SIMP_TAC[NEGLIGIBLE_IMP_MEASURABLE; MEASURABLE_IMP_LEBESGUE_MEASURABLE]);;

let LEBESGUE_MEASURABLE_EMPTY = prove
 (`lebesgue_measurable {}`,
  SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; MEASURABLE_EMPTY]);;

let LEBESGUE_MEASURABLE_UNIV = prove
 (`lebesgue_measurable (:real^N)`,
  REWRITE_TAC[lebesgue_measurable; indicator; IN_UNIV; MEASURABLE_ON_CONST]);;

let LEBESGUE_MEASURABLE_COMPACT = prove
 (`!s:real^N->bool. compact s ==> lebesgue_measurable s`,
  SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; MEASURABLE_COMPACT]);;

let LEBESGUE_MEASURABLE_INTERVAL = prove
 (`(!a b:real^N. lebesgue_measurable(interval[a,b])) /\
   (!a b:real^N. lebesgue_measurable(interval(a,b)))`,
  SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; MEASURABLE_INTERVAL]);;

let LEBESGUE_MEASURABLE_INTER = prove
 (`!s t:real^N->bool.
        lebesgue_measurable s /\ lebesgue_measurable t
        ==> lebesgue_measurable(s INTER t)`,
  REWRITE_TAC[indicator; lebesgue_measurable; MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[MEASURABLE_ON_INTER]);;

let LEBESGUE_MEASURABLE_UNION = prove
 (`!s t:real^N->bool.
        lebesgue_measurable s /\ lebesgue_measurable t
        ==> lebesgue_measurable(s UNION t)`,
  REWRITE_TAC[indicator; lebesgue_measurable; MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[MEASURABLE_ON_UNION]);;

let LEBESGUE_MEASURABLE_DIFF = prove
 (`!s t:real^N->bool.
        lebesgue_measurable s /\ lebesgue_measurable t
        ==> lebesgue_measurable(s DIFF t)`,
  REWRITE_TAC[indicator; lebesgue_measurable; MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[MEASURABLE_ON_DIFF]);;

let LEBESGUE_MEASURABLE_COMPL = prove
 (`!s. lebesgue_measurable((:real^N) DIFF s) <=> lebesgue_measurable s`,
  MESON_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_UNIV;
            SET_RULE `UNIV DIFF (UNIV DIFF s) = s`]);;

let LEBESGUE_MEASURABLE_ON_SUBINTERVALS = prove
 (`!s. lebesgue_measurable s <=>
       !a b:real^N. lebesgue_measurable(s INTER interval[a,b])`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[LEBESGUE_MEASURABLE_INTERVAL; LEBESGUE_MEASURABLE_INTER] THEN
  REWRITE_TAC[lebesgue_measurable] THEN DISCH_TAC THEN
  MATCH_MP_TAC INTEGRABLE_SUBINTERVALS_IMP_MEASURABLE THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `(\x. vec 1):real^N->real^1` THEN
  REWRITE_TAC[INTEGRABLE_CONST] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; indicator; IN_INTER] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[indicator] THEN
    COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC; NORM_REAL; GSYM drop] THEN
    REAL_ARITH_TAC]);;

let LEBESGUE_MEASURABLE_CLOSED = prove
 (`!s:real^N->bool. closed s ==> lebesgue_measurable s`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[LEBESGUE_MEASURABLE_ON_SUBINTERVALS] THEN
  ASM_SIMP_TAC[CLOSED_INTER_COMPACT; LEBESGUE_MEASURABLE_COMPACT;
               COMPACT_INTERVAL]);;

let LEBESGUE_MEASURABLE_OPEN = prove
 (`!s:real^N->bool. open s ==> lebesgue_measurable s`,
  REWRITE_TAC[OPEN_CLOSED] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM LEBESGUE_MEASURABLE_COMPL] THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_CLOSED]);;

let LEBESGUE_MEASURABLE_UNIONS = prove
 (`!f. FINITE f /\ (!s. s IN f ==> lebesgue_measurable s)
       ==> lebesgue_measurable (UNIONS f)`,
  REWRITE_TAC[indicator; lebesgue_measurable; MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[MEASURABLE_ON_UNIONS]);;

let LEBESGUE_MEASURABLE_COUNTABLE_UNIONS = prove
 (`!f:(real^N->bool)->bool.
        COUNTABLE f /\ (!s. s IN f ==> lebesgue_measurable s)
        ==> lebesgue_measurable (UNIONS f)`,
  REWRITE_TAC[indicator; lebesgue_measurable; MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[MEASURABLE_ON_COUNTABLE_UNIONS]);;

let LEBESGUE_MEASURABLE_COUNTABLE_UNIONS_EXPLICIT = prove
 (`!s:num->real^N->bool.
        (!n. lebesgue_measurable(s n))
        ==> lebesgue_measurable(UNIONS {s n | n IN (:num)})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV; NUM_COUNTABLE]);;

let LEBESGUE_MEASURABLE_COUNTABLE_INTERS = prove
 (`!f:(real^N->bool)->bool.
        COUNTABLE f /\ (!s. s IN f ==> lebesgue_measurable s)
        ==> lebesgue_measurable (INTERS f)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[INTERS_UNIONS; LEBESGUE_MEASURABLE_COMPL] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; COUNTABLE_IMAGE;
               LEBESGUE_MEASURABLE_COMPL]);;

let LEBESGUE_MEASURABLE_COUNTABLE_INTERS_EXPLICIT = prove
 (`!s:num->real^N->bool.
        (!n. lebesgue_measurable(s n))
        ==> lebesgue_measurable(INTERS {s n | n IN (:num)})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_INTERS THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; COUNTABLE_IMAGE;
               NUM_COUNTABLE]);;

let LEBESGUE_MEASURABLE_INTERS = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> lebesgue_measurable s)
        ==> lebesgue_measurable (INTERS f)`,
  SIMP_TAC[LEBESGUE_MEASURABLE_COUNTABLE_INTERS; FINITE_IMP_COUNTABLE]);;

let LEBESGUE_MEASURABLE_IFF_MEASURABLE = prove
 (`!s:real^N->bool. bounded s ==> (lebesgue_measurable s <=> measurable s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
  REWRITE_TAC[lebesgue_measurable; indicator; MEASURABLE_INTEGRABLE] THEN
  SUBGOAL_THEN `?a b:real^N. s = s INTER interval[a,b]`
   (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
  THENL [REWRITE_TAC[SET_RULE `s = s INTER t <=> s SUBSET t`] THEN
         ASM_MESON_TAC[BOUNDED_SUBSET_CLOSED_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; MESON[]
   `(if P x /\ Q x then a else b) =
    (if Q x then if P x then a else b else b)`] THEN
  REWRITE_TAC[MEASURABLE_ON_UNIV; INTEGRABLE_RESTRICT_UNIV] THEN
  STRIP_TAC THEN MATCH_MP_TAC
    MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `(\x. vec 1):real^N->real^1` THEN
  ASM_REWRITE_TAC[INTEGRABLE_CONST; NORM_REAL; DROP_VEC; GSYM drop] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN SIMP_TAC[DROP_VEC] THEN
  REAL_ARITH_TAC);;

let LEBESGUE_MEASURABLE_MEASURABLE_ON_SUBINTERVALS = prove
 (`!s:real^N->bool.
        lebesgue_measurable s <=>
        (!a b. measurable(s INTER interval[a,b]))`,
  MESON_TAC[LEBESGUE_MEASURABLE_ON_SUBINTERVALS;
            LEBESGUE_MEASURABLE_IFF_MEASURABLE;
            BOUNDED_INTER; BOUNDED_INTERVAL]);;

let LEBESGUE_MEASURABLE_MEASURABLE_ON_COUNTABLE_SUBINTERVALS = prove
 (`!s:real^N->bool.
        lebesgue_measurable s <=>
        (!n. measurable(s INTER interval[--vec n,vec n]))`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV
   [LEBESGUE_MEASURABLE_MEASURABLE_ON_SUBINTERVALS] THEN
  EQ_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b:real^N. ?n. s INTER interval[a,b] =
                     ((s INTER interval[--vec n,vec n]) INTER interval[a,b])`
   (fun th -> ASM_MESON_TAC[th; MEASURABLE_INTERVAL; MEASURABLE_INTER]) THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`interval[a:real^N,b]`; `vec 0:real^N`]
        BOUNDED_SUBSET_CBALL) THEN
  REWRITE_TAC[BOUNDED_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `r:real` REAL_ARCH_SIMPLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `i SUBSET b ==> b SUBSET n ==> s INTER i = (s INTER n) INTER i`)) THEN
  REWRITE_TAC[SUBSET; IN_CBALL_0; IN_INTERVAL; VEC_COMPONENT;
              VECTOR_NEG_COMPONENT; GSYM REAL_ABS_BOUNDS]  THEN
  ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]);;

let MEASURABLE_ON_MEASURABLE_SUBSET = prove
 (`!f s t. s SUBSET t /\ f measurable_on t /\ measurable s
           ==> f measurable_on s`,
  MESON_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET;
            MEASURABLE_IMP_LEBESGUE_MEASURABLE]);;

let MEASURABLE_ON_CASES = prove
 (`!P f g:real^M->real^N s.
        lebesgue_measurable {x | P x} /\
        f measurable_on s /\ g measurable_on s
        ==> (\x. if P x then f x else g x) measurable_on s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. (if x IN s then if P x then (f:real^M->real^N) x else g x else vec 0) =
        (if x IN {x | P x} then if x IN s then f x else vec 0 else vec 0) +
        (if x IN (:real^M) DIFF {x | P x}
         then if x IN s then g x else vec 0 else vec 0)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[IN_UNIV; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID];
    MATCH_MP_TAC MEASURABLE_ON_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_ON_RESTRICT THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL]]);;

let LEBESGUE_MEASURABLE_JORDAN = prove
 (`!s:real^N->bool. negligible(frontier s) ==> lebesgue_measurable s`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[LEBESGUE_MEASURABLE_ON_SUBINTERVALS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  MATCH_MP_TAC MEASURABLE_IMP_LEBESGUE_MEASURABLE THEN
  MATCH_MP_TAC MEASURABLE_JORDAN THEN
  SIMP_TAC[BOUNDED_INTER; BOUNDED_INTERVAL] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `frontier s UNION frontier(interval[a:real^N,b])` THEN
  ASM_REWRITE_TAC[FRONTIER_INTER_SUBSET; NEGLIGIBLE_UNION_EQ] THEN
  SIMP_TAC[NEGLIGIBLE_CONVEX_FRONTIER; CONVEX_INTERVAL]);;

let LEBESGUE_MEASURABLE_CONVEX = prove
 (`!s:real^N->bool. convex s ==> lebesgue_measurable s`,
  SIMP_TAC[LEBESGUE_MEASURABLE_JORDAN; NEGLIGIBLE_CONVEX_FRONTIER]);;

(* ------------------------------------------------------------------------- *)
(* Invariance theorems for Lebesgue measurability.                           *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_TRANSLATION = prove
 (`!f:real^M->real^N s a.
          f measurable_on (IMAGE (\x. a + x) s)
          ==> (\x. f(a + x)) measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[measurable_on; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `g:num->real^M->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `IMAGE (\x:real^M. --a + x) k` THEN
  EXISTS_TAC `\n. (g:num->real^M->real^N) n o (\x. a + x)` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_TRANSLATION_EQ] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    X_GEN_TAC `x:real^M` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a + x:real^M`) THEN
    REWRITE_TAC[o_DEF; IN_IMAGE] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^N = --a + y <=> a + x = y`] THEN
    REWRITE_TAC[UNWIND_THM1; VECTOR_ARITH `a + x:real^N = a + y <=> x = y`]]);;

let MEASURABLE_ON_TRANSLATION_EQ = prove
 (`!f:real^M->real^N s a.
        (\x. f(a + x)) measurable_on s <=>
        f measurable_on (IMAGE (\x. a + x) s)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[MEASURABLE_ON_TRANSLATION] THEN
  MP_TAC(ISPECL [`\x. (f:real^M->real^N) (a + x)`;
                 `IMAGE (\x:real^M. a + x) s`; `--a:real^M`]
    MEASURABLE_ON_TRANSLATION) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; ETA_AX; IMAGE_ID; VECTOR_ARITH
   `--a + a + x:real^N = x /\ a + --a + x = x`]);;

let NEGLIGIBLE_LINEAR_IMAGE_GEN = prove
 (`!f:real^M->real^N s.
        linear f /\ negligible s /\ dimindex(:M) <= dimindex(:N)
        ==> negligible (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_ON_LINEAR]);;

let MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN = prove
 (`!f:real^M->real^N h:real^N->real^P s.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((h o f) measurable_on s <=> h measurable_on (IMAGE f s))`,
  let lemma = prove
   (`!f:real^N->real^P g:real^M->real^N h s.
        dimindex(:M) = dimindex(:N) /\
        linear g /\ linear h /\ (!x. h(g x) = x) /\ (!x. g(h x) = x)
        ==> (f o g) measurable_on s ==> f measurable_on (IMAGE g s)`,
    REPEAT GEN_TAC THEN REWRITE_TAC[measurable_on] THEN
    STRIP_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool`
     (X_CHOOSE_THEN `G:num->real^M->real^P` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `IMAGE (g:real^M->real^N) k` THEN
    EXISTS_TAC `\n x. (G:num->real^M->real^P) n ((h:real^N->real^M) x)` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_LINEAR_IMAGE_GEN THEN
      ASM_MESON_TAC[LE_REFL];
      GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_MESON_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(h:real^N->real^M) y`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[o_THM] THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; FUN_EQ_THM; o_THM; I_THM] THEN
  X_GEN_TAC `g:real^N->real^M` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^N. (f:real^M->real^N) ((g:real^N->real^M) y) = y`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (f:real^M->real^N) UNIV = UNIV` MP_TAC THENL
     [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
    ASM_MESON_TAC[LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN];
    ALL_TAC] THEN
  EQ_TAC THENL [ASM_MESON_TAC[lemma]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`(h:real^N->real^P) o (f:real^M->real^N)`;
                 `g:real^N->real^M`; `f:real^M->real^N`;
                 `IMAGE (f:real^M->real^N) s`] lemma) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let MEASURABLE_ON_LINEAR_IMAGE_EQ = prove
 (`!f:real^N->real^N h:real^N->real^P s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((h o f) measurable_on s <=> h measurable_on (IMAGE f s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN THEN
  ASM_MESON_TAC[]);;

let LEBESGUE_MEASURABLE_TRANSLATION = prove
 (`!a:real^N s.
     lebesgue_measurable (IMAGE (\x. a + x) s) <=>
     lebesgue_measurable s`,
  ONCE_REWRITE_TAC[LEBESGUE_MEASURABLE_ON_SUBINTERVALS] THEN
  SIMP_TAC[LEBESGUE_MEASURABLE_IFF_MEASURABLE;
           BOUNDED_INTER; BOUNDED_INTERVAL] THEN
  GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [LEBESGUE_MEASURABLE_TRANSLATION];;

let LEBESGUE_MEASURABLE_LINEAR_IMAGE_EQ = prove
 (`!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
         ==> (lebesgue_measurable (IMAGE f s) <=>
              lebesgue_measurable s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC o
        MATCH_MP LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE) THEN
  REWRITE_TAC[lebesgue_measurable] THEN MP_TAC(ISPECL
   [`g:real^N->real^N`; `indicator(s:real^N->bool)`; `(:real^N)`]
   MEASURABLE_ON_LINEAR_IMAGE_EQ) THEN
  ASM_REWRITE_TAC[indicator; o_DEF] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; MATCH_MP_TAC EQ_IMP] THEN
  BINOP_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    AP_TERM_TAC THEN ASM SET_TAC[]]);;

add_linear_invariants [LEBESGUE_MEASURABLE_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Various common equivalent forms of function measurability.                *)
(* ------------------------------------------------------------------------- *)

let (MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT,
     MEASURABLE_ON_SIMPLE_FUNCTION_LIMIT) = (CONJ_PAIR o prove)
 (`(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a k. 1 <= k /\ k <= dimindex(:N)
              ==> lebesgue_measurable {x | f(x)$k < a}) /\
   (!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        ?g. (!n. (g n) measurable_on (:real^M)) /\
            (!n. FINITE(IMAGE (g n) (:real^M))) /\
            (!x. ((\n. g n x) --> f x) sequentially))`,
  let lemma0 = prove
   (`!f:real^M->real^1 n m.
          integer m /\
          m / &2 pow n <= drop(f x) /\
          drop(f x) < (m + &1) / &2 pow n /\
          abs(m) <= &2 pow (2 * n)
          ==> vsum {k | integer k /\ abs(k) <= &2 pow (2 * n)}
                   (\k. k / &2 pow n %
                        indicator {y:real^M | k / &2 pow n <= drop(f y) /\
                                              drop(f y) < (k + &1) / &2 pow n}
                                  x) =
              lift(m / &2 pow n)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `vsum {m} (\k. k / &2 pow n %
                    indicator {y:real^M | k / &2 pow n <= drop(f y) /\
                                          drop(f y) < (k + &1) / &2 pow n}
                              x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_SUPERSET THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `k:real` THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
      ASM_REWRITE_TAC[indicator; IN_ELIM_THM] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `~(k:real = m)` THEN ASM_SIMP_TAC[REAL_EQ_INTEGERS] THEN
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[VSUM_SING; indicator; IN_ELIM_THM; LIFT_EQ_CMUL]]) in
  let lemma1 = prove
   (`!f:real^M->real^1.
          (!a b. lebesgue_measurable {x | a <= drop(f x) /\ drop(f x) < b})
          ==> ?g. (!n. (g n) measurable_on (:real^M)) /\
                  (!n. FINITE(IMAGE (g n) (:real^M))) /\
                  (!x. ((\n. g n x) --> f x) sequentially)`,
    REPEAT STRIP_TAC THEN
    EXISTS_TAC
     `\n x. vsum {k | integer k /\ abs(k) <= &2 pow (2 * n)}
                 (\k. k / &2 pow n %
                      indicator {y:real^M | k / &2 pow n <= drop(f y) /\
                                            drop(f y) < (k + &1) / &2 pow n}
                                x)` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC MEASURABLE_ON_VSUM THEN
      REWRITE_TAC[REAL_ABS_BOUNDS; FINITE_INTSEG; IN_ELIM_THM] THEN
      GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_CMUL THEN
      ASM_REWRITE_TAC[GSYM lebesgue_measurable; ETA_AX];
      X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\k. lift(k / &2 pow n))
                        {k | integer k /\ abs(k) <= &2 pow (2 * n)}` THEN
      CONJ_TAC THENL
       [SIMP_TAC[REAL_ABS_BOUNDS; FINITE_INTSEG; FINITE_IMAGE];
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_IMAGE] THEN
      ASM_CASES_TAC
       `?k. integer k /\ abs k <= &2 pow (2 * n) /\
            k / &2 pow n <= drop(f(x:real^M)) /\
            drop(f x) < (k + &1) / &2 pow n`
      THENL
       [FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_EXISTS) THEN
        X_GEN_TAC `m:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC lemma0 THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `&0` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; INTEGER_CLOSED; REAL_ABS_NUM] THEN
        SIMP_TAC[REAL_POW_LE; REAL_POS; real_div; REAL_MUL_LZERO] THEN
        REWRITE_TAC[LIFT_NUM; GSYM real_div] THEN
        MATCH_MP_TAC VSUM_EQ_0 THEN
        X_GEN_TAC `k:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
        REWRITE_TAC[indicator; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN
      MP_TAC(ISPECL [`&2`; `abs(drop((f:real^M->real^1) x))`]
          REAL_ARCH_POW) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N1:num`)] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
      REWRITE_TAC[REAL_POW_INV] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N2:num` MP_TAC) THEN
      SUBST1_TAC(REAL_ARITH `inv(&2 pow N2) = &1 / &2 pow N2`) THEN
      SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN DISCH_TAC THEN
      EXISTS_TAC `MAX N1 N2` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      ABBREV_TAC `m = floor(&2 pow n * drop(f(x:real^M)))` THEN
      SUBGOAL_THEN `dist(lift(m / &2 pow n),(f:real^M->real^1) x) < e`
      MP_TAC THENL
       [REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
        MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `abs(&2 pow n)` THEN
        REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_LDISTRIB] THEN
        SIMP_TAC[REAL_DIV_LMUL; REAL_POW_EQ_0; GSYM REAL_ABS_NZ;
                 REAL_OF_NUM_EQ; ARITH] THEN
        MATCH_MP_TAC(REAL_ARITH
         `x <= y /\ y < x + &1 /\ &1 <= z ==> abs(x - y) < z`) THEN
        EXPAND_TAC "m" THEN REWRITE_TAC[FLOOR] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `e * &2 pow N2` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_POW; REAL_ABS_NUM] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC(NORM_ARITH
         `x:real^1 = y ==> dist(y,z) < e ==> dist(x,z) < e`) THEN
        MATCH_MP_TAC lemma0 THEN
        SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        EXPAND_TAC "m" THEN REWRITE_TAC[FLOOR] THEN
        SIMP_TAC[REAL_ABS_BOUNDS; REAL_LE_FLOOR; REAL_FLOOR_LE;
                 INTEGER_CLOSED] THEN
        MATCH_MP_TAC(REAL_ARITH `abs(x) <= e ==> --e <= x /\ x - &1 < e`) THEN
        REWRITE_TAC[MULT_2; REAL_POW_ADD; REAL_ABS_MUL; REAL_ABS_POW;
                    REAL_ABS_NUM] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `x < e ==> e <= d ==> x <= d`))] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_ARITH_TAC]) in
  MATCH_MP_TAC(MESON[]
   `(!f. P f ==> Q f) /\ (!f. Q f ==> R f) /\ (!f. R f ==> P f)
    ==> (!f. P f <=> Q f) /\ (!f. P f <=> R f)`) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `g:real^M->real^N` THEN DISCH_TAC THEN
    ABBREV_TAC `f:real^M->real^N = \x. --(g x)` THEN
    SUBGOAL_THEN `(f:real^M->real^N) measurable_on (:real^M)` ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN MATCH_MP_TAC MEASURABLE_ON_NEG THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_LT_NEG2] THEN X_GEN_TAC `a:real` THEN
    SPEC_TAC(`--a:real`,`a:real`) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    SIMP_TAC[GSYM VECTOR_NEG_COMPONENT] THEN DISCH_THEN(K ALL_TAC) THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
      GEN_REWRITE_RULE I [MEASURABLE_ON_COMPONENTWISE]) THEN
    ASM_REWRITE_TAC[] THEN  REPEAT STRIP_TAC THEN
    MP_TAC(GEN `d:real` (ISPECL
     [`\x. lift ((f:real^M->real^N) x$k)`;
       `(\x. lift a + (lambda i. d)):real^M->real^1`;
      `(:real^M)`] MEASURABLE_ON_MIN)) THEN
    ASM_REWRITE_TAC[MEASURABLE_ON_CONST] THEN
    DISCH_THEN(fun th ->
      MP_TAC(GEN `n:num` (ISPEC `&n + &1` (MATCH_MP MEASURABLE_ON_CMUL
        (MATCH_MP MEASURABLE_ON_SUB
       (CONJ (SPEC `inv(&n + &1)` th) (SPEC `&0` th))))))) THEN
    REWRITE_TAC[lebesgue_measurable; indicator] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
          MEASURABLE_ON_LIMIT)) THEN
    EXISTS_TAC `{}:real^M->bool` THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; IN_DIFF; IN_UNIV; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[LIM_SEQUENTIALLY; DIST_REAL; VECTOR_MUL_COMPONENT;
             VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
             LAMBDA_BETA; DIMINDEX_1; ARITH] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_ADD_RID] THEN
    SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`; REAL_ARITH
     `&0 < d ==> (min x (a + d) - min x a =
                  if x <= a then &0 else if x <= a + d then x - a else d)`] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `a < (f:real^M->real^N) x $k` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[REAL_ARITH `(x:real^N)$k <= a <=> ~(a < x$k)`] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; DROP_VEC; REAL_SUB_REFL; REAL_ABS_NUM] THEN
    MP_TAC(SPEC `((f:real^M->real^N) x)$k - a` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `a + inv(&n + &1) < ((f:real^M->real^N) x)$k` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `N < f - a ==> n <= N ==> a + n < f`)) THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_ARITH `~(&n + &1 = &0)`] THEN
      ASM_REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!k. 1 <= k /\ k <= dimindex(:N)
          ==> ?g. (!n. (g n) measurable_on (:real^M)) /\
                  (!n. FINITE(IMAGE (g n) (:real^M))) /\
                  (!x. ((\n. g n x) --> lift((f x:real^N)$k)) sequentially)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma1 THEN
      ASM_SIMP_TAC[LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
      REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | Q x} DIFF {x | ~P x}`] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN
      ASM_SIMP_TAC[REAL_NOT_LE];
      GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM]] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:num->num->real^M->real^1` MP_TAC) THEN
    REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
    EXISTS_TAC
      `\n x. (lambda k. drop((g:num->num->real^M->real^1) k n x)):real^N` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN ONCE_REWRITE_TAC[MEASURABLE_ON_COMPONENTWISE] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX];
      X_GEN_TAC `n:num` THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                        ==> lift(x$i) IN IMAGE (g i (n:num)) (:real^M)}` THEN
      ASM_SIMP_TAC[GSYM IN_IMAGE_LIFT_DROP; SET_RULE `{x | x IN s} = s`;
                   FINITE_IMAGE; FINITE_CART] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
      SIMP_TAC[IN_IMAGE; IN_UNIV; LAMBDA_BETA; DROP_EQ] THEN MESON_TAC[];
      X_GEN_TAC `x:real^M` THEN ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX]];
    X_GEN_TAC `f:real^M->real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `g:num->real^M->real^N` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`g:num->real^M->real^N`; `{}:real^M->bool`] THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY]]);;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GE = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a k. 1 <= k /\ k <= dimindex(:N)
              ==> lebesgue_measurable {x | f(x)$k >= a}`,
  GEN_TAC THEN REWRITE_TAC[REAL_ARITH `x >= a <=> ~(x < a)`] THEN
  REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT]);;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a k. 1 <= k /\ k <= dimindex(:N)
              ==> lebesgue_measurable {x | f(x)$k > a}`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM MEASURABLE_ON_NEG_EQ] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MESON[REAL_NEG_NEG] `(!x. P x) <=> (!x:real. P(--x))`] THEN
  REWRITE_TAC[real_gt; VECTOR_NEG_COMPONENT; REAL_LT_NEG2]);;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a k. 1 <= k /\ k <= dimindex(:N)
              ==> lebesgue_measurable {x | f(x)$k <= a}`,
  GEN_TAC THEN REWRITE_TAC[REAL_ARITH `x <= a <=> ~(x > a)`] THEN
  REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT]);;

let (MEASURABLE_ON_PREIMAGE_OPEN_INTERVAL,
    MEASURABLE_ON_PREIMAGE_OPEN) = (CONJ_PAIR o prove)
 (`(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a b. lebesgue_measurable {x | f(x) IN interval(a,b)}) /\
   (!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !t. open t ==> lebesgue_measurable {x | f(x) IN t})`,
  let ulemma = prove
   (`{x | f x IN UNIONS D} = UNIONS {{x | f(x) IN s} | s IN D}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
  MATCH_MP_TAC(MESON[]
   `(!f. P f ==> Q f) /\ (!f. Q f ==> R f) /\ (!f. R f ==> P f)
    ==> (!f. P f <=> Q f) /\ (!f. P f <=> R f)`) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN
    `{x | (f:real^M->real^N) x IN interval(a,b)} =
        INTERS {{x | a$k < f(x)$k} | k IN 1..dimindex(:N)} INTER
        INTERS {{x | (--b)$k < --(f(x))$k} | k IN 1..dimindex(:N)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[IN_INTERVAL; GSYM IN_NUMSEG] THEN
      REWRITE_TAC[VECTOR_NEG_COMPONENT; REAL_LT_NEG2] THEN
      REWRITE_TAC[INTERS_GSPEC] THEN SET_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN
      CONJ_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_INTERS THEN
      SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
      REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
         [MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT]);
        FIRST_X_ASSUM(MP_TAC o MATCH_MP MEASURABLE_ON_NEG) THEN
        REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT]] THEN
      ASM_SIMP_TAC[real_gt]];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_COUNTABLE_UNION_OPEN_INTERVALS) THEN
    DISCH_THEN(X_CHOOSE_THEN `D:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ONCE_REWRITE_TAC[ulemma] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `i:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE
      `{x:real^M | (f x)$k < a} = {x | f x IN {y:real^N | y$k < a}}`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT]]);;

let MEASURABLE_ON_PREIMAGE_CLOSED = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !t. closed t ==> lebesgue_measurable {x | f(x) IN t}`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM LEBESGUE_MEASURABLE_COMPL; closed] THEN
  REWRITE_TAC[SET_RULE
   `UNIV DIFF {x | f x IN t} = {x | f x IN (UNIV DIFF t)}`] THEN
  REWRITE_TAC[MESON[SET_RULE `UNIV DIFF (UNIV DIFF s) = s`]
   `(!s. P(UNIV DIFF s)) <=> (!s. P s)`] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_OPEN]);;

let MEASURABLE_ON_PREIMAGE_CLOSED_INTERVAL = prove
 (`!f:real^M->real^N.
         f measurable_on (:real^M) <=>
         !a b. lebesgue_measurable {x | f(x) IN interval[a,b]}`,
  let ulemma = prove
   (`{x | f x IN UNIONS D} = UNIONS {{x | f(x) IN s} | s IN D}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[MEASURABLE_ON_PREIMAGE_CLOSED; CLOSED_INTERVAL]; DISCH_TAC] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_OPEN] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_COUNTABLE_UNION_CLOSED_INTERVALS) THEN
  DISCH_THEN(X_CHOOSE_THEN `D:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ONCE_REWRITE_TAC[ulemma] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `i:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM]);;

let LEBESGUE_MEASURABLE_PREIMAGE_OPEN = prove
 (`!f:real^M->real^N t.
        f measurable_on (:real^M) /\ open t
        ==> lebesgue_measurable {x | f(x) IN t}`,
  SIMP_TAC[MEASURABLE_ON_PREIMAGE_OPEN]);;

let LEBESGUE_MEASURABLE_PREIMAGE_CLOSED = prove
 (`!f:real^M->real^N t.
        f measurable_on (:real^M) /\ closed t
        ==> lebesgue_measurable {x | f(x) IN t}`,
  SIMP_TAC[MEASURABLE_ON_PREIMAGE_CLOSED]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_LE = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a. lebesgue_measurable {x | !k. 1 <= k /\ k <= dimindex(:N)
                                         ==> f(x)$k <= (a:real^N)$k}`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN
    ONCE_REWRITE_TAC[SET_RULE `{x | !k. P k ==> f x$k <= a k} =
                     {x | f(x) IN {y | !k. P k ==> y$k <= a k}}`] THEN
    FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I
        [MEASURABLE_ON_PREIMAGE_CLOSED]) THEN
    REWRITE_TAC[CLOSED_INTERVAL_LEFT];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `k:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `{x | (f:real^M->real^N) x$k <= a} =
      UNIONS
       {{x | !j. 1 <= j /\ j <= dimindex(:N) ==>
                 f x$j <= ((lambda i. if i = k then a else &n):real^N)$j} |
        n IN (:num)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `x:real^M` THEN SIMP_TAC[LAMBDA_BETA] THEN
      SPEC_TAC(`(f:real^M->real^N) x`,`y:real^N`) THEN GEN_TAC THEN
      ASM_CASES_TAC `(y:real^N)$k <= a` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC
       `sup {(y:real^N)$j | j IN 1..dimindex(:N)}` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC[REAL_SUP_LE_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1]  THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE;
                   FORALL_IN_IMAGE]]]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_GE = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a. lebesgue_measurable {x | !k. 1 <= k /\ k <= dimindex(:N)
                                         ==> f(x)$k >= (a:real^N)$k}`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM MEASURABLE_ON_NEG_EQ] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_ORTHANT_LE] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MESON[VECTOR_NEG_NEG] `(!x:real^N. P x) <=> (!x. P(--x))`] THEN
  REWRITE_TAC[REAL_ARITH `--x <= --y <=> x >= y`; VECTOR_NEG_COMPONENT]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_LT = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a. lebesgue_measurable {x | !k. 1 <= k /\ k <= dimindex(:N)
                                         ==> f(x)$k < (a:real^N)$k}`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN
    ONCE_REWRITE_TAC[SET_RULE `{x | !k. P k ==> f x$k < a k} =
                     {x | f(x) IN {y | !k. P k ==> y$k < a k}}`] THEN
    FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I
        [MEASURABLE_ON_PREIMAGE_OPEN]) THEN
    REWRITE_TAC[OPEN_INTERVAL_LEFT];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `k:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `{x | (f:real^M->real^N) x$k < a} =
      UNIONS
       {{x | !j. 1 <= j /\ j <= dimindex(:N) ==>
                 f x$j < ((lambda i. if i = k then a else &n):real^N)$j} |
        n IN (:num)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `x:real^M` THEN SIMP_TAC[LAMBDA_BETA] THEN
      SPEC_TAC(`(f:real^M->real^N) x`,`y:real^N`) THEN GEN_TAC THEN
      ASM_CASES_TAC `(y:real^N)$k < a` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC
       `&1 + sup {(y:real^N)$j | j IN 1..dimindex(:N)}` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      REWRITE_TAC[REAL_ARITH `&1 + x <= y <=> x <= y - &1`] THEN
      SIMP_TAC[REAL_SUP_LE_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1]  THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG] THEN
      ASM_MESON_TAC[REAL_ARITH `x <= y - &1 ==> x < y`];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE;
                   FORALL_IN_IMAGE]]]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_GT = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a. lebesgue_measurable {x | !k. 1 <= k /\ k <= dimindex(:N)
                                         ==> f(x)$k > (a:real^N)$k}`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM MEASURABLE_ON_NEG_EQ] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_ORTHANT_LT] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MESON[VECTOR_NEG_NEG] `(!x:real^N. P x) <=> (!x. P(--x))`] THEN
  REWRITE_TAC[REAL_ARITH `--x < --y <=> x > y`; VECTOR_NEG_COMPONENT]);;

let MEASURABLE_ON_SIMPLE_FUNCTION_LIMIT_INCREASING = prove
 (`!f:real^N->real^1.
        f measurable_on (:real^N) /\ (!x. &0 <= drop(f x)) <=>
        ?g. (!n x. &0 <= drop(g n x) /\ drop(g n x) <= drop(f x)) /\
            (!n x. drop(g n x) <= drop(g(SUC n) x)) /\
            (!n. (g n) measurable_on (:real^N)) /\
            (!n. FINITE(IMAGE (g n) (:real^N))) /\
            (!x. ((\n. g n x) --> f x) sequentially)`,
  let lemma = prove
   (`!f:real^M->real^1 n m.
          integer m /\
          m / &2 pow n <= drop(f x) /\
          drop(f x) < (m + &1) / &2 pow n /\
          abs(m) <= &2 pow (2 * n)
          ==> vsum {k | integer k /\ abs(k) <= &2 pow (2 * n)}
                   (\k. k / &2 pow n %
                        indicator {y:real^M | k / &2 pow n <= drop(f y) /\
                                              drop(f y) < (k + &1) / &2 pow n}
                                  x) =
              lift(m / &2 pow n)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `vsum {m} (\k. k / &2 pow n %
                    indicator {y:real^M | k / &2 pow n <= drop(f y) /\
                                          drop(f y) < (k + &1) / &2 pow n}
                              x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_SUPERSET THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `k:real` THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
      ASM_REWRITE_TAC[indicator; IN_ELIM_THM] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `~(k:real = m)` THEN ASM_SIMP_TAC[REAL_EQ_INTEGERS] THEN
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[VSUM_SING; indicator; IN_ELIM_THM; LIFT_EQ_CMUL]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC;
    DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
     [GEN_REWRITE_TAC RAND_CONV [MEASURABLE_ON_SIMPLE_FUNCTION_LIMIT] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
      MESON_TAC[REAL_LE_TRANS]]] THEN
  SUBGOAL_THEN
   `!a b. lebesgue_measurable {x:real^N | a <= drop(f x) /\ drop(f x) < b}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | Q x} DIFF {x | ~P x}`] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN REWRITE_TAC[REAL_NOT_LE] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT]) THEN
    SIMP_TAC[drop; FORALL_1; DIMINDEX_1];
    FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [measurable_on])] THEN
  REWRITE_TAC[FORALL_AND_THM; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(MESON[]
   `(!x. P x /\ R x ==> Q x) /\ (?x. P x /\ R x)
    ==> (?x. P x /\ Q x /\ R x)`) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `g:num->real^N->real^1` THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY] o
        SPEC `x:real^N`) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `drop((g:num->real^N->real^1) n x - f x)`) THEN
    ASM_REWRITE_TAC[DROP_SUB; REAL_SUB_LT; NOT_EXISTS_THM] THEN
    X_GEN_TAC `N:num` THEN DISCH_THEN(MP_TAC o SPEC `N + n:num`) THEN
    REWRITE_TAC[LE_ADD; DIST_REAL; GSYM drop] THEN
    MATCH_MP_TAC(REAL_ARITH
     `f < g /\ g <= g' ==> ~(abs(g' - f) < g - f)`) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ARITH_RULE `n:num <= N + n`) THEN
    SPEC_TAC(`N + n:num`,`m:num`) THEN SPEC_TAC(`n:num`,`n:num`) THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC
   `\n x. vsum {k | integer k /\ abs(k) <= &2 pow (2 * n)}
               (\k. k / &2 pow n %
                    indicator {y:real^N | k / &2 pow n <= drop(f y) /\
                                          drop(f y) < (k + &1) / &2 pow n}
                              x)` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n. FINITE {k | integer k /\ abs k <= &2 pow (2 * n)}`
  ASSUME_TAC THENL
   [SIMP_TAC[REAL_ABS_BOUNDS; FINITE_INTSEG; FINITE_IMAGE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[VSUM_REAL; LIFT_DROP; o_DEF] THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `k:real` THEN STRIP_TAC THEN REWRITE_TAC[DROP_CMUL] THEN
    ASM_CASES_TAC `&0 <= k` THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
      REWRITE_TAC[DROP_INDICATOR_POS_LE];
      MATCH_MP_TAC(REAL_ARITH `x = &0 ==> &0 <= x`) THEN
      REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN REWRITE_TAC[indicator] THEN
      COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_ELIM_THM]) THEN
      MATCH_MP_TAC(TAUT `~b ==> a /\ b ==> c`) THEN
      REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&0` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_INTEGERS; REAL_MUL_LZERO; INTEGER_CLOSED] THEN
      ASM_REAL_ARITH_TAC];
    REPEAT GEN_TAC THEN SIMP_TAC[VSUM_REAL; LIFT_DROP; o_DEF; DROP_CMUL] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum {k | integer k /\ abs(k) <= &2 pow (2 * n)}
          (\k. k / &2 pow n *
           (drop(indicator {y:real^N | k / &2 pow n <= drop(f y) /\
                         drop(f y) < (k + &1 / &2) / &2 pow n} x) +
            drop(indicator {y:real^N | (k + &1 / &2) / &2 pow n <= drop(f y) /\
                             drop(f y) < (k + &1) / &2 pow n} x)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      X_GEN_TAC `k:real` THEN STRIP_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[indicator; IN_ELIM_THM] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[DROP_VEC]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [REAL_ARITH `x / y = (&2 * x) * inv(&2) * inv(y)`] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN REWRITE_TAC[GSYM real_div] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 real_pow);
                REAL_ARITH `&2 * (k + &1 / &2) = &2 * k + &1`;
                REAL_ARITH `&2 * (k + &1) = (&2 * k + &1) + &1`] THEN
    ASM_SIMP_TAC[REAL_ADD_LDISTRIB; SUM_ADD]  THEN
    MATCH_MP_TAC(REAL_ARITH
     `!g. sum s f <= sum s g /\ a + sum s g <= b ==> a + sum s f <= b`) THEN
    EXISTS_TAC
     `\k. (&2 * k + &1) / &2 pow SUC n *
          drop
          (indicator
           {y | (&2 * k + &1) / &2 pow SUC n <= drop ((f:real^N->real^1) y) /\
                drop (f y) < ((&2 * k + &1) + &1) / &2 pow SUC n} x)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      SIMP_TAC[DROP_INDICATOR_POS_LE; REAL_LE_DIV2_EQ; REAL_LT_POW2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `\x. &2 * x` SUM_IMAGE) THEN
    MP_TAC(ISPEC `\x. &2 * x + &1` SUM_IMAGE) THEN
    REWRITE_TAC[REAL_EQ_ADD_RCANCEL; REAL_EQ_MUL_LCANCEL] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; ARITH; IMP_CONJ; o_DEF] THEN
    REPEAT(DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th])) THEN
    W(MP_TAC o PART_MATCH (rand o rand) SUM_UNION o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE; SET_RULE
       `DISJOINT (IMAGE f s) (IMAGE g s) <=>
        !x. x IN s ==> !y. y IN s ==> ~(f x = g y)`] THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:real` THEN STRIP_TAC THEN
      X_GEN_TAC `j:real` THEN STRIP_TAC THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
       `&2 * x = &2 * y + &1 ==> &2 * abs(x - y) = &1`)) THEN
      SUBGOAL_THEN `integer(i - j)` MP_TAC THENL
       [ASM_SIMP_TAC[INTEGER_CLOSED]; REWRITE_TAC[integer]] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
      DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
      REWRITE_TAC[EVEN_MULT; ARITH];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC SUM_SUBSET THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> x IN u) /\ (!x. x IN t ==> x IN u)
        ==> !x. x IN (s UNION t) DIFF u ==> P x`) THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[INTEGER_CLOSED; ARITH_RULE `2 * SUC n = 2 + 2 * n`] THEN
      REWRITE_TAC[REAL_POW_ADD] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; REPEAT STRIP_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(x) <= n /\ &1 <= n ==> abs(&2 * x + &1) <= &2 pow 2 * n`) THEN
      ASM_REWRITE_TAC[REAL_LE_POW2];
      X_GEN_TAC `k:real` THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
      STRIP_TAC THEN REWRITE_TAC[DROP_CMUL] THEN
      ASM_CASES_TAC `&0 <= k` THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
        REWRITE_TAC[DROP_INDICATOR_POS_LE];
        MATCH_MP_TAC(REAL_ARITH `x = &0 ==> &0 <= x`) THEN
        REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
        REWRITE_TAC[indicator] THEN
        COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_ELIM_THM]) THEN
        MATCH_MP_TAC(TAUT `~b ==> a /\ b ==> c`) THEN
        REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&0` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
        ASM_SIMP_TAC[GSYM REAL_LT_INTEGERS; REAL_MUL_LZERO;
                     INTEGER_CLOSED] THEN
        ASM_REAL_ARITH_TAC]];
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC MEASURABLE_ON_VSUM THEN
    REWRITE_TAC[REAL_ABS_BOUNDS; FINITE_INTSEG; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_CMUL THEN
    ASM_REWRITE_TAC[GSYM lebesgue_measurable; ETA_AX];
    X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\k. lift(k / &2 pow n))
                      {k | integer k /\ abs(k) <= &2 pow (2 * n)}` THEN
    CONJ_TAC THENL
     [SIMP_TAC[REAL_ABS_BOUNDS; FINITE_INTSEG; FINITE_IMAGE];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_IMAGE] THEN
    ASM_CASES_TAC
     `?k. integer k /\ abs k <= &2 pow (2 * n) /\
          k / &2 pow n <= drop(f(x:real^N)) /\
          drop(f x) < (k + &1) / &2 pow n`
    THENL
     [FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_EXISTS) THEN
      X_GEN_TAC `m:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; INTEGER_CLOSED; REAL_ABS_NUM] THEN
      SIMP_TAC[REAL_POW_LE; REAL_POS; real_div; REAL_MUL_LZERO] THEN
      REWRITE_TAC[LIFT_NUM; GSYM real_div] THEN
      MATCH_MP_TAC VSUM_EQ_0 THEN
      X_GEN_TAC `k:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
      REWRITE_TAC[indicator; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    MP_TAC(ISPECL [`&2`; `abs(drop((f:real^N->real^1) x))`]
        REAL_ARCH_POW) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N1:num`)] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
    REWRITE_TAC[REAL_POW_INV] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` MP_TAC) THEN
    SUBST1_TAC(REAL_ARITH `inv(&2 pow N2) = &1 / &2 pow N2`) THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN DISCH_TAC THEN
    EXISTS_TAC `MAX N1 N2` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ABBREV_TAC `m = floor(&2 pow n * drop(f(x:real^N)))` THEN
    SUBGOAL_THEN `dist(lift(m / &2 pow n),(f:real^N->real^1) x) < e`
    MP_TAC THENL
     [REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `abs(&2 pow n)` THEN
      REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_LDISTRIB] THEN
      SIMP_TAC[REAL_DIV_LMUL; REAL_POW_EQ_0; GSYM REAL_ABS_NZ;
               REAL_OF_NUM_EQ; ARITH] THEN
      MATCH_MP_TAC(REAL_ARITH
       `x <= y /\ y < x + &1 /\ &1 <= z ==> abs(x - y) < z`) THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[FLOOR] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `e * &2 pow N2` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_POW; REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC(NORM_ARITH
       `x:real^1 = y ==> dist(y,z) < e ==> dist(x,z) < e`) THEN
      MATCH_MP_TAC lemma THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[FLOOR] THEN
      SIMP_TAC[REAL_ABS_BOUNDS; REAL_LE_FLOOR; REAL_FLOOR_LE;
               INTEGER_CLOSED] THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x) <= e ==> --e <= x /\ x - &1 < e`) THEN
      REWRITE_TAC[MULT_2; REAL_POW_ADD; REAL_ABS_MUL; REAL_ABS_POW;
                  REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `x < e ==> e <= d ==> x <= d`))] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* More connections with measure where Lebesgue measurability is useful.     *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_LEGESGUE_MEASURABLE_SUBSET = prove
 (`!s t:real^N->bool.
        lebesgue_measurable s /\ measurable t /\ s SUBSET t
        ==> measurable s`,
  REWRITE_TAC[lebesgue_measurable; MEASURABLE_INTEGRABLE] THEN
  REWRITE_TAC[indicator] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `(\x. if x IN t then vec 1 else vec 0):real^N->real^1` THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[DROP_VEC; NORM_REAL; GSYM drop]) THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_LE_REFL; REAL_POS] THEN ASM SET_TAC[]);;

let MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE = prove
 (`!s t:real^N->bool.
        lebesgue_measurable s /\ measurable t ==> measurable(s INTER t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_LEGESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `t:real^N->bool` THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_INTER; MEASURABLE_IMP_LEBESGUE_MEASURABLE;
               INTER_SUBSET]);;

let MEASURABLE_MEASURABLE_INTER_LEGESGUE_MEASURABLE = prove
 (`!s t:real^N->bool.
        measurable s /\ lebesgue_measurable t ==> measurable(s INTER t)`,
  MESON_TAC[INTER_COMM; MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE]);;

let MEASURABLE_INTER_HALFSPACE_LE = prove
 (`!s a i. measurable s ==> measurable(s INTER {x:real^N | x$i <= a})`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_MEASURABLE_INTER_LEGESGUE_MEASURABLE THEN
  ASM_SIMP_TAC[CLOSED_HALFSPACE_COMPONENT_LE; LEBESGUE_MEASURABLE_CLOSED]);;

let MEASURABLE_INTER_HALFSPACE_GE = prove
 (`!s a i. measurable s ==> measurable(s INTER {x:real^N | x$i >= a})`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_MEASURABLE_INTER_LEGESGUE_MEASURABLE THEN
  ASM_SIMP_TAC[CLOSED_HALFSPACE_COMPONENT_GE; LEBESGUE_MEASURABLE_CLOSED]);;

let MEASURABLE_MEASURABLE_DIFF_LEGESGUE_MEASURABLE = prove
 (`!s t. measurable s /\ lebesgue_measurable t ==> measurable(s DIFF t)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
  ASM_SIMP_TAC[MEASURABLE_MEASURABLE_INTER_LEGESGUE_MEASURABLE;
                LEBESGUE_MEASURABLE_COMPL]);;

(* ------------------------------------------------------------------------- *)
(* Negigibility of set with uncountably many disjoint translates.            *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_DISJOINT_TRANSLATES = prove
 (`!s:real^N->bool k z.
        lebesgue_measurable s /\ z limit_point_of k /\
        pairwise (\a b. DISJOINT (IMAGE (\x. a + x) s) (IMAGE (\x. b + x) s)) k
        ==> negligible s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  ABBREV_TAC `t = s INTER interval[a:real^N,b]` THEN
  SUBGOAL_THEN `measurable(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE;
                  MEASURABLE_INTERVAL; INTER_COMM];
    ALL_TAC] THEN
  SUBGOAL_THEN `bounded(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[BOUNDED_INTER; BOUNDED_INTERVAL]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM MEASURABLE_MEASURE_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  ASM_SIMP_TAC[MEASURE_POS_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1` o
    GEN_REWRITE_RULE I [LIMPT_INFINITE_CBALL]) THEN
  REWRITE_TAC[REAL_LT_01] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o
    SPEC `measure(IMAGE (\x:real^N. z + x) (interval[a - vec 1,b + vec 1]))` o
    MATCH_MP REAL_ARCH) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
  MP_TAC(ISPECL [`n:num`; `k INTER cball(z:real^N,&1)`]
    CHOOSE_SUBSET_STRONG) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[INFINITE]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET_INTER; LEFT_IMP_EXISTS_THM; REAL_NOT_LT] THEN
  X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `measure(UNIONS(IMAGE (\a. IMAGE (\x:real^N. a + x) t) u))` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  SUBGOAL_THEN
   `UNIONS(IMAGE (\a. IMAGE (\x:real^N. a + x) t) u) has_measure
    &n * measure(t:real^N->bool)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\a. IMAGE (\x:real^N. a + x) t`; `u:real^N->bool`]
        HAS_MEASURE_DISJOINT_UNIONS_IMAGE) THEN
    ASM_SIMP_TAC[MEASURABLE_TRANSLATION_EQ; MEASURE_TRANSLATION;
                 SUM_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM SET_TAC[];
    REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN STRIP_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL]; MATCH_MP_TAC MEASURE_SUBSET] THEN
  ASM_REWRITE_TAC[MEASURABLE_TRANSLATION_EQ; MEASURABLE_INTERVAL] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; FORALL_IN_IMAGE; IMP_CONJ;
              RIGHT_FORALL_IMP_THM] THEN
  X_GEN_TAC `e:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_IMAGE; UNWIND_THM1; VECTOR_ARITH
   `d + e:real^N = z + y <=> e + d - z = y`] THEN
  SUBGOAL_THEN `x IN interval[a:real^N,b]` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[IN_INTERVAL]] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT] THEN
  REWRITE_TAC[VEC_COMPONENT] THEN MATCH_MP_TAC(REAL_ARITH
   `abs(d) <= &1
    ==> a <= x /\ x <= b ==> a - &1 <= x + d /\ x + d <= b + &1`) THEN
  SUBGOAL_THEN `e IN cball(z:real^N,&1)` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[IN_CBALL]] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
  MESON_TAC[REAL_LE_TRANS; COMPONENT_LE_NORM]);;

(* ------------------------------------------------------------------------- *)
(* Sometimes convenient to restrict the sets in "preimage" characterization  *)
(* of measurable functions to choose points from a dense set.                *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE_DENSE = prove
 (`!f:real^M->real^N r.
        closure (IMAGE lift r) = (:real^1)
        ==> (f measurable_on (:real^M) <=>
             !a k. 1 <= k /\ k <= dimindex(:N) /\ a IN r
                   ==> lebesgue_measurable {x | f(x)$k <= a})`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `k:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. ?x. x IN r /\ a < x /\ x < a + inv(&n + &1)`
  MP_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_UNIV; CLOSURE_APPROACHABLE; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`lift(a + inv(&n + &1) / &2)`; `inv(&n + &1) / &2`]) THEN
    REWRITE_TAC[REAL_HALF; DIST_LIFT; REAL_LT_INV_EQ] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS] THEN
    SIMP_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `t:num->real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{x | (f:real^M->real^N) x$k <= a} =
    INTERS {{x | (f x)$k <= t n} | n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN EQ_TAC THENL
     [ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `i < f - a ==> !j. j <= i /\ a < t /\ t < a + j ==> &0 < f - t`)) THEN
    EXISTS_TAC `inv(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_INTERS THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE]]);;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GE_DENSE = prove
 (`!f:real^M->real^N r.
        closure (IMAGE lift r) = (:real^1)
        ==> (f measurable_on (:real^M) <=>
             !a k. 1 <= k /\ k <= dimindex(:N) /\ a IN r
                   ==> lebesgue_measurable {x | f(x)$k >= a})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEASURABLE_ON_NEG_EQ] THEN
  MP_TAC(ISPECL [`(\x. --f x):real^M->real^N`; `IMAGE (--) r:real->bool`]
        MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE_DENSE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_NEG] THEN
    ASM_REWRITE_TAC[GSYM o_DEF; IMAGE_o; CLOSURE_NEGATIONS] THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC[IN_UNIV] THEN
    MESON_TAC[VECTOR_NEG_NEG];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[VECTOR_NEG_COMPONENT; REAL_ARITH `--x <= --y <=> x >= y`]]);;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT_DENSE = prove
 (`!f:real^M->real^N r.
        closure (IMAGE lift r) = (:real^1)
        ==> (f measurable_on (:real^M) <=>
             !a k. 1 <= k /\ k <= dimindex(:N) /\ a IN r
                   ==> lebesgue_measurable {x | f(x)$k < a})`,
  GEN_TAC THEN REWRITE_TAC[REAL_ARITH `x < a <=> ~(x >= a)`] THEN
  REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL] THEN
  SIMP_TAC[GSYM MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GE_DENSE]);;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT_DENSE = prove
 (`!f:real^M->real^N r.
        closure (IMAGE lift r) = (:real^1)
        ==> (f measurable_on (:real^M) <=>
             !a k. 1 <= k /\ k <= dimindex(:N) /\ a IN r
                   ==> lebesgue_measurable {x | f(x)$k > a})`,
  GEN_TAC THEN REWRITE_TAC[REAL_ARITH `x > a <=> ~(x <= a)`] THEN
  REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL] THEN
  SIMP_TAC[GSYM MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE_DENSE]);;

let MEASURABLE_ON_PREIMAGE_CLOSED_INTERVAL_DENSE = prove
 (`!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a b. a IN t /\ b IN t
                   ==> lebesgue_measurable {x | f(x) IN interval[a,b]})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_PREIMAGE_CLOSED_INTERVAL] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  SUBGOAL_THEN
   `!n. ?u v:real^N.
        (u IN t /\ u IN interval[(a - lambda i. inv(&n + &1)),a]) /\
        (v IN t /\ v IN interval[b,(b + lambda i. inv(&n + &1))])`
  MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM] THEN
    CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
     `~(interior s INTER t = {}) /\ interior s SUBSET s
      ==> ?x. x IN t /\ x IN s`) THEN
    REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED] THEN
    W(MP_TAC o PART_MATCH (rand o rand) OPEN_INTER_CLOSURE_EQ_EMPTY o
      rand o snd) THEN
    REWRITE_TAC[OPEN_INTERVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[INTER_UNIV; INTERVAL_NE_EMPTY] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    REWRITE_TAC[REAL_ARITH `a - i < a <=> &0 < i`;
                REAL_ARITH `b < b + i <=> &0 < i`] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:num->real^N`; `v:num->real^N`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_INTERVAL] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | (f:real^M->real^N) x IN interval[a,b]} =
    INTERS {{x | f x IN interval[u n,v n]} | n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN
    REWRITE_TAC[IN_INTERVAL] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
    ASM_CASES_TAC `1 <= k /\ k <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN
    REWRITE_TAC[DE_MORGAN_THM; EXISTS_OR_THM; REAL_NOT_LE] THEN
    MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN STRIP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `!a i j. i < a - f /\ j <= i /\ a - j <= t /\ t <= a
                ==> &0 < t - f`) THEN EXISTS_TAC `(a:real^N)$k`;
      MATCH_MP_TAC(REAL_ARITH
       `!a i j. i < f - a /\ j <= i /\ a <= t /\ t <= a + j
                ==> &0 < f - t`) THEN EXISTS_TAC `(b:real^N)$k`] THEN
    MAP_EVERY EXISTS_TAC [`inv(&n)`; `inv(&n + &1)`] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_INTERS THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE]]);;

let MEASURABLE_ON_PREIMAGE_OPEN_INTERVAL_DENSE = prove
 (`!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a b. a IN t /\ b IN t
                   ==> lebesgue_measurable {x | f(x) IN interval(a,b)})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_PREIMAGE_OPEN_INTERVAL] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  SUBGOAL_THEN
   `!n. ?u v:real^N.
        (u IN t /\ u IN interval[a,(a + lambda i. inv(&n + &1))]) /\
        (v IN t /\ v IN interval[(b - lambda i. inv(&n + &1)),b])`
  MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM] THEN
    CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
     `~(interior s INTER t = {}) /\ interior s SUBSET s
      ==> ?x. x IN t /\ x IN s`) THEN
    REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED] THEN
    W(MP_TAC o PART_MATCH (rand o rand) OPEN_INTER_CLOSURE_EQ_EMPTY o
      rand o snd) THEN
    REWRITE_TAC[OPEN_INTERVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[INTER_UNIV; INTERVAL_NE_EMPTY] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    REWRITE_TAC[REAL_ARITH `a - i < a <=> &0 < i`;
                REAL_ARITH `b < b + i <=> &0 < i`] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:num->real^N`; `v:num->real^N`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_INTERVAL] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | (f:real^M->real^N) x IN interval(a,b)} =
    UNIONS {{x | f x IN interval(u n,v n)} | n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_INTERVAL] THEN
    EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LET_TRANS; REAL_LTE_TRANS]] THEN
    SPEC_TAC(`(f:real^M->real^N) x`,`y:real^N`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `&0 < inf { min ((y - a:real^N)$i) ((b - y:real^N)$i) |
                 i IN 1..dimindex(:N)}`
    MP_TAC THENL
     [SIMP_TAC[REAL_LT_INF_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1] THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; REAL_LT_MIN; REAL_SUB_LT;
                   VECTOR_SUB_COMPONENT; IN_NUMSEG];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    SIMP_TAC[REAL_LT_INF_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
             IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; VECTOR_SUB_COMPONENT; IN_NUMSEG] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `k:num`])) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(&n + &1) <= inv(&n)` MP_TAC THENL
     [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE]]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_LE_DENSE = prove
 (`!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a. a IN t
                 ==> lebesgue_measurable
                        {x | !k. 1 <= k /\ k <= dimindex(:N)
                                 ==> f(x)$k <= (a:real^N)$k})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_PREIMAGE_ORTHANT_LE] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `a:real^N` THEN
  SUBGOAL_THEN
   `!n. ?u:real^N.
        u IN t /\ u IN interval[a,(a + lambda i. inv(&n + &1))]`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(SET_RULE
     `~(interior s INTER t = {}) /\ interior s SUBSET s
      ==> ?x. x IN t /\ x IN s`) THEN
    REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED] THEN
    W(MP_TAC o PART_MATCH (rand o rand) OPEN_INTER_CLOSURE_EQ_EMPTY o
      rand o snd) THEN
    REWRITE_TAC[OPEN_INTERVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[INTER_UNIV; INTERVAL_NE_EMPTY] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    REWRITE_TAC[REAL_ARITH `b < b + i <=> &0 < i`] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `u:num->real^N` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_INTERVAL] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; LAMBDA_BETA]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | !i. 1 <= i /\ i <= dimindex(:N)
             ==> (f:real^M->real^N) x$i <= (a:real^N)$i} =
    INTERS {{x | !i. 1 <= i /\ i <= dimindex(:N)
                      ==> (f:real^M->real^N) x$i <= (u n:real^N)$i} |
            n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
    ASM_CASES_TAC `1 <= k /\ k <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `!a i j. i < f - a /\ j <= i /\ a <= t /\ t <= a + j
              ==> &0 < f - t`) THEN EXISTS_TAC `(a:real^N)$k` THEN
    MAP_EVERY EXISTS_TAC [`inv(&n)`; `inv(&n + &1)`] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_INTERS THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE]]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_GE_DENSE = prove
 (`!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a. a IN t
                 ==> lebesgue_measurable
                        {x | !k. 1 <= k /\ k <= dimindex(:N)
                                 ==> f(x)$k >= (a:real^N)$k})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEASURABLE_ON_NEG_EQ] THEN
  MP_TAC(ISPECL [`(\x. --f x):real^M->real^N`; `IMAGE (--) t:real^N->bool`]
        MEASURABLE_ON_PREIMAGE_ORTHANT_LE_DENSE) THEN
  ASM_REWRITE_TAC[CLOSURE_NEGATIONS; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; REAL_ARITH `--x <= --y <=> x >= y`] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_UNIV] THEN MESON_TAC[VECTOR_NEG_NEG]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_LT_DENSE = prove
 (`!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a. a IN t
                 ==> lebesgue_measurable
                        {x | !k. 1 <= k /\ k <= dimindex(:N)
                                 ==> f(x)$k < (a:real^N)$k})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_PREIMAGE_ORTHANT_LT] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `a:real^N` THEN
  SUBGOAL_THEN
   `!n. ?u:real^N.
        u IN t /\ u IN interval[(a - lambda i. inv(&n + &1)):real^N,a]`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(SET_RULE
     `~(interior s INTER t = {}) /\ interior s SUBSET s
      ==> ?x. x IN t /\ x IN s`) THEN
    REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED] THEN
    W(MP_TAC o PART_MATCH (rand o rand) OPEN_INTER_CLOSURE_EQ_EMPTY o
      rand o snd) THEN
    REWRITE_TAC[OPEN_INTERVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[INTER_UNIV; INTERVAL_NE_EMPTY] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    REWRITE_TAC[REAL_ARITH `b - i < b <=> &0 < i`] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `u:num->real^N` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_INTERVAL] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; LAMBDA_BETA]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | !i. 1 <= i /\ i <= dimindex(:N)
             ==> (f:real^M->real^N) x$i < (a:real^N)$i} =
    UNIONS {{x | !i. 1 <= i /\ i <= dimindex(:N)
                      ==> (f:real^M->real^N) x$i < (u n:real^N)$i} |
            n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_INTERVAL] THEN
    EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LET_TRANS; REAL_LTE_TRANS]] THEN
    SPEC_TAC(`(f:real^M->real^N) x`,`y:real^N`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `&0 < inf { (a - y:real^N)$i | i IN 1..dimindex(:N)}`
    MP_TAC THENL
     [SIMP_TAC[REAL_LT_INF_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1] THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; REAL_LT_MIN; REAL_SUB_LT;
                   VECTOR_SUB_COMPONENT; IN_NUMSEG];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    SIMP_TAC[REAL_LT_INF_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
             IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; VECTOR_SUB_COMPONENT; IN_NUMSEG] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `k:num`])) THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; LAMBDA_BETA] THEN
    SUBGOAL_THEN `inv(&n + &1) <= inv(&n)` MP_TAC THENL
     [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE]]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_GT_DENSE = prove
 (`!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a. a IN t
                 ==> lebesgue_measurable
                        {x | !k. 1 <= k /\ k <= dimindex(:N)
                                 ==> f(x)$k > (a:real^N)$k})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEASURABLE_ON_NEG_EQ] THEN
  MP_TAC(ISPECL [`(\x. --f x):real^M->real^N`; `IMAGE (--) t:real^N->bool`]
        MEASURABLE_ON_PREIMAGE_ORTHANT_LT_DENSE) THEN
  ASM_REWRITE_TAC[CLOSURE_NEGATIONS; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; REAL_ARITH `--x < --y <=> x > y`] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_UNIV] THEN MESON_TAC[VECTOR_NEG_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Localized variants of function measurability equivalents.                 *)
(* ------------------------------------------------------------------------- *)

let [MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED_INTERVAL;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GE;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GT;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LE;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LT;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN_INTERVAL] =
  (CONJUNCTS o prove)
 (`(!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !t. closed t ==> lebesgue_measurable {x | x IN s /\ f x IN t})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a b. lebesgue_measurable {x | x IN s /\ f x IN interval[a,b]})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !t. open t ==> lebesgue_measurable {x | x IN s /\ f x IN t})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> lebesgue_measurable {x | x IN s /\ (f x)$k >= a})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> lebesgue_measurable {x | x IN s /\ (f x)$k > a})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> lebesgue_measurable {x | x IN s /\ (f x)$k <= a})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> lebesgue_measurable {x | x IN s /\ (f x)$k < a})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a b. lebesgue_measurable {x | x IN s /\ f x IN interval(a,b)}))`,
  let lemma = prove
   (`!f s P. {x | P(if x IN s then f x else vec 0)} =
             if P(vec 0) then s INTER {x | P(f x)} UNION ((:real^M) DIFF s)
             else {x | x IN s /\ P(f x)}`,
    REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]) in
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[MEASURABLE_ON_PREIMAGE_CLOSED];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_CLOSED_INTERVAL];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_OPEN];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GE];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_OPEN_INTERVAL]] THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`] lemma) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  TRY(MATCH_MP_TAC(TAUT `(q <=> q') ==> (p ==> q <=> p ==> q')`)) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER {x | P x}`] THEN
  EQ_TAC THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_UNION; LEBESGUE_MEASURABLE_COMPL] THEN
  UNDISCH_TAC `lebesgue_measurable(s:real^M->bool)` THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LEBESGUE_MEASURABLE_INTER) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]);;

let LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_OPEN = prove
 (`!f:real^M->real^N s t.
        f measurable_on s /\ lebesgue_measurable s /\ open t
        ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`,
  MESON_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN]);;

let LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED = prove
 (`!f:real^M->real^N s t.
        f measurable_on s /\ lebesgue_measurable s /\ closed t
        ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`,
  MESON_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED]);;

let MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN_EQ = prove
 (`!f:real^M->real^N s.
        f measurable_on s /\ lebesgue_measurable s <=>
        !t. open t ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_OPEN] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `(:real^N)` th)) THEN
  REWRITE_TAC[OPEN_UNIV; SET_RULE `{x | x IN s /\ f x IN UNIV} = s`] THEN
  SIMP_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN]);;

let MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED_EQ = prove
 (`!f:real^M->real^N s.
        f measurable_on s /\ lebesgue_measurable s <=>
        !t. closed t ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `(:real^N)` th)) THEN
  REWRITE_TAC[CLOSED_UNIV; SET_RULE `{x | x IN s /\ f x IN UNIV} = s`] THEN
  SIMP_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED]);;

let [MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED_INTERVAL;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GE;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GT;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LE;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LT;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN_INTERVAL] =
  (CONJUNCTS o prove)
 (`(!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !t. closed t ==> measurable {x | x IN s /\ f x IN t})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a b. measurable {x | x IN s /\ f x IN interval[a,b]})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !t. open t ==> measurable {x | x IN s /\ f x IN t})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> measurable {x | x IN s /\ (f x)$k >= a})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> measurable {x | x IN s /\ (f x)$k > a})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> measurable {x | x IN s /\ (f x)$k <= a})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> measurable {x | x IN s /\ (f x)$k < a})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a b. measurable {x | x IN s /\ f x IN interval(a,b)}))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEASURABLE_IMP_LEBESGUE_MEASURABLE) THENL
   [ASM_SIMP_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED];
    ASM_SIMP_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED_INTERVAL];
    ASM_SIMP_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN];
    ASM_SIMP_TAC
     [MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GE];
    ASM_SIMP_TAC
     [MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GT];
    ASM_SIMP_TAC
     [MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LE];
    ASM_SIMP_TAC
     [MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LT];
    ASM_SIMP_TAC
     [MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN_INTERVAL]] THEN
  EQ_TAC THEN SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_LEGESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[] THEN SET_TAC[]);;

let MEASURABLE_MEASURABLE_PREIMAGE_OPEN = prove
 (`!f:real^M->real^N s t.
        f measurable_on s /\ measurable s /\ open t
        ==> measurable {x | x IN s /\ f(x) IN t}`,
  MESON_TAC[MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN]);;

let MEASURABLE_MEASURABLE_PREIMAGE_CLOSED = prove
 (`!f:real^M->real^N s t.
        f measurable_on s /\ measurable s /\ closed t
        ==> measurable {x | x IN s /\ f(x) IN t}`,
  MESON_TAC[MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED]);;

let MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN_EQ = prove
 (`!f:real^M->real^N s.
        f measurable_on s /\ measurable s <=>
        !t. open t ==> measurable {x | x IN s /\ f(x) IN t}`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[MEASURABLE_MEASURABLE_PREIMAGE_OPEN] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `(:real^N)` th)) THEN
  REWRITE_TAC[OPEN_UNIV; SET_RULE `{x | x IN s /\ f x IN UNIV} = s`] THEN
  SIMP_TAC[MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN]);;

let MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED_EQ = prove
 (`!f:real^M->real^N s.
        f measurable_on s /\ measurable s <=>
        !t. closed t ==> measurable {x | x IN s /\ f(x) IN t}`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[MEASURABLE_MEASURABLE_PREIMAGE_CLOSED] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `(:real^N)` th)) THEN
  REWRITE_TAC[CLOSED_UNIV; SET_RULE `{x | x IN s /\ f x IN UNIV} = s`] THEN
  SIMP_TAC[MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* Regularity properties and Steinhaus, this time for Lebesgue measure.      *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_OUTER_OPEN = prove
 (`!s:real^N->bool e.
        lebesgue_measurable s /\ &0 < e
        ==> ?t. open t /\
                s SUBSET t /\
                measurable(t DIFF s) /\
                measure(t DIFF s) < e`,
  REPEAT STRIP_TAC THEN MP_TAC(GEN `n:num`
   (ISPECL [`s INTER ball(vec 0:real^N,&2 pow n)`;
            `e / &4 / &2 pow n`]
        MEASURABLE_OUTER_OPEN)) THEN
  ASM_SIMP_TAC[MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE; REAL_LT_DIV;
               MEASURABLE_BALL; REAL_LT_INV_EQ; REAL_LT_POW2;
               REAL_ARITH `&0 < e / &4 <=> &0 < e`] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `t:num->real^N->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `UNIONS(IMAGE t (:num)):real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_UNIONS; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `norm(x:real^N)` REAL_ARCH_POW2) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[IN_BALL_0; IN_INTER];
    REWRITE_TAC[UNIONS_DIFF; SET_RULE
     `{f x | x IN IMAGE g s} = {f(g(x)) | x IN s}`] THEN
    MATCH_MP_TAC(MESON[REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`]
        `&0 < e /\ P /\ x <= e / &2 ==> P /\ x < e`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE THEN
    ASM_SIMP_TAC[MEASURABLE_MEASURABLE_DIFF_LEGESGUE_MEASURABLE] THEN
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\i. e / &4 / &2 pow i)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `measure(t i DIFF (s INTER ball(vec 0:real^N,&2 pow i)))` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURE_SUBSET THEN
        ASM_SIMP_TAC[MEASURABLE_MEASURABLE_DIFF_LEGESGUE_MEASURABLE;
          MEASURABLE_INTER; MEASURABLE_BALL; LEBESGUE_MEASURABLE_INTER;
          MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
        SET_TAC[];
        ASM_SIMP_TAC[MEASURE_DIFF_SUBSET; MEASURABLE_DIFF; MEASURABLE_BALL;
                     MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE] THEN
        ASM_SIMP_TAC[REAL_ARITH `t < s + e ==> t - s <= e`]];
      REWRITE_TAC[real_div; SUM_LMUL; REAL_INV_POW; SUM_GP] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[CONJUNCT1 LT] THEN
      ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_LE_LMUL_EQ] THEN
      REWRITE_TAC[REAL_ARITH
        `&1 / &4 * (&1 - x) * &2 <= &1 / &2 <=> &0 <= x`] THEN
      MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV]]);;

let LEBESGUE_MEASURABLE_INNER_CLOSED = prove
 (`!s:real^N->bool e.
        lebesgue_measurable s /\ &0 < e
        ==> ?t. closed t /\
                t SUBSET s /\
                measurable(s DIFF t) /\
                measure(s DIFF t) < e`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM LEBESGUE_MEASURABLE_COMPL] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:real^N->bool` o MATCH_MP
    LEBESGUE_MEASURABLE_OUTER_OPEN) THEN
  EXISTS_TAC `(:real^N) DIFF t` THEN POP_ASSUM MP_TAC THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
  REWRITE_TAC[GSYM OPEN_CLOSED] THENL
   [SET_TAC[];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC] THEN
  SET_TAC[]);;

let STEINHAUS_LEBESGUE = prove
 (`!s:real^N->bool.
        lebesgue_measurable s /\ ~negligible s
        ==> ?d. &0 < d /\ ball(vec 0,d) SUBSET {x - y | x IN s /\ y IN s}`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
  REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  MP_TAC(ISPEC `s INTER interval[a:real^N,b]` STEINHAUS) THEN
  ASM_SIMP_TAC[GSYM MEASURABLE_MEASURE_POS_LT; MEASURABLE_INTERVAL;
               MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE] THEN
  SET_TAC[]);;

let LEBESGUE_MEASURABLE_REGULAR_OUTER = prove
 (`!s:real^N->bool.
        lebesgue_measurable s
        ==> ?k c. negligible k /\ (!n. open(c n)) /\
                  s = INTERS {c n | n IN (:num)} DIFF k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    LEBESGUE_MEASURABLE_OUTER_OPEN)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&2 pow n)`) THEN
  REWRITE_TAC[REAL_LT_POW2; SKOLEM_THM; REAL_LT_INV_EQ] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `c:num->real^N->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `INTERS {c n | n IN (:num)} DIFF s:real^N->bool` THEN
  EXISTS_TAC `c:num->real^N->bool` THEN
  ASM_REWRITE_TAC[SET_RULE `s = t DIFF (t DIFF s) <=> s SUBSET t`] THEN
  ASM_REWRITE_TAC[SUBSET_INTERS; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_POW_INV]] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  EXISTS_TAC `(c:num->real^N->bool) n DIFF s` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SET_TAC[]; ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]]);;

let LEBESGUE_MEASURABLE_REGULAR_INNER = prove
 (`!s:real^N->bool.
        lebesgue_measurable s
        ==> ?k c. negligible k /\ (!n. compact(c n)) /\
                  s = UNIONS {c n | n IN (:num)} UNION k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    LEBESGUE_MEASURABLE_INNER_CLOSED)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&2 pow n)`) THEN
  REWRITE_TAC[REAL_LT_POW2; SKOLEM_THM; REAL_LT_INV_EQ] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `c:num->real^N->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `s DIFF UNIONS {c n | n IN (:num)}:real^N->bool` THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_POW_INV]] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    EXISTS_TAC `s DIFF (c:num->real^N->bool) n` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SET_TAC[]; ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]];
    SUBGOAL_THEN
     `?d. (!n. compact(d n:real^N->bool)) /\
          UNIONS {d n | n IN (:num)} = UNIONS {c n | n IN (:num)}`
    MP_TAC THENL
     [MP_TAC(GEN `n:num` (ISPEC
       `(c:num->real^N->bool) n` CLOSED_UNION_COMPACT_SUBSETS)) THEN
      ASM_REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN DISCH_THEN
       (X_CHOOSE_THEN `d:num->num->real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `COUNTABLE {d n m:real^N->bool | n IN (:num) /\ m IN (:num)}`
      MP_TAC THENL
       [MATCH_MP_TAC COUNTABLE_PRODUCT_DEPENDENT THEN
        REWRITE_TAC[NUM_COUNTABLE];
        DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          COUNTABLE_AS_IMAGE)) THEN
        ANTS_TAC THENL [SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
        ASM SET_TAC[]];
      MATCH_MP_TAC MONO_EXISTS THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[SET_RULE `s = t UNION (s DIFF t) <=> t SUBSET s`] THEN
      ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC]]]);;

(* ------------------------------------------------------------------------- *)
(* A Lebesgue measurable set is almost an F_sigma.                           *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_ALMOST_FSIGMA = prove
 (`!s:real^N->bool.
        lebesgue_measurable s
        ==> ?c t. UNIONS c UNION t = s /\ DISJOINT (UNIONS c) t /\
                  COUNTABLE c /\ (!u. u IN c ==> closed u) /\ negligible t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        LEBESGUE_MEASURABLE_INNER_CLOSED)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; SKOLEM_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `f:num->real^N->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (f:num->real^N->bool) (:num)` THEN
  EXISTS_TAC `s DIFF UNIONS (IMAGE (f:num->real^N->bool) (:num))` THEN
  ASM_SIMP_TAC[SET_RULE `DISJOINT s (u DIFF s)`; COUNTABLE_IMAGE;
               NUM_COUNTABLE; FORALL_IN_IMAGE; IN_UNIV; UNIONS_SUBSET;
               SET_RULE `s UNION (u DIFF s) = u <=> s SUBSET u`] THEN
  REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s DIFF (f:num->real^N->bool) n` THEN
  ASM_REWRITE_TAC[UNIONS_IMAGE] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `inv(&n + &1)` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN TRANS_TAC REAL_LE_TRANS `inv(&n)` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Existence of nonmeasurable subsets of any set of positive measure.        *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_IFF_LEBESGUE_MEASURABLE_SUBSETS = prove
 (`!s:real^N->bool. negligible s <=> !t. t SUBSET s ==> lebesgue_measurable t`,
  let lemma = prove
   (`!s:real^N->bool.
      lebesgue_measurable s /\
      (!x y q. x IN s /\ y IN s /\ rational q /\ y = q % basis 1 + x ==> y = x)
      ==> negligible s`,
    SIMP_TAC[VECTOR_ARITH `q + x:real^N = x <=> q = vec 0`; VECTOR_MUL_EQ_0;
             BASIS_NONZERO; DIMINDEX_GE_1; ARITH] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_TAC THEN MP_TAC(ISPEC `s:real^N->bool` STEINHAUS_LEBESGUE) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `q:real` o MATCH_MP RATIONAL_BETWEEN) THEN
    FIRST_X_ASSUM
     (MP_TAC o SPEC `q % basis 1:real^N` o GEN_REWRITE_RULE I [SUBSET]) THEN
    SIMP_TAC[IN_BALL_0; NORM_MUL; NORM_BASIS; DIMINDEX_GE_1;
             ARITH; NOT_IMP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[IN_ELIM_THM]] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; IN_ELIM_THM; NOT_EXISTS_THM;
                    VECTOR_ARITH `q:real^N = x - y <=> x = q + y`] THEN
    ASM_CASES_TAC `q = &0` THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]) in
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[NEGLIGIBLE_SUBSET; NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE];
    DISCH_TAC] THEN
  ABBREV_TAC
   `(canonize:real^N->real^N) =
    \x. @y. y IN s /\ ?q. rational q /\ q % basis 1 + y = x` THEN
  SUBGOAL_THEN
   `!x:real^N. x IN s
               ==> canonize x IN s /\
                   ?q. rational q /\ q % basis 1 + canonize x = x`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "canonize" THEN
    CONV_TAC SELECT_CONV THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[RATIONAL_CLOSED] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `v = IMAGE (canonize:real^N->real^N) s` THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC
   `UNIONS (IMAGE (\q. IMAGE (\x:real^N. q % basis 1 + x) v) rational)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[UNIONS_IMAGE; SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
  SIMP_TAC[COUNTABLE_RATIONAL; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_TRANSLATION_EQ] THEN GEN_TAC THEN
  DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC lemma THEN
  CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "v" THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `q:real` THEN REPEAT DISCH_TAC THEN
  EXPAND_TAC "canonize" THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `z:real^N` THEN AP_TERM_TAC THEN FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `y:real^N` th) THEN MP_TAC(SPEC `x:real^N` th)) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `q % b + x:real^N = y <=> x = y - q % b`] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `x - q % b:real^N = y - r % b - s % b <=>
                   y + (q - r - s) % b = x /\ x + (r + s - q) % b = y`] THEN
  STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
   (BINDER_CONV o RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
  SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_GE_1; ARITH; VECTOR_ARITH
   `y - q % b:real^N = (y + r % b) - s % b <=> (q + r - s) % b = vec 0`] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[REAL_ARITH `a + b - c = &0 <=> c = a + b`; UNWIND_THM2] THEN
  ASM_SIMP_TAC[RATIONAL_CLOSED]);;

let NEGLIGIBLE_IFF_MEASURABLE_SUBSETS = prove
 (`!s:real^N->bool. negligible s <=> !t. t SUBSET s ==> measurable t`,
  MESON_TAC[NEGLIGIBLE_SUBSET; NEGLIGIBLE_IMP_MEASURABLE;
            MEASURABLE_IMP_LEBESGUE_MEASURABLE;
            NEGLIGIBLE_IFF_LEBESGUE_MEASURABLE_SUBSETS]);;

(* ------------------------------------------------------------------------- *)
(* Preserving Lebesgue measurability vs. preserving negligibility.           *)
(* ------------------------------------------------------------------------- *)

let PRESERVES_LEBESGUE_MEASURABLE_IMP_PRESERVES_NEGLIGIBLE = prove
 (`!f s:real^N->bool.
        (!t. negligible t /\ t SUBSET s ==> lebesgue_measurable(IMAGE f t))
        ==> (!t. negligible t /\ t SUBSET s ==> negligible(IMAGE f t))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NEGLIGIBLE_IFF_LEBESGUE_MEASURABLE_SUBSETS] THEN
  REWRITE_TAC[FORALL_SUBSET_IMAGE] THEN
  ASM_MESON_TAC[NEGLIGIBLE_SUBSET; SUBSET_TRANS]);;

let LEBESGUE_MEASURABLE_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\
        (!t. negligible t /\ t SUBSET s ==> negligible(IMAGE f t))
        ==> !t. lebesgue_measurable t /\ t SUBSET s
                ==> lebesgue_measurable(IMAGE f t)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP LEBESGUE_MEASURABLE_REGULAR_INNER) THEN
  ASM_REWRITE_TAC[IMAGE_UNION; IMAGE_UNIONS] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_UNION THEN
  SUBGOAL_THEN `(k:real^M->bool) SUBSET s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ASM_SIMP_TAC[NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE]] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
  REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o; FORALL_IN_IMAGE] THEN
  SIMP_TAC[IN_UNIV; COUNTABLE_IMAGE; NUM_COUNTABLE] THEN
  GEN_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_COMPACT THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let LEBESGUE_MEASURABLE_DIFFERENTIABLE_IMAGE = prove
 (`!f:real^M->real^N s.
        dimindex(:M) <= dimindex(:N) /\
        f differentiable_on s /\ lebesgue_measurable s
        ==> lebesgue_measurable(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
   (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]
        LEBESGUE_MEASURABLE_CONTINUOUS_IMAGE) THEN
  EXISTS_TAC `s:real^M->bool` THEN
  ASM_SIMP_TAC[SUBSET_REFL; DIFFERENTIABLE_IMP_CONTINUOUS_ON] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE THEN
  ASM_MESON_TAC[DIFFERENTIABLE_ON_SUBSET]);;

let LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN = prove
 (`!f:real^M->real^N s.
        linear f /\ lebesgue_measurable s /\ dimindex(:M) <= dimindex(:N)
        ==> lebesgue_measurable(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFFERENTIABLE_IMAGE THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_ON_LINEAR]);;

let MEASURABLE_LINEAR_IMAGE_GEN = prove
 (`!f:real^M->real^N s.
        linear f /\ measurable s /\ dimindex(:M) <= dimindex(:N)
        ==> measurable(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `m:num <= n ==> m < n \/ m = n`))
  THENL
   [MATCH_MP_TAC NEGLIGIBLE_IMP_MEASURABLE THEN
    MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_LOWDIM THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_ON_LINEAR];
    ASM_CASES_TAC `!x y. (f:real^M->real^N) x = f y ==> x = y` THENL
     [ASM_MESON_TAC[MEASURABLE_LINEAR_IMAGE_EQ_GEN]; ALL_TAC] THEN
    MATCH_MP_TAC NEGLIGIBLE_IMP_MEASURABLE THEN
    MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `(:real^M)`]
        DIM_IMAGE_KERNEL_GEN) THEN
    ASM_REWRITE_TAC[SUBSPACE_UNIV; DIM_UNIV] THEN ONCE_ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC(ARITH_RULE
     `x <= y /\ ~(d = 0) ==> x < y + d`) THEN
    SIMP_TAC[DIM_SUBSET; IMAGE_SUBSET; SUBSET_UNIV] THEN
    REWRITE_TAC[IN_UNIV; DIM_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_INJECTIVE_0) THEN ASM SET_TAC[]]);;

let LEBESGUE_MEASURABLE_LINEAR_IMAGE_EQ_GEN = prove
 (`!f:real^M->real^N s.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x y. f x = f y ==> x = y)
        ==> (lebesgue_measurable(IMAGE f s) <=> lebesgue_measurable s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y. f((g:real^N->real^M) y) = y` ASSUME_TAC THENL
   [MP_TAC(ISPEC `f:real^M->real^N` LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN; LE_REFL]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `s = IMAGE (g:real^N->real^M) (IMAGE f s)` SUBST1_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN; LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Measurability of continuous functions.                                    *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ lebesgue_measurable s
        ==> f measurable_on s`,
  let lemma = prove
   (`!s. lebesgue_measurable s
         ==> ?u:num->real^M->bool.
                (!n. closed(u n)) /\ (!n. u n SUBSET s) /\
                (!n. measurable(s DIFF u n) /\
                     measure(s DIFF u n) < inv(&n + &1)) /\
                (!n. u(n) SUBSET u(SUC n))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!n t. closed t /\ t SUBSET s
            ==> ?u:real^M->bool.
                      closed u /\ t SUBSET u /\ u SUBSET s /\
                      measurable(s DIFF u) /\ measure(s DIFF u) < inv(&n + &1)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`s DIFF t:real^M->bool`; `inv(&n + &1)`]
        LEBESGUE_MEASURABLE_INNER_CLOSED) THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_CLOSED] THEN
      REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t UNION u:real^M->bool` THEN ASM_SIMP_TAC[CLOSED_UNION] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[SET_RULE `s DIFF (t UNION u) = s DIFF t DIFF u`];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `v:num->(real^M->bool)->(real^M->bool)` THEN DISCH_TAC THEN
      MP_TAC(prove_recursive_functions_exist num_RECURSION
          `(u:num->real^M->bool) 0 = v 0 {} /\
           (!n. u(SUC n) = v (SUC n) (u n))`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:num->real^M->bool` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       `!n. closed(u n) /\ (u:num->real^M->bool) n SUBSET s`
      ASSUME_TAC THENL
       [INDUCT_TAC THEN
        ASM_SIMP_TAC[CLOSED_EMPTY; EMPTY_SUBSET];
        ASM_SIMP_TAC[]] THEN
      INDUCT_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[CLOSED_EMPTY; EMPTY_SUBSET]]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `u:num->real^M->bool` STRIP_ASSUME_TAC o
    MATCH_MP lemma) THEN
  SUBGOAL_THEN `lebesgue_measurable((:real^M) DIFF s)` MP_TAC THENL
   [ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:num->real^M->bool` STRIP_ASSUME_TAC o
    MATCH_MP lemma) THEN
  REWRITE_TAC[measurable_on] THEN
  EXISTS_TAC `(:real^M) DIFF
           (UNIONS {u n | n IN (:num)} UNION UNIONS {v n | n IN (:num)})` THEN
  SUBGOAL_THEN
   `!n. ?g. g continuous_on (:real^M) /\
            (!x. x IN u(n) UNION v(n:num)
                 ==> g x = if x IN s then (f:real^M->real^N)(x) else vec 0)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC TIETZE_UNBOUNDED THEN
    ASM_SIMP_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; CLOSED_UNION] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CONST] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
    REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `g:num->real^M->real^N` THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `(s DIFF UNIONS {u n | n IN (:num)}) UNION
                ((:real^M) DIFF s DIFF UNIONS {v n | n IN (:num)})` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC THEN
    REWRITE_TAC[NEGLIGIBLE_OUTER] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `e:real` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `s DIFF u(n:num):real^M->bool`;
      EXISTS_TAC `(:real^M) DIFF s DIFF v(n:num):real^M->bool`] THEN
    (CONJ_TAC THENL [SET_TAC[]; ASM_REWRITE_TAC[]] THEN
     MATCH_MP_TAC REAL_LT_TRANS THEN
     EXISTS_TAC `inv(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LT_TRANS THEN
     EXISTS_TAC `inv(&n)` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
     CONJ_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]);
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[SET_RULE
     `~(x IN (UNIV DIFF (s UNION t))) <=> x IN s \/ x IN t`] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNION] THEN
    SUBGOAL_THEN
     `!i j. i <= j ==> (u:num->real^M->bool)(i) SUBSET u(j) /\
                       (v:num->real^M->bool)(i) SUBSET v(j)`
     (fun th -> ASM_MESON_TAC[SUBSET; th]) THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
   ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ closed s ==> f measurable_on s`,
  SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET;
           LEBESGUE_MEASURABLE_CLOSED]);;

let CONTINUOUS_AE_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET = prove
 (`!f:real^M->real^N s m.
        f continuous_on (s DIFF m) /\ lebesgue_measurable s /\ negligible m
        ==> f measurable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) measurable_on (s DIFF m)` MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE];
    MATCH_MP_TAC MEASURABLE_ON_SPIKE_SET THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       NEGLIGIBLE_SUBSET)) THEN
    SET_TAC[]]);;
