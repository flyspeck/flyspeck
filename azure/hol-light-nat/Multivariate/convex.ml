open Hol_core
open Floor
open Vectors
open Determinants
open Topology
include Convex2

(* ------------------------------------------------------------------------- *)
(* Upper bound on a ball implies upper and lower bounds.                     *)
(* ------------------------------------------------------------------------- *)

let CONVEX_BOUNDS_LEMMA = prove
 (`!f x:real^N e.
        f convex_on cball(x,e) /\
        (!y. y IN cball(x,e) ==> f(y) <= b)
        ==> !y. y IN cball(x,e) ==> abs(f(y)) <= b + &2 * abs(f(x))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 <= e` THENL
   [ALL_TAC;
    REWRITE_TAC[IN_CBALL] THEN ASM_MESON_TAC[DIST_POS_LE; REAL_LE_TRANS]] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [convex_on]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`y:real^N`; `&2 % x - y:real^N`; `&1 / &2`; `&1 / &2`]) THEN
  REWRITE_TAC[GSYM VECTOR_ADD_LDISTRIB; GSYM REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[VECTOR_ARITH `y + x - y = x:real^N`] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ABBREV_TAC `z = &2 % x - y:real^N` THEN
  SUBGOAL_THEN `z:real^N IN cball(x,e)` ASSUME_TAC THENL
   [UNDISCH_TAC `y:real^N IN cball(x,e)`  THEN
    EXPAND_TAC "z" THEN REWRITE_TAC[dist; IN_CBALL] THEN
    REWRITE_TAC[VECTOR_ARITH `x - (&2 % x - y) = y - x`] THEN
    REWRITE_TAC[NORM_SUB];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  FIRST_X_ASSUM(fun th ->
    MAP_EVERY (MP_TAC o C SPEC th) [`y:real^N`; `z:real^N`]) THEN
  ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence a convex function on an open set is continuous.                     *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_CONTINUOUS = prove
 (`!f s:real^N->bool. open s /\ f convex_on s ==> lift o f continuous_on s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d = e / &(dimindex(:N))` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1;
                    ARITH_RULE `0 < d <=> 1 <= d`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?b. !y:real^N. y IN interval[(x - lambda i. d),(x + lambda i. d)]
                   ==> f(y) <= b`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x - (lambda i. d):real^N`; `x + (lambda i. d):real^N`]
        CLOSED_INTERVAL_AS_CONVEX_HULL) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `c = {}:real^N->bool` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
    MP_TAC(ISPEC `IMAGE (f:real^N->real) c` SUP_FINITE) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    ABBREV_TAC `k = sup(IMAGE (f:real^N->real) c)` THEN
    STRIP_TAC THEN EXISTS_TAC `k:real` THEN
    MATCH_MP_TAC CONVEX_ON_CONVEX_HULL_BOUND THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONVEX_ON_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball (x:real^N,e)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL; IN_CBALL] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; LAMBDA_BETA] THEN
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[REAL_ARITH `x - d <= z /\ z <= x + d <=> abs(x - z) <= d`] THEN
    DISCH_TAC THEN REWRITE_TAC[dist] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `sum(1..dimindex(:N)) (\i. abs((x - z:real^N)$i))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN
    MATCH_MP_TAC SUM_BOUND_GEN THEN
    REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; CARD_NUMSEG] THEN
    ASM_SIMP_TAC[IN_NUMSEG; NOT_LT; DIMINDEX_GE_1; ADD_SUB;
                 VECTOR_SUB_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(x:real^N,d) SUBSET cball(x,e)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL] THEN GEN_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `d <= e ==> x <= d ==> x <= e`) THEN
    EXPAND_TAC "d" THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; DIMINDEX_GE_1;
                 ARITH_RULE `0 < x <=> 1 <= x`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_OF_NUM_LE; DIMINDEX_GE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N. y IN cball(x,d) ==> abs(f(y)) <= b + &2 * abs(f(x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONVEX_BOUNDS_LEMMA THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONVEX_ON_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `y:real^N IN cball(x,d)` THEN REWRITE_TAC[IN_CBALL] THEN
    REWRITE_TAC[IN_INTERVAL; IN_CBALL; dist] THEN DISCH_TAC THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; LAMBDA_BETA] THEN
    REWRITE_TAC[REAL_ARITH `x - d <= z /\ z <= x + d <=> abs(x - z) <= d`] THEN
    SIMP_TAC[GSYM VECTOR_SUB_COMPONENT] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x - y:real^N)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(lift o f) continuous_on (ball(x:real^N,d))` MP_TAC THENL
   [MATCH_MP_TAC CONVEX_ON_BOUNDED_CONTINUOUS THEN REWRITE_TAC[OPEN_BALL] THEN
    EXISTS_TAC `b + &2 * abs(f(x:real^N))` THEN
    ASM_MESON_TAC[SUBSET; CONVEX_ON_SUBSET; SUBSET_TRANS; BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL; CENTRE_IN_BALL]);;

(* ------------------------------------------------------------------------- *)
(* Characterizations of convex functions in terms of sequents.               *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_LEFT_SECANT_MUL,CONVEX_ON_RIGHT_SECANT_MUL = (CONJ_PAIR o prove)
 (`(!f s:real^N->bool.
        f convex_on s <=>
          !a b x. a IN s /\ b IN s /\ x IN segment[a,b]
                  ==> (f x - f a) * norm(b - a) <= (f b - f a) * norm(x - a)) /\
   (!f s:real^N->bool.
        f convex_on s <=>
          !a b x. a IN s /\ b IN s /\ x IN segment[a,b]
                  ==> (f b - f a) * norm(b - x) <= (f b - f x) * norm(b - a))`,
  CONJ_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[convex_on] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `a:real^N` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `b:real^N` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `(a:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(b:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_SEGMENT; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `u:real` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[TAUT `a /\ x = y <=> x = y /\ a`;
              TAUT `a /\ x = y /\ b <=> x = y /\ a /\ b`] THEN
  REWRITE_TAC[REAL_ARITH `v + u = &1 <=> v = &1 - u`] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; IMP_CONJ] THEN
  REWRITE_TAC[REAL_SUB_LE] THEN
  ASM_CASES_TAC `&0 <= u` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `u <= &1` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_ARITH `((&1 - u) % a + u % b) - a:real^N = u % (b - a)`;
   VECTOR_ARITH `b - ((&1 - u) % a + u % b):real^N = (&1 - u) % (b - a)`] THEN
  REWRITE_TAC[NORM_MUL; REAL_MUL_ASSOC] THEN
  (ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL; REAL_SUB_REFL;
                    VECTOR_ARITH `(&1 - u) % a + u % a:real^N = a`] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[REAL_ARITH
     `&0 <= u /\ u <= &1 ==> abs u = u /\ abs(&1 - u) = &1 - u`] THEN
    REAL_ARITH_TAC]));;

let CONVEX_ON_LEFT_SECANT,CONVEX_ON_RIGHT_SECANT = (CONJ_PAIR o prove)
 (`(!f s:real^N->bool.
      f convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN segment(a,b)
                ==> (f x - f a) / norm(x - a) <= (f b - f a) / norm(b - a)) /\
   (!f s:real^N->bool.
      f convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN segment(a,b)
                ==> (f b - f a) / norm(b - a) <= (f b - f x) / norm(b - x))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[CONVEX_ON_LEFT_SECANT_MUL];
    REWRITE_TAC[CONVEX_ON_RIGHT_SECANT_MUL]] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `a:real^N` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `b:real^N` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `(a:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(b:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; NOT_IN_EMPTY; REAL_SUB_REFL; VECTOR_SUB_REFL;
                  NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  MAP_EVERY ASM_CASES_TAC [`x:real^N = a`; `x:real^N = b`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_SUB_REFL; VECTOR_SUB_REFL; NORM_0;
                  REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM REAL_LE_LDIV_EQ; NORM_POS_LT;
               VECTOR_SUB_EQ] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Starlike sets and more stuff about line segments.                         *)
(* ------------------------------------------------------------------------- *)

let starlike = new_definition
 `starlike s <=> ?a. a IN s /\ !x. x IN s ==> segment[a,x] SUBSET s`;;

let CONVEX_IMP_STARLIKE = prove
 (`!s. convex s /\ ~(s = {}) ==> starlike s`,
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT; starlike; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[]);;

let SEGMENT_CONVEX_HULL = prove
 (`!a b. segment[a,b] = convex hull {a,b}`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CONVEX_HULL_INSERT; CONVEX_HULL_SING; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IN_SING; RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
  REWRITE_TAC[segment; EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_ARITH `u + v = &1 <=> u = &1 - v`] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> c /\ a /\ b /\ d`] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[REAL_LE_SUB_LADD; REAL_ADD_LID] THEN MESON_TAC[]);;

let SEGMENT_FURTHEST_LE = prove
 (`!a b x y:real^N.
        x IN segment[a,b] ==> norm(y - x) <= norm(y - a) \/
                              norm(y - x) <= norm(y - b)`,
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real^N`; `{a:real^N,b}`] SIMPLEX_FURTHEST_LE) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_RULES; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
  ASM_MESON_TAC[NORM_SUB]);;

let SEGMENT_BOUND = prove
 (`!a b x:real^N.
        x IN segment[a,b] ==> norm(x - a) <= norm(b - a) /\
                              norm(x - b) <= norm(b - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real^N`; `b:real^N`; `x:real^N`] SEGMENT_FURTHEST_LE) THENL
   [DISCH_THEN(MP_TAC o SPEC `a:real^N`);
    DISCH_THEN(MP_TAC o SPEC `b:real^N`)] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
  ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS; NORM_SUB]);;

let BETWEEN_IN_CONVEX_HULL = prove
 (`!x a b:real^N. between x (a,b) <=> x IN convex hull {a,b}`,
  REWRITE_TAC[BETWEEN_IN_SEGMENT; SEGMENT_CONVEX_HULL]);;

let STARLIKE_LINEAR_IMAGE = prove
 (`!f s. starlike s /\ linear f ==> starlike(IMAGE f s)`,
  REWRITE_TAC[starlike; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  SIMP_TAC[CLOSED_SEGMENT_LINEAR_IMAGE] THEN SET_TAC[]);;

let STARLIKE_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (starlike (IMAGE f s) <=> starlike s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE STARLIKE_LINEAR_IMAGE));;

add_linear_invariants [STARLIKE_LINEAR_IMAGE_EQ];;

let STARLIKE_TRANSLATION_EQ = prove
 (`!a s. starlike (IMAGE (\x. a + x) s) <=> starlike s`,
  REWRITE_TAC[starlike] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [STARLIKE_TRANSLATION_EQ];;

let BETWEEN_LINEAR_IMAGE_EQ = prove
 (`!f x y z. linear f /\ (!x y. f x = f y ==> x = y)
             ==> (between (f x) (f y,f z) <=> between x (y,z))`,
  SIMP_TAC[BETWEEN_IN_SEGMENT; CLOSED_SEGMENT_LINEAR_IMAGE] THEN SET_TAC[]);;

add_linear_invariants [BETWEEN_LINEAR_IMAGE_EQ];;

let BETWEEN_TRANSLATION = prove
 (`!a x y. between (a + x) (a + y,a + z) <=> between x (y,z)`,
  REWRITE_TAC[between] THEN NORM_ARITH_TAC);;

add_translation_invariants [STARLIKE_TRANSLATION_EQ];;

let STARLIKE_CLOSURE = prove
 (`!s:real^N->bool. starlike s ==> starlike(closure s)`,
  GEN_TAC THEN REWRITE_TAC[starlike; SUBSET; segment; FORALL_IN_GSPEC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[SUBSET; CLOSURE_APPROACHABLE] THEN
  DISCH_TAC THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(&1 - u) % a + u % y:real^N` THEN
  ASM_SIMP_TAC[dist; NORM_MUL; VECTOR_ARITH
   `(v % a + u % y) - (v % a + u % z):real^N = u % (y - z)`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_LET_TRANS)) THEN
  REWRITE_TAC[dist; REAL_ARITH `u * n <= n <=> &0 <= n * (&1 - u)`] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  ASM_REAL_ARITH_TAC);;

let STARLIKE_UNIV = prove
 (`starlike(:real^N)`,
  MESON_TAC[CONVEX_IMP_STARLIKE; CONVEX_UNIV;
            BOUNDED_EMPTY; NOT_BOUNDED_UNIV]);;

let STARLIKE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        starlike s /\ starlike t ==> starlike(s PCROSS t)`,
  SIMP_TAC[starlike; EXISTS_IN_PCROSS; SUBSET; IN_SEGMENT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; IMP_IMP] THEN
  REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS] THEN MESON_TAC[]);;

let STARLIKE_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        starlike(s PCROSS t) <=> starlike s /\ starlike t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [ASM_REWRITE_TAC[PCROSS_EMPTY] THEN MESON_TAC[starlike; NOT_IN_EMPTY];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[PCROSS_EMPTY] THEN MESON_TAC[starlike; NOT_IN_EMPTY];
    ALL_TAC] THEN
  EQ_TAC THEN REWRITE_TAC[STARLIKE_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
     `(s:real^M->bool) PCROSS (t:real^N->bool)`] STARLIKE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
     `(s:real^M->bool) PCROSS (t:real^N->bool)`] STARLIKE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let BETWEEN_DIST_LT = prove
 (`!r a b c:real^N.
        dist(c,a) < r /\ dist(c,b) < r /\ between x (a,b) ==> dist(c,x) < r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex hull {a,b} SUBSET ball(c:real^N,r)` MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[CONVEX_BALL; INSERT_SUBSET; EMPTY_SUBSET; IN_BALL];
    ASM_SIMP_TAC[SUBSET; GSYM BETWEEN_IN_CONVEX_HULL; IN_BALL]]);;

let BETWEEN_DIST_LE = prove
 (`!r a b c:real^N.
      dist(c,a) <= r /\ dist(c,b) <= r /\ between x (a,b) ==> dist(c,x) <= r`,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex hull {a,b} SUBSET cball(c:real^N,r)` MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[CONVEX_CBALL; INSERT_SUBSET; EMPTY_SUBSET; IN_CBALL];
    ASM_SIMP_TAC[SUBSET; GSYM BETWEEN_IN_CONVEX_HULL; IN_CBALL]]);;

let BETWEEN_NORM_LT = prove
 (`!r a b x:real^N.
        norm a < r /\ norm b < r /\ between x (a,b) ==> norm x < r`,
  REWRITE_TAC[GSYM(CONJUNCT2(SPEC_ALL DIST_0)); BETWEEN_DIST_LT]);;

let BETWEEN_NORM_LE = prove
 (`!r a b x:real^N.
        norm a <= r /\ norm b <= r /\ between x (a,b) ==> norm x <= r`,
  REWRITE_TAC[GSYM(CONJUNCT2(SPEC_ALL DIST_0)); BETWEEN_DIST_LE]);;

let UNION_SEGMENT = prove
 (`!a b c:real^N.
        b IN segment[a,c]
        ==> segment[a,b] UNION segment[b,c] = segment[a,c]`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c:real^N = a` THENL
   [ASM_SIMP_TAC[SEGMENT_REFL; IN_SING; UNION_IDEMPOT];
    ONCE_REWRITE_TAC[UNION_COMM] THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP CONVEX_HULL_EXCHANGE_UNION) THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    REWRITE_TAC[IMAGE_CLAUSES; UNIONS_2] THEN
    BINOP_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Shrinking towards the interior of a convex set.                           *)
(* ------------------------------------------------------------------------- *)

let IN_INTERIOR_CONVEX_SHRINK = prove
 (`!s e x c:real^N.
     convex s /\ c IN interior s /\
     x IN s /\ &0 < e /\ e <= &1
     ==> x - e % (x - c) IN interior s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
  REWRITE_TAC[IN_INTERIOR; SUBSET; IN_BALL; dist] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e * d:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  X_GEN_TAC `y':real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&1 / e) % y' - ((&1 - e) / e) % x:real^N`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `norm (x - e % (x - c) - y':real^N) < e * d` THEN
    SUBGOAL_THEN `x - e % (x - c) - y':real^N =
                  e % (c - (&1 / e % y' - (&1 - e) / e % x))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC;
                   REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC;
      ASM_SIMP_TAC[NORM_MUL; REAL_LT_LMUL_EQ; real_abs; REAL_LT_IMP_LE]];
    DISCH_TAC THEN
    SUBGOAL_THEN `y' = (&1 - (&1 - e)) % (&1 / e % y' - (&1 - e) / e % x) +
                       (&1 - e) % x:real^N`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&1 - (&1 - e) = e`; VECTOR_SUB_LDISTRIB;
                   VECTOR_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      VECTOR_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

let IN_INTERIOR_CLOSURE_CONVEX_SHRINK = prove
 (`!s e x c:real^N.
     convex s /\ c IN interior s /\
     x IN closure s /\ &0 < e /\ e <= &1
     ==> x - e % (x - c) IN interior s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?y:real^N. y IN s /\ norm(y - x) * (&1 - e) < e * d`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(x:real^N) IN s` THENL
     [EXISTS_TAC `x:real^N` THEN
      ASM_SIMP_TAC[REAL_LT_MUL; VECTOR_SUB_REFL; NORM_0; REAL_MUL_LZERO];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [closure]) THEN
    ASM_REWRITE_TAC[IN_UNION; IN_ELIM_THM; LIMPT_APPROACHABLE; dist] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
     `e <= &1 ==> e = &1 \/ e < &1`)) THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; GSYM REAL_LT_RDIV_EQ; REAL_SUB_LT] THENL
     [DISCH_THEN(MP_TAC o SPEC `&1`) THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_01];
      DISCH_THEN(MP_TAC o SPEC `(e * d) / (&1 - e)`)] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_SUB_LT; REAL_MUL_LZERO; REAL_LT_MUL;
                 REAL_MUL_LID] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z:real^N = c + ((&1 - e) / e) % (x - y)` THEN
  SUBGOAL_THEN `x - e % (x - c):real^N = y - e % (y - z)` SUBST1_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_ADD_LDISTRIB] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC IN_INTERIOR_CONVEX_SHRINK THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
     MATCH_MP SUBSET_INTERIOR) THEN
  SIMP_TAC[INTERIOR_OPEN; OPEN_BALL] THEN
  REWRITE_TAC[IN_BALL; dist] THEN EXPAND_TAC "z" THEN
  REWRITE_TAC[NORM_ARITH `norm(c - (c + x)) = norm(x)`] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
  ASM_MESON_TAC[REAL_MUL_SYM; NORM_SUB]);;

let IN_INTERIOR_CLOSURE_CONVEX_SEGMENT = prove
 (`!s a b:real^N.
        convex s /\ a IN interior s /\ b IN closure s
        ==> segment(a,b) SUBSET interior s`,
  REWRITE_TAC[SUBSET; IN_SEGMENT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `(&1 - u) % a + u % b:real^N = b - (&1 - u) % (b - a)`] THEN
  MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Relative interior of a set.                                               *)
(* ------------------------------------------------------------------------- *)

let relative_interior = new_definition
 `relative_interior s =
   {x | ?t. open_in (subtopology euclidean (affine hull s)) t /\
            x IN t /\ t SUBSET s}`;;

let relative_frontier = new_definition
 `relative_frontier s = closure s DIFF relative_interior s`;;

let RELATIVE_INTERIOR = prove
 (`!s. relative_interior s =
          {x | x IN s /\
               ?t. open t /\ x IN t /\ t INTER (affine hull s) SUBSET s}`,
  REWRITE_TAC[EXTENSION; relative_interior; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> b /\ a /\ c /\ d`] THEN
  REWRITE_TAC[UNWIND_THM2; SUBSET; IN_INTER; RIGHT_AND_EXISTS_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MESON_TAC[HULL_INC]);;

let RELATIVE_INTERIOR_EQ = prove
 (`!s. relative_interior s = s <=>
       open_in(subtopology euclidean (affine hull s)) s`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; relative_interior; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [OPEN_IN_SUBOPEN] THEN MESON_TAC[SUBSET]);;

let RELATIVE_INTERIOR_OPEN_IN = prove
 (`!s. open_in(subtopology euclidean (affine hull s)) s
       ==> relative_interior s = s`,
  REWRITE_TAC[RELATIVE_INTERIOR_EQ]);;

let RELATIVE_INTERIOR_EMPTY = prove
 (`relative_interior {} = {}`,
  SIMP_TAC[RELATIVE_INTERIOR_OPEN_IN; OPEN_IN_EMPTY]);;

let RELATIVE_FRONTIER_EMPTY = prove
 (`relative_frontier {} = {}`,
  REWRITE_TAC[relative_frontier; CLOSURE_EMPTY; EMPTY_DIFF]);;

let RELATIVE_INTERIOR_AFFINE = prove
 (`!s:real^N->bool. affine s ==> relative_interior s = s`,
  SIMP_TAC[RELATIVE_INTERIOR_EQ; OPEN_IN_SUBTOPOLOGY_REFL; HULL_P] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV]);;

let RELATIVE_INTERIOR_UNIV = prove
 (`!s. relative_interior(affine hull s) = affine hull s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RELATIVE_INTERIOR_OPEN_IN THEN
  REWRITE_TAC[HULL_HULL; OPEN_IN_SUBTOPOLOGY_REFL] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV]);;

let OPEN_IN_RELATIVE_INTERIOR = prove
 (`!s. open_in (subtopology euclidean (affine hull s))
               (relative_interior s)`,
  GEN_TAC THEN REWRITE_TAC[relative_interior] THEN
  GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let RELATIVE_INTERIOR_SUBSET = prove
 (`!s. (relative_interior s) SUBSET s`,
  REWRITE_TAC[SUBSET; relative_interior; IN_ELIM_THM] THEN MESON_TAC[]);;

let OPEN_IN_SET_RELATIVE_INTERIOR = prove
 (`!s:real^N->bool. open_in (subtopology euclidean s) (relative_interior s)`,
  GEN_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
  EXISTS_TAC `affine hull s:real^N->bool` THEN
  REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR; RELATIVE_INTERIOR_SUBSET;
              HULL_SUBSET]);;

let SUBSET_RELATIVE_INTERIOR = prove
 (`!s t. s SUBSET t /\ affine hull s = affine hull t
         ==> (relative_interior s) SUBSET (relative_interior t)`,
  REWRITE_TAC[relative_interior; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let RELATIVE_INTERIOR_MAXIMAL = prove
 (`!s t. t SUBSET s /\
         open_in(subtopology euclidean (affine hull s)) t
         ==> t SUBSET (relative_interior s)`,
  REWRITE_TAC[relative_interior; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let RELATIVE_INTERIOR_UNIQUE = prove
 (`!s t. t SUBSET s /\
         open_in(subtopology euclidean (affine hull s)) t /\
         (!t'. t' SUBSET s /\
               open_in(subtopology euclidean (affine hull s)) t'
               ==> t' SUBSET t)
         ==> (relative_interior s = t)`,
  MESON_TAC[SUBSET_ANTISYM; RELATIVE_INTERIOR_MAXIMAL; RELATIVE_INTERIOR_SUBSET;
            OPEN_IN_RELATIVE_INTERIOR]);;

let IN_RELATIVE_INTERIOR = prove
 (`!x:real^N s.
        x IN relative_interior s <=>
        x IN s /\ ?e. &0 < e /\ (ball(x,e) INTER (affine hull s)) SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[relative_interior; IN_ELIM_THM] THEN
  REWRITE_TAC[OPEN_IN_OPEN; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> b /\ a /\ c /\ d`] THEN
  REWRITE_TAC[UNWIND_THM2; SUBSET; IN_INTER] THEN EQ_TAC THENL
   [ASM_MESON_TAC[SUBSET; OPEN_CONTAINS_BALL];
    STRIP_TAC THEN EXISTS_TAC `ball(x:real^N,e)` THEN
    ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL; HULL_INC]]);;

let IN_RELATIVE_INTERIOR_CBALL = prove
 (`!x:real^N s.
        x IN relative_interior s <=>
        x IN s /\ ?e. &0 < e /\ (cball(x,e) INTER affine hull s) SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN
  AP_TERM_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(x:real^N,e) INTER affine hull s` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_CBALL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`];
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(x:real^N,e) INTER affine hull s` THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[SUBSET; IN_INTER; IN_BALL; IN_CBALL; REAL_LT_IMP_LE]]);;

let OPEN_IN_SUBSET_RELATIVE_INTERIOR = prove
 (`!s t. open_in(subtopology euclidean (affine hull t)) s
         ==> (s SUBSET relative_interior t <=> s SUBSET t)`,
  MESON_TAC[RELATIVE_INTERIOR_MAXIMAL; RELATIVE_INTERIOR_SUBSET;
            SUBSET_TRANS]);;

let RELATIVE_INTERIOR_TRANSLATION = prove
 (`!a:real^N s.
        relative_interior (IMAGE (\x. a + x) s) =
        IMAGE (\x. a + x) (relative_interior s)`,
  REWRITE_TAC[relative_interior; OPEN_IN_OPEN] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [RELATIVE_INTERIOR_TRANSLATION];;

let RELATIVE_FRONTIER_TRANSLATION = prove
 (`!a:real^N s.
        relative_frontier (IMAGE (\x. a + x) s) =
        IMAGE (\x. a + x) (relative_frontier s)`,
  REWRITE_TAC[relative_frontier] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [RELATIVE_FRONTIER_TRANSLATION];;

let RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> relative_interior(IMAGE f s) = IMAGE f (relative_interior s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[relative_interior; AFFINE_HULL_LINEAR_IMAGE] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> c /\ a /\ b`] THEN
  REWRITE_TAC[EXISTS_SUBSET_IMAGE] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_INJECTIVE_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

add_linear_invariants [RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE];;

let RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> relative_frontier(IMAGE f s) = IMAGE f (relative_frontier s)`,
  REWRITE_TAC[relative_frontier] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE];;

let RELATIVE_INTERIOR_EQ_EMPTY = prove
 (`!s:real^N->bool.
        convex s ==> (relative_interior s = {} <=> s = {})`,
  SUBGOAL_THEN
   `!s:real^N->bool.
        vec 0 IN s /\ convex s ==> ~(relative_interior s = {})`
  ASSUME_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (\x:real^N. --a + x) s`) THEN
    REWRITE_TAC[CONVEX_TRANSLATION_EQ; RELATIVE_INTERIOR_TRANSLATION] THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC] THEN
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_RELATIVE_INTERIOR] THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC] THEN
  X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC
   (ISPEC `s:real^N->bool` BASIS_EXISTS) THEN
  SUBGOAL_THEN `span(s:real^N->bool) = span b` SUBST_ALL_TAC THENL
   [ASM_SIMP_TAC[SPAN_EQ] THEN ASM_MESON_TAC[SPAN_INC; SUBSET_TRANS];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ABBREV_TAC `n = dim(s:real^N->bool)` THEN
  SUBGOAL_THEN
   `!c. (!v. v IN b ==> &0 <= c(v)) /\ sum b c <= &1
        ==> vsum b (\v:real^N. c(v) % v) IN s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `vsum (vec 0 INSERT b :real^N->bool)
           (\v. (if v = vec 0 then &1 - sum b c else c v) % v) IN s`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_EXPLICIT]) THEN
      ASM_SIMP_TAC[INSERT_SUBSET; FINITE_INSERT; SUM_CLAUSES;
                   INDEPENDENT_NONZERO; IN_INSERT] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_SUB_LE]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&1 - x + y = &1 <=> x = y`] THEN
      MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[INDEPENDENT_NONZERO];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[VSUM_CLAUSES; INDEPENDENT_NONZERO] THEN
      REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
      MATCH_MP_TAC VSUM_EQ THEN ASM_MESON_TAC[INDEPENDENT_NONZERO]];
    ALL_TAC] THEN
  ABBREV_TAC `a:real^N = vsum b (\v. inv(&2 * &n + &1) % v)` THEN
  EXISTS_TAC `a:real^N` THEN CONJ_TAC THENL
   [EXPAND_TAC "a" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SUM_CONST; REAL_LE_INV_EQ; REAL_ARITH `&0 < &2 * &n + &1`;
                 GSYM real_div; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `inv(&2 * &n + &1)`]
        BASIS_COORDINATES_CONTINUOUS) THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUBSET; IN_INTER; IMP_CONJ_ALT] THEN
  ASM_SIMP_TAC[SPAN_FINITE; LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
  GEN_TAC THEN X_GEN_TAC `u:real^N->real` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_BALL; dist] THEN
  EXPAND_TAC "a" THEN ASM_SIMP_TAC[GSYM VSUM_SUB] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
  REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[REAL_ARITH `abs(x - y) < x <=> &0 < y /\ abs(y) < &2 * x`] THEN
  SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(b:real^N->bool)) * &2 * inv(&2 * &n + &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_BOUND THEN
    ASM_SIMP_TAC[REAL_ARITH `abs x < a ==> x <= a`];
    ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &2 * &n + &1`] THEN
    REAL_ARITH_TAC]);;

let RELATIVE_INTERIOR_INTERIOR = prove
 (`!s. affine hull s = (:real^N)
       ==> relative_interior s = interior s`,
  SIMP_TAC[relative_interior; interior; SUBTOPOLOGY_UNIV; OPEN_IN]);;

let RELATIVE_INTERIOR_OPEN = prove
 (`!s:real^N->bool. open s ==> relative_interior s = s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[RELATIVE_INTERIOR_EMPTY] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR; AFFINE_HULL_OPEN; INTERIOR_EQ]);;

let RELATIVE_INTERIOR_NONEMPTY_INTERIOR = prove
 (`!s. ~(interior s = {}) ==> relative_interior s = interior s`,
  MESON_TAC[RELATIVE_INTERIOR_INTERIOR; AFFINE_HULL_NONEMPTY_INTERIOR]);;

let RELATIVE_FRONTIER_NONEMPTY_INTERIOR = prove
 (`!s. ~(interior s = {}) ==> relative_frontier s = frontier s`,
  SIMP_TAC[relative_frontier; frontier; RELATIVE_INTERIOR_NONEMPTY_INTERIOR]);;

let RELATIVE_FRONTIER_FRONTIER = prove
 (`!s. affine hull s = (:real^N) ==> relative_frontier s = frontier s`,
  SIMP_TAC[relative_frontier; frontier; RELATIVE_INTERIOR_INTERIOR]);;

let AFFINE_HULL_CONVEX_HULL = prove
 (`!s. affine hull (convex hull s) = affine hull s`,
  GEN_TAC THEN MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[AFFINE_AFFINE_HULL; CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_MESON_TAC[SUBSET_TRANS; HULL_SUBSET]);;

let INTERIOR_SIMPLEX_NONEMPTY = prove
 (`!s:real^N->bool.
        independent s /\ s HAS_SIZE (dimindex(:N))
        ==> ?a. a IN interior(convex hull (vec 0 INSERT s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `convex hull (vec 0 INSERT s):real^N->bool`
    RELATIVE_INTERIOR_EQ_EMPTY) THEN
  ASM_SIMP_TAC[AFFINE_HULL_CONVEX_HULL] THEN
  REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; CONVEX_CONVEX_HULL; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; IN_INSERT; HULL_INC] THEN
  MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
  EXISTS_TAC `span s:real^N->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_MONO THEN MATCH_MP_TAC(SET_RULE
     `(a INSERT s) SUBSET P hull (a INSERT s)
      ==> s SUBSET P hull (a INSERT s)`) THEN REWRITE_TAC[HULL_SUBSET];
    MATCH_MP_TAC(SET_RULE `UNIV SUBSET s ==> s = UNIV`) THEN
    MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
    ASM_REWRITE_TAC[DIM_UNIV; SUBSET_UNIV] THEN
    ASM_MESON_TAC[LE_REFL;HAS_SIZE]]);;

let INTERIOR_SUBSET_RELATIVE_INTERIOR = prove
 (`!s. interior s SUBSET relative_interior s`,
  REWRITE_TAC[SUBSET; IN_INTERIOR; IN_RELATIVE_INTERIOR; IN_INTER] THEN
  MESON_TAC[CENTRE_IN_BALL]);;

let CONVEX_RELATIVE_INTERIOR = prove
 (`!s:real^N->bool. convex s ==> convex(relative_interior s)`,
  REWRITE_TAC[CONVEX_ALT; IN_RELATIVE_INTERIOR; IN_INTER;
              SUBSET; IN_BALL; dist] THEN
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `(a /\ b) /\ (c /\ d) /\ e ==> f <=>
                    a /\ c /\ e ==> b /\ d ==> f`] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(MESON[] `(!d e. P d /\ Q e ==> R(min d e))
                        ==> (?e. P e) /\ (?e. Q e) ==> (?e. R e)`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  SUBST1_TAC(VECTOR_ARITH `z:real^N =
   (&1 - u) % (z - u % (y - x)) + u % (z + (&1 - u) % (y - x))`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN MATCH_MP_TAC MONO_AND THEN
  CONJ_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  (CONJ_TAC THENL
    [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
      `norm x < e ==> norm x = y ==> y < e`)) THEN
     AP_TERM_TAC THEN VECTOR_ARITH_TAC;
     REWRITE_TAC[VECTOR_ARITH `a - b % c:real^N = a + --b % c`] THEN
     MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
     ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC]]));;

let IN_RELATIVE_INTERIOR_CONVEX_SHRINK = prove
 (`!s e x c:real^N.
     convex s /\ c IN relative_interior s /\
     x IN s /\ &0 < e /\ e <= &1
     ==> x - e % (x - c) IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]) THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR; SUBSET; IN_INTER; IN_BALL; dist] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH
     `x - e % (x - c):real^N = (&1 - e) % x + e % c`] THEN
    FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `e * d:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  X_GEN_TAC `y':real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&1 / e) % y' - ((&1 - e) / e) % x:real^N`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `norm (x - e % (x - c) - y':real^N) < e * d` THEN
      SUBGOAL_THEN `x - e % (x - c) - y':real^N =
                    e % (c - (&1 / e % y' - (&1 - e) / e % x))`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC;
                     REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC;
        ASM_SIMP_TAC[NORM_MUL; REAL_LT_LMUL_EQ; real_abs; REAL_LT_IMP_LE]];
      REWRITE_TAC[real_div; REAL_SUB_RDISTRIB] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[VECTOR_ARITH `a % y - (b - c) % x:real^N =
                                (c - b) % x + a % y`] THEN
      MATCH_MP_TAC(REWRITE_RULE[AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
      ASM_SIMP_TAC[HULL_INC]];
    DISCH_TAC THEN
    SUBGOAL_THEN `y' = (&1 - (&1 - e)) % (&1 / e % y' - (&1 - e) / e % x) +
                       (&1 - e) % x:real^N`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&1 - (&1 - e) = e`; VECTOR_SUB_LDISTRIB;
                   VECTOR_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      VECTOR_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

let IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK = prove
 (`!s e x c:real^N.
     convex s /\ c IN relative_interior s /\
     x IN closure s /\ &0 < e /\ e <= &1
     ==> x - e % (x - c) IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?y:real^N. y IN s /\ norm(y - x) * (&1 - e) < e * d`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(x:real^N) IN s` THENL
     [EXISTS_TAC `x:real^N` THEN
      ASM_SIMP_TAC[REAL_LT_MUL; VECTOR_SUB_REFL; NORM_0; REAL_MUL_LZERO];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [closure]) THEN
    ASM_REWRITE_TAC[IN_UNION; IN_ELIM_THM; LIMPT_APPROACHABLE; dist] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
     `e <= &1 ==> e = &1 \/ e < &1`)) THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; GSYM REAL_LT_RDIV_EQ; REAL_SUB_LT] THENL
     [DISCH_THEN(MP_TAC o SPEC `&1`) THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_01];
      DISCH_THEN(MP_TAC o SPEC `(e * d) / (&1 - e)`)] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_SUB_LT; REAL_MUL_LZERO; REAL_LT_MUL;
                 REAL_MUL_LID] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z:real^N = c + ((&1 - e) / e) % (x - y)` THEN
  SUBGOAL_THEN `x - e % (x - c):real^N = y - e % (y - z)` SUBST1_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_ADD_LDISTRIB] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC IN_RELATIVE_INTERIOR_CONVEX_SHRINK THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dist(c:real^N,z) < d` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[NORM_ARITH `dist(c:real^N,c + x) = norm x`] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_DIV] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    REWRITE_TAC[REAL_ARITH `a / b * c:real = (c * a) / b`] THEN
    ASM_SIMP_TAC[real_abs; REAL_SUB_LE; REAL_LT_IMP_LE; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN affine hull s` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC] THEN
    MATCH_MP_TAC(SET_RULE `!t. x IN t /\ t = s ==> x IN s`) THEN
    EXISTS_TAC `closure(affine hull s):real^N->bool` THEN
    SIMP_TAC[CLOSURE_EQ; CLOSED_AFFINE_HULL] THEN
    ASM_MESON_TAC[SUBSET_CLOSURE; HULL_INC; SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[IN_BALL; IN_INTER; SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `d - dist(c:real^N,z)` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS)) THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `dist(c:real^N,z) < d` THEN REWRITE_TAC[IN_BALL] THEN
  NORM_ARITH_TAC);;

let IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT = prove
 (`!s a b:real^N.
        convex s /\ a IN relative_interior s /\ b IN closure s
        ==> segment(a,b) SUBSET relative_interior s`,
  REWRITE_TAC[SUBSET; IN_SEGMENT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `(&1 - u) % a + u % b:real^N = b - (&1 - u) % (b - a)`] THEN
  MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CONVEX_OPEN_SEGMENT_CASES = prove
 (`!s a b:real^N.
        convex s /\ a IN closure s /\ b IN closure s
        ==> segment(a,b) SUBSET relative_frontier s \/
            segment(a,b) SUBSET relative_interior s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[relative_frontier] THEN
  MATCH_MP_TAC(SET_RULE
   `s SUBSET c /\ (!a. a IN i /\ a IN s ==> s SUBSET i)
    ==> s SUBSET c DIFF i \/ s SUBSET i`) THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[CONVEX_CONTAINS_OPEN_SEGMENT; CONVEX_CLOSURE];
    X_GEN_TAC `c:real^N` THEN ONCE_REWRITE_TAC[segment]] THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; DE_MORGAN_THM; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP UNION_SEGMENT) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c:real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `b:real^N` th) THEN MP_TAC(SPEC `a:real^N` th)) THEN
  ASM_REWRITE_TAC[SEGMENT_SYM; CONJUNCT2 segment] THEN ASM SET_TAC[]);;

let RELATIVE_INTERIOR_SING = prove
 (`!a. relative_interior {a} = {a}`,
  GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `s SUBSET {a} /\ ~(s = {}) ==> s = {a}`) THEN
  SIMP_TAC[RELATIVE_INTERIOR_SUBSET; RELATIVE_INTERIOR_EQ_EMPTY;
           CONVEX_SING] THEN
  SET_TAC[]);;

let RELATIVE_FRONTIER_SING = prove
 (`!a:real^N. relative_frontier {a} = {}`,
  REWRITE_TAC[relative_frontier; RELATIVE_INTERIOR_SING; CLOSURE_SING] THEN
  SET_TAC[]);;

let RELATIVE_INTERIOR_CBALL = prove
 (`!a r. relative_interior(cball(a,r)) = if r = &0 then {a} else ball(a,r)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NE; CBALL_EMPTY; BALL_EMPTY;
               RELATIVE_INTERIOR_EMPTY; REAL_LT_IMP_LE] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[CBALL_SING; RELATIVE_INTERIOR_SING] THEN
  REWRITE_TAC[GSYM INTERIOR_CBALL] THEN
  MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR THEN
  ASM_REWRITE_TAC[INTERIOR_CBALL; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC);;

let RELATIVE_INTERIOR_BALL = prove
 (`!a r. relative_interior(ball(a,r)) = ball(a,r)`,
  SIMP_TAC[RELATIVE_INTERIOR_OPEN; OPEN_BALL]);;

let RELATIVE_FRONTIER_CBALL = prove
 (`!a:real^N r. relative_frontier(cball(a,r)) =
                if r = &0 then {} else sphere(a,r)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CBALL_SING; RELATIVE_FRONTIER_SING] THEN
  ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[CBALL_EMPTY; SPHERE_EMPTY; RELATIVE_FRONTIER_EMPTY] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; INTERIOR_CBALL;
               BALL_EQ_EMPTY; GSYM REAL_NOT_LT; FRONTIER_CBALL]);;

let RELATIVE_FRONTIER_BALL = prove
 (`!a:real^N r. relative_frontier(ball(a,r)) =
                if r = &0 then {} else sphere(a,r)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[BALL_EMPTY; REAL_LE_REFL; RELATIVE_FRONTIER_EMPTY] THEN
  ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[BALL_EMPTY; REAL_LT_IMP_LE; SPHERE_EMPTY;
               RELATIVE_FRONTIER_EMPTY] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; INTERIOR_OPEN; OPEN_BALL;
               BALL_EQ_EMPTY; GSYM REAL_NOT_LT; FRONTIER_BALL]);;

let STARLIKE_CONVEX_TWEAK_BOUNDARY_POINTS = prove
 (`!s t:real^N->bool.
        convex s /\ ~(s = {}) /\
        relative_interior s SUBSET t /\ t SUBSET closure s
        ==> starlike t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(relative_interior s:real^N->bool = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; REWRITE_TAC[starlike]] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `a:real^N` THEN
  REPEAT STRIP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `a IN s /\ b IN s /\ segment[a,b] DIFF {a,b} SUBSET s
    ==> segment[a:real^N,b] SUBSET s`) THEN
  ASM_REWRITE_TAC[GSYM open_segment] THEN
  ASM_MESON_TAC[IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT; SUBSET]);;

let RELATIVE_INTERIOR_PROLONG = prove
 (`!s x y:real^N.
        x IN relative_interior s /\ y IN s
        ==> ?t. &1 < t /\ (y + t % (x - y)) IN s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR_CBALL; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real`
  STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `y:real^N = x` THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `y + t % (x - x):real^N = y`] THEN
    EXISTS_TAC `&2` THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    EXISTS_TAC `&1 + e / norm(x - y:real^N)` THEN
    ASM_SIMP_TAC[REAL_LT_ADDR; REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    REWRITE_TAC[VECTOR_ARITH
     `y + (&1 + e) % (x - y):real^N = x + e % (x - y)`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; IN_INTER; IN_AFFINE_ADD_MUL_DIFF;
                 HULL_INC; IN_CBALL] THEN
    REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

let RELATIVE_INTERIOR_CONVEX_PROLONG = prove
 (`!s. convex s
       ==> relative_interior s =
           {x:real^N | x IN s /\
                       !y. y IN s ==> ?t. &1 < t /\ (y + t % (x - y)) IN s}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [SIMP_TAC[RELATIVE_INTERIOR_PROLONG] THEN
    MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    STRIP_TAC THEN
    SUBGOAL_THEN `?y:real^N. y IN relative_interior s` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[MEMBER_NOT_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_CASES_TAC `y:real^N = x` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `y:real^N`; `y + t % (x - y):real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; CLOSURE_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SEGMENT; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `y:real^N = y + x <=> x = vec 0`;
      VECTOR_ARITH `(&1 - u) % y + u % (y + t % (x - y)):real^N =
                    y + t % u % (x - y)`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `inv t:real` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_INV_EQ;
      REAL_INV_LT_1; REAL_LT_IMP_NZ; REAL_ARITH `&1 < x ==> &0 < x`] THEN
    VECTOR_ARITH_TAC]);;

let RELATIVE_INTERIOR_EQ_CLOSURE = prove
 (`!s:real^N->bool.
        relative_interior s = closure s <=> affine s`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[RELATIVE_INTERIOR_EMPTY; CLOSURE_EMPTY; AFFINE_EMPTY] THEN
  EQ_TAC THEN
  SIMP_TAC[RELATIVE_INTERIOR_AFFINE; CLOSURE_CLOSED; CLOSED_AFFINE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `relative_interior s = closure s
    ==> relative_interior s SUBSET s /\ s SUBSET closure s
        ==> relative_interior s = s /\ closure s = s`)) THEN
  REWRITE_TAC[RELATIVE_INTERIOR_SUBSET; CLOSURE_SUBSET] THEN
  REWRITE_TAC[RELATIVE_INTERIOR_EQ; CLOSURE_EQ; GSYM AFFINE_HULL_EQ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `~(s = {}) ==> s = {} \/ s = a ==> a = s`)) THEN
  MP_TAC(ISPEC `affine hull s:real^N->bool` CONNECTED_CLOPEN) THEN
  SIMP_TAC[AFFINE_IMP_CONVEX; CONVEX_CONNECTED; AFFINE_AFFINE_HULL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[HULL_SUBSET]);;

let RAY_TO_RELATIVE_FRONTIER = prove
 (`!s a l:real^N.
        bounded s /\ a IN relative_interior s /\
        (a + l) IN affine hull s /\ ~(l = vec 0)
        ==> ?d. &0 < d /\
                (a + d % l) IN relative_frontier s /\
                !e. &0 <= e /\ e < d ==> (a + e % l) IN relative_interior s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[relative_frontier] THEN
  MP_TAC(ISPEC
   `{d | &0 < d /\ ~((a + d % l:real^N) IN relative_interior(s))}` INF) THEN
  ABBREV_TAC
   `d = inf {d | &0 < d /\ ~((a + d % l:real^N) IN relative_interior(s))}` THEN
  SUBGOAL_THEN
   `?e. &0 < e /\ !d. &0 <= d /\ d < e
                      ==> (a + d % l:real^N) IN relative_interior s`
   (X_CHOOSE_THEN `k:real` (LABEL_TAC "0"))
  THENL
   [MP_TAC(ISPEC `s:real^N->bool` OPEN_IN_RELATIVE_INTERIOR) THEN
    REWRITE_TAC[open_in; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e / norm(l:real^N)` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT] THEN X_GEN_TAC `x:real` THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC IN_AFFINE_ADD_MUL THEN
      ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
      ASM_MESON_TAC[SUBSET; HULL_SUBSET; RELATIVE_INTERIOR_SUBSET];
      REWRITE_TAC[NORM_ARITH `dist(a + x:real^N,a) = norm x`] THEN
      ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LT_RDIV_EQ; NORM_POS_LT] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_NOT_LT; REAL_LT_IMP_LE]] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o
       MATCH_MP BOUNDED_SUBSET_BALL) THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B / norm(l:real^N)` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
     [GSYM CONTRAPOS_THM]) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[NORM_ARITH `dist(a:real^N,a + x) = norm x`] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM;
                 REAL_DIV_RMUL; NORM_EQ_0] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "1") (LABEL_TAC "2")) THEN
    EXISTS_TAC `d:real` THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `k:real` THEN
      ASM_MESON_TAC[REAL_NOT_LT; REAL_LT_IMP_LE];
      DISCH_TAC] THEN
    MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_LT] THEN
      ASM_MESON_TAC[VECTOR_ARITH `a + &0 % l:real^N = a`;
                    REAL_NOT_LT; REAL_LT_IMP_LE];
      DISCH_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      EXISTS_TAC `a + (d - min d (x / &2 / norm(l:real^N))) % l` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x /\ &0 < d ==> d - min d x < d`) THEN
        ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; NORM_POS_LT];
        REWRITE_TAC[NORM_ARITH `dist(a + x:real^N,a + y) = norm(x - y)`] THEN
        REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
        ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_POS_LT] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 < x /\ x < y /\ &0 < d ==> abs((d - min d x) - d) < y`) THEN
        REWRITE_TAC[REAL_ARITH `x / &2 / y < x / y <=> &0 < x / y`] THEN
        ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; NORM_POS_LT]];
      DISCH_TAC THEN
      MP_TAC(ISPEC `s:real^N->bool` OPEN_IN_RELATIVE_INTERIOR) THEN
      REWRITE_TAC[open_in; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `a + d % l:real^N` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real`
       (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "3"))) THEN
      REMOVE_THEN "2" (MP_TAC o SPEC `d + e / norm(l:real^N)`) THEN
      ASM_SIMP_TAC[NOT_IMP; REAL_ARITH `~(d + l <= d) <=> &0 < l`;
                   REAL_LT_DIV; NORM_POS_LT] THEN
      X_GEN_TAC `x:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
      ASM_CASES_TAC `x < d` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REMOVE_THEN "3" MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC IN_AFFINE_ADD_MUL THEN
        ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
        ASM_MESON_TAC[SUBSET; HULL_SUBSET; RELATIVE_INTERIOR_SUBSET];
        REWRITE_TAC[NORM_ARITH `dist(a + x:real^N,a + y) = norm(x - y)`] THEN
        REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
        ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_POS_LT] THEN
        ASM_REAL_ARITH_TAC]]]);;

let RAY_TO_FRONTIER = prove
 (`!s a l:real^N.
        bounded s /\ a IN interior s /\ ~(l = vec 0)
        ==> ?d. &0 < d /\ (a + d % l) IN frontier s /\
                !e. &0 <= e /\ e < d ==> (a + e % l) IN interior s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier] THEN
  SUBGOAL_THEN `interior s:real^N->bool = relative_interior s` SUBST1_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM relative_frontier] THEN
    MATCH_MP_TAC RAY_TO_RELATIVE_FRONTIER THEN ASM_REWRITE_TAC[]] THEN
  ASM_MESON_TAC[NOT_IN_EMPTY; RELATIVE_INTERIOR_NONEMPTY_INTERIOR; IN_UNIV;
                AFFINE_HULL_NONEMPTY_INTERIOR]);;

let RELATIVE_FRONTIER_NOT_SING = prove
 (`!s a:real^N. bounded s ==> ~(relative_frontier s = {a})`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[RELATIVE_FRONTIER_EMPTY; NOT_INSERT_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN
  ASM_CASES_TAC `s = {z:real^N}` THEN
  ASM_REWRITE_TAC[RELATIVE_FRONTIER_SING; NOT_INSERT_EMPTY] THEN
  SUBGOAL_THEN `?w:real^N. w IN s /\ ~(w = z)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; REPEAT STRIP_TAC] THEN
  SUBGOAL_THEN
    `~((w:real^N) IN relative_frontier s /\ z IN relative_frontier s)`
  MP_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`relative_frontier s = {a:real^N}`; `bounded(s:real^N->bool)`;
    `~(w:real^N = z)`; `(z:real^N) IN s`; `(w:real^N) IN s`;
    `~((w:real^N) IN relative_frontier s /\ z IN relative_frontier s)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[DE_MORGAN_THM] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`z:real^N`; `w:real^N`] THEN
  MATCH_MP_TAC(MESON[]
   `(!w z. Q w z <=> Q z w) /\ (!w z. P z ==> Q w z)
    ==> !w z. P w \/ P z ==> Q w z`) THEN
  CONJ_TAC THENL [MESON_TAC[]; REPEAT GEN_TAC] THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  REWRITE_TAC[relative_frontier; IN_DIFF] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; CLOSURE_SUBSET]; DISCH_TAC] THEN
  MP_TAC(GEN `d:real`
   (ISPECL [`s:real^N->bool`; `z:real^N`; `d % (w - z):real^N`]
   RAY_TO_RELATIVE_FRONTIER)) THEN
  ASM_SIMP_TAC[VECTOR_SUB_EQ; IN_AFFINE_ADD_MUL_DIFF; AFFINE_AFFINE_HULL;
               HULL_INC; VECTOR_MUL_EQ_0] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `&1` th) THEN MP_TAC(SPEC `--(&1)` th)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (STRIP_ASSUME_TAC o GSYM)) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL; VECTOR_MUL_ASSOC; VECTOR_SUB_EQ;
                  VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  ASM_REAL_ARITH_TAC);;

let RELATIVE_INTERIOR_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        relative_interior(s PCROSS t) =
        relative_interior s PCROSS relative_interior t`,
  REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`s:real^M->bool = {}`; `t:real^N->bool = {}`] THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; RELATIVE_INTERIOR_EMPTY] THEN
  REWRITE_TAC[relative_interior; AFFINE_HULL_PCROSS] THEN
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_THM;
              PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^N`] THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> r /\ q /\ p`] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^(M,N)finite_sum->bool`
     (CONJUNCTS_THEN ASSUME_TAC)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PASTECART_IN_INTERIOR_SUBTOPOLOGY) THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (funpow 3 rand) SUBSET_PCROSS o snd) THEN
    ASM SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(v:real^M->bool) PCROSS (w:real^N->bool)` THEN
    ASM_SIMP_TAC[PASTECART_IN_PCROSS; SUBSET_PCROSS; OPEN_IN_PCROSS]]);;

let RELATIVE_FRONTIER_EQ_EMPTY = prove
 (`!s:real^N->bool. relative_frontier s = {} <=> affine s`,
  GEN_TAC THEN REWRITE_TAC[relative_frontier] THEN
  REWRITE_TAC[GSYM RELATIVE_INTERIOR_EQ_CLOSURE] THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN SET_TAC[]);;

let DIAMETER_BOUNDED_BOUND_LT = prove
 (`!s x y:real^N.
        bounded s /\ x IN relative_interior s /\ y IN closure s /\
        ~(diameter s = &0)
        ==> norm(x - y) < diameter s`,
  let lemma = prove
   (`!s x y:real^N.
          bounded s /\ x IN relative_interior s /\ y IN s /\
          ~(diameter s = &0)
          ==> norm(x - y) < diameter s`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM
     (MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR_CBALL]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real`
     STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[REAL_LT_LE; DIAMETER_BOUNDED_BOUND] THEN
    ASM_CASES_TAC `y:real^N = x` THEN
    ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `x + e / norm(x - y) % (x - y):real^N`) THEN
    REWRITE_TAC[NOT_IMP; IN_INTER] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_CBALL; NORM_ARITH `dist(x:real^M,x + y) = norm y`] THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL;
                   NORM_EQ_0; VECTOR_SUB_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
      ASM_SIMP_TAC[HULL_INC; AFFINE_AFFINE_HULL];
      DISCH_TAC THEN MP_TAC(ISPECL
       [`s:real^N->bool`; `x + e / norm(x - y) % (x - y):real^N`; `y:real^N`]
          DIAMETER_BOUNDED_BOUND) THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[VECTOR_ARITH
       `(x + e % (x - y)) - y:real^N = (&1 + e) % (x - y)`] THEN
      SIMP_TAC[NORM_MUL; REAL_ARITH `~(a * n <= n) <=> &0 < n * (a - &1)`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e ==> &0 < abs(&1 + e) - &1`) THEN
      MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`closure s:real^N->bool`; `x:real^N`; `y:real^N`]
        lemma) THEN
  ASM_SIMP_TAC[DIAMETER_CLOSURE; BOUNDED_CLOSURE] THEN
  DISCH_THEN MATCH_MP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (SET_RULE `x IN s ==> s SUBSET t ==> x IN t`)) THEN
  MATCH_MP_TAC SUBSET_RELATIVE_INTERIOR THEN
  REWRITE_TAC[CLOSURE_SUBSET; AFFINE_HULL_CLOSURE]);;

let DIAMETER_ATTAINED_RELATIVE_FRONTIER = prove
 (`!s:real^N->bool.
        bounded s /\ ~(diameter s = &0)
        ==> ?x y. x IN relative_frontier s /\
                  y IN relative_frontier s /\
                  norm(x - y) = diameter s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[DIAMETER_EMPTY; relative_frontier] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `closure s:real^N->bool` DIAMETER_COMPACT_ATTAINED) THEN
  ASM_SIMP_TAC[COMPACT_CLOSURE; CLOSURE_EQ_EMPTY; DIAMETER_CLOSURE] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` DIAMETER_BOUNDED_BOUND_LT) THENL
   [DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `y:real^N`]);
    DISCH_THEN(MP_TAC o SPECL [`y:real^N`; `x:real^N`])] THEN
  ASM_MESON_TAC[REAL_LT_REFL; NORM_SUB]);;

let DIAMETER_RELATIVE_FRONTIER = prove
 (`!s:real^N->bool.
        bounded s /\ ~(?a. s = {a})
        ==> diameter(relative_frontier s) = diameter s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[RELATIVE_FRONTIER_EMPTY] THEN
  REWRITE_TAC[relative_frontier] THEN
  ASM_SIMP_TAC[GSYM DIAMETER_CLOSURE; GSYM REAL_LE_ANTISYM] THEN
  ASM_SIMP_TAC[SUBSET_DIFF; DIAMETER_SUBSET; BOUNDED_CLOSURE] THEN
  ASM_SIMP_TAC[DIAMETER_CLOSURE] THEN
  MP_TAC(ISPEC `s:real^N->bool` DIAMETER_ATTAINED_RELATIVE_FRONTIER) THEN
  ASM_SIMP_TAC[DIAMETER_EQ_0; relative_frontier] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
  ASM_SIMP_TAC[BOUNDED_CLOSURE; BOUNDED_DIFF]);;

let DIAMETER_ATTAINED_FRONTIER = prove
 (`!s:real^N->bool.
        bounded s /\ ~(diameter s = &0)
        ==> ?x y. x IN frontier s /\ y IN frontier s /\
                  norm(x - y) = diameter s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIAMETER_ATTAINED_RELATIVE_FRONTIER) THEN
  REWRITE_TAC[frontier; relative_frontier; IN_DIFF] THEN
  MESON_TAC[REWRITE_RULE[SUBSET] INTERIOR_SUBSET_RELATIVE_INTERIOR]);;

let DIAMETER_FRONTIER = prove
 (`!s:real^N->bool. bounded s ==> diameter(frontier s) = diameter s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `?a:real^N. s = {a}` THENL
   [ASM_MESON_TAC[FRONTIER_SING]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!r. r <= f /\ f <= s /\ r = s ==> f = s`) THEN
  EXISTS_TAC `diameter(closure s DIFF relative_interior s:real^N->bool)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM DIAMETER_CLOSURE] THEN MATCH_MP_TAC DIAMETER_SUBSET THEN
    ASM_SIMP_TAC[BOUNDED_FRONTIER] THEN REWRITE_TAC[frontier] THEN
    MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
    SET_TAC[];
    ASM_SIMP_TAC[GSYM DIAMETER_CLOSURE] THEN MATCH_MP_TAC DIAMETER_SUBSET THEN
    ASM_SIMP_TAC[BOUNDED_CLOSURE; frontier; SUBSET_DIFF];
    ASM_SIMP_TAC[DIAMETER_RELATIVE_FRONTIER; GSYM relative_frontier]]);;

let DIAMETER_SPHERE = prove
 (`!a:real^N r. diameter(sphere(a,r)) = if r < &0 then &0 else &2 * r`,
  REWRITE_TAC[GSYM FRONTIER_CBALL] THEN
  ASM_SIMP_TAC[DIAMETER_FRONTIER; BOUNDED_CBALL; DIAMETER_CBALL]);;

let CLOSEST_POINT_IN_RELATIVE_INTERIOR = prove
 (`!s x:real^N.
        closed s /\ ~(s = {}) /\ x IN affine hull s
        ==> ((closest_point s x) IN relative_interior s <=>
             x IN relative_interior s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:real^N) IN s` THEN
  ASM_SIMP_TAC[CLOSEST_POINT_SELF] THEN
  MATCH_MP_TAC(TAUT `~q /\ ~p ==> (p <=> q)`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR_CBALL]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(closest_point s (x:real^N) = x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`;
   `closest_point s x -
    (min (&1) (e / norm(closest_point s x - x))) %
    (closest_point s x - x):real^N`]
    CLOSEST_POINT_LE) THEN
  ASM_REWRITE_TAC[dist; NOT_IMP; VECTOR_ARITH
   `x - (y - e % (y - x)):real^N = (&1 - e) % (x - y)`] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_CBALL; IN_INTER] THEN CONJ_TAC THENL
     [REWRITE_TAC[NORM_ARITH `dist(a:real^N,a - x) = norm x`] THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> abs(min (&1) a) <= a`) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_DIV; NORM_POS_LE];
      MATCH_MP_TAC IN_AFFINE_SUB_MUL_DIFF THEN
      ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC]];
    REWRITE_TAC[NORM_MUL; REAL_ARITH
     `~(n <= a * n) <=> &0 < (&1 - a) * n`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ e <= &1 ==> &0 < &1 - abs(&1 - e)`) THEN
    REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN; REAL_LT_01; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ]]);;

let CLOSEST_POINT_IN_RELATIVE_FRONTIER = prove
 (`!s x:real^N.
        closed s /\ ~(s = {}) /\ x IN affine hull s DIFF relative_interior s
        ==> closest_point s x IN relative_frontier s`,
  SIMP_TAC[relative_frontier; IN_DIFF; CLOSEST_POINT_IN_RELATIVE_INTERIOR] THEN
  MESON_TAC[CLOSURE_SUBSET; CLOSEST_POINT_IN_SET; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Interior, relative interior and closure interrelations.                   *)
(* ------------------------------------------------------------------------- *)

let CONVEX_CLOSURE_INTERIOR = prove
 (`!s:real^N->bool.
        convex s /\ ~(interior s = {})
        ==> closure(interior s) = closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET_CLOSURE; INTERIOR_SUBSET] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[closure; IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `b - min (e / &2 / norm(b - a)) (&1) % (b - a):real^N` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
    ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN; REAL_LE_REFL; REAL_LT_01];
    REWRITE_TAC[VECTOR_ARITH `b - x:real^N = b <=> x = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(min x (&1) = &0)`);
    REWRITE_TAC[NORM_ARITH `dist(b - x:real^N,b) = norm x`] THEN
    REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `e / &2 / norm(b - a:real^N) * norm(b - a)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> abs(min x (&1)) <= x`);
      ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_POS_LT; REAL_LT_IMP_NZ;
                   VECTOR_SUB_EQ] THEN
      ASM_REAL_ARITH_TAC]] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; REAL_OF_NUM_LT;
                 VECTOR_SUB_EQ; ARITH]);;

let EMPTY_INTERIOR_SUBSET_HYPERPLANE = prove
 (`!s. convex s /\ interior s = {}
       ==> ?a:real^N b. ~(a = vec 0) /\ s SUBSET {x | a dot x = b}`,
  let lemma = prove
   (`!s. convex s /\ (vec 0) IN s /\ interior s = {}
         ==> ?a:real^N b. ~(a = vec 0) /\ s SUBSET {x | a dot x = b}`,
    GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(relative_interior(s:real^N->bool) = {})` MP_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
    ASM_REWRITE_TAC[CONTRAPOS_THM] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC] THEN
    ONCE_REWRITE_TAC[GSYM SPAN_UNIV] THEN MATCH_MP_TAC DIM_EQ_SPAN THEN
    REWRITE_TAC[SUBSET_UNIV; DIM_UNIV; GSYM NOT_LT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LOWDIM_SUBSET_HYPERPLANE) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN EXISTS_TAC `&0` THEN
    ASM_MESON_TAC[SUBSET_TRANS; SPAN_INC]) in
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_MESON_TAC[EMPTY_SUBSET; BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. --a + x) s` lemma) THEN
  ASM_REWRITE_TAC[CONVEX_TRANSLATION_EQ; INTERIOR_TRANSLATION;
                  IMAGE_EQ_EMPTY; IN_IMAGE; UNWIND_THM2;
                  VECTOR_ARITH `vec 0:real^N = --a + x <=> x = a`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; DOT_RADD] THEN
  MESON_TAC[REAL_ARITH `a + x:real = b <=> x = b - a`]);;

let CONVEX_INTERIOR_CLOSURE = prove
 (`!s:real^N->bool. convex s ==> interior(closure s) = interior s`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interior(s:real^N->bool) = {}` THENL
   [MP_TAC(ISPEC `s:real^N->bool` EMPTY_INTERIOR_SUBSET_HYPERPLANE) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!t. s SUBSET t /\ t = {} ==> s = {}`) THEN
    EXISTS_TAC `interior {x:real^N | a dot x = b}` THEN CONJ_TAC THENL
     [ALL_TAC;  ASM_SIMP_TAC[INTERIOR_HYPERPLANE]] THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_REWRITE_TAC[CLOSED_HYPERPLANE];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET_INTERIOR; CLOSURE_SUBSET] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
  MP_TAC(ASSUME `(b:real^N) IN interior(closure s)`) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_INTERIOR_CBALL] THEN
  REWRITE_TAC[SUBSET; IN_CBALL; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `e:real` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `b:real^N = a` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `b + e / norm(b - a) % (b - a):real^N`) THEN
  ASM_SIMP_TAC[NORM_ARITH `dist(b:real^N,b + e) = norm e`; NORM_MUL;
    REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ;
    REAL_ARITH `&0 < e ==> abs e <= e`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `b = (b + e / norm(b - a) % (b - a)) -
        e / norm(b - a) / (&1 + e / norm(b - a)) %
        ((b + e / norm(b - a) % (b - a)) - a):real^N`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH
     `b = (b + e % (b - a)) - d % ((b + e % (b - a)) - a) <=>
      (e - d * (&1 + e)) % (b - a) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_EQ; VECTOR_MUL_EQ_0];
    MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SHRINK] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_DIV; NORM_POS_LT;
               VECTOR_SUB_EQ; REAL_ARITH `&0 < x ==> &0 < &1 + x`;
               REAL_ARITH `&0 < x ==> ~(&1 + x = &0)`;
               REAL_MUL_LID; REAL_ADD_RDISTRIB; REAL_DIV_RMUL;
               REAL_LT_IMP_NZ; REAL_LE_ADDL; NORM_POS_LE; REAL_SUB_REFL]);;

let FRONTIER_CLOSURE_CONVEX = prove
 (`!s:real^N->bool. convex s ==> frontier(closure s) = frontier s`,
  SIMP_TAC[frontier; CLOSURE_CLOSURE; CONVEX_INTERIOR_CLOSURE]);;

let CONVEX_CLOSURE_RELATIVE_INTERIOR = prove
 (`!s:real^N->bool.
        convex s ==> closure(relative_interior s) = closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET_CLOSURE; RELATIVE_INTERIOR_SUBSET] THEN
  ASM_CASES_TAC `relative_interior(s:real^N->bool) = {}` THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; SUBSET_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[closure; IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `b - min (e / &2 / norm(b - a)) (&1) % (b - a):real^N` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
    ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN; REAL_LE_REFL; REAL_LT_01];
    REWRITE_TAC[VECTOR_ARITH `b - x:real^N = b <=> x = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(min x (&1) = &0)`);
    REWRITE_TAC[NORM_ARITH `dist(b - x:real^N,b) = norm x`] THEN
    REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `e / &2 / norm(b - a:real^N) * norm(b - a)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> abs(min x (&1)) <= x`);
      ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_POS_LT; REAL_LT_IMP_NZ;
                   VECTOR_SUB_EQ] THEN
      ASM_REAL_ARITH_TAC]] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; REAL_OF_NUM_LT;
                 VECTOR_SUB_EQ; ARITH]);;

let AFFINE_HULL_RELATIVE_INTERIOR = prove
 (`!s. convex s
       ==> affine hull (relative_interior s) = affine hull s`,
  MESON_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; AFFINE_HULL_CLOSURE]);;

let CONVEX_RELATIVE_INTERIOR_CLOSURE = prove
 (`!s:real^N->bool.
        convex s ==> relative_interior(closure s) = relative_interior s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CLOSURE_EMPTY; RELATIVE_INTERIOR_EMPTY] THEN
  SUBGOAL_THEN `?a:real^N. a IN relative_interior s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEMBER_NOT_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IN_RELATIVE_INTERIOR; AFFINE_HULL_CLOSURE; SUBSET] THEN
    MESON_TAC[CLOSURE_SUBSET; SUBSET]] THEN
  X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
  MP_TAC(ASSUME `(b:real^N) IN relative_interior(closure s)`) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_RELATIVE_INTERIOR_CBALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[SUBSET; IN_CBALL; IN_INTER; LEFT_IMP_EXISTS_THM;
              AFFINE_HULL_CLOSURE] THEN
  X_GEN_TAC `e:real` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `b:real^N = a` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `b + e / norm(b - a) % (b - a):real^N`) THEN
  ASM_SIMP_TAC[NORM_ARITH `dist(b:real^N,b + e) = norm e`; NORM_MUL;
    REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ;
    REAL_ARITH `&0 < e ==> abs e <= e`] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
    ASM_MESON_TAC[SUBSET; AFFINE_AFFINE_HULL; RELATIVE_INTERIOR_SUBSET;
                  CLOSURE_SUBSET_AFFINE_HULL; HULL_INC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `b = (b + e / norm(b - a) % (b - a)) -
        e / norm(b - a) / (&1 + e / norm(b - a)) %
        ((b + e / norm(b - a) % (b - a)) - a):real^N`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH
     `b = (b + e % (b - a)) - d % ((b + e % (b - a)) - a) <=>
      (e - d * (&1 + e)) % (b - a) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_EQ; VECTOR_MUL_EQ_0];
    MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_DIV; NORM_POS_LT;
               VECTOR_SUB_EQ; REAL_ARITH `&0 < x ==> &0 < &1 + x`;
               REAL_ARITH `&0 < x ==> ~(&1 + x = &0)`;
               REAL_MUL_LID; REAL_ADD_RDISTRIB; REAL_DIV_RMUL;
               REAL_LT_IMP_NZ; REAL_LE_ADDL; NORM_POS_LE; REAL_SUB_REFL]);;

let RELATIVE_FRONTIER_CLOSURE = prove
 (`!s. convex s ==> relative_frontier(closure s) = relative_frontier s`,
  SIMP_TAC[relative_frontier; CLOSURE_CLOSURE;
           CONVEX_RELATIVE_INTERIOR_CLOSURE]);;

let RELATIVE_FRONTIER_RELATIVE_INTERIOR = prove
 (`!s:real^N->bool.
        convex s
        ==> relative_frontier(relative_interior s) = relative_frontier s`,
  ASM_MESON_TAC[RELATIVE_FRONTIER_CLOSURE; CONVEX_CLOSURE_RELATIVE_INTERIOR;
                CONVEX_RELATIVE_INTERIOR]);;

let CONNECTED_INTER_RELATIVE_FRONTIER = prove
 (`!s t:real^N->bool.
        connected s /\ s SUBSET affine hull t /\
        ~(s INTER t = {}) /\ ~(s DIFF t = {})
        ==> ~(s INTER relative_frontier t = {})`,
  REWRITE_TAC[relative_frontier] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_OPEN_IN]) THEN
  REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC
   [`s INTER relative_interior t:real^N->bool`;
    `s DIFF closure t:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
    EXISTS_TAC `affine hull t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN
    REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR; OPEN_IN_SUBTOPOLOGY_REFL] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    REWRITE_TAC[GSYM closed; CLOSED_CLOSURE];
    ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `i SUBSET t /\ t SUBSET c ==> (s INTER i) INTER (s DIFF c) = {}`) THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SUBSET; CLOSURE_SUBSET];
    MP_TAC(ISPEC `t:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
    MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    ASM SET_TAC[]]);;

let CLOSED_RELATIVE_FRONTIER = prove
 (`!s:real^N->bool. closed(relative_frontier s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[relative_frontier] THEN
  MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
  EXISTS_TAC `affine hull s:real^N->bool` THEN
  REWRITE_TAC[CLOSED_AFFINE_HULL] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
  REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR] THEN
  MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
  MATCH_MP_TAC(SET_RULE
   `s SUBSET closure t /\ closure t = t ==> s SUBSET t`) THEN
  SIMP_TAC[SUBSET_CLOSURE; HULL_SUBSET; CLOSURE_EQ; CLOSED_AFFINE_HULL]);;

let CLOSED_RELATIVE_BOUNDARY = prove
 (`!s. closed s ==> closed(s DIFF relative_interior s)`,
  MESON_TAC[CLOSED_RELATIVE_FRONTIER; relative_frontier; CLOSURE_CLOSED]);;

let COMPACT_RELATIVE_BOUNDARY = prove
 (`!s. compact s ==> compact(s DIFF relative_interior s)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_RELATIVE_BOUNDARY;
           BOUNDED_DIFF]);;

let BOUNDED_RELATIVE_FRONTIER = prove
 (`!s:real^N->bool. bounded s ==> bounded(relative_frontier s)`,
  REWRITE_TAC[relative_frontier] THEN
  MESON_TAC[BOUNDED_CLOSURE; BOUNDED_SUBSET; SUBSET_DIFF]);;

let COMPACT_RELATIVE_FRONTIER_BOUNDED = prove
 (`!s:real^N->bool. bounded s ==> compact(relative_frontier s)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_RELATIVE_FRONTIER;
           BOUNDED_RELATIVE_FRONTIER]);;

let COMPACT_RELATIVE_FRONTIER = prove
 (`!s:real^N->bool. compact s ==> compact(relative_frontier s)`,
  SIMP_TAC[COMPACT_RELATIVE_FRONTIER_BOUNDED; COMPACT_IMP_BOUNDED]);;

let CONVEX_SAME_RELATIVE_INTERIOR_CLOSURE = prove
 (`!s t. convex s /\ convex t
         ==> (relative_interior s = relative_interior t <=>
              closure s = closure t)`,
  MESON_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR;
            CONVEX_RELATIVE_INTERIOR_CLOSURE]);;

let CONVEX_SAME_RELATIVE_INTERIOR_CLOSURE_STRADDLE = prove
 (`!s t. convex s /\ convex t
         ==> (relative_interior s = relative_interior t <=>
              relative_interior s SUBSET t /\ t SUBSET closure s)`,
  MESON_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR;
            CONVEX_RELATIVE_INTERIOR_CLOSURE; SUBSET_CLOSURE;
                SUBSET_ANTISYM; RELATIVE_INTERIOR_SUBSET;
                CLOSURE_SUBSET; CLOSURE_CLOSURE]);;

let RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX = prove
 (`!f:real^M->real^N s.
        linear f /\ convex s
        ==> relative_interior(IMAGE f s) = IMAGE f (relative_interior s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `relative_interior (IMAGE f (relative_interior s)) =
      relative_interior (IMAGE (f:real^M->real^N) s)`
     (fun th -> REWRITE_TAC[SYM th; RELATIVE_INTERIOR_SUBSET]) THEN
    ASM_SIMP_TAC[CONVEX_SAME_RELATIVE_INTERIOR_CLOSURE_STRADDLE;
                 CONVEX_RELATIVE_INTERIOR; CONVEX_LINEAR_IMAGE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f:real^M->real^N) (relative_interior s)` THEN
      SIMP_TAC[RELATIVE_INTERIOR_SUBSET; IMAGE_SUBSET];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
        `IMAGE (f:real^M->real^N) (closure(relative_interior s))` THEN
      ASM_SIMP_TAC[CLOSURE_LINEAR_IMAGE_SUBSET] THEN
      ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^M` THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_PROLONG; CONVEX_LINEAR_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `z:real^M`; `x:real^M`]
        RELATIVE_INTERIOR_PROLONG) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o ISPEC `f:real^M->real^N` o MATCH_MP FUN_IN_IMAGE) THEN
    ASM_MESON_TAC[LINEAR_ADD; LINEAR_SUB; LINEAR_CMUL]]);;

let CLOSURE_INTERS_CONVEX = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> convex s) /\
        ~(INTERS(IMAGE relative_interior f) = {})
        ==> closure(INTERS f) = INTERS(IMAGE closure f)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[CLOSURE_INTERS_SUBSET] THEN
  REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[INTERS_IMAGE; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `b:real^N = a` THENL
   [EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[DIST_REFL; IN_INTERS] THEN
    ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  EXISTS_TAC `b - min (&1 / &2) (e / &2 / norm(b - a)) % (b - a):real^N` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[NORM_ARITH `dist(b - a:real^N,b) = norm a`; NORM_MUL] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < a /\ &0 < x /\ x < y ==> abs(min a x) < y`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_HALF; REAL_LT_DIV; NORM_POS_LT;
                 VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[IN_INTERS] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC
   (MESON[RELATIVE_INTERIOR_SUBSET; SUBSET]
         `!x. x IN relative_interior s ==> x IN s`) THEN
  MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_HALF; REAL_LT_DIV; NORM_POS_LT;
               VECTOR_SUB_EQ] THEN
  REAL_ARITH_TAC);;

let CLOSURE_INTERS_CONVEX_OPEN = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> convex s /\ open s)
        ==> closure(INTERS f) =
                if INTERS f = {} then {}
                else INTERS(IMAGE closure f)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[CLOSURE_EMPTY] THEN
  MATCH_MP_TAC CLOSURE_INTERS_CONVEX THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `~(s = {}) ==> s = t ==> ~(t = {})`)) THEN
  AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = x) ==> s = IMAGE f s`) THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_OPEN; INTERIOR_EQ]);;

let CLOSURE_INTER_CONVEX = prove
 (`!s t:real^N->bool.
        convex s /\ convex t /\
        ~(relative_interior s INTER relative_interior t = {})
        ==> closure(s INTER t) = closure(s) INTER closure(t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{s:real^N->bool,t}` CLOSURE_INTERS_CONVEX) THEN
  ASM_SIMP_TAC[IMAGE_CLAUSES; INTERS_2] THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let CLOSURE_INTER_CONVEX_OPEN = prove
 (`!s t. convex s /\ open s /\ convex t /\ open t
         ==> closure(s INTER t) =
                if s INTER t = {} then {} else closure(s) INTER closure(t)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[CLOSURE_EMPTY] THEN
  MATCH_MP_TAC CLOSURE_INTER_CONVEX THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_OPEN]);;

let CLOSURE_CONVEX_INTER_SUPERSET = prove
 (`!s t:real^N->bool.
        convex s /\ ~(interior s = {}) /\ interior s SUBSET closure t
        ==> closure(s INTER t) = closure s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET_CLOSURE; INTER_SUBSET; SUBSET_INTER] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `closure(interior s):real^N->bool` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_INTERIOR; SUBSET_REFL];
    ASM_SIMP_TAC[GSYM CLOSURE_OPEN_INTER_SUPERSET; OPEN_INTERIOR] THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN
    MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[]]);;

let CLOSURE_DYADIC_RATIONALS_IN_CONVEX_SET = prove
 (`!s:real^N->bool.
        convex s /\ ~(interior s = {})
        ==> closure(s INTER
                    { inv(&2 pow n) % x | n,x |
                      !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) }) =
            closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_CONVEX_INTER_SUPERSET THEN
  ASM_REWRITE_TAC[CLOSURE_DYADIC_RATIONALS; SUBSET_UNIV]);;

let CLOSURE_RATIONALS_IN_CONVEX_SET = prove
 (`!s:real^N->bool.
      convex s /\ ~(interior s = {})
      ==> closure(s INTER
                  { x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) }) =
          closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_CONVEX_INTER_SUPERSET THEN
  ASM_REWRITE_TAC[CLOSURE_RATIONAL_COORDINATES; SUBSET_UNIV]);;

let RELATIVE_INTERIOR_CONVEX_INTER_AFFINE = prove
 (`!s t:real^N->bool.
        convex s /\ affine t /\ ~(interior s INTER t = {})
        ==> relative_interior(s INTER t) = interior s INTER t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; RIGHT_AND_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` MP_TAC) THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REWRITE_TAC[IN_INTER] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(vec 0:real^N) IN t` THEN
  ASM_SIMP_TAC[AFFINE_EQ_SUBSPACE] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `s:real^N->bool`]
        (ONCE_REWRITE_RULE[INTER_COMM]
           AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR)) THEN
  ASM_SIMP_TAC[SUBSPACE_IMP_AFFINE; IN_RELATIVE_INTERIOR_CBALL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_INTER; IN_INTERIOR_CBALL]] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SUBSET; IN_INTER] THEN
  ASM_CASES_TAC `(x:real^N) IN s` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE]] THEN
  EQ_TAC THENL [REWRITE_TAC[IN_CBALL]; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `x:real^N = vec 0` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR_CBALL]) THEN
    ASM_REWRITE_TAC[SUBSET; IN_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`s:real^N->bool`; `vec 0:real^N`; `(&1 + e / norm x) % x:real^N`]
   IN_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[SUBSPACE_MUL] THEN
    REWRITE_TAC[VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID;
                NORM_ARITH `dist(a:real^N,a + x) = norm x`] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM;
                 REAL_DIV_RMUL; NORM_EQ_0] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_INTERIOR_CBALL; IN_CBALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    EXISTS_TAC `inv(&1 + e / norm(x:real^N))` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_LT_DIV; NORM_POS_LT; VECTOR_MUL_LID;
                 REAL_LT_INV_EQ; REAL_MUL_LINV; REAL_INV_LT_1; REAL_ARITH
                 `&0 < x ==> &1 < &1 + x /\ &0 < &1 + x /\ ~(&1 + x = &0)`]]);;

(* ------------------------------------------------------------------------- *)
(* Homeomorphism of all convex compact sets with same affine dimension, and  *)
(* in particular all those with nonempty interior.                           *)
(* ------------------------------------------------------------------------- *)

let COMPACT_FRONTIER_LINE_LEMMA = prove
 (`!s x. compact s /\ (vec 0 IN s) /\ ~(x = vec 0 :real^N)
         ==> ?u. &0 <= u /\ (u % x) IN frontier s /\
                 !v. u < v ==> ~((v % x) IN s)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
    [`{y:real^N | ?u. &0 <= u /\ u <= b / norm(x) /\ (y = u % x)} INTER s`;
     `vec 0:real^N`]
   DISTANCE_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^N` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      EXISTS_TAC `&0` THEN
      ASM_SIMP_TAC[VECTOR_MUL_LZERO; REAL_LE_REFL; REAL_LT_IMP_LE;
                   REAL_LT_DIV; NORM_POS_LT]] THEN
    MATCH_MP_TAC COMPACT_INTER THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{y:real^N | ?u. &0 <= u /\ u <= b / norm(x) /\ (y = u % x)} =
      IMAGE (\u. drop u % x) (interval [vec 0,lambda i. b / norm(x:real^N)])`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_INTERVAL] THEN
      SIMP_TAC[LAMBDA_BETA] THEN
      SIMP_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> (i = 1)`] THEN
      REWRITE_TAC[GSYM drop; LEFT_FORALL_IMP_THM; EXISTS_REFL; DROP_VEC] THEN
      REWRITE_TAC[EXISTS_LIFT; LIFT_DROP] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_VMUL THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> c /\ a /\ b /\ d`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC (BINDER_CONV o ONCE_DEPTH_CONV) [SWAP_FORALL_THM] THEN
  SIMP_TAC[IMP_CONJ] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LEFT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real` THEN
  REWRITE_TAC[dist; VECTOR_SUB_LZERO; NORM_NEG; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ; NORM_POS_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[real_abs] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[FRONTIER_STRADDLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [EXISTS_TAC `u % x :real^N` THEN ASM_REWRITE_TAC[DIST_REFL];
      ALL_TAC] THEN
    EXISTS_TAC `(u + (e / &2) / norm(x)) % x :real^N` THEN
    REWRITE_TAC[dist; VECTOR_ARITH `u % x - (u + a) % x = --(a % x)`] THEN
    ASM_SIMP_TAC[NORM_NEG; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; NORM_EQ_0;
                 REAL_DIV_RMUL; REAL_ABS_NUM; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH; REAL_ARITH `abs e < e * &2 <=> &0 < e`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u + (e / &2) / norm(x:real^N)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ &0 <= u /\ u + e <= b
      ==> ~(&0 <= u + e /\ u + e <= b ==> u + e <= u)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; NORM_POS_LT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(u + (e / &2) / norm(x:real^N)) % x`) THEN
    ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LE_RDIV_EQ; NORM_POS_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real`) THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN ASM_REWRITE_TAC[REAL_NOT_LT] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_LET_TRANS; REAL_LT_IMP_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v % x:real^N`) THEN
  ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LE_RDIV_EQ; NORM_POS_LT] THEN
  REAL_ARITH_TAC);;

let STARLIKE_COMPACT_PROJECTIVE = prove
 (`!s:real^N->bool a.
        compact s /\ a IN relative_interior s /\
        (!x. x IN s ==> segment(a,x) SUBSET relative_interior s)
        ==> s DIFF relative_interior s homeomorphic
            sphere(a,&1) INTER affine hull s /\
            s homeomorphic cball(a,&1) INTER affine hull s`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `a:real^N` THEN
  REWRITE_TAC[SUBSET; IMP_IMP; RIGHT_IMP_FORALL_THM] THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^N u. x IN s /\ &0 <= u /\ u < &1
                 ==> (u % x) IN relative_interior s`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&0 <= u <=> u = &0 \/ &0 < u`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(K ALL_TAC o SPECL [`x:real^N`; `x:real^N`])] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
    RELATIVE_INTERIOR_SUBSET)) THEN
  ABBREV_TAC `proj = \x:real^N. inv(norm(x)) % x` THEN
  SUBGOAL_THEN
   `!x:real^N y. (proj(x) = proj(y):real^N) /\ (norm x = norm y) <=> (x = y)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    ASM_CASES_TAC `y:real^N = vec 0` THEN
    ASM_SIMP_TAC[NORM_EQ_0; NORM_0] THEN
    ASM_CASES_TAC `x:real^N = vec 0` THENL
     [ASM_MESON_TAC[NORM_EQ_0]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    EXPAND_TAC "proj" THEN REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
     `a % x = a % y <=> a % (x - y):real^N = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN affine hull s ==> proj x IN affine hull s) /\
    (!x. ~(x = vec 0) ==> norm(proj x) = &1) /\
    (!x:real^N. proj x = vec 0 <=> x = vec 0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "proj" THEN REWRITE_TAC[NORM_MUL; VECTOR_MUL_EQ_0] THEN
    REWRITE_TAC[REAL_INV_EQ_0; NORM_EQ_0; REAL_ABS_INV; REAL_ABS_NORM] THEN
    SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_LID] THEN
    MATCH_MP_TAC IN_AFFINE_ADD_MUL THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; VECTOR_ADD_LID; HULL_INC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(proj:real^N->real^N) continuous_on (UNIV DELETE vec 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[IN_DELETE; IN_UNIV] THEN EXPAND_TAC "proj" THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
    ASM_SIMP_TAC[CONTINUOUS_AT_ID] THEN
    REWRITE_TAC[GSYM(ISPEC `lift` o_DEF);
                GSYM(ISPEC `inv:real->real` o_DEF)] THEN
    MATCH_MP_TAC CONTINUOUS_AT_INV THEN
    ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ; CONTINUOUS_AT_LIFT_NORM];
    ALL_TAC] THEN
  ABBREV_TAC `usph = {x:real^N | x IN affine hull s /\ norm x = &1}` THEN
  SUBGOAL_THEN ` sphere(vec 0:real^N,&1) INTER affine hull s = usph`
  SUBST1_TAC THENL
   [EXPAND_TAC "usph" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_SPHERE_0] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN affine hull s /\ ~(x = vec 0)
        ==> (proj:real^N->real^N) x IN usph`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?surf. homeomorphism (s DIFF relative_interior s,usph)
                                     (proj:real^N->real^N,surf)`
  MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
    ASM_SIMP_TAC[COMPACT_RELATIVE_BOUNDARY] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN
        EXPAND_TAC "usph" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_MESON_TAC[HULL_INC];
        MAP_EVERY EXPAND_TAC ["proj"; "usph"] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
        ASM_CASES_TAC `x:real^N = vec 0` THEN
        ASM_REWRITE_TAC[NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `vec 0:real^N`; `x:real^N`]
            RAY_TO_RELATIVE_FRONTIER) THEN
        REWRITE_TAC[relative_frontier] THEN
        ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; CLOSURE_CLOSED; COMPACT_IMP_CLOSED;
                     VECTOR_ADD_LID] THEN
        DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
        EXPAND_TAC "proj" THEN REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `d % x:real^N` THEN ASM_REWRITE_TAC[NORM_MUL] THEN
        ASM_SIMP_TAC[REAL_MUL_RID; real_abs; REAL_LT_IMP_LE] THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                     VECTOR_MUL_LID]];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
      REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      ASM_CASES_TAC `x:real^N = vec 0` THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `y:real^N = vec 0` THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(proj:real^N->real^N) x = proj y` THEN
      EXPAND_TAC "proj" THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH
       `norm(x:real^N) = norm(y:real^N) \/
        norm x < norm y \/ norm y < norm x`)
      THENL
       [ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_INV_EQ_0; NORM_EQ_0];
        DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
         [`y:real^N`; `norm(x:real^N) / norm(y:real^N)`]);
        DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
         [`x:real^N`; `norm(y:real^N) / norm(x:real^N)`])] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_LDIV_EQ; NORM_POS_LT;
                   REAL_MUL_LID] THEN
      ASM_REWRITE_TAC[real_div; GSYM VECTOR_MUL_ASSOC] THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM); ALL_TAC] THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LID]];
    DISCH_THEN(fun th ->
      CONJ_TAC THENL
       [MESON_TAC[homeomorphic; th];
        ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
        MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
        SIMP_TAC[COMPACT_INTER_CLOSED; CLOSED_AFFINE_HULL; COMPACT_CBALL] THEN
        MP_TAC th]) THEN
    REWRITE_TAC[HOMEOMORPHISM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `surf:real^N->real^N` THEN STRIP_TAC THEN
    EXISTS_TAC `\x:real^N. norm(x) % (surf:real^N->real^N)(proj(x))` THEN
    REWRITE_TAC[]] THEN
  UNDISCH_THEN
   `(proj:real^N->real^N) continuous_on s DIFF relative_interior s`
   (K ALL_TAC) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_INTER] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    ASM_CASES_TAC `x = vec 0:real^N` THENL
     [ASM_REWRITE_TAC[CONTINUOUS_WITHIN; VECTOR_MUL_LZERO; NORM_0] THEN
      MATCH_MP_TAC LIM_NULL_VMUL_BOUNDED THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
      REWRITE_TAC[BOUNDED_POS] THEN MATCH_MP_TAC MONO_EXISTS THEN
      REPEAT STRIP_TAC THENL
       [REWRITE_TAC[LIM_WITHIN; o_THM; DIST_0; NORM_LIFT; REAL_ABS_NORM] THEN
        MESON_TAC[];
        REWRITE_TAC[EVENTUALLY_WITHIN] THEN EXISTS_TAC `&1` THEN
        REWRITE_TAC[REAL_LT_01; IN_INTER; DIST_0; NORM_POS_LT] THEN
        ASM SET_TAC[]];
      MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN
      EXISTS_TAC `affine hull s:real^N->bool` THEN
      REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
      SIMP_TAC[CONTINUOUS_LIFT_NORM_COMPOSE; CONTINUOUS_WITHIN_ID; o_DEF] THEN
      SUBGOAL_THEN
       `((surf:real^N->real^N) o (proj:real^N->real^N)) continuous_on
        (affine hull s DELETE vec 0)`
      MP_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
        SIMP_TAC[SUBSET; IN_DELETE; IN_UNIV; FORALL_IN_IMAGE] THEN
        EXPAND_TAC "usph" THEN ASM_SIMP_TAC[IN_ELIM_THM];
        SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_SIMP_TAC[IN_DELETE] THEN
        REWRITE_TAC[CONTINUOUS_WITHIN; o_DEF] THEN MATCH_MP_TAC EQ_IMP THEN
        MATCH_MP_TAC LIM_TRANSFORM_WITHIN_SET THEN
        REWRITE_TAC[EVENTUALLY_AT] THEN EXISTS_TAC `norm(x:real^N)` THEN
        ASM_REWRITE_TAC[IN_DELETE; IN_INTER; IN_CBALL; NORM_POS_LT] THEN
        X_GEN_TAC `y:real^N` THEN
        ASM_CASES_TAC `(y:real^N) IN affine hull s` THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC NORM_ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a x. &0 < a ==> (proj:real^N->real^N)(a % x) = proj x`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "proj" THEN
    REWRITE_TAC[NORM_MUL; REAL_INV_MUL; VECTOR_MUL_ASSOC] THEN
    SIMP_TAC[REAL_FIELD `&0 < a ==> (inv(a) * x) * a = x`; real_abs;
             REAL_LT_IMP_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
    ASM_CASES_TAC `y:real^N = vec 0` THENL
     [ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_EQ_0; NORM_0; NORM_EQ_0] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `x:real^N = vec 0` THENL
     [CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
      ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_EQ_0; NORM_0; NORM_EQ_0] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_CBALL_0] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> MP_TAC th THEN
             MP_TAC(AP_TERM `proj:real^N->real^N` th)) THEN
    ASM_SIMP_TAC[NORM_POS_LT; VECTOR_MUL_RCANCEL] THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_CBALL_0] THEN
    X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_LZERO; IN_INTER] THEN
    REWRITE_TAC[IN_CBALL_0; REAL_LE_LT] THEN STRIP_TAC  THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
      ASM SET_TAC[];
      ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_CBALL_0; IN_INTER] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:real^N = vec 0` THENL
   [EXISTS_TAC `vec 0:real^N` THEN
    ASM_SIMP_TAC[NORM_0; VECTOR_MUL_LZERO; HULL_INC; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN usph ==> ~((surf:real^N->real^N) x = vec 0)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `inv(norm(surf(proj x:real^N):real^N)) % x:real^N` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [NORM_POS_LT; REAL_LT_INV_EQ; HULL_INC; REAL_LT_MUL; NORM_MUL;
    REAL_ABS_INV; REAL_ABS_NORM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `~(y = &0) ==> x = (inv y * x) * y`) THEN
    ASM_SIMP_TAC[NORM_EQ_0; HULL_INC];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
     [GSYM real_div; REAL_LE_LDIV_EQ; NORM_POS_LT; HULL_INC; REAL_MUL_LID] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`x:real^N`; `norm(surf(proj x:real^N):real^N) / norm(x:real^N)`]) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_LDIV_EQ; NORM_POS_LT] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[REAL_NOT_LT; REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `norm(surf(proj x)) / norm x % x:real^N = surf(proj x:real^N)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
      ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
       [NORM_POS_LT; REAL_LT_INV_EQ; HULL_INC; REAL_LT_MUL; NORM_MUL;
        REAL_ABS_INV; REAL_ABS_NORM; REAL_ABS_DIV; REAL_LT_DIV;
        REAL_DIV_RMUL; NORM_EQ_0];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE f s SUBSET t DIFF u ==> x IN s ==> ~(f x IN u)`)) THEN
      ASM_SIMP_TAC[HULL_INC]];
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_LID] THEN
    MATCH_MP_TAC IN_AFFINE_ADD_MUL THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; VECTOR_ADD_LID; HULL_INC]]);;

let HOMEOMORPHIC_CONVEX_COMPACT_SETS,
    HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS = (CONJ_PAIR o prove)
 (`(!s:real^M->bool t:real^N->bool.
        convex s /\ compact s /\ convex t /\ compact t /\ aff_dim s = aff_dim t
        ==> s homeomorphic t) /\
   (!s:real^M->bool t:real^N->bool.
        convex s /\ bounded s /\ convex t /\ bounded t /\ aff_dim s = aff_dim t
        ==> relative_frontier s homeomorphic relative_frontier t)`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool.
          convex s /\ compact s /\ convex t /\ compact t /\
          aff_dim s = aff_dim t
          ==> (s DIFF relative_interior s) homeomorphic
              (t DIFF relative_interior t) /\
              s homeomorphic t`,
    REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_CASES_TAC `relative_interior t:real^N->bool = {}` THENL
     [UNDISCH_TAC `relative_interior t:real^N->bool = {}` THEN
      ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_EQ_MINUS1;
                   EMPTY_DIFF; HOMEOMORPHIC_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY];
       FIRST_X_ASSUM(X_CHOOSE_THEN `b:real^N` MP_TAC o
          GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY])] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    ASM_CASES_TAC `relative_interior s:real^M->bool = {}` THENL
     [UNDISCH_TAC `relative_interior s:real^M->bool = {}` THEN
      ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_EQ_MINUS1;
                   EMPTY_DIFF; HOMEOMORPHIC_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY];
      FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^M` MP_TAC o
          GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY])] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    GEOM_ORIGIN_TAC `b:real^N` THEN REPEAT GEN_TAC THEN
    GEOM_ORIGIN_TAC `a:real^M` THEN REPEAT GEN_TAC THEN
    REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `vec 0:real^M`]
          STARLIKE_COMPACT_PROJECTIVE) THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `vec 0:real^N`]
          STARLIKE_COMPACT_PROJECTIVE) THEN
    ASM_SIMP_TAC[IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT;
                 REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC MONO_AND THEN MP_TAC th) THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMEOMORPHIC_TRANS) THEN
     MP_TAC(ONCE_REWRITE_RULE[HOMEOMORPHIC_SYM] th)) THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] HOMEOMORPHIC_TRANS) THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
          RELATIVE_INTERIOR_SUBSET))) THEN
    FIRST_X_ASSUM(MP_TAC o SYM) THEN
    ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; AFF_DIM_DIM_0] THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`span s:real^M->bool`; `span t:real^N->bool`]
            ISOMETRIES_SUBSPACES) THEN
    ASM_REWRITE_TAC[SUBSPACE_SPAN; DIM_SPAN; homeomorphic; HOMEOMORPHISM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^N` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_CBALL_0; IN_SPHERE_0] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN ASM SET_TAC[]) in
  SIMP_TAC[lemma; relative_frontier] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`closure s:real^M->bool`; `closure t:real^N->bool`] lemma) THEN
  ASM_SIMP_TAC[CONVEX_CLOSURE; COMPACT_CLOSURE; AFF_DIM_CLOSURE] THEN
  ASM_SIMP_TAC[CONVEX_RELATIVE_INTERIOR_CLOSURE]);;

let HOMEOMORPHIC_CONVEX_COMPACT = prove
 (`!s:real^N->bool t:real^N->bool.
        convex s /\ compact s /\ ~(interior s = {}) /\
        convex t /\ compact t /\ ~(interior t = {})
        ==> s homeomorphic t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_CONVEX_COMPACT_SETS THEN
  ASM_SIMP_TAC[AFF_DIM_NONEMPTY_INTERIOR]);;

let HOMEOMORPHIC_CONVEX_COMPACT_CBALL = prove
 (`!s:real^N->bool b:real^N e.
        convex s /\ compact s /\ ~(interior s = {}) /\ &0 < e
        ==> s homeomorphic cball(b,e)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_CONVEX_COMPACT THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; INTERIOR_CBALL; CONVEX_CBALL] THEN
  ASM_REWRITE_TAC[BALL_EQ_EMPTY; REAL_NOT_LE]);;

let HOMEOMORPHIC_CLOSED_INTERVALS = prove
 (`!a b:real^N c d:real^N.
        ~(interval(a,b) = {}) /\ ~(interval(c,d) = {})
        ==> interval[a,b] homeomorphic interval[c,d]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_CONVEX_COMPACT THEN
  REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL] THEN
  ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* More about affine dimension of special sets.                              *)
(* ------------------------------------------------------------------------- *)

let AFF_DIM_NONEMPTY_INTERIOR_EQ = prove
 (`!s:real^N->bool.
        convex s ==> (aff_dim s = &(dimindex (:N)) <=> ~(interior s = {}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[AFF_DIM_NONEMPTY_INTERIOR] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` EMPTY_INTERIOR_SUBSET_HYPERPLANE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN
  ASM_SIMP_TAC[AFF_DIM_HYPERPLANE] THEN INT_ARITH_TAC);;

let AFF_DIM_BALL = prove
 (`!a:real^N r.
        aff_dim(ball(a,r)) = if &0 < r then &(dimindex(:N)) else --(&1)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC AFF_DIM_OPEN THEN
    ASM_REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT; GSYM BALL_EQ_EMPTY]) THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY]]);;

let AFF_DIM_CBALL = prove
 (`!a:real^N r.
        aff_dim(cball(a,r)) =
            if &0 < r then &(dimindex(:N))
            else if r = &0 then &0 else --(&1)`,
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THENL
   [MATCH_MP_TAC AFF_DIM_NONEMPTY_INTERIOR THEN
    ASM_REWRITE_TAC[INTERIOR_CBALL; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[CBALL_SING; AFF_DIM_SING];
    MATCH_MP_TAC(MESON[AFF_DIM_EMPTY] `s = {} ==> aff_dim s = --(&1)`) THEN
    REWRITE_TAC[CBALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC]);;

let AFF_DIM_INTERVAL = prove
 (`(!a b:real^N.
        aff_dim(interval[a,b]) =
                if interval[a,b] = {} then --(&1)
                else &(CARD {i | 1 <= i /\ i <= dimindex(:N) /\ a$i < b$i})) /\
   (!a b:real^N.
         aff_dim(interval(a,b)) =
                if interval(a,b) = {} then --(&1)
                else &(dimindex(:N)))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_OPEN; OPEN_INTERVAL] THEN
  POP_ASSUM MP_TAC THEN GEOM_ORIGIN_TAC `a:real^N` THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VEC_COMPONENT; REAL_LT_LADD] THEN
  ASM_SIMP_TAC[AFF_DIM_DIM_0; HULL_INC; ENDS_IN_INTERVAL] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN MATCH_MP_TAC DIM_UNIQUE THEN EXISTS_TAC
   `{basis i:real^N | 1 <= i /\ i <= dimindex(:N) /\ &0 < (b:real^N)$i}` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY; VEC_COMPONENT]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `basis i:real^N = inv(b$i) % (b:real^N)$i % basis i`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[VECTOR_MUL_LID];
      MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
      SIMP_TAC[IN_INTERVAL; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
      X_GEN_TAC `j:num` THEN REWRITE_TAC[VEC_COMPONENT] THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_LE_REFL]];
    MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
    REWRITE_TAC[SUBSPACE_SPAN; SUBSET; IN_INTERVAL; VEC_COMPONENT] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    MATCH_MP_TAC SPAN_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_CASES_TAC `&0 < (b:real^N)$i` THENL
     [MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC[];
      SUBGOAL_THEN `(x:real^N)$i = &0`
        (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO; SPAN_0]) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
    REWRITE_TAC[SET_RULE `~(a IN {f x | P x}) <=> !x. P x ==> ~(f x = a)`] THEN
    SIMP_TAC[BASIS_NONZERO; pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    SIMP_TAC[FORALL_IN_GSPEC; BASIS_INJ_EQ; ORTHOGONAL_BASIS_BASIS];
    GEN_REWRITE_TAC LAND_CONV [SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC; BASIS_INJ_EQ;
             HAS_SIZE] THEN
    SIMP_TAC[CONJ_ASSOC; GSYM IN_NUMSEG; FINITE_RESTRICT; FINITE_NUMSEG]]);;

(* ------------------------------------------------------------------------- *)
(* Deducing convexity from midpoint convexity in common cases.               *)
(* ------------------------------------------------------------------------- *)

let MIDPOINT_CONVEX_DYADIC_RATIONALS = prove
 (`!f:real^N->real s.
        (!x y. x IN s /\ y IN s
               ==> midpoint(x,y) IN s /\
                   f(midpoint(x,y)) <= (f(x) + f(y)) / &2)
        ==> !n m p x y.
                x IN s /\ y IN s /\ m + p = 2 EXP n
                ==> (&m / &2 pow n % x + &p / &2 pow n % y) IN s /\
                    f(&m / &2 pow n % x + &p / &2 pow n % y)
                    <= &m / &2 pow n * f x + &p / &2 pow n * f y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE
     `m + p = 2 EXP 0 <=> m = 0 /\ p = 1 \/ m = 1 /\ p = 0`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                  VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_SYM; REAL_ADD_SYM; ADD_SYM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `p:num`] THEN DISCH_TAC THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[EXP; real_pow] THEN STRIP_TAC THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x * inv(&2) * y = inv(&2) * x * y`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM VECTOR_ADD_LDISTRIB] THEN
    SUBGOAL_THEN `2 EXP n <= p` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&p * inv(&2 pow n) = &(p - 2 EXP n) * inv(&2 pow n) + &1`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_POW] THEN
      ASM_SIMP_TAC[REAL_SUB_RDISTRIB; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                   REAL_LT_POW2] THEN REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_ADD_RDISTRIB; REAL_ADD_RDISTRIB] THEN
      REWRITE_TAC[VECTOR_MUL_LID; REAL_MUL_LID] THEN
      REWRITE_TAC[VECTOR_ADD_ASSOC; REAL_ADD_ASSOC] THEN
      REWRITE_TAC[GSYM midpoint; GSYM real_div] THEN FIRST_X_ASSUM(fun th ->
        W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
      FIRST_X_ASSUM(fun th ->
        W(MP_TAC o PART_MATCH (lhand o rand) th o funpow 3 lhand o  snd)) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[] THEN REAL_ARITH_TAC]]]);;

let CONTINUOUS_MIDPOINT_CONVEX = prove
 (`!f:real^N->real s.
        (lift o f) continuous_on s /\ convex s /\
        (!x y. x IN s /\ y IN s ==> f(midpoint(x,y)) <= (f(x) + f(y)) / &2)
         ==> f convex_on s`,
  REWRITE_TAC[midpoint] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[convex_on] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `u + v = &1 <=> v = &1 - u`; IMP_CONJ] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; REAL_SUB_LE] THEN
  REWRITE_TAC[FORALL_DROP; GSYM DROP_VEC; IMP_IMP; GSYM IN_INTERVAL_1] THEN
  MP_TAC(ISPEC `interval[vec 0:real^1,vec 1]`
        CLOSURE_DYADIC_RATIONALS_IN_CONVEX_SET) THEN
  SIMP_TAC[CONVEX_INTERVAL; INTERIOR_CLOSED_INTERVAL;
           CLOSURE_CLOSED; CLOSED_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop] THEN
  DISCH_THEN(fun th -> SUBST1_TAC(SYM th) THEN ASSUME_TAC th) THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a <= b <=> a - b <= &0`] THEN
  MATCH_MP_TAC CONTINUOUS_LE_ON_CLOSURE THEN
  REWRITE_TAC[IN_INTER; IMP_CONJ_ALT; FORALL_IN_GSPEC] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; GSYM FORALL_DROP; DROP_VEC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_ADD; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
     [REPLICATE_TAC 2 (ONCE_REWRITE_TAC[GSYM o_DEF]) THEN
      REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      CONJ_TAC THENL
       [ALL_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; GSYM FORALL_DROP;
                    DROP_VEC] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST;
             LIFT_SUB; CONTINUOUS_ON_SUB];
    MAP_EVERY X_GEN_TAC [`n:num`; `i:real`] THEN
    ASM_SIMP_TAC[REAL_LE_MUL_EQ; REAL_LT_INV_EQ; REAL_LT_POW2] THEN
    ASM_CASES_TAC `&0 <= i` THEN ASM_SIMP_TAC[INTEGER_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_POW2; REAL_MUL_LID] THEN
    GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV)
     [REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real`; `s:real^N->bool`]
        MIDPOINT_CONVEX_DYADIC_RATIONALS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[midpoint] THEN REWRITE_TAC[VECTOR_ADD_LDISTRIB] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPECL
       [`n:num`; `m:num`; `2 EXP n - m`; `x:real^N`; `y:real^N`]) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_POW] THEN
      ASM_SIMP_TAC[REAL_LT_POW2; REAL_FIELD
       `&0 < y ==> (y - x) / y = &1 - x / y`] THEN
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Slightly shaper separating/supporting hyperplane results.                 *)
(* ------------------------------------------------------------------------- *)

let SEPARATING_HYPERPLANE_RELATIVE_INTERIORS = prove
 (`!s t. convex s /\ convex t /\
         ~(s = {} /\ t = (:real^N) \/ s = (:real^N) /\ t = {}) /\
         DISJOINT (relative_interior s) (relative_interior t)
         ==> ?a b. ~(a = vec 0) /\
                   (!x. x IN s ==> a dot x <= b) /\
                   (!x. x IN t ==> a dot x >= b)`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`s:real^N->bool = {}`; `t:real^N->bool = {}`] THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; UNIV_NOT_EMPTY; CONVEX_EMPTY;
                  RELATIVE_INTERIOR_EMPTY] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `basis 1:real^N` THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL];
    FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^N` o MATCH_MP (SET_RULE
     `~(s = UNIV) ==> ?a. ~(a IN s)`)) THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `x:real^N`]
        SEPARATING_HYPERPLANE_SET_POINT_INAFF) THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^N` o MATCH_MP (SET_RULE
     `~(s = UNIV) ==> ?a. ~(a IN s)`)) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
        SEPARATING_HYPERPLANE_SET_POINT_INAFF) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; real_ge] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`--a:real^N`; `--b:real`] THEN
    ASM_REWRITE_TAC[VECTOR_NEG_EQ_0; DOT_LNEG; REAL_LE_NEG2];
    MP_TAC(ISPECL [`relative_interior s:real^N->bool`;
                   `relative_interior t:real^N->bool`]
          SEPARATING_HYPERPLANE_SETS) THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; CONVEX_RELATIVE_INTERIOR] THEN
    SIMP_TAC[real_ge] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `a:real^N` THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `b:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC
    (MESON[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_SUBSET; SUBSET]
      `convex s /\ (!x. x IN closure(relative_interior s) ==> P x)
       ==> !x. x IN s ==> P x`) THEN
    ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC CONTINUOUS_LE_ON_CLOSURE;
      MATCH_MP_TAC CONTINUOUS_GE_ON_CLOSURE] THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT]]);;

let SUPPORTING_HYPERPLANE_RELATIVE_BOUNDARY = prove
 (`!s x:real^N.
        convex s /\ x IN s /\ ~(x IN relative_interior s)
        ==> ?a. ~(a = vec 0) /\
                (!y. y IN s ==> a dot x <= a dot y) /\
                (!y. y IN relative_interior s ==> a dot x < a dot y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`relative_interior s:real^N->bool`; `x:real^N`]
        SEPARATING_HYPERPLANE_SET_POINT_INAFF) THEN
  ASM_SIMP_TAC[CONVEX_SING; CONVEX_RELATIVE_INTERIOR;
               RELATIVE_INTERIOR_EQ_EMPTY; real_ge] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`lift o (\x:real^N. a dot x)`;
                   `relative_interior s:real^N->bool`;
                   `y:real^N`; `(a:real^N) dot x`; `1`]
      CONTINUOUS_ON_CLOSURE_COMPONENT_GE) THEN
    REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT; GSYM drop; o_THM; LIFT_DROP] THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR] THEN
    ASM_MESON_TAC[CLOSURE_SUBSET; REAL_LE_TRANS; SUBSET];
    DISCH_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `(y:real^N) IN relative_interior s` THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR_CBALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET; IN_INTER; IN_CBALL] THEN
  X_GEN_TAC `e:real` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `y + --(e / norm(a)) % ((x + a) - x):real^N`) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[NORM_ARITH `dist(y:real^N,y + e) = norm e`; VECTOR_ADD_SUB] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_NEG; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s SUBSET t ==> x IN t`)) THEN
    MATCH_MP_TAC HULL_MONO THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; RELATIVE_INTERIOR_SUBSET];
    REWRITE_TAC[VECTOR_ADD_SUB] THEN DISCH_TAC THEN
    UNDISCH_TAC `!y:real^N. y IN s ==> a dot x <= a dot y` THEN
    DISCH_THEN(MP_TAC o SPEC `y + --(e / norm(a)) % a:real^N`) THEN
    ASM_REWRITE_TAC[DOT_RMUL; DOT_RNEG; DOT_RADD] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x * y ==> ~(a <= a + --x * y)`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; NORM_POS_LT; DOT_POS_LT]]);;

let SUPPORTING_HYPERPLANE_RELATIVE_FRONTIER = prove
 (`!s x:real^N.
        convex s /\ x IN closure s /\ ~(x IN relative_interior s)
        ==> ?a. ~(a = vec 0) /\
                (!y. y IN closure s ==> a dot x <= a dot y) /\
                (!y. y IN relative_interior s ==> a dot x < a dot y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`closure s:real^N->bool`; `x:real^N`]
    SUPPORTING_HYPERPLANE_RELATIVE_BOUNDARY) THEN
  ASM_SIMP_TAC[CONVEX_CLOSURE; CONVEX_RELATIVE_INTERIOR_CLOSURE]);;

(* ------------------------------------------------------------------------- *)
(* Containment of rays in unbounded convex sets.                             *)
(* ------------------------------------------------------------------------- *)

let UNBOUNDED_CONVEX_CLOSED_CONTAINS_RAY = prove
 (`!s a:real^N.
        convex s /\ ~bounded s /\ closed s /\ a IN s
        ==> ?l. ~(l = vec 0) /\ !t. &0 <= t ==> (a + t % l) IN s`,
  GEN_GEOM_ORIGIN_TAC `a:real^N` ["l"] THEN
  REWRITE_TAC[VECTOR_ADD_LID] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [BOUNDED_POS]) THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&n + &1:real`) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[REAL_NOT_LE; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `x:num->real^N` THEN REWRITE_TAC[FORALL_AND_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!n. ~((x:num->real^N) n = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_ARITH `~(&n + &1 < norm(vec 0:real^N))`]; ALL_TAC] THEN
  MP_TAC(ISPEC `sphere(vec 0:real^N,&1)` compact) THEN
  REWRITE_TAC[COMPACT_SPHERE] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. inv(norm(x n)) % (x:num->real^N) n`) THEN
  ASM_SIMP_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
               REAL_MUL_LINV; NORM_EQ_0; o_DEF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[NORM_ARITH `~(norm(vec 0:real^N) = &1)`]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC CLOSED_CONTAINS_SEQUENTIAL_LIMIT THEN
  SUBGOAL_THEN
   `?N:num. !n. N <= n ==> t / norm(x n:real^N) <= &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; NORM_POS_LT] THEN
    MP_TAC(SPEC `t:real` REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_MUL_LID] THEN
    ASM_MESON_TAC[REAL_ARITH `t <= m /\ m <= n /\ n + &1 < x ==> t <= x`];
    EXISTS_TAC `\n:num. t / norm((x:num->real^N)(r(N + n))) % x(r(N + n))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `N + n:num` o MATCH_MP MONOTONE_BIGGER) THEN
      ARITH_TAC;
      REWRITE_TAC[real_div; GSYM VECTOR_MUL_ASSOC] THEN
      MATCH_MP_TAC LIM_CMUL THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      FIRST_ASSUM(MP_TAC o SPEC `N:num` o MATCH_MP SEQ_OFFSET) THEN
      ASM_REWRITE_TAC[]]]);;

let CONVEX_CLOSED_CONTAINS_SAME_RAY = prove
 (`!s a b l:real^N.
        convex s /\ closed s /\ b IN s /\ (!t. &0 <= t ==> (a + t % l) IN s)
        ==> !t. &0 <= t ==> (b + t % l) IN s`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_IN_CLOSED_SET) THEN
  EXISTS_TAC `\n. (&1 - t / (&n + &1)) % b +
                  t / (&n + &1) % (a + (&n + &1) % l):real^N` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `t:real` REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_ARITH `&0 <= &n + &1`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % b + u % c:real^N = b + u % (c - b)`] THEN
    MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_SUB_LDISTRIB] THEN
    SIMP_TAC[VECTOR_MUL_ASSOC; REAL_FIELD `t / (&n + &1) * (&n + &1) = t`] THEN
    SIMP_TAC[VECTOR_ARITH `(v % a + b) - v % c:real^N = b + v % (a - c)`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_RID] THEN
    MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
    REWRITE_TAC[real_div; VECTOR_ARITH `(x * y) % a:real^N = y % x % a`] THEN
    MATCH_MP_TAC LIM_NULL_VMUL_BOUNDED THEN
    EXISTS_TAC `norm(t % (a - b):real^N)` THEN
    REWRITE_TAC[REAL_LE_REFL; EVENTUALLY_TRUE; o_DEF] THEN
    MP_TAC(MATCH_MP SEQ_OFFSET SEQ_HARMONIC) THEN
    SIMP_TAC[REAL_OF_NUM_ADD]]);;

let UNBOUNDED_CONVEX_CLOSED_CONTAINS_RAYS = prove
 (`!s:real^N->bool.
        convex s /\ ~bounded s /\ closed s
        ==> ?l. ~(l = vec 0) /\ !a t. a IN s /\ &0 <= t ==> (a + t % l) IN s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[BOUNDED_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[UNBOUNDED_CONVEX_CLOSED_CONTAINS_RAY;
                CONVEX_CLOSED_CONTAINS_SAME_RAY]);;

let RELATIVE_INTERIOR_UNBOUNDED_CONVEX_CONTAINS_RAY = prove
 (`!s a:real^N.
        convex s /\ ~bounded s /\ a IN relative_interior s
        ==> ?l. ~(l = vec 0) /\
                !t. &0 <= t ==> (a + t % l) IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`closure s:real^N->bool`; `a:real^N`]
        UNBOUNDED_CONVEX_CLOSED_CONTAINS_RAY) THEN
  ASM_SIMP_TAC[CONVEX_CLOSURE; CLOSED_CLOSURE] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET; SUBSET; CLOSURE_SUBSET;
                  RELATIVE_INTERIOR_SUBSET];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
      `a + t % l:real^N =
       (a + (&2 * t) % l) - inv(&2) % ((a + (&2 * t) % l) - a)`] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let RELATIVE_INTERIOR_CONVEX_CONTAINS_SAME_RAY = prove
 (`!s a b l:real^N.
        convex s /\ b IN relative_interior s /\
        (!t. &0 <= t ==> (a + t % l) IN relative_interior s)
        ==> !t. &0 <= t ==> (b + t % l) IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`closure s:real^N->bool`; `a:real^N`; `b:real^N`; `l:real^N`]
        CONVEX_CLOSED_CONTAINS_SAME_RAY) THEN
  ASM_SIMP_TAC[CONVEX_CLOSURE; CLOSED_CLOSURE] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET; SUBSET; CLOSURE_SUBSET;
                  RELATIVE_INTERIOR_SUBSET];
    DISCH_TAC THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
      `a + t % l:real^N =
       (a + (&2 * t) % l) - inv(&2) % ((a + (&2 * t) % l) - a)`] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let RELATIVE_INTERIOR_UNBOUNDED_CONVEX_CONTAINS_RAYS = prove
 (`!s:real^N->bool.
        convex s /\ ~bounded s
        ==> ?l. ~(l = vec 0) /\
                !a t. a IN relative_interior s /\ &0 <= t
                      ==> (a + t % l) IN relative_interior s`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `relative_interior s:real^N->bool = {}` THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; BOUNDED_EMPTY]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[RELATIVE_INTERIOR_UNBOUNDED_CONVEX_CONTAINS_RAY;
                RELATIVE_INTERIOR_CONVEX_CONTAINS_SAME_RAY]);;

(* ------------------------------------------------------------------------- *)
(* Explicit formulas for interior and relative interior of convex hull.      *)
(* ------------------------------------------------------------------------- *)

let EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL = prove
 (`!s. FINITE s
       ==> {y:real^N | ?u. (!x. x IN s ==> &0 < u x /\ u x < &1) /\
                           sum s u = &1 /\
                           vsum s (\x. u x % x) = y}
       SUBSET relative_interior(convex hull s)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[EMPTY_GSPEC; EMPTY_SUBSET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RELATIVE_INTERIOR_MAXIMAL THEN
  REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_FINITE; SUBSET; IN_ELIM_THM] THEN
    GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[open_in; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[AFFINE_HULL_FINITE; SUBSET; IN_ELIM_THM] THEN
    GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = inf (IMAGE (\x:real^N. min (&1 - u x) (u x)) s)` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_SUB_LT; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\z:real^N. z - y) (affine hull s)` BASIS_EXISTS) THEN
  REWRITE_TAC[SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool`
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:real^N->bool` (STRIP_ASSUME_TAC o GSYM))
                    MP_TAC)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; HAS_SIZE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[SPAN_FINITE; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `compo:real^N->real^N->real`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o
    MATCH_MP BASIS_COORDINATES_LIPSCHITZ) THEN
  SUBGOAL_THEN
   `!i. i IN b ==> ?u. sum s u = &0 /\ vsum s (\x:real^N. u x % x) = i`
  MP_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN affine hull s` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[AFFINE_HULL_FINITE; IN_ELIM_THM]] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(\x. v x - u x):real^N->real` THEN
    ASM_SIMP_TAC[SUM_SUB; VSUM_SUB; VECTOR_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_SUB_REFL; VECTOR_SUB_RZERO];
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [RIGHT_IMP_EXISTS_THM; SKOLEM_THM; FORALL_AND_THM;
                TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->real^N->real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `e / B /
              (&1 + sum (b:real^N->bool)
                   (\i. abs(sup(IMAGE (abs o w i) (s:real^N->bool)))))` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 <= x ==> &0 < &1 + x`;
               SUM_POS_LE; REAL_ABS_POS] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  EXISTS_TAC
   `\x:real^N. u x + sum (b:real^N->bool)
                         (\i. compo (z:real^N) i * w i x)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SUM_ADD; REAL_ARITH `&1 + x = &1 <=> x = &0`] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_0 THEN
    ASM_SIMP_TAC[SUM_LMUL; ETA_AX; REAL_MUL_RZERO; SUM_0];
    ASM_SIMP_TAC[VSUM_ADD; VECTOR_ADD_RDISTRIB] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `y + w:real^N = z <=> w = z - y`] THEN
    ASM_SIMP_TAC[GSYM VSUM_LMUL; GSYM VSUM_RMUL; GSYM VECTOR_MUL_ASSOC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[VSUM_LMUL] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum b (\v:real^N. compo (z:real^N) v % v)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[]] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(x) < min u (&1 - u) ==> &0 < u + x /\ u + x < &1`) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
    `B * norm(z - y:real^N) * sum (b:real^N->bool)
                   (\i. abs(sup(IMAGE (abs o w i) (s:real^N->bool))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_ABS_LE THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_ASSOC] THEN
    X_GEN_TAC `i:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`(compo:real^N->real^N->real) z`;
                                  `i:real^N`]) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs a`) THEN
      ASM_SIMP_TAC[REAL_LE_SUP_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; o_THM] THEN ASM_MESON_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ x * (&1 + e) < d ==> x * e < d`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN
  ASM_SIMP_TAC[NORM_POS_LE; GSYM REAL_LT_RDIV_EQ;
               REAL_ARITH `&0 <= x ==> &0 < &1 + x`;
               SUM_POS_LE; REAL_ABS_POS] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
   `dist(z:real^N,y) < k ==> k <= d ==> norm(z - y) < d`)) THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 <= x ==> &0 < &1 + x`;
               SUM_POS_LE; REAL_ABS_POS] THEN
  EXPAND_TAC "e" THEN
  ASM_SIMP_TAC[REAL_INF_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN EXISTS_TAC `x:real^N` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL_MINIMAL = prove
 (`!s. FINITE s
       ==> {y:real^N | ?u. (!x. x IN s ==> &0 < u x) /\
                           sum s u = &1 /\
                           vsum s (\x. u x % x) = y}
       SUBSET relative_interior(convex hull s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[EMPTY_GSPEC; EMPTY_SUBSET] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `s = {a:real^N}` THENL
   [ASM_REWRITE_TAC[SUM_SING; VSUM_SING; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SING; CONVEX_HULL_SING] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN
    MESON_TAC[VECTOR_MUL_LID];
    FIRST_ASSUM(MP_TAC o MATCH_MP
      EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:real^N` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->real` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?y:real^N. y IN s /\ ~(y = x)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `sum {x,y} u <= sum s (u:real^N->real)` MP_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE; REAL_LT_IMP_LE; IN_DIFF] THEN
      ASM SET_TAC[];
      ASM_SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < y ==> x + y + &0 <= &1 ==> x < &1`) THEN
      ASM_SIMP_TAC[]]]);;

let RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT = prove
 (`!s. ~(affine_dependent s)
       ==> relative_interior(convex hull s) =
             {y:real^N | ?u. (!x. x IN s ==> &0 < u x) /\
                             sum s u = &1 /\
                             vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL_MINIMAL] THEN
  ASM_CASES_TAC `?a:real^N. s = {a}` THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[SUM_SING; VSUM_SING; CONVEX_HULL_SING;
                    RELATIVE_INTERIOR_SING] THEN
    REWRITE_TAC[IN_ELIM_THM; SUBSET; IN_SING] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `\x:real^N. &1` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `relative_interior s SUBSET s /\
    (!x. x IN s /\ ~(x IN t) ==> ~(x IN relative_interior s))
    ==> relative_interior s SUBSET t`) THEN
  REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN
  REWRITE_TAC[AFFINE_HULL_CONVEX_HULL; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC)
   (MP_TAC o SPEC `u:real^N->real`)) THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; IN_RELATIVE_INTERIOR; DE_MORGAN_THM;
                  SUBSET; IN_ELIM_THM; IN_BALL; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN DISJ2_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THEN
  SUBGOAL_THEN `(u:real^N->real) a = &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`]; ALL_TAC] THEN
  SUBGOAL_THEN `?b:real^N. b IN s /\ ~(b = a)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ norm(d % (a - b):real^N) < e`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `e / &2 / norm(a - b:real^N)` THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; NORM_POS_LT;
                 REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_NUM;
                 REAL_DIV_RMUL; REAL_LT_IMP_NZ; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `y - d % (a - b):real^N`) THEN
  ASM_REWRITE_TAC[NORM_ARITH `dist(a:real^N,a - b) = norm b`] THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IN_AFFINE_SUB_MUL_DIFF THEN
    ASM_SIMP_TAC[HULL_INC; AFFINE_AFFINE_HULL] THEN
    REWRITE_TAC[AFFINE_HULL_FINITE; IN_ELIM_THM] THEN
    EXISTS_TAC `u:real^N->real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(affine_dependent(s:real^N->bool))` THEN
  ASM_SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT_FINITE] THEN
  EXISTS_TAC `\x:real^N. (v x - u x) -
                   (if x = a then --d else if x = b then d else &0)` THEN
  REWRITE_TAC[VECTOR_SUB_RDISTRIB; MESON[]
   `(if p then a else b) % x = (if p then a % x else b % x)`] THEN
  ASM_SIMP_TAC[SUM_SUB; VSUM_SUB] THEN
  ASM_SIMP_TAC[VSUM_CASES; SUM_CASES; FINITE_RESTRICT; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[SET_RULE `a IN s ==> {x | x IN s /\ x = a} = {a}`;
   SET_RULE `b IN s /\ ~(b = a)
             ==> {x | (x IN s /\ ~(x = a)) /\ x = b} = {b}`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_LZERO; SUM_0; VSUM_0; SUM_SING; VSUM_SING] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let EXPLICIT_SUBSET_INTERIOR_CONVEX_HULL = prove
 (`!s. FINITE s /\ affine hull s = (:real^N)
       ==> {y | ?u. (!x. x IN s ==> &0 < u x /\ u x < &1) /\
                    sum s u = &1 /\
                    vsum s (\x. u x % x) = y}
           SUBSET interior(convex hull s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o
    MATCH_MP EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL) THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR; AFFINE_HULL_CONVEX_HULL]);;

let EXPLICIT_SUBSET_INTERIOR_CONVEX_HULL_MINIMAL = prove
 (`!s. FINITE s /\ affine hull s = (:real^N)
       ==> {y | ?u. (!x. x IN s ==> &0 < u x) /\
                    sum s u = &1 /\
                    vsum s (\x. u x % x) = y}
           SUBSET interior(convex hull s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o
    MATCH_MP EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL_MINIMAL) THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR; AFFINE_HULL_CONVEX_HULL]);;

let INTERIOR_CONVEX_HULL_EXPLICIT_MINIMAL = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> interior(convex hull s) =
             if CARD(s) <= dimindex(:N) then {}
              else {y | ?u. (!x. x IN s ==> &0 < u x) /\
                            sum s u = &1 /\
                            vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[EMPTY_INTERIOR_CONVEX_HULL] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `relative_interior(convex hull s):real^N->bool` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
    MATCH_MP_TAC AFFINE_INDEPENDENT_SPAN_GT THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT]]);;

let INTERIOR_CONVEX_HULL_EXPLICIT = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> interior(convex hull s) =
             if CARD(s) <= dimindex(:N) then {}
              else {y | ?u. (!x. x IN s ==> &0 < u x /\ u x < &1) /\
                            sum s u = &1 /\
                            vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_EXPLICIT_MINIMAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
 REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `u:real^N->real` THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` CHOOSE_SUBSET) THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
  DISCH_THEN(MP_TAC o SPEC `2`) THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `~(c <= n) ==> 1 <= n ==> 2 <= c`)) THEN
    REWRITE_TAC[DIMINDEX_GE_1];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
        STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?y:real^N. y IN s /\ ~(y = x)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sum {x,y} u <= sum s (u:real^N->real)` MP_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE; REAL_LT_IMP_LE; IN_DIFF] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < y ==> x + y + &0 <= &1 ==> x < &1`) THEN
  ASM_SIMP_TAC[]);;

let INTERIOR_CONVEX_HULL_3_MINIMAL = prove
 (`!a b c:real^2.
        ~collinear{a,b,c}
        ==> interior(convex hull {a,b,c}) =
                {v | ?x y z. &0 < x /\
                             &0 < y /\
                             &0 < z /\
                             x + y + z = &1 /\
                             x % a + y % b + z % c = v}`,
  REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_EXPLICIT_MINIMAL] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  CONV_TAC(LAND_CONV(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV(REWRITE_CONV
   [IN_INSERT; NOT_IN_EMPTY]))))) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH] THEN
  SIMP_TAC[FINITE_INSERT; FINITE_UNION; FINITE_EMPTY; RIGHT_EXISTS_AND_THM;
           AFFINE_HULL_FINITE_STEP_GEN; REAL_LT_ADD; REAL_HALF] THEN
  REWRITE_TAC[REAL_ARITH `&1 - a - b - c = &0 <=> a + b + c = &1`;
         VECTOR_ARITH `y - a - b - c:real^N = vec 0 <=> a + b + c = y`]);;

let INTERIOR_CONVEX_HULL_3 = prove
 (`!a b c:real^2.
        ~collinear{a,b,c}
        ==> interior(convex hull {a,b,c}) =
                {v | ?x y z. &0 < x /\ x < &1 /\
                             &0 < y /\ y < &1 /\
                             &0 < z /\ z < &1 /\
                             x + y + z = &1 /\
                             x % a + y % b + z % c = v}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Similar results for closure and (relative or absolute) frontier.          *)
(* ------------------------------------------------------------------------- *)

let CLOSURE_CONVEX_HULL = prove
 (`!s. compact s ==> closure(convex hull s) = convex hull s`,
  SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED; COMPACT_CONVEX_HULL]);;

let RELATIVE_FRONTIER_CONVEX_HULL_EXPLICIT = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> relative_frontier(convex hull s) =
                {y | ?u. (!x. x IN s ==> &0 <= u x) /\
                         (?x. x IN s /\ u x = &0) /\
                         sum s u = &1 /\
                         vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[relative_frontier; UNIONS_GSPEC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  ASM_SIMP_TAC[CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT] THEN
  ASM_SIMP_TAC[CONVEX_HULL_FINITE; RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^N->real`) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> (~(&0 < x) <=> x = &0)`] THEN
    DISCH_TAC THEN EXISTS_TAC `u:real^N->real` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->real`
     (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `u:real^N->real` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [AFFINE_DEPENDENT_EXPLICIT]) THEN
    REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC
     [`s:real^N->bool`; `(\x. u x - v x):real^N->real`] THEN
    ASM_SIMP_TAC[SUBSET_REFL; VECTOR_SUB_RDISTRIB; SUM_SUB; VSUM_SUB] THEN
    REWRITE_TAC[REAL_SUB_0; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[REAL_LT_REFL]]);;

let FRONTIER_CONVEX_HULL_EXPLICIT = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> frontier(convex hull s) =
                {y | ?u. (!x. x IN s ==> &0 <= u x) /\
                         (dimindex(:N) < CARD s ==> ?x. x IN s /\ u x = &0) /\
                         sum s u = &1 /\
                         vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  DISJ_CASES_TAC
   (ARITH_RULE `CARD(s:real^N->bool) <= dimindex(:N) \/
                dimindex(:N) < CARD(s:real^N->bool)`)
  THENL
   [ASM_SIMP_TAC[GSYM NOT_LE; INTERIOR_CONVEX_HULL_EXPLICIT] THEN
    ASM_SIMP_TAC[CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT; DIFF_EMPTY] THEN
    REWRITE_TAC[CONVEX_HULL_FINITE];
    ASM_SIMP_TAC[GSYM RELATIVE_FRONTIER_CONVEX_HULL_EXPLICIT] THEN
    REWRITE_TAC[relative_frontier] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
    EXISTS_TAC `affine hull s:real^N->bool` THEN
    ASM_SIMP_TAC[AFFINE_INDEPENDENT_SPAN_GT; HULL_MONO; HULL_SUBSET]]);;

let RELATIVE_FRONTIER_CONVEX_HULL_CASES = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> relative_frontier(convex hull s) =
                UNIONS { convex hull (s DELETE a) |a| a IN s }`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_CONVEX_HULL_EXPLICIT] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONVEX_HULL_FINITE] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:real^N->real` THEN
    ASM_SIMP_TAC[IN_DELETE; SUM_DELETE; VSUM_DELETE; REAL_SUB_RZERO] THEN
    VECTOR_ARITH_TAC;
    REWRITE_TAC[IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `(\x. if x = a then &0 else u x):real^N->real` THEN
    ASM_SIMP_TAC[COND_RAND; COND_RATOR; REAL_LE_REFL; COND_ID] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CASES; VSUM_CASES; VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC[GSYM DELETE; SUM_0; VSUM_0; REAL_ADD_LID; VECTOR_ADD_LID]]);;

let FRONTIER_CONVEX_HULL_CASES = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> frontier(convex hull s) =
                if CARD(s) <= dimindex(:N) then convex hull s
                else UNIONS { convex hull (s DELETE a) |a| a IN s }`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_EXPLICIT; DIFF_EMPTY]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RELATIVE_FRONTIER_CONVEX_HULL_CASES] THEN
  ASM_SIMP_TAC[relative_frontier; frontier;
               CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
  MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
  EXISTS_TAC `affine hull s:real^N->bool` THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_SPAN_GT; HULL_MONO; HULL_SUBSET]);;

let IN_FRONTIER_CONVEX_HULL = prove
 (`!s x:real^N.
        FINITE s /\ CARD s <= dimindex(:N) + 1 /\ x IN s
        ==> x IN frontier(convex hull s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `affine_dependent(s:real^N->bool)` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [affine_dependent]) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT] THEN
    ASM_SIMP_TAC[HULL_INC; IN_DIFF] THEN MATCH_MP_TAC(SET_RULE
     `!t. s SUBSET t /\ t = {} ==> ~(x IN s)`) THEN
    EXISTS_TAC `interior(affine hull s):real^N->bool` THEN
    SIMP_TAC[SUBSET_INTERIOR; CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    SUBGOAL_THEN `s = (a:real^N) INSERT (s DELETE a)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[HULL_REDUNDANT] THEN
    MATCH_MP_TAC EMPTY_INTERIOR_AFFINE_HULL THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[FRONTIER_CONVEX_HULL_CASES] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[HULL_INC] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    SUBGOAL_THEN `?y:real^N. y IN s /\ ~(y = x)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `x IN s ==> ~(s = {x}) ==> ?y. y IN s /\ ~(y = x)`)) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      REWRITE_TAC[NOT_LT; NOT_IN_EMPTY; ARITH_SUC; DIMINDEX_GE_1];
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]]]);;

let NOT_IN_INTERIOR_CONVEX_HULL = prove
 (`!s x:real^N.
        FINITE s /\ CARD s <= dimindex(:N) + 1 /\ x IN s
        ==> ~(x IN interior(convex hull s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP IN_FRONTIER_CONVEX_HULL) THEN
  SIMP_TAC[frontier; IN_DIFF]);;

let INTERIOR_CONVEX_HULL_EQ_EMPTY = prove
 (`!s:real^N->bool.
        s HAS_SIZE (dimindex(:N) + 1)
        ==> (interior(convex hull s) = {} <=> affine_dependent s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  ASM_CASES_TAC `affine_dependent(s:real^N->bool)` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [affine_dependent]) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT] THEN
    ASM_SIMP_TAC[HULL_INC; IN_DIFF] THEN MATCH_MP_TAC(SET_RULE
     `!t. s SUBSET t /\ t = {} ==> s = {}`) THEN
    EXISTS_TAC `interior(affine hull s):real^N->bool` THEN
    SIMP_TAC[SUBSET_INTERIOR; CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    SUBGOAL_THEN `s = (a:real^N) INSERT (s DELETE a)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[HULL_REDUNDANT] THEN
    MATCH_MP_TAC EMPTY_INTERIOR_AFFINE_HULL THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_EXPLICIT_MINIMAL] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; ARITH_RULE `~(n + 1 <= n)`] THEN
    EXISTS_TAC `vsum s (\x:real^N. inv(&(dimindex(:N)) + &1) % x)` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `\x:real^N. inv(&(dimindex(:N)) + &1)` THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    ASM_SIMP_TAC[SUM_CONST; GSYM REAL_OF_NUM_ADD] THEN
    CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Similar things in special case (could use above as lemmas here instead).  *)
(* ------------------------------------------------------------------------- *)

let SIMPLEX_EXPLICIT = prove
 (`!s:real^N->bool.
        FINITE s /\ ~(vec 0 IN s)
        ==> convex hull (vec 0 INSERT s) =
            { y | ?u. (!x. x IN s ==> &0 <= u x) /\
                      sum s u <= &1 /\
                      vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONVEX_HULL_FINITE; FINITE_INSERT] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; IN_INSERT] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `u:real^N->real` THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^N`) THEN REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `\x:real^N. if x = vec 0 then &1 - sum (s:real^N->bool) u
                           else u(x)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
      ASM_REWRITE_TAC[REAL_SUB_LE];
      MATCH_MP_TAC(REAL_ARITH `s = t ==> &1 - s + t = &1`) THEN
      MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC VSUM_EQ THEN ASM_MESON_TAC[]]]);;

let STD_SIMPLEX = prove
 (`convex hull (vec 0 INSERT { basis i | 1 <= i /\ i <= dimindex(:N)}) =
        {x:real^N | (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i) /\
                    sum (1..dimindex(:N)) (\i. x$i) <= &1 }`,
  W(MP_TAC o PART_MATCH (lhs o rand) SIMPLEX_EXPLICIT o lhs o snd) THEN ANTS_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE; GSYM IN_NUMSEG] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IN_IMAGE] THEN
    REWRITE_TAC[IN_NUMSEG] THEN MESON_TAC[BASIS_NONZERO];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXTENSION] THEN
  ONCE_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[SIMPLE_IMAGE; GSYM IN_NUMSEG] THEN
  SUBGOAL_THEN `!u. sum (IMAGE (basis:num->real^N) (1..dimindex(:N))) u =
                        sum (1..dimindex(:N)) (u o basis)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_IMAGE THEN REWRITE_TAC[IN_NUMSEG] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; BASIS_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. vsum (IMAGE (basis:num->real^N) (1..dimindex(:N))) u =
                        vsum (1..dimindex(:N)) ((u:real^N->real^N) o basis)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC VSUM_IMAGE THEN REWRITE_TAC[IN_NUMSEG] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; BASIS_INJ; FINITE_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; BASIS_EXPANSION_UNIQUE; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_NUMSEG] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x <= &1 ==> x = y ==> y <= &1`)) THEN
    MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_NUMSEG];
    STRIP_TAC THEN EXISTS_TAC `\y:real^N. y dot x` THEN
    ASM_SIMP_TAC[DOT_BASIS]]);;

let INTERIOR_STD_SIMPLEX = prove
 (`interior
    (convex hull (vec 0 INSERT { basis i | 1 <= i /\ i <= dimindex(:N)})) =
        {x:real^N | (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 < x$i) /\
                    sum (1..dimindex(:N)) (\i. x$i) < &1 }`,
  REWRITE_TAC[EXTENSION; IN_INTERIOR; IN_ELIM_THM; STD_SIMPLEX] THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:real^N`) THEN REWRITE_TAC[DIST_REFL] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_LE] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x - (e / &2) % basis k:real^N`) THEN
      REWRITE_TAC[NORM_ARITH `dist(x,x - e) = norm(e)`; NORM_MUL] THEN
      ASM_SIMP_TAC[NORM_BASIS; REAL_ARITH `&0 < e ==> abs(e / &2) * &1 < e`;
                   VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[BASIS_COMPONENT] THEN UNDISCH_TAC `&0 < e` THEN
      REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `x + (e / &2) % basis 1:real^N`) THEN
      REWRITE_TAC[NORM_ARITH `dist(x,x + e) = norm(e)`; NORM_MUL] THEN
      ASM_SIMP_TAC[NORM_BASIS; LE_REFL; DIMINDEX_GE_1] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs(e / &2) * &1 < e`] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      MATCH_MP_TAC(REAL_ARITH `x < y ==> y <= &1 ==> ~(x = &1)`) THEN
      MATCH_MP_TAC SUM_LT THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> ~(a /\ b ==> ~c)`] THEN
      SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               BASIS_COMPONENT] THEN
      CONJ_TAC THENL
       [GEN_TAC THEN COND_CASES_TAC;
        EXISTS_TAC `1` THEN REWRITE_TAC[LE_REFL; DIMINDEX_GE_1]] THEN
      ASM_REAL_ARITH_TAC];
    STRIP_TAC THEN
    EXISTS_TAC
     `min (inf(IMAGE (\i. (x:real^N)$i) (1..dimindex(:N))))
          ((&1 - sum (1..dimindex(:N)) (\i. x$i)) / &(dimindex(:N)))` THEN
    ASM_SIMP_TAC[REAL_LT_MIN] THEN
    SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; FINITE_NUMSEG;
             IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < x <=> 1 <= x`; DIMINDEX_GE_1] THEN
    ASM_REWRITE_TAC[IN_NUMSEG; REAL_MUL_LZERO; REAL_SUB_LT] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN X_GEN_TAC `y:real^N` THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `abs(xk - yk) <= d ==> d < xk ==> &0 <= yk`);
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
       [GSYM CARD_NUMSEG_1] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      SIMP_TAC[GSYM SUM_CONST; FINITE_NUMSEG] THEN
      MATCH_MP_TAC(REAL_ARITH
       `s2 <= s0 + s1 ==> s0 < &1 - s1 ==> s2 <= &1`) THEN
      REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs(y - x) <= z ==> x <= z + y`)] THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; dist; COMPONENT_LE_NORM]]);;


print_endline "convex.ml loaded"
