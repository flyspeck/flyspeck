open Hol_core
open Card
open Products
open Permutations
open Floor
open Vectors
open Determinants
include Topology1

(* ------------------------------------------------------------------------- *)
(* Basic arithmetical combining theorems for limits.                         *)
(* ------------------------------------------------------------------------- *)

let LIM_LINEAR = prove
 (`!net:(A)net h f l.
        (f --> l) net /\ linear h ==> ((\x. h(f x)) --> h l) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  ASM_CASES_TAC `trivial_limit (net:(A)net)` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o
    MATCH_MP LINEAR_BOUNDED_POS) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / B`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; dist; GSYM LINEAR_SUB; REAL_LT_RDIV_EQ] THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_MUL_SYM]);;

let LIM_CONST = prove
 (`!net a:real^N. ((\x. a) --> a) net`,
  SIMP_TAC[LIM; DIST_REFL; trivial_limit] THEN MESON_TAC[]);;

let LIM_CMUL = prove
 (`!f l c. (f --> l) net ==> ((\x. c % f x) --> c % l) net`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_LINEAR THEN
  ASM_REWRITE_TAC[REWRITE_RULE[ETA_AX]
    (MATCH_MP LINEAR_COMPOSE_CMUL LINEAR_ID)]);;

let LIM_CMUL_EQ = prove
 (`!net f l c.
        ~(c = &0) ==> (((\x. c % f x) --> c % l) net <=> (f --> l) net)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[LIM_CMUL] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c:real` o MATCH_MP LIM_CMUL) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID; ETA_AX]);;

let LIM_NEG = prove
 (`!net f l:real^N. (f --> l) net ==> ((\x. --(f x)) --> --l) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM; dist] THEN
  REWRITE_TAC[VECTOR_ARITH `--x - --y = --(x - y:real^N)`; NORM_NEG]);;

let LIM_NEG_EQ = prove
 (`!net f l:real^N. ((\x. --(f x)) --> --l) net <=> (f --> l) net`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_NEG) THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX]);;

let LIM_ADD = prove
 (`!net:(A)net f g l m.
    (f --> l) net /\ (g --> m) net ==> ((\x. f(x) + g(x)) --> l + m) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  ASM_CASES_TAC `trivial_limit (net:(A)net)` THEN
  ASM_REWRITE_TAC[AND_FORALL_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NET_DILEMMA) THEN MATCH_MP_TAC MONO_EXISTS THEN
  MESON_TAC[REAL_HALF; DIST_TRIANGLE_ADD; REAL_LT_ADD2; REAL_LET_TRANS]);;

let LIM_ABS = prove
 (`!net:(A)net f:A->real^N l.
     (f --> l) net
     ==> ((\x. lambda i. (abs(f(x)$i))) --> (lambda i. abs(l$i)):real^N) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  ASM_CASES_TAC `trivial_limit (net:(A)net)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x - y) <= norm(a - b) ==> dist(a,b) < e ==> dist(x,y) < e`) THEN
  MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
  SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT] THEN
  REAL_ARITH_TAC);;

let LIM_SUB = prove
 (`!net:(A)net f g l m.
    (f --> l) net /\ (g --> m) net ==> ((\x. f(x) - g(x)) --> l - m) net`,
  REWRITE_TAC[real_sub; VECTOR_SUB] THEN ASM_SIMP_TAC[LIM_ADD; LIM_NEG]);;

let LIM_MAX = prove
 (`!net:(A)net f g l:real^N m:real^N.
    (f --> l) net /\ (g --> m) net
    ==> ((\x. lambda i. max (f(x)$i) (g(x)$i))
         --> (lambda i. max (l$i) (m$i)):real^N) net`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LIM_ADD) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LIM_SUB) THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_ABS) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o MATCH_MP LIM_CMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  SIMP_TAC[FUN_EQ_THM; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           VECTOR_SUB_COMPONENT; LAMBDA_BETA] THEN
  REAL_ARITH_TAC);;

let LIM_MIN = prove
 (`!net:(A)net f g l:real^N m:real^N.
    (f --> l) net /\ (g --> m) net
    ==> ((\x. lambda i. min (f(x)$i) (g(x)$i))
         --> (lambda i. min (l$i) (m$i)):real^N) net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP LIM_NEG)) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_NEG o MATCH_MP LIM_MAX) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA; VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

let LIM_NORM = prove
 (`!net f:A->real^N l.
        (f --> l) net ==> ((\x. lift(norm(f x))) --> lift(norm l)) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto; DIST_LIFT] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  REWRITE_TAC[] THEN NORM_ARITH_TAC);;

let LIM_NULL = prove
 (`!net f l. (f --> l) net <=> ((\x. f(x) - l) --> vec 0) net`,
  REWRITE_TAC[LIM; dist; VECTOR_SUB_RZERO]);;

let LIM_NULL_NORM = prove
 (`!net f. (f --> vec 0) net <=> ((\x. lift(norm(f x))) --> vec 0) net`,
  REWRITE_TAC[LIM; dist; VECTOR_SUB_RZERO; REAL_ABS_NORM; NORM_LIFT]);;

let LIM_NULL_CMUL_EQ = prove
 (`!net f c.
        ~(c = &0) ==> (((\x. c % f x) --> vec 0) net <=> (f --> vec 0) net)`,
  MESON_TAC[LIM_CMUL_EQ; VECTOR_MUL_RZERO]);;

let LIM_NULL_CMUL = prove
 (`!net f c. (f --> vec 0) net ==> ((\x. c % f x) --> vec 0) net`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = &0` THEN
  ASM_SIMP_TAC[LIM_NULL_CMUL_EQ; VECTOR_MUL_LZERO; LIM_CONST]);;

let LIM_NULL_ADD = prove
 (`!net f g:A->real^N.
        (f --> vec 0) net /\ (g --> vec 0) net
        ==> ((\x. f x + g x) --> vec 0) net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD) THEN
  REWRITE_TAC[VECTOR_ADD_LID]);;

let LIM_NULL_SUB = prove
 (`!net f g:A->real^N.
        (f --> vec 0) net /\ (g --> vec 0) net
        ==> ((\x. f x - g x) --> vec 0) net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN
  REWRITE_TAC[VECTOR_SUB_RZERO]);;

let LIM_NULL_COMPARISON = prove
 (`!net f g. eventually (\x. norm(f x) <= g x) net /\
             ((\x. lift(g x)) --> vec 0) net
             ==> (f --> vec 0) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto; RIGHT_AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO; NORM_LIFT] THEN REAL_ARITH_TAC);;

let LIM_COMPONENT = prove
 (`!net f i l:real^N. (f --> l) net /\ 1 <= i /\ i <= dimindex(:N)
                      ==> ((\a. lift(f(a)$i)) --> lift(l$i)) net`,
  REWRITE_TAC[LIM; dist; GSYM LIFT_SUB; NORM_LIFT] THEN
  SIMP_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
  MESON_TAC[COMPONENT_LE_NORM; REAL_LET_TRANS]);;

let LIM_TRANSFORM_BOUND = prove
 (`!f g. eventually (\n. norm(f n) <= norm(g n)) net /\ (g --> vec 0) net
         ==> (f --> vec 0) net`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[tendsto; RIGHT_AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO] THEN REAL_ARITH_TAC);;

let LIM_NULL_CMUL_BOUNDED = prove
 (`!f g:A->real^N B.
        eventually (\a. g a = vec 0 \/ abs(f a) <= B) net /\
        (g --> vec 0) net
        ==> ((\n. f n % g n) --> vec 0) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (abs B + &1)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < abs x + &1`] THEN
  UNDISCH_TAC `eventually (\a. g a:real^N = vec 0 \/ abs(f a) <= B)
                           (net:(A net))` THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MP) THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO; o_THM; NORM_LIFT; NORM_MUL] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `x:A` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `(g:A->real^N) x = vec 0` THEN
  ASM_REWRITE_TAC[NORM_0; REAL_MUL_RZERO] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `B * e / (abs B + &1)` THEN
  ASM_SIMP_TAC[REAL_LE_MUL2; REAL_ABS_POS; NORM_POS_LE; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_ARITH `c * (a / b) = (c * a) / b`] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < abs x + &1`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `e * B <= e * abs B /\ &0 < e ==> B * e < e * (abs B + &1)`) THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC);;

let LIM_NULL_VMUL_BOUNDED = prove
 (`!f g:A->real^N B.
        ((lift o f) --> vec 0) net /\
        eventually (\a. f a = &0 \/ norm(g a) <= B) net
        ==> ((\n. f n % g n) --> vec 0) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (abs B + &1)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < abs x + &1`] THEN
  UNDISCH_TAC `eventually(\a. f a = &0 \/ norm((g:A->real^N) a) <= B) net` THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MP) THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO; o_THM; NORM_LIFT; NORM_MUL] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `x:A` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `(f:A->real) x = &0` THEN
  ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LZERO] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `e / (abs B + &1) * B` THEN
  ASM_SIMP_TAC[REAL_LE_MUL2; REAL_ABS_POS; NORM_POS_LE; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_ARITH `(a / b) * c = (a * c) / b`] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < abs x + &1`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `e * B <= e * abs B /\ &0 < e ==> e * B < e * (abs B + &1)`) THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC);;

let LIM_VSUM = prove
 (`!net f:A->B->real^N l s.
        FINITE s /\ (!i. i IN s ==> ((f i) --> (l i)) net)
        ==> ((\x. vsum s (\i. f i x)) --> vsum s l) net`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; LIM_CONST; LIM_ADD; IN_INSERT; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Deducing things about the limit from the elements.                        *)
(* ------------------------------------------------------------------------- *)

let LIM_IN_CLOSED_SET = prove
 (`!net f:A->real^N s l.
        closed s /\ eventually (\x. f(x) IN s) net /\
        ~(trivial_limit net) /\ (f --> l) net
        ==> l IN s`,
  REWRITE_TAC[closed] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `~(x IN (UNIV DIFF s)) ==> x IN s`) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `l:real^N` o GEN_REWRITE_RULE I
          [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNION] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o GEN_REWRITE_RULE I [tendsto]) THEN
  UNDISCH_TAC `eventually (\x. (f:A->real^N) x IN s) net` THEN
  ASM_REWRITE_TAC[GSYM EVENTUALLY_AND; TAUT `a ==> ~b <=> ~(a /\ b)`] THEN
  MATCH_MP_TAC NOT_EVENTUALLY THEN ASM_MESON_TAC[DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Need to prove closed(cball(x,e)) before deducing this as a corollary.     *)
(* ------------------------------------------------------------------------- *)

let LIM_NORM_UBOUND = prove
 (`!net:(A)net f (l:real^N) b.
      ~(trivial_limit net) /\
      (f --> l) net /\
      eventually (\x. norm(f x) <= b) net
      ==> norm(l) <= b`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[LIM] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[eventually] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?x:A. dist(f(x):real^N,l) < norm(l:real^N) - b /\ norm(f x) <= b`
  (CHOOSE_THEN MP_TAC) THENL [ASM_MESON_TAC[NET]; ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LT; REAL_LE_SUB_RADD; DE_MORGAN_THM; dist] THEN
  NORM_ARITH_TAC);;

let LIM_NORM_LBOUND = prove
 (`!net:(A)net f (l:real^N) b.
      ~(trivial_limit net) /\ (f --> l) net /\
      eventually (\x. b <= norm(f x)) net
      ==> b <= norm(l)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[LIM] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[eventually] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?x:A. dist(f(x):real^N,l) < b - norm(l:real^N) /\ b <= norm(f x)`
  (CHOOSE_THEN MP_TAC) THENL [ASM_MESON_TAC[NET]; ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LT; REAL_LE_SUB_RADD; DE_MORGAN_THM; dist] THEN
  NORM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of the limit, when nontrivial.                                 *)
(* ------------------------------------------------------------------------- *)

let LIM_UNIQUE = prove
 (`!net:(A)net f l:real^N l'.
      ~(trivial_limit net) /\ (f --> l) net /\ (f --> l') net ==> (l = l')`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[VECTOR_SUB_REFL] o MATCH_MP LIM_SUB) THEN
  SUBGOAL_THEN `!e. &0 < e ==> norm(l:real^N - l') <= e` MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC LIM_NORM_UBOUND THEN
    MAP_EVERY EXISTS_TAC [`net:(A)net`; `\x:A. vec 0 : real^N`] THEN
    ASM_SIMP_TAC[NORM_0; REAL_LT_IMP_LE; eventually] THEN
    ASM_MESON_TAC[trivial_limit];
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[DIST_NZ; dist] THEN
    DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `norm(l - l':real^N) / &2`) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `&0 < norm(l - l':real^N)` THEN REAL_ARITH_TAC]);;

let TENDSTO_LIM = prove
 (`!net f l. ~(trivial_limit net) /\ (f --> l) net ==> lim net f = l`,
  REWRITE_TAC[lim] THEN MESON_TAC[LIM_UNIQUE]);;

let LIM_CONST_EQ = prove
 (`!net:(A net) c d:real^N.
        ((\x. c) --> d) net <=> trivial_limit net \/ c = d`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `trivial_limit (net:A net)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[LIM]; ALL_TAC] THEN
  EQ_TAC THEN SIMP_TAC[LIM_CONST] THEN DISCH_TAC THEN
  MATCH_MP_TAC(SPEC `net:A net` LIM_UNIQUE) THEN
  EXISTS_TAC `(\x. c):A->real^N` THEN ASM_REWRITE_TAC[LIM_CONST]);;

(* ------------------------------------------------------------------------- *)
(* Some unwieldy but occasionally useful theorems about uniform limits.      *)
(* ------------------------------------------------------------------------- *)

let UNIFORM_LIM_ADD = prove
 (`!net:(A)net P f g l m.
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> norm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> norm((f n x + g n x) - (l n + m n)) < e)
                     net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AND_FORALL_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  GEN_TAC THEN REWRITE_TAC[AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:B` THEN
  ASM_CASES_TAC `(P:B->bool) n` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NORM_ARITH);;

let UNIFORM_LIM_SUB = prove
 (`!net:(A)net P f g l m.
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> norm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> norm((f n x - g n x) - (l n - m n)) < e)
                     net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AND_FORALL_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  GEN_TAC THEN REWRITE_TAC[AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:B` THEN
  ASM_CASES_TAC `(P:B->bool) n` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NORM_ARITH);;

(* ------------------------------------------------------------------------- *)
(* Limit under bilinear function, uniform version first.                     *)
(* ------------------------------------------------------------------------- *)

let UNIFORM_LIM_BILINEAR = prove
 (`!net:(A)net P (h:real^M->real^N->real^P) f g l m b1 b2.
        bilinear h /\
        eventually (\x. !n. P n ==> norm(l n) <= b1) net /\
        eventually (\x. !n. P n ==> norm(m n) <= b2) net /\
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> norm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> norm(h (f n x) (g n x) - h (l n) (m n)) < e)
                     net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o  MATCH_MP
   BILINEAR_BOUNDED_POS) THEN
  REWRITE_TAC[AND_FORALL_THM; RIGHT_AND_FORALL_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `min (abs b2 + &1) (e / &2 / (B * (abs b1 + abs b2 + &2)))`) THEN
  ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; REAL_LT_MUL; REAL_LT_MIN;
               REAL_ARITH `&0 < abs x + &1`;
               REAL_ARITH `&0 < abs x + abs y + &2`] THEN
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:B` THEN
  ASM_CASES_TAC `(P:B->bool) n` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH
    `h a b - h c d :real^N = (h a b - h a d) + (h a d - h c d)`] THEN
  ASM_SIMP_TAC[GSYM BILINEAR_LSUB; GSYM BILINEAR_RSUB] THEN
  MATCH_MP_TAC NORM_TRIANGLE_LT THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (MESON[REAL_LE_ADD2; REAL_LET_TRANS]
     `(!x y. norm(h x y:real^P) <= B * norm x * norm y)
       ==> B * norm a * norm b + B * norm c * norm d < e
           ==> norm(h a b) + norm(h c d) < e`)) THEN
  MATCH_MP_TAC(REAL_ARITH
   `x * B < e / &2 /\ y * B < e / &2 ==> B * x + B * y < e`) THEN
  CONJ_TAC THEN ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `e / &2 / (B * (abs b1 + abs b2 + &2)) *
             (abs b1 + abs b2 + &1)` THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL2 THEN
     ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN
     ASM_SIMP_TAC[REAL_ARITH `a <= b2 ==> a <= abs b1 + abs b2 + &1`] THEN
     ASM_MESON_TAC[NORM_ARITH
       `norm(f - l:real^P) < abs b2 + &1 /\ norm(l) <= b1
        ==> norm(f) <= abs b1 + abs b2 + &1`];
     ONCE_REWRITE_TAC[real_div] THEN
     ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_HALF; GSYM REAL_MUL_ASSOC;
                  REAL_INV_MUL] THEN
     REWRITE_TAC[REAL_ARITH `B * inv x * y < B <=> B * y / x < B * &1`] THEN
     ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_LT_LMUL_EQ; REAL_LT_LDIV_EQ;
                  REAL_ARITH `&0 < abs x + abs y + &2`] THEN
     REAL_ARITH_TAC]));;

let LIM_BILINEAR = prove
 (`!net:(A)net (h:real^M->real^N->real^P) f g l m.
        (f --> l) net /\ (g --> m) net /\ bilinear h
        ==> ((\x. h (f x) (g x)) --> (h l m)) net`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`net:(A)net`; `\x:one. T`; `h:real^M->real^N->real^P`;
    `\n:one. (f:A->real^M)`; `\n:one. (g:A->real^N)`;
    `\n:one. (l:real^M)`; `\n:one. (m:real^N)`;
    `norm(l:real^M)`; `norm(m:real^N)`]
   UNIFORM_LIM_BILINEAR) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; EVENTUALLY_TRUE] THEN
  ASM_REWRITE_TAC[GSYM dist; GSYM tendsto]);;

(* ------------------------------------------------------------------------- *)
(* These are special for limits out of the same vector space.                *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_ID = prove
 (`!a s. ((\x. x) --> a) (at a within s)`,
  REWRITE_TAC[LIM_WITHIN] THEN MESON_TAC[]);;

let LIM_AT_ID = prove
 (`!a. ((\x. x) --> a) (at a)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN REWRITE_TAC[LIM_WITHIN_ID]);;

let LIM_AT_ZERO = prove
 (`!f:real^M->real^N l a.
        (f --> l) (at a) <=> ((\x. f(a + x)) --> l) (at(vec 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_AT] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `&0 < d` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:real^M` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a + x:real^M`) THEN
    REWRITE_TAC[dist; VECTOR_ADD_SUB; VECTOR_SUB_RZERO];
    FIRST_X_ASSUM(MP_TAC o SPEC `x - a:real^M`) THEN
    REWRITE_TAC[dist; VECTOR_SUB_RZERO; VECTOR_SUB_ADD2]]);;

(* ------------------------------------------------------------------------- *)
(* It's also sometimes useful to extract the limit point from the net.       *)
(* ------------------------------------------------------------------------- *)

let netlimit = new_definition
  `netlimit net = @a. !x. ~(netord net x a)`;;

let NETLIMIT_WITHIN = prove
 (`!a:real^N s. ~(trivial_limit (at a within s))
                ==> (netlimit (at a within s) = a)`,
  REWRITE_TAC[trivial_limit; netlimit; AT; WITHIN; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x:real^N. ~(&0 < dist(x,a) /\ dist(x,a) <= dist(a,a) /\ x IN s)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[DIST_REFL; REAL_NOT_LT]; ASM_MESON_TAC[]]);;

let NETLIMIT_AT = prove
 (`!a. netlimit(at a) = a`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MATCH_MP_TAC NETLIMIT_WITHIN THEN
  SIMP_TAC[TRIVIAL_LIMIT_AT; WITHIN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Transformation of limit.                                                  *)
(* ------------------------------------------------------------------------- *)

let LIM_TRANSFORM = prove
 (`!net f g l.
     ((\x. f x - g x) --> vec 0) net /\ (f --> l) net ==> (g --> l) net`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_NEG) THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN BINOP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  VECTOR_ARITH_TAC);;

let LIM_TRANSFORM_EVENTUALLY = prove
 (`!net f g l.
        eventually (\x. f x = g x) net /\ (f --> l) net ==> (g --> l) net`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP LIM_EVENTUALLY) MP_TAC) THEN
  MESON_TAC[LIM_TRANSFORM]);;

let LIM_TRANSFORM_WITHIN = prove
 (`!f g x s d.
        &0 < d /\
        (!x'. x' IN s /\ &0 < dist(x',x) /\ dist(x',x) < d ==> f(x') = g(x')) /\
        (f --> l) (at x within s)
        ==> (g --> l) (at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
  REWRITE_TAC[LIM_WITHIN] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `d:real` THEN
  ASM_SIMP_TAC[VECTOR_SUB_REFL; DIST_REFL]);;

let LIM_TRANSFORM_AT = prove
 (`!f g x d.
        &0 < d /\
        (!x'. &0 < dist(x',x) /\ dist(x',x) < d ==> f(x') = g(x')) /\
        (f --> l) (at x)
        ==> (g --> l) (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN MESON_TAC[LIM_TRANSFORM_WITHIN]);;

let LIM_TRANSFORM_EQ = prove
 (`!net f:A->real^N g l.
     ((\x. f x - g x) --> vec 0) net ==> ((f --> l) net <=> (g --> l) net)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN MATCH_MP_TAC LIM_TRANSFORM THENL
   [EXISTS_TAC `f:A->real^N` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `g:A->real^N` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM LIM_NEG_EQ] THEN
    ASM_REWRITE_TAC[VECTOR_NEG_SUB; VECTOR_NEG_0]]);;

let LIM_TRANSFORM_WITHIN_SET = prove
 (`!f a s t.
        eventually (\x. x IN s <=> x IN t) (at a)
        ==> ((f --> l) (at a within s) <=> (f --> l) (at a within t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVENTUALLY_AT; LIM_WITHIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d k:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Common case assuming being away from some crucial point like 0.           *)
(* ------------------------------------------------------------------------- *)

let LIM_TRANSFORM_AWAY_WITHIN = prove
 (`!f:real^M->real^N g a b s.
        ~(a = b) /\
        (!x. x IN s /\ ~(x = a) /\ ~(x = b) ==> f(x) = g(x)) /\
        (f --> l) (at a within s)
        ==> (g --> l) (at a within s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `dist(a:real^M,b)`] THEN
  ASM_REWRITE_TAC[GSYM DIST_NZ] THEN X_GEN_TAC `y:real^M` THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[DIST_SYM; REAL_LT_REFL]);;

let LIM_TRANSFORM_AWAY_AT = prove
 (`!f:real^M->real^N g a b.
        ~(a = b) /\
        (!x. ~(x = a) /\ ~(x = b) ==> f(x) = g(x)) /\
        (f --> l) (at a)
        ==> (g --> l) (at a)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MESON_TAC[LIM_TRANSFORM_AWAY_WITHIN]);;

(* ------------------------------------------------------------------------- *)
(* Alternatively, within an open set.                                        *)
(* ------------------------------------------------------------------------- *)

let LIM_TRANSFORM_WITHIN_OPEN = prove
 (`!f g:real^M->real^N s a l.
        open s /\ a IN s /\
        (!x. x IN s /\ ~(x = a) ==> f x = g x) /\
        (f --> l) (at a)
        ==> (g --> l) (at a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_AT THEN
  EXISTS_TAC `f:real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
  ASM_MESON_TAC[DIST_NZ; DIST_SYM]);;

let LIM_TRANSFORM_WITHIN_OPEN_IN = prove
 (`!f g:real^M->real^N s t a l.
        open_in (subtopology euclidean t) s /\ a IN s /\
        (!x. x IN s /\ ~(x = a) ==> f x = g x) /\
        (f --> l) (at a within t)
        ==> (g --> l) (at a within t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_WITHIN THEN
  EXISTS_TAC `f:real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^M` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN
  ASM_MESON_TAC[DIST_NZ; DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Another quite common idiom of an explicit conditional in a sequence.      *)
(* ------------------------------------------------------------------------- *)

let LIM_CASES_FINITE_SEQUENTIALLY = prove
 (`!f g l. FINITE {n | P n}
           ==> (((\n. if P n then f n else g n) --> l) sequentially <=>
                (g --> l) sequentially)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  FIRST_ASSUM(MP_TAC o SPEC `\n:num. n` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN SIMP_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `N + 1` THEN
  ASM_MESON_TAC[ARITH_RULE `~(x <= n /\ n + 1 <= x)`]);;

let LIM_CASES_COFINITE_SEQUENTIALLY = prove
 (`!f g l. FINITE {n | ~P n}
           ==> (((\n. if P n then f n else g n) --> l) sequentially <=>
                (f --> l) sequentially)`,
  ONCE_REWRITE_TAC[TAUT `(if p then x else y) = (if ~p then y else x)`] THEN
  REWRITE_TAC[LIM_CASES_FINITE_SEQUENTIALLY]);;

let LIM_CASES_SEQUENTIALLY = prove
 (`!f g l m. (((\n. if m <= n then f n else g n) --> l) sequentially <=>
              (f --> l) sequentially) /\
             (((\n. if m < n then f n else g n) --> l) sequentially <=>
              (f --> l) sequentially) /\
             (((\n. if n <= m then f n else g n) --> l) sequentially <=>
              (g --> l) sequentially) /\
             (((\n. if n < m then f n else g n) --> l) sequentially <=>
              (g --> l) sequentially)`,
  SIMP_TAC[LIM_CASES_FINITE_SEQUENTIALLY; LIM_CASES_COFINITE_SEQUENTIALLY;
           NOT_LE; NOT_LT; FINITE_NUMSEG_LT; FINITE_NUMSEG_LE]);;

(* ------------------------------------------------------------------------- *)
(* A congruence rule allowing us to transform limits assuming not at point.  *)
(* ------------------------------------------------------------------------- *)

let LIM_CONG_WITHIN = prove
 (`(!x. ~(x = a) ==> f x = g x)
   ==> (((\x. f x) --> l) (at a within s) <=> ((g --> l) (at a within s)))`,
  REWRITE_TAC[LIM_WITHIN; GSYM DIST_NZ] THEN SIMP_TAC[]);;

let LIM_CONG_AT = prove
 (`(!x. ~(x = a) ==> f x = g x)
   ==> (((\x. f x) --> l) (at a) <=> ((g --> l) (at a)))`,
  REWRITE_TAC[LIM_AT; GSYM DIST_NZ] THEN SIMP_TAC[]);;

extend_basic_congs [LIM_CONG_WITHIN; LIM_CONG_AT];;

(* ------------------------------------------------------------------------- *)
(* Useful lemmas on closure and set of possible sequential limits.           *)
(* ------------------------------------------------------------------------- *)

let CLOSURE_SEQUENTIAL = prove
 (`!s l:real^N.
     l IN closure(s) <=> ?x. (!n. x(n) IN s) /\ (x --> l) sequentially`,
  REWRITE_TAC[closure; IN_UNION; LIMPT_SEQUENTIAL; IN_ELIM_THM; IN_DELETE] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
    `((b ==> c) /\ (~a /\ c ==> b)) /\ (a ==> c) ==> (a \/ b <=> c)`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  EXISTS_TAC `\n:num. l:real^N` THEN
  ASM_REWRITE_TAC[LIM_CONST]);;

let CLOSED_CONTAINS_SEQUENTIAL_LIMIT = prove
 (`!s x l:real^N.
        closed s /\ (!n. x n IN s) /\ (x --> l) sequentially ==> l IN s`,
  MESON_TAC[CLOSURE_SEQUENTIAL; CLOSURE_CLOSED]);;

let CLOSED_SEQUENTIAL_LIMITS = prove
 (`!s. closed s <=>
       !x l. (!n. x(n) IN s) /\ (x --> l) sequentially ==> l IN s`,
  MESON_TAC[CLOSURE_SEQUENTIAL; CLOSURE_CLOSED;
            CLOSED_LIMPT; LIMPT_SEQUENTIAL; IN_DELETE]);;

let CLOSURE_APPROACHABLE = prove
 (`!x s. x IN closure(s) <=> !e. &0 < e ==> ?y. y IN s /\ dist(y,x) < e`,
  REWRITE_TAC[closure; LIMPT_APPROACHABLE; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[DIST_REFL]);;

let CLOSED_APPROACHABLE = prove
 (`!x s. closed s
         ==> ((!e. &0 < e ==> ?y. y IN s /\ dist(y,x) < e) <=> x IN s)`,
  MESON_TAC[CLOSURE_CLOSED; CLOSURE_APPROACHABLE]);;

let IN_CLOSURE_DELETE = prove
 (`!s x:real^N. x IN closure(s DELETE x) <=> x limit_point_of s`,
  SIMP_TAC[CLOSURE_APPROACHABLE; LIMPT_APPROACHABLE; IN_DELETE; CONJ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Some other lemmas about sequences.                                        *)
(* ------------------------------------------------------------------------- *)

let SEQ_OFFSET = prove
 (`!f l k. (f --> l) sequentially ==> ((\i. f(i + k)) --> l) sequentially`,
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  MESON_TAC[ARITH_RULE `N <= n ==> N <= n + k:num`]);;

let SEQ_OFFSET_NEG = prove
 (`!f l k. (f --> l) sequentially ==> ((\i. f(i - k)) --> l) sequentially`,
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  MESON_TAC[ARITH_RULE `N + k <= n ==> N <= n - k:num`]);;

let SEQ_OFFSET_REV = prove
 (`!f l k. ((\i. f(i + k)) --> l) sequentially ==> (f --> l) sequentially`,
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  MESON_TAC[ARITH_RULE `N + k <= n ==> N <= n - k /\ (n - k) + k = n:num`]);;

let SEQ_HARMONIC = prove
 (`((\n. lift(inv(&n))) --> vec 0) sequentially`,
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
  EXISTS_TAC `N:num` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO; NORM_LIFT] THEN
  ASM_REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; LT_NZ]);;

(* ------------------------------------------------------------------------- *)
(* More properties of closed balls.                                          *)
(* ------------------------------------------------------------------------- *)

let CLOSED_CBALL = prove
 (`!x:real^N e. closed(cball(x,e))`,
  REWRITE_TAC[CLOSED_SEQUENTIAL_LIMITS; IN_CBALL; dist] THEN
  GEN_TAC THEN GEN_TAC THEN X_GEN_TAC `s:num->real^N` THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\n. x - (s:num->real^N) n` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  ASM_SIMP_TAC[LIM_SUB; LIM_CONST; SEQUENTIALLY] THEN MESON_TAC[GE_REFL]);;

let IN_INTERIOR_CBALL = prove
 (`!x s. x IN interior s <=> ?e. &0 < e /\ cball(x,e) SUBSET s`,
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  MESON_TAC[OPEN_CONTAINS_CBALL; SUBSET_TRANS;
            BALL_SUBSET_CBALL; CENTRE_IN_BALL; OPEN_BALL]);;

let LIMPT_BALL = prove
 (`!x:real^N y e. y limit_point_of ball(x,e) <=> &0 < e /\ y IN cball(x,e)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 < e` THENL
   [ALL_TAC; ASM_MESON_TAC[LIMPT_EMPTY; REAL_NOT_LT; BALL_EQ_EMPTY]] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [MESON_TAC[CLOSED_CBALL; CLOSED_LIMPT; LIMPT_SUBSET; BALL_SUBSET_CBALL];
    REWRITE_TAC[IN_CBALL; LIMPT_APPROACHABLE; IN_BALL]] THEN
  DISCH_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `y:real^N = x` THEN ASM_REWRITE_TAC[DIST_NZ] THENL
   [MP_TAC(SPECL [`d:real`; `e:real`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_MESON_TAC 0 40 1 [VECTOR_CHOOSE_DIST; DIST_SYM; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`norm(y:real^N - x)`; `d:real`] REAL_DOWN2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIST_NZ; dist]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(y:real^N) - (k / dist(y,x)) % (y - x)` THEN
  REWRITE_TAC[dist; VECTOR_ARITH `(y - c % z) - y = --c % z`] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_ARITH `x - (y - k % (y - x)) = (&1 - k) % (x - y)`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> &0 < abs k`; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < k /\ k < d ==> abs k < d`] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `norm(x:real^N - y)` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[NORM_SUB]] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < k /\ k < &1 ==> abs(&1 - k) < &1`) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_MUL_LZERO;
               REAL_MUL_LID]);;

let CLOSURE_BALL = prove
 (`!x:real^N e. &0 < e ==> (closure(ball(x,e)) = cball(x,e))`,
  SIMP_TAC[EXTENSION; closure; IN_ELIM_THM; IN_UNION; LIMPT_BALL] THEN
  REWRITE_TAC[IN_BALL; IN_CBALL] THEN REAL_ARITH_TAC);;

let INTERIOR_BALL = prove
 (`!a r. interior(ball(a,r)) = ball(a,r)`,
  SIMP_TAC[INTERIOR_OPEN; OPEN_BALL]);;

let INTERIOR_CBALL = prove
 (`!x:real^N e. interior(cball(x,e)) = ball(x,e)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 <= e` THENL
   [ALL_TAC;
    SUBGOAL_THEN `cball(x:real^N,e) = {} /\ ball(x:real^N,e) = {}`
     (fun th -> REWRITE_TAC[th; INTERIOR_EMPTY]) THEN
    REWRITE_TAC[IN_BALL; IN_CBALL; EXTENSION; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`] DIST_POS_LE) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC INTERIOR_UNIQUE THEN
  REWRITE_TAC[BALL_SUBSET_CBALL; OPEN_BALL] THEN
  X_GEN_TAC `t:real^N->bool` THEN
  SIMP_TAC[SUBSET; IN_CBALL; IN_BALL; REAL_LT_LE] THEN STRIP_TAC THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [open_def]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `z:real^N = x` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `k:real` o MATCH_MP REAL_DOWN) THEN
    SUBGOAL_THEN `?w:real^N. dist(w,x) = k` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[VECTOR_CHOOSE_DIST; DIST_SYM; REAL_LT_IMP_LE];
      ASM_MESON_TAC[REAL_NOT_LE; DIST_REFL; DIST_SYM]];
    RULE_ASSUM_TAC(REWRITE_RULE[DIST_NZ]) THEN
    DISCH_THEN(MP_TAC o SPEC `z + ((d / &2) / dist(z,x)) % (z - x:real^N)`) THEN
    REWRITE_TAC[dist; VECTOR_ADD_SUB; NORM_MUL; REAL_ABS_DIV;
                REAL_ABS_NORM; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; GSYM dist; REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    ASM_REWRITE_TAC[REAL_ARITH `abs d < d * &2 <=> &0 < d`] THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[dist] THEN
    REWRITE_TAC[VECTOR_ARITH `x - (z + k % (z - x)) = (&1 + k) % (x - z)`] THEN
    REWRITE_TAC[REAL_NOT_LE; NORM_MUL] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ; GSYM dist] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &1 < abs(&1 + x)`) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH]]);;

let FRONTIER_BALL = prove
 (`!a e. &0 < e ==> frontier(ball(a,e)) = sphere(a,e)`,
  SIMP_TAC[frontier; sphere; CLOSURE_BALL; INTERIOR_OPEN; OPEN_BALL;
           REAL_LT_IMP_LE] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; IN_BALL; IN_CBALL] THEN
  REAL_ARITH_TAC);;

let FRONTIER_CBALL = prove
 (`!a e. frontier(cball(a,e)) = sphere(a,e)`,
  SIMP_TAC[frontier; sphere; INTERIOR_CBALL; CLOSED_CBALL; CLOSURE_CLOSED;
           REAL_LT_IMP_LE] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; IN_BALL; IN_CBALL] THEN
  REAL_ARITH_TAC);;

let CBALL_EQ_EMPTY = prove
 (`!x e. (cball(x,e) = {}) <=> e < &0`,
  REWRITE_TAC[EXTENSION; IN_CBALL; NOT_IN_EMPTY; REAL_NOT_LE] THEN
  MESON_TAC[DIST_POS_LE; DIST_REFL; REAL_LTE_TRANS]);;

let CBALL_EMPTY = prove
 (`!x e. e < &0 ==> cball(x,e) = {}`,
  REWRITE_TAC[CBALL_EQ_EMPTY]);;

let CBALL_EQ_SING = prove
 (`!x:real^N e. (cball(x,e) = {x}) <=> e = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_CBALL; IN_SING] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[DIST_LE_0]] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `x + (e / &2) % basis 1:real^N` th) THEN
                       MP_TAC(SPEC `x:real^N` th)) THEN
  REWRITE_TAC[dist; VECTOR_ARITH `x - (x + e):real^N = --e`;
              VECTOR_ARITH `x + e = x <=> e:real^N = vec 0`] THEN
  REWRITE_TAC[NORM_NEG; NORM_MUL; VECTOR_MUL_EQ_0; NORM_0; VECTOR_SUB_REFL] THEN
  SIMP_TAC[NORM_BASIS; BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1] THEN
  REAL_ARITH_TAC);;

let CBALL_SING = prove
 (`!x e. e = &0 ==> cball(x,e) = {x}`,
  REWRITE_TAC[CBALL_EQ_SING]);;

let SPHERE_SING = prove
 (`!x e. e = &0 ==> sphere(x,e) = {x}`,
  SIMP_TAC[sphere; DIST_EQ_0; SING_GSPEC]);;

let SPHERE_EQ_SING = prove
 (`!a:real^N r x. sphere(a,r) = {x} <=> x = a /\ r = &0`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[SPHERE_SING] THEN
  ASM_CASES_TAC `r < &0` THEN ASM_SIMP_TAC[SPHERE_EMPTY; NOT_INSERT_EMPTY] THEN
  ASM_CASES_TAC `r = &0` THEN ASM_SIMP_TAC[SPHERE_SING] THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `!y. (x IN s ==> y IN s /\ ~(y = x)) ==> ~(s = {x})`) THEN
  EXISTS_TAC `a - (x - a):real^N` THEN REWRITE_TAC[IN_SPHERE] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NORM_ARITH);;

(* ------------------------------------------------------------------------- *)
(* For points in the interior, localization of limits makes no difference.   *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_WITHIN_INTERIOR = prove
 (`!p s x.
        x IN interior s
        ==> (eventually p (at x within s) <=> eventually p (at x))`,
  REWRITE_TAC[EVENTUALLY_WITHIN; EVENTUALLY_AT; IN_INTERIOR] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[SUBSET; IN_BALL; LEFT_IMP_FORALL_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d:real) e` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_MESON_TAC[DIST_SYM]);;

let LIM_WITHIN_INTERIOR = prove
 (`!f l s x.
        x IN interior s
        ==> ((f --> l) (at x within s) <=> (f --> l) (at x))`,
  SIMP_TAC[tendsto; EVENTUALLY_WITHIN_INTERIOR]);;

let NETLIMIT_WITHIN_INTERIOR = prove
 (`!s x:real^N. x IN interior s ==> netlimit(at x within s) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NETLIMIT_WITHIN THEN
  REWRITE_TAC[TRIVIAL_LIMIT_WITHIN] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(REWRITE_RULE[OPEN_CONTAINS_BALL]
   (SPEC_ALL OPEN_INTERIOR))) THEN
  ASM_MESON_TAC[LIMPT_SUBSET; LIMPT_BALL; CENTRE_IN_CBALL; REAL_LT_IMP_LE;
                SUBSET_TRANS; INTERIOR_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* A non-singleton connected set is perfect (i.e. has no isolated points).   *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_IMP_PERFECT = prove
 (`!s x:real^N.
        connected s /\ ~(?a. s = {a}) /\ x IN s ==> x limit_point_of s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[limit_point_of] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I
   [OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{x:real^N}` o
    GEN_REWRITE_RULE I [CONNECTED_CLOPEN]) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM SET_TAC[];
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN
    EXISTS_TAC `cball(x:real^N,e)` THEN REWRITE_TAC[CLOSED_CBALL] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_SING] THEN
    ASM_MESON_TAC[CENTRE_IN_CBALL; SUBSET; REAL_LT_IMP_LE];
    ASM SET_TAC[]]);;

let CONNECTED_IMP_PERFECT_CLOSED = prove
 (`!s x. connected s /\ closed s /\ ~(?a. s = {a})
         ==> (x limit_point_of s <=> x IN s)`,
  MESON_TAC[CONNECTED_IMP_PERFECT; CLOSED_LIMPT]);;

(* ------------------------------------------------------------------------- *)
(* Boundedness.                                                              *)
(* ------------------------------------------------------------------------- *)

let bounded = new_definition
  `bounded s <=> ?a. !x:real^N. x IN s ==> norm(x) <= a`;;

let BOUNDED_EMPTY = prove
 (`bounded {}`,
  REWRITE_TAC[bounded; NOT_IN_EMPTY]);;

let BOUNDED_SUBSET = prove
 (`!s t. bounded t /\ s SUBSET t ==> bounded s`,
  MESON_TAC[bounded; SUBSET]);;

let BOUNDED_INTERIOR = prove
 (`!s:real^N->bool. bounded s ==> bounded(interior s)`,
  MESON_TAC[BOUNDED_SUBSET; INTERIOR_SUBSET]);;

let BOUNDED_CLOSURE = prove
 (`!s:real^N->bool. bounded s ==> bounded(closure s)`,
  REWRITE_TAC[bounded; CLOSURE_SEQUENTIAL] THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MESON_TAC[REWRITE_RULE[eventually] LIM_NORM_UBOUND;
            TRIVIAL_LIMIT_SEQUENTIALLY; trivial_limit]);;

let BOUNDED_CLOSURE_EQ = prove
 (`!s:real^N->bool. bounded(closure s) <=> bounded s`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[BOUNDED_CLOSURE] THEN
  MESON_TAC[BOUNDED_SUBSET; CLOSURE_SUBSET]);;

let BOUNDED_CBALL = prove
 (`!x:real^N e. bounded(cball(x,e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bounded] THEN
  EXISTS_TAC `norm(x:real^N) + e` THEN REWRITE_TAC[IN_CBALL; dist] THEN
  NORM_ARITH_TAC);;

let BOUNDED_BALL = prove
 (`!x e. bounded(ball(x,e))`,
  MESON_TAC[BALL_SUBSET_CBALL; BOUNDED_CBALL; BOUNDED_SUBSET]);;

let FINITE_IMP_BOUNDED = prove
 (`!s:real^N->bool. FINITE s ==> bounded s`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[BOUNDED_EMPTY] THEN
  REWRITE_TAC[bounded; IN_INSERT] THEN X_GEN_TAC `x:real^N` THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `norm(x:real^N) + abs B` THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[NORM_POS_LE; REAL_ARITH
   `(y <= b /\ &0 <= x ==> y <= x + abs b) /\ x <= x + abs b`]);;

let BOUNDED_UNION = prove
 (`!s t. bounded (s UNION t) <=> bounded s /\ bounded t`,
  REWRITE_TAC[bounded; IN_UNION] THEN MESON_TAC[REAL_LE_MAX]);;

let BOUNDED_UNIONS = prove
 (`!f. FINITE f /\ (!s. s IN f ==> bounded s) ==> bounded(UNIONS f)`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; BOUNDED_EMPTY; IN_INSERT; UNIONS_INSERT] THEN
  MESON_TAC[BOUNDED_UNION]);;

let BOUNDED_POS = prove
 (`!s. bounded s <=> ?b. &0 < b /\ !x. x IN s ==> norm(x) <= b`,
  REWRITE_TAC[bounded] THEN
  MESON_TAC[REAL_ARITH `&0 < &1 + abs(y) /\ (x <= y ==> x <= &1 + abs(y))`]);;

let BOUNDED_POS_LT = prove
 (`!s. bounded s <=> ?b. &0 < b /\ !x. x IN s ==> norm(x) < b`,
  REWRITE_TAC[bounded] THEN
  MESON_TAC[REAL_LT_IMP_LE;
            REAL_ARITH `&0 < &1 + abs(y) /\ (x <= y ==> x < &1 + abs(y))`]);;

let BOUNDED_INTER = prove
 (`!s t. bounded s \/ bounded t ==> bounded (s INTER t)`,
  MESON_TAC[BOUNDED_SUBSET; INTER_SUBSET]);;

let BOUNDED_DIFF = prove
 (`!s t. bounded s ==> bounded (s DIFF t)`,
  MESON_TAC[BOUNDED_SUBSET; SUBSET_DIFF]);;

let BOUNDED_INSERT = prove
 (`!x s. bounded(x INSERT s) <=> bounded s`,
  ONCE_REWRITE_TAC[SET_RULE `x INSERT s = {x} UNION s`] THEN
  SIMP_TAC[BOUNDED_UNION; FINITE_IMP_BOUNDED; FINITE_RULES]);;

let BOUNDED_SING = prove
 (`!a. bounded {a}`,
  REWRITE_TAC[BOUNDED_INSERT; BOUNDED_EMPTY]);;

let BOUNDED_INTERS = prove
 (`!f:(real^N->bool)->bool.
        (?s:real^N->bool. s IN f /\ bounded s) ==> bounded(INTERS f)`,
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
  ASM SET_TAC[]);;

let NOT_BOUNDED_UNIV = prove
 (`~(bounded (:real^N))`,
  REWRITE_TAC[BOUNDED_POS; NOT_FORALL_THM; NOT_EXISTS_THM; IN_UNIV;
              DE_MORGAN_THM; REAL_NOT_LE] THEN
  X_GEN_TAC `B:real` THEN ASM_CASES_TAC `&0 < B` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `B + &1` VECTOR_CHOOSE_SIZE) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < B ==> &0 <= B + &1`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REAL_ARITH_TAC);;

let COBOUNDED_IMP_UNBOUNDED = prove
 (`!s. bounded((:real^N) DIFF s) ==> ~bounded s`,
  GEN_TAC THEN REWRITE_TAC[TAUT `a ==> ~b <=> ~(a /\ b)`] THEN
  REWRITE_TAC[GSYM BOUNDED_UNION; SET_RULE `UNIV DIFF s UNION s = UNIV`] THEN
  REWRITE_TAC[NOT_BOUNDED_UNIV]);;

let BOUNDED_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s. bounded s /\ linear f ==> bounded(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B1:real`) MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `B2:real` o MATCH_MP LINEAR_BOUNDED_POS) THEN
  EXISTS_TAC `B2 * B1` THEN ASM_SIMP_TAC[REAL_LT_MUL; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B2 * norm(x:real^M)` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ]);;

let BOUNDED_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (bounded (IMAGE f s) <=> bounded s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE BOUNDED_LINEAR_IMAGE));;

add_linear_invariants [BOUNDED_LINEAR_IMAGE_EQ];;

let BOUNDED_SCALING = prove
 (`!c s. bounded s ==> bounded (IMAGE (\x. c % x) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_LINEAR_IMAGE THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE_CMUL; LINEAR_ID]);;

let BOUNDED_NEGATIONS = prove
 (`!s. bounded s ==> bounded (IMAGE (--) s)`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `-- &1` o MATCH_MP BOUNDED_SCALING) THEN
  REWRITE_TAC[bounded; IN_IMAGE; VECTOR_MUL_LNEG; VECTOR_MUL_LID]);;

let BOUNDED_TRANSLATION = prove
 (`!a:real^N s. bounded s ==> bounded (IMAGE (\x. a + x) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `B + norm(a:real^N)` THEN POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL [NORM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN NORM_ARITH_TAC);;

let BOUNDED_TRANSLATION_EQ = prove
 (`!a s. bounded (IMAGE (\x:real^N. a + x) s) <=> bounded s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[BOUNDED_TRANSLATION] THEN
  DISCH_THEN(MP_TAC o SPEC `--a:real^N` o MATCH_MP BOUNDED_TRANSLATION) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID;
              VECTOR_ARITH `--a + a + x:real^N = x`]);;

add_translation_invariants [BOUNDED_TRANSLATION_EQ];;

let BOUNDED_DIFFS = prove
 (`!s t:real^N->bool.
        bounded s /\ bounded t ==> bounded {x - y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `B:real`) (X_CHOOSE_TAC `C:real`)) THEN
  EXISTS_TAC `B + C:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REPEAT STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(NORM_ARITH
   `norm x <= a /\ norm y <= b ==> norm(x - y) <= a + b`) THEN
  ASM_SIMP_TAC[]);;

let BOUNDED_SUMS = prove
 (`!s t:real^N->bool.
        bounded s /\ bounded t ==> bounded {x + y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `B:real`) (X_CHOOSE_TAC `C:real`)) THEN
  EXISTS_TAC `B + C:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REPEAT STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(NORM_ARITH
   `norm x <= a /\ norm y <= b ==> norm(x + y) <= a + b`) THEN
  ASM_SIMP_TAC[]);;

let BOUNDED_SUMS_IMAGE = prove
 (`!f g t. bounded {f x | x IN t} /\ bounded {g x | x IN t}
           ==> bounded {f x + g x | x IN t}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUMS) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
  SET_TAC[]);;

let BOUNDED_SUMS_IMAGES = prove
 (`!f:A->B->real^N t s.
        FINITE s /\
        (!a. a IN s ==> bounded {f x a | x IN t})
        ==> bounded { vsum s (f x) | x IN t}`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES] THEN CONJ_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `{vec 0:real^N}` THEN
    SIMP_TAC[FINITE_IMP_BOUNDED; FINITE_RULES] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_SUMS_IMAGE THEN
  ASM_SIMP_TAC[IN_INSERT]);;

let BOUNDED_SUBSET_BALL = prove
 (`!s x:real^N. bounded(s) ==> ?r. &0 < r /\ s SUBSET ball(x,r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&2 * B + norm(x:real^N)` THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_ARITH
    `&0 < B /\ &0 <= x ==> &0 < &2 * B + x`] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[IN_BALL] THEN
  UNDISCH_TAC `&0 < B` THEN NORM_ARITH_TAC);;

let BOUNDED_SUBSET_CBALL = prove
 (`!s x:real^N. bounded(s) ==> ?r. &0 < r /\ s SUBSET cball(x,r)`,
  MESON_TAC[BOUNDED_SUBSET_BALL; SUBSET_TRANS; BALL_SUBSET_CBALL]);;

let UNBOUNDED_INTER_COBOUNDED = prove
 (`!s t. ~bounded s /\ bounded((:real^N) DIFF t) ==> ~(s INTER t = {})`,
  REWRITE_TAC[SET_RULE `s INTER t = {} <=> s SUBSET (:real^N) DIFF t`] THEN
  MESON_TAC[BOUNDED_SUBSET]);;

let COBOUNDED_INTER_UNBOUNDED = prove
 (`!s t. bounded((:real^N) DIFF s) /\ ~bounded t ==> ~(s INTER t = {})`,
  REWRITE_TAC[SET_RULE `s INTER t = {} <=> t SUBSET (:real^N) DIFF s`] THEN
  MESON_TAC[BOUNDED_SUBSET]);;

let SUBSPACE_BOUNDED_EQ_TRIVIAL = prove
 (`!s:real^N->bool. subspace s ==> (bounded s <=> s = {vec 0})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[BOUNDED_SING] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `~(s = {a}) ==> a IN s ==> ?b. b IN s /\ ~(b = a)`)) THEN
  ASM_SIMP_TAC[SUBSPACE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[bounded; NOT_EXISTS_THM] THEN X_GEN_TAC `B:real` THEN
  DISCH_THEN(MP_TAC o SPEC `(B + &1) / norm v % v:real^N`) THEN
  ASM_SIMP_TAC[SUBSPACE_MUL; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0] THEN REAL_ARITH_TAC);;

let BOUNDED_COMPONENTWISE = prove
 (`!s:real^N->bool.
        bounded s <=> !i. 1 <= i /\ i <= dimindex(:N)
                          ==> bounded (IMAGE (\x. lift(x$i)) s)`,
  GEN_TAC THEN REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  EQ_TAC THENL [ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  SIMP_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `b:num->real` THEN
  DISCH_TAC THEN EXISTS_TAC `sum(1..dimindex(:N)) b` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. &0)` THEN
    SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_POS] THEN
    MATCH_MP_TAC SUM_LT_ALL THEN
    ASM_SIMP_TAC[IN_NUMSEG; FINITE_NUMSEG; NUMSEG_EMPTY] THEN
    REWRITE_TAC[NOT_LT; DIMINDEX_GE_1];
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[IN_NUMSEG; FINITE_NUMSEG]]);;

(* ------------------------------------------------------------------------- *)
(* Some theorems on sups and infs using the notion "bounded".                *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_LIFT = prove
 (`!s. bounded(IMAGE lift s) <=>  ?a. !x. x IN s ==> abs(x) <= a`,
  REWRITE_TAC[bounded; FORALL_LIFT; NORM_LIFT; LIFT_IN_IMAGE_LIFT]);;

let BOUNDED_HAS_SUP = prove
 (`!s. bounded(IMAGE lift s) /\ ~(s = {})
       ==> (!x. x IN s ==> x <= sup s) /\
           (!b. (!x. x IN s ==> x <= b) ==> sup s <= b)`,
  REWRITE_TAC[BOUNDED_LIFT; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[SUP; REAL_ARITH `abs(x) <= a ==> x <= a`]);;

let SUP_INSERT = prove
 (`!x s. bounded (IMAGE lift s)
         ==> sup(x INSERT s) = if s = {} then x else max x (sup s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_UNIQUE THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING] THENL
   [MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_MAX; REAL_LT_MAX; IN_INSERT] THEN
  MP_TAC(ISPEC `s:real->bool` BOUNDED_HAS_SUP) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[REAL_LE_REFL; REAL_NOT_LT]);;

let BOUNDED_HAS_INF = prove
 (`!s. bounded(IMAGE lift s) /\ ~(s = {})
       ==> (!x. x IN s ==> inf s <= x) /\
           (!b. (!x. x IN s ==> b <= x) ==> b <= inf s)`,
  REWRITE_TAC[BOUNDED_LIFT; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[INF; REAL_ARITH `abs(x) <= a ==> --a <= x`]);;

let INF_INSERT = prove
 (`!x s. bounded (IMAGE lift s)
         ==> inf(x INSERT s) = if s = {} then x else min x (inf s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INF_UNIQUE THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING] THENL
   [MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MIN_LE; REAL_MIN_LT; IN_INSERT] THEN
  MP_TAC(ISPEC `s:real->bool` BOUNDED_HAS_INF) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[REAL_LE_REFL; REAL_NOT_LT]);;

(* ------------------------------------------------------------------------- *)
(* Subset and overlapping relations on balls.                                *)
(* ------------------------------------------------------------------------- *)

let SUBSET_BALLS = prove
 (`(!a a':real^N r r'.
      ball(a,r) SUBSET ball(a',r') <=> dist(a,a') + r <= r' \/ r <= &0) /\
   (!a a':real^N r r'.
      ball(a,r) SUBSET cball(a',r') <=> dist(a,a') + r <= r' \/ r <= &0) /\
   (!a a':real^N r r'.
      cball(a,r) SUBSET ball(a',r') <=> dist(a,a') + r < r' \/ r < &0) /\
   (!a a':real^N r r'.
      cball(a,r) SUBSET cball(a',r') <=> dist(a,a') + r <= r' \/ r < &0)`,
  let lemma = prove
   (`(!a':real^N r r'.
       cball(a,r) SUBSET cball(a',r') <=> dist(a,a') + r <= r' \/ r < &0) /\
     (!a':real^N r r'.
       cball(a,r) SUBSET ball(a',r') <=> dist(a,a') + r < r' \/ r < &0)`,
    CONJ_TAC THEN
    (GEOM_ORIGIN_TAC `a':real^N` THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
    EQ_TAC THENL [REWRITE_TAC[DIST_0]; NORM_ARITH_TAC] THEN
    DISJ_CASES_TAC(REAL_ARITH `r < &0 \/ &0 <= r`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISJ1_TAC THEN
    ASM_CASES_TAC `a:real^N = vec 0` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `r % basis 1:real^N`) THEN
      ASM_SIMP_TAC[DIST_0; NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL];
      FIRST_X_ASSUM(MP_TAC o SPEC `(&1 + r / norm(a)) % a:real^N`) THEN
      SIMP_TAC[dist; VECTOR_ARITH `a - (&1 + x) % a:real^N = --(x % a)`] THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; NORM_NEG; REAL_POS;
                   REAL_LE_DIV; NORM_POS_LE; REAL_ADD_RDISTRIB; REAL_DIV_RMUL;
               NORM_EQ_0; REAL_ARITH `&0 <= x ==> abs(&1 + x) = &1 + x`]] THEN
    UNDISCH_TAC `&0 <= r` THEN NORM_ARITH_TAC))
  and tac = DISCH_THEN(MP_TAC o MATCH_MP SUBSET_CLOSURE) THEN
            ASM_SIMP_TAC[CLOSED_CBALL; CLOSURE_CLOSED; CLOSURE_BALL] in
  REWRITE_TAC[AND_FORALL_THM] THEN GEOM_ORIGIN_TAC `a':real^N` THEN
  REPEAT STRIP_TAC THEN
  (EQ_TAC THENL
    [ALL_TAC; REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN NORM_ARITH_TAC]) THEN
  MATCH_MP_TAC(SET_RULE
   `(s = {} <=> q) /\ (s SUBSET t /\ ~(s = {}) /\ ~(t = {}) ==> p)
    ==> s SUBSET t ==> p \/ q`) THEN
  REWRITE_TAC[BALL_EQ_EMPTY; CBALL_EQ_EMPTY; REAL_NOT_LE; REAL_NOT_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THENL
   [tac; tac; ALL_TAC; ALL_TAC] THEN REWRITE_TAC[lemma] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC);;

let INTER_BALLS_EQ_EMPTY = prove
 (`(!a b:real^N r s. ball(a,r) INTER ball(b,s) = {} <=>
                     r <= &0 \/ s <= &0 \/ r + s <= dist(a,b)) /\
   (!a b:real^N r s. ball(a,r) INTER cball(b,s) = {} <=>
                     r <= &0 \/ s < &0 \/ r + s <= dist(a,b)) /\
   (!a b:real^N r s. cball(a,r) INTER ball(b,s) = {} <=>
                     r < &0 \/ s <= &0 \/ r + s <= dist(a,b)) /\
   (!a b:real^N r s. cball(a,r) INTER cball(b,s) = {} <=>
                     r < &0 \/ s < &0 \/ r + s < dist(a,b))`,
  REPEAT STRIP_TAC THEN GEOM_ORIGIN_TAC `a:real^N` THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `b:real^N` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_CBALL; IN_BALL] THEN
  (EQ_TAC THENL
    [ALL_TAC;
     SPEC_TAC(`b % basis 1:real^N`,`v:real^N`) THEN CONV_TAC NORM_ARITH]) THEN
  DISCH_THEN(MP_TAC o GEN `c:real` o SPEC `c % basis 1:real^N`) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; LE_REFL; DIMINDEX_GE_1; dist; NORM_NEG;
           VECTOR_SUB_LZERO; GSYM VECTOR_SUB_RDISTRIB; REAL_MUL_RID] THEN
  ASM_REWRITE_TAC[real_abs] THEN REWRITE_TAC[GSYM real_abs] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `min b r:real` th) THEN
    MP_TAC(SPEC `max (&0) (b - s:real)` th) THEN
    MP_TAC(SPEC `(r + (b - s)) / &2` th)) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Every closed set is a G_Delta.                                            *)
(* ------------------------------------------------------------------------- *)

let CLOSED_AS_GDELTA = prove
 (`!s:real^N->bool.
        closed s
        ==> ?g. COUNTABLE g /\
                (!u. u IN g ==> open u) /\
                INTERS g = s`,
  REPEAT STRIP_TAC THEN EXISTS_TAC
   `{ UNIONS { ball(x:real^N,inv(&n + &1)) | x IN s} | n IN (:num)}` THEN
  SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE] THEN
  SIMP_TAC[FORALL_IN_IMAGE; OPEN_UNIONS; OPEN_BALL] THEN
  MATCH_MP_TAC(SET_RULE
   `closure s = s /\ s SUBSET t /\ t SUBSET closure s
    ==> t = s`) THEN
  ASM_REWRITE_TAC[CLOSURE_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_INTERS; FORALL_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[UNIONS_IMAGE; SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; CLOSURE_APPROACHABLE; INTERS_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM; UNIONS_IMAGE] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN  DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[IN_BALL] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LT_TRANS) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_LT_TRANS)) THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Compactness (the definition is the one based on convegent subsequences).  *)
(* ------------------------------------------------------------------------- *)

let compact = new_definition
  `compact s <=>
        !f:num->real^N.
            (!n. f(n) IN s)
            ==> ?l r. l IN s /\ (!m n:num. m < n ==> r(m) < r(n)) /\
                      ((f o r) --> l) sequentially`;;

let MONOTONE_BIGGER = prove
 (`!r. (!m n. m < n ==> r(m) < r(n)) ==> !n:num. n <= r(n)`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  ASM_MESON_TAC[LE_0; ARITH_RULE `n <= m /\ m < p ==> SUC n <= p`; LT]);;

let LIM_SUBSEQUENCE = prove
 (`!s r l. (!m n. m < n ==> r(m) < r(n)) /\ (s --> l) sequentially
           ==> (s o r --> l) sequentially`,
  REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN
  MESON_TAC[MONOTONE_BIGGER; LE_TRANS]);;

let MONOTONE_SUBSEQUENCE = prove
 (`!s:num->real. ?r:num->num.
           (!m n. m < n ==> r(m) < r(n)) /\
           ((!m n. m <= n ==> s(r(m)) <= s(r(n))) \/
            (!m n. m <= n ==> s(r(n)) <= s(r(m))))`,
  GEN_TAC THEN
  ASM_CASES_TAC `!n:num. ?p. n < p /\ !m. p <= m ==> s(m) <= s(p)` THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; NOT_IMP; DE_MORGAN_THM] THEN
  REWRITE_TAC[RIGHT_OR_EXISTS_THM; SKOLEM_THM; REAL_NOT_LE; REAL_NOT_LT] THENL
   [ABBREV_TAC `N = 0`; DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC)] THEN
  DISCH_THEN(X_CHOOSE_THEN `next:num->num` STRIP_ASSUME_TAC) THEN
  (MP_TAC o prove_recursive_functions_exist num_RECURSION)
   `(r 0 = next(SUC N)) /\ (!n. r(SUC n) = next(r n))` THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `!m:num n:num. r n <= m ==> s(m) <= s(r n):real`
    ASSUME_TAC THEN TRY CONJ_TAC THEN TRY DISJ2_TAC THEN
    GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LT; LE] THEN
    ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL; LT_IMP_LE; LT_TRANS];
    SUBGOAL_THEN `!n. N < (r:num->num) n` ASSUME_TAC THEN
    TRY(CONJ_TAC THENL [GEN_TAC; DISJ1_TAC THEN GEN_TAC]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[LT; LE] THEN
    TRY STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_LT_REFL; LT_LE; LTE_TRANS; REAL_LE_REFL;
                  REAL_LT_LE; REAL_LE_TRANS; LT]]);;

let CONVERGENT_BOUNDED_INCREASING = prove
 (`!s:num->real b. (!m n. m <= n ==> s m <= s n) /\ (!n. abs(s n) <= b)
                   ==> ?l. !e. &0 < e ==> ?N. !n. N <= n ==> abs(s n - l) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\x. ?n. (s:num->real) n = x` REAL_COMPLETE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `abs(x) <= b ==> x <= b`]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l - e`) THEN
  ASM_MESON_TAC[REAL_ARITH `&0 < e ==> ~(l <= l - e)`;
      REAL_ARITH `x <= y /\ y <= l /\ ~(x <= l - e) ==> abs(y - l) < e`]);;

let CONVERGENT_BOUNDED_MONOTONE = prove
 (`!s:num->real b. (!n. abs(s n) <= b) /\
                   ((!m n. m <= n ==> s m <= s n) \/
                    (!m n. m <= n ==> s n <= s m))
                   ==> ?l. !e. &0 < e ==> ?N. !n. N <= n ==> abs(s n - l) < e`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[CONVERGENT_BOUNDED_INCREASING]; ALL_TAC] THEN
  MP_TAC(SPEC `\n. --((s:num->real) n)` CONVERGENT_BOUNDED_INCREASING) THEN
  ASM_REWRITE_TAC[REAL_LE_NEG2; REAL_ABS_NEG] THEN
  ASM_MESON_TAC[REAL_ARITH `abs(x - --l) = abs(--x - l)`]);;

let COMPACT_REAL_LEMMA = prove
 (`!s b. (!n:num. abs(s n) <= b)
         ==> ?l r. (!m n:num. m < n ==> r(m) < r(n)) /\
                   !e. &0 < e ==> ?N. !n. N <= n ==> abs(s(r n) - l) < e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MP_TAC(SPEC `s:num->real` MONOTONE_SUBSEQUENCE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC CONVERGENT_BOUNDED_MONOTONE THEN ASM_MESON_TAC[]);;

let COMPACT_LEMMA = prove
 (`!s. bounded s /\ (!n. (x:num->real^N) n IN s)
       ==> !d. d <= dimindex(:N)
               ==> ?l:real^N r. (!m n. m < n ==> r m < (r:num->num) n) /\
                         !e. &0 < e
                             ==> ?N. !n i. 1 <= i /\ i <= d
                                           ==> N <= n
                                               ==> abs(x(r n)$i - l$i) < e`,
  GEN_TAC THEN REWRITE_TAC[bounded] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `b:real`) ASSUME_TAC) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 0 <=> F`; CONJ_ASSOC] THEN
    DISCH_TAC THEN EXISTS_TAC `\n:num. n` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC d <= n ==> d <= n`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\n:num. (x:num->real^N) (r n) $ (SUC d)`; `b:real`]
         COMPACT_REAL_LEMMA) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; COMPONENT_LE_NORM; ARITH_RULE `1 <= SUC n`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` (X_CHOOSE_THEN `s:num->num`
        STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`(lambda k. if k = SUC d then y else (l:real^N)$k):real^N`;
    `(r:num->num) o (s:num->num)`] THEN
  ASM_SIMP_TAC[o_THM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REPEAT(FIRST_ASSUM(C UNDISCH_THEN (MP_TAC o SPEC `e:real`) o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N1 + N2:num` THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[LAMBDA_BETA; MATCH_MP(ARITH_RULE
   `SUC d <= n ==> !i. 1 <= i /\ i <= SUC d ==> 1 <= i /\ i <= n`) th]) THEN
  REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN
  ASM_MESON_TAC[MONOTONE_BIGGER; LE_TRANS;
    ARITH_RULE `N1 + N2 <= n ==> N2 <= n:num /\ N1 <= n`;
    ARITH_RULE `1 <= i /\ i <= d /\ SUC d <= n
                ==> ~(i = SUC d) /\ 1 <= SUC d /\ d <= n /\ i <= n`]);;

let BOUNDED_CLOSED_IMP_COMPACT = prove
 (`!s:real^N->bool. bounded s /\ closed s ==> compact s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[compact] THEN
  X_GEN_TAC `x:num->real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` COMPACT_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `dimindex(:N)`) THEN
  REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->num` THEN ASM_SIMP_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> a /\ b`) THEN
  REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CLOSED_SEQUENTIAL_LIMITS]) THEN
    EXISTS_TAC `(x:num->real^N) o (r:num->num)` THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2 / &(dimindex(:N))`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; DIMINDEX_NONZERO;
               REAL_HALF; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REWRITE_TAC[dist] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MATCH_MP (REAL_ARITH `a <= b ==> b < e ==> a < e`)
                        (SPEC_ALL NORM_LE_L1)) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sum (1..dimindex(:N))
                  (\k. e / &2 / &(dimindex(:N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN
    SIMP_TAC[o_THM; LAMBDA_BETA; vector_sub] THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; LE_TRANS];
    ASM_SIMP_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_DIV_LMUL; REAL_OF_NUM_EQ;
                 DIMINDEX_NONZERO; REAL_LE_REFL; REAL_LT_LDIV_EQ; ARITH;
                 REAL_OF_NUM_LT; REAL_ARITH `x < x * &2 <=> &0 < x`]]);;

(* ------------------------------------------------------------------------- *)
(* Completeness.                                                             *)
(* ------------------------------------------------------------------------- *)

let cauchy = new_definition
  `cauchy (s:num->real^N) <=>
     !e. &0 < e ==> ?N. !m n. m >= N /\ n >= N ==> dist(s m,s n) < e`;;

let complete = new_definition
  `complete s <=>
     !f:num->real^N. (!n. f n IN s) /\ cauchy f
                      ==> ?l. l IN s /\ (f --> l) sequentially`;;

let CAUCHY = prove
 (`!s:num->real^N.
      cauchy s <=> !e. &0 < e ==> ?N. !n. n >= N ==> dist(s n,s N) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cauchy; GE] THEN EQ_TAC THENL
   [MESON_TAC[LE_REFL]; DISCH_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MESON_TAC[DIST_TRIANGLE_HALF_L]);;

let CONVERGENT_IMP_CAUCHY = prove
 (`!s l. (s --> l) sequentially ==> cauchy s`,
  REWRITE_TAC[LIM_SEQUENTIALLY; cauchy] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  ASM_MESON_TAC[GE; LE_REFL; DIST_TRIANGLE_HALF_L]);;

let CAUCHY_IMP_BOUNDED = prove
 (`!s:num->real^N. cauchy s ==> bounded {y | ?n. y = s n}`,
  REWRITE_TAC[cauchy; bounded; IN_ELIM_THM] THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[GE_REFL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n:num. N <= n ==> norm(s n :real^N) <= norm(s N) + &1`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[GE; dist; DIST_SYM; NORM_TRIANGLE_SUB;
                  REAL_ARITH `a <= b + c /\ c < &1 ==> a <= b + &1`];
    MP_TAC(ISPECL [`\n:num. norm(s n :real^N)`; `0..N`]
                  UPPER_BOUND_FINITE_SET_REAL) THEN
    SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0; LEFT_IMP_EXISTS_THM] THEN
    ASM_MESON_TAC[LE_CASES;
                  REAL_ARITH `x <= a \/ x <= b ==> x <= abs a + abs b`]]);;

let COMPACT_IMP_COMPLETE = prove
 (`!s:real^N->bool. compact s ==> complete s`,
  GEN_TAC THEN REWRITE_TAC[complete; compact] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `f:num->real^N` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] LIM_ADD)) THEN
  DISCH_THEN(MP_TAC o SPEC `\n. (f:num->real^N)(n) - f(r n)`) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0: real^N`) THEN ASM_REWRITE_TAC[o_THM] THEN
  REWRITE_TAC[VECTOR_ADD_RID; VECTOR_SUB_ADD2; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cauchy]) THEN
  REWRITE_TAC[GE; LIM; SEQUENTIALLY; dist; VECTOR_SUB_RZERO] THEN
  SUBGOAL_THEN `!n:num. n <= r(n)` MP_TAC THENL [INDUCT_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[ LE_TRANS; LE_REFL; LT; LET_TRANS; LE_0; LE_SUC_LT]);;

let COMPLETE_UNIV = prove
 (`complete(:real^N)`,
  REWRITE_TAC[complete; IN_UNIV] THEN X_GEN_TAC `x:num->real^N` THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CAUCHY_IMP_BOUNDED) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP BOUNDED_CLOSURE) THEN
  MP_TAC(ISPEC `closure {y:real^N | ?n:num. y = x n}`
               COMPACT_IMP_COMPLETE) THEN
  ASM_SIMP_TAC[BOUNDED_CLOSED_IMP_COMPACT; CLOSED_CLOSURE; complete] THEN
  DISCH_THEN(MP_TAC o SPEC `x:num->real^N`) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_REWRITE_TAC[closure; IN_ELIM_THM; IN_UNION] THEN MESON_TAC[]);;

let COMPLETE_EQ_CLOSED = prove
 (`!s:real^N->bool. complete s <=> closed s`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[complete; CLOSED_LIMPT; LIMPT_SEQUENTIAL] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN GEN_TAC THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    MESON_TAC[CONVERGENT_IMP_CAUCHY; IN_DELETE; LIM_UNIQUE;
              TRIVIAL_LIMIT_SEQUENTIALLY];
    REWRITE_TAC[complete; CLOSED_SEQUENTIAL_LIMITS] THEN DISCH_TAC THEN
    X_GEN_TAC `f:num->real^N` THEN STRIP_TAC THEN
    MP_TAC(REWRITE_RULE[complete] COMPLETE_UNIV) THEN
    DISCH_THEN(MP_TAC o SPEC `f:num->real^N`) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN ASM_MESON_TAC[]]);;

let CONVERGENT_EQ_CAUCHY = prove
 (`!s. (?l. (s --> l) sequentially) <=> cauchy s`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM; CONVERGENT_IMP_CAUCHY];
    REWRITE_TAC[REWRITE_RULE[complete; IN_UNIV] COMPLETE_UNIV]]);;

let CONVERGENT_IMP_BOUNDED = prove
 (`!s l. (s --> l) sequentially ==> bounded (IMAGE s (:num))`,
  REWRITE_TAC[LEFT_FORALL_IMP_THM; CONVERGENT_EQ_CAUCHY] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CAUCHY_IMP_BOUNDED) THEN
  REWRITE_TAC[IMAGE; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Total boundedness.                                                        *)
(* ------------------------------------------------------------------------- *)

let COMPACT_IMP_TOTALLY_BOUNDED = prove
 (`!s:real^N->bool.
        compact s
        ==> !e. &0 < e ==> ?k. FINITE k /\ k SUBSET s /\
                               s SUBSET (UNIONS(IMAGE (\x. ball(x,e)) k))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`; SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?x:num->real^N. !n. x(n) IN s /\ !m. m < n ==> ~(dist(x(m),x(n)) < e)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `?x:num->real^N.
          !n. x(n) = @y. y IN s /\ !m. m < n ==> ~(dist(x(m),y) < e)`
    MP_TAC THENL
     [MATCH_MP_TAC(MATCH_MP WF_REC WF_num) THEN SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:num->real^N` THEN
    DISCH_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    CONV_TAC SELECT_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (x:num->real^N) {m | m < n}`) THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; NOT_FORALL_THM; NOT_IMP] THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[IN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[compact; NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:num->real^N` THEN  REWRITE_TAC[NOT_IMP; FORALL_AND_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CONVERGENT_IMP_CAUCHY) THEN
  REWRITE_TAC[cauchy] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[o_THM; NOT_EXISTS_THM; NOT_IMP; NOT_FORALL_THM; NOT_IMP] THEN
  X_GEN_TAC `N:num` THEN MAP_EVERY EXISTS_TAC [`N:num`; `SUC N`] THEN
  CONJ_TAC THENL [ARITH_TAC; ASM_MESON_TAC[LT]]);;

(* ------------------------------------------------------------------------- *)
(* Heine-Borel theorem (following Burkill & Burkill vol. 2)                  *)
(* ------------------------------------------------------------------------- *)

let HEINE_BOREL_LEMMA = prove
 (`!s:real^N->bool.
      compact s
      ==> !t. s SUBSET (UNIONS t) /\ (!b. b IN t ==> open b)
              ==> ?e. &0 < e /\
                      !x. x IN s ==> ?b. b IN t /\ ball(x,e) SUBSET b`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&1 / (&n + &1)`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_LT_01; REAL_ARITH `x <= y ==> x < y + &1`;
   FORALL_AND_THM; REAL_POS; NOT_FORALL_THM; NOT_IMP; SKOLEM_THM; compact] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`l:real^N`; `r:num->num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?b:real^N->bool. l IN b /\ b IN t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; IN_UNIONS]; ALL_TAC] THEN
  SUBGOAL_THEN `?e. &0 < e /\ !z:real^N. dist(z,l) < e ==> z IN b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[open_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  SUBGOAL_THEN `&0 < e / &2` (fun th ->
    REWRITE_TAC[th; o_THM] THEN MP_TAC(GEN_REWRITE_RULE I [REAL_ARCH_INV] th))
  THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(r:num->num)(N1 + N2)`; `b:real^N->bool`]) THEN
  ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC DIST_TRIANGLE_HALF_R THEN
  EXISTS_TAC `(f:num->real^N)(r(N1 + N2:num))` THEN CONJ_TAC THENL
   [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x < a ==> x < b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N1)` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
  ASM_MESON_TAC[ARITH_RULE `(~(n = 0) ==> 0 < n)`; LE_ADD; MONOTONE_BIGGER;
                LT_IMP_LE; LE_TRANS]);;

let COMPACT_IMP_HEINE_BOREL = prove
 (`!s. compact (s:real^N->bool)
       ==> !f. (!t. t IN f ==> open t) /\ s SUBSET (UNIONS f)
               ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET (UNIONS f')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `f:(real^N->bool)->bool` o
    MATCH_MP HEINE_BOREL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real^N->real^N->bool`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `e:real` o
    MATCH_MP COMPACT_IMP_TOTALLY_BOUNDED) THEN
  ASM_REWRITE_TAC[UNIONS_IMAGE; SUBSET; IN_ELIM_THM] THEN
  REWRITE_TAC[IN_UNIONS; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (B:real^N->real^N->bool) k` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  ASM_MESON_TAC[IN_BALL]);;

(* ------------------------------------------------------------------------- *)
(* Bolzano-Weierstrass property.                                             *)
(* ------------------------------------------------------------------------- *)

let HEINE_BOREL_IMP_BOLZANO_WEIERSTRASS = prove
 (`!s:real^N->bool.
        (!f. (!t. t IN f ==> open t) /\ s SUBSET (UNIONS f)
             ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET (UNIONS f'))
        ==> !t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of t`,
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; limit_point_of] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b /\ c ==> d <=> c ==> ~d ==> a ==> ~b`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; RIGHT_AND_FORALL_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `f:real^N->real^N->bool`) THEN
  DISCH_THEN(MP_TAC o SPEC
   `{t:real^N->bool | ?x:real^N. x IN s /\ (t = f x)}`) THEN
  REWRITE_TAC[INFINITE; SUBSET; IN_ELIM_THM; IN_UNIONS; NOT_IMP] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:real^N | x IN t /\ (f(x):real^N->bool) IN g}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ_GENERAL THEN ASM_MESON_TAC[SUBSET];
    SIMP_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `u:real^N` THEN
    DISCH_TAC THEN SUBGOAL_THEN `(u:real^N) IN s` ASSUME_TAC THEN
    ASM_MESON_TAC[SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Complete the chain of compactness variants.                               *)
(* ------------------------------------------------------------------------- *)

let BOLZANO_WEIERSTRASS_IMP_BOUNDED = prove
 (`!s:real^N->bool.
        (!t. INFINITE t /\ t SUBSET s ==> ?x. x limit_point_of t)
        ==> bounded s`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  SIMP_TAC[compact; bounded] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; SKOLEM_THM; NOT_IMP] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(X_CHOOSE_TAC `beyond:real->real^N`) THEN
  (MP_TAC o prove_recursive_functions_exist num_RECURSION)
   `(f(0) = beyond(&0)) /\
    (!n. f(SUC n) = beyond(norm(f n) + &1):real^N)` THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (x:num->real^N) UNIV` THEN
  SUBGOAL_THEN
   `!m n. m < n ==> norm((x:num->real^N) m) + &1 < norm(x n)`
  ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LT] THEN
    ASM_MESON_TAC[REAL_LT_TRANS; REAL_ARITH `b < b + &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. ~(m = n) ==> &1 < dist((x:num->real^N) m,x n)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [`m:num`; `n:num`] LT_CASES) THEN
    ASM_MESON_TAC[dist; LT_CASES; NORM_TRIANGLE_SUB; NORM_SUB;
                  REAL_ARITH `x + &1 < y /\ y <= x + d ==> &1 < d`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[INFINITE_IMAGE_INJ; num_INFINITE; DIST_REFL;
                  REAL_ARITH `~(&1 < &0)`];
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN INDUCT_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `l:real^N` THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIV; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `&1 / &2`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dist((x:num->real^N) k,l)`) THEN
  ASM_SIMP_TAC[DIST_POS_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `m:num = k` THEN
  ASM_MESON_TAC[DIST_TRIANGLE_HALF_L; REAL_LT_TRANS; REAL_LT_REFL]);;

let SEQUENCE_INFINITE_LEMMA = prove
 (`!f l. (!n. ~(f(n) = l)) /\ (f --> l) sequentially
         ==> INFINITE {y:real^N | ?n. y = f n}`,
  REWRITE_TAC[INFINITE] THEN REPEAT STRIP_TAC THEN MP_TAC(ISPEC
   `IMAGE (\y:real^N. dist(y,l)) {y | ?n:num. y = f n}` INF_FINITE) THEN
  ASM_SIMP_TAC[GSYM MEMBER_NOT_EMPTY; IN_IMAGE; FINITE_IMAGE; IN_ELIM_THM] THEN
  ASM_MESON_TAC[LIM_SEQUENTIALLY; LE_REFL; REAL_NOT_LE; DIST_POS_LT]);;

let LIMPT_OF_SEQUENCE_SUBSEQUENCE = prove
 (`!f:num->real^N l.
        l limit_point_of (IMAGE f (:num))
        ==> ?r. (!m n. m < n ==> r(m) < r(n)) /\ ((f o r) --> l) sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIMPT_APPROACHABLE]) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC
   `inf((inv(&n + &1)) INSERT
    IMAGE (\k. dist((f:num->real^N) k,l))
          {k | k IN 0..n /\ ~(f k = l)})`) THEN
  SIMP_TAC[REAL_LT_INF_FINITE; FINITE_INSERT; NOT_INSERT_EMPTY;
           FINITE_RESTRICT; FINITE_NUMSEG; FINITE_IMAGE] THEN
  REWRITE_TAC[FORALL_IN_INSERT; EXISTS_IN_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  SIMP_TAC[FORALL_AND_THM; FORALL_IN_GSPEC; GSYM DIST_NZ; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num->num` STRIP_ASSUME_TAC) THEN
  (MP_TAC o prove_recursive_functions_exist num_RECURSION)
   `r 0 = nn 0 /\ (!n. r (SUC n) = nn(r n))` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->num` THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN REWRITE_TAC[LT_TRANS] THEN
    X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(r:num->num) n`; `(nn:num->num)(r(n:num))`]) THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_0; REAL_LT_REFL] THEN ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o MATCH_MP MONOTONE_BIGGER)] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[CONJUNCT1 LE] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[o_THM] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
  EXISTS_TAC `inv(&((r:num->num) n) + &1)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; LE_1; REAL_OF_NUM_ADD] THEN
  MATCH_MP_TAC(ARITH_RULE `N <= SUC n /\ n <= r n ==> N <= r n + 1`) THEN
  ASM_REWRITE_TAC[]);;

let SEQUENCE_UNIQUE_LIMPT = prove
 (`!f l l':real^N.
        (f --> l) sequentially /\ l' limit_point_of {y | ?n. y = f n}
        ==> l' = l`,
  REWRITE_TAC[SET_RULE `{y | ?n. y = f n} = IMAGE f (:num)`] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LIMPT_OF_SEQUENCE_SUBSEQUENCE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `(f:num->real^N) o (r:num->num)` THEN
  ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIM_SUBSEQUENCE]);;

let BOLZANO_WEIERSTRASS_IMP_CLOSED = prove
 (`!s:real^N->bool.
        (!t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of t)
        ==> closed s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSED_SEQUENTIAL_LIMITS] THEN
  MAP_EVERY X_GEN_TAC [`f:num->real^N`; `l:real^N`] THEN
  DISCH_TAC THEN
  MAP_EVERY (MP_TAC o ISPECL [`f:num->real^N`; `l:real^N`])
   [SEQUENCE_UNIQUE_LIMPT; SEQUENCE_INFINITE_LEMMA] THEN
  MATCH_MP_TAC(TAUT
   `(~d ==> a /\ ~(b /\ c)) ==> (a ==> b) ==> c ==> d`) THEN
  DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{y:real^N | ?n:num. y = f n}`) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM];
    ABBREV_TAC `t = {y:real^N | ?n:num. y = f n}`] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence express everything as an equivalence.                               *)
(* ------------------------------------------------------------------------- *)

let COMPACT_EQ_HEINE_BOREL = prove
 (`!s:real^N->bool.
        compact s <=>
           !f. (!t. t IN f ==> open t) /\ s SUBSET (UNIONS f)
               ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET (UNIONS f')`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[COMPACT_IMP_HEINE_BOREL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HEINE_BOREL_IMP_BOLZANO_WEIERSTRASS) THEN
  DISCH_TAC THEN MATCH_MP_TAC BOUNDED_CLOSED_IMP_COMPACT THEN
  ASM_MESON_TAC[BOLZANO_WEIERSTRASS_IMP_BOUNDED;
                BOLZANO_WEIERSTRASS_IMP_CLOSED]);;

let COMPACT_EQ_BOLZANO_WEIERSTRASS = prove
 (`!s:real^N->bool.
        compact s <=>
           !t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of t`,
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[COMPACT_EQ_HEINE_BOREL; HEINE_BOREL_IMP_BOLZANO_WEIERSTRASS];
    MESON_TAC[BOLZANO_WEIERSTRASS_IMP_BOUNDED; BOLZANO_WEIERSTRASS_IMP_CLOSED;
              BOUNDED_CLOSED_IMP_COMPACT]]);;

let COMPACT_EQ_BOUNDED_CLOSED = prove
 (`!s:real^N->bool. compact s <=> bounded s /\ closed s`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[BOUNDED_CLOSED_IMP_COMPACT] THEN
  MESON_TAC[COMPACT_EQ_BOLZANO_WEIERSTRASS; BOLZANO_WEIERSTRASS_IMP_BOUNDED;
            BOLZANO_WEIERSTRASS_IMP_CLOSED]);;

let COMPACT_IMP_BOUNDED = prove
 (`!s. compact s ==> bounded s`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED]);;

let COMPACT_IMP_CLOSED = prove
 (`!s. compact s ==> closed s`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED]);;

let COMPACT_SEQUENCE_WITH_LIMIT = prove
 (`!f l:real^N.
        (f --> l) sequentially ==> compact (l INSERT IMAGE f (:num))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
  REWRITE_TAC[BOUNDED_INSERT] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONVERGENT_IMP_BOUNDED];
    SIMP_TAC[CLOSED_LIMPT; LIMPT_INSERT; IN_INSERT] THEN
    REWRITE_TAC[IMAGE; IN_UNIV] THEN REPEAT STRIP_TAC THEN DISJ1_TAC THEN
    MATCH_MP_TAC SEQUENCE_UNIQUE_LIMPT THEN ASM_MESON_TAC[]]);;

let CLOSED_IN_COMPACT = prove
 (`!s t:real^N->bool.
        compact s /\ closed_in (subtopology euclidean s) t
        ==> compact t`,
  SIMP_TAC[IMP_CONJ; COMPACT_EQ_BOUNDED_CLOSED; CLOSED_IN_CLOSED_EQ] THEN
  MESON_TAC[BOUNDED_SUBSET]);;

let CLOSED_IN_COMPACT_EQ = prove
 (`!s t. compact s
         ==> (closed_in (subtopology euclidean s) t <=>
              compact t /\ t SUBSET s)`,
  MESON_TAC[CLOSED_IN_CLOSED_EQ; COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* A version of Heine-Borel for subtopology.                                 *)
(* ------------------------------------------------------------------------- *)

let COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY = prove
 (`!s:real^N->bool.
        compact s <=>
        (!f. (!t. t IN f ==> open_in(subtopology euclidean s) t) /\
             s SUBSET UNIONS f
             ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET UNIONS f')`,
  GEN_TAC THEN REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `f:(real^N->bool)->bool` THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `m:(real^N->bool)->(real^N->bool)`) ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `IMAGE (m:(real^N->bool)->(real^N->bool)) f`) THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (\t:real^N->bool. s INTER t) f'` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; UNIONS_IMAGE; SUBSET; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_IMAGE]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{s INTER t:real^N->bool | t IN f}`) THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; OPEN_IN_OPEN; UNIONS_IMAGE] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
    REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE; UNIONS_IMAGE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* More easy lemmas.                                                         *)
(* ------------------------------------------------------------------------- *)

let COMPACT_CLOSURE = prove
 (`!s. compact(closure s) <=> bounded s`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_CLOSURE; BOUNDED_CLOSURE_EQ]);;

let BOLZANO_WEIERSTRASS_CONTRAPOS = prove
 (`!s t:real^N->bool.
        compact s /\ t SUBSET s /\
        (!x. x IN s ==> ~(x limit_point_of t))
        ==> FINITE t`,
  REWRITE_TAC[COMPACT_EQ_BOLZANO_WEIERSTRASS; INFINITE] THEN MESON_TAC[]);;

let DISCRETE_BOUNDED_IMP_FINITE = prove
 (`!s:real^N->bool e.
        &0 < e /\
        (!x y. x IN s /\ y IN s /\ norm(y - x) < e ==> y = x) /\
        bounded s
        ==> FINITE s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact(s:real^N->bool)` MP_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
    ASM_MESON_TAC[DISCRETE_IMP_CLOSED];
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_HEINE_BOREL)] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\x:real^N. ball(x,e)) s`) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; UNIONS_IMAGE; IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[CENTRE_IN_BALL];
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`]] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s:real^N->bool = t` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [UNIONS_IMAGE]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [SUBSET]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IN_BALL; dist] THEN ASM_MESON_TAC[SUBSET]);;

let BOLZANO_WEIERSTRASS = prove
 (`!s:real^N->bool. bounded s /\ INFINITE s ==> ?x. x limit_point_of s`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NO_LIMIT_POINT_IMP_CLOSED) THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` COMPACT_EQ_BOLZANO_WEIERSTRASS) THEN
  ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_MESON_TAC[]);;

let BOUNDED_EQ_BOLZANO_WEIERSTRASS = prove
 (`!s:real^N->bool.
        bounded s <=> !t. t SUBSET s /\ INFINITE t ==> ?x. x limit_point_of t`,
  MESON_TAC[BOLZANO_WEIERSTRASS_IMP_BOUNDED; BOLZANO_WEIERSTRASS;
            BOUNDED_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* In particular, some common special cases.                                 *)
(* ------------------------------------------------------------------------- *)

let COMPACT_EMPTY = prove
 (`compact {}`,
  REWRITE_TAC[compact; NOT_IN_EMPTY]);;

let COMPACT_UNION = prove
 (`!s t. compact s /\ compact t ==> compact (s UNION t)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_UNION; CLOSED_UNION]);;

let COMPACT_INTER = prove
 (`!s t. compact s /\ compact t ==> compact (s INTER t)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_INTER; CLOSED_INTER]);;

let COMPACT_INTER_CLOSED = prove
 (`!s t. compact s /\ closed t ==> compact (s INTER t)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_INTER] THEN
  MESON_TAC[BOUNDED_SUBSET; INTER_SUBSET]);;

let CLOSED_INTER_COMPACT = prove
 (`!s t. closed s /\ compact t ==> compact (s INTER t)`,
  MESON_TAC[COMPACT_INTER_CLOSED; INTER_COMM]);;

let COMPACT_INTERS = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> compact s) /\ ~(f = {})
        ==> compact(INTERS f)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_INTERS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_INTERS THEN ASM SET_TAC[]);;

let FINITE_IMP_CLOSED = prove
 (`!s. FINITE s ==> closed s`,
  MESON_TAC[BOLZANO_WEIERSTRASS_IMP_CLOSED; INFINITE; FINITE_SUBSET]);;

let FINITE_IMP_CLOSED_IN = prove
 (`!s t. FINITE s /\ s SUBSET t ==> closed_in (subtopology euclidean t) s`,
  SIMP_TAC[CLOSED_SUBSET_EQ; FINITE_IMP_CLOSED]);;

let FINITE_IMP_COMPACT = prove
 (`!s. FINITE s ==> compact s`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; FINITE_IMP_CLOSED; FINITE_IMP_BOUNDED]);;

let COMPACT_SING = prove
 (`!a. compact {a}`,
  SIMP_TAC[FINITE_IMP_COMPACT; FINITE_RULES]);;

let COMPACT_INSERT = prove
 (`!a s. compact s ==> compact(a INSERT s)`,
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  SIMP_TAC[COMPACT_UNION; COMPACT_SING]);;

let CLOSED_SING = prove
 (`!a. closed {a}`,
  MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; COMPACT_SING]);;

let CLOSED_IN_SING = prove
 (`!u x:real^N. closed_in (subtopology euclidean u) {x} <=> x IN u`,
  SIMP_TAC[CLOSED_SUBSET_EQ; CLOSED_SING] THEN SET_TAC[]);;

let CLOSURE_SING = prove
 (`!x:real^N. closure {x} = {x}`,
  SIMP_TAC[CLOSURE_CLOSED; CLOSED_SING]);;

let CLOSED_INSERT = prove
 (`!a s. closed s ==> closed(a INSERT s)`,
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  SIMP_TAC[CLOSED_UNION; CLOSED_SING]);;

let COMPACT_CBALL = prove
 (`!x e. compact(cball(x,e))`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_CBALL; CLOSED_CBALL]);;

let COMPACT_FRONTIER_BOUNDED = prove
 (`!s. bounded s ==> compact(frontier s)`,
  SIMP_TAC[frontier; COMPACT_EQ_BOUNDED_CLOSED;
           CLOSED_DIFF; OPEN_INTERIOR; CLOSED_CLOSURE] THEN
  MESON_TAC[SUBSET_DIFF; BOUNDED_SUBSET; BOUNDED_CLOSURE]);;

let COMPACT_FRONTIER = prove
 (`!s. compact s ==> compact (frontier s)`,
  MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; COMPACT_FRONTIER_BOUNDED]);;

let BOUNDED_FRONTIER = prove
 (`!s:real^N->bool. bounded s ==> bounded(frontier s)`,
  MESON_TAC[COMPACT_FRONTIER_BOUNDED; COMPACT_IMP_BOUNDED]);;

let FRONTIER_SUBSET_COMPACT = prove
 (`!s. compact s ==> frontier s SUBSET s`,
  MESON_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_EQ_BOUNDED_CLOSED]);;

let OPEN_DELETE = prove
 (`!s x. open s ==> open(s DELETE x)`,
  let lemma = prove(`s DELETE x = s DIFF {x}`,SET_TAC[]) in
  SIMP_TAC[lemma; OPEN_DIFF; CLOSED_SING]);;

let OPEN_IN_DELETE = prove
 (`!u s a:real^N.
        open_in (subtopology euclidean u) s
        ==> open_in (subtopology euclidean u) (s DELETE a)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(a:real^N) IN s` THENL
   [ONCE_REWRITE_TAC[SET_RULE `s DELETE a = s DIFF {a}`] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_SING] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN ASM SET_TAC[];
    ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> s DELETE a = s`]]);;

let CLOSED_INTERS_COMPACT = prove
 (`!s:real^N->bool.
        closed s <=> !e. compact(cball(vec 0,e) INTER s)`,
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_INTER; CLOSED_CBALL;
             BOUNDED_INTER; BOUNDED_CBALL];
    ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[CLOSED_LIMPT] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `norm(x:real^N) + &1`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_CLOSED) THEN
  REWRITE_TAC[CLOSED_LIMPT] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  REWRITE_TAC[IN_INTER] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min e (&1 / &2)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `y:real^N` THEN SIMP_TAC[IN_INTER; IN_CBALL] THEN NORM_ARITH_TAC);;

let COMPACT_UNIONS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> compact t) ==> compact(UNIONS s)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_UNIONS; BOUNDED_UNIONS]);;

let COMPACT_DIFF = prove
 (`!s t. compact s /\ open t ==> compact(s DIFF t)`,
  ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
  SIMP_TAC[COMPACT_INTER_CLOSED; GSYM OPEN_CLOSED]);;

let COMPACT_SPHERE = prove
 (`!a:real^N r. compact(sphere(a,r))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM FRONTIER_CBALL] THEN MATCH_MP_TAC COMPACT_FRONTIER THEN
  REWRITE_TAC[COMPACT_CBALL]);;

let BOUNDED_SPHERE = prove
 (`!a:real^N r. bounded(sphere(a,r))`,
  SIMP_TAC[COMPACT_SPHERE; COMPACT_IMP_BOUNDED]);;

let CLOSED_SPHERE = prove
 (`!a r. closed(sphere(a,r))`,
  SIMP_TAC[COMPACT_SPHERE; COMPACT_IMP_CLOSED]);;

let FRONTIER_SING = prove
 (`!a:real^N. frontier {a} = {a}`,
  REWRITE_TAC[frontier; CLOSURE_SING; INTERIOR_SING; DIFF_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Finite intersection property. I could make it an equivalence in fact.     *)
(* ------------------------------------------------------------------------- *)

let COMPACT_IMP_FIP = prove
 (`!s:real^N->bool f.
        compact s /\
        (!t. t IN f ==> closed t) /\
        (!f'. FINITE f' /\ f' SUBSET f ==> ~(s INTER (INTERS f') = {}))
        ==> ~(s INTER (INTERS f) = {})`,
  let lemma = prove(`(s = UNIV DIFF t) <=> (UNIV DIFF s = t)`,SET_TAC[]) in
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\t:real^N->bool. UNIV DIFF t) f`) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[OPEN_DIFF; CLOSED_DIFF; OPEN_UNIV; CLOSED_UNIV; NOT_IMP] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) INTER INTERS f = {}` THEN
    ONCE_REWRITE_TAC[SUBSET; EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` MP_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (\t:real^N->bool. UNIV DIFF t) g`) THEN
    ASM_CASES_TAC `FINITE(g:(real^N->bool)->bool)` THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN ONCE_REWRITE_TAC[SUBSET; EXTENSION] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; IN_INTERS; IN_IMAGE; IN_DIFF;
                IN_UNIV; NOT_IN_EMPTY; lemma; UNWIND_THM1; IN_UNIONS] THEN
    SET_TAC[]]);;

let CLOSED_IMP_FIP = prove
 (`!s:real^N->bool f.
        closed s /\
        (!t. t IN f ==> closed t) /\ (?t. t IN f /\ bounded t) /\
        (!f'. FINITE f' /\ f' SUBSET f ==> ~(s INTER (INTERS f') = {}))
        ==> ~(s INTER (INTERS f) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `~((s INTER t) INTER u = {}) ==> ~(s INTER u = {})`) THEN
  MATCH_MP_TAC COMPACT_IMP_FIP THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CLOSED_INTER_COMPACT; COMPACT_EQ_BOUNDED_CLOSED];
    REWRITE_TAC[INTER_ASSOC] THEN ONCE_REWRITE_TAC[GSYM INTERS_INSERT]] THEN
  GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FINITE_INSERT; INSERT_SUBSET]);;

let CLOSED_IMP_FIP_COMPACT = prove
 (`!s:real^N->bool f.
        closed s /\ (!t. t IN f ==> compact t) /\
        (!f'. FINITE f' /\ f' SUBSET f ==> ~(s INTER (INTERS f') = {}))
        ==> ~(s INTER (INTERS f) = {})`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
  ASM_SIMP_TAC[SUBSET_EMPTY; INTERS_0; INTER_UNIV] THENL
   [MESON_TAC[FINITE_EMPTY]; ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC CLOSED_IMP_FIP THEN
  ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; MEMBER_NOT_EMPTY]);;

let CLOSED_FIP = prove
 (`!f. (!t:real^N->bool. t IN f ==> closed t) /\ (?t. t IN f /\ bounded t) /\
       (!f'. FINITE f' /\ f' SUBSET f ==> ~(INTERS f' = {}))
       ==> ~(INTERS f = {})`,
  GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `s = {} <=> UNIV INTER s = {}`] THEN
  MATCH_MP_TAC CLOSED_IMP_FIP THEN ASM_REWRITE_TAC[CLOSED_UNIV; INTER_UNIV]);;

let COMPACT_FIP = prove
 (`!f. (!t:real^N->bool. t IN f ==> compact t) /\
       (!f'. FINITE f' /\ f' SUBSET f ==> ~(INTERS f' = {}))
       ==> ~(INTERS f = {})`,
  GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `s = {} <=> UNIV INTER s = {}`] THEN
  MATCH_MP_TAC CLOSED_IMP_FIP_COMPACT THEN
  ASM_REWRITE_TAC[CLOSED_UNIV; INTER_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Bounded closed nest property (proof does not use Heine-Borel).            *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_CLOSED_NEST = prove
 (`!s. (!n. closed(s n)) /\ (!n. ~(s n = {})) /\
       (!m n. m <= n ==> s(n) SUBSET s(m)) /\
       bounded(s 0)
       ==> ?a:real^N. !n:num. a IN s(n)`,
  GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `a:num->real^N`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `compact(s 0:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[BOUNDED_CLOSED_IMP_COMPACT]; ALL_TAC] THEN
  REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `a:num->real^N`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; LE_0]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^N` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~(~p)`] THEN
  GEN_REWRITE_TAC RAND_CONV [NOT_FORALL_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
  MP_TAC(ISPECL [`l:real^N`; `(s:num->real^N->bool) N`]
                CLOSED_APPROACHABLE) THEN
  ASM_MESON_TAC[SUBSET; LE_REFL; LE_TRANS; LE_CASES; MONOTONE_BIGGER]);;

(* ------------------------------------------------------------------------- *)
(* Decreasing case does not even need compactness, just completeness.        *)
(* ------------------------------------------------------------------------- *)

let DECREASING_CLOSED_NEST = prove
 (`!s. (!n. closed(s n)) /\ (!n. ~(s n = {})) /\
       (!m n. m <= n ==> s(n) SUBSET s(m)) /\
       (!e. &0 < e ==> ?n. !x y. x IN s(n) /\ y IN s(n) ==> dist(x,y) < e)
       ==> ?a:real^N. !n:num. a IN s(n)`,
  GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `a:num->real^N`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?l:real^N. (a --> l) sequentially` MP_TAC THENL
   [ASM_MESON_TAC[cauchy; GE; SUBSET; LE_TRANS; LE_REFL;
                  complete; COMPLETE_UNIV; IN_UNIV];
    ASM_MESON_TAC[LIM_SEQUENTIALLY; CLOSED_APPROACHABLE;
                  SUBSET; LE_REFL; LE_TRANS; LE_CASES]]);;

(* ------------------------------------------------------------------------- *)
(* Strengthen it to the intersection actually being a singleton.             *)
(* ------------------------------------------------------------------------- *)

let DECREASING_CLOSED_NEST_SING = prove
 (`!s. (!n. closed(s n)) /\ (!n. ~(s n = {})) /\
       (!m n. m <= n ==> s(n) SUBSET s(m)) /\
       (!e. &0 < e ==> ?n. !x y. x IN s(n) /\ y IN s(n) ==> dist(x,y) < e)
       ==> ?a:real^N. INTERS {t | ?n:num. t = s n} = {a}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DECREASING_CLOSED_NEST) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  DISCH_TAC THEN REWRITE_TAC[EXTENSION; IN_INTERS; IN_SING; IN_ELIM_THM] THEN
  ASM_MESON_TAC[DIST_POS_LT; REAL_LT_REFL; SUBSET; LE_CASES]);;

(* ------------------------------------------------------------------------- *)
(* A version for a more general chain, not indexed by N.                     *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_CLOSED_CHAIN = prove
 (`!f b:real^N->bool.
        (!s. s IN f ==> closed s /\ ~(s = {})) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s) /\
         b IN f /\ bounded b
         ==> ~(INTERS f = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(b INTER (INTERS f):real^N->bool = {})` MP_TAC THENL
   [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC COMPACT_IMP_FIP THEN
  ASM_SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
  X_GEN_TAC `u:(real^N->bool)->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN f /\ !t. t IN u ==> s SUBSET t`
  MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  UNDISCH_TAC `(u:(real^N->bool)->bool) SUBSET f` THEN
  UNDISCH_TAC `FINITE(u:(real^N->bool)->bool)` THEN
  SPEC_TAC(`u:(real^N->bool)->bool`,`u:(real^N->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:(real^N->bool)->bool`] THEN
  REWRITE_TAC[INSERT_SUBSET] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `t:real^N->bool`]) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Analogous things directly for compactness.                                *)
(* ------------------------------------------------------------------------- *)

let COMPACT_CHAIN = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> compact s /\ ~(s = {})) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[INTERS_0] THEN SET_TAC[];
    MATCH_MP_TAC BOUNDED_CLOSED_CHAIN THEN ASM SET_TAC[]]);;

let COMPACT_NEST = prove
 (`!s. (!n. compact(s n) /\ ~(s n = {})) /\
       (!m n. m <= n ==> s n SUBSET s m)
       ==> ~(INTERS {s n | n IN (:num)} = {})`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC COMPACT_CHAIN THEN
  ASM_SIMP_TAC[FORALL_IN_GSPEC; IN_UNIV; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC WLOG_LE THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cauchy-type criteria for *uniform* convergence.                           *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONVERGENT_EQ_CAUCHY = prove
 (`!P s:num->A->real^N.
         (?l. !e. &0 < e
                  ==> ?N. !n x. N <= n /\ P x ==> dist(s n x,l x) < e) <=>
         (!e. &0 < e
              ==> ?N. !m n x. N <= m /\ N <= n /\ P x
                              ==> dist(s m x,s n x) < e)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `l:A->real^N`) THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN MESON_TAC[DIST_TRIANGLE_HALF_L];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x:A. P x ==> cauchy (\n. s n x :real^N)` MP_TAC THENL
   [REWRITE_TAC[cauchy; GE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY; LIM_SEQUENTIALLY] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `l:A->real^N` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `N + M:num`; `x:A`]) THEN
  ASM_REWRITE_TAC[LE_ADD] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M + N:num`) THEN REWRITE_TAC[LE_ADD] THEN
  ASM_MESON_TAC[DIST_TRIANGLE_HALF_L; DIST_SYM]);;

let UNIFORMLY_CONVERGENT_EQ_CAUCHY_ALT = prove
 (`!P s:num->A->real^N.
         (?l. !e. &0 < e
                  ==> ?N. !n x. N <= n /\ P x ==> dist(s n x,l x) < e) <=>
         (!e. &0 < e
              ==> ?N. !m n x. N <= m /\ N <= n /\ m < n /\ P x
                              ==> dist(s m x,s n x) < e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNIFORMLY_CONVERGENT_EQ_CAUCHY] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC WLOG_LT THEN
  ASM_SIMP_TAC[DIST_REFL] THEN MESON_TAC[DIST_SYM]);;

let UNIFORMLY_CAUCHY_IMP_UNIFORMLY_CONVERGENT = prove
 (`!P (s:num->A->real^N) l.
    (!e. &0 < e
         ==> ?N. !m n x. N <= m /\ N <= n /\ P x ==> dist(s m x,s n x) < e) /\
    (!x. P x ==> !e. &0 < e ==> ?N. !n. N <= n ==> dist(s n x,l x) < e)
    ==> (!e. &0 < e ==> ?N. !n x. N <= n /\ P x ==> dist(s n x,l x) < e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM UNIFORMLY_CONVERGENT_EQ_CAUCHY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `l':A->real^N`) ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. P x ==> (l:A->real^N) x = l' x` MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n. (s:num->A->real^N) n x` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Define continuity over a net to take in restrictions of the set.          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("continuous",(12,"right"));;

let continuous = new_definition
  `f continuous net <=> (f --> f(netlimit net)) net`;;

let CONTINUOUS_TRIVIAL_LIMIT = prove
 (`!f net. trivial_limit net ==> f continuous net`,
  SIMP_TAC[continuous; LIM]);;

let CONTINUOUS_WITHIN = prove
 (`!f x:real^M. f continuous (at x within s) <=> (f --> f(x)) (at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous] THEN
  ASM_CASES_TAC `trivial_limit(at (x:real^M) within s)` THENL
   [ASM_REWRITE_TAC[LIM]; ASM_SIMP_TAC[NETLIMIT_WITHIN]]);;

let CONTINUOUS_AT = prove
 (`!f (x:real^N). f continuous (at x) <=> (f --> f(x)) (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_WITHIN; IN_UNIV]);;

let CONTINUOUS_AT_WITHIN = prove
 (`!f:real^M->real^N x s.
        f continuous (at x) ==> f continuous (at x within s)`,
  SIMP_TAC[LIM_AT_WITHIN; CONTINUOUS_AT; CONTINUOUS_WITHIN]);;

let CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL = prove
 (`!a s. closed s /\ ~(a IN s) ==> f continuous (at a within s)`,
  ASM_SIMP_TAC[continuous; LIM; LIM_WITHIN_CLOSED_TRIVIAL]);;

let CONTINUOUS_TRANSFORM_WITHIN = prove
 (`!f g:real^M->real^N s x d.
        &0 < d /\ x IN s /\
        (!x'. x' IN s /\ dist(x',x) < d ==> f(x') = g(x')) /\
        f continuous (at x within s)
        ==> g continuous (at x within s)`,
  REWRITE_TAC[CONTINUOUS_WITHIN] THEN
  MESON_TAC[LIM_TRANSFORM_WITHIN; DIST_REFL]);;

let CONTINUOUS_TRANSFORM_AT = prove
 (`!f g:real^M->real^N x d.
        &0 < d /\ (!x'. dist(x',x) < d ==> f(x') = g(x')) /\
        f continuous (at x)
        ==> g continuous (at x)`,
  REWRITE_TAC[CONTINUOUS_AT] THEN
  MESON_TAC[LIM_TRANSFORM_AT; DIST_REFL]);;

let CONTINUOUS_TRANSFORM_WITHIN_OPEN = prove
 (`!f g:real^M->real^N s a.
        open s /\ a IN s /\
        (!x. x IN s ==> f x = g x) /\
        f continuous at a
        ==> g continuous at a`,
  MESON_TAC[CONTINUOUS_AT; LIM_TRANSFORM_WITHIN_OPEN]);;

let CONTINUOUS_TRANSFORM_WITHIN_OPEN_IN = prove
 (`!f g:real^M->real^N s t a.
        open_in (subtopology euclidean t) s /\ a IN s /\
        (!x. x IN s ==> f x = g x) /\
        f continuous (at a within t)
        ==> g continuous (at a within t)`,
  MESON_TAC[CONTINUOUS_WITHIN; LIM_TRANSFORM_WITHIN_OPEN_IN]);;

(* ------------------------------------------------------------------------- *)
(* Derive the epsilon-delta forms, which we often use as "definitions"       *)
(* ------------------------------------------------------------------------- *)

let continuous_within = prove
 (`f continuous (at x within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x'. x' IN s /\ dist(x',x) < d ==> dist(f(x'),f(x)) < e`,
  REWRITE_TAC[CONTINUOUS_WITHIN; LIM_WITHIN] THEN
  REWRITE_TAC[GSYM DIST_NZ] THEN MESON_TAC[DIST_REFL]);;

let continuous_at = prove
 (`f continuous (at x) <=>
        !e. &0 < e ==> ?d. &0 < d /\
                           !x'. dist(x',x) < d ==> dist(f(x'),f(x)) < e`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[continuous_within; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Versions in terms of open balls.                                          *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_BALL = prove
 (`!f s x. f continuous (at x within s) <=>
                !e. &0 < e
                    ==> ?d. &0 < d /\
                            IMAGE f (ball(x,d) INTER s) SUBSET ball(f x,e)`,
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL; continuous_within; IN_INTER] THEN
  MESON_TAC[DIST_SYM]);;

let CONTINUOUS_AT_BALL = prove
 (`!f x. f continuous (at x) <=>
                !e. &0 < e
                    ==> ?d. &0 < d /\
                            IMAGE f (ball(x,d)) SUBSET ball(f x,e)`,
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL; continuous_at] THEN
  MESON_TAC[DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* For setwise continuity, just start from the epsilon-delta definitions.    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("continuous_on",(12,"right"));;
parse_as_infix ("uniformly_continuous_on",(12,"right"));;

let continuous_on = new_definition
  `f continuous_on s <=>
        !x. x IN s ==> !e. &0 < e
                           ==> ?d. &0 < d /\
                                   !x'. x' IN s /\ dist(x',x) < d
                                        ==> dist(f(x'),f(x)) < e`;;

let uniformly_continuous_on = new_definition
  `f uniformly_continuous_on s <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. x IN s /\ x' IN s /\ dist(x',x) < d
                           ==> dist(f(x'),f(x)) < e`;;

(* ------------------------------------------------------------------------- *)
(* Some simple consequential lemmas.                                         *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS = prove
 (`!f s. f uniformly_continuous_on s ==> f continuous_on s`,
  REWRITE_TAC[uniformly_continuous_on; continuous_on] THEN MESON_TAC[]);;

let CONTINUOUS_AT_IMP_CONTINUOUS_ON = prove
 (`!f s. (!x. x IN s ==> f continuous (at x)) ==> f continuous_on s`,
  REWRITE_TAC[continuous_at; continuous_on] THEN MESON_TAC[]);;

let CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN = prove
 (`!f s. f continuous_on s <=> !x. x IN s ==> f continuous (at x within s)`,
  REWRITE_TAC[continuous_on; continuous_within]);;

let CONTINUOUS_ON = prove
 (`!f (s:real^N->bool).
        f continuous_on s <=> !x. x IN s ==> (f --> f(x)) (at x within s)`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_WITHIN]);;

let CONTINUOUS_ON_EQ_CONTINUOUS_AT = prove
 (`!f:real^M->real^N s.
      open s ==> (f continuous_on s <=> (!x. x IN s ==> f continuous (at x)))`,
  SIMP_TAC[CONTINUOUS_ON; CONTINUOUS_AT; LIM_WITHIN_OPEN]);;

let CONTINUOUS_WITHIN_SUBSET = prove
 (`!f s t x. f continuous (at x within s) /\ t SUBSET s
             ==> f continuous (at x within t)`,
   REWRITE_TAC[CONTINUOUS_WITHIN] THEN MESON_TAC[LIM_WITHIN_SUBSET]);;

let CONTINUOUS_ON_SUBSET = prove
 (`!f s t. f continuous_on s /\ t SUBSET s ==> f continuous_on t`,
  REWRITE_TAC[CONTINUOUS_ON] THEN MESON_TAC[SUBSET; LIM_WITHIN_SUBSET]);;

let UNIFORMLY_CONTINUOUS_ON_SUBSET = prove
 (`!f s t. f uniformly_continuous_on s /\ t SUBSET s
           ==> f uniformly_continuous_on t`,
  REWRITE_TAC[uniformly_continuous_on] THEN
  MESON_TAC[SUBSET; LIM_WITHIN_SUBSET]);;

let CONTINUOUS_ON_INTERIOR = prove
 (`!f:real^M->real^N s x.
        f continuous_on s /\ x IN interior(s) ==> f continuous at x`,
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; CONTINUOUS_ON_SUBSET]);;

let CONTINUOUS_ON_EQ = prove
 (`!f g s. (!x. x IN s ==> f(x) = g(x)) /\ f continuous_on s
           ==> g continuous_on s`,
  SIMP_TAC[continuous_on; IMP_CONJ]);;

let UNIFORMLY_CONTINUOUS_ON_EQ = prove
 (`!f g s.
        (!x. x IN s ==> f x = g x) /\ f uniformly_continuous_on s
        ==> g uniformly_continuous_on s`,
  SIMP_TAC[uniformly_continuous_on; IMP_CONJ]);;

let CONTINUOUS_ON_SING = prove
 (`!f:real^M->real^N a. f continuous_on {a}`,
  SIMP_TAC[continuous_on; IN_SING; FORALL_UNWIND_THM2; DIST_REFL] THEN
  MESON_TAC[]);;

let CONTINUOUS_ON_EMPTY = prove
 (`!f:real^M->real^N. f continuous_on {}`,
  MESON_TAC[CONTINUOUS_ON_SING; EMPTY_SUBSET; CONTINUOUS_ON_SUBSET]);;

let CONTINUOUS_ON_NO_LIMPT = prove
 (`!f:real^M->real^N s.
     ~(?x. x limit_point_of s) ==> f continuous_on s`,
  REWRITE_TAC[continuous_on; LIMPT_APPROACHABLE] THEN MESON_TAC[DIST_REFL]);;

let CONTINUOUS_ON_FINITE = prove
 (`!f:real^M->real^N s. FINITE s ==> f continuous_on s`,
  MESON_TAC[CONTINUOUS_ON_NO_LIMPT; LIMIT_POINT_FINITE]);;

let CONTRACTION_IMP_CONTINUOUS_ON = prove
 (`!f:real^M->real^N.
        (!x y. x IN s /\ y IN s ==> dist(f x,f y) <= dist(x,y))
        ==> f continuous_on s`,
  SIMP_TAC[continuous_on] THEN MESON_TAC[REAL_LET_TRANS]);;

let ISOMETRY_ON_IMP_CONTINUOUS_ON = prove
 (`!f:real^M->real^N.
        (!x y. x IN s /\ y IN s ==> dist(f x,f y) = dist(x,y))
        ==> f continuous_on s`,
  SIMP_TAC[CONTRACTION_IMP_CONTINUOUS_ON; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Characterization of various kinds of continuity in terms of sequences.    *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_SEQUENTIALLY = prove
 (`!f a:real^N.
        f continuous (at a within s) <=>
                !x. (!n. x(n) IN s) /\ (x --> a) sequentially
                     ==> ((f o x) --> f(a)) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_within] THEN EQ_TAC THENL
   [REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&1 / (&n + &1)`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_POS; ARITH;
       REAL_ARITH `&0 <= n ==> &0 < n + &1`; NOT_FORALL_THM; SKOLEM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[NOT_IMP; FORALL_AND_THM] THEN
  X_GEN_TAC `y:num->real^N` THEN REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[LE_REFL]] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FORALL_POS_MONO_1 THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `&1 / (&m + &1)` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_INV2; real_div; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
               REAL_POS; REAL_MUL_LID; REAL_LE_RADD; REAL_OF_NUM_LE]);;

let CONTINUOUS_AT_SEQUENTIALLY = prove
 (`!f a:real^N.
        f continuous (at a) <=>
              !x. (x --> a) sequentially
                  ==> ((f o x) --> f(a)) sequentially`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_WITHIN_SEQUENTIALLY; IN_UNIV]);;

let CONTINUOUS_ON_SEQUENTIALLY = prove
 (`!f s:real^N->bool.
        f continuous_on s <=>
              !x a. a IN s /\ (!n. x(n) IN s) /\ (x --> a) sequentially
                    ==> ((f o x) --> f(a)) sequentially`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              CONTINUOUS_WITHIN_SEQUENTIALLY] THEN MESON_TAC[]);;

let UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY = prove
 (`!f s:real^N->bool.
        f uniformly_continuous_on s <=>
              !x y. (!n. x(n) IN s) /\ (!n. y(n) IN s) /\
                    ((\n. x(n) - y(n)) --> vec 0) sequentially
                    ==> ((\n. f(x(n)) - f(y(n))) --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[uniformly_continuous_on] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; dist; VECTOR_SUB_RZERO] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&1 / (&n + &1)`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_POS; ARITH;
       REAL_ARITH `&0 <= n ==> &0 < n + &1`; NOT_FORALL_THM; SKOLEM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:num->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:num->real^N` THEN
  REWRITE_TAC[NOT_IMP; FORALL_AND_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FORALL_POS_MONO_1 THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&1 / (&m + &1)` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_INV2; real_div; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
                 REAL_POS; REAL_MUL_LID; REAL_LE_RADD; REAL_OF_NUM_LE];
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `\x:num. x` THEN ASM_REWRITE_TAC[LE_REFL]]);;

let LIM_CONTINUOUS_FUNCTION = prove
 (`!f net g l.
        f continuous (at l) /\ (g --> l) net ==> ((\x. f(g x)) --> f l) net`,
  REWRITE_TAC[tendsto; continuous_at; eventually] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Combination results for pointwise continuity.                             *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_CONST = prove
 (`!net c. (\x. c) continuous net`,
  REWRITE_TAC[continuous; LIM_CONST]);;

let CONTINUOUS_CMUL = prove
 (`!f c net. f continuous net ==> (\x. c % f(x)) continuous net`,
  REWRITE_TAC[continuous; LIM_CMUL]);;

let CONTINUOUS_NEG = prove
 (`!f net. f continuous net ==> (\x. --(f x)) continuous net`,
  REWRITE_TAC[continuous; LIM_NEG]);;

let CONTINUOUS_ADD = prove
 (`!f g net. f continuous net /\ g continuous net
           ==> (\x. f(x) + g(x)) continuous net`,
  REWRITE_TAC[continuous; LIM_ADD]);;

let CONTINUOUS_SUB = prove
 (`!f g net. f continuous net /\ g continuous net
           ==> (\x. f(x) - g(x)) continuous net`,
  REWRITE_TAC[continuous; LIM_SUB]);;

let CONTINUOUS_ABS = prove
 (`!(f:A->real^N) net.
        f continuous net
        ==> (\x. (lambda i. abs(f(x)$i)):real^N) continuous net`,
  REWRITE_TAC[continuous; LIM_ABS]);;

let CONTINUOUS_MAX = prove
 (`!(f:A->real^N) (g:A->real^N) net.
        f continuous net /\ g continuous net
        ==> (\x. (lambda i. max (f(x)$i) (g(x)$i)):real^N) continuous net`,
  REWRITE_TAC[continuous; LIM_MAX]);;

let CONTINUOUS_MIN = prove
 (`!(f:A->real^N) (g:A->real^N) net.
        f continuous net /\ g continuous net
        ==> (\x. (lambda i. min (f(x)$i) (g(x)$i)):real^N) continuous net`,
  REWRITE_TAC[continuous; LIM_MIN]);;

let CONTINUOUS_VSUM = prove
 (`!net f s. FINITE s /\ (!a. a IN s ==> (f a) continuous net)
             ==> (\x. vsum s (\a. f a x)) continuous net`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; VSUM_CLAUSES;
           CONTINUOUS_CONST; CONTINUOUS_ADD; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Same thing for setwise continuity.                                        *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CONST = prove
 (`!s c. (\x. c) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_CONST]);;

let CONTINUOUS_ON_CMUL = prove
 (`!f c s. f continuous_on s ==> (\x. c % f(x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_CMUL]);;

let CONTINUOUS_ON_NEG = prove
 (`!f s. f continuous_on s
         ==> (\x. --(f x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_NEG]);;

let CONTINUOUS_ON_ADD = prove
 (`!f g s. f continuous_on s /\ g continuous_on s
           ==> (\x. f(x) + g(x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_ADD]);;

let CONTINUOUS_ON_SUB = prove
 (`!f g s. f continuous_on s /\ g continuous_on s
           ==> (\x. f(x) - g(x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_SUB]);;

let CONTINUOUS_ON_ABS = prove
 (`!f:real^M->real^N s.
        f continuous_on s
        ==> (\x. (lambda i. abs(f(x)$i)):real^N) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_ABS]);;

let CONTINUOUS_ON_MAX = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. (lambda i. max (f(x)$i) (g(x)$i)):real^N)
            continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_MAX]);;

let CONTINUOUS_ON_MIN = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. (lambda i. min (f(x)$i) (g(x)$i)):real^N)
            continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_MIN]);;

let CONTINUOUS_ON_VSUM = prove
 (`!t f s. FINITE s /\ (!a. a IN s ==> (f a) continuous_on t)
             ==> (\x. vsum s (\a. f a x)) continuous_on t`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_VSUM]);;

(* ------------------------------------------------------------------------- *)
(* Same thing for uniform continuity, using sequential formulations.         *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONTINUOUS_ON_CONST = prove
 (`!s c. (\x. c) uniformly_continuous_on s`,
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY; o_DEF;
              VECTOR_SUB_REFL; LIM_CONST]);;

let LINEAR_UNIFORMLY_CONTINUOUS_ON = prove
 (`!f:real^M->real^N s. linear f ==> f uniformly_continuous_on s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[uniformly_continuous_on; dist; GSYM LINEAR_SUB] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o
        MATCH_MP LINEAR_BOUNDED_POS) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `e / B:real` THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `B * norm(y - x:real^M)` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_LT_RDIV_EQ; REAL_MUL_SYM]);;

let UNIFORMLY_CONTINUOUS_ON_COMPOSE = prove
 (`!f g s. f uniformly_continuous_on s /\
           g uniformly_continuous_on (IMAGE f s)
           ==> (g o f) uniformly_continuous_on s`,
  let lemma = prove
   (`(!y. ((?x. (y = f x) /\ P x) /\ Q y ==> R y)) <=>
     (!x. P x /\ Q (f x) ==> R (f x))`,
    MESON_TAC[]) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[uniformly_continuous_on; o_THM; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[lemma] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[lemma] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `e:real` THEN ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let BILINEAR_UNIFORMLY_CONTINUOUS_ON_COMPOSE = prove
 (`!f:real^M->real^N g (h:real^N->real^P->real^Q) s.
           f uniformly_continuous_on s /\ g uniformly_continuous_on s /\
           bilinear h /\ bounded(IMAGE f s) /\ bounded(IMAGE g s)
           ==> (\x. h (f x) (g x)) uniformly_continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[uniformly_continuous_on; dist] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!a b c d. (h:real^N->real^P->real^Q) a b - h c d =
              h (a - c) b + h c (b - d)`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP BILINEAR_LSUB th]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP BILINEAR_RSUB th]) THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o
    MATCH_MP BILINEAR_BOUNDED_POS) THEN
  UNDISCH_TAC `bounded(IMAGE (g:real^M->real^P) s)` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(g:real^M->real^P) uniformly_continuous_on s` THEN
  UNDISCH_TAC `(f:real^M->real^N) uniformly_continuous_on s` THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2 / &2 / B / B2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; dist] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2 / &2 / B / B1`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; dist] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `y:real^M`])) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
   `B * e / &2 / &2 / B / B2 * B2 + B * B1 * e / &2 / &2 / B / B1` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(x) <= a /\ norm(y) <= b ==> norm(x + y:real^N) <= a + b`) THEN
    CONJ_TAC THEN
    FIRST_X_ASSUM(fun th -> W(MP_TAC o PART_MATCH lhand th o lhand o snd)) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
    ASM_REAL_ARITH_TAC]);;

let UNIFORMLY_CONTINUOUS_ON_MUL = prove
 (`!f g:real^M->real^N s.
        (lift o f) uniformly_continuous_on s /\ g uniformly_continuous_on s /\
        bounded(IMAGE (lift o f) s) /\ bounded(IMAGE g s)
        ==>  (\x. f x % g x) uniformly_continuous_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`lift o (f:real^M->real)`; `g:real^M->real^N`;
    `\c (v:real^N). drop c % v`; `s:real^M->bool`]
        BILINEAR_UNIFORMLY_CONTINUOUS_ON_COMPOSE) THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[bilinear; linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC);;

let UNIFORMLY_CONTINUOUS_ON_CMUL = prove
 (`!f c s. f uniformly_continuous_on s
           ==> (\x. c % f(x)) uniformly_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_CMUL) THEN
  ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_RZERO]);;

let UNIFORMLY_CONTINUOUS_ON_VMUL = prove
 (`!s:real^M->bool c v:real^N.
      (lift o c) uniformly_continuous_on s
      ==> (\x. c x % v) uniformly_continuous_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o ISPEC `\x. (drop x % v:real^N)` o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] UNIFORMLY_CONTINUOUS_ON_COMPOSE)) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC LINEAR_UNIFORMLY_CONTINUOUS_ON THEN
  MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]);;

let UNIFORMLY_CONTINUOUS_ON_NEG = prove
 (`!f s. f uniformly_continuous_on s
         ==> (\x. --(f x)) uniformly_continuous_on s`,
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_CMUL]);;

let UNIFORMLY_CONTINUOUS_ON_ADD = prove
 (`!f g s. f uniformly_continuous_on s /\ g uniformly_continuous_on s
           ==> (\x. f(x) + g(x)) uniformly_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD) THEN
  MATCH_MP_TAC EQ_IMP THEN
  REWRITE_TAC[VECTOR_ADD_LID] THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC);;

let UNIFORMLY_CONTINUOUS_ON_SUB = prove
 (`!f g s. f uniformly_continuous_on s /\ g uniformly_continuous_on s
           ==> (\x. f(x) - g(x)) uniformly_continuous_on s`,
  REWRITE_TAC[VECTOR_SUB] THEN
  SIMP_TAC[UNIFORMLY_CONTINUOUS_ON_NEG; UNIFORMLY_CONTINUOUS_ON_ADD]);;

let UNIFORMLY_CONTINUOUS_ON_VSUM = prove
 (`!t f s. FINITE s /\ (!a. a IN s ==> (f a) uniformly_continuous_on t)
             ==> (\x. vsum s (\a. f a x)) uniformly_continuous_on t`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; VSUM_CLAUSES;
       UNIFORMLY_CONTINUOUS_ON_CONST; UNIFORMLY_CONTINUOUS_ON_ADD; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Identity function is continuous in every sense.                           *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_ID = prove
 (`!a s. (\x. x) continuous (at a within s)`,
  REWRITE_TAC[continuous_within] THEN MESON_TAC[]);;

let CONTINUOUS_AT_ID = prove
 (`!a. (\x. x) continuous (at a)`,
  REWRITE_TAC[continuous_at] THEN MESON_TAC[]);;

let CONTINUOUS_ON_ID = prove
 (`!s. (\x. x) continuous_on s`,
  REWRITE_TAC[continuous_on] THEN MESON_TAC[]);;

let UNIFORMLY_CONTINUOUS_ON_ID = prove
 (`!s. (\x. x) uniformly_continuous_on s`,
  REWRITE_TAC[uniformly_continuous_on] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of all kinds is preserved under composition.                   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_COMPOSE = prove
 (`!f g x s. f continuous (at x within s) /\
             g continuous (at (f x) within IMAGE f s)
             ==> (g o f) continuous (at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_within; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let CONTINUOUS_AT_COMPOSE = prove
 (`!f g x. f continuous (at x) /\ g continuous (at (f x))
           ==> (g o f) continuous (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MESON_TAC[CONTINUOUS_WITHIN_COMPOSE; IN_IMAGE; CONTINUOUS_WITHIN_SUBSET;
            SUBSET_UNIV; IN_UNIV]);;

let CONTINUOUS_ON_COMPOSE = prove
 (`!f g s. f continuous_on s /\ g continuous_on (IMAGE f s)
           ==> (g o f) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  MESON_TAC[IN_IMAGE; CONTINUOUS_WITHIN_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Continuity in terms of open preimages.                                    *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_OPEN = prove
 (`!f:real^M->real^N x u.
     f continuous (at x within u) <=>
        !t. open t /\ f(x) IN t
            ==> ?s. open s /\ x IN s /\
                    !x'. x' IN s /\ x' IN u ==> f(x') IN t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_within] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `t:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [open_def] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN
    ASM_MESON_TAC[IN_BALL; DIST_SYM; OPEN_BALL; CENTRE_IN_BALL; DIST_SYM];
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ball((f:real^M->real^N) x,e)`) THEN
    ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    MESON_TAC[open_def; IN_BALL; REAL_LT_TRANS; DIST_SYM]]);;

let CONTINUOUS_AT_OPEN = prove
 (`!f:real^M->real^N x.
     f continuous (at x) <=>
        !t. open t /\ f(x) IN t
            ==> ?s. open s /\ x IN s /\
                    !x'. x' IN s ==> f(x') IN t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_at] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `t:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [open_def] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN
    ASM_MESON_TAC[IN_BALL; DIST_SYM; OPEN_BALL; CENTRE_IN_BALL];
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ball((f:real^M->real^N) x,e)`) THEN
    ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    MESON_TAC[open_def; IN_BALL; REAL_LT_TRANS; DIST_SYM]]);;

let CONTINUOUS_ON_OPEN_GEN = prove
 (`!f:real^M->real^N s t.
    IMAGE f s SUBSET t
    ==> (f continuous_on s <=>
         !u. open_in (subtopology euclidean t) u
             ==> open_in (subtopology euclidean s) {x | x IN s /\ f x IN u})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_on] THEN EQ_TAC THENL
   [REWRITE_TAC[open_in; SUBSET; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIST_REFL]; ALL_TAC] THEN
    X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN ASM SET_TAC[];
    DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o
      SPEC `ball((f:real^M->real^N) x,e) INTER t`) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_OPEN; INTER_COMM; OPEN_BALL]; ALL_TAC] THEN
    REWRITE_TAC[open_in; SUBSET; IN_INTER; IN_ELIM_THM; IN_BALL; IN_IMAGE] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_MESON_TAC[DIST_REFL; DIST_SYM]]);;

let CONTINUOUS_ON_OPEN = prove
 (`!f:real^M->real^N s.
      f continuous_on s <=>
        !t. open_in (subtopology euclidean (IMAGE f s)) t
            ==> open_in (subtopology euclidean s) {x | x IN s /\ f(x) IN t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_OPEN_GEN THEN
  REWRITE_TAC[SUBSET_REFL]);;

let CONTINUOUS_OPEN_IN_PREIMAGE_GEN = prove
 (`!f:real^M->real^N s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        open_in (subtopology euclidean t) u
        ==> open_in (subtopology euclidean s) {x | x IN s /\ f x IN u}`,
  MESON_TAC[CONTINUOUS_ON_OPEN_GEN]);;

let CONTINUOUS_ON_IMP_OPEN_IN = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\
        open_in (subtopology euclidean (IMAGE f s)) t
        ==> open_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`,
  MESON_TAC[CONTINUOUS_ON_OPEN]);;

(* ------------------------------------------------------------------------- *)
(* Similarly in terms of closed sets.                                        *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CLOSED_GEN = prove
 (`!f:real^M->real^N s t.
    IMAGE f s SUBSET t
    ==> (f continuous_on s <=>
         !u. closed_in (subtopology euclidean t) u
             ==> closed_in (subtopology euclidean s)
                           {x | x IN s /\ f x IN u})`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th ->
    ONCE_REWRITE_TAC[MATCH_MP CONTINUOUS_ON_OPEN_GEN th]) THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `u:real^N->bool` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t DIFF u:real^N->bool`) THENL
   [REWRITE_TAC[closed_in]; REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ]] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let CONTINUOUS_ON_CLOSED = prove
 (`!f:real^M->real^N s.
      f continuous_on s <=>
        !t. closed_in (subtopology euclidean (IMAGE f s)) t
            ==> closed_in (subtopology euclidean s) {x | x IN s /\ f(x) IN t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_CLOSED_GEN THEN
  REWRITE_TAC[SUBSET_REFL]);;

let CONTINUOUS_CLOSED_IN_PREIMAGE_GEN = prove
 (`!f:real^M->real^N s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        closed_in (subtopology euclidean t) u
        ==> closed_in (subtopology euclidean s) {x | x IN s /\ f x IN u}`,
  MESON_TAC[CONTINUOUS_ON_CLOSED_GEN]);;

let CONTINUOUS_ON_IMP_CLOSED_IN = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\
        closed_in (subtopology euclidean (IMAGE f s)) t
        ==> closed_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`,
  MESON_TAC[CONTINUOUS_ON_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* Half-global and completely global cases.                                  *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_OPEN_IN_PREIMAGE = prove
 (`!f s t.
         f continuous_on s /\ open t
         ==> open_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE
   `x IN s /\ f x IN t <=> x IN s /\ f x IN (t INTER IMAGE f s)`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONTINUOUS_ON_OPEN]) THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
  ASM_REWRITE_TAC[]);;

let CONTINUOUS_CLOSED_IN_PREIMAGE = prove
 (`!f s t.
         f continuous_on s /\ closed t
         ==> closed_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE
   `x IN s /\ f x IN t <=> x IN s /\ f x IN (t INTER IMAGE f s)`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONTINUOUS_ON_CLOSED]) THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN
  ASM_REWRITE_TAC[]);;

let CONTINUOUS_OPEN_PREIMAGE = prove
 (`!f:real^M->real^N s t.
     f continuous_on s /\ open s /\ open t
     ==> open {x | x IN s /\ f(x) IN t}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_ON_OPEN]) THEN
  REWRITE_TAC [OPEN_IN_OPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (f:real^M->real^N) s INTER t`) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    SUBGOAL_THEN `{x | x IN s /\ (f:real^M->real^N) x IN t} =
                 s INTER t'` SUBST1_TAC THENL
    [ASM SET_TAC []; ASM_MESON_TAC [OPEN_INTER]]]);;

let CONTINUOUS_CLOSED_PREIMAGE = prove
 (`!f:real^M->real^N s t.
     f continuous_on s /\ closed s /\ closed t
     ==> closed {x | x IN s /\ f(x) IN t}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_ON_CLOSED]) THEN
  REWRITE_TAC [CLOSED_IN_CLOSED] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (f:real^M->real^N) s INTER t`) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    SUBGOAL_THEN `{x | x IN s /\ (f:real^M->real^N) x IN t} =
                 s INTER t'` SUBST1_TAC THENL
    [ASM SET_TAC []; ASM_MESON_TAC [CLOSED_INTER]]]);;

let CONTINUOUS_OPEN_PREIMAGE_UNIV = prove
 (`!f:real^M->real^N s.
        (!x. f continuous (at x)) /\ open s ==> open {x | f(x) IN s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:real^M->real^N`; `(:real^M)`; `s:real^N->bool`]
    CONTINUOUS_OPEN_PREIMAGE) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; CONTINUOUS_AT_IMP_CONTINUOUS_ON]);;

let CONTINUOUS_CLOSED_PREIMAGE_UNIV = prove
 (`!f:real^M->real^N s.
        (!x. f continuous (at x)) /\ closed s ==> closed {x | f(x) IN s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:real^M->real^N`; `(:real^M)`; `s:real^N->bool`]
    CONTINUOUS_CLOSED_PREIMAGE) THEN
  ASM_SIMP_TAC[CLOSED_UNIV; IN_UNIV; CONTINUOUS_AT_IMP_CONTINUOUS_ON]);;

let CONTINUOUS_OPEN_IN_PREIMAGE_EQ = prove
 (`!f:real^M->real^N s.
    f continuous_on s <=>
    !t. open t ==> open_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[CONTINUOUS_OPEN_IN_PREIMAGE] THEN
  REWRITE_TAC[CONTINUOUS_ON_OPEN] THEN DISCH_TAC THEN
  X_GEN_TAC `t:real^N->bool` THEN GEN_REWRITE_TAC LAND_CONV [OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]);;

let CONTINUOUS_CLOSED_IN_PREIMAGE_EQ = prove
 (`!f:real^M->real^N s.
    f continuous_on s <=>
    !t. closed t
        ==> closed_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[CONTINUOUS_CLOSED_IN_PREIMAGE] THEN
  REWRITE_TAC[CONTINUOUS_ON_CLOSED] THEN DISCH_TAC THEN
  X_GEN_TAC `t:real^N->bool` THEN
  GEN_REWRITE_TAC LAND_CONV [CLOSED_IN_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Linear functions are (uniformly) continuous on any set.                   *)
(* ------------------------------------------------------------------------- *)

let LINEAR_LIM_0 = prove
 (`!f. linear f ==> (f --> vec 0) (at (vec 0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_AT] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LINEAR_BOUNDED_POS) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `e / B` THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN REWRITE_TAC[dist; VECTOR_SUB_RZERO] THEN
  ASM_MESON_TAC[REAL_MUL_SYM; REAL_LET_TRANS; REAL_LT_RDIV_EQ]);;

let LINEAR_CONTINUOUS_AT = prove
 (`!f:real^M->real^N a. linear f ==> f continuous (at a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x. (f:real^M->real^N) (a + x) - f(a)` LINEAR_LIM_0) THEN
  ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN SIMP_TAC[linear] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIM_NULL; CONTINUOUS_AT] THEN
  GEN_REWRITE_TAC RAND_CONV [LIM_AT_ZERO] THEN SIMP_TAC[]);;

let LINEAR_CONTINUOUS_WITHIN = prove
 (`!f:real^M->real^N s x. linear f ==> f continuous (at x within s)`,
  SIMP_TAC[CONTINUOUS_AT_WITHIN; LINEAR_CONTINUOUS_AT]);;

let LINEAR_CONTINUOUS_ON = prove
 (`!f:real^M->real^N s. linear f ==> f continuous_on s`,
  MESON_TAC[LINEAR_CONTINUOUS_AT; CONTINUOUS_AT_IMP_CONTINUOUS_ON]);;

let LINEAR_CONTINUOUS_COMPOSE = prove
 (`!net f:A->real^N g:real^N->real^P.
        f continuous net /\ linear g ==> (\x. g(f x)) continuous net`,
  REWRITE_TAC[continuous; LIM_LINEAR]);;

let LINEAR_CONTINUOUS_ON_COMPOSE = prove
 (`!f:real^M->real^N g:real^N->real^P s.
        f continuous_on s /\ linear g ==> (\x. g(f x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
           LINEAR_CONTINUOUS_COMPOSE]);;

let CONTINUOUS_LIFT_COMPONENT_COMPOSE = prove
 (`!net f:A->real^N i. f continuous net ==> (\x. lift(f x$i)) continuous net`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `linear(\x:real^N. lift (x$i))` MP_TAC THENL
   [REWRITE_TAC[LINEAR_LIFT_COMPONENT]; REWRITE_TAC[GSYM IMP_CONJ_ALT]] THEN
  REWRITE_TAC[LINEAR_CONTINUOUS_COMPOSE]);;

let CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE = prove
 (`!f:real^M->real^N s.
        f continuous_on s
        ==> (\x. lift (f x$i)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
           CONTINUOUS_LIFT_COMPONENT_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Also bilinear functions, in composition form.                             *)
(* ------------------------------------------------------------------------- *)

let BILINEAR_CONTINUOUS_COMPOSE = prove
 (`!net f:A->real^M g:A->real^N h:real^M->real^N->real^P.
        f continuous net /\ g continuous net /\ bilinear h
        ==> (\x. h (f x) (g x)) continuous net`,
  REWRITE_TAC[continuous; LIM_BILINEAR]);;

let BILINEAR_CONTINUOUS_ON_COMPOSE = prove
 (`!f g h s. f continuous_on s /\ g continuous_on s /\ bilinear h
             ==> (\x. h (f x) (g x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
           BILINEAR_CONTINUOUS_COMPOSE]);;

let BILINEAR_DOT = prove
 (`bilinear (\x y:real^N. lift(x dot y))`,
  REWRITE_TAC[bilinear; linear; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  REWRITE_TAC[LIFT_ADD; LIFT_CMUL]);;

let CONTINUOUS_LIFT_DOT2 = prove
 (`!net f g:A->real^N.
        f continuous net /\ g continuous net
        ==> (\x. lift(f x dot g x)) continuous net`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (MATCH_MP (REWRITE_RULE
   [TAUT `p /\ q /\ r ==> s <=> r ==> p /\ q ==> s`]
  BILINEAR_CONTINUOUS_COMPOSE) BILINEAR_DOT)) THEN REWRITE_TAC[]);;

let CONTINUOUS_ON_LIFT_DOT2 = prove
 (`!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. lift(f x dot g x)) continuous_on s`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (MATCH_MP (REWRITE_RULE
   [TAUT `p /\ q /\ r ==> s <=> r ==> p /\ q ==> s`]
  BILINEAR_CONTINUOUS_ON_COMPOSE) BILINEAR_DOT)) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Preservation of compactness and connectedness under continuous function.  *)
(* ------------------------------------------------------------------------- *)

let COMPACT_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ compact s ==> compact(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_on; compact] THEN
  STRIP_TAC THEN X_GEN_TAC `y:num->real^N` THEN
  REWRITE_TAC[IN_IMAGE; SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->real^M` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num->real^M`) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `r:num->num` THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:real^M->real^N) l` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:real^M`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[o_THM] THEN
  ASM_MESON_TAC[]);;

let COMPACT_TRANSLATION = prove
 (`!s a:real^N. compact s ==> compact (IMAGE (\x. a + x) s)`,
  SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; CONTINUOUS_ON_ADD;
           CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]);;

let COMPACT_TRANSLATION_EQ = prove
 (`!a s. compact (IMAGE (\x:real^N. a + x) s) <=> compact s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[COMPACT_TRANSLATION] THEN
  DISCH_THEN(MP_TAC o ISPEC `--a:real^N` o MATCH_MP COMPACT_TRANSLATION) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID;
              VECTOR_ARITH `--a + a + x:real^N = x`]);;

add_translation_invariants [COMPACT_TRANSLATION_EQ];;

let COMPACT_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s. compact s /\ linear f ==> compact(IMAGE f s)`,
  SIMP_TAC[LINEAR_CONTINUOUS_ON; COMPACT_CONTINUOUS_IMAGE]);;

let COMPACT_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (compact (IMAGE f s) <=> compact s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE COMPACT_LINEAR_IMAGE));;

add_linear_invariants [COMPACT_LINEAR_IMAGE_EQ];;

let CONNECTED_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ connected s ==> connected(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_ON_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[CONNECTED_CLOPEN; NOT_FORALL_THM; NOT_IMP; DE_MORGAN_THM] THEN
  REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `t:real^N->bool` th) THEN
    MP_TAC(SPEC `IMAGE (f:real^M->real^N) s DIFF t` th)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{x | x IN s /\ (f:real^M->real^N) x IN IMAGE f s DIFF t} =
                s DIFF {x | x IN s /\ f x IN t}`
  SUBST1_TAC THENL
   [UNDISCH_TAC `t SUBSET IMAGE (f:real^M->real^N) s` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF; IN_ELIM_THM; SUBSET] THEN
    MESON_TAC[];
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `{x | x IN s /\ (f:real^M->real^N) x IN t}` THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[IN_IMAGE; SUBSET; IN_ELIM_THM; NOT_IN_EMPTY; EXTENSION] THEN
    MESON_TAC[]]);;

let CONNECTED_TRANSLATION = prove
 (`!a s. connected s ==> connected (IMAGE (\x:real^N. a + x) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]);;

let CONNECTED_TRANSLATION_EQ = prove
 (`!a s. connected (IMAGE (\x:real^N. a + x) s) <=> connected s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[CONNECTED_TRANSLATION] THEN
  DISCH_THEN(MP_TAC o ISPEC `--a:real^N` o MATCH_MP CONNECTED_TRANSLATION) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID;
              VECTOR_ARITH `--a + a + x:real^N = x`]);;

add_translation_invariants [CONNECTED_TRANSLATION_EQ];;

let CONNECTED_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s. connected s /\ linear f ==> connected(IMAGE f s)`,
  SIMP_TAC[LINEAR_CONTINUOUS_ON; CONNECTED_CONTINUOUS_IMAGE]);;

let CONNECTED_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (connected (IMAGE f s) <=> connected s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE CONNECTED_LINEAR_IMAGE));;

add_linear_invariants [CONNECTED_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Preservation properties for pasted sets (Cartesian products).             *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        bounded (s PCROSS t) <=>
        s = {} \/ t = {} \/ bounded s /\ bounded t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS] THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{f x y |x,y| F} = {}`; BOUNDED_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[bounded; FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
  ASM_MESON_TAC[NORM_LE_PASTECART; REAL_LE_TRANS; NORM_PASTECART_LE;
                REAL_LE_ADD2]);;

let BOUNDED_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
     bounded s /\ bounded t ==> bounded (s PCROSS t)`,
  SIMP_TAC[BOUNDED_PCROSS_EQ]);;

let CLOSED_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        closed (s PCROSS t) <=>
        s = {} \/ t = {} \/ closed s /\ closed t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS] THEN MAP_EVERY ASM_CASES_TAC
   [`s:real^M->bool = {}`; `t:real^N->bool = {}`] THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; CLOSED_EMPTY; SET_RULE
   `{f x y |x,y| F} = {}`] THEN
  REWRITE_TAC[CLOSED_SEQUENTIAL_LIMITS; LIM_SEQUENTIALLY] THEN
  REWRITE_TAC[FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
  REWRITE_TAC[IN_ELIM_THM; SKOLEM_THM; FORALL_AND_THM] THEN
  ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  SIMP_TAC[TAUT `((p /\ q) /\ r) /\ s ==> t <=> r ==> p /\ q /\ s ==> t`] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(!a b c d e. P a b c d e) <=> (!d e b c a. P a b c d e)`] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN EQ_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`; FORALL_AND_THM] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [ALL_TAC; GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM]] THEN
    MATCH_MP_TAC MONO_FORALL THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC(MESON[]
     `(?x. P x (\n. x)) ==> (?s x. P x s)`) THEN
    ASM_MESON_TAC[DIST_PASTECART_CANCEL];
    ONCE_REWRITE_TAC[MESON[]
     `(!x l. P x l) /\ (!y m. Q y m) <=> (!x y l m. P x l /\ Q y m)`] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REWRITE_TAC[dist; PASTECART_SUB] THEN
    ASM_MESON_TAC[NORM_LE_PASTECART; REAL_LET_TRANS]]);;

let CLOSED_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
     closed s /\ closed t ==> closed (s PCROSS t)`,
  SIMP_TAC[CLOSED_PCROSS_EQ]);;

let COMPACT_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        compact (s PCROSS t) <=>
        s = {} \/ t = {} \/ compact s /\ compact t`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_PCROSS_EQ;
              BOUNDED_PCROSS_EQ] THEN
  MESON_TAC[]);;

let COMPACT_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
     compact s /\ compact t ==> compact (s PCROSS t)`,
  SIMP_TAC[COMPACT_PCROSS_EQ]);;

let OPEN_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        open (s PCROSS t) <=>
        s = {} \/ t = {} \/ open s /\ open t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS] THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{f x y |x,y| F} = {}`; OPEN_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  EQ_TAC THENL
   [REWRITE_TAC[open_def; FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
    ASM_MESON_TAC[DIST_PASTECART_CANCEL];
    REWRITE_TAC[OPEN_CLOSED] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `UNIV DIFF {pastecart x y | x IN s /\ y IN t} =
      {pastecart x y | x IN ((:real^M) DIFF s) /\ y IN (:real^N)} UNION
      {pastecart x y | x IN (:real^M) /\ y IN ((:real^N) DIFF t)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; FORALL_PASTECART; IN_UNIV] THEN
      REWRITE_TAC[IN_ELIM_THM; PASTECART_EQ; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN MESON_TAC[];
      SIMP_TAC[GSYM PCROSS] THEN MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC CLOSED_PCROSS THEN ASM_REWRITE_TAC[CLOSED_UNIV]]]);;

let OPEN_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        open s /\ open t ==> open (s PCROSS t)`,
  SIMP_TAC[OPEN_PCROSS_EQ]);;

let OPEN_IN_PCROSS = prove
 (`!s s':real^M->bool t t':real^N->bool.
        open_in (subtopology euclidean s) s' /\
        open_in (subtopology euclidean t) t'
        ==> open_in (subtopology euclidean (s PCROSS t)) (s' PCROSS t')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s'':real^M->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `t'':real^N->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(s'':real^M->bool) PCROSS (t'':real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; EXTENSION; FORALL_PASTECART] THEN
  REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS] THEN ASM SET_TAC[]);;

let PASTECART_IN_INTERIOR_SUBTOPOLOGY = prove
 (`!s t u x:real^M y:real^N.
     pastecart x y IN u /\ open_in (subtopology euclidean (s PCROSS t)) u
     ==> ?v w. open_in (subtopology euclidean s) v /\ x IN v /\
               open_in (subtopology euclidean t) w /\ y IN w /\
               (v PCROSS w) SUBSET u`,
  REWRITE_TAC[open_in; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(x:real^M,e / &2) INTER s` THEN
  EXISTS_TAC `ball(y:real^N,e / &2) INTER t` THEN
  SUBGOAL_THEN `(x:real^M) IN s /\ (y:real^N) IN t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; PASTECART_IN_PCROSS]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTER_SUBSET; IN_INTER; CENTRE_IN_BALL; REAL_HALF] THEN
  REWRITE_TAC[IN_BALL] THEN REPEAT(CONJ_TAC THENL
   [MESON_TAC[REAL_SUB_LT; NORM_ARITH
     `dist(x,y) < e /\ dist(z,y) < e - dist(x,y)
      ==> dist(x:real^N,z) < e`];
    ALL_TAC]) THEN
  REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  REWRITE_TAC[IN_BALL; IN_INTER] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[dist; PASTECART_SUB] THEN
  W(MP_TAC o PART_MATCH lhand NORM_PASTECART_LE o lhand o snd) THEN
  REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[DIST_SYM] dist)] THEN
  ASM_REAL_ARITH_TAC);;

let OPEN_IN_PCROSS_EQ = prove
 (`!s s':real^M->bool t t':real^N->bool.
        open_in (subtopology euclidean (s PCROSS t)) (s' PCROSS t') <=>
        s' = {} \/ t' = {} \/
        open_in (subtopology euclidean s) s' /\
        open_in (subtopology euclidean t) t'`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s':real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; OPEN_IN_EMPTY] THEN
  ASM_CASES_TAC `t':real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; OPEN_IN_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[OPEN_IN_PCROSS] THEN REPEAT STRIP_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    UNDISCH_TAC `~(t':real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`);
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `~(s':real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^M`)] THEN
   MP_TAC(ISPECL
     [`s:real^M->bool`; `t:real^N->bool`;
      `(s':real^M->bool) PCROSS (t':real^N->bool)`;
      `x:real^M`; `y:real^N`] PASTECART_IN_INTERIOR_SUBTOPOLOGY) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MESON_TAC[]);;

let INTERIOR_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        interior (s PCROSS t) = (interior s) PCROSS (interior t)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^N`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(:real^M)`; `(:real^N)`;
         `interior((s:real^M->bool) PCROSS (t:real^N->bool))`;
         `x:real^M`; `y:real^N`] PASTECART_IN_INTERIOR_SUBTOPOLOGY) THEN
    REWRITE_TAC[UNIV_PCROSS_UNIV; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[INTERIOR_SUBSET; SUBSET_TRANS]
      `s SUBSET interior t ==> s SUBSET t`)) THEN
    REWRITE_TAC[SUBSET_PCROSS] THEN
    ASM_MESON_TAC[NOT_IN_EMPTY; INTERIOR_MAXIMAL; SUBSET];
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERIOR; PCROSS_MONO; INTERIOR_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Quotient maps are occasionally useful.                                    *)
(* ------------------------------------------------------------------------- *)

let QUASICOMPACT_OPEN_CLOSED = prove
 (`!f:real^M->real^N s t.
    IMAGE f s SUBSET t
    ==> ((!u. u SUBSET t
              ==> (open_in (subtopology euclidean s)
                           {x | x IN s /\ f x IN u}
                   ==> open_in (subtopology euclidean t) u)) <=>
         (!u. u SUBSET t
              ==> (closed_in (subtopology euclidean s)
                             {x | x IN s /\ f x IN u}
                   ==> closed_in (subtopology euclidean t) u)))`,
  SIMP_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `u:real^N->bool` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t DIFF u:real^N->bool`) THEN
  ASM_SIMP_TAC[SET_RULE `u SUBSET t ==> t DIFF (t DIFF u) = u`] THEN
  (ANTS_TAC THENL [SET_TAC[]; REPEAT STRIP_TAC]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_RESTRICT] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
   `open_in top x ==> x = y ==> open_in top y`)) THEN
  ASM SET_TAC[]);;

let QUOTIENT_MAP_IMP_CONTINUOUS_OPEN = prove
 (`!f:real^M->real^N s t.
     IMAGE f s SUBSET t /\
     (!u. u SUBSET t
          ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
               open_in (subtopology euclidean t) u))
     ==> f continuous_on s`,
  MESON_TAC[OPEN_IN_IMP_SUBSET; CONTINUOUS_ON_OPEN_GEN]);;

let QUOTIENT_MAP_IMP_CONTINUOUS_CLOSED = prove
 (`!f:real^M->real^N s t.
     IMAGE f s SUBSET t /\
     (!u. u SUBSET t
          ==> (closed_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
               closed_in (subtopology euclidean t) u))
     ==> f continuous_on s`,
  MESON_TAC[CLOSED_IN_IMP_SUBSET; CONTINUOUS_ON_CLOSED_GEN]);;

let OPEN_MAP_IMP_QUOTIENT_MAP = prove
 (`!f:real^M->real^N s.
    f continuous_on s /\
    (!t. open_in (subtopology euclidean s) t
         ==> open_in (subtopology euclidean (IMAGE f s)) (IMAGE f t))
    ==> !t. t SUBSET IMAGE f s
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN t} <=>
                 open_in (subtopology euclidean (IMAGE f s)) t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN
     `t = IMAGE f {x | x IN s /\ (f:real^M->real^N) x IN t}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_ON_OPEN]) THEN
    ASM_SIMP_TAC[]]);;

let CLOSED_MAP_IMP_QUOTIENT_MAP = prove
 (`!f:real^M->real^N s.
    f continuous_on s /\
    (!t. closed_in (subtopology euclidean s) t
         ==> closed_in (subtopology euclidean (IMAGE f s)) (IMAGE f t))
    ==> !t. t SUBSET IMAGE f s
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN t} <=>
                 open_in (subtopology euclidean (IMAGE f s)) t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC
     `s DIFF {x | x IN s /\ (f:real^M->real^N) x IN t}`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_DIFF THEN
      ASM_SIMP_TAC[CLOSED_IN_SUBTOPOLOGY_REFL;
                   TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
      REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN ASM SET_TAC[]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_ON_OPEN]) THEN
    ASM_SIMP_TAC[]]);;

let CONTINUOUS_RIGHT_INVERSE_IMP_QUOTIENT_MAP = prove
 (`!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        (!y. y IN t ==> f(g y) = y)
        ==> (!u. u SUBSET t
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                 open_in (subtopology euclidean t) u))`,
  REWRITE_TAC[CONTINUOUS_ON_OPEN] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `(IMAGE (g:real^N->real^M) t)
       INTER
       {x | x IN s /\ (f:real^M->real^N) x IN u}`) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN MATCH_MP_TAC MONO_EXISTS THEN
      ASM SET_TAC[];
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]];
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `IMAGE (f:real^M->real^N) s = t`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM SET_TAC[]]);;

let CONTINUOUS_LEFT_INVERSE_IMP_QUOTIENT_MAP = prove
 (`!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        (!x. x IN s ==> g(f x) = x)
        ==> (!u. u SUBSET (IMAGE f s)
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                 open_in (subtopology euclidean (IMAGE f s)) u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_RIGHT_INVERSE_IMP_QUOTIENT_MAP THEN
  EXISTS_TAC `g:real^N->real^M` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let QUOTIENT_MAP_OPEN_CLOSED = prove
 (`!f:real^M->real^N s t.
    IMAGE f s SUBSET t
    ==> ((!u. u SUBSET t
              ==> (open_in (subtopology euclidean s)
                           {x | x IN s /\ f x IN u} <=>
                   open_in (subtopology euclidean t) u)) <=>
         (!u. u SUBSET t
              ==> (closed_in (subtopology euclidean s)
                             {x | x IN s /\ f x IN u} <=>
                   closed_in (subtopology euclidean t) u)))`,
  SIMP_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `u:real^N->bool` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t DIFF u:real^N->bool`) THEN
  ASM_SIMP_TAC[SET_RULE `u SUBSET t ==> t DIFF (t DIFF u) = u`] THEN
  (ANTS_TAC THENL [SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  REWRITE_TAC[SUBSET_RESTRICT] THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let CONTINUOUS_ON_COMPOSE_QUOTIENT = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
      IMAGE f s SUBSET t /\ IMAGE g t SUBSET u /\
      (!v. v SUBSET t
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN v} <=>
                open_in (subtopology euclidean t) v)) /\
      (g o f) continuous_on s
      ==> g continuous_on t`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CONTINUOUS_ON_OPEN_GEN th]) THEN
  SUBGOAL_THEN
   `IMAGE ((g:real^N->real^P) o (f:real^M->real^N)) s SUBSET u`
   (fun th -> REWRITE_TAC[MATCH_MP CONTINUOUS_ON_OPEN_GEN th])
  THENL [REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  X_GEN_TAC `v:real^P->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^P->bool`) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{x | x IN t /\ (g:real^N->real^P) x IN v}`) THEN
  ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
   `open_in top s ==> s = t ==> open_in top t`)) THEN
  ASM SET_TAC[]);;

let LIFT_TO_QUOTIENT_SPACE = prove
 (`!f:real^M->real^N h:real^M->real^P s t u.
        IMAGE f s = t /\
        (!v. v SUBSET t
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN v} <=>
                open_in (subtopology euclidean t) v)) /\
        h continuous_on s /\ IMAGE h s = u /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> h x = h y)
        ==> ?g. g continuous_on t /\ IMAGE g t = u /\
                !x. x IN s ==> h(x) = g(f x)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[FUNCTION_FACTORS_LEFT_GEN] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^P` THEN
  DISCH_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE_QUOTIENT THEN MAP_EVERY EXISTS_TAC
   [`f:real^M->real^N`; `s:real^M->bool`; `u:real^P->bool`] THEN
  ASM_SIMP_TAC[SUBSET_REFL] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    CONTINUOUS_ON_EQ)) THEN
  ASM_REWRITE_TAC[o_THM]);;

let QUOTIENT_MAP_COMPOSE = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        IMAGE f s SUBSET t /\
        (!v. v SUBSET t
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN v} <=>
                open_in (subtopology euclidean t) v)) /\
        (!v. v SUBSET u
           ==> (open_in (subtopology euclidean t) {x | x IN t /\ g x IN v} <=>
                open_in (subtopology euclidean u) v))
        ==> !v. v SUBSET u
                ==> (open_in (subtopology euclidean s)
                             {x | x IN s /\ (g o f) x IN v} <=>
                     open_in (subtopology euclidean u) v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN
   `{x | x IN s /\ (g:real^N->real^P) ((f:real^M->real^N) x) IN v} =
    {x | x IN s /\ f x IN {x | x IN t /\ g x IN v}}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[SUBSET_RESTRICT]]);;

let QUOTIENT_MAP_FROM_COMPOSITION = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        (!v. v SUBSET u
             ==> (open_in (subtopology euclidean s)
                          {x | x IN s /\ (g o f) x IN v} <=>
                  open_in (subtopology euclidean u) v))
        ==> !v. v SUBSET u
                ==> (open_in (subtopology euclidean t)
                              {x | x IN t /\ g x IN v} <=>
                     open_in (subtopology euclidean u) v)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^P->bool`) THEN
    ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `{x | x IN s /\ (g:real^N->real^P) ((f:real^M->real^N) x) IN v} =
      {x | x IN s /\ f x IN {x | x IN t /\ g x IN v}}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `u:real^P->bool` THEN ASM_REWRITE_TAC[]]);;

let QUOTIENT_MAP_FROM_SUBSET = prove
 (`!f:real^M->real^N s t u.
        f continuous_on t /\ IMAGE f t SUBSET u /\
        s SUBSET t /\ IMAGE f s = u /\
        (!v. v SUBSET u
             ==> (open_in (subtopology euclidean s)
                          {x | x IN s /\ f x IN v} <=>
                  open_in (subtopology euclidean u) v))
        ==> !v. v SUBSET u
                ==> (open_in (subtopology euclidean t)
                             {x | x IN t /\ f x IN v} <=>
                     open_in (subtopology euclidean u) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC QUOTIENT_MAP_FROM_COMPOSITION THEN
  MAP_EVERY EXISTS_TAC [`\x:real^M. x`; `s:real^M->bool`] THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID; o_THM]);;

let QUOTIENT_MAP_RESTRICT = prove
 (`!f:real^M->real^N s t c.
     IMAGE f s SUBSET t /\
     (!u. u SUBSET t
        ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
             open_in (subtopology euclidean t) u)) /\
     (open_in (subtopology euclidean t) c \/
      closed_in (subtopology euclidean t) c)
     ==> !u. u SUBSET c
             ==> (open_in (subtopology euclidean {x | x IN s /\ f x IN c})
                          {x | x IN {x | x IN s /\ f x IN c} /\ f x IN u} <=>
                  open_in (subtopology euclidean c) u)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC (MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] QUOTIENT_MAP_IMP_CONTINUOUS_OPEN) th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) {x | x IN s /\ f x IN c} SUBSET c`
  ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET);
    ASM_SIMP_TAC[QUOTIENT_MAP_OPEN_CLOSED] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET)] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `u:real^N->bool` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  (ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  (MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
    [MATCH_MP_TAC(MESON[] `t = s /\ (P s <=> Q s) ==> (P s <=> Q t)`) THEN
     CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_ELIM_THM]];
     ALL_TAC]) THEN
  (EQ_TAC THENL
    [MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] OPEN_IN_SUBSET_TRANS) ORELSE
     MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] CLOSED_IN_SUBSET_TRANS);
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] OPEN_IN_TRANS) ORELSE
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CLOSED_IN_TRANS)]) THEN
  (MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN ORELSE
   MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_GEN ORELSE ASM_SIMP_TAC[]) THEN
  ASM SET_TAC[]);;

let CONNECTED_MONOTONE_QUOTIENT_PREIMAGE = prove
 (`!f:real^M->real^N s t.
      f continuous_on s /\ IMAGE f s = t /\
      (!u. u SUBSET t
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                open_in (subtopology euclidean t) u)) /\
      (!y. y IN t ==> connected {x | x IN s /\ f x = y}) /\
      connected t
      ==> connected s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `v:real^M->bool`] THEN STRIP_TAC THEN
  UNDISCH_TAC `connected(t:real^N->bool)` THEN SIMP_TAC[CONNECTED_OPEN_IN] THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (f:real^M->real^N) (s INTER u)`;
    `IMAGE (f:real^M->real^N) (s INTER v)`] THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^M->real^N) (s INTER u) INTER IMAGE f (s INTER v) = {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC  THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[connected]] THEN
    MAP_EVERY EXISTS_TAC [`u:real^M->bool`; `v:real^M->bool`] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [CONJ_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (rand o rand) th o snd)) THEN
  (ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  MATCH_MP_TAC(MESON[]
   `{x | x IN s /\ f x IN IMAGE f u} = u /\ open_in top u
    ==> open_in top {x | x IN s /\ f x IN IMAGE f u}`) THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER] THEN ASM SET_TAC[]);;

let CONNECTED_MONOTONE_QUOTIENT_PREIMAGE_GEN = prove
 (`!f:real^M->real^N s t c.
      IMAGE f s = t /\
      (!u. u SUBSET t
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                open_in (subtopology euclidean t) u)) /\
      (!y. y IN t ==> connected {x | x IN s /\ f x = y}) /\
      (open_in (subtopology euclidean t) c \/
       closed_in (subtopology euclidean t) c) /\
      connected c
      ==> connected {x | x IN s /\ f x IN c}`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
   (REWRITE_RULE[CONJ_ASSOC] CONNECTED_MONOTONE_QUOTIENT_PREIMAGE)) THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET t` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; CLOSED_IN_IMP_SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `f:real^M->real^N` THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      QUOTIENT_MAP_IMP_CONTINUOUS_OPEN)) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
    REWRITE_TAC[SUBSET_RESTRICT];
    ASM SET_TAC[];
    MATCH_MP_TAC QUOTIENT_MAP_RESTRICT THEN
    ASM_MESON_TAC[SUBSET_REFL];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC EQ_IMP] THEN
    AP_TERM_TAC THEN ASM SET_TAC[]]);;
