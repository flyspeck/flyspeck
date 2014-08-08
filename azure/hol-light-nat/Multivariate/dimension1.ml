(* ========================================================================= *)
(* Results connected with topological dimension.                             *)
(*                                                                           *)
(* At the moment this is just Brouwer's fixpoint theorem. The proof is from  *)
(* Kuhn: "some combinatorial lemmas in topology", IBM J. v4. (1960) p. 518   *)
(* See "http://www.research.ibm.com/journal/rd/045/ibmrd0405K.pdf".          *)
(*                                                                           *)
(* The script below is quite messy, but at least we avoid formalizing any    *)
(* topological machinery; we don't even use barycentric subdivision; this is *)
(* the big advantage of Kuhn's proof over the usual Sperner's lemma one.     *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

open Hol_core
open Card
open Floor
open Vectors
open Determinants
open Vectors
open Topology
open Convex
open Paths
open Polytope


let BROUWER_COMPACTNESS_LEMMA = prove
 (`!f:real^M->real^N s.
        compact s /\ f continuous_on s /\ ~(?x. x IN s /\ (f x = vec 0))
        ==> ?d. &0 < d /\ !x. x IN s ==> d <= norm(f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`norm o (f:real^M->real^N)`; `s:real^M->bool`]
                CONTINUOUS_ATTAINS_INF) THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THENL
   [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; o_ASSOC; CONTINUOUS_ON_LIFT_NORM] THEN
  REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[NORM_POS_LT]);;

let KUHN_LABELLING_LEMMA = prove
 (`!f:real^N->real^N P Q.
        (!x. P x ==> P (f x))
        ==> (!x. P x ==> (!i. Q i ==> &0 <= x$i /\ x$i <= &1))
            ==> ?l. (!x i. l x i <= 1) /\
                    (!x i. P x /\ Q i /\ (x$i = &0) ==> (l x i = 0)) /\
                    (!x i. P x /\ Q i /\ (x$i = &1) ==> (l x i = 1)) /\
                    (!x i. P x /\ Q i /\ (l x i = 0) ==> x$i <= f(x)$i) /\
                    (!x i. P x /\ Q i /\ (l x i = 1) ==> f(x)$i <= x$i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AND_FORALL_THM;  GSYM SKOLEM_THM] THEN
  REWRITE_TAC[ARITH_RULE `n <= 1 <=> (n = 0) \/ (n = 1)`;
              RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2; ARITH_EQ] THEN
  MESON_TAC[REAL_ARITH
   `!x y. &0 <= x /\ x <= &1 /\ &0 <= y /\ y <= &1
          ==> ~(x = &1) /\ x <= y \/ ~(x = &0) /\ y <= x`]);;

(* ------------------------------------------------------------------------- *)
(* The key "counting" observation, somewhat abstracted.                      *)
(* ------------------------------------------------------------------------- *)

let KUHN_COUNTING_LEMMA = prove
 (`!face:F->S->bool faces simplices comp comp' bnd.
        FINITE faces /\ FINITE simplices /\
        (!f. f IN faces /\ bnd f
             ==> (CARD {s | s IN simplices /\ face f s} = 1)) /\
        (!f. f IN faces /\ ~bnd f
             ==> (CARD {s | s IN simplices /\ face f s} = 2)) /\
        (!s. s IN simplices /\ comp s
             ==> (CARD {f | f IN faces /\ face f s /\ comp' f} = 1)) /\
        (!s. s IN simplices /\ ~comp s
             ==> (CARD {f | f IN faces /\ face f s /\ comp' f} = 0) \/
                 (CARD {f | f IN faces /\ face f s /\ comp' f} = 2))
        ==> ODD(CARD {f | f IN faces /\ comp' f /\ bnd f})
            ==> ODD(CARD {s | s IN simplices /\ comp s})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum simplices
     (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) =
    sum simplices
     (\s. &(CARD {f | f IN {f | f IN faces /\ comp' f /\ bnd f} /\
                      face f s})) +
    sum simplices
     (\s. &(CARD {f | f IN {f | f IN faces /\ comp' f /\ ~(bnd f)} /\
                      face f s}))`
  MP_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_EQ THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC CARD_UNION_EQ THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN GEN_TAC THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s f. (face:F->S->bool) f s`; `simplices:S->bool`;
    `{f:F | f IN faces /\ comp' f /\ bnd f}`; `1`] SUM_MULTICOUNT) THEN
  MP_TAC(ISPECL
   [`\s f. (face:F->S->bool) f s`; `simplices:S->bool`;
    `{f:F | f IN faces /\ comp' f /\ ~(bnd f)}`; `2`] SUM_MULTICOUNT) THEN
  REWRITE_TAC[] THEN
  REPEAT(ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT] THEN GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    SIMP_TAC[IN_ELIM_THM];
    DISCH_THEN SUBST1_TAC]) THEN
  SUBGOAL_THEN
   `sum simplices
     (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) =
    sum {s | s IN simplices /\ comp s}
        (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) +
    sum {s | s IN simplices /\ ~(comp s)}
        (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f}))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTER; IN_UNION] THEN
    CONJ_TAC THEN GEN_TAC THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {s | s IN simplices /\ comp s}
        (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) =
    sum {s | s IN simplices /\ comp s} (\s. &1)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {s | s IN simplices /\ ~(comp s)}
        (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) =
    sum {s | s IN simplices /\ ~(comp s) /\
             (CARD {f | f IN faces /\ face f s /\ comp' f} = 0)}
        (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) +
    sum {s | s IN simplices /\ ~(comp s) /\
             (CARD {f | f IN faces /\ face f s /\ comp' f} = 2)}
        (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f}))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_UNION] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[ARITH_RULE `~(2 = 0)`];
      ALL_TAC] THEN
    X_GEN_TAC `s:S` THEN UNDISCH_TAC
     `!s:S. s IN simplices /\ ~comp s
            ==> (CARD {f:F | f IN faces /\ face f s /\ comp' f} = 0) \/
                (CARD {f | f IN faces /\ face f s /\ comp' f} = 2)` THEN
    DISCH_THEN(MP_TAC o SPEC `s:S`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. sum {s | s IN simplices /\ ~(comp s) /\
             (CARD {f | f IN faces /\ face f s /\ comp' f} = n)}
            (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) =
        sum {s | s IN simplices /\ ~(comp s) /\
             (CARD {f | f IN faces /\ face f s /\ comp' f} = n)}
            (\s:S. &n)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_0] THEN ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
  DISCH_THEN(MP_TAC o AP_TERM `ODD`) THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH_ODD; ODD]);;

(* ------------------------------------------------------------------------- *)
(* The odd/even result for faces of complete vertices, generalized.          *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_1_EXISTS = prove
 (`!s. s HAS_SIZE 1 <=> ?!x. x IN s`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[EXTENSION; IN_SING] THEN MESON_TAC[]);;

let HAS_SIZE_2_EXISTS = prove
 (`!s. s HAS_SIZE 2 <=> ?x y. ~(x = y) /\ !z. z IN s <=> (z = x) \/ (z = y)`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let IMAGE_LEMMA_0 = prove
 (`!f:A->B s n.
      {a | a IN s /\ (IMAGE f (s DELETE a) = t DELETE b)} HAS_SIZE n
      ==> {s' | ?a. a IN s /\ (s' = s DELETE a) /\ (IMAGE f s' = t DELETE b)}
          HAS_SIZE n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{s' | ?a. a IN s /\ (s' = s DELETE a) /\ (IMAGE f s' = t DELETE b)} =
    IMAGE (\a. s DELETE a)
          {a | a IN s /\ (IMAGE (f:A->B) (s DELETE a) = t DELETE b)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE] THEN MESON_TAC[]]);;

let IMAGE_LEMMA_1 = prove
 (`!f:A->B s t b.
        FINITE s /\ FINITE t /\ (CARD s = CARD t) /\
        (IMAGE f s = t) /\ b IN t
        ==> (CARD {s' | ?a. a IN s /\ (s' = s DELETE a) /\
                            (IMAGE f s' = t DELETE b)} = 1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_SIZE_CARD THEN
  MATCH_MP_TAC IMAGE_LEMMA_0 THEN REWRITE_TAC[HAS_SIZE_1_EXISTS] THEN
  SUBGOAL_THEN `!x y. x IN s /\ y IN s /\ ((f:A->B) x = f y) ==> (x = y)`
  ASSUME_TAC THENL [ASM_MESON_TAC[IMAGE_IMP_INJECTIVE_GEN]; ALL_TAC] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM; IN_ELIM_THM] THEN CONJ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_IMAGE] THENL
   [DISCH_THEN(fun th -> MP_TAC(SPEC `b:B` th) THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE] THEN ASM_MESON_TAC[]]);;

let IMAGE_LEMMA_2 = prove
 (`!f:A->B s t b.
        FINITE s /\ FINITE t /\ (CARD s = CARD t) /\
        (IMAGE f s) SUBSET t /\ ~(IMAGE f s = t) /\ b IN t
        ==> (CARD {s' | ?a. a IN s /\ (s' = s DELETE a) /\
                            (IMAGE f s' = t DELETE b)} = 0) \/
            (CARD {s' | ?a. a IN s /\ (s' = s DELETE a) /\
                            (IMAGE f s' = t DELETE b)} = 2)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC
   `{a | a IN s /\ (IMAGE (f:A->B) (s DELETE a) = t DELETE b)} = {}`
  THENL [DISJ1_TAC; DISJ2_TAC] THEN MATCH_MP_TAC HAS_SIZE_CARD THEN
  MATCH_MP_TAC IMAGE_LEMMA_0 THEN
  ASM_REWRITE_TAC[HAS_SIZE_0; HAS_SIZE_2_EXISTS] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a1:A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->B) a1 IN (t DELETE b)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_DELETE] THEN
    ASM_MESON_TAC[SUBSET; IN_IMAGE; INSERT_DELETE; IMAGE_CLAUSES];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  DISCH_THEN(MP_TAC o SPEC `(f:A->B) a1`) THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a2:A` THEN
  REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x y. x IN (s DELETE a1) /\ y IN (s DELETE a1) /\ ((f:A->B) x = f y)
          ==> (x = y)`
  MP_TAC THENL
   [MATCH_MP_TAC IMAGE_IMP_INJECTIVE_GEN THEN EXISTS_TAC `t DELETE (b:B)` THEN
    ASM_SIMP_TAC[CARD_DELETE; FINITE_DELETE];
    REWRITE_TAC[IN_DELETE] THEN DISCH_TAC] THEN
  X_GEN_TAC `a:A` THEN ASM_CASES_TAC `a:A = a1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(a:A) IN s` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(f:A->B) a = f a1` THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[IN_DELETE]] THEN
  FIRST_X_ASSUM(fun t -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM t]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `(f:A->B) a`); ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Combine this with the basic counting lemma.                               *)
(* ------------------------------------------------------------------------- *)

let KUHN_COMPLETE_LEMMA = prove
 (`!face:(A->bool)->(A->bool)->bool simplices rl bnd n.
        FINITE simplices /\
        (!f s. face f s <=> ?a. a IN s /\ (f = s DELETE a)) /\
        (!s. s IN simplices ==> s HAS_SIZE (n + 2) /\
                                (IMAGE rl s) SUBSET 0..n+1) /\
        (!f. f IN {f | ?s. s IN simplices /\ face f s} /\ bnd f
             ==> (CARD {s | s IN simplices /\ face f s} = 1)) /\
        (!f. f IN {f | ?s. s IN simplices /\ face f s} /\ ~bnd f
             ==> (CARD {s | s IN simplices /\ face f s} = 2))
        ==> ODD(CARD {f | f IN {f | ?s. s IN simplices /\ face f s} /\
                          (IMAGE rl f = 0..n) /\ bnd f})
            ==> ODD(CARD {s | s IN simplices /\ (IMAGE rl s = 0..n+1)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!P f:A->bool s.
       s IN simplices
       ==> (f IN {f | ?s. s IN simplices /\ (?a. a IN s /\ (f = s DELETE a))} /\
            (?a. a IN s /\ (f = s DELETE a)) /\ P f <=>
           (?a. a IN s /\ (f = s DELETE a) /\ P f))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `0..n = (0..n+1) DELETE (n+1)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_DELETE] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC KUHN_COUNTING_LEMMA THEN
  EXISTS_TAC `face:(A->bool)->(A->bool)->bool` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_SIMP_TAC[] THENL
   [SUBGOAL_THEN
     `{f:A->bool | ?s. s IN simplices /\ (?a. a IN s /\ (f = s DELETE a))} =
      UNIONS (IMAGE (\s. {f | ?a. a IN s /\ (f = s DELETE a)}) simplices)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; UNIONS_IMAGE; IN_ELIM_THM]; ALL_TAC] THEN
    ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `s:A->bool` THEN
    DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_POWERSET THEN ASM_MESON_TAC[HAS_SIZE];
      SIMP_TAC[SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_DELETE]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_LEMMA_1;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_LEMMA_2] THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0; LE_REFL] THEN
  REWRITE_TAC[CARD_NUMSEG; ARITH_RULE `((n + 1) + 1) - 0 = n + 2`] THEN
  ASM_MESON_TAC[HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* We use the following notion of ordering rather than pointwise indexing.   *)
(* ------------------------------------------------------------------------- *)

let kle = new_definition
  `kle n x y <=> ?k. k SUBSET 1..n /\
                     (!j. y(j) = x(j) + (if j IN k then 1 else 0))`;;

let KLE_REFL = prove
 (`!n x. kle n x x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kle] THEN EXISTS_TAC `{}:num->bool` THEN
  REWRITE_TAC[ADD_CLAUSES; NOT_IN_EMPTY; EMPTY_SUBSET]);;

let KLE_ANTISYM = prove
 (`!n x y. kle n x y /\ kle n y x <=> (x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [REWRITE_TAC[kle]; MESON_TAC[KLE_REFL]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[ARITH_RULE `(x = (x + a) + b) ==> (x = x + a:num)`]);;

let POINTWISE_MINIMAL,POINTWISE_MAXIMAL = (CONJ_PAIR o prove)
 (`(!s:(num->num)->bool.
        FINITE s
        ==> ~(s = {}) /\
            (!x y. x IN s /\ y IN s
                   ==> (!j. x(j) <= y(j)) \/ (!j. y(j) <= x(j)))
            ==> ?a. a IN s /\ !x. x IN s ==> !j. a(j) <= x(j)) /\
   (!s:(num->num)->bool.
        FINITE s
        ==> ~(s = {}) /\
            (!x y. x IN s /\ y IN s
                   ==> (!j. x(j) <= y(j)) \/ (!j. y(j) <= x(j)))
            ==> ?a. a IN s /\ !x. x IN s ==> !j. x(j) <= a(j))`,
  CONJ_TAC THEN
  (MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[NOT_INSERT_EMPTY] THEN
   MAP_EVERY X_GEN_TAC [`a:num->num`; `s:(num->num)->bool`] THEN
   ASM_CASES_TAC `s:(num->num)->bool = {}` THEN ASM_REWRITE_TAC[] THENL
    [REWRITE_TAC[IN_SING] THEN MESON_TAC[LE_REFL]; ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
   DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `b:num->num` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`a:num->num`; `b:num->num`]) THEN
   ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[LE_CASES; LE_TRANS]));;

let KLE_IMP_POINTWISE = prove
 (`!n x y. kle n x y ==> !j. x(j) <= y(j)`,
  REWRITE_TAC[kle] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_ADD]);;

let POINTWISE_ANTISYM = prove
 (`!x y:num->num. (!j. x(j) <= y(j)) /\ (!j. y(j) <= x(j)) <=> (x = y)`,
  REWRITE_TAC[AND_FORALL_THM; FUN_EQ_THM; LE_ANTISYM]);;

let KLE_TRANS = prove
 (`!x y z n. kle n x y /\ kle n y z /\ (kle n x z \/ kle n z x)
             ==> kle n x z`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `x:num->num = z` (fun th -> REWRITE_TAC[KLE_REFL; th]) THEN
  REWRITE_TAC[FUN_EQ_THM; GSYM LE_ANTISYM; FORALL_AND_THM] THEN
  ASM_MESON_TAC[KLE_IMP_POINTWISE; LE_TRANS]);;

let KLE_STRICT = prove
 (`!n x y. kle n x y /\ ~(x = y)
           ==> (!j. x(j) <= y(j)) /\ (?k. 1 <= k /\ k <= n /\ x(k) < y(k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kle] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num->bool` MP_TAC) THEN
  ASM_CASES_TAC `k:num->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; ADD_CLAUSES; GSYM FUN_EQ_THM; ETA_AX];
    STRIP_TAC THEN ASM_REWRITE_TAC[LE_ADD] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN
    ASM_MESON_TAC[SUBSET; IN_NUMSEG]]);;

let KLE_MINIMAL = prove
 (`!s n. FINITE s /\ ~(s = {}) /\
         (!x y. x IN s /\ y IN s ==> kle n x y \/ kle n y x)
         ==> ?a. a IN s /\ !x. x IN s ==> kle n a x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a:num->num. a IN s /\ !x. x IN s ==> !j. a(j) <= x(j)`
  MP_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] POINTWISE_MINIMAL); ALL_TAC] THEN
  ASM_MESON_TAC[POINTWISE_ANTISYM; KLE_IMP_POINTWISE]);;

let KLE_MAXIMAL = prove
 (`!s n. FINITE s /\ ~(s = {}) /\
         (!x y. x IN s /\ y IN s ==> kle n x y \/ kle n y x)
         ==> ?a. a IN s /\ !x. x IN s ==> kle n x a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a:num->num. a IN s /\ !x. x IN s ==> !j. x(j) <= a(j)`
  MP_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] POINTWISE_MAXIMAL); ALL_TAC] THEN
  ASM_MESON_TAC[POINTWISE_ANTISYM; KLE_IMP_POINTWISE]);;

let KLE_STRICT_SET = prove
 (`!n x y. kle n x y /\ ~(x = y) ==> 1 <= CARD {k | k IN 1..n /\ x(k) < y(k)}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP KLE_STRICT) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {i:num}` THEN CONJ_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_RULES; ARITH; NOT_IN_EMPTY];
    MATCH_MP_TAC CARD_SUBSET THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN
    SIMP_TAC[IN_ELIM_THM; IN_NUMSEG; SUBSET; IN_SING] THEN ASM_MESON_TAC[]]);;

let KLE_RANGE_COMBINE = prove
 (`!n x y m1 m2.
        kle n x y /\ kle n y z /\ (kle n x z \/ kle n z x) /\
        m1 <= CARD {k | k IN 1..n /\ x(k) < y(k)} /\
        m2 <= CARD {k | k IN 1..n /\ y(k) < z(k)}
        ==> kle n x z /\ m1 + m2 <= CARD {k | k IN 1..n /\ x(k) < z(k)}`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[KLE_TRANS]; DISCH_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD {k | k IN 1..n /\ x(k):num < y(k)} +
              CARD {k | k IN 1..n /\ y(k) < z(k)}` THEN
  ASM_SIMP_TAC[LE_ADD2] THEN MATCH_MP_TAC EQ_IMP_LE THEN
  MATCH_MP_TAC CARD_UNION_EQ THEN
  SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[KLE_IMP_POINTWISE; ARITH_RULE
     `x <= y:num /\ y <= z ==> (x < y \/ y < z <=> x < z)`]] THEN
  X_GEN_TAC `i:num` THEN UNDISCH_TAC `kle n x z` THEN
  REWRITE_TAC[kle] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i IN 1..n` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `d <= 1 ==> ~(a < x /\ x < a + d)`) THEN
  COND_CASES_TAC THEN REWRITE_TAC[ARITH]);;

let KLE_RANGE_COMBINE_L = prove
 (`!n x y m.
        kle n x y /\ kle n y z /\ (kle n x z \/ kle n z x) /\
        m <= CARD {k | k IN 1..n /\ y(k) < z(k)}
        ==> kle n x z /\ m <= CARD {k | k IN 1..n /\ x(k) < z(k)}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:num->num = y` THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `kle n x z /\ 1 + m <= CARD {k | k IN 1 .. n /\ x k < z k}`
   (fun th -> MESON_TAC[th; ARITH_RULE `1 + m <= x ==> m <= x`]) THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `y:num->num` THEN
  ASM_SIMP_TAC[KLE_STRICT_SET]);;

let KLE_RANGE_COMBINE_R = prove
 (`!n x y m.
        kle n x y /\ kle n y z /\ (kle n x z \/ kle n z x) /\
        m <= CARD {k | k IN 1..n /\ x(k) < y(k)}
        ==> kle n x z /\ m <= CARD {k | k IN 1..n /\ x(k) < z(k)}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `y:num->num = z` THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `kle n x z /\ m + 1 <= CARD {k | k IN 1 .. n /\ x k < z k}`
   (fun th -> MESON_TAC[th; ARITH_RULE `m + 1 <= x ==> m <= x`]) THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `y:num->num` THEN
  ASM_SIMP_TAC[KLE_STRICT_SET]);;

let KLE_RANGE_INDUCT = prove
 (`!n m s. s HAS_SIZE (SUC m)
           ==> (!x y. x IN s /\ y IN s ==> kle n x y \/ kle n y x)
               ==> ?x y. x IN s /\ y IN s /\ kle n x y /\
                         m <= CARD {k | k IN 1..n /\ x(k) < y(k)}`,
  GEN_TAC THEN INDUCT_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ARITH; LE_0] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN MESON_TAC[IN_SING; KLE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `s:(num->num)->bool` THEN
  ONCE_REWRITE_TAC[HAS_SIZE_SUC] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num->num)->bool`; `n:num`] KLE_MINIMAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HAS_SIZE_SUC; HAS_SIZE]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:num->num` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:num->num)`) THEN
  REPEAT(ANTS_TAC THENL [ASM_MESON_TAC[IN_DELETE]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->num` MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->num` THEN
  REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `SUC m = 1 + m`] THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `x:num->num` THEN
  ASM_SIMP_TAC[KLE_STRICT_SET]);;

let KLE_SUC = prove
 (`!n x y. kle n x y ==> kle (n + 1) x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kle] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG] THEN
  MESON_TAC[ARITH_RULE `k <= n ==> k <= n + 1`]);;

let KLE_TRANS_1 = prove
 (`!n x y. kle n x y ==> !j. x j <= y j /\ y j <= x j + 1`,
  SIMP_TAC[kle; LEFT_IMP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ARITH_TAC);;

let KLE_TRANS_2 = prove
 (`!a b c. kle n a b /\ kle n b c /\ (!j. c j <= a j + 1)
           ==> kle n a c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[kle] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk1:num->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `kk2:num->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    EXISTS_TAC `(kk1:num->bool) UNION kk2` THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[UNION_SUBSET; IN_UNION] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `(i:num) IN kk1` THEN ASM_CASES_TAC `(i:num) IN kk2` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let KLE_BETWEEN_R = prove
 (`!a b c x. kle n a b /\ kle n b c /\ kle n a x /\ kle n c x
             ==> kle n b x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KLE_TRANS_2 THEN
  EXISTS_TAC `c:num->num` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[KLE_TRANS_1; ARITH_RULE
   `x <= c + 1 /\ c <= b ==> x <= b + 1`]);;

let KLE_BETWEEN_L = prove
 (`!a b c x. kle n a b /\ kle n b c /\ kle n x a /\ kle n x c
             ==> kle n x b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KLE_TRANS_2 THEN
  EXISTS_TAC `a:num->num` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[KLE_TRANS_1; ARITH_RULE
   `c <= x + 1 /\ b <= c ==> b <= x + 1`]);;

let KLE_ADJACENT = prove
 (`!a b x k.
        1 <= k /\ k <= n /\ (!j. b(j) = if j = k then a(j) + 1 else a(j)) /\
        kle n a x /\ kle n x b
        ==> (x = a) \/ (x = b)`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP KLE_IMP_POINTWISE)) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; IMP_IMP; AND_FORALL_THM] THEN
  ASM_CASES_TAC `(x:num->num) k = a k` THENL
   [DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th);
    DISCH_THEN(fun th -> DISJ2_TAC THEN MP_TAC th)] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_ANTISYM] THEN
  ASM_MESON_TAC[ARITH_RULE
   `a <= x /\ x <= a + 1 /\ ~(x = a) ==> (x = a + 1)`]);;

(* ------------------------------------------------------------------------- *)
(* Kuhn's notion of a simplex (my reformulation to avoid so much indexing).  *)
(* ------------------------------------------------------------------------- *)

let ksimplex = new_definition
 `ksimplex p n s <=>
        s HAS_SIZE (n + 1) /\
        (!x j. x IN s ==> x(j) <= p) /\
        (!x j. x IN s /\ ~(1 <= j /\ j <= n) ==> (x j = p)) /\
        (!x y. x IN s /\ y IN s ==> kle n x y \/ kle n y x)`;;

let KSIMPLEX_EXTREMA = prove
 (`!p n s.
        ksimplex p n s
        ==> ?a b. a IN s /\ b IN s /\
                  (!x. x IN s ==> kle n a x /\ kle n x b) /\
                  (!i. b(i) = if 1 <= i /\ i <= n then a(i) + 1 else a(i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ksimplex] THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 0 <=> F`; GSYM FUN_EQ_THM] THEN
    REWRITE_TAC[ADD_CLAUSES; ETA_AX] THEN
    CONV_TAC(LAND_CONV(LAND_CONV HAS_SIZE_CONV)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[KLE_REFL];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num->num)->bool`; `n:num`] KLE_MINIMAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HAS_SIZE; HAS_SIZE_SUC; ADD1]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:num->num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num->num)->bool`; `n:num`] KLE_MAXIMAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HAS_SIZE; HAS_SIZE_SUC; ADD1]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `n:num`; `s:(num->num)->bool`] KLE_RANGE_INDUCT) THEN
  ASM_REWRITE_TAC[ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->num` (X_CHOOSE_THEN `d:num->num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `{k | k IN 1 .. n /\ a k :num < b k} = 1..n` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_LE THEN
    ASM_REWRITE_TAC[CARD_NUMSEG; ADD_SUB; FINITE_NUMSEG; SUBSET_RESTRICT] THEN
    SUBGOAL_THEN `kle n a b /\ n <= CARD {k | k IN 1..n /\ a(k) < b(k)}`
     (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC KLE_RANGE_COMBINE_L THEN EXISTS_TAC `c:num->num` THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `kle n c b /\ n <= CARD {k | k IN 1 .. n /\ c k < b k}`
     (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC KLE_RANGE_COMBINE_R THEN EXISTS_TAC `d:num->num` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `kle n a b` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [kle]) THEN
  ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_REFL] THEN
  ASM_MESON_TAC[SUBSET; IN_NUMSEG]);;

let KSIMPLEX_EXTREMA_STRONG = prove
 (`!p n s.
        ksimplex p n s /\ ~(n = 0)
        ==> ?a b. a IN s /\ b IN s /\ ~(a = b) /\
                  (!x. x IN s ==> kle n a x /\ kle n x b) /\
                  (!i. b(i) = if 1 <= i /\ i <= n then a(i) + 1 else a(i))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP KSIMPLEX_EXTREMA) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN
  ASM_REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN ARITH_TAC);;

let KSIMPLEX_SUCCESSOR = prove
 (`!a p n s.
        ksimplex p n s /\ a IN s
        ==> (!x. x IN s ==> kle n x a) \/
            (?y. y IN s /\ ?k. 1 <= k /\ k <= n /\
                               !j. y(j) = if j = k then a(j) + 1 else a(j))`,
  REWRITE_TAC[ksimplex] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[TAUT `a \/ b <=> ~a ==> b`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`{x | x IN s /\ ~kle n x a}`; `n:num`] KLE_MINIMAL) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  ASM_SIMP_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= CARD {k | k IN 1..n /\ a(k):num < b(k)}` MP_TAC THENL
   [MATCH_MP_TAC KLE_STRICT_SET THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC o MATCH_MP (ARITH_RULE
   `1 <= n ==> (n = 1) \/ 2 <= n`))
  THENL
   [DISCH_TAC THEN
    MP_TAC(HAS_SIZE_CONV `{k | k IN 1 .. n /\ a k :num < b k} HAS_SIZE 1`) THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; IN_NUMSEG] THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL [MESON_TAC[th]; MP_TAC th]) THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL [MESON_TAC[th]; MP_TAC th]) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
    SUBGOAL_THEN `kle n a b` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [kle]) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_REFL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_REFL] THEN
    ASM_MESON_TAC[SUBSET; IN_NUMSEG; ARITH_RULE `~(a + 1 = a)`;
                  ARITH_RULE `a < a + 1`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `PRE(CARD {x | x IN s /\ ~(kle n x a)})`;
                `{x | x IN s /\ ~(kle n x a)}`] KLE_RANGE_INDUCT) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; CARD_EQ_0; GSYM MEMBER_NOT_EMPTY;
    ARITH_RULE `(n = SUC(PRE n)) <=> ~(n = 0)`] THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->num`
   (X_CHOOSE_THEN `d:num->num` MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2
   (STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM]) MP_TAC)) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `PRE(CARD {x | x IN s /\ kle n x a})`;
                `{x | x IN s /\ kle n x a}`] KLE_RANGE_INDUCT) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; CARD_EQ_0; GSYM MEMBER_NOT_EMPTY;
    ARITH_RULE `(n = SUC(PRE n)) <=> ~(n = 0)`] THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[KLE_REFL]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num->num`
    (X_CHOOSE_THEN `f:num->num` MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2
   (STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM]) MP_TAC)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `kle n e d /\ n + 1 <= CARD {k | k IN 1..n /\ e(k) < d(k)}`
  MP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[ARITH_RULE `~(n + 1 <= x) <=> x <= n`] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(1..n)` THEN
    SIMP_TAC[CARD_SUBSET; SUBSET_RESTRICT; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    REWRITE_TAC[CARD_NUMSEG; ADD_SUB; LE_REFL]] THEN
  SUBGOAL_THEN
   `(CARD {x | x IN s /\ kle n x a} - 1) +
    2 + (CARD {x | x IN s /\ ~kle n x a} - 1) = n + 1`
   (SUBST1_TAC o SYM)
  THENL
   [MATCH_MP_TAC(ARITH_RULE
     `~(a = 0) /\ ~(b = 0) /\ (a + b = n + 1)
       ==> ((a - 1) + 2 + (b - 1) = n + 1)`) THEN
    ASM_SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT; GSYM MEMBER_NOT_EMPTY] THEN
    REPEAT (CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT2) THEN
    MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `a:num->num` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN CONJ_TAC THENL
   [W(fun(asl,w) -> SUBGOAL_THEN(mk_conj(`kle n e a`,w))
     (fun th -> REWRITE_TAC[th])) THEN
    MATCH_MP_TAC KLE_RANGE_COMBINE_R THEN EXISTS_TAC `f:num->num` THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - 1 = PRE k`];
    ALL_TAC] THEN
  W(fun(asl,w) -> SUBGOAL_THEN(mk_conj(`kle n a d`,w))
     (fun th -> REWRITE_TAC[th])) THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `b:num->num` THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - 1 = PRE k`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  W(fun(asl,w) -> SUBGOAL_THEN(mk_conj(`kle n b d`,w))
     (fun th -> REWRITE_TAC[th])) THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE_L THEN EXISTS_TAC `c:num->num` THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - 1 = PRE k`] THEN ASM_MESON_TAC[KLE_TRANS]);;

let KSIMPLEX_PREDECESSOR = prove
 (`!a p n s.
        ksimplex p n s /\ a IN s
        ==> (!x. x IN s ==> kle n a x) \/
            (?y. y IN s /\ ?k. 1 <= k /\ k <= n /\
                               !j. a(j) = if j = k then y(j) + 1 else y(j))`,
  REWRITE_TAC[ksimplex] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[TAUT `a \/ b <=> ~a ==> b`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`{x | x IN s /\ ~kle n a x}`; `n:num`] KLE_MAXIMAL) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  ASM_SIMP_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= CARD {k | k IN 1..n /\ b(k):num < a(k)}` MP_TAC THENL
   [MATCH_MP_TAC KLE_STRICT_SET THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC o MATCH_MP (ARITH_RULE
   `1 <= n ==> (n = 1) \/ 2 <= n`))
  THENL
   [DISCH_TAC THEN
    MP_TAC(HAS_SIZE_CONV `{k | k IN 1 .. n /\ b k :num < a k} HAS_SIZE 1`) THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; IN_NUMSEG] THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL [MESON_TAC[th]; MP_TAC th]) THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL [MESON_TAC[th]; MP_TAC th]) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
    SUBGOAL_THEN `kle n b a` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [kle]) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_REFL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_REFL] THEN
    ASM_MESON_TAC[SUBSET; IN_NUMSEG; ARITH_RULE `~(a + 1 = a)`;
                  ARITH_RULE `a < a + 1`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `PRE(CARD {x | x IN s /\ ~(kle n a x)})`;
                `{x | x IN s /\ ~(kle n a x)}`] KLE_RANGE_INDUCT) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; CARD_EQ_0; GSYM MEMBER_NOT_EMPTY;
    ARITH_RULE `(n = SUC(PRE n)) <=> ~(n = 0)`] THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->num`
   (X_CHOOSE_THEN `c:num->num` MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2
   (STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM]) MP_TAC)) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `PRE(CARD {x | x IN s /\ kle n a x})`;
                `{x | x IN s /\ kle n a x}`] KLE_RANGE_INDUCT) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; CARD_EQ_0; GSYM MEMBER_NOT_EMPTY;
    ARITH_RULE `(n = SUC(PRE n)) <=> ~(n = 0)`] THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[KLE_REFL]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num`
    (X_CHOOSE_THEN `e:num->num` MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2
   (STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM]) MP_TAC)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `kle n d e /\ n + 1 <= CARD {k | k IN 1..n /\ d(k) < e(k)}`
  MP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[ARITH_RULE `~(n + 1 <= x) <=> x <= n`] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(1..n)` THEN
    SIMP_TAC[CARD_SUBSET; SUBSET_RESTRICT; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    REWRITE_TAC[CARD_NUMSEG; ADD_SUB; LE_REFL]] THEN
  SUBGOAL_THEN
   `((CARD {x | x IN s /\ ~kle n a x} - 1) + 2) +
    (CARD {x | x IN s /\ kle n a x} - 1) = n + 1`
   (SUBST1_TAC o SYM)
  THENL
   [MATCH_MP_TAC(ARITH_RULE
     `~(a = 0) /\ ~(b = 0) /\ (a + b = n + 1)
       ==> (((b - 1) + 2) + (a - 1) = n + 1)`) THEN
    ASM_SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT; GSYM MEMBER_NOT_EMPTY] THEN
    REPEAT (CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT2) THEN
    MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `a:num->num` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN CONJ_TAC THENL
   [ALL_TAC;
    W(fun(asl,w) -> SUBGOAL_THEN(mk_conj(`kle n a e`,w))
     (fun th -> REWRITE_TAC[th])) THEN
    MATCH_MP_TAC KLE_RANGE_COMBINE_L THEN EXISTS_TAC `f:num->num` THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - 1 = PRE k`]] THEN
  W(fun(asl,w) -> SUBGOAL_THEN(mk_conj(`kle n d a`,w))
     (fun th -> REWRITE_TAC[th])) THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `b:num->num` THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - 1 = PRE k`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  W(fun(asl,w) -> SUBGOAL_THEN(mk_conj(`kle n d b`,w))
     (fun th -> REWRITE_TAC[th])) THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE_R THEN EXISTS_TAC `c:num->num` THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - 1 = PRE k`] THEN ASM_MESON_TAC[KLE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* The lemmas about simplices that we need.                                  *)
(* ------------------------------------------------------------------------- *)

let FINITE_SIMPLICES = prove
 (`!p n. FINITE {s | ksimplex p n s}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{s | s SUBSET {f | (!i. i IN 1..n ==> f(i) IN 0..p) /\
                                 (!i. ~(i IN 1..n) ==> (f(i) = p))}}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_FUNSPACE; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; ksimplex] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_0]);;

let SIMPLEX_TOP_FACE = prove
 (`0 < p /\
   (!x. x IN f ==> (x(n + 1) = p))
   ==> ((?s a. ksimplex p (n + 1) s /\ a IN s /\ (f = s DELETE a)) <=>
        ksimplex p n f)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[ksimplex; LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(s:(num->num)->bool) HAS_SIZE ((n + 1) + 1)` THEN
      SIMP_TAC[HAS_SIZE; CARD_DELETE; FINITE_DELETE] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN X_GEN_TAC `j:num` THEN
      ONCE_REWRITE_TAC[ARITH_RULE
       `(1 <= j /\ j <= n) <=> (1 <= j /\ j <= n + 1) /\ ~(j = (n + 1))`] THEN
      ASM_MESON_TAC[IN_DELETE];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `kle (n + 1) x y \/ kle (n + 1) y x` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
      (REWRITE_TAC[kle] THEN
       MATCH_MP_TAC MONO_EXISTS THEN
       REWRITE_TAC[GSYM ADD1; NUMSEG_CLAUSES; ARITH_RULE `1 <= SUC n`] THEN
       X_GEN_TAC `k:num->bool` THEN SIMP_TAC[] THEN
       REWRITE_TAC[SUBSET; IN_INSERT] THEN
       ASM_CASES_TAC `(SUC n) IN k` THENL
        [ALL_TAC; ASM_MESON_TAC[]] THEN
       DISCH_THEN(MP_TAC o SPEC `n + 1` o CONJUNCT2) THEN
       ASM_REWRITE_TAC[GSYM ADD1] THEN
       ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
       MATCH_MP_TAC(ARITH_RULE `(x = p) /\ (y = p) ==> ~(x = SUC y)`) THEN
       CONJ_TAC THEN ASM_MESON_TAC[ADD1; IN_DELETE])];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP KSIMPLEX_EXTREMA) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num->num` (X_CHOOSE_THEN `b:num->num`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `c = \i. if i = (n + 1) then p - 1 else a(i)` THEN
  MAP_EVERY EXISTS_TAC [`(c:num->num) INSERT f`; `c:num->num`] THEN
  REWRITE_TAC[IN_INSERT; DELETE_INSERT] THEN
  SUBGOAL_THEN `~((c:num->num) IN f)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `!x:num->num. x IN f ==> (x (n + 1) = p)` THEN
    DISCH_THEN(MP_TAC o SPEC `c:num->num`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[] THEN UNDISCH_TAC `0 < p` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC; UNDISCH_TAC `~((c:num->num) IN f)` THEN SET_TAC[]] THEN
  UNDISCH_TAC `ksimplex p n f` THEN REWRITE_TAC[ksimplex] THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
   [SIMP_TAC[HAS_SIZE; FINITE_RULES; CARD_CLAUSES] THEN ASM_REWRITE_TAC[ADD1];
    EXPAND_TAC "c" THEN REWRITE_TAC[IN_INSERT] THEN
    SIMP_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
    ASM_MESON_TAC[ARITH_RULE `p - 1 <= p`];
    EXPAND_TAC "c" THEN REWRITE_TAC[IN_INSERT; TAUT
      `(a \/ b) /\ c ==> d <=> (a /\ c ==> d) /\ (b /\ c ==> d)`] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN CONJ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC); ALL_TAC] THEN
    ASM_MESON_TAC[LE_REFL; ARITH_RULE `1 <= n + 1`;
                  ARITH_RULE `j <= n ==> j <= n + 1`];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[IN_INSERT] THEN
  SUBGOAL_THEN `!x. x IN f ==> kle (n + 1) c x`
    (fun th -> ASM_MESON_TAC[th; KLE_SUC; KLE_REFL]) THEN
  X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `kle (n + 1) a x` MP_TAC THENL
   [ASM_MESON_TAC[KLE_SUC]; ALL_TAC] THEN
  EXPAND_TAC "c" THEN REWRITE_TAC[kle] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(n + 1) INSERT k` THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; IN_NUMSEG] THEN
  ASM_REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= n + 1`] THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_INSERT] THEN
  ASM_CASES_TAC `j = n + 1` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(n + 1 IN k)`
   (fun th -> ASM_MESON_TAC[th; ARITH_RULE `0 < p ==> (p = (p - 1) + 1)`]) THEN
  DISCH_TAC THEN UNDISCH_TAC `!x:num->num. x IN f ==> (x (n + 1) = p)` THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `x:num->num` th) THEN
                       MP_TAC(SPEC `a:num->num` th)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[ARITH_RULE `~(p + 1 = p)`]);;

let KSIMPLEX_FIX_PLANE = prove
 (`!p q n j s a a0 a1.
        ksimplex p n s /\ a IN s /\
        1 <= j /\ j <= n /\ (!x. x IN (s DELETE a) ==> (x j = q)) /\
        a0 IN s /\ a1 IN s /\
        (!i. a1 i = (if 1 <= i /\ i <= n then a0 i + 1 else a0 i))
        ==> (a = a0) \/ (a = a1)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~a /\ ~b ==> F) ==> a \/ b`) THEN STRIP_TAC THEN
  UNDISCH_TAC `!x:num->num. x IN s DELETE a ==> (x j = q)` THEN
  DISCH_THEN(fun th ->
   MP_TAC(SPEC `a0:num->num` th) THEN MP_TAC(SPEC `a1:num->num` th)) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN ARITH_TAC);;

let KSIMPLEX_FIX_PLANE_0 = prove
 (`!p n j s a a0 a1.
        ksimplex p n s /\ a IN s /\
        1 <= j /\ j <= n /\ (!x. x IN (s DELETE a) ==> (x j = 0)) /\
        a0 IN s /\ a1 IN s /\
        (!i. a1 i = (if 1 <= i /\ i <= n then a0 i + 1 else a0 i))
        ==> (a = a1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a = a0) \/ (a = a1:num->num)` MP_TAC THENL
   [MATCH_MP_TAC KSIMPLEX_FIX_PLANE THEN
    MAP_EVERY EXISTS_TAC
     [`p:num`; `0`; `n:num`; `j:num`; `s:(num->num)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a0:num->num = a1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~a ==> (a \/ b ==> b)`) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a1:num->num`) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN ARITH_TAC);;

let KSIMPLEX_FIX_PLANE_P = prove
 (`!p n j s a a0 a1.
        ksimplex p n s /\ a IN s /\
        1 <= j /\ j <= n /\ (!x. x IN (s DELETE a) ==> (x j = p)) /\
        a0 IN s /\ a1 IN s /\
        (!i. a1 i = (if 1 <= i /\ i <= n then a0 i + 1 else a0 i))
        ==> (a = a0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a = a0) \/ (a = a1:num->num)` MP_TAC THENL
   [MATCH_MP_TAC KSIMPLEX_FIX_PLANE THEN
    MAP_EVERY EXISTS_TAC
     [`p:num`; `p:num`; `n:num`; `j:num`; `s:(num->num)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a0:num->num = a1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~b ==> (a \/ b ==> a)`) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a0:num->num`) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ksimplex]) THEN
  DISCH_THEN(MP_TAC o SPEC `a1:num->num` o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let KSIMPLEX_REPLACE_0 = prove
 (`ksimplex p n s /\ a IN s /\ ~(n = 0) /\
   (?j. 1 <= j /\ j <= n /\ !x. x IN (s DELETE a) ==> (x j = 0))
   ==> (CARD
         {s' | ksimplex p n s' /\ ?b. b IN s' /\ (s' DELETE b = s DELETE a)} =
        1)`,
  let lemma = prove
   (`!a a'. (s' DELETE a' = s DELETE a) /\ (a' = a) /\ a' IN s' /\ a IN s
            ==> (s' = s)`,
    SET_TAC[]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_SIZE_CARD THEN
  REWRITE_TAC[HAS_SIZE_1_EXISTS] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `!s' a'. ksimplex p n s' /\ a' IN s' /\ (s' DELETE a' = s DELETE a)
            ==> (s' = s)`
   (fun th -> ASM_MESON_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `n:num`; `s:(num->num)->bool`]
       KSIMPLEX_EXTREMA_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:num->num` (X_CHOOSE_THEN `a1:num->num`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`p:num`; `n:num`; `s':(num->num)->bool`]
       KSIMPLEX_EXTREMA_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:num->num` (X_CHOOSE_THEN `b1:num->num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `a:num->num = a1` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KSIMPLEX_FIX_PLANE_0 THEN MAP_EVERY EXISTS_TAC
     [`p:num`; `n:num`; `j:num`; `s:(num->num)->bool`; `a0:num->num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a':num->num = b1` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KSIMPLEX_FIX_PLANE_0 THEN MAP_EVERY EXISTS_TAC
     [`p:num`; `n:num`; `j:num`; `s':(num->num)->bool`; `b0:num->num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN
  MAP_EVERY EXISTS_TAC [`a1:num->num`; `b1:num->num`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `b0:num->num = a0` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM KLE_ANTISYM] THEN ASM_MESON_TAC[IN_DELETE];
    ASM_REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]]);;

let KSIMPLEX_REPLACE_1 = prove
 (`ksimplex p n s /\ a IN s /\ ~(n = 0) /\
   (?j. 1 <= j /\ j <= n /\ !x. x IN (s DELETE a) ==> (x j = p))
   ==> (CARD
         {s' | ksimplex p n s' /\ ?b. b IN s' /\ (s' DELETE b = s DELETE a)} =
        1)`,
  let lemma = prove
   (`!a a'. (s' DELETE a' = s DELETE a) /\ (a' = a) /\ a' IN s' /\ a IN s
            ==> (s' = s)`,
    SET_TAC[]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_SIZE_CARD THEN
  REWRITE_TAC[HAS_SIZE_1_EXISTS] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `!s' a'. ksimplex p n s' /\ a' IN s' /\ (s' DELETE a' = s DELETE a)
            ==> (s' = s)`
   (fun th -> ASM_MESON_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `n:num`; `s:(num->num)->bool`]
       KSIMPLEX_EXTREMA_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:num->num` (X_CHOOSE_THEN `a1:num->num`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`p:num`; `n:num`; `s':(num->num)->bool`]
       KSIMPLEX_EXTREMA_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:num->num` (X_CHOOSE_THEN `b1:num->num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `a:num->num = a0` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KSIMPLEX_FIX_PLANE_P THEN MAP_EVERY EXISTS_TAC
     [`p:num`; `n:num`; `j:num`; `s:(num->num)->bool`; `a1:num->num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a':num->num = b0` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KSIMPLEX_FIX_PLANE_P THEN MAP_EVERY EXISTS_TAC
     [`p:num`; `n:num`; `j:num`; `s':(num->num)->bool`; `b1:num->num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN
  MAP_EVERY EXISTS_TAC [`a0:num->num`; `b0:num->num`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `b1:num->num = a1` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM KLE_ANTISYM] THEN ASM_MESON_TAC[IN_DELETE];
    ASM_REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    MESON_TAC[EQ_ADD_RCANCEL]]);;

let KSIMPLEX_REPLACE_2 = prove
 (`ksimplex p n s /\ a IN s /\ ~(n = 0) /\
   ~(?j. 1 <= j /\ j <= n /\ !x. x IN (s DELETE a) ==> (x j = 0)) /\
   ~(?j. 1 <= j /\ j <= n /\ !x. x IN (s DELETE a) ==> (x j = p))
   ==> (CARD
         {s' | ksimplex p n s' /\ ?b. b IN s' /\ (s' DELETE b = s DELETE a)} =
        2)`,
  let lemma = prove
   (`!a a'. (s' DELETE a' = s DELETE a) /\ (a' = a) /\ a' IN s' /\ a IN s
            ==> (s' = s)`,
    SET_TAC[])
  and lemma_1 = prove
   (`a IN s /\ ~(b = a) ==> ~(s = b INSERT (s DELETE a))`,
    SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `n:num`; `s:(num->num)->bool`]
       KSIMPLEX_EXTREMA_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:num->num` (X_CHOOSE_THEN `a1:num->num`
   STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `a:num->num = a0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`a0:num->num`; `p:num`; `n:num`; `s:(num->num)->bool`]
                 KSIMPLEX_SUCCESSOR) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~a /\ (b ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC `a1:num->num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP KLE_IMP_POINTWISE) THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; ARITH] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a2:num->num`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `a3 = \j:num. if j = k then a1 j + 1 else a1 j` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    MATCH_MP_TAC HAS_SIZE_CARD THEN CONV_TAC HAS_SIZE_CONV THEN
    MAP_EVERY EXISTS_TAC
     [`s:(num->num)->bool`; `a3 INSERT (s DELETE (a0:num->num))`] THEN
    SUBGOAL_THEN `~((a3:num->num) IN s)` ASSUME_TAC THENL
     [DISCH_TAC THEN SUBGOAL_THEN `kle n a3 a1` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP KLE_IMP_POINTWISE) THEN
      ASM_REWRITE_TAC[LE_REFL] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(a3:num->num = a0) /\ ~(a3 = a1)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(a2:num->num = a0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[ARITH_RULE `~(x + 1 = x)`];
      ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC lemma_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!x. x IN (s DELETE a0) ==> kle n a2 x` ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
      SUBGOAL_THEN `kle n a2 x \/ kle n x a2` MP_TAC THENL
       [ASM_MESON_TAC[ksimplex]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(~b ==> ~a) ==> b \/ a ==> b`) THEN
      DISCH_TAC THEN SUBGOAL_THEN `kle n a0 x` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:num->num = a0) \/ (x = a2)`
       (fun th -> ASM_MESON_TAC[KLE_REFL; th]) THEN
      MATCH_MP_TAC KLE_ADJACENT THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `ksimplex p n (a3 INSERT (s DELETE a0))` ASSUME_TAC THENL
     [MP_TAC(ASSUME `ksimplex p n s`) THEN REWRITE_TAC[ksimplex] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_DELETE; CARD_CLAUSES;
                 CARD_DELETE] THEN
        ASM_REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [DISCH_TAC THEN REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
        SUBGOAL_THEN `!j. (a3:num->num) j <= p`
         (fun th -> ASM_MESON_TAC[th]) THEN
        X_GEN_TAC `j:num` THEN ONCE_ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
         [ALL_TAC; ASM_MESON_TAC[]] THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        UNDISCH_TAC
         `~(?j. 1 <= j /\ j <= n /\
                (!x. x IN s DELETE a0 ==> (x j = (p:num))))` THEN
        REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
        REWRITE_TAC[ASSUME `1 <= k`; ASSUME `k:num <= n`; NOT_FORALL_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `a4:num->num` MP_TAC) THEN
        REWRITE_TAC[IN_DELETE; NOT_IMP] THEN STRIP_TAC THEN
        UNDISCH_TAC `!x. x IN s DELETE a0 ==> kle n a2 x` THEN
        DISCH_THEN(MP_TAC o SPEC `a4:num->num`) THEN
        ASM_REWRITE_TAC[IN_DELETE] THEN
        DISCH_THEN(MP_TAC o MATCH_MP KLE_IMP_POINTWISE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~((a4:num->num) k = p)` THEN
        SUBGOAL_THEN `(a4:num->num) k <= p` MP_TAC THENL
         [ASM_MESON_TAC[ksimplex]; ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_INSERT; IN_DELETE] THEN REPEAT STRIP_TAC THENL
         [ALL_TAC; ASM_MESON_TAC[]] THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        ONCE_ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      DISCH_TAC THEN REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
      SUBGOAL_THEN `!x. x IN s /\ ~(x = a0) ==> kle n x a3`
       (fun th -> ASM_MESON_TAC[th; KLE_REFL]) THEN
      X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `kle n a2 x /\ kle n x a1` MP_TAC THENL
       [ASM_MESON_TAC[IN_DELETE]; ALL_TAC] THEN
      REWRITE_TAC[IMP_CONJ] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP KLE_IMP_POINTWISE) THEN
      DISCH_TAC THEN REWRITE_TAC[kle] THEN
      DISCH_THEN(X_CHOOSE_THEN `kk:num->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(k:num) INSERT kk` THEN
      REWRITE_TAC[INSERT_SUBSET; IN_NUMSEG] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `j:num` THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[IN_INSERT] THEN ASM_CASES_TAC `j:num = k` THENL
       [ALL_TAC; ASM_MESON_TAC[]] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
       `a2 <= x ==> !a0. x <= a1 /\ (a1 = a0 + 1) /\ (a2 = a0 + 1)
             ==> (a1 + 1 = x + 1)`)) THEN
      EXISTS_TAC `(a0:num->num) k` THEN
      ASM_MESON_TAC[KLE_IMP_POINTWISE];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s':(num->num)->bool` THEN EQ_TAC THENL
     [ALL_TAC;
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `a3:num->num` THEN
      REWRITE_TAC[IN_INSERT; DELETE_INSERT] THEN
      UNDISCH_TAC `~((a3:num->num) IN s)` THEN SET_TAC[]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `a':num->num` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`p:num`; `n:num`; `s':(num->num)->bool`]
                 KSIMPLEX_EXTREMA_STRONG) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a_min:num->num` (X_CHOOSE_THEN `a_max:num->num`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a':num->num = a_min) \/ (a' = a_max)` MP_TAC THENL
     [MATCH_MP_TAC KSIMPLEX_FIX_PLANE THEN MAP_EVERY EXISTS_TAC
       [`p:num`; `(a2:num->num) k`; `n:num`;
        `k:num`; `s':(num->num)->bool`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
      X_GEN_TAC `x:num->num` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `kle n a2 x /\ kle n x a1` MP_TAC THENL
       [ASM_MESON_TAC[IN_DELETE]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `k:num` o MATCH_MP
        KLE_IMP_POINTWISE)) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC lemma THEN
      MAP_EVERY EXISTS_TAC [`a0:num->num`; `a_min:num->num`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `a_max:num->num = a1` MP_TAC THENL
       [SUBGOAL_THEN `a1:num->num IN (s' DELETE a_min) /\
                      a_max:num->num IN (s DELETE a0)`
        MP_TAC THENL
         [ASM_MESON_TAC[IN_DELETE]; ASM_MESON_TAC[KLE_ANTISYM; IN_DELETE]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      MESON_TAC[EQ_ADD_RCANCEL];
      DISJ2_TAC THEN MATCH_MP_TAC lemma THEN
      MAP_EVERY EXISTS_TAC [`a3:num->num`; `a_max:num->num`] THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN CONJ_TAC THENL
       [UNDISCH_TAC `~(a3:num->num IN s)` THEN SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `a_min:num->num = a2` MP_TAC THENL
       [SUBGOAL_THEN `a2:num->num IN (s' DELETE a_max) /\
                      a_min:num->num IN (s DELETE a0)`
        MP_TAC THENL
         [ASM_MESON_TAC[IN_DELETE]; ASM_MESON_TAC[KLE_ANTISYM; IN_DELETE]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      MESON_TAC[EQ_ADD_RCANCEL]];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:num->num = a1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`a1:num->num`; `p:num`; `n:num`; `s:(num->num)->bool`]
                 KSIMPLEX_PREDECESSOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~a /\ (b ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC `a0:num->num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP KLE_IMP_POINTWISE) THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; ARITH] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a2:num->num`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `!x. x IN (s DELETE a1) ==> kle n x a2` ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
      SUBGOAL_THEN `kle n a2 x \/ kle n x a2` MP_TAC THENL
       [ASM_MESON_TAC[ksimplex]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(~b ==> ~a) ==> a \/ b ==> b`) THEN
      DISCH_TAC THEN SUBGOAL_THEN `kle n x a1` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:num->num = a2) \/ (x = a1)`
       (fun th -> ASM_MESON_TAC[KLE_REFL; th]) THEN
      MATCH_MP_TAC KLE_ADJACENT THEN EXISTS_TAC `k:num` THEN
      REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(a2:num->num = a1)` ASSUME_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[ARITH_RULE `~(x + 1 = x)`];
      ALL_TAC] THEN
    ABBREV_TAC `a3 = \j:num. if j = k then a0 j - 1 else a0 j` THEN
    SUBGOAL_THEN `!j:num. a0(j) = if j = k then a3(j) + 1 else a3 j`
    ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN EXPAND_TAC "a3" THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[ARITH_RULE `(a = a - 1 + 1) <=> ~(a = 0)`] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `!j:num. a1 j = (if j = k then a2 j + 1 else a2 j)` THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `(0 + 1 = x + 1) <=> (x = 0)`] THEN DISCH_TAC THEN
      UNDISCH_TAC
       `~(?j. 1 <= j /\ j <= n /\ (!x. x IN s DELETE a1 ==> (x j = 0)))` THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN EXISTS_TAC `k:num` THEN
      ASM_MESON_TAC[KLE_IMP_POINTWISE; LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(kle n a0 a3)` ASSUME_TAC THENL
     [ASM_MESON_TAC[KLE_IMP_POINTWISE; ARITH_RULE `~(a + 1 <= a)`];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(a3:num->num IN s)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `kle n a3 a2` ASSUME_TAC THENL
     [SUBGOAL_THEN `kle n a0 a1` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[kle] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      ONCE_REWRITE_TAC[
        ASSUME `!j:num. a0 j = (if j = k then a3 j + 1 else a3 j)`;
        ASSUME `!j:num. a1 j = (if j = k then a2 j + 1 else a2 j)`] THEN
      REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `kle n a3 a0` ASSUME_TAC THENL
     [REWRITE_TAC[kle] THEN EXISTS_TAC `{k:num}` THEN
      ASM_REWRITE_TAC[SUBSET; IN_SING; IN_NUMSEG] THEN
      ASM_MESON_TAC[ADD_CLAUSES];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_CARD THEN CONV_TAC HAS_SIZE_CONV THEN
    MAP_EVERY EXISTS_TAC
     [`s:(num->num)->bool`; `a3 INSERT (s DELETE (a1:num->num))`] THEN
    SUBGOAL_THEN `~(a3:num->num = a1) /\ ~(a3 = a0)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC lemma_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `ksimplex p n (a3 INSERT (s DELETE a1))` ASSUME_TAC THENL
     [MP_TAC(ASSUME `ksimplex p n s`) THEN REWRITE_TAC[ksimplex] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_DELETE; CARD_CLAUSES;
                 CARD_DELETE] THEN
        ASM_REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [DISCH_TAC THEN REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
        SUBGOAL_THEN `!j. (a3:num->num) j <= p`
         (fun th -> ASM_MESON_TAC[th]) THEN
        X_GEN_TAC `j:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`a0:num->num`; `j:num`]) THEN
        ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_INSERT; IN_DELETE] THEN REPEAT STRIP_TAC THENL
         [ALL_TAC; ASM_MESON_TAC[]] THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        EXPAND_TAC "a3" THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      DISCH_TAC THEN REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
      SUBGOAL_THEN `!x. x IN s /\ ~(x = a1) ==> kle n a3 x`
       (fun th -> ASM_MESON_TAC[th; KLE_REFL]) THEN
      X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN
      MATCH_MP_TAC KLE_BETWEEN_L THEN
      MAP_EVERY EXISTS_TAC [`a0:num->num`; `a2:num->num`] THEN
      ASM_MESON_TAC[IN_DELETE];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s':(num->num)->bool` THEN EQ_TAC THENL
     [ALL_TAC;
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `a3:num->num` THEN
      REWRITE_TAC[IN_INSERT; DELETE_INSERT] THEN
      UNDISCH_TAC `~((a3:num->num) IN s)` THEN SET_TAC[]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `a':num->num` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`p:num`; `n:num`; `s':(num->num)->bool`]
                 KSIMPLEX_EXTREMA_STRONG) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a_min:num->num` (X_CHOOSE_THEN `a_max:num->num`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a':num->num = a_min) \/ (a' = a_max)` MP_TAC THENL
     [MATCH_MP_TAC KSIMPLEX_FIX_PLANE THEN MAP_EVERY EXISTS_TAC
       [`p:num`; `(a2:num->num) k`; `n:num`;
        `k:num`; `s':(num->num)->bool`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
      X_GEN_TAC `x:num->num` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `kle n a0 x /\ kle n x a2` MP_TAC THENL
       [ASM_MESON_TAC[IN_DELETE]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `k:num` o MATCH_MP
        KLE_IMP_POINTWISE)) THEN
      SUBGOAL_THEN `(a2:num->num) k <= a0 k`
        (fun th -> MP_TAC th THEN ARITH_TAC) THEN
      UNDISCH_TAC `!j:num. a1 j = (if j = k then a2 j + 1 else a2 j)` THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [DISJ2_TAC THEN MATCH_MP_TAC lemma THEN
      MAP_EVERY EXISTS_TAC [`a3:num->num`; `a_min:num->num`] THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN CONJ_TAC THENL
       [UNDISCH_TAC `~(a3:num->num IN s)` THEN SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `a_max:num->num = a2` MP_TAC THENL
       [SUBGOAL_THEN `a2:num->num IN (s' DELETE a_min) /\
                      a_max:num->num IN (s DELETE a1)`
        MP_TAC THENL
         [ASM_MESON_TAC[IN_DELETE]; ASM_MESON_TAC[KLE_ANTISYM; IN_DELETE]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!j. a2 j = if 1 <= j /\ j <= n then a3 j + 1 else a3 j`
       (fun th -> ASM_REWRITE_TAC[th; FUN_EQ_THM])
      THENL
       [ALL_TAC;
        MATCH_MP_TAC MONO_FORALL THEN MESON_TAC[EQ_ADD_RCANCEL]] THEN
      UNDISCH_TAC `!j:num. a1 j = (if j = k then a2 j + 1 else a2 j)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN
      MESON_TAC[EQ_ADD_RCANCEL];
      DISJ1_TAC THEN MATCH_MP_TAC lemma THEN
      MAP_EVERY EXISTS_TAC [`a1:num->num`; `a_max:num->num`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      SUBGOAL_THEN `a_min:num->num = a0` MP_TAC THENL
       [SUBGOAL_THEN `a0:num->num IN (s' DELETE a_max) /\
                      a_min:num->num IN (s DELETE a1)`
        MP_TAC THENL
         [ASM_MESON_TAC[IN_DELETE]; ASM_MESON_TAC[KLE_ANTISYM; IN_DELETE]];
        ALL_TAC] THEN
      UNDISCH_THEN `!j:num. a1 j = (if j = k then a2 j + 1 else a2 j)`
       (K ALL_TAC) THEN
      ASM_REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      MESON_TAC[EQ_ADD_RCANCEL]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:num->num`; `p:num`; `n:num`; `s:(num->num)->bool`]
        KSIMPLEX_PREDECESSOR) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~a /\ (b ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[KLE_ANTISYM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:num->num`
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:num->num`; `p:num`; `n:num`; `s:(num->num)->bool`]
        KSIMPLEX_SUCCESSOR) THEN
  REWRITE_TAC[ASSUME `ksimplex p n s`; ASSUME `a:num->num IN s`] THEN
  MATCH_MP_TAC(TAUT `~a /\ (b ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[KLE_ANTISYM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:num->num`
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `a' = \j:num. if j = l then u(j) + 1 else u(j)` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
  REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o GSYM) THEN
  SUBGOAL_THEN `~(k:num = l)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `!j:num. v j = (if j = l then a j + 1 else a j)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `l:num`) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ksimplex]) THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`u:num->num`; `v:num->num`]) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[kle] THEN
    DISCH_THEN(DISJ_CASES_THEN (CHOOSE_THEN (MP_TAC o SPEC `l:num` o
      CONJUNCT2))) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a':num->num = a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((a':num->num) IN s)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ksimplex]) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:num->num`; `a':num->num`] o
      last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP KLE_IMP_POINTWISE)) THENL
     [DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      DISCH_THEN(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `kle n u a /\ kle n u a' /\ kle n a v /\ kle n a' v`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[kle] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `{k:num}`;
      EXISTS_TAC `{l:num}`;
      EXISTS_TAC `{l:num}`;
      EXISTS_TAC `{k:num}`] THEN
    ASM_REWRITE_TAC[IN_SING; SUBSET; IN_NUMSEG] THEN
    ASM_MESON_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. kle n u x /\ kle n x v
                    ==> ((x = u) \/ (x = a) \/ (x = a') \/ (x = v))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:num->num` THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP KLE_IMP_POINTWISE)) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; IMP_IMP; AND_FORALL_THM] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    ASM_CASES_TAC `(x:num->num) k = u k` THEN
    ASM_CASES_TAC `(x:num->num) l = u l` THENL
     [DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th);
      DISCH_THEN(fun th -> DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
                           MP_TAC th);
      DISCH_THEN(fun th -> DISJ2_TAC THEN DISJ1_TAC THEN MP_TAC th);
      DISCH_THEN(fun th -> REPEAT DISJ2_TAC THEN MP_TAC th)] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `j:num` THEN
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[LE_ANTISYM;
       ARITH_RULE `x <= u + 1 /\ u <= x <=> (x = u) \/ (x = u + 1)`]);
    ALL_TAC] THEN
  SUBGOAL_THEN `kle n u v` ASSUME_TAC THENL
   [ASM_MESON_TAC[KLE_TRANS; ksimplex]; ALL_TAC] THEN
  SUBGOAL_THEN `ksimplex p n (a' INSERT (s DELETE a))` ASSUME_TAC THENL
   [MP_TAC(ASSUME `ksimplex p n s`) THEN REWRITE_TAC[ksimplex] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_DELETE; CARD_CLAUSES;
               CARD_DELETE; IN_DELETE] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
      SIMP_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `j:num` THEN MP_TAC th) THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `v:num->num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
      REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
      SIMP_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[EXISTS_REFL; LEFT_FORALL_IMP_THM] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
    SUBGOAL_THEN
     `!x. x IN s /\ kle n v x ==> kle n a' x`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN
      MATCH_MP_TAC KLE_BETWEEN_R THEN
      MAP_EVERY EXISTS_TAC [`u:num->num`; `v:num->num`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ksimplex; KLE_TRANS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN s /\ kle n x u ==> kle n x a'`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN
      MATCH_MP_TAC KLE_BETWEEN_L THEN
      MAP_EVERY EXISTS_TAC [`u:num->num`; `v:num->num`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ksimplex; KLE_TRANS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN s /\ ~(x = a) ==> kle n a' x \/ kle n x a'`
     (fun th -> MESON_TAC[th; KLE_REFL; ASSUME `(a:num->num) IN s`]) THEN
    X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `kle n v x` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `kle n x u` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:num->num = u) \/ (x = a) \/ (x = a') \/ (x = v)`
     (fun th -> ASM_MESON_TAC[th; KLE_REFL]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[ksimplex];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_CARD THEN CONV_TAC HAS_SIZE_CONV THEN
  MAP_EVERY EXISTS_TAC
   [`s:(num->num)->bool`; `a' INSERT (s DELETE (a:num->num))`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DELETE; IN_INSERT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `s':(num->num)->bool` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `a':num->num` THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE] THEN ASM_MESON_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `a'':num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:num->num) IN s' \/ a' IN s'` MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN DISCH_TAC THEN
    MP_TAC(ASSUME `s' DELETE a'' = s DELETE (a:num->num)`) THEN
    REWRITE_TAC[EXTENSION] THEN
    DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THENL
     [DISCH_THEN(MP_TAC o SPEC `a:num->num`);
      DISCH_THEN(MP_TAC o SPEC `a':num->num`)] THEN
    REWRITE_TAC[IN_DELETE] THEN ASM_REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `~(u:num->num = v)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `l:num`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(kle n v u)` ASSUME_TAC THENL
   [ASM_MESON_TAC[KLE_ANTISYM]; ALL_TAC] THEN
  SUBGOAL_THEN `~(u:num->num = a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v:num->num = a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `l:num`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u:num->num IN s' /\ v IN s'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTENSION; IN_DELETE]; ALL_TAC] THEN
  ASM_CASES_TAC
   `!x. x IN s' ==> kle n x u \/ kle n v x`
  THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:num->num` MP_TAC) THEN
    REWRITE_TAC[NOT_IMP; DE_MORGAN_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:num->num = u) \/ (w = a) \/ (w = a') \/ (w = v)`
     (fun th -> ASM_MESON_TAC[KLE_REFL; th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[ksimplex]] THEN
  MP_TAC(SPECL [`u:num->num`; `p:num`; `n:num`; `s':(num->num)->bool`]
               KSIMPLEX_SUCCESSOR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[EXTENSION; IN_DELETE]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (MP_TAC o SPEC `v:num->num`) MP_TAC) THENL
   [ASM_MESON_TAC[EXTENSION; IN_DELETE]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  UNDISCH_TAC `!x. x IN s' ==> kle n x u \/ kle n v x` THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `w:num->num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN(MP_TAC o MATCH_MP KLE_IMP_POINTWISE)) THEN
  ASM_REWRITE_TAC[] THENL
   [MESON_TAC[ARITH_RULE `~(i + 1 <= i)`]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `k:num` th) THEN
                       MP_TAC(SPEC `l:num` th)) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN TRY ARITH_TAC THEN
  UNDISCH_TAC `~(k:num = l)` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence another step towards concreteness.                                  *)
(* ------------------------------------------------------------------------- *)

let KUHN_SIMPLEX_LEMMA = prove
 (`!p n. (!s. ksimplex p (n + 1) s ==> (IMAGE rl s SUBSET 0..n+1)) /\
         ODD(CARD{f | (?s a. ksimplex p (n + 1) s /\
                             a IN s /\
                             (f = s DELETE a)) /\
                      (IMAGE rl f = 0 .. n) /\
                      ((?j. 1 <= j /\ j <= n + 1 /\
                            !x. x IN f ==> (x j = 0)) \/
                       (?j. 1 <= j /\ j <= n + 1 /\
                            !x. x IN f ==> (x j = p)))})
         ==>  ODD(CARD {s | s IN {s | ksimplex p (n + 1) s} /\
                            (IMAGE rl s = 0..n+1)})`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `ODD(CARD {f | f IN {f | ?s. s IN {s | ksimplex p (n + 1) s} /\
                             (?a. a IN s /\ (f = s DELETE a))} /\
               (IMAGE rl f = 0..n) /\
               ((?j. 1 <= j /\ j <= n + 1 /\ !x. x IN f ==> (x j = 0)) \/
                (?j. 1 <= j /\ j <= n + 1 /\ !x. x IN f ==> (x j = p)))})`
  MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; RIGHT_AND_EXISTS_THM]; ALL_TAC] THEN
  MATCH_MP_TAC KUHN_COMPLETE_LEMMA THEN  REWRITE_TAC[FINITE_SIMPLICES] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[ksimplex; ARITH_RULE `(n + 1) + 1 = n + 2`];
    ASM_SIMP_TAC[];
    MATCH_MP_TAC KSIMPLEX_REPLACE_0;
    MATCH_MP_TAC KSIMPLEX_REPLACE_1;
    MATCH_MP_TAC KSIMPLEX_REPLACE_2] THEN
  ASM_MESON_TAC[ARITH_RULE `~(n + 1 = 0)`]);;

(* ------------------------------------------------------------------------- *)
(* Reduced labelling.                                                        *)
(* ------------------------------------------------------------------------- *)

let reduced = new_definition
 `reduced label n (x:num->num) =
     @k. k <= n /\
         (!i. 1 <= i /\ i < k + 1 ==> (label x i = 0)) /\
         ((k = n) \/ ~(label x (k + 1) = 0))`;;

let REDUCED_LABELLING = prove
 (`!label x n.
      reduced label n x <= n /\
      (!i. 1 <= i /\ i < reduced label n x + 1 ==> (label x i = 0)) /\
      ((reduced label n x = n) \/ ~(label x (reduced label n x + 1) = 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reduced] THEN CONV_TAC SELECT_CONV THEN
  MP_TAC(SPEC `\j. j <= n /\ ~(label (x:num->num) (j + 1) = 0) \/ (n = j)`
     num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
  ASM_CASES_TAC `k = n:num` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LE_REFL] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
  SIMP_TAC[LT_IMP_LE] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i /\ i < n + 1 ==> i - 1 < n`] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i /\ i < n + 1 ==> ~(n = i - 1)`] THEN
  ASM_SIMP_TAC[SUB_ADD] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  ARITH_TAC);;

let REDUCED_LABELLING_UNIQUE = prove
 (`!label x n.
      r <= n /\
      (!i. 1 <= i /\ i < r + 1 ==> (label x i = 0)) /\
      ((r = n) \/ ~(label x (r + 1) = 0))
      ==> (reduced label n x = r)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC(SPECL
        [`label:(num->num)->(num->num)`; `x:num->num`; `n:num`]
        REDUCED_LABELLING) THEN
  MATCH_MP_TAC(ARITH_RULE `~(a < b) /\ ~(b < a:num) ==> (a = b)`) THEN
  ASM_MESON_TAC[ARITH_RULE `s < r:num /\ r <= n ==> ~(s = n)`;
                ARITH_RULE `s < r ==> 1 <= s + 1 /\ s + 1 < r + 1`]);;

let REDUCED_LABELLING_0 = prove
 (`!label n x j.
        1 <= j /\ j <= n /\ (label x j = 0)
        ==> ~(reduced label n x = j - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`label:(num->num)->num->num`; `x:num->num`; `n:num`]
               REDUCED_LABELLING) THEN
  ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `1 <= j /\ j <= n ==> ~(j - 1 = n)`]);;

let REDUCED_LABELLING_1 = prove
 (`!label n x j.
        1 <= j /\ j <= n /\ ~(label x j = 0)
        ==> reduced label n x < j`,
  REWRITE_TAC[GSYM NOT_LE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`label:(num->num)->num->num`; `x:num->num`; `n:num`]
               REDUCED_LABELLING) THEN
  DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[ARITH_RULE `y < x + 1 <=> (y <= x)`]);;

let REDUCED_LABELLING_SUC = prove
 (`!lab n x.
        ~(reduced lab (n + 1) x = n + 1)
        ==> (reduced lab (n + 1) x = reduced lab n x)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REDUCED_LABELLING_UNIQUE THEN
  ASM_MESON_TAC[REDUCED_LABELLING; ARITH_RULE
   `x <= n + 1 /\ ~(x = n + 1) ==> x <= n`]);;

let COMPLETE_FACE_TOP = prove
 (`!lab f n.
         (!x j. x IN f /\ 1 <= j /\ j <= n + 1 /\ (x j = 0)
                ==> (lab x j = 0)) /\
         (!x j. x IN f /\ 1 <= j /\ j <= n + 1 /\ (x j = p)
                ==> (lab x j = 1))
         ==> ((IMAGE (reduced lab (n + 1)) f = 0..n) /\
              ((?j. 1 <= j /\ j <= n + 1 /\ !x. x IN f ==> (x j = 0)) \/
               (?j. 1 <= j /\ j <= n + 1 /\ !x. x IN f ==> (x j = p))) <=>
              (IMAGE (reduced lab (n + 1)) f = 0..n) /\
              (!x. x IN f ==> (x (n + 1) = p)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[ARITH_RULE `1 <= n + 1`; LE_REFL]] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THENL
   [DISCH_THEN(MP_TAC o SPEC `j - 1`) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[IN_IMAGE; IN_NUMSEG; LE_0; NOT_EXISTS_THM;
                 ARITH_RULE `j <= n + 1 ==> j - 1 <= n`] THEN
    ASM_MESON_TAC[REDUCED_LABELLING_0];
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0; NOT_LE] THEN
    ASM_SIMP_TAC[ARITH_RULE `j <= n + 1 ==> ((j <= n) <=> ~(j = n + 1))`] THEN
    ASM_MESON_TAC[REDUCED_LABELLING_1; ARITH_RULE `~(1 = 0)`; LT_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Hence we get just about the nice induction.                               *)
(* ------------------------------------------------------------------------- *)

let KUHN_INDUCTION = prove
 (`!p n. 0 < p /\
         (!x j. (!j. x(j) <= p) /\ 1 <= j /\ j <= n + 1 /\ (x j = 0)
                ==> (lab x j = 0)) /\
         (!x j. (!j. x(j) <= p) /\ 1 <= j /\ j <= n + 1 /\ (x j = p)
                ==> (lab x j = 1))
         ==> ODD(CARD {f | ksimplex p n f /\
                           (IMAGE (reduced lab n) f = 0..n)})
             ==> ODD(CARD {s | ksimplex p (n + 1) s /\
                           (IMAGE (reduced lab (n + 1)) s = 0..n+1)})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IN_ELIM_THM] KUHN_SIMPLEX_LEMMA) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; LE_0] THEN
    MESON_TAC[ARITH_RULE `x <= n ==> x <= n + 1`; REDUCED_LABELLING];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC th THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC) THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `f:(num->num)->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC
   `(!x j. x IN f /\ 1 <= j /\ j <= n + 1 /\ (x j = 0) ==> (lab x j = 0)) /\
    (!x j. x IN f /\ 1 <= j /\ j <= n + 1 /\ (x j = p) ==> (lab x j = 1))`
  THENL
   [ALL_TAC;
    MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a /\ c <=> b /\ d)`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN REWRITE_TAC[ksimplex] THEN
    ASM_MESON_TAC[IN_DELETE]] THEN
  ASM_SIMP_TAC[COMPLETE_FACE_TOP] THEN
  ASM_CASES_TAC `!x. x IN f ==> (x(n + 1):num = p)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[ksimplex] THEN
    ASM_MESON_TAC[ARITH_RULE `~(n + 1 <= n)`]] THEN
  ASM_SIMP_TAC[SIMPLEX_TOP_FACE] THEN
  ASM_CASES_TAC `ksimplex p n f` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `x:num->num` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:num->num) IN f` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REDUCED_LABELLING_SUC THEN
  MATCH_MP_TAC(ARITH_RULE `a:num < b ==> ~(a = b)`) THEN
  MATCH_MP_TAC REDUCED_LABELLING_1 THEN
  REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= n + 1`] THEN
  MATCH_MP_TAC(ARITH_RULE `(n = 1) ==> ~(n = 0)`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= n + 1`] THEN
  ASM_MESON_TAC[ksimplex]);;

(* ------------------------------------------------------------------------- *)
(* And so we get the final combinatorial result.                             *)
(* ------------------------------------------------------------------------- *)

let KSIMPLEX_0 = prove
 (`ksimplex p 0 s <=> (s = {(\x. p)})`,
  REWRITE_TAC[ksimplex; ADD_CLAUSES] THEN
  CONV_TAC(LAND_CONV(LAND_CONV HAS_SIZE_CONV)) THEN
  REWRITE_TAC[ARITH_RULE `1 <= j /\ j <= 0 <=> F`] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN REWRITE_TAC[IN_SING] THEN
  SIMP_TAC[RIGHT_FORALL_IMP_THM] THEN REWRITE_TAC[KLE_REFL] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[AND_FORALL_THM; ARITH_RULE
   `x <= y:num /\ (x = y) <=> (x = y)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  REWRITE_TAC[GSYM FUN_EQ_THM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[UNWIND_THM2]);;

let REDUCE_LABELLING_0 = prove
 (`!lab x. reduced lab 0 x = 0`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REDUCED_LABELLING_UNIQUE THEN
  REWRITE_TAC[LE_REFL] THEN ARITH_TAC);;

let KUHN_COMBINATORIAL = prove
 (`!lab p n.
         0 < p /\
         (!x j. (!j. x(j) <= p) /\ 1 <= j /\ j <= n /\ (x j = 0)
                ==> (lab x j = 0)) /\
         (!x j. (!j. x(j) <= p) /\ 1 <= j /\ j <= n  /\ (x j = p)
                ==> (lab x j = 1))
         ==> ODD(CARD {s | ksimplex p n s /\
                           (IMAGE (reduced lab n) s = 0..n)})`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN
    SUBGOAL_THEN `{s | ksimplex p 0 s /\ (IMAGE (reduced lab 0) s = 0 .. 0)} =
                  {{(\x. p)}}`
     (fun th -> SIMP_TAC[CARD_CLAUSES; NOT_IN_EMPTY;
                         FINITE_RULES; th; ARITH]) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; KSIMPLEX_0; IN_SING] THEN
    GEN_TAC THEN MATCH_MP_TAC(TAUT `(a ==> b) ==> (a /\ b <=> a)`) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[NUMSEG_SING; EXTENSION; IN_SING; IN_IMAGE] THEN
    REWRITE_TAC[REDUCE_LABELLING_0] THEN MESON_TAC[];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `j <= n ==> j <= SUC n`];
      ALL_TAC] THEN
    REWRITE_TAC[ADD1] THEN MATCH_MP_TAC KUHN_INDUCTION THEN
    ASM_REWRITE_TAC[GSYM ADD1]]);;

let KUHN_LEMMA = prove
 (`!n p label.
        0 < p /\ 0 < n /\
        (!x. (!i. 1 <= i /\ i <= n ==> x(i) <= p)
             ==> !i. 1 <= i /\ i <= n ==> (label x i = 0) \/ (label x i = 1)) /\
        (!x. (!i. 1 <= i /\ i <= n ==> x(i) <= p)
             ==> !i. 1 <= i /\ i <= n /\ (x i = 0) ==> (label x i = 0)) /\
        (!x. (!i. 1 <= i /\ i <= n ==> x(i) <= p)
             ==> !i. 1 <= i /\ i <= n /\ (x i = p) ==> (label x i = 1))
        ==> ?q. (!i. 1 <= i /\ i <= n ==> q(i) < p) /\
                (!i. 1 <= i /\ i <= n
                     ==> ?r s. (!j. 1 <= j /\ j <= n
                                    ==> q(j) <= r(j) /\ r(j) <= q(j) + 1) /\
                               (!j. 1 <= j /\ j <= n
                                    ==> q(j) <= s(j) /\ s(j) <= q(j) + 1) /\
                               ~(label r i = label s i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`label:(num->num)->num->num`; `p:num`; `n:num`]
               KUHN_COMBINATORIAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC
   `{s | ksimplex p n s /\ (IMAGE (reduced label n) s = 0 .. n)} = {}`
  THENL [ASM_REWRITE_TAC[CARD_CLAUSES; ARITH]; ALL_TAC] THEN
  DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(num->num)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`p:num`; `n:num`; `s:(num->num)->bool`]
               KSIMPLEX_EXTREMA_STRONG) THEN
  ASM_REWRITE_TAC[GSYM LT_NZ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:num->num` THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->num` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x + 1 <= y ==> x < y`) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(b:num->num) i` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_MESON_TAC[ksimplex];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (reduced label n) s = 0 .. n` THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `i - 1` th) THEN MP_TAC(SPEC `i:num` th)) THEN
  ASM_REWRITE_TAC[IN_NUMSEG; LE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:num->num` (STRIP_ASSUME_TAC o GSYM)) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i /\ i <= n ==> i - 1 <= n`] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:num->num` (STRIP_ASSUME_TAC o GSYM)) THEN
  MAP_EVERY EXISTS_TAC [`u:num->num`; `v:num->num`] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_IMP_POINTWISE]; ALL_TAC] THEN
  MP_TAC(SPECL [`label:(num->num)->num->num`; `u:num->num`; `n:num`]
                REDUCED_LABELLING) THEN
  MP_TAC(SPECL [`label:(num->num)->num->num`; `v:num->num`; `n:num`]
                REDUCED_LABELLING) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i /\ i <= n ==> ~(i - 1 = n)`] THEN
  ASM_SIMP_TAC[SUB_ADD] THEN ASM_MESON_TAC[ARITH_RULE `i < i + 1`]);;

(* ------------------------------------------------------------------------- *)
(* The main result for the unit cube.                                        *)
(* ------------------------------------------------------------------------- *)

let BROUWER_CUBE = prove
 (`!f:real^N->real^N.
        f continuous_on (interval [vec 0,vec 1]) /\
        IMAGE f (interval [vec 0,vec 1]) SUBSET (interval [vec 0,vec 1])
        ==> ?x. x IN interval[vec 0,vec 1] /\ (f x = x)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `n = dimindex(:N)` THEN
  SUBGOAL_THEN `1 <= n /\ 0 < n /\ ~(n = 0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[DIMINDEX_NONZERO; DIMINDEX_GE_1] THEN
    ASM_MESON_TAC[LT_NZ; DIMINDEX_NONZERO];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~ p`] THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
  DISCH_TAC THEN SUBGOAL_THEN
   `?d. &0 < d /\ !x:real^N. x IN interval[vec 0,vec 1] ==> d <= norm(f x - x)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC BROUWER_COMPACTNESS_LEMMA THEN
    ASM_SIMP_TAC[COMPACT_INTERVAL; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
                 CONTINUOUS_ON_ID] THEN
    ASM_MESON_TAC[VECTOR_SUB_EQ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  FREEZE_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th))
        (SPEC `f:real^N->real^N` KUHN_LABELLING_LEMMA) THEN
  DISCH_THEN(MP_TAC o SPEC `\i. 1 <= i /\ i <= n`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_INTERVAL; VEC_COMPONENT]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `label:real^N->num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x y i. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1] /\
            1 <= i /\ i <= n /\ ~(label (x:real^N) i :num = label y i)
            ==> abs((f(x) - x)$i) <= norm(f(y) - f(x)) + norm(y - x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(((f:real^N->real^N)(y) - f(x))$i) + abs((y - x)$i)` THEN
    ASM_SIMP_TAC[REAL_LE_ADD2; COMPONENT_LE_NORM] THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x y fx fy d. (x <= fx /\ fy <= y \/ fx <= x /\ y <= fy)
             ==> abs(fx - x) <= abs(fy - fx) + abs(y - x)`) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `~(a = b)
      ==> a <= 1 /\ b <= 1 ==> (a = 0) /\ (b = 1) \/ (a = 1) /\ (b = 0)`)) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e. &0 < e /\
        !x y z i. x IN interval[vec 0,vec 1] /\
                  y IN interval[vec 0,vec 1] /\
                  z IN interval[vec 0,vec 1] /\
                  1 <= i /\ i <= n /\
                  norm(x - z) < e /\ norm(y - z) < e /\
                  ~(label (x:real^N) i :num = label y i)
                  ==> abs((f(z) - z)$i) < d / &n`
  MP_TAC THENL
   [SUBGOAL_THEN
     `(f:real^N->real^N) uniformly_continuous_on interval[vec 0,vec 1]`
    MP_TAC THENL
     [ASM_SIMP_TAC[COMPACT_UNIFORMLY_CONTINUOUS; COMPACT_INTERVAL];
      ALL_TAC] THEN
    REWRITE_TAC[uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `d / &n / &8`) THEN
    SUBGOAL_THEN `&0 < d / &n / &8` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LT_MULT; ARITH];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[dist] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min (e / &2) (d / &n / &8)` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_MIN; REAL_HALF] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `z:real^N`; `i:num`] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x fx n1 n2 n3 n4 d4.
        abs(fx - x) <= n1 + n2 /\
        abs(fx - fz) <= n3 /\ abs(x - z) <= n4 /\
        n1 < d4 /\ n2 < &2 * d4 /\ n3 < d4 /\ n4 < d4 /\ (&8 * d4 = d)
        ==> abs(fz - z) < d`) THEN
    MAP_EVERY EXISTS_TAC
     [`(x:real^N)$i`; `(f:real^N->real^N)(x)$i`;
      `norm((f:real^N->real^N) y - f x)`; `norm(y - x:real^N)`;
      `norm((f:real^N->real^N) x - f z)`;
      `norm(x - z:real^N)`; `d / &n / &8`] THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM] THEN
    SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm(x - z:real^N) + norm(y - z)` THEN
      ASM_SIMP_TAC[REAL_ARITH `a < e / &2 /\ b < e / &2 /\
                               (&2 * (e / &2) = e) ==> a + b < e`;
                   REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[GSYM dist] THEN MESON_TAC[DIST_TRIANGLE; DIST_SYM];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm(x - z:real^N) + norm(y - z)` THEN
      ASM_SIMP_TAC[REAL_ARITH `a < e /\ b < e ==> a + b < &2 * e`] THEN
      REWRITE_TAC[GSYM dist] THEN MESON_TAC[DIST_TRIANGLE; DIST_SYM];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH
        `a < e / &2 /\ &0 < e /\ (&2 * (e / &2) = e) ==> a < e`) THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  X_CHOOSE_THEN `p:num` MP_TAC (SPEC `&1 + &n / e` REAL_ARCH_SIMPLE) THEN
  DISJ_CASES_TAC(ARITH_RULE `(p = 0) \/ 0 < p`) THENL
   [DISCH_THEN(fun th -> DISCH_THEN(K ALL_TAC) THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[LT_REFL; REAL_NOT_LE] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT;
                 REAL_ARITH `&0 < x ==> &0 < &1 + x`];
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[NOT_FORALL_THM] THEN
  MP_TAC(SPECL [`n:num`; `p:num`;
            `\v:(num->num). label((lambda i. &(v i) / &p):real^N):num->num`]
               KUHN_LEMMA) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(x = 0) \/ (x = 1) <=> x <= 1`] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; IN_INTERVAL; VEC_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_MUL_LZERO; REAL_MUL_LID;
                 REAL_LT_IMP_NZ; REAL_OF_NUM_LT] THEN
    ASM_REWRITE_TAC[LE_0; REAL_OF_NUM_LE] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->num` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC BINDER_CONV [SWAP_EXISTS_THM] THEN
  GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
  ABBREV_TAC `z:real^N = lambda i. &(q i) / &p` THEN EXISTS_TAC `z:real^N` THEN
  REWRITE_TAC[TAUT `~(a ==> b) <=> ~b /\ a`] THEN
  GEN_REWRITE_TAC BINDER_CONV [SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  SUBGOAL_THEN `z:real^N IN interval[vec 0,vec 1]` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; VEC_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
    ASM_SIMP_TAC[LE_0; LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= n /\ d / &n <= abs((f z - z:real^N)$i)`
  MP_TAC THENL
   [SUBGOAL_THEN `d <= norm(f z - z:real^N)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
     `sum(1..dimindex(:N)) (\i. abs((f z - z:real^N)$i))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_BOUND_LT_GEN THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; NUMSEG_EMPTY; CARD_NUMSEG] THEN
    ASM_REWRITE_TAC[NOT_LT; ADD_SUB];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_NOT_LT] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` (X_CHOOSE_THEN `s:num->num`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(lambda i. &(r i) / &p) :real^N` THEN
  EXISTS_TAC `(lambda i. &(s i) / &p) :real^N` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; VEC_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
    ASM_MESON_TAC[LE_0; ARITH_RULE `r <= q + 1 /\ q < p ==> r <= p`];
    SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; VEC_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
    ASM_MESON_TAC[LE_0; ARITH_RULE `r <= q + 1 /\ q < p ==> r <= p`];
    ALL_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(MATCH_MP (REAL_ARITH `a <= b ==> b < e ==> a < e`)
                        (SPEC_ALL NORM_LE_L1)) THEN
  MATCH_MP_TAC SUM_BOUND_LT_GEN THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; NUMSEG_EMPTY; CARD_NUMSEG] THEN
  ASM_REWRITE_TAC[NOT_LT; ADD_SUB] THEN EXPAND_TAC "z" THEN
  EXPAND_TAC "n" THEN SIMP_TAC[VECTOR_SUB_COMPONENT; LAMBDA_BETA] THEN
  ASM_REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div; REAL_ABS_DIV; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&1` THEN
  ASM_SIMP_TAC[REAL_ARITH `q <= r /\ r <= q + &1 ==> abs(r - q) <= &1`;
               REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN
  REWRITE_TAC[REAL_INV_DIV; REAL_INV_MUL] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ;
               REAL_OF_NUM_LT; ARITH] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_OF_NUM_LT] THEN
  REWRITE_TAC[REAL_INV_1; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_ARITH `&1 + x <= y ==> x < y`]);;

(* ------------------------------------------------------------------------- *)
(* Retractions.                                                              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("retract_of",(12,"right"));;

let retraction = new_definition
  `retraction (s,t) (r:real^N->real^N) <=>
        t SUBSET s /\ r continuous_on s /\ (IMAGE r s SUBSET t) /\
        (!x. x IN t ==> (r x = x))`;;

let retract_of = new_definition
  `t retract_of s <=> ?r. retraction (s,t) r`;;

let RETRACTION = prove
 (`!s t r. retraction (s,t) r <=>
           t SUBSET s /\
           r continuous_on s /\
           IMAGE r s = t /\
           (!x. x IN t ==> r x = x)`,
  REWRITE_TAC[retraction] THEN SET_TAC[]);;

let RETRACT_OF_IMP_EXTENSIBLE = prove
 (`!f:real^M->real^N u s t.
        s retract_of t /\ f continuous_on s /\ IMAGE f s SUBSET u
        ==> ?g. g continuous_on t /\ IMAGE g t SUBSET u /\
                (!x. x IN s ==> g x = f x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[RETRACTION; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^M->real^M` THEN STRIP_TAC THEN
  EXISTS_TAC `(f:real^M->real^N) o (r:real^M->real^M)` THEN
  REWRITE_TAC[IMAGE_o; o_THM] THEN
  CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE; ASM SET_TAC[]] THEN
  ASM_MESON_TAC[]);;

let RETRACTION_IDEMPOTENT = prove
 (`!r s t. retraction (s,t) r ==> !x. x IN s ==> (r(r(x)) = r(x))`,
  REWRITE_TAC[retraction; SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[]);;

let IDEMPOTENT_IMP_RETRACTION = prove
 (`!f:real^N->real^N s.
        f continuous_on s /\ IMAGE f s SUBSET s /\
        (!x. x IN s ==> f(f x) = f x)
        ==> retraction (s,IMAGE f s) f`,
  REWRITE_TAC[retraction] THEN SET_TAC[]);;

let RETRACTION_SUBSET = prove
 (`!r s s' t. retraction (s,t) r /\ t SUBSET s' /\ s' SUBSET s
              ==> retraction (s',t) r`,
  SIMP_TAC[retraction] THEN
  MESON_TAC[IMAGE_SUBSET; SUBSET_TRANS; CONTINUOUS_ON_SUBSET]);;

let RETRACT_OF_SUBSET = prove
 (`!s s' t. t retract_of s /\ t SUBSET s' /\ s' SUBSET s
            ==> t retract_of s'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[retract_of; LEFT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[RETRACTION_SUBSET]);;

let RETRACT_OF_TRANSLATION = prove
 (`!a t s:real^N->bool.
        t retract_of s
        ==> (IMAGE (\x. a + x) t) retract_of (IMAGE (\x. a + x) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of; retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(\x:real^N. a + x) o r o (\x:real^N. --a + x)` THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
     SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]) THEN
    ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `--a + a + x:real^N = x`;
                    IMAGE_ID];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM IMAGE_o] THEN
    ASM_REWRITE_TAC[o_DEF; VECTOR_ARITH `--a + a + x:real^N = x`; IMAGE_ID];
    ASM_SIMP_TAC[o_DEF; VECTOR_ARITH `--a + a + x:real^N = x`]]);;

let RETRACT_OF_TRANSLATION_EQ = prove
 (`!a t s:real^N->bool.
        (IMAGE (\x. a + x) t) retract_of (IMAGE (\x. a + x) s) <=>
        t retract_of s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[RETRACT_OF_TRANSLATION] THEN
  DISCH_THEN(MP_TAC o SPEC `--a:real^N` o MATCH_MP RETRACT_OF_TRANSLATION) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID;
              VECTOR_ARITH `--a + a + x:real^N = x`]);;

add_translation_invariants [RETRACT_OF_TRANSLATION_EQ];;

let RETRACT_OF_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y) /\ t retract_of s
        ==> (IMAGE f t) retract_of (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[retract_of; retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^M->real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:real^M->real^N) o r o (g:real^N->real^M)` THEN
  UNDISCH_THEN `!x y. (f:real^M->real^N) x = f y ==> x = y` (K ALL_TAC) THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
           ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON]) THEN
    ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM IMAGE_o] THEN
    ASM_REWRITE_TAC[o_DEF; IMAGE_ID];
    ASM_SIMP_TAC[o_DEF]]);;

let RETRACT_OF_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> ((IMAGE f t) retract_of (IMAGE f s) <=> t retract_of s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[RETRACT_OF_INJECTIVE_LINEAR_IMAGE]] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^N->real^M` STRIP_ASSUME_TAC o
        MATCH_MP LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE) THEN
  SUBGOAL_THEN
   `!s. s = IMAGE (h:real^N->real^M) (IMAGE (f:real^M->real^N) s)`
   (fun th -> ONCE_REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC RETRACT_OF_INJECTIVE_LINEAR_IMAGE THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

add_linear_invariants [RETRACT_OF_LINEAR_IMAGE_EQ];;

let RETRACTION_REFL = prove
 (`!s. retraction (s,s) (\x. x)`,
  REWRITE_TAC[retraction; IMAGE_ID; SUBSET_REFL; CONTINUOUS_ON_ID]);;

let RETRACT_OF_REFL = prove
 (`!s. s retract_of s`,
  REWRITE_TAC[retract_of] THEN MESON_TAC[RETRACTION_REFL]);;

let RETRACT_OF_IMP_SUBSET = prove
 (`!s t. s retract_of t ==> s SUBSET t`,
  SIMP_TAC[retract_of; retraction] THEN MESON_TAC[]);;

let RETRACT_OF_EMPTY = prove
 (`(!s:real^N->bool. {} retract_of s <=> s = {}) /\
   (!s:real^N->bool. s retract_of {} <=> s = {})`,
  REWRITE_TAC[retract_of; retraction; SUBSET_EMPTY; IMAGE_CLAUSES] THEN
  CONJ_TAC THEN X_GEN_TAC `s:real^N->bool` THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; IMAGE_EQ_EMPTY; CONTINUOUS_ON_EMPTY;
                  SUBSET_REFL]);;

let RETRACT_OF_SING = prove
 (`!s x:real^N. {x} retract_of s <=> x IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of; RETRACTION] THEN EQ_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `(\y. x):real^N->real^N` THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[]);;

let RETRACTION_o = prove
 (`!f g s t u:real^N->bool.
        retraction (s,t) f /\ retraction (t,u) g
        ==> retraction (s,u) (g o f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retraction] THEN REPEAT STRIP_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[]]);;

let RETRACT_OF_TRANS = prove
 (`!s t u:real^N->bool.
        s retract_of t /\ t retract_of u ==> s retract_of u`,
  REWRITE_TAC[retract_of] THEN MESON_TAC[RETRACTION_o]);;

let CLOSED_IN_RETRACT = prove
 (`!s t:real^N->bool.
        s retract_of t ==> closed_in (subtopology euclidean t) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of; retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `s = {x:real^N | x IN t /\ lift(norm(r x - x)) = vec 0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP; NORM_EQ_0] THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_SIMP_TAC[CONTINUOUS_ON_ID]]);;

let RETRACT_OF_CONTRACTIBLE = prove
 (`!s t:real^N->bool. contractible t /\ s retract_of t ==> contractible s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contractible; retract_of] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `r:real^N->real^N`)) THEN
  SIMP_TAC[HOMOTOPIC_WITH; PCROSS; LEFT_IMP_EXISTS_THM] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [retraction]) THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `h:real^(1,N)finite_sum->real^N`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`(r:real^N->real^N) a`;
    `(r:real^N->real^N) o (h:real^(1,N)finite_sum->real^N)`] THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o; SUBSET] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
           CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let RETRACT_OF_COMPACT = prove
 (`!s t:real^N->bool. compact t /\ s retract_of t ==> compact s`,
  REWRITE_TAC[retract_of; RETRACTION] THEN
  MESON_TAC[COMPACT_CONTINUOUS_IMAGE]);;

let RETRACT_OF_CLOSED = prove
 (`!s t. closed t /\ s retract_of t ==> closed s`,
  MESON_TAC[CLOSED_IN_CLOSED_EQ; CLOSED_IN_RETRACT]);;

let RETRACT_OF_CONNECTED = prove
 (`!s t:real^N->bool. connected t /\ s retract_of t ==> connected s`,
  REWRITE_TAC[retract_of; RETRACTION] THEN
  MESON_TAC[CONNECTED_CONTINUOUS_IMAGE]);;

let RETRACT_OF_PATH_CONNECTED = prove
 (`!s t:real^N->bool. path_connected t /\ s retract_of t ==> path_connected s`,
  REWRITE_TAC[retract_of; RETRACTION] THEN
  MESON_TAC[PATH_CONNECTED_CONTINUOUS_IMAGE]);;

let RETRACT_OF_SIMPLY_CONNECTED = prove
 (`!s t:real^N->bool.
       simply_connected t /\ s retract_of t ==> simply_connected s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
   (REWRITE_RULE[CONJ_ASSOC] SIMPLY_CONNECTED_RETRACTION_GEN)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[IMAGE_ID; CONTINUOUS_ON_ID]);;

let RETRACT_OF_HOMOTOPICALLY_TRIVIAL = prove
 (`!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f g. f continuous_on u /\ IMAGE f u SUBSET s /\
               g continuous_on u /\ IMAGE g u SUBSET s
               ==> homotopic_with (\x. T) (u,s)  f g)
        ==> (!f g. f continuous_on u /\ IMAGE f u SUBSET t /\
                   g continuous_on u /\ IMAGE g u SUBSET t
                   ==> homotopic_with (\x. T) (u,t) f g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> p /\ q /\ T /\ r /\ s /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    HOMOTOPICALLY_TRIVIAL_RETRACTION_GEN) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let RETRACT_OF_HOMOTOPICALLY_TRIVIAL_NULL = prove
 (`!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f. f continuous_on u /\ IMAGE f u SUBSET s
             ==> ?c. homotopic_with (\x. T) (u,s) f (\x. c))
        ==> (!f. f continuous_on u /\ IMAGE f u SUBSET t
                 ==> ?c. homotopic_with (\x. T) (u,t) f (\x. c))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> p /\ q /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    HOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let RETRACT_OF_COHOMOTOPICALLY_TRIVIAL = prove
 (`!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f g. f continuous_on s /\ IMAGE f s SUBSET u /\
               g continuous_on s /\ IMAGE g s SUBSET u
               ==> homotopic_with (\x. T) (s,u)  f g)
        ==> (!f g. f continuous_on t /\ IMAGE f t SUBSET u /\
                   g continuous_on t /\ IMAGE g t SUBSET u
                   ==> homotopic_with (\x. T) (t,u) f g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> p /\ q /\ T /\ r /\ s /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    COHOMOTOPICALLY_TRIVIAL_RETRACTION_GEN) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let RETRACT_OF_COHOMOTOPICALLY_TRIVIAL_NULL = prove
 (`!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET u
             ==> ?c. homotopic_with (\x. T) (s,u) f (\x. c))
        ==> (!f. f continuous_on t /\ IMAGE f t SUBSET u
                 ==> ?c. homotopic_with (\x. T) (t,u) f (\x. c))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> p /\ q /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    COHOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let RETRACTION_IMP_QUOTIENT_MAP = prove
 (`!r s t:real^N->bool.
    retraction (s,t) r
    ==> !u. u SUBSET t
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ r x IN u} <=>
                 open_in (subtopology euclidean t) u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_RIGHT_INVERSE_IMP_QUOTIENT_MAP THEN
  EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; SUBSET_REFL; IMAGE_ID]);;

let RETRACT_OF_LOCALLY_CONNECTED = prove
 (`!s t:real^N->bool.
        s retract_of t /\ locally connected t ==> locally connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o el 2 o CONJUNCTS o GEN_REWRITE_RULE I
   [RETRACTION]) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LOCALLY_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC RETRACTION_IMP_QUOTIENT_MAP THEN
  ASM_MESON_TAC[RETRACTION]);;

let RETRACT_OF_LOCALLY_PATH_CONNECTED = prove
 (`!s t:real^N->bool.
        s retract_of t /\ locally path_connected t
        ==> locally path_connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o el 2 o CONJUNCTS o GEN_REWRITE_RULE I
   [RETRACTION]) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
    LOCALLY_PATH_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC RETRACTION_IMP_QUOTIENT_MAP THEN
  ASM_MESON_TAC[RETRACTION]);;

let RETRACT_OF_LOCALLY_COMPACT = prove
 (`!s t:real^N->bool.
        locally compact s /\ t retract_of s ==> locally compact t`,
  MESON_TAC[CLOSED_IN_RETRACT; LOCALLY_COMPACT_CLOSED_IN]);;

let RETRACT_OF_PCROSS = prove
 (`!s:real^M->bool s' t:real^N->bool t'.
        s retract_of s' /\ t retract_of t'
        ==> (s PCROSS t) retract_of (s' PCROSS t')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS] THEN
  REWRITE_TAC[retract_of; retraction; SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `f:real^M->real^M` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\z. pastecart ((f:real^M->real^M) (fstcart z))
                            ((g:real^N->real^N) (sndcart z))` THEN
  REWRITE_TAC[FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
   CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART]);;

let RETRACT_OF_PCROSS_EQ = prove
 (`!s s':real^M->bool t t':real^N->bool.
        s PCROSS t retract_of s' PCROSS t' <=>
        (s = {} \/ t = {}) /\ (s' = {} \/ t' = {}) \/
        s retract_of s' /\ t retract_of t'`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`s:real^M->bool = {}`;
    `s':real^M->bool = {}`;
    `t:real^N->bool = {}`;
    `t':real^N->bool = {}`] THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; RETRACT_OF_EMPTY; PCROSS_EQ_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[RETRACT_OF_PCROSS] THEN
  REWRITE_TAC[retract_of; retraction; SUBSET; FORALL_IN_PCROSS;
              FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^(M,N)finite_sum->real^(M,N)finite_sum`
    STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `?b:real^N. b IN t` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `\x. fstcart((r:real^(M,N)finite_sum->real^(M,N)finite_sum)
                            (pastecart x b))` THEN
    ASM_SIMP_TAC[FSTCART_PASTECART] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_FSTCART; LINEAR_CONTINUOUS_ON] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
      ASM_MESON_TAC[MEMBER_NOT_EMPTY];
      ASM_MESON_TAC[PASTECART_FST_SND; PASTECART_IN_PCROSS; MEMBER_NOT_EMPTY]];
    SUBGOAL_THEN `?a:real^M. a IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `\x. sndcart((r:real^(M,N)finite_sum->real^(M,N)finite_sum)
                            (pastecart a x))` THEN
    ASM_SIMP_TAC[SNDCART_PASTECART] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
      ASM_MESON_TAC[MEMBER_NOT_EMPTY];
      ASM_MESON_TAC[PASTECART_FST_SND; PASTECART_IN_PCROSS;
                    MEMBER_NOT_EMPTY]]]);;

let HOMOTOPIC_INTO_RETRACT = prove
 (`!f:real^M->real^N g s t u.
        IMAGE f s SUBSET t /\ IMAGE g s SUBSET t /\ t retract_of u /\
        homotopic_with (\x. T) (s,u) f g
        ==> homotopic_with (\x. T) (s,t) f g`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  SIMP_TAC[HOMOTOPIC_WITH; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:real^(1,M)finite_sum->real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
  EXISTS_TAC `(r:real^N->real^N) o (h:real^(1,M)finite_sum->real^N)` THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE; ASM SET_TAC[]] THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    CONTINUOUS_ON_SUBSET)) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Absolute retracts (AR), absolute neighbourhood retracts (ANR) and also    *)
(* Euclidean neighbourhood retracts (ENR). We define AR and ANR by           *)
(* specializing the standard definitions for a set in R^n to embedding in    *)
(* spaces inside R^{n+1}. This turns out to be sufficient (since any set in  *)
(* R^n can be embedded as a closed subset of a convex subset of R^{n+1}) to  *)
(* derive the usual definitions, but we need to split them into two          *)
(* implications because of the lack of type quantifiers. Then ENR turns out  *)
(* to be equivalent to ANR plus local compactness.                           *)
(* ------------------------------------------------------------------------- *)

let AR = new_definition
 `AR(s:real^N->bool) <=>
        !u s':real^(N,1)finite_sum->bool.
                s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
                ==> s' retract_of u`;;

let ANR = new_definition
 `ANR(s:real^N->bool) <=>
        !u s':real^(N,1)finite_sum->bool.
                s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
                ==> ?t. open_in (subtopology euclidean u) t /\
                        s' retract_of t`;;

let ENR = new_definition
 `ENR s <=> ?u. open u /\ s retract_of u`;;

(* ------------------------------------------------------------------------- *)
(* First, show that we do indeed get the "usual" properties of ARs and ANRs. *)
(* ------------------------------------------------------------------------- *)

let AR_IMP_ABSOLUTE_EXTENSOR = prove
 (`!f:real^M->real^N u t s.
        AR s /\ f continuous_on t /\ IMAGE f t SUBSET s /\
        closed_in (subtopology euclidean u) t
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET s /\
                !x. x IN t ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?c s':real^(N,1)finite_sum->bool.
        convex c /\ ~(c = {}) /\ closed_in (subtopology euclidean c) s' /\
        (s:real^N->bool) homeomorphic s'`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_CLOSED_IN_CONVEX THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[INT_ARITH `x:int < y + &1 <=> x <= y`; AFF_DIM_LE_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AR]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`c:real^(N,1)finite_sum->bool`; `s':real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real^N->real^(N,1)finite_sum`; `h:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`(g:real^N->real^(N,1)finite_sum) o (f:real^M->real^N)`;
    `c:real^(N,1)finite_sum->bool`; `u:real^M->bool`; `t:real^M->bool`]
        DUGUNDJI) THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^(N,1)finite_sum`
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^(N,1)finite_sum->real^(N,1)finite_sum` THEN
  STRIP_TAC THEN
  EXISTS_TAC `(h:real^(N,1)finite_sum->real^N) o r o
              (f':real^M->real^(N,1)finite_sum)` THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let AR_IMP_ABSOLUTE_RETRACT = prove
 (`!s:real^N->bool u s':real^M->bool.
        AR s /\ s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
        ==> s' retract_of u`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^N->real^M`; `h:real^M->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `u:real^M->bool`; `s':real^M->bool`;
                 `s:real^N->bool`] AR_IMP_ABSOLUTE_EXTENSOR) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real^M->real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `(g:real^N->real^M) o (h':real^M->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let AR_IMP_ABSOLUTE_RETRACT_UNIV = prove
 (`!s:real^N->bool s':real^M->bool.
    AR s /\ s homeomorphic s' /\ closed s' ==> s' retract_of (:real^M)`,
  MESON_TAC[AR_IMP_ABSOLUTE_RETRACT;
            TOPSPACE_EUCLIDEAN; SUBTOPOLOGY_UNIV; OPEN_IN; CLOSED_IN]);;

let ABSOLUTE_EXTENSOR_IMP_AR = prove
 (`!s:real^N->bool.
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?g. g continuous_on u /\ IMAGE g u SUBSET s /\
                     !x. x IN t ==> g x = f x)
        ==> AR s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AR] THEN MAP_EVERY X_GEN_TAC
   [`u:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`g:real^N->real^(N,1)finite_sum`; `h:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o ISPECL
    [`h:real^(N,1)finite_sum->real^N`;
     `u:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(X_CHOOSE_THEN
    `h':real^(N,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `(g:real^N->real^(N,1)finite_sum) o
              (h':real^(N,1)finite_sum->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let AR_EQ_ABSOLUTE_EXTENSOR = prove
 (`!s:real^N->bool.
        AR s <=>
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?g. g continuous_on u /\ IMAGE g u SUBSET s /\
                     !x. x IN t ==> g x = f x)`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[AR_IMP_ABSOLUTE_EXTENSOR; ABSOLUTE_EXTENSOR_IMP_AR]);;

let AR_IMP_RETRACT = prove
 (`!s u:real^N->bool.
        AR s /\ closed_in (subtopology euclidean u) s ==> s retract_of u`,
  MESON_TAC[AR_IMP_ABSOLUTE_RETRACT; HOMEOMORPHIC_REFL]);;

let HOMEOMORPHIC_ARNESS = prove
 (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t ==> (AR s <=> AR t)`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t /\ AR t ==> AR s`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[AR] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ]
      AR_IMP_ABSOLUTE_RETRACT)) THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC HOMEOMORPHIC_TRANS `s:real^M->bool` THEN
    ASM_MESON_TAC[HOMEOMORPHIC_SYM]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN POP_ASSUM MP_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM]; ALL_TAC] THEN
  ASM_MESON_TAC[lemma]);;

let AR_TRANSLATION = prove
 (`!a:real^N s. AR(IMAGE (\x. a + x) s) <=> AR s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ARNESS THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

add_translation_invariants [AR_TRANSLATION];;

let AR_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (AR(IMAGE f s) <=> AR s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ARNESS THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF]);;

add_linear_invariants [AR_LINEAR_IMAGE_EQ];;

let ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR = prove
 (`!f:real^M->real^N u t s.
        ANR s /\ f continuous_on t /\ IMAGE f t SUBSET s /\
        closed_in (subtopology euclidean u) t
        ==> ?v g. t SUBSET v /\ open_in (subtopology euclidean u) v /\
                  g continuous_on v /\ IMAGE g v SUBSET s /\
                  !x. x IN t ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?c s':real^(N,1)finite_sum->bool.
        convex c /\ ~(c = {}) /\ closed_in (subtopology euclidean c) s' /\
        (s:real^N->bool) homeomorphic s'`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_CLOSED_IN_CONVEX THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[INT_ARITH `x:int < y + &1 <=> x <= y`; AFF_DIM_LE_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ANR]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`c:real^(N,1)finite_sum->bool`; `s':real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN
   `d:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real^N->real^(N,1)finite_sum`; `h:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`(g:real^N->real^(N,1)finite_sum) o (f:real^M->real^N)`;
    `c:real^(N,1)finite_sum->bool`; `u:real^M->bool`; `t:real^M->bool`]
        DUGUNDJI) THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^(N,1)finite_sum`
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^(N,1)finite_sum->real^(N,1)finite_sum` THEN
  STRIP_TAC THEN
  EXISTS_TAC `{x | x IN u /\ (f':real^M->real^(N,1)finite_sum) x IN d}` THEN
  EXISTS_TAC `(h:real^(N,1)finite_sum->real^N) o r o
              (f':real^M->real^(N,1)finite_sum)` THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN REPEAT CONJ_TAC THENL
   [REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET)) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN ASM_MESON_TAC[];
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
    REWRITE_TAC[IMAGE_o] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^N->bool u s':real^M->bool.
        ANR s /\ s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
        ==> ?v. open_in (subtopology euclidean u) v /\
                s' retract_of v`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^N->real^M`; `h:real^M->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `u:real^M->bool`; `s':real^M->bool`;
                `s:real^N->bool`] ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real^M->real^N` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `(g:real^N->real^M) o (h':real^M->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV = prove
 (`!s:real^N->bool s':real^M->bool.
    ANR s /\ s homeomorphic s' /\ closed s' ==> ?v. open v /\ s' retract_of v`,
  MESON_TAC[ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT;
            TOPSPACE_EUCLIDEAN; SUBTOPOLOGY_UNIV; OPEN_IN; CLOSED_IN]);;

let ABSOLUTE_NEIGHBOURHOOD_EXTENSOR_IMP_ANR = prove
 (`!s:real^N->bool.
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?v g. t SUBSET v /\ open_in  (subtopology euclidean u) v /\
                       g continuous_on v /\ IMAGE g v SUBSET s /\
                       !x. x IN t ==> g x = f x)
        ==> ANR s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ANR] THEN MAP_EVERY X_GEN_TAC
   [`u:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`g:real^N->real^(N,1)finite_sum`; `h:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o ISPECL
    [`h:real^(N,1)finite_sum->real^N`;
     `u:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^(N,1)finite_sum->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real^(N,1)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `(g:real^N->real^(N,1)finite_sum) o
              (h':real^(N,1)finite_sum->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR = prove
 (`!s:real^N->bool.
        ANR s <=>
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?v g. t SUBSET v /\ open_in  (subtopology euclidean u) v /\
                       g continuous_on v /\ IMAGE g v SUBSET s /\
                       !x. x IN t ==> g x = f x)`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR;
           ABSOLUTE_NEIGHBOURHOOD_EXTENSOR_IMP_ANR]);;

let ANR_IMP_ABSOLUTE_CLOSED_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^N->bool u s':real^M->bool.
        ANR s /\ s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
        ==> ?v w. open_in (subtopology euclidean u) v /\
                  closed_in (subtopology euclidean u) w /\
                  s' SUBSET v /\ v SUBSET w /\ s' retract_of w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?z. open_in (subtopology euclidean u) z /\
                    (s':real^M->bool) retract_of z`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
    [`s':real^M->bool`; `u DIFF z:real^M->bool`; `u:real^M->bool`]
    SEPARATION_NORMAL_LOCAL) THEN
  ASM_SIMP_TAC[CLOSED_IN_INTER; CLOSED_IN_REFL; CLOSED_IN_DIFF] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `v:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u DIFF w:real^M->bool` THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] RETRACT_OF_SUBSET)) THEN
  ASM SET_TAC[]);;

let ANR_IMP_ABSOLUTE_CLOSED_NEIGHBOURHOOD_EXTENSOR = prove
 (`!f:real^M->real^N u t s.
        ANR s /\ f continuous_on t /\ IMAGE f t SUBSET s /\
        closed_in (subtopology euclidean u) t
        ==> ?v w g. open_in (subtopology euclidean u) v /\
                    closed_in (subtopology euclidean u) w /\
                    t SUBSET v /\ v SUBSET w /\
                    g continuous_on w /\ IMAGE g w SUBSET s /\
                    !x. x IN t ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?v g. t SUBSET v /\ open_in (subtopology euclidean u) v /\
          g continuous_on v /\ IMAGE g v SUBSET s /\
          !x. x IN t ==> g x = (f:real^M->real^N) x`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
    [`t:real^M->bool`; `u DIFF v:real^M->bool`; `u:real^M->bool`]
    SEPARATION_NORMAL_LOCAL) THEN
  ASM_SIMP_TAC[CLOSED_IN_INTER; CLOSED_IN_REFL; CLOSED_IN_DIFF] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `w:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u DIFF z:real^M->bool` THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  EXISTS_TAC `g:real^M->real^N` THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
  ASM SET_TAC[]);;

let ANR_IMP_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^N->bool u.
        ANR s /\ closed_in (subtopology euclidean u) s
        ==> ?v. open_in (subtopology euclidean u) v /\
                s retract_of v`,
  MESON_TAC[ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT; HOMEOMORPHIC_REFL]);;

let ANR_IMP_CLOSED_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^N->bool u.
        ANR s /\ closed_in (subtopology euclidean u) s
        ==> ?v w. open_in (subtopology euclidean u) v /\
                  closed_in (subtopology euclidean u) w /\
                  s SUBSET v /\ v SUBSET w /\ s retract_of w`,
  MESON_TAC[ANR_IMP_ABSOLUTE_CLOSED_NEIGHBOURHOOD_RETRACT;
            HOMEOMORPHIC_REFL]);;

let HOMEOMORPHIC_ANRNESS = prove
 (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t ==> (ANR s <=> ANR t)`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t /\ ANR t ==> ANR s`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[ANR] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ]
      ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT)) THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC HOMEOMORPHIC_TRANS `s:real^M->bool` THEN
    ASM_MESON_TAC[HOMEOMORPHIC_SYM]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN POP_ASSUM MP_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM]; ALL_TAC] THEN
  ASM_MESON_TAC[lemma]);;

let ANR_TRANSLATION = prove
 (`!a:real^N s. ANR(IMAGE (\x. a + x) s) <=> ANR s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ANRNESS THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

add_translation_invariants [ANR_TRANSLATION];;

let ANR_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (ANR(IMAGE f s) <=> ANR s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ANRNESS THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF]);;

add_linear_invariants [ANR_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Analogous properties of ENRs.                                             *)
(* ------------------------------------------------------------------------- *)

let ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^M->bool s':real^N->bool u.
        ENR s /\ s homeomorphic s' /\ s' SUBSET u
        ==> ?t'. open_in (subtopology euclidean u) t' /\ s' retract_of t'`,
  REWRITE_TAC[ENR; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`X:real^M->bool`; `Y:real^N->bool`;
    `K:real^N->bool`; `U:real^M->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `locally compact (Y:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RETRACT_OF_LOCALLY_COMPACT;
                  OPEN_IMP_LOCALLY_COMPACT; HOMEOMORPHIC_LOCAL_COMPACTNESS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?W:real^N->bool.
        open_in (subtopology euclidean K) W /\
        closed_in (subtopology euclidean W) Y`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC o
        MATCH_MP LOCALLY_COMPACT_CLOSED_IN_OPEN) THEN
    EXISTS_TAC `K INTER W:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; CLOSED_IN_CLOSED] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSED_IN_CLOSED]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^M`; `W:real^N->bool`; `Y:real^N->bool`]
        TIETZE_UNBOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{x | x IN W /\ (h:real^N->real^M) x IN U}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; SUBSET_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; retract_of; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^M->real^M` THEN STRIP_TAC THEN
  EXISTS_TAC `(f:real^M->real^N) o r o (h:real^N->real^M)` THEN
  SUBGOAL_THEN
   `(W:real^N->bool) SUBSET K /\ Y SUBSET W`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; CLOSED_IN_IMP_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o; o_THM] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
  REWRITE_TAC[IMAGE_o] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  ASM SET_TAC[]);;

let ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV = prove
 (`!s:real^M->bool s':real^N->bool.
        ENR s /\ s homeomorphic s' ==> ?t'. open t' /\ s' retract_of t'`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN] THEN
  ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
  MATCH_MP_TAC ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT THEN
  ASM_MESON_TAC[SUBSET_UNIV]);;

let HOMEOMORPHIC_ENRNESS = prove
 (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t ==> (ENR s <=> ENR t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ENR] THENL
   [MP_TAC(ISPECL [`s:real^M->bool`; `t:real^N->bool`]
        ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV);
    MP_TAC(ISPECL [`t:real^N->bool`; `s:real^M->bool`]
        ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SYM]);;

let ENR_TRANSLATION = prove
 (`!a:real^N s. ENR(IMAGE (\x. a + x) s) <=> ENR s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ENRNESS THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

add_translation_invariants [ENR_TRANSLATION];;

let ENR_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (ENR(IMAGE f s) <=> ENR s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ENRNESS THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF]);;

add_linear_invariants [ENR_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Some relations among the concepts. We also relate AR to being a retract   *)
(* of UNIV, which is often a more convenient proxy in the closed case.       *)
(* ------------------------------------------------------------------------- *)

let AR_IMP_ANR = prove
 (`!s:real^N->bool. AR s ==> ANR s`,
  REWRITE_TAC[AR; ANR] THEN MESON_TAC[OPEN_IN_REFL; CLOSED_IN_IMP_SUBSET]);;

let ENR_IMP_ANR = prove
 (`!s:real^N->bool. ENR s ==> ANR s`,
  REWRITE_TAC[ANR] THEN
  MESON_TAC[ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT; CLOSED_IN_IMP_SUBSET]);;

let ENR_ANR = prove
 (`!s:real^N->bool. ENR s <=> ANR s /\ locally compact s`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN ASM_SIMP_TAC[ENR_IMP_ANR] THENL
   [ASM_MESON_TAC[ENR; RETRACT_OF_LOCALLY_COMPACT; OPEN_IMP_LOCALLY_COMPACT];
    SUBGOAL_THEN
     `?t. closed t /\
          (s:real^N->bool) homeomorphic (t:real^(N,1)finite_sum->bool)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC LOCALLY_COMPACT_HOMEOMORPHIC_CLOSED THEN
      ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ANR]) THEN
      DISCH_THEN(MP_TAC o SPECL
       [`(:real^(N,1)finite_sum)`; `t:real^(N,1)finite_sum->bool`]) THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; GSYM OPEN_IN] THEN
      REWRITE_TAC[GSYM ENR] THEN ASM_MESON_TAC[HOMEOMORPHIC_ENRNESS]]]);;

let AR_ANR = prove
 (`!s:real^N->bool. AR s <=> ANR s /\ contractible s /\ ~(s = {})`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[AR_IMP_ANR] THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      ASM_MESON_TAC[AR; HOMEOMORPHIC_EMPTY; RETRACT_OF_EMPTY;
           FORALL_UNWIND_THM2; CLOSED_IN_EMPTY; UNIV_NOT_EMPTY]] THEN
    SUBGOAL_THEN
     `?c s':real^(N,1)finite_sum->bool.
          convex c /\ ~(c = {}) /\ closed_in (subtopology euclidean c) s' /\
          (s:real^N->bool) homeomorphic s'`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_CLOSED_IN_CONVEX THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
      REWRITE_TAC[INT_ARITH `x:int < y + &1 <=> x <= y`; AFF_DIM_LE_UNIV];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AR]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`c:real^(N,1)finite_sum->bool`; `s':real^(N,1)finite_sum->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[HOMEOMORPHIC_SYM; HOMEOMORPHIC_CONTRACTIBLE;
                  RETRACT_OF_CONTRACTIBLE; CONVEX_IMP_CONTRACTIBLE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [contractible]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; homotopic_with] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `h:real^(1,N)finite_sum->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[AR_EQ_ABSOLUTE_EXTENSOR] THEN
  MAP_EVERY X_GEN_TAC
   [`f:real^(N,1)finite_sum->real^N`; `w:real^(N,1)finite_sum->bool`;
    `t:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o  ISPECL
    [`f:real^(N,1)finite_sum->real^N`; `w:real^(N,1)finite_sum->bool`;
     `t:real^(N,1)finite_sum->bool`]  o
    REWRITE_RULE[ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
    [`u:real^(N,1)finite_sum->bool`; `g:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`t:real^(N,1)finite_sum->bool`; `w DIFF u:real^(N,1)finite_sum->bool`;
    `w:real^(N,1)finite_sum->bool`] SEPARATION_NORMAL_LOCAL) THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC
   [`v:real^(N,1)finite_sum->bool`; `v':real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`t:real^(N,1)finite_sum->bool`; `w DIFF v:real^(N,1)finite_sum->bool`;
    `w:real^(N,1)finite_sum->bool`; `vec 0:real^1`; `vec 1:real^1`]
        URYSOHN_LOCAL) THEN
  ASM_SIMP_TAC[SEGMENT_1; CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  REWRITE_TAC[DROP_VEC; REAL_POS] THEN
  X_GEN_TAC `e:real^(N,1)finite_sum->real^1` THEN STRIP_TAC THEN
  EXISTS_TAC
   `\x. if (x:real^(N,1)finite_sum) IN w DIFF v then a
        else (h:real^(1,N)finite_sum->real^N) (pastecart (e x) (g x))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `w:real^(N,1)finite_sum->bool = (w DIFF v) UNION (w DIFF v')`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th ->
        GEN_REWRITE_TAC RAND_CONV [th] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
        REWRITE_TAC[GSYM th]) THEN
    ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL; CONTINUOUS_ON_CONST] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN RULE_ASSUM_TAC
     (REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS]) THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    COND_CASES_TAC THEN ASM SET_TAC[]]);;

let ANR_RETRACT_OF_ANR = prove
 (`!s t:real^N->bool. ANR t /\ s retract_of t ==> ANR s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^(N,1)finite_sum->real^N`
        STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(r:real^N->real^N) o (g:real^(N,1)finite_sum->real^N)` THEN
  ASM_SIMP_TAC[IMAGE_o; o_THM] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  ASM SET_TAC[]);;

let AR_RETRACT_OF_AR = prove
 (`!s t:real^N->bool. AR t /\ s retract_of t ==> AR s`,
  REWRITE_TAC[AR_ANR] THEN
  MESON_TAC[ANR_RETRACT_OF_ANR; RETRACT_OF_CONTRACTIBLE; RETRACT_OF_EMPTY]);;

let ENR_RETRACT_OF_ENR = prove
 (`!s t:real^N->bool. ENR t /\ s retract_of t ==> ENR s`,
  REWRITE_TAC[ENR] THEN MESON_TAC[RETRACT_OF_TRANS]);;

let RETRACT_OF_UNIV = prove
 (`!s:real^N->bool. s retract_of (:real^N) <=> AR s /\ closed s`,
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC AR_RETRACT_OF_AR THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ABSOLUTE_EXTENSOR_IMP_AR THEN
    MESON_TAC[DUGUNDJI; CONVEX_UNIV; UNIV_NOT_EMPTY];
    MATCH_MP_TAC RETRACT_OF_CLOSED THEN ASM_MESON_TAC[CLOSED_UNIV];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        AR_IMP_ABSOLUTE_RETRACT)) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; HOMEOMORPHIC_REFL]]);;

let COMPACT_AR = prove
 (`!s. compact s /\ AR s <=> compact s /\ s retract_of (:real^N)`,
  REWRITE_TAC[RETRACT_OF_UNIV] THEN MESON_TAC[COMPACT_IMP_CLOSED]);;
