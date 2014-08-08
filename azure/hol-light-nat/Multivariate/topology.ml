open Hol_core
open Card
open Products
open Permutations
open Floor
open Vectors
open Determinants
include Topology5

(* ------------------------------------------------------------------------- *)
(* Hausdorff distance between sets.                                          *)
(* ------------------------------------------------------------------------- *)

let hausdist = new_definition
 `hausdist(s:real^N->bool,t:real^N->bool) =
        let ds = {setdist({x},t) | x IN s} UNION {setdist({y},s) | y IN t} in
        if ~(ds = {}) /\ (?b. !d. d IN ds ==> d <= b) then sup ds
        else &0`;;

let HAUSDIST_POS_LE = prove
 (`!s t:real^N->bool. &0 <= hausdist(s,t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hausdist; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; FORALL_IN_UNION] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_SUP THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC; FORALL_IN_UNION; SETDIST_POS_LE] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC(SET_RULE
   `~(s = {}) /\ (!x. x IN s ==> P x) ==> ?y. y IN s /\ P y`) THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC; FORALL_IN_UNION; SETDIST_POS_LE]);;

let HAUSDIST_REFL = prove
 (`!s:real^N->bool. hausdist(s,s) = &0`,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM; HAUSDIST_POS_LE] THEN
  REWRITE_TAC[hausdist; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN
  REWRITE_TAC[FORALL_IN_GSPEC; FORALL_IN_UNION] THEN
  ASM_SIMP_TAC[SETDIST_SING_IN_SET; REAL_LE_REFL]);;

let HAUSDIST_SYM = prove
 (`!s t:real^N->bool. hausdist(s,t) = hausdist(t,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hausdist; LET_DEF; LET_END_DEF] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [UNION_COMM] THEN
  REWRITE_TAC[]);;

let HAUSDIST_EMPTY = prove
 (`(!t:real^N->bool. hausdist ({},t) = &0) /\
   (!s:real^N->bool. hausdist (s,{}) = &0)`,
  REWRITE_TAC[hausdist; LET_DEF; LET_END_DEF; SETDIST_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{f x | x IN {}} = {}`; UNION_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{c |x| x IN s} = {} <=> s = {}`] THEN
  X_GEN_TAC `s:real^N->bool` THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SET_RULE `~(s = {}) ==> {c |x| x IN s} = {c}`] THEN
  REWRITE_TAC[SUP_SING; COND_ID]);;

let HAUSDIST_SINGS = prove
 (`!x y:real^N. hausdist({x},{y}) = dist(x,y)`,
  REWRITE_TAC[hausdist; LET_DEF; LET_END_DEF; SETDIST_SINGS] THEN
  REWRITE_TAC[SET_RULE `{f x | x IN {a}} = {f a}`] THEN
  REWRITE_TAC[DIST_SYM; UNION_IDEMPOT; SUP_SING; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IN_SING; FORALL_UNWIND_THM2] THEN
  MESON_TAC[REAL_LE_REFL]);;

let HAUSDIST_EQ = prove
 (`!s t:real^M->bool s' t':real^N->bool.
        (!b. (!x. x IN s ==> setdist({x},t) <= b) /\
             (!y. y IN t ==> setdist({y},s) <= b) <=>
             (!x. x IN s' ==> setdist({x},t') <= b) /\
             (!y. y IN t' ==> setdist({y},s') <= b))
        ==> hausdist(s,t) = hausdist(s',t')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hausdist; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC(MESON[]
   `(p <=> p') /\ s = s'
    ==> (if p then s else &0) = (if p' then s' else &0)`) THEN
  CONJ_TAC THENL
   [BINOP_TAC THENL
     [PURE_REWRITE_TAC[SET_RULE `s = {} <=> !x. x IN s ==> F`];
      AP_TERM_TAC THEN ABS_TAC];
    MATCH_MP_TAC SUP_EQ] THEN
  PURE_REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_GSPEC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM; MEMBER_NOT_EMPTY] THEN
  REWRITE_TAC[GSYM DE_MORGAN_THM] THEN AP_TERM_TAC THEN EQ_TAC THEN
  DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `--(&1):real`) THEN
  SIMP_TAC[SETDIST_POS_LE; REAL_ARITH `&0 <= x ==> ~(x <= --(&1))`] THEN
  SET_TAC[]);;

let HAUSDIST_TRANSLATION = prove
 (`!a s t:real^N->bool.
        hausdist(IMAGE (\x. a + x) s,IMAGE (\x. a + x) t) = hausdist(s,t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hausdist] THEN
  REWRITE_TAC[SET_RULE `{f x | x IN IMAGE g s} = {f(g x) | x IN s}`] THEN
  REWRITE_TAC[SET_RULE `{a + x:real^N} = IMAGE (\x. a + x) {x}`] THEN
  REWRITE_TAC[SETDIST_TRANSLATION]);;

add_translation_invariants [HAUSDIST_TRANSLATION];;

let HAUSDIST_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s t.
           linear f /\ (!x. norm(f x) = norm x)
           ==> hausdist(IMAGE f s,IMAGE f t) = hausdist(s,t)`,
  REPEAT STRIP_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[hausdist] THEN
  REWRITE_TAC[SET_RULE `{f x | x IN IMAGE g s} = {f(g x) | x IN s}`] THEN
  ONCE_REWRITE_TAC[SET_RULE `{(f:real^M->real^N) x} = IMAGE f {x}`] THEN
  ASM_SIMP_TAC[SETDIST_LINEAR_IMAGE]);;

add_linear_invariants [HAUSDIST_LINEAR_IMAGE];;

let HAUSDIST_CLOSURE = prove
 (`(!s t:real^N->bool. hausdist(closure s,t) = hausdist(s,t)) /\
   (!s t:real^N->bool. hausdist(s,closure t) = hausdist(s,t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAUSDIST_EQ THEN
  GEN_TAC THEN BINOP_TAC THEN REWRITE_TAC[SETDIST_CLOSURE] THEN
  PURE_ONCE_REWRITE_TAC[SET_RULE
   `(!x. P x ==> Q x) <=> (!x. P x ==> x IN {x | Q x})`] THEN
  MATCH_MP_TAC FORALL_IN_CLOSURE_EQ THEN
  REWRITE_TAC[EMPTY_GSPEC; CONTINUOUS_ON_ID; CLOSED_EMPTY] THEN
  ONCE_REWRITE_TAC[MESON[LIFT_DROP] `x <= b <=> drop(lift x) <= b`] THEN
  REWRITE_TAC[SET_RULE
    `{x | drop(lift(f x)) <= b} =
     {x | x IN UNIV /\ lift(f x) IN {x | drop x <= b}}`] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
  REWRITE_TAC[CLOSED_UNIV; CONTINUOUS_ON_LIFT_SETDIST] THEN
  REWRITE_TAC[drop; CLOSED_HALFSPACE_COMPONENT_LE]);;

let REAL_HAUSDIST_LE = prove
 (`!s t:real^N->bool b.
        ~(s = {}) /\ ~(t = {}) /\
        (!x. x IN s ==> setdist({x},t) <= b) /\
        (!y. y IN t ==> setdist({y},s) <= b)
        ==> hausdist(s,t) <= b`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[hausdist; LET_DEF; LET_END_DEF; SETDIST_SINGS] THEN
  ASM_REWRITE_TAC[EMPTY_UNION; SET_RULE `{f x | x IN s} = {} <=> s = {}`] THEN
  REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_GSPEC] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN
  ASM_REWRITE_TAC[EMPTY_UNION; SET_RULE `{f x | x IN s} = {} <=> s = {}`] THEN
  ASM_REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_GSPEC]);;

let REAL_HAUSDIST_LE_SUMS = prove
 (`!s t:real^N->bool b.
        ~(s = {}) /\ ~(t = {}) /\
        s SUBSET {y + z | y IN t /\ z IN cball(vec 0,b)} /\
        t SUBSET {y + z | y IN s /\ z IN cball(vec 0,b)}
        ==> hausdist(s,t) <= b`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL_0] THEN
  REWRITE_TAC[VECTOR_ARITH `a:real^N = b + x <=> a - b = x`;
              ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
  REWRITE_TAC[GSYM dist] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_HAUSDIST_LE THEN
  ASM_MESON_TAC[SETDIST_LE_DIST; REAL_LE_TRANS; IN_SING]);;

let REAL_LE_HAUSDIST  = prove
 (`!s t:real^N->bool a b c z.
        ~(s = {}) /\ ~(t = {}) /\
        (!x. x IN s ==> setdist({x},t) <= b) /\
        (!y. y IN t ==> setdist({y},s) <= c) /\
        (z IN s /\ a <= setdist({z},t) \/ z IN t /\ a <= setdist({z},s))
        ==> a <= hausdist(s,t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[hausdist; LET_DEF; LET_END_DEF; SETDIST_SINGS] THEN
  ASM_REWRITE_TAC[EMPTY_UNION; SET_RULE `{f x | x IN s} = {} <=> s = {}`] THEN
  REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_GSPEC] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC REAL_LE_SUP THEN
    ASM_SIMP_TAC[EMPTY_UNION; SET_RULE `{f x | x IN s} = {} <=> s = {}`] THEN
    REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_GSPEC];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[NOT_FORALL_THM]] THEN
  EXISTS_TAC `max b c:real` THEN
  ASM_SIMP_TAC[REAL_LE_MAX] THEN ASM SET_TAC[]);;

let SETDIST_LE_HAUSDIST = prove
 (`!s t:real^N->bool.
        bounded s /\ bounded t ==> setdist(s,t) <= hausdist(s,t)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SETDIST_EMPTY; HAUSDIST_EMPTY; REAL_LE_REFL] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SETDIST_EMPTY; HAUSDIST_EMPTY; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_HAUSDIST THEN REWRITE_TAC[CONJ_ASSOC] THEN
  ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM] THEN
  CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SETDIST_LE_SING; MEMBER_NOT_EMPTY]] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] BOUNDED_DIFFS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[bounded; FORALL_IN_GSPEC; GSYM dist] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real`) THEN
  CONJ_TAC THEN EXISTS_TAC `b:real` THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[REAL_LE_TRANS; SETDIST_LE_DIST; MEMBER_NOT_EMPTY; IN_SING;
                DIST_SYM]);;

let SETDIST_SING_LE_HAUSDIST = prove
 (`!s t x:real^N.
        bounded s /\ bounded t /\ x IN s ==> setdist({x},t) <= hausdist(s,t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SETDIST_EMPTY; HAUSDIST_EMPTY; REAL_LE_REFL] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_HAUSDIST THEN
  ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[LEFT_EXISTS_AND_THM; EXISTS_OR_THM; CONJ_ASSOC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_REFL]] THEN CONJ_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] BOUNDED_DIFFS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[GSYM dist] THEN GEN_TAC THENL
   [ALL_TAC; ONCE_REWRITE_TAC[SWAP_FORALL_THM]] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:real^N` THEN
  REPEAT STRIP_TAC THENL
   [UNDISCH_TAC `~(t:real^N->bool = {})`;
    UNDISCH_TAC `~(s:real^N->bool = {})`] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THENL
   [ALL_TAC; ONCE_REWRITE_TAC[DIST_SYM]] THEN
  MATCH_MP_TAC SETDIST_LE_DIST THEN ASM_REWRITE_TAC[IN_SING]);;

let UPPER_LOWER_HEMICONTINUOUS = prove
 (`!f:real^M->real^N->bool t s.
      (!x. x IN s ==> f(x) SUBSET t) /\
      (!u. open_in (subtopology euclidean t) u
           ==> open_in (subtopology euclidean s)
                       {x | x IN s /\ f(x) SUBSET u}) /\
      (!u. closed_in (subtopology euclidean t) u
           ==> closed_in (subtopology euclidean s)
                         {x | x IN s /\ f(x) SUBSET u})
      ==> !x e. x IN s /\ &0 < e /\ bounded(f x)
                ==> ?d. &0 < d /\
                        !x'. x' IN s /\ dist(x,x') < d
                             ==> hausdist(f x,f x') < e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(f:real^M->real^N->bool) x = {}` THENL
   [ASM_REWRITE_TAC[HAUSDIST_EMPTY] THEN MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:real^M`; `e / &2`] o MATCH_MP
        UPPER_LOWER_HEMICONTINUOUS_EXPLICIT) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_BALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `t INTER ball(vec 0:real^N,r)` o
        CONJUNCT1 o CONJUNCT2) THEN
  SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN REWRITE_TAC[open_in] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M` o CONJUNCT2) THEN
  ASM_SIMP_TAC[SUBSET_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `x':real^M` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x':real^M`)) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(f:real^M->real^N->bool) x' = {}` THEN
  ASM_REWRITE_TAC[HAUSDIST_EMPTY] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_HAUSDIST_LE THEN
  ASM_MESON_TAC[SETDIST_LE_DIST; DIST_SYM; REAL_LE_TRANS;
                IN_SING; REAL_LT_IMP_LE]);;

let HAUSDIST_NONTRIVIAL = prove
 (`!s t:real^N->bool.
        bounded s /\ bounded t /\ ~(s = {}) /\ ~(t = {})
        ==> hausdist(s,t) =
            sup({setdist ({x},t) | x IN s} UNION {setdist ({y},s) | y IN t})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hausdist; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
  ASM_SIMP_TAC[EMPTY_UNION; SIMPLE_IMAGE; IMAGE_EQ_EMPTY] THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] BOUNDED_DIFFS) THEN
  ASM_REWRITE_TAC[bounded; FORALL_IN_UNION; FORALL_IN_IMAGE; GSYM dist] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  ASM_MESON_TAC[SETDIST_LE_DIST; dist; DIST_SYM; REAL_LE_TRANS;
                MEMBER_NOT_EMPTY; IN_SING]);;

let HAUSDIST_NONTRIVIAL_ALT = prove
 (`!s t:real^N->bool.
        bounded s /\ bounded t /\ ~(s = {}) /\ ~(t = {})
        ==> hausdist(s,t) = max (sup {setdist ({x},t) | x IN s})
                                (sup {setdist ({y},s) | y IN t})`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HAUSDIST_NONTRIVIAL] THEN
  MATCH_MP_TAC SUP_UNION THEN
  ASM_REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
  CONJ_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] BOUNDED_DIFFS) THEN
  ASM_REWRITE_TAC[bounded; FORALL_IN_UNION; FORALL_IN_IMAGE; GSYM dist] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[FORALL_IN_GSPEC; GSYM dist] THEN
  ASM_MESON_TAC[SETDIST_LE_DIST; dist; DIST_SYM; REAL_LE_TRANS;
                MEMBER_NOT_EMPTY; IN_SING]);;

let REAL_HAUSDIST_LE_EQ = prove
 (`!s t:real^N->bool b.
        ~(s = {}) /\ ~(t = {}) /\ bounded s /\ bounded t
        ==> (hausdist(s,t) <= b <=>
             (!x. x IN s ==> setdist({x},t) <= b) /\
             (!y. y IN t ==> setdist({y},s) <= b))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[HAUSDIST_NONTRIVIAL_ALT; REAL_MAX_LE] THEN
  BINOP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `(!x. x IN s ==> f x <= b) <=>
                             (!y. y IN {f x | x IN s} ==> y <= b)`] THEN
  MATCH_MP_TAC REAL_SUP_LE_EQ THEN
  ASM_REWRITE_TAC[SIMPLE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] BOUNDED_DIFFS) THEN
  ASM_REWRITE_TAC[bounded; FORALL_IN_UNION; FORALL_IN_IMAGE; GSYM dist] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[FORALL_IN_GSPEC; GSYM dist] THEN
  ASM_MESON_TAC[SETDIST_LE_DIST; dist; DIST_SYM; REAL_LE_TRANS;
                MEMBER_NOT_EMPTY; IN_SING]);;

let HAUSDIST_COMPACT_EXISTS = prove
 (`!s t:real^N->bool.
        bounded s /\ compact t /\ ~(t = {})
        ==> !x. x IN s ==> ?y. y IN t /\ dist(x,y) <= hausdist(s,t)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^N}`; `t:real^N->bool`]
        SETDIST_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_SING; COMPACT_IMP_CLOSED; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IN_SING; UNWIND_THM2; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_HAUSDIST THEN
  ASM_REWRITE_TAC[LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [CONJ_TAC; ASM_MESON_TAC[REAL_LE_REFL]] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] BOUNDED_DIFFS) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
  REWRITE_TAC[bounded; FORALL_IN_GSPEC; GSYM dist] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[SETDIST_LE_DIST; dist; DIST_SYM; REAL_LE_TRANS;
                MEMBER_NOT_EMPTY; IN_SING]);;

let HAUSDIST_COMPACT_SUMS = prove
 (`!s t:real^N->bool.
        bounded s /\ compact t /\ ~(t = {})
        ==> s SUBSET {y + z | y IN t /\ z IN cball(vec 0,hausdist(s,t))}`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL_0] THEN
  REWRITE_TAC[VECTOR_ARITH `a:real^N = b + x <=> a - b = x`;
              ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
  REWRITE_TAC[GSYM dist; HAUSDIST_COMPACT_EXISTS]);;

let HAUSDIST_TRANS = prove
 (`!s t u:real^N->bool.
        bounded s /\ bounded t /\ bounded u /\ ~(t = {})
        ==> hausdist(s,u) <= hausdist(s,t) + hausdist(t,u)`,
  let lemma = prove
   (`!s t u:real^N->bool.
          bounded s /\ bounded t /\ bounded u /\
          ~(s = {}) /\ ~(t = {}) /\ ~(u = {})
          ==> !x. x IN s ==> setdist({x},u) <= hausdist(s,t) + hausdist(t,u)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`closure s:real^N->bool`; `closure t:real^N->bool`]
        HAUSDIST_COMPACT_EXISTS) THEN
    ASM_SIMP_TAC[COMPACT_CLOSURE; BOUNDED_CLOSURE; CLOSURE_EQ_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET; HAUSDIST_CLOSURE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`closure t:real^N->bool`; `closure u:real^N->bool`]
      HAUSDIST_COMPACT_EXISTS) THEN
    ASM_SIMP_TAC[COMPACT_CLOSURE; BOUNDED_CLOSURE; CLOSURE_EQ_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET; HAUSDIST_CLOSURE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    TRANS_TAC REAL_LE_TRANS `dist(x:real^N,z)` THEN  CONJ_TAC THENL
     [ASM_MESON_TAC[SETDIST_CLOSURE; SETDIST_LE_DIST; IN_SING]; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `dist(x:real^N,y) + dist(y,z)` THEN
    REWRITE_TAC[DIST_TRIANGLE] THEN ASM_REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[HAUSDIST_EMPTY; REAL_ADD_LID; HAUSDIST_POS_LE] THEN
  ASM_CASES_TAC `u:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[HAUSDIST_EMPTY; REAL_ADD_RID; HAUSDIST_POS_LE] THEN
  ASM_SIMP_TAC[REAL_HAUSDIST_LE_EQ] THEN
  ASM_MESON_TAC[lemma; HAUSDIST_SYM; SETDIST_SYM; REAL_ADD_SYM]);;

let HAUSDIST_EQ_0 = prove
 (`!s t:real^N->bool.
      bounded s /\ bounded t
      ==> (hausdist(s,t) = &0 <=> s = {} \/ t = {} \/ closure s = closure t)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`s:real^N->bool = {}`; `t:real^N->bool = {}`] THEN
  ASM_REWRITE_TAC[HAUSDIST_EMPTY] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_ANTISYM; HAUSDIST_POS_LE; REAL_HAUSDIST_LE_EQ] THEN
  SIMP_TAC[SETDIST_POS_LE; REAL_ARITH `&0 <= x ==> (x <= &0 <=> x = &0)`] THEN
  ASM_REWRITE_TAC[SETDIST_EQ_0_SING; GSYM SUBSET_ANTISYM_EQ; SUBSET] THEN
  SIMP_TAC[FORALL_IN_CLOSURE_EQ; CLOSED_CLOSURE; CONTINUOUS_ON_ID]);;

let HAUSDIST_COMPACT_NONTRIVIAL = prove
 (`!s t:real^N->bool.
        compact s /\ compact t /\ ~(s = {}) /\ ~(t = {})
        ==> hausdist(s,t) =
            inf {e | &0 <= e /\
                   s SUBSET {x + y | x IN t /\ norm y <= e} /\
                   t SUBSET {x + y | x IN s /\ norm y <= e}}`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_INF_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  REWRITE_TAC[VECTOR_ARITH `a:real^N = b + x <=> a - b = x`;
              ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
  REWRITE_TAC[GSYM dist] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_HAUSDIST_LE THEN
    ASM_MESON_TAC[SETDIST_LE_DIST; DIST_SYM; REAL_LE_TRANS;
                  IN_SING; REAL_LT_IMP_LE];
    REPEAT STRIP_TAC THEN EXISTS_TAC `hausdist(s:real^N->bool,t)` THEN
    ASM_REWRITE_TAC[HAUSDIST_POS_LE] THEN
    ASM_MESON_TAC[DIST_SYM; HAUSDIST_SYM;
                  HAUSDIST_COMPACT_EXISTS; COMPACT_IMP_BOUNDED]]);;

let HAUSDIST_BALLS = prove
 (`(!a b:real^N r s.
        hausdist(ball(a,r),ball(b,s)) =
        if r <= &0 \/ s <= &0 then &0 else dist(a,b) + abs(r - s)) /\
   (!a b:real^N r s.
        hausdist(ball(a,r),cball(b,s)) =
        if r <= &0 \/ s < &0 then &0 else dist(a,b) + abs(r - s)) /\
   (!a b:real^N r s.
        hausdist(cball(a,r),ball(b,s)) =
        if r < &0 \/ s <= &0 then &0 else dist(a,b) + abs(r - s)) /\
   (!a b:real^N r s.
        hausdist(cball(a,r),cball(b,s)) =
        if r < &0 \/ s < &0 then &0 else dist(a,b) + abs(r - s))`,
  REWRITE_TAC[MESON[]
   `(x = if p then y else z) <=> (p ==> x = y) /\ (~p ==> x = z)`] THEN
  SIMP_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  SIMP_TAC[BALL_EMPTY; CBALL_EMPTY; HAUSDIST_EMPTY; DE_MORGAN_THM] THEN
  ONCE_REWRITE_TAC[MESON[HAUSDIST_CLOSURE]
   `hausdist(s,t) = hausdist(closure s,closure t)`] THEN
  SIMP_TAC[REAL_NOT_LE; REAL_NOT_LT; CLOSURE_BALL] THEN
  REWRITE_TAC[HAUSDIST_CLOSURE] THEN
  MATCH_MP_TAC(TAUT `(s ==> p /\ q /\ r) /\ s ==> p /\ q /\ r /\ s`) THEN
  CONJ_TAC THENL [MESON_TAC[REAL_LT_IMP_LE]; REPEAT STRIP_TAC] THEN
  ASM_SIMP_TAC[HAUSDIST_NONTRIVIAL; BOUNDED_CBALL; CBALL_EQ_EMPTY;
               REAL_NOT_LT] THEN
  MATCH_MP_TAC SUP_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_GSPEC; FORALL_IN_UNION] THEN
  REWRITE_TAC[MESON[CBALL_SING] `{a} = cball(a:real^N,&0)`] THEN
  ASM_REWRITE_TAC[SETDIST_BALLS; REAL_LT_REFL] THEN
  X_GEN_TAC `c:real` THEN REWRITE_TAC[IN_CBALL] THEN
  EQ_TAC THENL [ALL_TAC; NORM_ARITH_TAC] THEN
  ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_REWRITE_TAC[DIST_SYM; DIST_REFL; REAL_MAX_LE] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC o SPEC `a + r % basis 1:real^N`)
     (MP_TAC o SPEC `a + s % basis 1:real^N`)) THEN
    REWRITE_TAC[NORM_ARITH `dist(a:real^N,a + x) = norm x`] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; LE_REFL; DIMINDEX_GE_1] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC o SPEC `a - r / dist(a,b) % (b - a):real^N`)
     (MP_TAC o SPEC `b - s / dist(a,b) % (a - b):real^N`)) THEN
    REWRITE_TAC[NORM_ARITH `dist(a:real^N,a - x) = norm x`] THEN
    REWRITE_TAC[dist; NORM_MUL; VECTOR_ARITH
     `b - e % (a - b) - a:real^N = (&1 + e) % (b - a)`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_ABS_NORM] THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REWRITE_TAC[REAL_ABS_NORM] THEN
    REWRITE_TAC[NORM_SUB; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

let HAUSDIST_ALT = prove
 (`!s t:real^N->bool.
        bounded s /\ bounded t /\ ~(s = {}) /\ ~(t = {})
        ==> hausdist(s,t) =
            sup {abs(setdist({x},s) - setdist({x},t)) | x IN (:real^N)}`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM COMPACT_CLOSURE; GSYM(CONJUNCT2 SETDIST_CLOSURE);
    GSYM CLOSURE_EQ_EMPTY; MESON[HAUSDIST_CLOSURE]
    `hausdist(s:real^N->bool,t) = hausdist(closure s,closure t)`] THEN
  SPEC_TAC(`closure t:real^N->bool`,`t:real^N->bool`) THEN
  SPEC_TAC(`closure s:real^N->bool`,`s:real^N->bool`) THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[HAUSDIST_NONTRIVIAL; COMPACT_IMP_BOUNDED] THEN
  MATCH_MP_TAC SUP_EQ THEN
  REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_GSPEC; IN_UNIV] THEN
  REWRITE_TAC[REAL_ARITH `abs(y - x) <= b <=> x <= y + b /\ y <= x + b`] THEN
  GEN_TAC THEN REWRITE_TAC[FORALL_AND_THM] THEN BINOP_TAC THEN
  (EQ_TAC THENL [ALL_TAC; MESON_TAC[SETDIST_SING_IN_SET; REAL_ADD_LID]]) THEN
  DISCH_TAC THEN X_GEN_TAC `z:real^N` THENL
   [MP_TAC(ISPECL[`{z:real^N}`; `s:real^N->bool`] SETDIST_CLOSED_COMPACT);
    MP_TAC(ISPECL[`{z:real^N}`; `t:real^N->bool`] SETDIST_CLOSED_COMPACT)] THEN
  ASM_REWRITE_TAC[CLOSED_SING; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IN_SING; RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (STRIP_ASSUME_TAC o GSYM)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL[`{y:real^N}`; `t:real^N->bool`] SETDIST_CLOSED_COMPACT);
    MP_TAC(ISPECL[`{y:real^N}`; `s:real^N->bool`] SETDIST_CLOSED_COMPACT)] THEN
  ASM_REWRITE_TAC[CLOSED_SING; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IN_SING; RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (STRIP_ASSUME_TAC o GSYM)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS `dist(z:real^N,x)` THEN
  ASM_SIMP_TAC[SETDIST_LE_DIST; IN_SING] THEN
  UNDISCH_TAC `dist(y:real^N,x) <= b` THEN CONV_TAC NORM_ARITH);;

let CONTINUOUS_DIAMETER = prove
 (`!s:real^N->bool e.
        bounded s /\ ~(s = {}) /\ &0 < e
        ==> ?d. &0 < d /\
                !t. bounded t /\ ~(t = {}) /\ hausdist(s,t) < d
                    ==> abs(diameter s - diameter t) < e`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `e / &2` THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `diameter(s:real^N->bool) - diameter(t:real^N->bool) =
                diameter(closure s) - diameter(closure t)`
  SUBST1_TAC THENL [ASM_MESON_TAC[DIAMETER_CLOSURE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&2 * hausdist(s:real^N->bool,t)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `hausdist(s:real^N->bool,t)`]
    DIAMETER_CBALL) THEN
  ASM_SIMP_TAC[HAUSDIST_POS_LE; GSYM REAL_NOT_LE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC(REAL_ARITH
   `x <= y + e /\ y <= x + e ==> abs(x - y) <= e`) THEN
  CONJ_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) DIAMETER_SUMS o rand o snd) THEN
  ASM_SIMP_TAC[BOUNDED_CBALL; BOUNDED_CLOSURE] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  MATCH_MP_TAC DIAMETER_SUBSET THEN
  ASM_SIMP_TAC[BOUNDED_SUMS; BOUNDED_CBALL; BOUNDED_CLOSURE] THEN
  ONCE_REWRITE_TAC[MESON[HAUSDIST_CLOSURE]
   `hausdist(s:real^N->bool,t) = hausdist(closure s,closure t)`]
  THENL [ALL_TAC; ONCE_REWRITE_TAC[HAUSDIST_SYM]] THEN
  MATCH_MP_TAC HAUSDIST_COMPACT_SUMS THEN
  ASM_SIMP_TAC[COMPACT_CLOSURE; BOUNDED_CLOSURE; CLOSURE_EQ_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Isometries are embeddings, and even surjective in the compact case.       *)
(* ------------------------------------------------------------------------- *)

let ISOMETRY_IMP_OPEN_MAP = prove
 (`!f:real^M->real^N s t u.
        IMAGE f s = t /\
        (!x y. x IN s /\ y IN s ==> dist(f x,f y) = dist(x,y)) /\
        open_in (subtopology euclidean s) u
        ==> open_in (subtopology euclidean t) (IMAGE f u)`,
  REWRITE_TAC[open_in; FORALL_IN_IMAGE] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `x:real^M` THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IMP_CONJ] THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
  ASM_SIMP_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]);;

let ISOMETRY_IMP_EMBEDDING = prove
 (`!f:real^M->real^N s t.
        IMAGE f s = t /\ (!x y. x IN s /\ y IN s ==> dist(f x,f y) = dist(x,y))
        ==> ?g. homeomorphism (s,t) (f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_INJECTIVE_OPEN_MAP THEN
  ASM_SIMP_TAC[ISOMETRY_ON_IMP_CONTINUOUS_ON] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIST_EQ_0]; REPEAT STRIP_TAC] THEN
  MATCH_MP_TAC ISOMETRY_IMP_OPEN_MAP THEN ASM_MESON_TAC[]);;

let ISOMETRY_IMP_HOMEOMORPHISM_COMPACT = prove
 (`!f s:real^N->bool.
        compact s /\ IMAGE f s SUBSET s /\
        (!x y. x IN s /\ y IN s ==> dist(f x,f y) = dist(x,y))
        ==> ?g. homeomorphism (s,s) (f,g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) s = s`
   (fun th -> ASM_MESON_TAC[th; ISOMETRY_IMP_EMBEDDING]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ISOMETRY_ON_IMP_CONTINUOUS_ON) THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `setdist({x},IMAGE (f:real^N->real^N) s) = &0` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
    REWRITE_TAC[SETDIST_POS_LE] THEN DISCH_TAC THEN
    (X_CHOOSE_THEN `z:num->real^N` STRIP_ASSUME_TAC o
     prove_recursive_functions_exist num_RECURSION)
     `z 0 = (x:real^N) /\ !n. z(SUC n) = f(z n)` THEN
    SUBGOAL_THEN `!n. (z:num->real^N) n IN s` ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [compact]) THEN
    DISCH_THEN(MP_TAC o SPEC `z:num->real^N`) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`l:real^N`; `r:num->num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGENT_IMP_CAUCHY) THEN
    REWRITE_TAC[cauchy] THEN
    DISCH_THEN(MP_TAC o SPEC `setdist({x},IMAGE (f:real^N->real^N) s)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:num`
     (MP_TAC o SPECL [`N:num`; `N + 1`])) THEN
    ANTS_TAC THENL [ARITH_TAC; REWRITE_TAC[REAL_NOT_LT; o_THM]] THEN
    SUBGOAL_THEN `(r:num->num) N < r (N + 1)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      REWRITE_TAC[LT_EXISTS; LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `d:num` THEN DISCH_THEN SUBST1_TAC THEN
    TRANS_TAC REAL_LE_TRANS `dist(x:real^N,z(SUC d))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SETDIST_LE_DIST THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SPEC_TAC(`(r:num->num) N`,`m:num`) THEN
    INDUCT_TAC THEN ASM_MESON_TAC[ADD_CLAUSES];
    REWRITE_TAC[SETDIST_EQ_0_SING; IMAGE_EQ_EMPTY] THEN
    ASM_MESON_TAC[COMPACT_IMP_CLOSED; NOT_IN_EMPTY;
                  COMPACT_CONTINUOUS_IMAGE; CLOSURE_CLOSED]]);;

(* ------------------------------------------------------------------------- *)
(* Urysohn's lemma (for real^N, where the proof is easy using distances).    *)
(* ------------------------------------------------------------------------- *)

let URYSOHN_LOCAL_STRONG = prove
 (`!s t u a b.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        s INTER t = {} /\ ~(a = b)
        ==> ?f:real^N->real^M.
               f continuous_on u /\
               (!x. x IN u ==> f(x) IN segment[a,b]) /\
               (!x. x IN u ==> (f x = a <=> x IN s)) /\
               (!x. x IN u ==> (f x = b <=> x IN t))`,
  let lemma = prove
   (`!s t u a b.
          closed_in (subtopology euclidean u) s /\
          closed_in (subtopology euclidean u) t /\
          s INTER t = {} /\ ~(s = {}) /\ ~(t = {}) /\ ~(a = b)
          ==> ?f:real^N->real^M.
                 f continuous_on u /\
                 (!x. x IN u ==> f(x) IN segment[a,b]) /\
                 (!x. x IN u ==> (f x = a <=> x IN s)) /\
                 (!x. x IN u ==> (f x = b <=> x IN t))`,
    REPEAT STRIP_TAC THEN EXISTS_TAC
      `\x:real^N. a + setdist({x},s) / (setdist({x},s) + setdist({x},t)) %
                      (b - a:real^M)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(!x:real^N. x IN u ==> (setdist({x},s) = &0 <=> x IN s)) /\
      (!x:real^N. x IN u ==> (setdist({x},t) = &0 <=> x IN t))`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SETDIST_EQ_0_SING] THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `s:real^N->bool` CLOSED_IN_CLOSED);
        MP_TAC(ISPEC `t:real^N->bool` CLOSED_IN_CLOSED)] THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool`
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
      ASM_MESON_TAC[CLOSURE_CLOSED; INTER_SUBSET; SUBSET_CLOSURE; SUBSET;
                    IN_INTER; CLOSURE_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x:real^N. x IN u ==> &0 < setdist({x},s) + setdist({x},t)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
        `&0 <= x /\ &0 <= y /\ ~(x = &0 /\ y = &0) ==> &0 < x + y`) THEN
      REWRITE_TAC[SETDIST_POS_LE] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      REWRITE_TAC[real_div; GSYM VECTOR_MUL_ASSOC] THEN
      REPEAT(MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; o_DEF] THEN
      REWRITE_TAC[CONTINUOUS_ON_LIFT_SETDIST] THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      REWRITE_TAC[CONTINUOUS_ON_LIFT_SETDIST];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[segment; IN_ELIM_THM] THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0; LEFT_OR_DISTRIB; VECTOR_ARITH
       `a + x % (b - a):real^N = (&1 - u) % a + u % b <=>
        (x - u) % (b - a) = vec 0`;
       EXISTS_OR_THM] THEN
      DISJ1_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
      REWRITE_TAC[REAL_SUB_0; UNWIND_THM1] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_ADD; SETDIST_POS_LE; REAL_LE_LDIV_EQ;
                   REAL_ARITH `a <= &1 * (a + b) <=> &0 <= b`];
      REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a <=> x = vec 0`];
      REWRITE_TAC[VECTOR_ARITH `a + x % (b - a):real^N = b <=>
                                (x - &1) % (b - a) = vec 0`]] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[REAL_SUB_0; REAL_EQ_LDIV_EQ;
                 REAL_MUL_LZERO; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ARITH `x:real = x + y <=> y = &0`] THEN
    ASM_REWRITE_TAC[]) in
  MATCH_MP_TAC(MESON[]
   `(!s t. P s t <=> P t s) /\
    (!s t. ~(s = {}) /\ ~(t = {}) ==> P s t) /\
    P {} {} /\ (!t. ~(t = {}) ==> P {} t)
    ==> !s t. P s t`) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV) [SWAP_FORALL_THM] THEN
    REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
    REWRITE_TAC[SEGMENT_SYM; INTER_COMM; CONJ_ACI; EQ_SYM_EQ];
    SIMP_TAC[lemma];
    REPEAT STRIP_TAC THEN EXISTS_TAC `(\x. midpoint(a,b)):real^N->real^M` THEN
    ASM_SIMP_TAC[NOT_IN_EMPTY; CONTINUOUS_ON_CONST; MIDPOINT_IN_SEGMENT] THEN
    REWRITE_TAC[midpoint] THEN CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(a:real^M = b)` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    VECTOR_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `t:real^N->bool = u` THENL
     [EXISTS_TAC `(\x. b):real^N->real^M` THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY; ENDS_IN_SEGMENT; IN_UNIV;
                      CONTINUOUS_ON_CONST];
      SUBGOAL_THEN `?c:real^N. c IN u /\ ~(c IN t)` STRIP_ASSUME_TAC THENL
       [REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET)) THEN
        REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`{c:real^N}`; `t:real^N->bool`; `u:real^N->bool`;
                     `midpoint(a,b):real^M`; `b:real^M`] lemma) THEN
      ASM_REWRITE_TAC[CLOSED_IN_SING; MIDPOINT_EQ_ENDPOINT] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[NOT_IN_EMPTY] THEN
      X_GEN_TAC `f:real^N->real^M` THEN STRIP_TAC THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `segment[midpoint(a,b):real^M,b] SUBSET segment[a,b]` MP_TAC
        THENL
         [REWRITE_TAC[SUBSET; IN_SEGMENT; midpoint] THEN GEN_TAC THEN
          DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `(&1 + u) / &2` THEN ASM_REWRITE_TAC[] THEN
          REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
          VECTOR_ARITH_TAC;
          ASM SET_TAC[]];
        SUBGOAL_THEN `~(a IN segment[midpoint(a,b):real^M,b])` MP_TAC THENL
         [ALL_TAC; ASM_MESON_TAC[]] THEN
        DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP DIST_IN_CLOSED_SEGMENT) THEN
        REWRITE_TAC[DIST_MIDPOINT] THEN
        UNDISCH_TAC `~(a:real^M = b)` THEN NORM_ARITH_TAC]]]);;

let URYSOHN_LOCAL = prove
 (`!s t u a b.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        s INTER t = {}
        ==> ?f:real^N->real^M.
               f continuous_on u /\
               (!x. x IN u ==> f(x) IN segment[a,b]) /\
               (!x. x IN s ==> f x = a) /\
               (!x. x IN t ==> f x = b)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a:real^M = b` THENL
   [EXISTS_TAC `(\x. b):real^N->real^M` THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT; CONTINUOUS_ON_CONST];
    MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `u:real^N->bool`;
                   `a:real^M`; `b:real^M`] URYSOHN_LOCAL_STRONG) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET)) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN SET_TAC[]]);;

let URYSOHN_STRONG = prove
 (`!s t a b.
        closed s /\ closed t /\ s INTER t = {} /\ ~(a = b)
        ==> ?f:real^N->real^M.
               f continuous_on (:real^N) /\ (!x. f(x) IN segment[a,b]) /\
               (!x. f x = a <=> x IN s) /\ (!x. f x = b <=> x IN t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN] THEN
  ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP URYSOHN_LOCAL_STRONG) THEN
  REWRITE_TAC[IN_UNIV]);;

let URYSOHN = prove
 (`!s t a b.
        closed s /\ closed t /\ s INTER t = {}
        ==> ?f:real^N->real^M.
               f continuous_on (:real^N) /\ (!x. f(x) IN segment[a,b]) /\
               (!x. x IN s ==> f x = a) /\ (!x. x IN t ==> f x = b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN] THEN
  ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN DISCH_THEN
   (MP_TAC o ISPECL [`a:real^M`; `b:real^M`] o MATCH_MP URYSOHN_LOCAL) THEN
  REWRITE_TAC[IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Countability of some relevant sets.                                       *)
(* ------------------------------------------------------------------------- *)

let COUNTABLE_INTEGER = prove
 (`COUNTABLE integer`,
  MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC
   `IMAGE (\n. (&n:real)) (:num) UNION IMAGE (\n. --(&n)) (:num)` THEN
  SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_UNION; NUM_COUNTABLE] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE; IN_UNIV] THEN
  REWRITE_TAC[IN; INTEGER_CASES]);;

let CARD_EQ_INTEGER = prove
 (`integer =_c (:num)`,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM; GSYM COUNTABLE_ALT; COUNTABLE_INTEGER] THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC `real_of_num` THEN
  REWRITE_TAC[IN_UNIV; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[IN; INTEGER_CLOSED]);;

let COUNTABLE_RATIONAL = prove
 (`COUNTABLE rational`,
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(x,y). x / y) (integer CROSS integer)` THEN
  SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_CROSS; COUNTABLE_INTEGER] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[rational; IN] THEN MESON_TAC[]);;

let CARD_EQ_RATIONAL = prove
 (`rational =_c (:num)`,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM; GSYM COUNTABLE_ALT; COUNTABLE_RATIONAL] THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC `real_of_num` THEN
  REWRITE_TAC[IN_UNIV; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[IN; RATIONAL_CLOSED]);;

let COUNTABLE_INTEGER_COORDINATES = prove
 (`COUNTABLE { x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) }`,
  MATCH_MP_TAC COUNTABLE_CART THEN
  REWRITE_TAC[SET_RULE `{x | P x} = P`; COUNTABLE_INTEGER]);;

let COUNTABLE_RATIONAL_COORDINATES = prove
 (`COUNTABLE { x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) }`,
  MATCH_MP_TAC COUNTABLE_CART THEN
  REWRITE_TAC[SET_RULE `{x | P x} = P`; COUNTABLE_RATIONAL]);;

(* ------------------------------------------------------------------------- *)
(* Density of points with rational, or just dyadic rational, coordinates.    *)
(* ------------------------------------------------------------------------- *)

let CLOSURE_DYADIC_RATIONALS = prove
 (`closure { inv(&2 pow n) % x |n,x|
             !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) } = (:real^N)`,
  REWRITE_TAC[EXTENSION; CLOSURE_APPROACHABLE; IN_UNIV; EXISTS_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `e:real`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`inv(&2)`; `e / &(dimindex(:N))`] REAL_ARCH_POW_INV) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1;
               REAL_POW_INV; REAL_LT_RDIV_EQ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC MONO_EXISTS THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  EXISTS_TAC `(lambda i. floor(&2 pow n * (x:real^N)$i)):real^N` THEN
  ASM_SIMP_TAC[LAMBDA_BETA; FLOOR; dist; NORM_MUL] THEN
  MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS)
   (SPEC_ALL NORM_LE_L1)) THEN
  SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&(dimindex(:N)) * inv(&2 pow n)` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  SIMP_TAC[REAL_ABS_MUL; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH;
    REAL_FIELD `~(a = &0) ==> inv a * b - x = inv a * (b - a * x)`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REWRITE_TAC[REAL_LE_REFL; REAL_ABS_POW; REAL_ABS_INV; REAL_ABS_NUM] THEN
  MP_TAC(SPEC `&2 pow n * (x:real^N)$k` FLOOR) THEN REAL_ARITH_TAC);;

let CLOSURE_RATIONAL_COORDINATES = prove
 (`closure { x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) } =
   (:real^N)`,
  MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
  EXISTS_TAC
   `closure { inv(&2 pow n) % x:real^N |n,x|
              !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) }` THEN

  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[CLOSURE_DYADIC_RATIONALS]] THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM; VECTOR_MUL_COMPONENT] THEN
  ASM_SIMP_TAC[RATIONAL_CLOSED]);;

let CLOSURE_DYADIC_RATIONALS_IN_OPEN_SET = prove
 (`!s:real^N->bool.
        open s
        ==> closure(s INTER
                    { inv(&2 pow n) % x | n,x |
                      !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) }) =
            closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_OPEN_INTER_SUPERSET THEN
  ASM_REWRITE_TAC[CLOSURE_DYADIC_RATIONALS; SUBSET_UNIV]);;

let CLOSURE_RATIONALS_IN_OPEN_SET = prove
 (`!s:real^N->bool.
        open s
        ==> closure(s INTER
                    { inv(&2 pow n) % x | n,x |
                      !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) }) =
            closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_OPEN_INTER_SUPERSET THEN
  ASM_REWRITE_TAC[CLOSURE_DYADIC_RATIONALS; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Various separability-type properties.                                     *)
(* ------------------------------------------------------------------------- *)

let UNIV_SECOND_COUNTABLE = prove
 (`?b. COUNTABLE b /\ (!c. c IN b ==> open c) /\
       !s:real^N->bool. open s ==> ?u. u SUBSET b /\ s = UNIONS u`,
  EXISTS_TAC
   `IMAGE (\(v:real^N,q). ball(v,q))
          ({v | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(v$i)} CROSS
           rational)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_IMAGE THEN MATCH_MP_TAC COUNTABLE_CROSS THEN
    REWRITE_TAC[COUNTABLE_RATIONAL] THEN MATCH_MP_TAC COUNTABLE_CART THEN
    REWRITE_TAC[COUNTABLE_RATIONAL; SET_RULE `{x | P x} = P`];
    REWRITE_TAC[FORALL_IN_IMAGE; CROSS; FORALL_IN_GSPEC; OPEN_BALL];
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THENL
     [EXISTS_TAC `{}:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[UNIONS_0; EMPTY_SUBSET];
      ALL_TAC] THEN
    EXISTS_TAC `{c | c IN IMAGE (\(v:real^N,q). ball(v,q))
          ({v | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(v$i)} CROSS
           rational) /\ c SUBSET s}` THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[CROSS; EXISTS_PAIR_THM; EXISTS_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET; IN_BALL] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(REWRITE_RULE[EXTENSION; IN_UNIV] CLOSURE_RATIONAL_COORDINATES) THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `e / &4`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[IN_ELIM_THM]] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?x. rational x /\ e / &3 < x /\ x < e / &2`
     (X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC)
    THENL
     [MP_TAC(ISPECL [`&5 / &12 * e`; `e / &12`] RATIONAL_APPROXIMATION) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS] THEN
      SIMP_TAC[] THEN REAL_ARITH_TAC;
      EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[IN];
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC;
        ASM_REAL_ARITH_TAC]]]);;

let UNIV_SECOND_COUNTABLE_SEQUENCE = prove
 (`?b:num->real^N->bool.
        (!m n. b m = b n <=> m = n) /\
        (!n. open(b n)) /\
        (!s. open s ==> ?k. s = UNIONS {b n | n IN k})`,
  X_CHOOSE_THEN `bb:(real^N->bool)->bool` STRIP_ASSUME_TAC
    UNIV_SECOND_COUNTABLE THEN
  MP_TAC(ISPEC `bb:(real^N->bool)->bool` COUNTABLE_AS_INJECTIVE_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `INFINITE {ball(vec 0:real^N,inv(&n + &1)) | n IN (:num)}`
    MP_TAC THENL
     [REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC(REWRITE_RULE
       [RIGHT_IMP_FORALL_THM; IMP_IMP] INFINITE_IMAGE_INJ) THEN
      REWRITE_TAC[num_INFINITE] THEN MATCH_MP_TAC WLOG_LT THEN SIMP_TAC[] THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
      REWRITE_TAC[EXTENSION] THEN
      DISCH_THEN(MP_TAC o SPEC `inv(&n + &1) % basis 1:real^N`) THEN
      REWRITE_TAC[IN_BALL; DIST_0; NORM_MUL; REAL_ABS_INV] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_MUL_RID] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_ARITH `abs(&n + &1) = &n + &1`; REAL_LT_REFL] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN ASM_ARITH_TAC;
      REWRITE_TAC[INFINITE; SIMPLE_IMAGE] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE UNIONS {u | u SUBSET bb} :(real^N->bool)->bool` THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_POWERSET] THEN
      GEN_REWRITE_TAC I [SUBSET] THEN SIMP_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[OPEN_BALL]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FORALL_IN_IMAGE; IN_UNIV]) THEN
    REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
    ASM_REWRITE_TAC[SUBSET_IMAGE; LEFT_AND_EXISTS_THM; SUBSET_UNIV] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SIMPLE_IMAGE]]);;

let SUBSET_SECOND_COUNTABLE = prove
 (`!s:real^N->bool.
       ?b. COUNTABLE b /\
           (!c. c IN b ==> ~(c = {}) /\ open_in(subtopology euclidean s) c) /\
           !t. open_in(subtopology euclidean s) t
               ==> ?u. u SUBSET b /\ t = UNIONS u`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `?b. COUNTABLE b /\
           (!c:real^N->bool. c IN b ==> open_in(subtopology euclidean s) c) /\
           !t. open_in(subtopology euclidean s) t
               ==> ?u. u SUBSET b /\ t = UNIONS u`
  STRIP_ASSUME_TAC THENL
   [X_CHOOSE_THEN `B:(real^N->bool)->bool` STRIP_ASSUME_TAC
      UNIV_SECOND_COUNTABLE THEN
    EXISTS_TAC `{s INTER c :real^N->bool | c IN B}` THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; EXISTS_SUBSET_IMAGE; OPEN_IN_OPEN_INTER] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    X_GEN_TAC `t:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `?b. b SUBSET B /\ u:real^N->bool = UNIONS b`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    EXISTS_TAC `b:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INTER_UNIONS] THEN AP_TERM_TAC THEN SET_TAC[];
    EXISTS_TAC `b DELETE ({}:real^N->bool)` THEN
    ASM_SIMP_TAC[COUNTABLE_DELETE; IN_DELETE; SUBSET_DELETE] THEN
    X_GEN_TAC `t:real^N->bool` THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u DELETE ({}:real^N->bool)` THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS] THEN
    GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    REWRITE_TAC[IN_DELETE] THEN SET_TAC[]]);;

let SEPARABLE = prove
 (`!s:real^N->bool.
        ?t. COUNTABLE t /\ t SUBSET s /\ s SUBSET closure t`,
  MP_TAC SUBSET_SECOND_COUNTABLE THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `s:real^N->bool` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_AND_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:(real^N->bool)->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:(real^N->bool)->real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE (f:(real^N->bool)->real^N) B` THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; CLOSURE_APPROACHABLE; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    UNDISCH_THEN
     `!t:real^N->bool.
        open_in (subtopology euclidean s) t
        ==> (?u. u SUBSET B /\ t = UNIONS u)`
     (MP_TAC o SPEC `s INTER ball(x:real^N,e)`) THEN
    SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `b:(real^N->bool)->bool` THEN
    ASM_CASES_TAC `b:(real^N->bool)->bool = {}` THENL
     [MATCH_MP_TAC(TAUT `~b ==> a /\ b ==> c`) THEN
      ASM_REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; UNIONS_0] THEN
      ASM_MESON_TAC[CENTRE_IN_BALL];
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N->bool` THEN
      DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
      DISCH_THEN(MP_TAC o SPEC `(f:(real^N->bool)->real^N) c`) THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN
      MATCH_MP_TAC(TAUT `a /\ c ==> (a /\ b <=> c) ==> b`) THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN] THEN
      ASM SET_TAC[]]]);;

let OPEN_SET_RATIONAL_COORDINATES = prove
 (`!s. open s /\ ~(s = {})
       ==> ?x:real^N. x IN s /\
                      !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `~(closure { x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) } INTER
    (s:real^N->bool) = {})`
  MP_TAC THENL
   [ASM_REWRITE_TAC[CLOSURE_RATIONAL_COORDINATES; INTER_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; CLOSURE_APPROACHABLE; IN_INTER;
              IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o REWRITE_RULE[open_def]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let OPEN_COUNTABLE_UNION_OPEN_INTERVALS,
    OPEN_COUNTABLE_UNION_CLOSED_INTERVALS = (CONJ_PAIR o prove)
 (`(!s:real^N->bool.
        open s
        ==> ?D. COUNTABLE D /\
                (!i. i IN D ==> i SUBSET s /\ ?a b. i = interval(a,b)) /\
                UNIONS D = s) /\
   (!s:real^N->bool.
        open s
        ==> ?D. COUNTABLE D /\
                (!i. i IN D ==> i SUBSET s /\ ?a b. i = interval[a,b]) /\
                UNIONS D = s)`,
  REPEAT STRIP_TAC THENL
   [EXISTS_TAC
     `{i | i IN IMAGE (\(a:real^N,b). interval(a,b))
            ({x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i)} CROSS
             {x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i)}) /\
           i SUBSET s}`;
    EXISTS_TAC
     `{i | i IN IMAGE (\(a:real^N,b). interval[a,b])
            ({x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i)} CROSS
             {x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i)}) /\
           i SUBSET s}`] THEN
  (SIMP_TAC[COUNTABLE_RESTRICT; COUNTABLE_IMAGE; COUNTABLE_CROSS;
           COUNTABLE_RATIONAL_COORDINATES] THEN
   REWRITE_TAC[IN_ELIM_THM; UNIONS_GSPEC; IMP_CONJ; GSYM CONJ_ASSOC] THEN
   REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
   REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
   CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
   X_GEN_TAC `x:real^N` THEN EQ_TAC THENL [SET_TAC[]; DISCH_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o REWRITE_RULE[open_def]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
    `!i. 1 <= i /\ i <= dimindex(:N)
         ==> ?a b. rational a /\ rational b /\
                   a < (x:real^N)$i /\ (x:real^N)$i < b /\
                   abs(b - a) < e / &(dimindex(:N))`
   MP_TAC THENL
    [REPEAT STRIP_TAC THEN MATCH_MP_TAC RATIONAL_APPROXIMATION_STRADDLE THEN
     ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1];
     REWRITE_TAC[LAMBDA_SKOLEM]] THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN
   DISCH_TAC THEN ASM_SIMP_TAC[SUBSET; IN_INTERVAL; REAL_LT_IMP_LE] THEN
   X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC[dist] THEN MP_TAC(ISPEC `y - x:real^N` NORM_LE_L1) THEN
   MATCH_MP_TAC(REAL_ARITH `s < e ==> n <= s ==> n < e`) THEN
   MATCH_MP_TAC SUM_BOUND_LT_GEN THEN
   REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; CARD_NUMSEG_1] THEN
   REWRITE_TAC[DIMINDEX_GE_1; IN_NUMSEG; VECTOR_SUB_COMPONENT] THEN
   X_GEN_TAC `k:num` THEN STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `k:num`)) THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC));;

let LINDELOF = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> open s)
        ==> ?f'. f' SUBSET f /\ COUNTABLE f' /\ UNIONS f' = UNIONS f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?b. COUNTABLE b /\
        (!c:real^N->bool. c IN b ==> open c) /\
        (!s. open s ==> ?u. u SUBSET b /\ s = UNIONS u)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[UNIV_SECOND_COUNTABLE]; ALL_TAC] THEN
  ABBREV_TAC
   `d = {s:real^N->bool | s IN b /\ ?u. u IN f /\ s SUBSET u}` THEN
  SUBGOAL_THEN
   `COUNTABLE d /\ UNIONS f :real^N->bool = UNIONS d`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_SIMP_TAC[COUNTABLE_RESTRICT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. ?u. s IN d ==> u IN f /\ s SUBSET u`
  MP_TAC THENL [EXPAND_TAC "d" THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:(real^N->bool)->(real^N->bool)` THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (g:(real^N->bool)->(real^N->bool)) d` THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; UNIONS_IMAGE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[]);;

let LINDELOF_OPEN_IN = prove
 (`!f u:real^N->bool.
        (!s. s IN f ==> open_in (subtopology euclidean u) s)
        ==> ?f'. f' SUBSET f /\ COUNTABLE f' /\ UNIONS f' = UNIONS f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `v:(real^N->bool)->real^N->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (v:(real^N->bool)->real^N->bool) f` LINDELOF) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REWRITE_TAC[EXISTS_COUNTABLE_SUBSET_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f':(real^N->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
  `!f'. f' SUBSET f ==> UNIONS f' = (u:real^N->bool) INTER UNIONS (IMAGE v f')`
  MP_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[SUBSET_REFL]]);;

let COUNTABLE_DISJOINT_OPEN_SUBSETS = prove
 (`!f. (!s:real^N->bool. s IN f ==> open s) /\ pairwise DISJOINT f
       ==> COUNTABLE f`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP LINDELOF) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC `({}:real^N->bool) INSERT g` THEN
  ASM_REWRITE_TAC[COUNTABLE_INSERT] THEN
  REWRITE_TAC[SUBSET; IN_INSERT] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[EXTENSION; SUBSET] THEN
  REWRITE_TAC[IN_UNIONS; pairwise] THEN
  REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. ~(x IN s /\ x IN t)`] THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN MESON_TAC[]);;

let CARD_EQ_OPEN_SETS = prove
 (`{s:real^N->bool | open s} =_c (:real)`,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [X_CHOOSE_THEN `b:(real^N->bool)->bool` STRIP_ASSUME_TAC
      UNIV_SECOND_COUNTABLE THEN
    TRANS_TAC CARD_LE_TRANS `{s:(real^N->bool)->bool | s SUBSET b}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LE_C] THEN
      EXISTS_TAC `UNIONS:((real^N->bool)->bool)->real^N->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      TRANS_TAC CARD_LE_TRANS `{s | s SUBSET (:num)}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CARD_LE_POWERSET THEN ASM_REWRITE_TAC[GSYM COUNTABLE_ALT];
        REWRITE_TAC[SUBSET_UNIV; UNIV_GSPEC] THEN
        MESON_TAC[CARD_EQ_IMP_LE; CARD_EQ_SYM; CARD_EQ_REAL]]];
    REWRITE_TAC[le_c; IN_UNIV; IN_ELIM_THM] THEN
    EXISTS_TAC `\x. ball(x % basis 1:real^N,&1)` THEN
    REWRITE_TAC[OPEN_BALL; GSYM SUBSET_ANTISYM_EQ; SUBSET_BALLS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[NORM_ARITH `dist(p:real^N,q) + &1 <= &1 <=> p = q`] THEN
    REWRITE_TAC[VECTOR_MUL_RCANCEL; EQ_SYM_EQ] THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; ARITH]]);;

let CARD_EQ_CLOSED_SETS = prove
 (`{s:real^N->bool | closed s} =_c (:real)`,
  SUBGOAL_THEN
   `{s:real^N->bool | closed s} =
    IMAGE (\s. (:real^N) DIFF s) {s | open s}`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM OPEN_CLOSED] THEN
    MESON_TAC[SET_RULE `UNIV DIFF (UNIV DIFF s) = s`];
    TRANS_TAC CARD_EQ_TRANS `{s:real^N->bool | open s}` THEN
    REWRITE_TAC[CARD_EQ_OPEN_SETS] THEN
    MATCH_MP_TAC CARD_EQ_IMAGE THEN SET_TAC[]]);;

let CARD_EQ_COMPACT_SETS = prove
 (`{s:real^N->bool | compact s} =_c (:real)`,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `{s:real^N->bool | closed s}` THEN
    SIMP_TAC[CARD_EQ_IMP_LE; CARD_EQ_CLOSED_SETS] THEN
    MATCH_MP_TAC CARD_LE_SUBSET THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; COMPACT_IMP_CLOSED];
    REWRITE_TAC[le_c; IN_UNIV; IN_ELIM_THM] THEN
    EXISTS_TAC `\x. {x % basis 1:real^N}` THEN
    REWRITE_TAC[COMPACT_SING; SET_RULE `{x} = {y} <=> x = y`] THEN
    SIMP_TAC[VECTOR_MUL_RCANCEL; BASIS_NONZERO; DIMINDEX_GE_1; ARITH]]);;

let COUNTABLE_NON_CONDENSATION_POINTS = prove
 (`!s:real^N->bool. COUNTABLE(s DIFF {x | x condensation_point_of s})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[condensation_point_of] THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  X_CHOOSE_THEN `b:(real^N->bool)->bool` STRIP_ASSUME_TAC
   UNIV_SECOND_COUNTABLE THEN
  EXISTS_TAC
   `s INTER UNIONS { u:real^N->bool | u IN b /\ COUNTABLE(s INTER u)}` THEN
  REWRITE_TAC[INTER_UNIONS; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_UNIONS THEN SIMP_TAC[FORALL_IN_GSPEC] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_RESTRICT];
    SIMP_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER; IN_DIFF] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?u:real^N->bool. x IN u /\ u IN b /\ u SUBSET t` MP_TAC THENL
     [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC `s INTER t:real^N->bool` THEN ASM SET_TAC[]]);;

let CARD_EQ_CONDENSATION_POINTS_IN_SET = prove
 (`!s:real^N->bool.
     ~(COUNTABLE s) ==> {x | x IN s /\ x condensation_point_of s} =_c s`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_EQ_TRANS
   `(s DIFF {x | x condensation_point_of s}) +_c
    {x:real^N | x IN s /\ x condensation_point_of s}` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN MATCH_MP_TAC CARD_ADD_ABSORB THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
      DISCH_THEN(MP_TAC o CONJ (SPEC `s:real^N->bool`
       COUNTABLE_NON_CONDENSATION_POINTS) o MATCH_MP FINITE_IMP_COUNTABLE) THEN
      REWRITE_TAC[GSYM COUNTABLE_UNION] THEN MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN SET_TAC[];
      REWRITE_TAC[INFINITE_CARD_LE] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CARD_LE_TRANS) THEN
      REWRITE_TAC[GSYM COUNTABLE_ALT; COUNTABLE_NON_CONDENSATION_POINTS]];
    ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
    W(MP_TAC o PART_MATCH (rand o rand) CARD_DISJOINT_UNION o rand o snd) THEN
    ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]]);;

let LIMPT_OF_CONDENSATION_POINTS,CONDENSATION_POINT_OF_CONDENSATION_POINTS =
  (CONJ_PAIR o prove)
 (`(!x:real^N s.
        x limit_point_of {y | y condensation_point_of s} <=>
        x condensation_point_of s) /\
   (!x:real^N s.
        x condensation_point_of {y | y condensation_point_of s} <=>
        x condensation_point_of s)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(r ==> q) /\ (q ==> p) /\ (p ==> r)
    ==> (q <=> p) /\ (r <=> p)`) THEN
  REWRITE_TAC[CONDENSATION_POINT_IMP_LIMPT] THEN CONJ_TAC THENL
   [REWRITE_TAC[LIMPT_APPROACHABLE; CONDENSATION_POINT_INFINITE_BALL] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
    SIMP_TAC[SUBSET; IN_INTER; IN_BALL] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC;
    ONCE_REWRITE_TAC[CONDENSATION_POINT_INFINITE_BALL] THEN DISCH_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN DISCH_THEN(MP_TAC o MATCH_MP
     (MESON[CARD_EQ_CONDENSATION_POINTS_IN_SET; CARD_COUNTABLE_CONG]
        `~COUNTABLE s
         ==> ~COUNTABLE {x | x IN s /\ x condensation_point_of s}`)) THEN
    REWRITE_TAC[UNCOUNTABLE_REAL; CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `y:real^N` THEN
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[CONDENSATION_POINT_OF_SUBSET; INTER_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `closure(s INTER ball(x:real^N,e / &2))` THEN CONJ_TAC THENL
     [REWRITE_TAC[closure; IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN
      ASM_SIMP_TAC[CONDENSATION_POINT_IMP_LIMPT];
      TRANS_TAC SUBSET_TRANS `closure(ball(x:real^N,e / &2))` THEN
      SIMP_TAC[SUBSET_CLOSURE; INTER_SUBSET] THEN
      ASM_SIMP_TAC[CLOSURE_BALL; REAL_HALF; SUBSET_BALLS; DIST_REFL] THEN
      ASM_REAL_ARITH_TAC]]);;

let CLOSED_CONDENSATION_POINTS = prove
 (`!s:real^N->bool. closed {x | x condensation_point_of s}`,
  SIMP_TAC[CLOSED_LIMPT; LIMPT_OF_CONDENSATION_POINTS; IN_ELIM_THM]);;

let CANTOR_BENDIXSON = prove
 (`!s:real^N->bool.
        closed s
        ==> ?t u. closed t /\ (!x. x IN t ==> x limit_point_of t) /\
                  COUNTABLE u /\ s = t UNION u`,
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`{x:real^N | x condensation_point_of s}`;
    `s DIFF {x:real^N | x condensation_point_of s}`] THEN
  REWRITE_TAC[COUNTABLE_NON_CONDENSATION_POINTS; CLOSED_CONDENSATION_POINTS;
              IN_ELIM_THM; LIMPT_OF_CONDENSATION_POINTS] THEN
  REWRITE_TAC[SET_RULE `s = t UNION (s DIFF t) <=> t SUBSET s`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSED_LIMPT]) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  ASM_MESON_TAC[CONDENSATION_POINT_IMP_LIMPT]);;

(* ------------------------------------------------------------------------- *)
(* A discrete set is countable, and an uncountable set has a limit point.    *)
(* ------------------------------------------------------------------------- *)

let DISCRETE_IMP_COUNTABLE = prove
 (`!s:real^N->bool.
        (!x. x IN s ==> ?e. &0 < e /\
                            !y. y IN s /\ ~(y = x) ==> e <= norm(y - x))
        ==> COUNTABLE s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN s
        ==> ?q. (!i. 1 <= i /\ i <= dimindex(:N) ==> rational(q$i)) /\
                !y:real^N. y IN s /\ ~(y = x) ==> norm(x - q) < norm(y - q)`
  MP_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SET_RULE `x IN (:real^N)`) THEN
    REWRITE_TAC[GSYM CLOSURE_RATIONAL_COORDINATES] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC;
    POP_ASSUM(K ALL_TAC) THEN
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `q:real^N->real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`s:real^N->bool`;
      `{ x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) }`;
      `(:num)`] CARD_LE_TRANS) THEN
    REWRITE_TAC[COUNTABLE; ge_c] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[REWRITE_RULE[COUNTABLE; ge_c] COUNTABLE_RATIONAL_COORDINATES] THEN
    REWRITE_TAC[le_c] THEN EXISTS_TAC `q:real^N->real^N` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LT_ANTISYM]]);;

let UNCOUNTABLE_CONTAINS_LIMIT_POINT = prove
 (`!s. ~(COUNTABLE s) ==> ?x. x IN s /\ x limit_point_of s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] DISCRETE_IMP_COUNTABLE)) THEN
  REWRITE_TAC[LIMPT_APPROACHABLE; GSYM REAL_NOT_LT; dist] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Brouwer reduction theorem.                                            *)
(* ------------------------------------------------------------------------- *)

let BROUWER_REDUCTION_THEOREM_GEN = prove
 (`!P s:real^N->bool.
        (!f. (!n. closed(f n) /\ P(f n)) /\ (!n. f(SUC n) SUBSET f(n))
              ==> P(INTERS {f n | n IN (:num)})) /\
        closed s /\ P s
        ==> ?t. t SUBSET s /\ closed t /\ P t /\
                (!u. u SUBSET s /\ closed u /\ P u ==> ~(u PSUBSET t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?b:num->real^N->bool.
        (!m n. b m = b n <=> m = n) /\
        (!n. open (b n)) /\
        (!s. open s ==> (?k. s = UNIONS {b n | n IN k}))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[UNIV_SECOND_COUNTABLE_SEQUENCE]; ALL_TAC] THEN
  X_CHOOSE_THEN `a:num->real^N->bool` MP_TAC
   (prove_recursive_functions_exist num_RECURSION
   `a 0 = (s:real^N->bool) /\
    (!n. a(SUC n) =
         if ?u. u SUBSET a(n) /\ closed u /\ P u /\ u INTER (b n) = {}
         then @u. u SUBSET a(n) /\ closed u /\ P u /\ u INTER (b n) = {}
         else a(n))`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "base") (LABEL_TAC "step")) THEN
  EXISTS_TAC `INTERS {a n :real^N->bool | n IN (:num)}` THEN
  SUBGOAL_THEN `!n. (a:num->real^N->bool)(SUC n) SUBSET a(n)` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[SUBSET_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (a:num->real^N->bool) n SUBSET s` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_MESON_TAC[SUBSET_REFL; SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. closed((a:num->real^N->bool) n) /\ P(a n)` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC CLOSED_INTERS THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[PSUBSET_ALT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[INTERS_GSPEC; EXISTS_IN_GSPEC; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?n. x IN (b:num->real^N->bool)(n) /\ t INTER b n = {}`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `(:real^N) DIFF t` OPEN_CONTAINS_BALL) THEN
      ASM_REWRITE_TAC[GSYM closed] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> t INTER s = {}`] THEN
      X_GEN_TAC `e:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      MP_TAC(ISPECL [`x:real^N`; `e:real`] CENTRE_IN_BALL) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `ball(x:real^N,e)`) THEN
      ASM_REWRITE_TAC[OPEN_BALL; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `k:num->bool` THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[IN_UNIONS; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
      SET_TAC[];
      REMOVE_THEN "step" (MP_TAC o SPEC `n:num`) THEN
      COND_CASES_TAC THENL
       [DISCH_THEN(ASSUME_TAC o SYM) THEN
        FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[];
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
        DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[]]]]);;

let BROUWER_REDUCTION_THEOREM = prove
 (`!P s:real^N->bool.
        (!f. (!n. compact(f n) /\ ~(f n = {}) /\ P(f n)) /\
             (!n. f(SUC n) SUBSET f(n))
             ==> P(INTERS {f n | n IN (:num)})) /\
        compact s /\ ~(s = {}) /\ P s
        ==> ?t. t SUBSET s /\ compact t /\ ~(t = {}) /\ P t /\
                (!u. u SUBSET s /\ closed u /\ ~(u = {}) /\ P u
                     ==> ~(u PSUBSET t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t:real^N->bool. ~(t = {}) /\ t SUBSET s /\ P t`;
                 `s:real^N->bool`]
        BROUWER_REDUCTION_THEOREM_GEN) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; SUBSET_REFL] THEN ANTS_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `!n. compact((f:num->real^N->bool) n)` ASSUME_TAC THENL
     [ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_SUBSET]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_NEST THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_SIMP_TAC[] THEN SET_TAC[];
      ASM SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* The Arzela-Ascoli theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let SUBSEQUENCE_DIAGONALIZATION_LEMMA = prove
 (`!P:num->(num->A)->bool.
    (!i r:num->A. ?k. (!m n. m < n ==> k m < k n) /\ P i (r o k)) /\
    (!i r:num->A k1 k2 N.
        P i (r o k1) /\ (!j. N <= j ==> ?j'. j <= j' /\ k2 j = k1 j')
        ==> P i (r o k2))
    ==> !r:num->A. ?k. (!m n. m < n ==> k m < k n) /\ (!i. P i (r o k))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [SKOLEM_THM] THEN
  REWRITE_TAC[FORALL_AND_THM; TAUT
   `(p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)`] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `kk:num->(num->A)->num->num` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `r:num->A` THEN
  (STRIP_ASSUME_TAC o prove_recursive_functions_exist num_RECURSION)
    `(rr 0 = (kk:num->(num->A)->num->num) 0 r) /\
     (!n. rr(SUC n) = rr n o kk (SUC n) (r o rr n))` THEN
  EXISTS_TAC `\n. (rr:num->num->num) n n` THEN REWRITE_TAC[ETA_AX] THEN
  SUBGOAL_THEN
   `(!i. (!m n. m < n ==> (rr:num->num->num) i m < rr i n)) /\
    (!i. (P:num->(num->A)->bool) i (r o rr i))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[AND_FORALL_THM] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[o_ASSOC] THEN
    REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j n. i <= j ==> (rr:num->num->num) i n <= rr j n`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
    SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN SPEC_TAC(`j:num`,`j:num`) THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN SIMP_TAC[FORALL_UNWIND_THM2] THEN
    INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] LE_TRANS)) THEN REWRITE_TAC[o_THM] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (MESON[LE_LT]
       `!f:num->num.
        (!m n. m < n ==> f m < f n) ==> (!m n. m <= n ==> f m <= f n)`) o
       SPEC `i + d:num`) THEN
    SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC MONOTONE_BIGGER THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `(rr:num->num->num) n m` THEN
    ASM_MESON_TAC[LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m n i. n <= m ==> ?j. i <= j /\ (rr:num->num->num) m i = rr n j`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `i:num` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(rr:num->num->num) i` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `i:num` THEN ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN
   `!p d i. ?j. i <= j /\ (rr:num->num->num) (p + d) i = rr p j`
   (fun th -> MESON_TAC[LE_EXISTS; th]) THEN
  X_GEN_TAC `p:num` THEN  MATCH_MP_TAC num_INDUCTION THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN CONJ_TAC THENL
   [MESON_TAC[LE_REFL]; ALL_TAC] THEN
  X_GEN_TAC `d:num` THEN DISCH_THEN(LABEL_TAC "+") THEN
  X_GEN_TAC `i:num` THEN ASM_REWRITE_TAC[o_THM] THEN
  REMOVE_THEN "+" (MP_TAC o SPEC
   `(kk:num->(num->A)->num->num) (SUC(p + d))
        ((r:num->A) o (rr:num->num->num) (p + d)) i`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:num` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LE_TRANS) THEN
  SPEC_TAC(`i:num`,`i:num`) THEN MATCH_MP_TAC MONOTONE_BIGGER THEN
  ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

let FUNCTION_CONVERGENT_SUBSEQUENCE = prove
 (`!f:num->real^M->real^N s M.
        COUNTABLE s /\ (!n x. x IN s ==> norm(f n x) <= M)
        ==> ?k. (!m n:num. m < n ==> k m < k n) /\
                !x. x IN s ==> ?l. ((\n. f (k n) x) --> l) sequentially`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [EXISTS_TAC `\n:num. n` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^M->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `X:num->real^M` THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPEC
    `\i r. ?l. ((\n. ((f:num->real^M->real^N) o (r:num->num)) n
                     ((X:num->real^M) i)) --> l) sequentially`
   SUBSEQUENCE_DIAGONALIZATION_LEMMA) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; o_THM; IN_UNIV] THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN MATCH_ACCEPT_TAC] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[FORALL_IN_IMAGE; IN_UNIV]) THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `r:num->num`] THEN
    MP_TAC(ISPEC `cball(vec 0:real^N,M)` compact) THEN
    REWRITE_TAC[COMPACT_CBALL] THEN DISCH_THEN(MP_TAC o SPEC
     `\n. (f:num->real^M->real^N) ((r:num->num) n) (X(i:num))`) THEN
    ASM_REWRITE_TAC[IN_CBALL_0; o_DEF] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY; GE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[LE_TRANS; ARITH_RULE `MAX a b <= c <=> a <= c /\ b <= c`]]);;

let ARZELA_ASCOLI = prove
 (`!f:num->real^M->real^N s M.
        compact s /\
        (!n x. x IN s ==> norm(f n x) <= M) /\
        (!x e. x IN s /\ &0 < e
               ==> ?d. &0 < d /\
                       !n y. y IN s /\ norm(x - y) < d
                             ==> norm(f n x - f n y) < e)
        ==> ?g. g continuous_on s /\
                ?r. (!m n:num. m < n ==> r m < r n) /\
                    !e. &0 < e
                        ==> ?N. !n x. n >= N /\ x IN s
                                      ==> norm(f(r n) x - g x) < e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GE] THEN
  MATCH_MP_TAC(MESON[]
   `(!k g. V k g ==> N g) /\ (?k. M k /\ ?g. V k g)
    ==> ?g. N g /\ ?k. M k /\ V k g`) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num->num`; `g:real^M->real^N`] THEN
    STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially`
      CONTINUOUS_UNIFORM_LIMIT) THEN
    EXISTS_TAC `(f:num->real^M->real^N) o (k:num->num)` THEN
    ASM_SIMP_TAC[EVENTUALLY_SEQUENTIALLY; o_THM; TRIVIAL_LIMIT_SEQUENTIALLY;
                 RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[continuous_on; dist] THEN
    ASM_MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (f:num->real^M->real^N) (:num)`;
    `s:real^M->bool`]
   COMPACT_UNIFORMLY_EQUICONTINUOUS) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(K ALL_TAC o SPEC `x:real^M`)] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; dist] THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[NORM_SUB]) THEN
  REWRITE_TAC[GSYM dist; UNIFORMLY_CONVERGENT_EQ_CAUCHY] THEN
  X_CHOOSE_THEN `r:real^M->bool` STRIP_ASSUME_TAC
   (ISPEC `s:real^M->bool` SEPARABLE) THEN
  MP_TAC(ISPECL [`f:num->real^M->real^N`; `r:real^M->bool`; `M:real`]
        FUNCTION_CONVERGENT_SUBSEQUENCE) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num->num` THEN
  REWRITE_TAC[CONVERGENT_EQ_CAUCHY; cauchy] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\x:real^M. ball(x,d)) r`) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN ANTS_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure r:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; CLOSURE_APPROACHABLE] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
    ASM_REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; IN_BALL];
    DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC)] THEN
  REMOVE_THEN "*" MP_TAC THEN REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &3 <=> &0 < e`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `M:real^M->num` THEN DISCH_THEN(LABEL_TAC "*") THEN
  MP_TAC(ISPECL [`M:real^M->num`; `t:real^M->bool`]
    UPPER_BOUND_FINITE_SET) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:real^M`] THEN STRIP_TAC THEN
  UNDISCH_TAC `s SUBSET UNIONS (IMAGE (\x:real^M. ball (x,d)) t)` THEN
  REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_REWRITE_TAC[IN_BALL; LEFT_IMP_EXISTS_THM; dist] THEN
  X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(f (k(m:num)) y - f (k m) x) < e / &3 /\
    norm(f (k n) y - f (k n) x) < e / &3 /\
    norm(f (k m) y - f (k n) y) < e / &3
    ==> norm(f (k m) x - f (k n) x :real^M) < e`) THEN
  ASM_SIMP_TAC[] THEN REMOVE_THEN "*" (MP_TAC o SPEC `y:real^M`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
  ASM_REWRITE_TAC[dist; GE] THEN ASM_MESON_TAC[SUBSET; LE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Two forms of the Baire propery of dense sets.                             *)
(* ------------------------------------------------------------------------- *)

let BAIRE = prove
 (`!g s:real^N->bool.
        closed s /\ COUNTABLE g /\
        (!t. t IN g
             ==> open_in (subtopology euclidean s) t /\ s SUBSET closure t)
        ==> s SUBSET closure(INTERS g)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `g:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[INTERS_0; CLOSURE_UNIV; SUBSET_UNIV] THEN
  MP_TAC(ISPEC `g:(real^N->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC))
   [`COUNTABLE(g:(real^N->bool)->bool)`;
    `~(g:(real^N->bool)->bool = {})`] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->real^N->bool` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FORALL_IN_IMAGE; IN_UNIV]) THEN
  REWRITE_TAC[SUBSET; CLOSURE_APPROACHABLE] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  REWRITE_TAC[GSYM IN_BALL; GSYM IN_INTER; MEMBER_NOT_EMPTY] THEN
  SUBGOAL_THEN
   `?t:num->real^N->bool.
        (!n. open_in (subtopology euclidean s) (t n) /\ ~(t n = {}) /\
             s INTER closure(t n) SUBSET g n /\
             closure(t n) SUBSET ball(x,e)) /\
        (!n. t(SUC n) SUBSET t n)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!u n. open_in (subtopology euclidean s) u /\ ~(u = {}) /\
            closure u SUBSET ball(x,e)
            ==> ?y. open_in (subtopology euclidean s) y /\
                    ~(y = {}) /\
                    s INTER closure y SUBSET (g:num->real^N->bool) n /\
                    closure y SUBSET ball(x,e) /\
                    y SUBSET u`
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `n:num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?y:real^N. y IN u /\ y IN g(n:num)` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o SPEC `n:num`) THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
        FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_in]) THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `y:real^N`)) THEN
        ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:real` THEN
        STRIP_TAC THEN REWRITE_TAC[SUBSET; CLOSURE_APPROACHABLE] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `open_in (subtopology euclidean s) (u INTER g(n:num):real^N->bool)`
      MP_TAC THENL [ASM_SIMP_TAC[OPEN_IN_INTER]; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [OPEN_IN_CONTAINS_BALL] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `y:real^N`)) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s INTER ball(y:real^N,d / &2)` THEN
      SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
        ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_HALF; IN_INTER] THEN
        ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `b SUBSET u INTER g ==> !s. s SUBSET b ==> s SUBSET g`)) THEN
        MATCH_MP_TAC(SET_RULE
         `closure(s INTER b) SUBSET closure b /\ closure b SUBSET c
          ==> s INTER closure(s INTER b) SUBSET c INTER s`) THEN
        SIMP_TAC[SUBSET_CLOSURE; INTER_SUBSET] THEN
        ASM_SIMP_TAC[CLOSURE_BALL; SUBSET_BALLS; REAL_HALF; DIST_REFL] THEN
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          SUBSET_TRANS)) THEN MATCH_MP_TAC SUBSET_CLOSURE;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `b INTER s SUBSET u INTER g ==> c SUBSET b
        ==> s INTER c SUBSET u`)) THEN
      REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC DEPENDENT_CHOICE THEN ASM_SIMP_TAC[GSYM CONJ_ASSOC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`s INTER ball(x:real^N,e / &2)`; `0`]) THEN
      ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL; GSYM MEMBER_NOT_EMPTY] THEN
      ANTS_TAC THENL [REWRITE_TAC[LEFT_AND_EXISTS_THM]; MESON_TAC[]] THEN
      EXISTS_TAC `x:real^N` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_HALF; IN_INTER] THEN
      TRANS_TAC SUBSET_TRANS `closure(ball(x:real^N,e / &2))` THEN
      SIMP_TAC[SUBSET_CLOSURE; INTER_SUBSET] THEN
      ASM_SIMP_TAC[CLOSURE_BALL; SUBSET_BALLS; REAL_HALF; DIST_REFL] THEN
      ASM_REAL_ARITH_TAC];
    MP_TAC(ISPEC
     `(\n. s INTER closure(t n)):num->real^N->bool` COMPACT_NEST) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_AND_THM] THEN REPEAT CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC CLOSED_INTER_COMPACT THEN
        ASM_MESON_TAC[BOUNDED_SUBSET; BOUNDED_BALL; COMPACT_EQ_BOUNDED_CLOSED;
                      CLOSED_CLOSURE];
        GEN_TAC THEN MATCH_MP_TAC(SET_RULE
         `~(t = {}) /\ t SUBSET s /\ t SUBSET closure t
          ==> ~(s INTER closure t = {})`) THEN
        ASM_MESON_TAC[CLOSURE_SUBSET; OPEN_IN_IMP_SUBSET];
        MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
        ASM_SIMP_TAC[SUBSET_CLOSURE; SET_RULE
         `t SUBSET u ==> s INTER t SUBSET s INTER u`] THEN
        SET_TAC[]];
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> ~(s = {}) ==> ~(t = {})`) THEN
      REWRITE_TAC[SUBSET_INTER] THEN
      REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      ASM SET_TAC[]]]);;

let BAIRE_ALT = prove
 (`!g s:real^N->bool.
        closed s /\ ~(s = {}) /\ COUNTABLE g /\ UNIONS g = s
        ==> ?t u. t IN g /\ open_in (subtopology euclidean s) u /\
                  u SUBSET (closure t)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
  [`IMAGE (\t:real^N->bool. s DIFF closure t) g`; `s:real^N->bool`] BAIRE) THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC(TAUT `~q /\ (~r ==> p) ==> (p ==> q) ==> r`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `~(s = {}) /\ (t = {} ==> closure t = {}) /\ t = {}
      ==> ~(s SUBSET closure t)`) THEN
    ASM_SIMP_TAC[CLOSURE_EMPTY] THEN
    MATCH_MP_TAC(SET_RULE `i SUBSET s /\ s DIFF i = s ==> i = {}`) THEN
    CONJ_TAC THENL [REWRITE_TAC[INTERS_IMAGE] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DIFF_INTERS] THEN
    REWRITE_TAC[SET_RULE `{f x | x IN IMAGE g s} = {f(g x) | x IN s}`] THEN
    REWRITE_TAC[SET_RULE `s DIFF (s DIFF t) = s INTER t`] THEN
    REWRITE_TAC[SET_RULE `{s INTER closure t | t IN g} =
                          {s INTER t | t IN IMAGE closure g}`] THEN
    SIMP_TAC[GSYM INTER_UNIONS; SET_RULE `s INTER t = s <=> s SUBSET t`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM IMAGE_ID] THEN
    MATCH_MP_TAC UNIONS_MONO_IMAGE THEN REWRITE_TAC[CLOSURE_SUBSET];
    REWRITE_TAC[NOT_EXISTS_THM] THEN STRIP_TAC THEN
    X_GEN_TAC `t:real^N->bool` THEN REPEAT STRIP_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s DIFF (s INTER t)`] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN
      ASM_SIMP_TAC[CLOSED_IN_CLOSED_INTER; CLOSED_CLOSURE; OPEN_IN_REFL];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
       [`t:real^N->bool`; `s INTER ball(x:real^N,e)`]) THEN
      ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL; SUBSET; IN_INTER; IN_BALL;
                   IN_DIFF] THEN
      MESON_TAC[DIST_SYM]]]);;

(* ------------------------------------------------------------------------- *)
(* Several variants of paracompactness.                                      *)
(* ------------------------------------------------------------------------- *)

let PARACOMPACT = prove
 (`!s c. (!t:real^N->bool. t IN c ==> open t) /\ s SUBSET UNIONS c
         ==> ?c'. s SUBSET UNIONS c' /\
                  (!u. u IN c'
                       ==> open u /\ ?t. t IN c /\ u SUBSET t) /\
                  (!x. x IN s
                       ==> ?v. open v /\ x IN v /\
                               FINITE {u | u IN c' /\ ~(u INTER v = {})})`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[EMPTY_SUBSET; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN s
               ==> ?t u. x IN u /\ open u /\ closure u SUBSET t /\ t IN c`
  MP_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [SUBSET]) THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [OPEN_CONTAINS_CBALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(x:real^N,e)` THEN
    ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL; CLOSURE_BALL];
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    MAP_EVERY X_GEN_TAC
      [`f:real^N->real^N->bool`; `e:real^N->real^N->bool`] THEN
    STRIP_TAC] THEN
  MP_TAC(ISPEC `IMAGE (e:real^N->real^N->bool) s` LINDELOF) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REWRITE_TAC[EXISTS_COUNTABLE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC `k:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `k:real^N->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num->real^N` SUBST_ALL_TAC) THEN
  STRIP_TAC THEN EXISTS_TAC
  `{ f(a n:real^N) DIFF UNIONS {closure(e(a m)):real^N->bool | m < n} |
     n IN (:num)}` THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CLOSED_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC; CLOSED_CLOSURE] THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT];
      EXISTS_TAC `f((a:num->real^N) n):real^N->bool` THEN ASM SET_TAC[]];
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_DIFF] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?n. x IN (f((a:num->real^N) n):real^N->bool)` MP_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[UNIONS_IMAGE; EXISTS_IN_IMAGE]) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
      DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(a:num->real^N) n`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]];
      GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
      MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[UNIONS_IMAGE; EXISTS_IN_IMAGE]) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    EXISTS_TAC `e((a:num->real^N) n):real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SET_RULE
     `{u | (?n. u = f n) /\ P u} = IMAGE f {n |n| P(f n) /\ n IN (:num)}`] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{m:num | m <= n}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `m:num` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_LE] THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `u SUBSET t ==> (s DIFF t) INTER u = {}`) THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]]);;

let PARACOMPACT_CLOSED_IN = prove
 (`!u:real^N->bool s c.
        closed_in (subtopology euclidean u) s /\
        (!t:real^N->bool. t IN c ==> open_in (subtopology euclidean u) t) /\
        s SUBSET UNIONS c
         ==> ?c'. s SUBSET UNIONS c' /\
                  (!v. v IN c'
                       ==> open_in (subtopology euclidean u) v /\
                           ?t. t IN c /\ v SUBSET t) /\
                  (!x. x IN u
                       ==> ?v. open_in (subtopology euclidean u) v /\ x IN v /\
                               FINITE {n | n IN c' /\ ~(n INTER v = {})})`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `uu:(real^N->bool)->(real^N->bool)` THEN
  DISCH_THEN(ASSUME_TAC o GSYM) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSED_IN_CLOSED]) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL
   [`u:real^N->bool`;
    `((:real^N) DIFF k) INSERT IMAGE (uu:(real^N->bool)->(real^N->bool)) c`]
   PARACOMPACT) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; UNIONS_IMAGE; UNIONS_INSERT; FORALL_IN_INSERT;
               EXISTS_IN_IMAGE; EXISTS_IN_INSERT; GSYM closed] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{u INTER v:real^N->bool | v IN d /\ ~(v INTER k = {})}` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u INTER v:real^N->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `{y | y IN {f x | P x} /\ Q y} = IMAGE f {x | P x /\ Q(f x)}`] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN SET_TAC[]]);;

let PARACOMPACT_CLOSED = prove
 (`!s:real^N->bool c.
        closed s /\ (!t:real^N->bool. t IN c ==> open t) /\ s SUBSET UNIONS c
        ==> ?c'. s SUBSET UNIONS c' /\
                 (!u. u IN c' ==> open u /\ ?t. t IN c /\ u SUBSET t) /\
                 (!x. ?v. open v /\ x IN v /\
                          FINITE {u | u IN c' /\ ~(u INTER v = {})})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `s:real^N->bool`; `c:(real^N->bool)->bool`]
        PARACOMPACT_CLOSED_IN) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; GSYM CLOSED_IN; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Partitions of unity subordinate to locally finite open coverings.         *)
(* ------------------------------------------------------------------------- *)

let SUBORDINATE_PARTITION_OF_UNITY = prove
 (`!c s. s SUBSET UNIONS c /\ (!u. u IN c ==> open u) /\
         (!x. x IN s
              ==> ?v. open v /\ x IN v /\
                      FINITE {u | u IN c /\ ~(u INTER v = {})})
         ==> ?f:(real^N->bool)->real^N->real.
                      (!u. u IN c
                           ==> (lift o f u) continuous_on s /\
                               !x. x IN s ==> &0 <= f u x) /\
                      (!x u. u IN c /\ x IN s /\ ~(x IN u) ==> f u x = &0) /\
                      (!x. x IN s ==> sum c (\u. f u x) = &1) /\
                      (!x. x IN s
                           ==> ?n. open n /\ x IN n /\
                                   FINITE {u | u IN c /\
                                           ~(!x. x IN n ==> f u x = &0)})`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?u:real^N->bool. u IN c /\ s SUBSET u` THENL
   [FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\v:real^N->bool x:real^N. if v = u then &1 else &0` THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; o_DEF; REAL_POS;
                REAL_OF_NUM_EQ; ARITH_EQ;
                MESON[] `(if p then q else T) <=> p ==> q`] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CONST; COND_ID; SUM_DELTA] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `ball(x:real^N,&1)` THEN
    REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{u:real^N->bool}` THEN
    REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `v:real^N->bool` THEN
    ASM_CASES_TAC `v:real^N->bool = u` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\u:real^N->bool x:real^N.
        if x IN s
        then setdist({x},s DIFF u) / sum c (\v. setdist({x},s DIFF v))
        else &0` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  SIMP_TAC[SUM_POS_LE; SETDIST_POS_LE; REAL_LE_DIV] THEN
  SIMP_TAC[SETDIST_SING_IN_SET; IN_DIFF; real_div; REAL_MUL_LZERO] THEN
  REWRITE_TAC[SUM_RMUL] THEN REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC(TAUT `r /\ p /\ q ==> p /\ q /\ r`) THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:real^N->bool` THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `u:real^N->bool` THEN
    ASM_CASES_TAC `(u:real^N->bool) IN c` THEN
    ASM_REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[real_div; REAL_ENTIRE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(y:real^N) IN u` THEN
    ASM_SIMP_TAC[SETDIST_SING_IN_SET; IN_DIFF; REAL_MUL_LZERO] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v x:real^N. v IN c /\ x IN s /\ x IN v ==> &0 < setdist({x},s DIFF v)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SIMP_TAC[SETDIST_POS_LE; REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `s DIFF v:real^N->bool`; `x:real^N`]
        SETDIST_EQ_0_CLOSED_IN) THEN
    ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
    ASM_SIMP_TAC[CLOSED_IN_CLOSED_INTER; GSYM OPEN_CLOSED] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNION] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN s ==> &0 < sum c (\v. setdist ({x},s DIFF v))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM SUM_SUPPORT] THEN
    REWRITE_TAC[support; NEUTRAL_REAL_ADD] THEN
    MATCH_MP_TAC SUM_POS_LT THEN REWRITE_TAC[SETDIST_POS_LE] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `u:real^N->bool` THEN
      ASM_CASES_TAC `(x:real^N) IN u` THEN
      ASM_SIMP_TAC[SETDIST_SING_IN_SET; IN_DIFF] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN REWRITE_TAC[IN_UNIONS] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      ASM_MESON_TAC[REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_DIV_REFL; o_DEF] THEN
  X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x:real^N.
        lift(setdist({x},s DIFF u) / sum c (\v. setdist({x},s DIFF v)))` THEN
  SIMP_TAC[] THEN REWRITE_TAC[real_div; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  SIMP_TAC[CONTINUOUS_ON_LIFT_SETDIST; o_DEF] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ; CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `x:real^N` th) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN_OPEN_IN THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^N. lift(sum {v | v IN c /\ ~(v INTER n = {})}
                         (\v. setdist({x},s DIFF v)))`;
    `s INTER n:real^N->bool`] THEN
  ASM_SIMP_TAC[IN_INTER; OPEN_IN_OPEN_INTER] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_EQ_SUPERSET THEN
    ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN X_GEN_TAC `v:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC SETDIST_SING_IN_SET THEN ASM SET_TAC[];
    ASM_SIMP_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_VSUM THEN
    ASM_SIMP_TAC[CONTINUOUS_AT_LIFT_SETDIST; CONTINUOUS_AT_WITHIN]]);;


print_endline "topology.ml loaded"
