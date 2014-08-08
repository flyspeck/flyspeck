open Hol_core
open Card
open Products
open Permutations
open Floor
open Vectors
open Determinants
include Topology2


(* ------------------------------------------------------------------------- *)
(* More properties of open and closed maps.                                  *)
(* ------------------------------------------------------------------------- *)

let OPEN_MAP_RESTRICT = prove
 (`!f:real^M->real^N s t t'.
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean t) (IMAGE f u)) /\
        t' SUBSET t
        ==> !u. open_in (subtopology euclidean {x | x IN s /\ f x IN t'}) u
                ==> open_in (subtopology euclidean t') (IMAGE f u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `c:real^M->bool` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

let CLOSED_MAP_RESTRICT = prove
 (`!f:real^M->real^N s t t'.
        (!u. closed_in (subtopology euclidean s) u
             ==> closed_in (subtopology euclidean t) (IMAGE f u)) /\
        t' SUBSET t
        ==> !u. closed_in (subtopology euclidean {x | x IN s /\ f x IN t'}) u
                ==> closed_in (subtopology euclidean t') (IMAGE f u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `c:real^M->bool` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

let QUOTIENT_MAP_OPEN_MAP_EQ = prove
 (`!f:real^M->real^N s t.
       IMAGE f s SUBSET t /\
       (!u. u SUBSET t
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                 open_in (subtopology euclidean t) u))
       ==> ((!k. open_in (subtopology euclidean s) k
                 ==> open_in (subtopology euclidean t) (IMAGE f k)) <=>
            (!k. open_in (subtopology euclidean s) k
                 ==> open_in (subtopology euclidean s)
                               {x | x IN s /\ f x IN IMAGE f k}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (f:real^M->real^N) k`) THEN
  ASM_SIMP_TAC[IMAGE_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]);;

let QUOTIENT_MAP_CLOSED_MAP_EQ = prove
 (`!f:real^M->real^N s t.
       IMAGE f s SUBSET t /\
       (!u. u SUBSET t
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                 open_in (subtopology euclidean t) u))
       ==> ((!k. closed_in (subtopology euclidean s) k
                 ==> closed_in (subtopology euclidean t) (IMAGE f k)) <=>
            (!k. closed_in (subtopology euclidean s) k
                 ==> closed_in (subtopology euclidean s)
                               {x | x IN s /\ f x IN IMAGE f k}))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[QUOTIENT_MAP_OPEN_CLOSED] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (f:real^M->real^N) k`) THEN
  ASM_SIMP_TAC[IMAGE_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]);;

let CLOSED_MAP_IMP_OPEN_MAP = prove
 (`!f:real^M->real^N s t.
        IMAGE f s = t /\
        (!u. closed_in (subtopology euclidean s) u
                ==> closed_in (subtopology euclidean t) (IMAGE f u)) /\
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean s)
                         {x | x IN s /\ f x IN IMAGE f u})
        ==> (!u. open_in (subtopology euclidean s) u
                 ==> open_in (subtopology euclidean t) (IMAGE f u))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `IMAGE (f:real^M->real^N) u =
     t DIFF IMAGE f (s DIFF {x | x IN s /\ f x IN IMAGE f u})`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN ASM SET_TAC[];
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    ASM_SIMP_TAC[CLOSED_IN_REFL]]);;

let OPEN_MAP_IMP_CLOSED_MAP = prove
 (`!f:real^M->real^N s t.
        IMAGE f s = t /\
        (!u. open_in (subtopology euclidean s) u
                ==> open_in (subtopology euclidean t) (IMAGE f u)) /\
        (!u. closed_in (subtopology euclidean s) u
             ==> closed_in (subtopology euclidean s)
                         {x | x IN s /\ f x IN IMAGE f u})
        ==> (!u. closed_in (subtopology euclidean s) u
                 ==> closed_in (subtopology euclidean t) (IMAGE f u))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `IMAGE (f:real^M->real^N) u =
     t DIFF IMAGE f (s DIFF {x | x IN s /\ f x IN IMAGE f u})`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN ASM SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
    ASM_SIMP_TAC[OPEN_IN_REFL]]);;

let OPEN_MAP_FROM_COMPOSITION_SURJECTIVE = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s = t /\ IMAGE g t SUBSET u /\
        (!k. open_in (subtopology euclidean s) k
             ==> open_in (subtopology euclidean u) (IMAGE (g o f) k))
        ==> (!k. open_in (subtopology euclidean t) k
                 ==> open_in (subtopology euclidean u) (IMAGE g k))`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `IMAGE g k = IMAGE ((g:real^N->real^P) o (f:real^M->real^N))
                      {x | x IN s /\ f(x) IN k}`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

let CLOSED_MAP_FROM_COMPOSITION_SURJECTIVE = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s = t /\ IMAGE g t SUBSET u /\
        (!k. closed_in (subtopology euclidean s) k
             ==> closed_in (subtopology euclidean u) (IMAGE (g o f) k))
        ==> (!k. closed_in (subtopology euclidean t) k
                 ==> closed_in (subtopology euclidean u) (IMAGE g k))`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `IMAGE g k = IMAGE ((g:real^N->real^P) o (f:real^M->real^N))
                      {x | x IN s /\ f(x) IN k}`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

let OPEN_MAP_FROM_COMPOSITION_INJECTIVE = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        IMAGE f s SUBSET t /\ IMAGE g t SUBSET u /\
        g continuous_on t /\ (!x y. x IN t /\ y IN t /\ g x = g y ==> x = y) /\
        (!k. open_in (subtopology euclidean s) k
             ==> open_in (subtopology euclidean u) (IMAGE (g o f) k))
        ==> (!k. open_in (subtopology euclidean s) k
                 ==> open_in (subtopology euclidean t) (IMAGE f k))`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `IMAGE f k = {x | x IN t /\
                    g(x) IN IMAGE ((g:real^N->real^P) o (f:real^M->real^N)) k}`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `u:real^P->bool` THEN ASM_SIMP_TAC[]]);;

let CLOSED_MAP_FROM_COMPOSITION_INJECTIVE = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        IMAGE f s SUBSET t /\ IMAGE g t SUBSET u /\
        g continuous_on t /\ (!x y. x IN t /\ y IN t /\ g x = g y ==> x = y) /\
        (!k. closed_in (subtopology euclidean s) k
             ==> closed_in (subtopology euclidean u) (IMAGE (g o f) k))
        ==> (!k. closed_in (subtopology euclidean s) k
                 ==> closed_in (subtopology euclidean t) (IMAGE f k))`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `IMAGE f k = {x | x IN t /\
                    g(x) IN IMAGE ((g:real^N->real^P) o (f:real^M->real^N)) k}`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `u:real^P->bool` THEN ASM_SIMP_TAC[]]);;

let OPEN_MAP_CLOSED_SUPERSET_PREIMAGE = prove
 (`!f:real^M->real^N s t u w.
        (!k. open_in (subtopology euclidean s) k
             ==> open_in (subtopology euclidean t) (IMAGE f k)) /\
        closed_in (subtopology euclidean s) u /\
        w SUBSET t /\ {x | x IN s /\ f(x) IN w} SUBSET u
        ==> ?v. closed_in (subtopology euclidean t) v /\
                w SUBSET v /\
                {x | x IN s /\ f(x) IN v} SUBSET u`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `t DIFF IMAGE (f:real^M->real^N) (s DIFF u)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL]);;

let OPEN_MAP_CLOSED_SUPERSET_PREIMAGE_EQ = prove
 (`!f:real^M->real^N s t.
       IMAGE f s SUBSET t
       ==> ((!k. open_in (subtopology euclidean s) k
                 ==> open_in (subtopology euclidean t) (IMAGE f k)) <=>
            (!u w. closed_in (subtopology euclidean s) u /\
                   w SUBSET t /\ {x | x IN s /\ f(x) IN w} SUBSET u
                   ==> ?v. closed_in (subtopology euclidean t) v /\
                           w SUBSET v /\ {x | x IN s /\ f(x) IN v} SUBSET u))`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  ASM_SIMP_TAC[OPEN_MAP_CLOSED_SUPERSET_PREIMAGE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`s DIFF k:real^M->bool`; `t DIFF IMAGE (f:real^M->real^N) k`]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) k = t DIFF v` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL]]);;

let CLOSED_MAP_OPEN_SUPERSET_PREIMAGE = prove
 (`!f:real^M->real^N s t u w.
        (!k. closed_in (subtopology euclidean s) k
             ==> closed_in (subtopology euclidean t) (IMAGE f k)) /\
        open_in (subtopology euclidean s) u /\
        w SUBSET t /\ {x | x IN s /\ f(x) IN w} SUBSET u
        ==> ?v. open_in (subtopology euclidean t) v /\
                w SUBSET v /\
                {x | x IN s /\ f(x) IN v} SUBSET u`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `t DIFF IMAGE (f:real^M->real^N) (s DIFF u)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL]);;

let CLOSED_MAP_OPEN_SUPERSET_PREIMAGE_EQ = prove
 (`!f:real^M->real^N s t.
       IMAGE f s SUBSET t
       ==> ((!k. closed_in (subtopology euclidean s) k
                 ==> closed_in (subtopology euclidean t) (IMAGE f k)) <=>
            (!u w. open_in (subtopology euclidean s) u /\
                   w SUBSET t /\ {x | x IN s /\ f(x) IN w} SUBSET u
                   ==> ?v. open_in (subtopology euclidean t) v /\
                           w SUBSET v /\ {x | x IN s /\ f(x) IN v} SUBSET u))`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  ASM_SIMP_TAC[CLOSED_MAP_OPEN_SUPERSET_PREIMAGE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`s DIFF k:real^M->bool`; `t DIFF IMAGE (f:real^M->real^N) k`]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) k = t DIFF v` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL]]);;

let CLOSED_MAP_OPEN_SUPERSET_PREIMAGE_POINT = prove
 (`!f:real^M->real^N s t.
       IMAGE f s SUBSET t
       ==> ((!k. closed_in (subtopology euclidean s) k
                 ==> closed_in (subtopology euclidean t) (IMAGE f k)) <=>
            (!u y. open_in (subtopology euclidean s) u /\
                   y IN t /\ {x | x IN s /\ f(x) = y} SUBSET u
                   ==> ?v. open_in (subtopology euclidean t) v /\
                           y IN v /\ {x | x IN s /\ f(x) IN v} SUBSET u))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CLOSED_MAP_OPEN_SUPERSET_PREIMAGE_EQ] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `y:real^N`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL  [`u:real^M->bool`; `{y:real^N}`]) THEN
    ASM_REWRITE_TAC[SING_SUBSET; IN_SING];
    MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `w:real^N->bool`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M->bool`) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `vv:real^N->real^N->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `UNIONS {(vv:real^N->real^N->bool) y | y IN w}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      ASM SET_TAC[];
      REWRITE_TAC[UNIONS_GSPEC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; RIGHT_AND_EXISTS_THM;
                  LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM SET_TAC[]]]);;

let CONNECTED_OPEN_MONOTONE_PREIMAGE = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!c. open_in (subtopology euclidean s) c
             ==> open_in (subtopology euclidean t) (IMAGE f c)) /\
        (!y. y IN t ==> connected {x | x IN s /\ f x = y})
        ==> !c. connected c /\ c SUBSET t
                ==> connected {x | x IN s /\ f x IN c}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `c:real^N->bool` o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] OPEN_MAP_RESTRICT)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC(ISPECL
   [`f:real^M->real^N`; `{x | x IN s /\ (f:real^M->real^N) x IN c}`]
   OPEN_MAP_IMP_QUOTIENT_MAP) THEN
  SUBGOAL_THEN `IMAGE f {x | x IN s /\ (f:real^M->real^N) x IN c} = c`
  ASSUME_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN SET_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC CONNECTED_MONOTONE_QUOTIENT_PREIMAGE THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `c:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN SET_TAC[];
    SIMP_TAC[SET_RULE
     `y IN c ==> {x | x IN {x | x IN s /\ f x IN c} /\ f x = y} =
                 {x | x IN s /\ f x = y}`] THEN
   ASM SET_TAC[]]);;

let CONNECTED_CLOSED_MONOTONE_PREIMAGE = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!c. closed_in (subtopology euclidean s) c
             ==> closed_in (subtopology euclidean t) (IMAGE f c)) /\
        (!y. y IN t ==> connected {x | x IN s /\ f x = y})
        ==> !c. connected c /\ c SUBSET t
                ==> connected {x | x IN s /\ f x IN c}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `c:real^N->bool` o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] CLOSED_MAP_RESTRICT)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC(ISPECL
   [`f:real^M->real^N`; `{x | x IN s /\ (f:real^M->real^N) x IN c}`]
   CLOSED_MAP_IMP_QUOTIENT_MAP) THEN
  SUBGOAL_THEN `IMAGE f {x | x IN s /\ (f:real^M->real^N) x IN c} = c`
  ASSUME_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN SET_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC CONNECTED_MONOTONE_QUOTIENT_PREIMAGE THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `c:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN SET_TAC[];
    SIMP_TAC[SET_RULE
     `y IN c ==> {x | x IN {x | x IN s /\ f x IN c} /\ f x = y} =
                 {x | x IN s /\ f x = y}`] THEN
   ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Proper maps, including projections out of compact sets.                   *)
(* ------------------------------------------------------------------------- *)

let PROPER_MAP = prove
 (`!f:real^M->real^N s t.
    IMAGE f s SUBSET t
    ==> ((!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) <=>
         (!k. closed_in (subtopology euclidean s) k
              ==> closed_in (subtopology euclidean t) (IMAGE f k)) /\
         (!a. a IN t ==> compact {x | x IN s /\ f x = a}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[SET_RULE `x = a <=> x IN {a}`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SING_SUBSET; COMPACT_SING]] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
    REWRITE_TAC[CLOSED_IN_LIMPT] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `y:real^N`] THEN
    REWRITE_TAC[LIMPT_SEQUENTIAL_INJ; IN_DELETE] THEN
    REWRITE_TAC[IN_IMAGE; LEFT_AND_EXISTS_THM; SKOLEM_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; FORALL_AND_THM] THEN
    ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
    REWRITE_TAC[UNWIND_THM2; FUN_EQ_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num->real^M` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `~(INTERS {{a | a IN k /\
                     (f:real^M->real^N) a IN
                     (y INSERT IMAGE (\i. f(x(n + i))) (:num))} |
                n IN (:num)} = {})`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_FIP THEN CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN X_GEN_TAC `n:num` THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSED_IN_CLOSED]) THEN
        DISCH_THEN(X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[SET_RULE
         `{x | x IN s INTER k /\ P x} = k INTER {x | x IN s /\ P x}`] THEN
        MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC COMPACT_SEQUENCE_WITH_LIMIT THEN
        FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP SEQ_OFFSET) THEN
        REWRITE_TAC[ADD_SYM];
        REWRITE_TAC[SIMPLE_IMAGE; FORALL_FINITE_SUBSET_IMAGE] THEN
        X_GEN_TAC `i:num->bool` THEN STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o ISPEC `\n:num. n` o MATCH_MP
          UPPER_BOUND_FINITE_SET) THEN
        REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; INTERS_IMAGE; IN_ELIM_THM] THEN
        EXISTS_TAC `(x:num->real^M) m` THEN
        X_GEN_TAC `p:num` THEN DISCH_TAC THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_INSERT; IN_IMAGE; IN_UNIV] THEN DISJ2_TAC THEN
        EXISTS_TAC `m - p:num` THEN
        ASM_MESON_TAC[ARITH_RULE `p <= m ==> p + m - p:num = m`]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `x:real^M` THEN
      REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      DISCH_THEN(fun th -> LABEL_TAC "*" th THEN MP_TAC(SPEC `0` th)) THEN
      REWRITE_TAC[ADD_CLAUSES; IN_INSERT; IN_IMAGE; IN_UNIV] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN MP_TAC)) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `i + 1`) THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT; IN_IMAGE; IN_UNIV] THEN ARITH_TAC];
    STRIP_TAC THEN X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN
    X_GEN_TAC `c:(real^M->bool)->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!a. a IN k
          ==> ?g. g SUBSET c /\ FINITE g /\
                  {x | x IN s /\ (f:real^M->real^N) x = a} SUBSET UNIONS g`
    MP_TAC THENL
     [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN UNDISCH_THEN
       `!a. a IN t ==> compact {x | x IN s /\ (f:real^M->real^N) x = a}`
       (MP_TAC o SPEC `a:real^N`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[COMPACT_EQ_HEINE_BOREL]] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `uu:real^N->(real^M->bool)->bool` THEN
      DISCH_THEN(LABEL_TAC "*")] THEN
    SUBGOAL_THEN
     `!a. a IN k
          ==> ?v. open v /\ a IN v /\
                 {x | x IN s /\ (f:real^M->real^N) x IN v} SUBSET UNIONS(uu a)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      UNDISCH_THEN
       `!k. closed_in (subtopology euclidean s) k
            ==> closed_in (subtopology euclidean t)
                          (IMAGE (f:real^M->real^N) k)`
       (MP_TAC o SPEC `(s:real^M->bool) DIFF UNIONS(uu(a:real^N))`) THEN
      SIMP_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[SET_RULE `s DIFF (s DIFF t) = s INTER t`] THEN
        MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
        MATCH_MP_TAC OPEN_UNIONS THEN ASM SET_TAC[];
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC[OPEN_IN_OPEN] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC `v:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N`)) THEN
        ASM_REWRITE_TAC[] THEN REPEAT
         ((ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC]) ORELSE STRIP_TAC)
        THENL [ALL_TAC; ASM SET_TAC[]] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
        DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM SET_TAC[]];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `vv:real^N->(real^N->bool)` THEN
      DISCH_THEN(LABEL_TAC "+")] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (vv:real^N->(real^N->bool)) k`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r ==> s <=> q /\ p ==> r ==> s`] THEN
    REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
    X_GEN_TAC `j:real^N->bool` THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `UNIONS(IMAGE (uu:real^N->(real^M->bool)->bool) j)` THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM_SIMP_TAC[FINITE_UNIONS; FORALL_IN_IMAGE; FINITE_IMAGE] THEN
      ASM SET_TAC[];
      REWRITE_TAC[UNIONS_IMAGE; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      ASM SET_TAC[]]]);;

let COMPACT_CONTINUOUS_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> (f continuous_on s <=>
             !t. compact t /\ t SUBSET s ==> compact(IMAGE f t))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MESON_TAC[COMPACT_CONTINUOUS_IMAGE; CONTINUOUS_ON_SUBSET]; DISCH_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `g:real^N->real^M` o
    GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
  REWRITE_TAC[CONTINUOUS_ON_CLOSED] THEN
  X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^M`; `IMAGE (f:real^M->real^N) s`;
                 `s:real^M->bool`] PROPER_MAP) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(q ==> s) /\ p ==> (p <=> q /\ r) ==> s`) THEN
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN
     `{x | x IN s /\ (f:real^M->real^N) x IN u} = IMAGE g u`
     (fun th -> ASM_MESON_TAC[th]);
    SUBGOAL_THEN
     `{x | x IN IMAGE f s /\ (g:real^N->real^M) x IN k} = IMAGE f k`
     (fun th -> ASM_SIMP_TAC[th])] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN ASM SET_TAC[]);;

let PROPER_MAP_FROM_COMPACT = prove
 (`!f:real^M->real^N s k.
        f continuous_on s /\ IMAGE f s SUBSET t /\ compact s /\
        closed_in (subtopology euclidean t) k
        ==> compact {x | x IN s /\ f x IN k}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC `s:real^M->bool` THEN
  ASM_MESON_TAC[CONTINUOUS_CLOSED_IN_PREIMAGE_GEN]);;

let PROPER_MAP_COMPOSE = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        IMAGE f s SUBSET t /\
        (!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) /\
        (!k. k SUBSET u /\ compact k ==> compact {x | x IN t /\ g x IN k})
        ==> !k. k SUBSET u /\ compact k
                ==> compact {x | x IN s /\ (g o f) x IN k}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^P->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{x | x IN t /\ (g:real^N->real^P) x IN k}`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC EQ_IMP] THEN
  AP_TERM_TAC THEN ASM SET_TAC[]);;

let PROPER_MAP_FROM_COMPOSITION_LEFT = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s = t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        (!k. k SUBSET u /\ compact k
             ==> compact {x | x IN s /\ (g o f) x IN k})
        ==> !k. k SUBSET u /\ compact k ==> compact {x | x IN t /\ g x IN k}`,
  REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^P->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o ISPEC `f:real^M->real^N` o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] COMPACT_CONTINUOUS_IMAGE)) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN SET_TAC[];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]]);;

let PROPER_MAP_FROM_COMPOSITION_RIGHT = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        (!k. k SUBSET u /\ compact k
             ==> compact {x | x IN s /\ (g o f) x IN k})
        ==> !k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}`,
  let lemma = prove
   (`!s t. closed_in (subtopology euclidean s) t ==> compact s ==> compact t`,
    MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_SUBSET;
              CLOSED_IN_CLOSED_EQ]) in
  REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (g:real^N->real^P) k`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC lemma THEN
    MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
    EXISTS_TAC `s:real^M->bool` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]);;

let PROPER_MAP_FSTCART = prove
 (`!s:real^M->bool t:real^N->bool k.
        compact t /\ k SUBSET s /\ compact k
        ==> compact {z | z IN s PCROSS t /\ fstcart z IN k}`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `{z | z IN s PCROSS t /\ fstcart z IN k} =
    (k:real^M->bool) PCROSS (t:real^N->bool)`
   (fun th -> ASM_SIMP_TAC[th; COMPACT_PCROSS]) THEN
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_THM;
              PASTECART_IN_PCROSS; FSTCART_PASTECART] THEN
  ASM SET_TAC[]);;

let CLOSED_MAP_FSTCART = prove
 (`!s:real^M->bool t:real^N->bool c.
        compact t /\ closed_in (subtopology euclidean (s PCROSS t)) c
        ==> closed_in (subtopology euclidean s) (IMAGE fstcart c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
                 `(s:real^M->bool) PCROSS (t:real^N->bool)`;
                 `s:real^M->bool`]
        PROPER_MAP) THEN
  ASM_SIMP_TAC[PROPER_MAP_FSTCART; IMAGE_FSTCART_PCROSS] THEN
  ASM SET_TAC[]);;

let PROPER_MAP_SNDCART = prove
 (`!s:real^M->bool t:real^N->bool k.
        compact s /\ k SUBSET t /\ compact k
        ==> compact {z | z IN s PCROSS t /\ sndcart z IN k}`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `{z | z IN s PCROSS t /\ sndcart z IN k} =
    (s:real^M->bool) PCROSS (k:real^N->bool)`
   (fun th -> ASM_SIMP_TAC[th; COMPACT_PCROSS]) THEN
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_THM;
              PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let CLOSED_MAP_SNDCART = prove
 (`!s:real^M->bool t:real^N->bool c.
        compact s /\ closed_in (subtopology euclidean (s PCROSS t)) c
        ==> closed_in (subtopology euclidean t) (IMAGE sndcart c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
                 `(s:real^M->bool) PCROSS (t:real^N->bool)`;
                 `t:real^N->bool`]
        PROPER_MAP) THEN
  ASM_SIMP_TAC[PROPER_MAP_SNDCART; IMAGE_SNDCART_PCROSS] THEN
  ASM SET_TAC[]);;

let CLOSED_IN_COMPACT_PROJECTION = prove
 (`!s:real^M->bool t:real^N->bool u.
    compact s /\ closed_in (subtopology euclidean (s PCROSS t)) u
    ==> closed_in (subtopology euclidean t)
                  {y | ?x. x IN s /\ pastecart x y IN u}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_MAP_SNDCART) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET o CONJUNCT2) THEN
  REWRITE_TAC[EXTENSION; SUBSET; IN_IMAGE; FORALL_PASTECART; EXISTS_PASTECART;
              PASTECART_IN_PCROSS; IN_ELIM_THM; SNDCART_PASTECART] THEN
  SET_TAC[]);;

let CLOSED_COMPACT_PROJECTION = prove
 (`!s:real^M->bool t:real^(M,N)finite_sum->bool.
      compact s /\ closed t ==> closed {y | ?x. x IN s /\ pastecart x y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{y | ?x:real^M. x IN s /\ pastecart x y IN t} =
    {y | ?x. x IN s /\ pastecart x y IN ((s PCROSS (:real^N)) INTER t)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTER] THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
    EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[CLOSED_UNIV] THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT_PROJECTION THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_SUBSET THEN
    ASM_SIMP_TAC[CLOSED_INTER; CLOSED_UNIV; CLOSED_PCROSS; COMPACT_IMP_CLOSED;
                 INTER_SUBSET]]);;

let TUBE_LEMMA = prove
 (`!s:real^M->bool t:real^N->bool u a.
        compact s /\ ~(s = {}) /\ {pastecart x a | x IN s} SUBSET u /\
        open_in(subtopology euclidean (s PCROSS t)) u
        ==> ?v. open_in (subtopology euclidean t) v /\ a IN v /\
                (s PCROSS v) SUBSET u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS] THEN
  REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT; PCROSS]
        CLOSED_IN_COMPACT_PROJECTION)) THEN
  ASM_REWRITE_TAC[IN_ELIM_PASTECART_THM; IN_DIFF] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN MATCH_MP_TAC(MESON[]
   `(closed_in top t ==> s DIFF (s DIFF t) = t) /\
    s DIFF t SUBSET s /\ P(s DIFF t)
    ==> closed_in top t
        ==> ?v. v SUBSET s /\ closed_in top (s DIFF v) /\ P v`) THEN
  REWRITE_TAC[SET_RULE `s DIFF (s DIFF t) = t <=> t SUBSET s`] THEN
  REWRITE_TAC[SUBSET_DIFF] THEN
  SIMP_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET])) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_SING; FORALL_PASTECART] THEN
  REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN ASM_MESON_TAC[MEMBER_NOT_EMPTY]);;

let TUBE_LEMMA_GEN = prove
 (`!s t t' u:real^(M,N)finite_sum->bool.
        compact s /\ ~(s = {}) /\ t SUBSET t' /\
        s PCROSS t SUBSET u /\
        open_in (subtopology euclidean (s PCROSS t')) u
        ==> ?v. open_in (subtopology euclidean t') v /\
                t SUBSET v /\
                s PCROSS v SUBSET u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a. a IN t ==> ?v. open_in (subtopology euclidean t') v /\ a IN v /\
                       (s:real^M->bool) PCROSS (v:real^N->bool) SUBSET u`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TUBE_LEMMA THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `vv:real^N->real^N->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `UNIONS (IMAGE (vv:real^N->real^N->bool) t)` THEN
    ASM_SIMP_TAC[OPEN_IN_UNIONS; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM; FORALL_IN_PCROSS] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `c:real^N`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N`) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_PCROSS] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Pasting functions together on open sets.                                  *)
(* ------------------------------------------------------------------------- *)

let PASTING_LEMMA = prove
 (`!f:A->real^M->real^N g t s k.
        (!i. i IN k
             ==> open_in (subtopology euclidean s) (t i) /\
                 (f i) continuous_on (t i)) /\
        (!i j x. i IN k /\ j IN k /\ x IN s INTER t i INTER t j
                 ==> f i x = f j x) /\
        (!x. x IN s ==> ?j. j IN k /\ x IN t j /\ g x = f j x)
        ==> g continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_OPEN_IN_PREIMAGE_EQ] THEN
  STRIP_TAC THEN X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{x | x IN s /\ g x IN u} =
    UNIONS {{x | x IN (t i) /\ ((f:A->real^M->real^N) i x) IN u} |
            i IN k}`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `!i. i IN k ==> ((t:A->real^M->bool) i) SUBSET s`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
      REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[]];
    MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    ASM_MESON_TAC[OPEN_IN_TRANS]]);;

let PASTING_LEMMA_EXISTS = prove
 (`!f:A->real^M->real^N t s k.
        s SUBSET UNIONS {t i | i IN k} /\
        (!i. i IN k
             ==> open_in (subtopology euclidean s) (t i) /\
                 (f i) continuous_on (t i)) /\
        (!i j x. i IN k /\ j IN k /\ x IN s INTER t i INTER t j
                 ==> f i x = f j x)
        ==> ?g. g continuous_on s /\
                (!x i. i IN k /\ x IN s INTER t i ==> g x = f i x)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x. (f:A->real^M->real^N)(@i. i IN k /\ x IN t i) x` THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN MATCH_MP_TAC PASTING_LEMMA THEN
  MAP_EVERY EXISTS_TAC
   [`f:A->real^M->real^N`; `t:A->real^M->bool`; `k:A->bool`] THEN
  ASM SET_TAC[]);;

let CONTINUOUS_ON_UNION_LOCAL_OPEN = prove
 (`!f:real^M->real^N s.
        open_in (subtopology euclidean (s UNION t)) s /\
        open_in (subtopology euclidean (s UNION t)) t /\
        f continuous_on s /\ f continuous_on t
        ==> f continuous_on (s UNION t)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\i:(real^M->bool). (f:real^M->real^N)`; `f:real^M->real^N`;
    `\i:(real^M->bool). i`; `s UNION t:real^M->bool`; `{s:real^M->bool,t}`]
   PASTING_LEMMA) THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_UNION]);;

let CONTINUOUS_ON_UNION_OPEN = prove
 (`!f s t. open s /\ open t /\ f continuous_on s /\ f continuous_on t
           ==> f continuous_on (s UNION t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN
  ASM_SIMP_TAC[OPEN_UNION] THEN SET_TAC[]);;

let CONTINUOUS_ON_CASES_LOCAL_OPEN = prove
 (`!P f g:real^M->real^N s t.
        open_in (subtopology euclidean (s UNION t)) s /\
        open_in (subtopology euclidean (s UNION t)) t /\
        f continuous_on s /\ g continuous_on t /\
        (!x. x IN s /\ ~P x \/ x IN t /\ P x ==> f x = g x)
        ==> (\x. if P x then f x else g x) continuous_on (s UNION t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
   [EXISTS_TAC `f:real^M->real^N`; EXISTS_TAC `g:real^M->real^N`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CONTINUOUS_ON_CASES_OPEN = prove
 (`!P f g s t.
           open s /\
           open t /\
           f continuous_on s /\
           g continuous_on t /\
           (!x. x IN s /\ ~P x \/ x IN t /\ P x ==> f x = g x)
           ==> (\x. if P x then f x else g x) continuous_on s UNION t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN
  ASM_SIMP_TAC[OPEN_UNION] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Likewise on closed sets, with a finiteness assumption.                    *)
(* ------------------------------------------------------------------------- *)

let PASTING_LEMMA_CLOSED = prove
 (`!f:A->real^M->real^N g t s k.
        FINITE k /\
        (!i. i IN k
             ==> closed_in (subtopology euclidean s) (t i) /\
                 (f i) continuous_on (t i)) /\
        (!i j x. i IN k /\ j IN k /\ x IN s INTER t i INTER t j
                 ==> f i x = f j x) /\
        (!x. x IN s ==> ?j. j IN k /\ x IN t j /\ g x = f j x)
        ==> g continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_CLOSED_IN_PREIMAGE_EQ] THEN
  STRIP_TAC THEN X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{x | x IN s /\ g x IN u} =
    UNIONS {{x | x IN (t i) /\ ((f:A->real^M->real^N) i x) IN u} |
            i IN k}`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `!i. i IN k ==> ((t:A->real^M->bool) i) SUBSET s`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[CLOSED_IN_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
      REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[]];
    MATCH_MP_TAC CLOSED_IN_UNIONS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[CLOSED_IN_TRANS]]);;

let PASTING_LEMMA_EXISTS_CLOSED = prove
 (`!f:A->real^M->real^N t s k.
        FINITE k /\
        s SUBSET UNIONS {t i | i IN k} /\
        (!i. i IN k
             ==> closed_in (subtopology euclidean s) (t i) /\
                 (f i) continuous_on (t i)) /\
        (!i j x. i IN k /\ j IN k /\ x IN s INTER t i INTER t j
                 ==> f i x = f j x)
        ==> ?g. g continuous_on s /\
                (!x i. i IN k /\ x IN s INTER t i ==> g x = f i x)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x. (f:A->real^M->real^N)(@i. i IN k /\ x IN t i) x` THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC PASTING_LEMMA_CLOSED THEN
  MAP_EVERY EXISTS_TAC
   [`f:A->real^M->real^N`; `t:A->real^M->bool`; `k:A->bool`] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Closure of halflines, halfspaces and hyperplanes.                         *)
(* ------------------------------------------------------------------------- *)

let LIM_LIFT_DOT = prove
 (`!f:real^M->real^N a.
        (f --> l) net ==> ((lift o (\y. a dot f(y))) --> lift(a dot l)) net`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = vec 0:real^N` THENL
   [ASM_REWRITE_TAC[DOT_LZERO; LIFT_NUM; o_DEF; LIM_CONST]; ALL_TAC] THEN
  REWRITE_TAC[LIM] THEN MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / norm(a:real^N)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; REAL_LT_RDIV_EQ] THEN
  REWRITE_TAC[dist; o_THM; GSYM LIFT_SUB; GSYM DOT_RSUB; NORM_LIFT] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN
  MESON_TAC[NORM_CAUCHY_SCHWARZ_ABS; REAL_MUL_SYM; REAL_LET_TRANS]);;

let CONTINUOUS_AT_LIFT_DOT = prove
 (`!a:real^N x. (lift o (\y. a dot y)) continuous at x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_AT; o_THM] THEN
  MATCH_MP_TAC LIM_LIFT_DOT THEN REWRITE_TAC[LIM_AT] THEN MESON_TAC[]);;

let CONTINUOUS_ON_LIFT_DOT = prove
 (`!s. (lift o (\y. a dot y)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_LIFT_DOT]);;

let CLOSED_INTERVAL_LEFT = prove
 (`!b:real^N.
     closed {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> x$i <= b$i}`,
  REWRITE_TAC[CLOSED_LIMPT; LIMPT_APPROACHABLE; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x:real^N)$i - (b:real^N)$i`) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[dist; REAL_NOT_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((z - x :real^N)$i)` THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_ARITH `z <= b /\ b < x ==> x - b <= abs(z - x)`]);;

let CLOSED_INTERVAL_RIGHT = prove
 (`!a:real^N.
     closed {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= x$i}`,
  REWRITE_TAC[CLOSED_LIMPT; LIMPT_APPROACHABLE; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a:real^N)$i - (x:real^N)$i`) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[dist; REAL_NOT_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((z - x :real^N)$i)` THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_ARITH `x < a /\ a <= z ==> a - x <= abs(z - x)`]);;

let CLOSED_HALFSPACE_LE = prove
 (`!a:real^N b. closed {x | a dot x <= b}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(:real^N)` CONTINUOUS_ON_LIFT_DOT) THEN
  REWRITE_TAC[CONTINUOUS_ON_CLOSED; GSYM CLOSED_IN; SUBTOPOLOGY_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE lift {r | ?x:real^N. (a dot x = r) /\ r <= b}`) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
    REWRITE_TAC[o_DEF] THEN MESON_TAC[LIFT_DROP]] THEN
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  EXISTS_TAC `{x | !i. 1 <= i /\ i <= dimindex(:1)
                       ==> (x:real^1)$i <= (lift b)$i}` THEN
  REWRITE_TAC[CLOSED_INTERVAL_LEFT] THEN
  SIMP_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM; IN_INTER;
    VEC_COMPONENT; DIMINDEX_1; LAMBDA_BETA; o_THM] THEN
  SIMP_TAC[ARITH_RULE `1 <= i /\ i <= 1 <=> (i = 1)`] THEN
  REWRITE_TAC[GSYM drop; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  MESON_TAC[LIFT_DROP]);;

let CLOSED_HALFSPACE_GE = prove
 (`!a:real^N b. closed {x | a dot x >= b}`,
  REWRITE_TAC[REAL_ARITH `a >= b <=> --a <= --b`] THEN
  REWRITE_TAC[GSYM DOT_LNEG; CLOSED_HALFSPACE_LE]);;

let CLOSED_HYPERPLANE = prove
 (`!a b. closed {x | a dot x = b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  REWRITE_TAC[REAL_ARITH `b <= a dot x <=> a dot x >= b`] THEN
  REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  SIMP_TAC[CLOSED_INTER; CLOSED_HALFSPACE_LE; CLOSED_HALFSPACE_GE]);;

let CLOSED_STANDARD_HYPERPLANE = prove
 (`!k a. closed {x:real^N | x$k = a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CLOSED_HYPERPLANE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CLOSED_HALFSPACE_COMPONENT_LE = prove
 (`!a k. closed {x:real^N | x$k <= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CLOSED_HALFSPACE_LE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CLOSED_HALFSPACE_COMPONENT_GE = prove
 (`!a k. closed {x:real^N | x$k >= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CLOSED_HALFSPACE_GE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

(* ------------------------------------------------------------------------- *)
(* Openness of halfspaces.                                                   *)
(* ------------------------------------------------------------------------- *)

let OPEN_HALFSPACE_LT = prove
 (`!a b. open {x | a dot x < b}`,
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  REWRITE_TAC[SET_RULE `{x | ~p x} = UNIV DIFF {x | p x}`] THEN
  REWRITE_TAC[GSYM closed; GSYM real_ge; CLOSED_HALFSPACE_GE]);;

let OPEN_HALFSPACE_COMPONENT_LT = prove
 (`!a k. open {x:real^N | x$k < a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] OPEN_HALFSPACE_LT) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let OPEN_HALFSPACE_GT = prove
 (`!a b. open {x | a dot x > b}`,
  REWRITE_TAC[REAL_ARITH `x > y <=> ~(x <= y)`] THEN
  REWRITE_TAC[SET_RULE `{x | ~p x} = UNIV DIFF {x | p x}`] THEN
  REWRITE_TAC[GSYM closed; CLOSED_HALFSPACE_LE]);;

let OPEN_HALFSPACE_COMPONENT_GT = prove
 (`!a k. open {x:real^N | x$k > a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] OPEN_HALFSPACE_GT) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let OPEN_POSITIVE_MULTIPLES = prove
 (`!s:real^N->bool. open s ==> open {c % x | &0 < c /\ x IN s}`,
  REWRITE_TAC[open_def; FORALL_IN_GSPEC] THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c * e:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(c) % y:real^N`) THEN ANTS_TAC THENL
   [SUBGOAL_THEN `x:real^N = inv c % c % x` SUBST1_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID;
                   REAL_LT_IMP_NZ];
      ASM_SIMP_TAC[DIST_MUL; real_abs; REAL_LT_INV_EQ; REAL_LT_IMP_LE] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `inv c * x:real = x / c`] THEN
      ASM_MESON_TAC[REAL_LT_LDIV_EQ; REAL_MUL_SYM]];
    DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `c:real` THEN EXISTS_TAC `inv(c) % y:real^N` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
    VECTOR_ARITH_TAC]);;

let OPEN_INTERVAL_LEFT = prove
 (`!b:real^N. open {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> x$i < b$i}`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `{x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> x$i < b$i} =
    INTERS{{x | x$i < (b:real^N)$i} | i IN 1..dimindex(:N)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_NUMSEG] THEN SET_TAC[];
    MATCH_MP_TAC OPEN_INTERS THEN
    SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; OPEN_HALFSPACE_COMPONENT_LT]]);;

let OPEN_INTERVAL_RIGHT = prove
 (`!a:real^N. open {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> a$i < x$i}`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `{x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> a$i < x$i} =
    INTERS{{x | (a:real^N)$i < x$i} | i IN 1..dimindex(:N)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_NUMSEG] THEN SET_TAC[];
    MATCH_MP_TAC OPEN_INTERS THEN
    SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT]]);;

let OPEN_POSITIVE_ORTHANT = prove
 (`open {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> &0 < x$i}`,
  MP_TAC(ISPEC `vec 0:real^N` OPEN_INTERVAL_RIGHT) THEN
  REWRITE_TAC[VEC_COMPONENT]);;

(* ------------------------------------------------------------------------- *)
(* Closures and interiors of halfspaces.                                     *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_HALFSPACE_LE = prove
 (`!a:real^N b.
        ~(a = vec 0) ==> interior {x | a dot x <= b} = {x | a dot x < b}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_UNIQUE THEN
  SIMP_TAC[OPEN_HALFSPACE_LT; SUBSET; IN_ELIM_THM; REAL_LT_IMP_LE] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[REAL_LT_LE] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[SUBSET; IN_CBALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x + e / norm(a) % a:real^N`) THEN
  REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL;
               NORM_EQ_0; REAL_ARITH `&0 < x ==> abs x <= x`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC  `x + e / norm(a) % a:real^N`) THEN
  ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e ==> ~(b + e <= b)`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; NORM_POS_LT; DOT_POS_LT]);;

let INTERIOR_HALFSPACE_GE = prove
 (`!a:real^N b.
        ~(a = vec 0) ==> interior {x | a dot x >= b} = {x | a dot x > b}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a >= b <=> --a <= --b`;
                   REAL_ARITH `a > b <=> --a < --b`] THEN
  ASM_SIMP_TAC[GSYM DOT_LNEG; INTERIOR_HALFSPACE_LE; VECTOR_NEG_EQ_0]);;

let INTERIOR_HALFSPACE_COMPONENT_LE = prove
 (`!a k. interior {x:real^N | x$k <= a} = {x | x$k < a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] INTERIOR_HALFSPACE_LE) THEN
  ASM_SIMP_TAC[DOT_BASIS; BASIS_NONZERO]);;

let INTERIOR_HALFSPACE_COMPONENT_GE = prove
 (`!a k. interior {x:real^N | x$k >= a} = {x | x$k > a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] INTERIOR_HALFSPACE_GE) THEN
  ASM_SIMP_TAC[DOT_BASIS; BASIS_NONZERO]);;

let CLOSURE_HALFSPACE_LT = prove
 (`!a:real^N b.
        ~(a = vec 0) ==> closure {x | a dot x < b} = {x | a dot x <= b}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSURE_INTERIOR] THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF {x | P x} = {x | ~P x}`] THEN
  ASM_SIMP_TAC[REAL_ARITH `~(x < b) <=> x >= b`; INTERIOR_HALFSPACE_GE] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CLOSURE_HALFSPACE_GT = prove
 (`!a:real^N b.
        ~(a = vec 0) ==> closure {x | a dot x > b} = {x | a dot x >= b}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a >= b <=> --a <= --b`;
                   REAL_ARITH `a > b <=> --a < --b`] THEN
  ASM_SIMP_TAC[GSYM DOT_LNEG; CLOSURE_HALFSPACE_LT; VECTOR_NEG_EQ_0]);;

let CLOSURE_HALFSPACE_COMPONENT_LT = prove
 (`!a k. closure {x:real^N | x$k < a} = {x | x$k <= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CLOSURE_HALFSPACE_LT) THEN
  ASM_SIMP_TAC[DOT_BASIS; BASIS_NONZERO]);;

let CLOSURE_HALFSPACE_COMPONENT_GT = prove
 (`!a k. closure {x:real^N | x$k > a} = {x | x$k >= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CLOSURE_HALFSPACE_GT) THEN
  ASM_SIMP_TAC[DOT_BASIS; BASIS_NONZERO]);;

let INTERIOR_HYPERPLANE = prove
 (`!a b. ~(a = vec 0) ==> interior {x | a dot x = b} = {}`,
  REWRITE_TAC[REAL_ARITH `x = y <=> x <= y /\ x >= y`] THEN
  REWRITE_TAC[SET_RULE `{x | p x /\ q x} = {x | p x} INTER {x | q x}`] THEN
  REWRITE_TAC[INTERIOR_INTER] THEN
  ASM_SIMP_TAC[INTERIOR_HALFSPACE_LE; INTERIOR_HALFSPACE_GE] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

let FRONTIER_HALFSPACE_LE = prove
 (`!a:real^N b. ~(a = vec 0 /\ b = &0)
                ==> frontier {x | a dot x <= b} = {x | a dot x = b}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
  ASM_SIMP_TAC[DOT_LZERO] THENL
   [ASM_CASES_TAC `&0 <= b` THEN
    ASM_REWRITE_TAC[UNIV_GSPEC; FRONTIER_UNIV; EMPTY_GSPEC; FRONTIER_EMPTY];
    ASM_SIMP_TAC[frontier; INTERIOR_HALFSPACE_LE; CLOSURE_CLOSED;
                 CLOSED_HALFSPACE_LE] THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

let FRONTIER_HALFSPACE_GE = prove
 (`!a:real^N b. ~(a = vec 0 /\ b = &0)
                ==> frontier {x | a dot x >= b} = {x | a dot x = b}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`--a:real^N`; `--b:real`] FRONTIER_HALFSPACE_LE) THEN
  ASM_REWRITE_TAC[VECTOR_NEG_EQ_0; REAL_NEG_EQ_0; DOT_LNEG] THEN
  REWRITE_TAC[REAL_LE_NEG2; REAL_EQ_NEG2; real_ge]);;

let FRONTIER_HALFSPACE_LT = prove
 (`!a:real^N b. ~(a = vec 0 /\ b = &0)
                ==> frontier {x | a dot x < b} = {x | a dot x = b}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
  ASM_SIMP_TAC[DOT_LZERO] THENL
   [ASM_CASES_TAC `&0 < b` THEN
    ASM_REWRITE_TAC[UNIV_GSPEC; FRONTIER_UNIV; EMPTY_GSPEC; FRONTIER_EMPTY];
    ASM_SIMP_TAC[frontier; CLOSURE_HALFSPACE_LT; INTERIOR_OPEN;
                 OPEN_HALFSPACE_LT] THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

let FRONTIER_HALFSPACE_GT = prove
 (`!a:real^N b. ~(a = vec 0 /\ b = &0)
                ==> frontier {x | a dot x > b} = {x | a dot x = b}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`--a:real^N`; `--b:real`] FRONTIER_HALFSPACE_LT) THEN
  ASM_REWRITE_TAC[VECTOR_NEG_EQ_0; REAL_NEG_EQ_0; DOT_LNEG] THEN
  REWRITE_TAC[REAL_LT_NEG2; REAL_EQ_NEG2; real_gt]);;

let INTERIOR_STANDARD_HYPERPLANE = prove
 (`!k a. interior {x:real^N | x$k = a} = {}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] INTERIOR_HYPERPLANE) THEN
  ASM_SIMP_TAC[DOT_BASIS; BASIS_NONZERO]);;

let EMPTY_INTERIOR_LOWDIM = prove
 (`!s:real^N->bool. dim(s) < dimindex(:N) ==> interior s = {}`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LOWDIM_SUBSET_HYPERPLANE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(SET_RULE
   `!t u. s SUBSET t /\ t SUBSET u /\ u = {} ==> s = {}`) THEN
  MAP_EVERY EXISTS_TAC
   [`interior(span(s):real^N->bool)`;
    `interior({x:real^N | a dot x = &0})`] THEN
  ASM_SIMP_TAC[SUBSET_INTERIOR; SPAN_INC; INTERIOR_HYPERPLANE]);;

(* ------------------------------------------------------------------------- *)
(* Unboundedness of halfspaces.                                              *)
(* ------------------------------------------------------------------------- *)

let UNBOUNDED_HALFSPACE_COMPONENT_LE = prove
 (`!a k. ~bounded {x:real^N | x$k <= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !z:real^N. z$k = z$i`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` MP_TAC) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  EXISTS_TAC `--(&1 + max (abs B) (abs a)) % basis i:real^N` THEN
  ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; BASIS_COMPONENT;
               VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let UNBOUNDED_HALFSPACE_COMPONENT_GE = prove
 (`!a k. ~bounded {x:real^N | x$k >= a}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_NEGATIONS) THEN
  MP_TAC(SPECL [`--a:real`; `k:num`] UNBOUNDED_HALFSPACE_COMPONENT_LE) THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN CONJ_TAC THENL
   [MESON_TAC[VECTOR_NEG_NEG];
    REWRITE_TAC[IN_ELIM_THM; VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC]);;

let UNBOUNDED_HALFSPACE_COMPONENT_LT = prove
 (`!a k. ~bounded {x:real^N | x$k < a}`,
  ONCE_REWRITE_TAC[GSYM BOUNDED_CLOSURE_EQ] THEN
  REWRITE_TAC[CLOSURE_HALFSPACE_COMPONENT_LT;
              UNBOUNDED_HALFSPACE_COMPONENT_LE]);;

let UNBOUNDED_HALFSPACE_COMPONENT_GT = prove
 (`!a k. ~bounded {x:real^N | x$k > a}`,
  ONCE_REWRITE_TAC[GSYM BOUNDED_CLOSURE_EQ] THEN
  REWRITE_TAC[CLOSURE_HALFSPACE_COMPONENT_GT;
              UNBOUNDED_HALFSPACE_COMPONENT_GE]);;

let BOUNDED_HALFSPACE_LE = prove
 (`!a:real^N b. bounded {x | a dot x <= b} <=> a = vec 0 /\ b < &0`,
  GEOM_BASIS_MULTIPLE_TAC 1 `a:real^N` THEN
  SIMP_TAC[DOT_LMUL; DOT_BASIS; VECTOR_MUL_EQ_0; DIMINDEX_GE_1; LE_REFL;
           BASIS_NONZERO] THEN
  X_GEN_TAC `a:real` THEN ASM_CASES_TAC `a = &0` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN X_GEN_TAC `b:real` THENL
   [REWRITE_TAC[REAL_MUL_LZERO; DOT_LZERO; GSYM REAL_NOT_LE] THEN
    ASM_CASES_TAC `&0 <= b` THEN
    ASM_REWRITE_TAC[BOUNDED_EMPTY; NOT_BOUNDED_UNIV;
                    SET_RULE `{x | T} = UNIV`; EMPTY_GSPEC];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_LE;
                 UNBOUNDED_HALFSPACE_COMPONENT_LE]]);;

let BOUNDED_HALFSPACE_GE = prove
 (`!a:real^N b. bounded {x | a dot x >= b} <=> a = vec 0 /\ &0 < b`,
  REWRITE_TAC[REAL_ARITH `a >= b <=> --a <= --b`] THEN
  REWRITE_TAC[GSYM DOT_LNEG; BOUNDED_HALFSPACE_LE] THEN
  REWRITE_TAC[VECTOR_NEG_EQ_0; REAL_ARITH `--b < &0 <=> &0 < b`]);;

let BOUNDED_HALFSPACE_LT = prove
 (`!a:real^N b. bounded {x | a dot x < b} <=> a = vec 0 /\ b <= &0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[DOT_LZERO; GSYM REAL_NOT_LE] THEN ASM_CASES_TAC `b <= &0` THEN
    ASM_REWRITE_TAC[BOUNDED_EMPTY; NOT_BOUNDED_UNIV;
                    SET_RULE `{x | T} = UNIV`; EMPTY_GSPEC];
    ONCE_REWRITE_TAC[GSYM BOUNDED_CLOSURE_EQ] THEN
    ASM_SIMP_TAC[CLOSURE_HALFSPACE_LT; BOUNDED_HALFSPACE_LE]]);;

let BOUNDED_HALFSPACE_GT = prove
 (`!a:real^N b. bounded {x | a dot x > b} <=> a = vec 0 /\ &0 <= b`,
  REWRITE_TAC[REAL_ARITH `a > b <=> --a < --b`] THEN
  REWRITE_TAC[GSYM DOT_LNEG; BOUNDED_HALFSPACE_LT] THEN
  REWRITE_TAC[VECTOR_NEG_EQ_0; REAL_ARITH `--b <= &0 <=> &0 <= b`]);;

(* ------------------------------------------------------------------------- *)
(* Equality of continuous functions on closure and related results.          *)
(* ------------------------------------------------------------------------- *)

let FORALL_IN_CLOSURE = prove
 (`!f:real^M->real^N s t.
        closed t /\ f continuous_on (closure s) /\
        (!x. x IN s ==> f x IN t)
        ==> (!x. x IN closure s ==> f x IN t)`,
  REWRITE_TAC[SET_RULE `(!x. x IN s ==> f x IN t) <=>
                        s SUBSET {x | x IN s /\ f x IN t}`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
  ASM_REWRITE_TAC[CLOSED_CLOSURE] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `s:real^M->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
    ASM_REWRITE_TAC[CLOSED_CLOSURE]]);;

let FORALL_IN_CLOSURE_EQ = prove
 (`!f s t.
         closed t /\ f continuous_on closure s
         ==> ((!x. x IN closure s ==> f x IN t) <=>
              (!x. x IN s ==> f x IN t))`,
  MESON_TAC[FORALL_IN_CLOSURE; CLOSURE_SUBSET; SUBSET]);;

let SUP_CLOSURE = prove
 (`!s. sup(IMAGE drop (closure s)) = sup(IMAGE drop s)`,
  GEN_TAC THEN MATCH_MP_TAC SUP_EQ THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `drop x <= b <=> x IN {x | drop x <= b}`] THEN
  MATCH_MP_TAC FORALL_IN_CLOSURE_EQ THEN
  REWRITE_TAC[CONTINUOUS_ON_ID; drop; CLOSED_HALFSPACE_COMPONENT_LE]);;

let INF_CLOSURE = prove
 (`!s. inf(IMAGE drop (closure s)) = inf(IMAGE drop s)`,
  GEN_TAC THEN MATCH_MP_TAC INF_EQ THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `b <= drop x <=> x IN {x | b <= drop x}`] THEN
  MATCH_MP_TAC FORALL_IN_CLOSURE_EQ THEN
  REWRITE_TAC[CONTINUOUS_ON_ID; drop; CLOSED_HALFSPACE_COMPONENT_GE;
              GSYM real_ge]);;

let CONTINUOUS_LE_ON_CLOSURE = prove
 (`!f:real^M->real s a.
        (lift o f) continuous_on closure(s) /\ (!x. x IN s ==> f(x) <= a)
        ==> !x. x IN closure(s) ==> f(x) <= a`,
  let lemma = prove
   (`x IN s ==> f x <= a <=> x IN s ==> (lift o f) x IN {y | y$1 <= a}`,
    REWRITE_TAC[IN_ELIM_THM; o_THM; GSYM drop; LIFT_DROP]) in
  REWRITE_TAC[lemma] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC FORALL_IN_CLOSURE THEN
  ASM_REWRITE_TAC[ETA_AX; CLOSED_HALFSPACE_COMPONENT_LE]);;

let CONTINUOUS_GE_ON_CLOSURE = prove
 (`!f:real^M->real s a.
        (lift o f) continuous_on closure(s) /\ (!x. x IN s ==> a <= f(x))
        ==> !x. x IN closure(s) ==> a <= f(x)`,
  let lemma = prove
   (`x IN s ==> a <= f x <=> x IN s ==> (lift o f) x IN {y | y$1 >= a}`,
    REWRITE_TAC[IN_ELIM_THM; o_THM; GSYM drop; real_ge; LIFT_DROP]) in
  REWRITE_TAC[lemma] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC FORALL_IN_CLOSURE THEN
  ASM_REWRITE_TAC[ETA_AX; CLOSED_HALFSPACE_COMPONENT_GE]);;

let CONTINUOUS_CONSTANT_ON_CLOSURE = prove
 (`!f:real^M->real^N s a.
        f continuous_on closure(s) /\ (!x. x IN s ==> f(x) = a)
        ==> !x. x IN closure(s) ==> f(x) = a`,
  REWRITE_TAC[SET_RULE
   `x IN s ==> f x = a <=> x IN s ==> f x IN {a}`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FORALL_IN_CLOSURE THEN
  ASM_REWRITE_TAC[CLOSED_SING]);;

let CONTINUOUS_AGREE_ON_CLOSURE = prove
 (`!g h:real^M->real^N.
        g continuous_on closure s /\ h continuous_on closure s /\
        (!x. x IN s ==> g x = h x)
        ==> !x. x IN closure s ==> g x = h x`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_CONSTANT_ON_CLOSURE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_SUB]);;

let CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT = prove
 (`!f:real^M->real^N s a.
        f continuous_on s
        ==> closed_in (subtopology euclidean s) {x | x IN s /\ f x = a}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x | x IN s /\ f(x) = a} = {x | x IN s /\ f(x) IN {a}}`] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
  ASM_REWRITE_TAC[CLOSED_SING]);;

let CONTINUOUS_CLOSED_PREIMAGE_CONSTANT = prove
 (`!f:real^M->real^N s.
      f continuous_on s /\ closed s ==> closed {x | x IN s /\ f(x) = a}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `{x | x IN s /\ (f:real^M->real^N)(x) = a} = {}` THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY] THEN ONCE_REWRITE_TAC[SET_RULE
   `{x | x IN s /\ f(x) = a} = {x | x IN s /\ f(x) IN {a}}`] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
  ASM_REWRITE_TAC[CLOSED_SING] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Theorems relating continuity and uniform continuity to closures.          *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CLOSURE = prove
 (`!f:real^M->real^N s.
        f continuous_on closure s <=>
        !x e. x IN closure s /\ &0 < e
              ==> ?d. &0 < d /\
                      !y. y IN s /\ dist(y,x) < d ==> dist(f y,f x) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_on] THEN
  EQ_TAC THENL [MESON_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:real^M`; `e / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^M`; `e / &2`]) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`y:real^M`; `s:real^M->bool`] CLOSURE_APPROACHABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `min k (d / &2)`) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_LT_MIN] THEN
  ASM_MESON_TAC[DIST_SYM; NORM_ARITH
    `dist(a,b) < e / &2 /\ dist(b,c) < e / &2 ==> dist(a,c) < e`]);;

let CONTINUOUS_ON_CLOSURE_SEQUENTIALLY = prove
 (`!f:real^M->real^N s.
        f continuous_on closure s <=>
        !x a. a IN closure s /\ (!n. x n IN s) /\ (x --> a) sequentially
              ==> ((f o x) --> f a) sequentially`,
  REWRITE_TAC[CONTINUOUS_ON_CLOSURE] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IMP_IMP; GSYM continuous_within] THEN
  REWRITE_TAC[CONTINUOUS_WITHIN_SEQUENTIALLY] THEN MESON_TAC[]);;

let UNIFORMLY_CONTINUOUS_ON_CLOSURE = prove
 (`!f:real^M->real^N s.
        f uniformly_continuous_on s /\ f continuous_on closure s
        ==> f uniformly_continuous_on closure s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[uniformly_continuous_on] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &3` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_on]) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `y:real^M` th) THEN MP_TAC(SPEC `x:real^M` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPECL [`x:real^M`; `s:real^M->bool`] CLOSURE_APPROACHABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `min d1 (d / &3)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_LT_MIN]] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^M` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `x':real^M`) THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPECL [`y:real^M`; `s:real^M->bool`] CLOSURE_APPROACHABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `min d2 (d / &3)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_LT_MIN]] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^M` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `y':real^M`) THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x':real^M`; `y':real^M`]) THEN
  ASM_MESON_TAC[DIST_SYM; NORM_ARITH
   `dist(y,x) < d / &3 /\ dist(x',x) < d / &3 /\ dist(y',y) < d / &3
    ==> dist(y',x') < d`]);;

(* ------------------------------------------------------------------------- *)
(* Continuity properties for square roots. We get other forms of this        *)
(* later (transcendentals.ml and realanalysis.ml) but it's nice to have      *)
(* them around earlier.                                                      *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_AT_SQRT = prove
 (`!a s. &0 < drop a ==>  (lift o sqrt o drop) continuous (at a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_at; o_THM; DIST_LIFT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `min (drop a) (e * sqrt(drop a))` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; SQRT_POS_LT; REAL_LT_MUL; DIST_REAL] THEN
  X_GEN_TAC `b:real^1` THEN REWRITE_TAC[GSYM drop] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `abs(b - a) < a ==> &0 < b`)) THEN
  SUBGOAL_THEN
   `sqrt(drop b) - sqrt(drop a) =
    (drop b - drop a) / (sqrt(drop a) + sqrt(drop b))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD
     `sa pow 2 = a /\ sb pow 2 = b /\ &0 < sa /\ &0 < sb
      ==> sb - sa = (b - a) / (sa + sb)`) THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_ABS_DIV; SQRT_POS_LT; REAL_LT_ADD; REAL_LT_LDIV_EQ;
                 REAL_ARITH `&0 < x ==> abs x = x`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        REAL_LTE_TRANS)) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LE_ADDR; SQRT_POS_LE;
                 REAL_LT_IMP_LE]]);;

let CONTINUOUS_WITHIN_LIFT_SQRT = prove
 (`!a s. (!x. x IN s ==> &0 <= drop x)
         ==> (lift o sqrt o drop) continuous (at a within s)`,
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `drop a < &0 \/ drop a = &0 \/ &0 < drop a`)
  THENL
   [MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN
    EXISTS_TAC `{x | &0 <= drop x}` THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM] THEN
    MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; REAL_NOT_LE] THEN
    REWRITE_TAC[drop; REWRITE_RULE[real_ge] CLOSED_HALFSPACE_COMPONENT_GE];
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM LIFT_EQ; LIFT_DROP; LIFT_NUM]) THEN
    ASM_REWRITE_TAC[continuous_within; o_THM; DROP_VEC; SQRT_0; LIFT_NUM] THEN
    REWRITE_TAC[DIST_0; NORM_LIFT; NORM_REAL; GSYM drop] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `(e:real) pow 2` THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[real_abs; SQRT_POS_LE] THEN
    SUBGOAL_THEN `e = sqrt(e pow 2)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
      MATCH_MP_TAC SQRT_MONO_LT THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    MATCH_MP_TAC CONTINUOUS_AT_SQRT THEN ASM_REWRITE_TAC[]]);;

let CONTINUOUS_WITHIN_SQRT_COMPOSE = prove
 (`!f s a:real^N.
        (\x. lift(f x)) continuous (at a within s) /\
        (&0 < f a \/ !x. x IN s ==> &0 <= f x)
        ==> (\x. lift(sqrt(f x))) continuous (at a within s)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\x:real^N. lift(sqrt(f x))) = (lift o sqrt o drop) o (lift o f)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF; LIFT_DROP]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  (MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[o_DEF]; ALL_TAC])
  THENL
   [MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    MATCH_MP_TAC CONTINUOUS_AT_SQRT THEN ASM_REWRITE_TAC[o_DEF; LIFT_DROP];
    MATCH_MP_TAC CONTINUOUS_WITHIN_LIFT_SQRT THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; o_DEF; LIFT_DROP]]);;

let CONTINUOUS_AT_SQRT_COMPOSE = prove
 (`!f a:real^N.
        (\x. lift(f x)) continuous (at a) /\ (&0 < f a \/ !x. &0 <= f x)
        ==> (\x. lift(sqrt(f x))) continuous (at a)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real`; `(:real^N)`; `a:real^N`]
        CONTINUOUS_WITHIN_SQRT_COMPOSE) THEN
  REWRITE_TAC[WITHIN_UNIV; IN_UNIV]);;

let CONTINUOUS_ON_LIFT_SQRT = prove
 (`!s. (!x. x IN s ==> &0 <= drop x)
       ==> (lift o sqrt o drop) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_WITHIN_LIFT_SQRT]);;

let CONTINUOUS_ON_LIFT_SQRT_COMPOSE = prove
 (`!f:real^N->real s.
        (lift o f) continuous_on s /\ (!x. x IN s ==> &0 <= f x)
        ==> (\x. lift(sqrt(f x))) continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^N. lift(sqrt(f x))) = (lift o sqrt o drop) o (lift o f)`
  SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_DROP];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP]]);;

(* ------------------------------------------------------------------------- *)
(* Cauchy continuity, and the extension of functions to closures.            *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONTINUOUS_IMP_CAUCHY_CONTINUOUS = prove
 (`!f:real^M->real^N s.
        f uniformly_continuous_on s
        ==> (!x. cauchy x /\ (!n. (x n) IN s) ==> cauchy(f o x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[uniformly_continuous_on; cauchy; o_DEF] THEN
  MESON_TAC[]);;

let CONTINUOUS_CLOSED_IMP_CAUCHY_CONTINUOUS = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ closed s
        ==> (!x. cauchy x /\ (!n. (x n) IN s) ==> cauchy(f o x))`,
  REWRITE_TAC[GSYM COMPLETE_EQ_CLOSED; CONTINUOUS_ON_SEQUENTIALLY] THEN
  REWRITE_TAC[complete] THEN MESON_TAC[CONVERGENT_IMP_CAUCHY]);;

let CAUCHY_CONTINUOUS_UNIQUENESS_LEMMA = prove
 (`!f:real^M->real^N s.
        (!x. cauchy x /\ (!n. (x n) IN s) ==> cauchy(f o x))
        ==> !a x. (!n. (x n) IN s) /\ (x --> a) sequentially
                  ==> ?l. ((f o x) --> l) sequentially /\
                          !y. (!n. (y n) IN s) /\ (y --> a) sequentially
                              ==> ((f o y) --> l) sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num->real^M`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONVERGENT_IMP_CAUCHY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `l:real^N` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:num->real^M` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:num->real^M`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONVERGENT_IMP_CAUCHY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `l:real^N = m` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n:num. (f:real^M->real^N)(x n) - f(y n)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
  ASM_SIMP_TAC[LIM_SUB; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `\n. if EVEN n then x(n DIV 2):real^M else y(n DIV 2)`) THEN
  REWRITE_TAC[cauchy; o_THM; LIM_SEQUENTIALLY] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN MAP_EVERY UNDISCH_TAC
     [`((y:num->real^M) --> a) sequentially`;
      `((x:num->real^M) --> a) sequentially`] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    EXISTS_TAC `2 * (N1 + N2)` THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `m DIV 2` th) THEN MP_TAC(SPEC `n DIV 2` th))) THEN
    REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC]) THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LE])) THEN
    CONV_TAC NORM_ARITH;
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`2 * n`; `2 * n + 1`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
    REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`] THEN
    REWRITE_TAC[dist; VECTOR_SUB_RZERO]]);;

let CAUCHY_CONTINUOUS_EXTENDS_TO_CLOSURE = prove
 (`!f:real^M->real^N s.
        (!x. cauchy x /\ (!n. (x n) IN s) ==> cauchy(f o x))
        ==> ?g. g continuous_on closure s /\ (!x. x IN s ==> g x = f x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a:real^M. ?x.
       a IN closure s ==> (!n. x n IN s) /\ (x --> a) sequentially`
  MP_TAC THENL [MESON_TAC[CLOSURE_SEQUENTIAL]; ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `X:real^M->num->real^M` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CAUCHY_CONTINUOUS_UNIQUENESS_LEMMA) THEN
  DISCH_THEN(MP_TAC o GEN `a:real^M` o
   SPECL [`a:real^M`; `(X:real^M->num->real^M) a`]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
   `(!a. P a ==> Q a) ==> ((!a. P a ==> R a) ==> p)
    ==> ((!a. Q a ==> R a) ==> p)`)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^N` THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [X_GEN_TAC `a:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^M`) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `(\n. a):num->real^M` o CONJUNCT2) THEN
    ASM_SIMP_TAC[LIM_CONST_EQ; o_DEF; TRIVIAL_LIMIT_SEQUENTIALLY];
    STRIP_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CLOSURE_SEQUENTIALLY] THEN
  MAP_EVERY X_GEN_TAC [`x:num->real^M`; `a:real^M`] THEN STRIP_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `(f:real^M->real^N) o (x:num->real^M)` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN ASM_SIMP_TAC[o_THM]);;

let UNIFORMLY_CONTINUOUS_EXTENDS_TO_CLOSURE = prove
 (`!f:real^M->real^N s.
   f uniformly_continuous_on s
   ==> ?g. g uniformly_continuous_on closure s /\ (!x. x IN s ==> g x = f x) /\
           !h. h continuous_on closure s /\ (!x. x IN s ==> h x = f x)
               ==> !x. x IN closure s ==> h x = g x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CAUCHY_CONTINUOUS_EXTENDS_TO_CLOSURE o
   MATCH_MP UNIFORMLY_CONTINUOUS_IMP_CAUCHY_CONTINUOUS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[UNIFORMLY_CONTINUOUS_ON_CLOSURE; UNIFORMLY_CONTINUOUS_ON_EQ];
    ASM_MESON_TAC[CONTINUOUS_AGREE_ON_CLOSURE]]);;

let CAUCHY_CONTINUOUS_IMP_CONTINUOUS = prove
 (`!f:real^M->real^N s.
        (!x. cauchy x /\ (!n. (x n) IN s) ==> cauchy(f o x))
        ==> f continuous_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(CHOOSE_TAC o MATCH_MP CAUCHY_CONTINUOUS_EXTENDS_TO_CLOSURE) THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; CLOSURE_SUBSET; CONTINUOUS_ON_EQ]);;

let BOUNDED_UNIFORMLY_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N s.
        f uniformly_continuous_on s /\ bounded s ==> bounded(IMAGE f s)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o MATCH_MP UNIFORMLY_CONTINUOUS_EXTENDS_TO_CLOSURE) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `IMAGE (g:real^M->real^N) (closure s)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[COMPACT_CLOSURE; UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS;
                  COMPACT_IMP_BOUNDED; COMPACT_CONTINUOUS_IMAGE];
    MP_TAC(ISPEC `s:real^M->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Occasionally useful invariance properties.                                *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_AT_COMPOSE_EQ = prove
 (`!f:real^M->real^N g:real^M->real^M h:real^M->real^M.
        g continuous at x /\ h continuous at (g x) /\
        (!y. g(h y) = y) /\ h(g x) = x
        ==> (f continuous at (g x) <=> (\x. f(g x)) continuous at x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_AT_COMPOSE] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `((f:real^M->real^N) o (g:real^M->real^M) o (h:real^M->real^M))
     continuous at (g(x:real^M))`
  MP_TAC THENL
   [REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    ASM_REWRITE_TAC[o_DEF];

    ASM_REWRITE_TAC[o_DEF; ETA_AX]]);;

let CONTINUOUS_AT_TRANSLATION = prove
 (`!a z f:real^M->real^N.
      f continuous at (a + z) <=> (\x. f(a + x)) continuous at z`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE_EQ THEN
  EXISTS_TAC `\x:real^M. x - a` THEN
  SIMP_TAC[CONTINUOUS_ADD; CONTINUOUS_SUB;
           CONTINUOUS_AT_ID; CONTINUOUS_CONST] THEN
  VECTOR_ARITH_TAC);;

add_translation_invariants [CONTINUOUS_AT_TRANSLATION];;

let CONTINUOUS_AT_LINEAR_IMAGE = prove
 (`!h:real^M->real^M z f:real^M->real^N.
        linear h /\ (!x. norm(h x) = norm x)
        ==> (f continuous at (h z) <=> (\x. f(h x)) continuous at z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I
   [GSYM ORTHOGONAL_TRANSFORMATION]) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g:real^M->real^M` o MATCH_MP
    ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE_EQ THEN
  EXISTS_TAC `g:real^M->real^M` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ORTHOGONAL_TRANSFORMATION]) THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT]);;

add_linear_invariants [CONTINUOUS_AT_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Interior of an injective image.                                           *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_IMAGE_SUBSET = prove
 (`!f:real^M->real^N s.
       (!x. f continuous at x) /\ (!x y. f x = f y ==> x = y)
       ==> interior(IMAGE f s) SUBSET IMAGE f (interior s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  SUBGOAL_THEN `y IN IMAGE (f:real^M->real^N) s` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  EXISTS_TAC `{x | (f:real^M->real^N)(x) IN t}` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_MESON_TAC[];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Making a continuous function avoid some value in a neighbourhood.         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_AVOID = prove
 (`!f:real^M->real^N x s a.
        f continuous (at x within s) /\ x IN s /\  ~(f x = a)
        ==> ?e. &0 < e /\ !y. y IN s /\ dist(x,y) < e ==> ~(f y = a)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_within]) THEN
  DISCH_THEN(MP_TAC o SPEC `norm((f:real^M->real^N) x - a)`) THEN
  ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN SIMP_TAC[] THEN NORM_ARITH_TAC);;

let CONTINUOUS_AT_AVOID = prove
 (`!f:real^M->real^N x a.
        f continuous (at x) /\ ~(f x = a)
        ==> ?e. &0 < e /\ !y. dist(x,y) < e ==> ~(f y = a)`,
  MP_TAC CONTINUOUS_WITHIN_AVOID THEN
  REPLICATE_TAC 2 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `(:real^M)`) THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  REWRITE_TAC[WITHIN_UNIV; IN_UNIV]);;

let CONTINUOUS_ON_AVOID = prove
 (`!f:real^M->real^N x s a.
        f continuous_on s /\ x IN s /\ ~(f x = a)
        ==> ?e. &0 < e /\ !y. y IN s /\ dist(x,y) < e ==> ~(f y = a)`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_WITHIN_AVOID THEN
  ASM_SIMP_TAC[]);;

let CONTINUOUS_ON_OPEN_AVOID = prove
 (`!f:real^M->real^N x s a.
        f continuous_on s /\ open s /\ x IN s /\ ~(f x = a)
        ==> ?e. &0 < e /\ !y. dist(x,y) < e ==> ~(f y = a)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `open(s:real^M->bool)` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_AVOID THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Proving a function is constant by proving open-ness of level set.         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_LEVELSET_OPEN_IN_CASES = prove
 (`!f:real^M->real^N s a.
        connected s /\
        f continuous_on s /\
        open_in (subtopology euclidean s) {x | x IN s /\ f x = a}
        ==> (!x. x IN s ==> ~(f x = a)) \/ (!x. x IN s ==> f x = a)`,
  REWRITE_TAC[SET_RULE `(!x. x IN s ==> ~(f x = a)) <=>
                        {x | x IN s /\ f x = a} = {}`;
              SET_RULE `(!x. x IN s ==> f x = a) <=>
                        {x | x IN s /\ f x = a} = s`] THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT]);;

let CONTINUOUS_LEVELSET_OPEN_IN = prove
 (`!f:real^M->real^N s a.
        connected s /\
        f continuous_on s /\
        open_in (subtopology euclidean s) {x | x IN s /\ f x = a} /\
        (?x. x IN s /\ f x = a)
        ==> (!x. x IN s ==> f x = a)`,
  MESON_TAC[CONTINUOUS_LEVELSET_OPEN_IN_CASES]);;

let CONTINUOUS_LEVELSET_OPEN = prove
 (`!f:real^M->real^N s a.
        connected s /\
        f continuous_on s /\
        open {x | x IN s /\ f x = a} /\
        (?x. x IN s /\ f x = a)
        ==> (!x. x IN s ==> f x = a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC CONTINUOUS_LEVELSET_OPEN_IN THEN
  ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
  EXISTS_TAC `{x | x IN s /\ (f:real^M->real^N) x = a}` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some arithmetical combinations (more to prove).                           *)
(* ------------------------------------------------------------------------- *)

let OPEN_SCALING = prove
 (`!s:real^N->bool c. ~(c = &0) /\ open s ==> open(IMAGE (\x. c % x) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[open_def; FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e * abs(c)` THEN ASM_SIMP_TAC[REAL_LT_MUL; GSYM REAL_ABS_NZ] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `inv(c) % y:real^N` THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `x = inv(c) % c % x:real^N` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID];
    REWRITE_TAC[dist; GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; GSYM REAL_ABS_NZ] THEN
    ASM_REWRITE_TAC[GSYM dist]]);;

let OPEN_NEGATIONS = prove
 (`!s:real^N->bool. open s ==> open (IMAGE (--) s)`,
  SUBGOAL_THEN `(--) = \x:real^N. --(&1) % x`
   (fun th -> SIMP_TAC[th; OPEN_SCALING; REAL_ARITH `~(--(&1) = &0)`]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC);;

let OPEN_TRANSLATION = prove
 (`!s a:real^N. open s ==> open(IMAGE (\x. a + x) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. x - a`; `s:real^N->bool`]
         CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  ASM_SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_AT_ID; CONTINUOUS_CONST] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
  ASM_MESON_TAC[VECTOR_ARITH `(a + x) - a = x:real^N`;
                VECTOR_ARITH `a + (x - a) = x:real^N`]);;

let OPEN_TRANSLATION_EQ = prove
 (`!a s. open (IMAGE (\x:real^N. a + x) s) <=> open s`,
  REWRITE_TAC[open_def] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [OPEN_TRANSLATION_EQ];;

let OPEN_AFFINITY = prove
 (`!s a:real^N c.
        open s /\ ~(c = &0) ==> open (IMAGE (\x. a + c % x) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; OPEN_TRANSLATION; OPEN_SCALING]);;

let INTERIOR_TRANSLATION = prove
 (`!a:real^N s.
    interior (IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (interior s)`,
  REWRITE_TAC[interior] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [INTERIOR_TRANSLATION];;

let OPEN_SUMS = prove
 (`!s t:real^N->bool.
        open s \/ open t ==> open {x + y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[open_def] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`);
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`)] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[VECTOR_ADD_SYM; VECTOR_ARITH `(z - y) + y:real^N = z`;
                NORM_ARITH `dist(z:real^N,x + y) < e ==> dist(z - y,x) < e`]);;

(* ------------------------------------------------------------------------- *)
(* Upper and lower hemicontinuous functions, relation in the case of         *)
(* preimage map to open and closed maps, and fact that upper and lower       *)
(* hemicontinuity together imply continuity in the sense of the Hausdorff    *)
(* metric (at points where the function gives a bounded and nonempty set).   *)
(* ------------------------------------------------------------------------- *)

let UPPER_HEMICONTINUOUS = prove
 (`!f:real^M->real^N->bool t s.
        (!x. x IN s ==> f(x) SUBSET t)
        ==> ((!u. open_in (subtopology euclidean t) u
                  ==> open_in (subtopology euclidean s)
                              {x | x IN s /\ f(x) SUBSET u}) <=>
             (!u. closed_in (subtopology euclidean t) u
                  ==> closed_in (subtopology euclidean s)
                                {x | x IN s /\ ~(f(x) INTER u = {})}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t DIFF u:real^N->bool`) THEN
  MATCH_MP_TAC MONO_IMP THEN
  SIMP_TAC[OPEN_IN_DIFF; CLOSED_IN_DIFF; OPEN_IN_REFL; CLOSED_IN_REFL] THENL
   [REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ]; REWRITE_TAC[closed_in]] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET_RESTRICT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let LOWER_HEMICONTINUOUS = prove
 (`!f:real^M->real^N->bool t s.
        (!x. x IN s ==> f(x) SUBSET t)
        ==> ((!u. closed_in (subtopology euclidean t) u
                  ==> closed_in (subtopology euclidean s)
                                {x | x IN s /\ f(x) SUBSET u}) <=>
             (!u. open_in (subtopology euclidean t) u
                  ==> open_in (subtopology euclidean s)
                              {x | x IN s /\ ~(f(x) INTER u = {})}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t DIFF u:real^N->bool`) THEN
  MATCH_MP_TAC MONO_IMP THEN
  SIMP_TAC[OPEN_IN_DIFF; CLOSED_IN_DIFF; OPEN_IN_REFL; CLOSED_IN_REFL] THENL
   [REWRITE_TAC[closed_in]; REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ]] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET_RESTRICT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let OPEN_MAP_IFF_LOWER_HEMICONTINUOUS_PREIMAGE = prove
 (`!f:real^M->real^N s t.
        IMAGE f s SUBSET t
        ==> ((!u. open_in (subtopology euclidean s) u
                  ==> open_in (subtopology euclidean t) (IMAGE f u)) <=>
             (!u. closed_in (subtopology euclidean s) u
                      ==> closed_in (subtopology euclidean t)
                                    {y | y IN t /\
                                         {x | x IN s /\ f x = y} SUBSET u}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `v:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s DIFF v:real^M->bool`) THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL] THEN
    REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[];
    X_GEN_TAC `v:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s DIFF v:real^M->bool`) THEN
    ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL [ASM SET_TAC[]; MP_TAC th]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]]);;

let CLOSED_MAP_IFF_UPPER_HEMICONTINUOUS_PREIMAGE = prove
 (`!f:real^M->real^N s t.
        IMAGE f s SUBSET t
        ==> ((!u. closed_in (subtopology euclidean s) u
                  ==> closed_in (subtopology euclidean t) (IMAGE f u)) <=>
             (!u. open_in (subtopology euclidean s) u
                  ==> open_in (subtopology euclidean t)
                              {y | y IN t /\
                                   {x | x IN s /\ f x = y} SUBSET u}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `v:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s DIFF v:real^M->bool`) THEN
    ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
    REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[];
    X_GEN_TAC `v:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s DIFF v:real^M->bool`) THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
    REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL [ASM SET_TAC[]; MP_TAC th]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]]);;

let UPPER_LOWER_HEMICONTINUOUS_EXPLICIT = prove
 (`!f:real^M->real^N->bool t s.
      (!x. x IN s ==> f(x) SUBSET t) /\
      (!u. open_in (subtopology euclidean t) u
           ==> open_in (subtopology euclidean s)
                       {x | x IN s /\ f(x) SUBSET u}) /\
      (!u. closed_in (subtopology euclidean t) u
           ==> closed_in (subtopology euclidean s)
                         {x | x IN s /\ f(x) SUBSET u})
      ==> !x e. x IN s /\ &0 < e /\ bounded(f x) /\ ~(f x = {})
                ==> ?d. &0 < d /\
                        !x'. x' IN s /\ dist(x,x') < d
                             ==> (!y. y IN f x
                                      ==> ?y'. y' IN f x' /\ dist(y,y') < e) /\
                                 (!y'. y' IN f x'
                                       ==> ?y. y IN f x /\ dist(y',y) < e)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC
   `!u. open_in (subtopology euclidean t) u
        ==> open_in (subtopology euclidean s)
                    {x | x IN s /\ (f:real^M->real^N->bool)(x) SUBSET u}` THEN
  DISCH_THEN(MP_TAC o SPEC
   `t INTER
    {a + b | a IN (f:real^M->real^N->bool) x /\ b IN ball(vec 0,e)}`) THEN
  SIMP_TAC[OPEN_SUMS; OPEN_BALL; OPEN_IN_OPEN_INTER] THEN
  REWRITE_TAC[open_in; SUBSET_RESTRICT] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; SUBSET_INTER] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[CENTRE_IN_BALL; VECTOR_ADD_RID];
    DISCH_THEN(X_CHOOSE_THEN `d1:real`
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1")))] THEN
  UNDISCH_TAC
   `!u. closed_in (subtopology euclidean t) u
        ==> closed_in (subtopology euclidean s)
                    {x | x IN s /\ (f:real^M->real^N->bool)(x) SUBSET u}` THEN
  ASM_SIMP_TAC[LOWER_HEMICONTINUOUS] THEN DISCH_THEN(MP_TAC o
    GEN `a:real^N` o SPEC `t INTER ball(a:real^N,e / &2)`) THEN
  SIMP_TAC[OPEN_BALL; OPEN_IN_OPEN_INTER] THEN

  MP_TAC(SPEC `closure((f:real^M->real^N->bool) x)`
    COMPACT_EQ_HEINE_BOREL) THEN
  ASM_REWRITE_TAC[COMPACT_CLOSURE] THEN DISCH_THEN(MP_TAC o SPEC
   `{ball(a:real^N,e / &2) | a IN (f:real^M->real^N->bool) x}`) THEN
  REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; OPEN_BALL] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN ANTS_TAC THENL
   [REWRITE_TAC[CLOSURE_APPROACHABLE; SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_BALL] THEN ASM_SIMP_TAC[REAL_HALF];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP
   (MESON[CLOSURE_SUBSET; SUBSET_TRANS]
        `closure s SUBSET t ==> s SUBSET t`)) THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean s)
      (INTERS {{x | x IN s /\
          ~((f:real^M->real^N->bool) x INTER t INTER ball(a,e / &2) = {})} |
     a IN c})`
  MP_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTERS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; FINITE_IMAGE] THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[open_in] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M` o CONJUNCT2) THEN ANTS_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; REAL_HALF] THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d2:real`
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2")))] THEN
  EXISTS_TAC `min d1 d2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `x':real^M` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    REMOVE_THEN "1" (MP_TAC o SPEC `x':real^M`) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL] THEN
    REWRITE_TAC[VECTOR_ARITH `x:real^N = a + b <=> x - a = b`;
                DIST_0; ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
    REWRITE_TAC[dist]] THEN
  REMOVE_THEN "2" (MP_TAC o SPEC `x':real^M`) THEN
  ASM_REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "3") THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  UNDISCH_TAC `(f:real^M->real^N->bool) x SUBSET
               UNIONS (IMAGE (\a. ball (a,e / &2)) c)` THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "3" (MP_TAC o SPEC `a:real^N`) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[DIST_TRIANGLE_HALF_L; DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Connected components, considered as a "connectedness" relation or a set.  *)
(* ------------------------------------------------------------------------- *)

let connected_component = new_definition
 `connected_component s x y <=>
        ?t. connected t /\ t SUBSET s /\ x IN t /\ y IN t`;;

let CONNECTED_COMPONENT_IN = prove
 (`!s x y. connected_component s x y ==> x IN s /\ y IN s`,
  REWRITE_TAC[connected_component] THEN SET_TAC[]);;

let CONNECTED_COMPONENT_REFL = prove
 (`!s x:real^N. x IN s ==> connected_component s x x`,
  REWRITE_TAC[connected_component] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `{x:real^N}` THEN REWRITE_TAC[CONNECTED_SING] THEN
  ASM SET_TAC[]);;

let CONNECTED_COMPONENT_REFL_EQ = prove
 (`!s x:real^N. connected_component s x x <=> x IN s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[CONNECTED_COMPONENT_REFL] THEN
  REWRITE_TAC[connected_component] THEN SET_TAC[]);;

let CONNECTED_COMPONENT_SYM = prove
 (`!s x y:real^N. connected_component s x y ==> connected_component s y x`,
  REWRITE_TAC[connected_component] THEN MESON_TAC[]);;

let CONNECTED_COMPONENT_TRANS = prove
 (`!s x y:real^N.
    connected_component s x y /\ connected_component s y z
    ==> connected_component s x z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected_component] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `t:real^N->bool`)
                             (X_CHOOSE_TAC `u:real^N->bool`)) THEN
  EXISTS_TAC `t UNION u:real^N->bool` THEN
  ASM_REWRITE_TAC[IN_UNION; UNION_SUBSET] THEN
  MATCH_MP_TAC CONNECTED_UNION THEN ASM SET_TAC[]);;

let CONNECTED_COMPONENT_OF_SUBSET = prove
 (`!s t x. s SUBSET t /\ connected_component s x y
           ==> connected_component t x y`,
  REWRITE_TAC[connected_component] THEN SET_TAC[]);;

let CONNECTED_COMPONENT_SET = prove
 (`!s x. connected_component s x =
            { y | ?t. connected t /\ t SUBSET s /\ x IN t /\ y IN t}`,
  REWRITE_TAC[IN_ELIM_THM; EXTENSION] THEN
  REWRITE_TAC[IN; connected_component] THEN MESON_TAC[]);;

let CONNECTED_COMPONENT_UNIONS = prove
 (`!s x. connected_component s x =
                UNIONS {t | connected t /\ x IN t /\ t SUBSET s}`,
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN SET_TAC[]);;

let CONNECTED_COMPONENT_SUBSET = prove
 (`!s x. (connected_component s x) SUBSET s`,
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN SET_TAC[]);;

let CONNECTED_CONNECTED_COMPONENT_SET = prove
 (`!s. connected s <=> !x:real^N. x IN s ==> connected_component s x = s`,
  GEN_TAC THEN REWRITE_TAC[CONNECTED_COMPONENT_UNIONS] THEN EQ_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CONNECTED_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CONNECTED_UNIONS THEN
  ASM SET_TAC[]);;

let CONNECTED_COMPONENT_EQ_SELF = prove
 (`!s x. connected s /\ x IN s ==> connected_component s x = s`,
  MESON_TAC[CONNECTED_CONNECTED_COMPONENT_SET]);;

let CONNECTED_IFF_CONNECTED_COMPONENT = prove
 (`!s. connected s <=>
          !x y. x IN s /\ y IN s ==> connected_component s x y`,
  REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT_SET] THEN
  REWRITE_TAC[EXTENSION] THEN MESON_TAC[IN; CONNECTED_COMPONENT_IN]);;

let CONNECTED_COMPONENT_MAXIMAL = prove
 (`!s t x:real^N.
        x IN t /\ connected t /\ t SUBSET s
        ==> t SUBSET (connected_component s x)`,
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN SET_TAC[]);;

let CONNECTED_COMPONENT_MONO = prove
 (`!s t x. s SUBSET t
           ==> (connected_component s x) SUBSET (connected_component t x)`,
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN SET_TAC[]);;

let CONNECTED_CONNECTED_COMPONENT = prove
 (`!s x. connected(connected_component s x)`,
  REWRITE_TAC[CONNECTED_COMPONENT_UNIONS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_UNIONS THEN SET_TAC[]);;

let CONNECTED_COMPONENT_EQ_EMPTY = prove
 (`!s x:real^N. connected_component s x = {} <=> ~(x IN s)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ];
    REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN SET_TAC[]]);;

let CONNECTED_COMPONENT_EMPTY = prove
 (`!x. connected_component {} x = {}`,
  REWRITE_TAC[CONNECTED_COMPONENT_EQ_EMPTY; NOT_IN_EMPTY]);;

let CONNECTED_COMPONENT_EQ = prove
 (`!s x y. y IN connected_component s x
           ==> (connected_component s y = connected_component s x)`,
  REWRITE_TAC[EXTENSION; IN] THEN
  MESON_TAC[CONNECTED_COMPONENT_SYM; CONNECTED_COMPONENT_TRANS]);;

let CLOSED_CONNECTED_COMPONENT = prove
 (`!s x:real^N. closed s ==> closed(connected_component s x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN s` THENL
   [ALL_TAC; ASM_MESON_TAC[CONNECTED_COMPONENT_EQ_EMPTY; CLOSED_EMPTY]] THEN
  REWRITE_TAC[GSYM CLOSURE_EQ] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[CLOSURE_SUBSET] THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
  SIMP_TAC[CONNECTED_CLOSURE; CONNECTED_CONNECTED_COMPONENT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ];
    MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]]);;

let CONNECTED_COMPONENT_DISJOINT = prove
 (`!s a b. DISJOINT (connected_component s a) (connected_component s b) <=>
             ~(a IN connected_component s b)`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN] THEN
  MESON_TAC[CONNECTED_COMPONENT_SYM; CONNECTED_COMPONENT_TRANS]);;

let CONNECTED_COMPONENT_NONOVERLAP = prove
 (`!s a b:real^N.
        (connected_component s a) INTER (connected_component s b) = {} <=>
        ~(a IN s) \/ ~(b IN s) \/
        ~(connected_component s a = connected_component s b)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(a:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONNECTED_COMPONENT_EQ_EMPTY]) THEN
  ASM_REWRITE_TAC[INTER_EMPTY] THEN
  ASM_CASES_TAC `(b:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONNECTED_COMPONENT_EQ_EMPTY]) THEN
  ASM_REWRITE_TAC[INTER_EMPTY] THEN ASM_CASES_TAC
   `connected_component s (a:real^N) = connected_component s b` THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT; CONNECTED_COMPONENT_EQ_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o check(is_neg o concl)) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM DISJOINT]) THEN
  REWRITE_TAC[CONNECTED_COMPONENT_DISJOINT]);;

let CONNECTED_COMPONENT_OVERLAP = prove
 (`!s a b:real^N.
        ~((connected_component s a) INTER (connected_component s b) = {}) <=>
        a IN s /\ b IN s /\
        connected_component s a = connected_component s b`,
  REWRITE_TAC[CONNECTED_COMPONENT_NONOVERLAP; DE_MORGAN_THM]);;

let CONNECTED_COMPONENT_SYM_EQ = prove
 (`!s x y. connected_component s x y <=> connected_component s y x`,
  MESON_TAC[CONNECTED_COMPONENT_SYM]);;

let CONNECTED_COMPONENT_EQ_EQ = prove
 (`!s x y:real^N.
        connected_component s x = connected_component s y <=>
           ~(x IN s) /\ ~(y IN s) \/
           x IN s /\ y IN s /\ connected_component s x y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(y:real^N) IN s` THENL
   [ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN
      ASM_MESON_TAC[CONNECTED_COMPONENT_TRANS; CONNECTED_COMPONENT_REFL;
                    CONNECTED_COMPONENT_SYM];
      ASM_MESON_TAC[CONNECTED_COMPONENT_EQ_EMPTY]];
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONNECTED_COMPONENT_EQ_EMPTY]) THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_EQ_EMPTY] THEN
    ONCE_REWRITE_TAC[CONNECTED_COMPONENT_SYM_EQ] THEN
    ASM_REWRITE_TAC[EMPTY] THEN ASM_MESON_TAC[CONNECTED_COMPONENT_EQ_EMPTY]]);;

let CONNECTED_EQ_CONNECTED_COMPONENT_EQ = prove
 (`!s. connected s <=>
       !x y. x IN s /\ y IN s
             ==> connected_component s x = connected_component s y`,
  SIMP_TAC[CONNECTED_COMPONENT_EQ_EQ] THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT]);;

let CONNECTED_COMPONENT_IDEMP = prove
 (`!s x:real^N. connected_component (connected_component s x) x =
                connected_component s x`,
  REWRITE_TAC[FUN_EQ_THM; connected_component] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_MAXIMAL; SUBSET_TRANS;
                CONNECTED_COMPONENT_SUBSET]);;

let CONNECTED_COMPONENT_UNIQUE = prove
 (`!s c x:real^N.
        x IN c /\ c SUBSET s /\ connected c /\
        (!c'. x IN c' /\ c' SUBSET s /\ connected c'
              ==> c' SUBSET c)
        ==> connected_component s x = c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET; CONNECTED_CONNECTED_COMPONENT] THEN
    REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]]);;

let JOINABLE_CONNECTED_COMPONENT_EQ = prove
 (`!s t x y:real^N.
        connected t /\ t SUBSET s /\
        ~(connected_component s x INTER t = {}) /\
        ~(connected_component s y INTER t = {})
        ==> connected_component s x = connected_component s y`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
  REWRITE_TAC[IN] THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
  EXISTS_TAC `z:real^N` THEN CONJ_TAC THENL [ASM_MESON_TAC[IN]; ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
  EXISTS_TAC `w:real^N` THEN CONJ_TAC THENL
   [REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[IN; CONNECTED_COMPONENT_SYM]]);;

let CONNECTED_COMPONENT_TRANSLATION = prove
 (`!a s x. connected_component (IMAGE (\x. a + x) s) (a + x) =
                IMAGE (\x. a + x) (connected_component s x)`,
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [CONNECTED_COMPONENT_TRANSLATION];;

let CONNECTED_COMPONENT_LINEAR_IMAGE = prove
 (`!f s x. linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
           ==> connected_component (IMAGE f s) (f x) =
               IMAGE f (connected_component s x)`,
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN
  GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [CONNECTED_COMPONENT_LINEAR_IMAGE];;

let UNIONS_CONNECTED_COMPONENT = prove
 (`!s:real^N->bool. UNIONS {connected_component s x |x| x IN s} = s`,
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; CONNECTED_COMPONENT_SUBSET] THEN
  REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ]);;

let COMPLEMENT_CONNECTED_COMPONENT_UNIONS = prove
 (`!s x:real^N.
     s DIFF connected_component s x =
     UNIONS({connected_component s y | y | y IN s} DELETE
            (connected_component s x))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
    [GSYM UNIONS_CONNECTED_COMPONENT] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s DELETE a ==> DISJOINT a x)
     ==> UNIONS s DIFF a = UNIONS (s DELETE a)`) THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC; IN_DELETE] THEN
  SIMP_TAC[CONNECTED_COMPONENT_DISJOINT; CONNECTED_COMPONENT_EQ_EQ] THEN
  MESON_TAC[IN; SUBSET; CONNECTED_COMPONENT_SUBSET]);;

let CLOSED_IN_CONNECTED_COMPONENT = prove
 (`!s x:real^N. closed_in (subtopology euclidean s) (connected_component s x)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `connected_component s (x:real^N) = {}` THEN
  ASM_REWRITE_TAC[CLOSED_IN_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONNECTED_COMPONENT_EQ_EMPTY]) THEN
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  EXISTS_TAC `closure(connected_component s x):real^N->bool` THEN
  REWRITE_TAC[CLOSED_CLOSURE] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET_INTER; CONNECTED_COMPONENT_SUBSET; CLOSURE_SUBSET] THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN REWRITE_TAC[INTER_SUBSET] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ];
    MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
    EXISTS_TAC `connected_component s (x:real^N)` THEN
    REWRITE_TAC[INTER_SUBSET; CONNECTED_CONNECTED_COMPONENT;
                SUBSET_INTER; CONNECTED_COMPONENT_SUBSET; CLOSURE_SUBSET]]);;

let OPEN_IN_CONNECTED_COMPONENT = prove
 (`!s x:real^N.
        FINITE {connected_component s x |x| x IN s}
        ==> open_in (subtopology euclidean s) (connected_component s x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `connected_component s (x:real^N) =
        s DIFF (UNIONS {connected_component s y |y| y IN s} DIFF
                connected_component s x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_CONNECTED_COMPONENT] THEN
    MATCH_MP_TAC(SET_RULE `t SUBSET s ==> t = s DIFF (s DIFF t)`) THEN
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET];
    MATCH_MP_TAC OPEN_IN_DIFF THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
    REWRITE_TAC[UNIONS_DIFF] THEN
    MATCH_MP_TAC CLOSED_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `connected_component s y DIFF connected_component s x =
      connected_component s y \/
      connected_component s (y:real^N) DIFF connected_component s x = {}`
     (DISJ_CASES_THEN SUBST1_TAC)
    THENL
     [MATCH_MP_TAC(SET_RULE
       `(~(s INTER t = {}) ==> s = t) ==> s DIFF t = s \/ s DIFF t = {}`) THEN
      SIMP_TAC[CONNECTED_COMPONENT_OVERLAP];
      REWRITE_TAC[CLOSED_IN_CONNECTED_COMPONENT];
      REWRITE_TAC[CLOSED_IN_EMPTY]]]);;

let CONNECTED_COMPONENT_EQUIVALENCE_RELATION = prove
 (`!R s:real^N->bool.
        (!x y. R x y ==> R y x) /\
        (!x y z. R x y /\ R y z ==> R x z) /\
        (!a. a IN s
             ==> ?t. open_in (subtopology euclidean s) t /\ a IN t /\
                     !x. x IN t ==> R a x)
        ==> !a b. connected_component s a b ==> R a b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:real^N->real^N->bool`; `connected_component s (a:real^N)`]
    CONNECTED_EQUIVALENCE_RELATION) THEN
  ASM_REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN ANTS_TAC THENL
   [X_GEN_TAC `c:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N`) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[CONNECTED_COMPONENT_SUBSET; SUBSET]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t INTER connected_component s (a:real^N)` THEN
    ASM_SIMP_TAC[IN_INTER; OPEN_IN_OPEN] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`]
        CONNECTED_COMPONENT_SUBSET) THEN
    SET_TAC[];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
    ASM_MESON_TAC[CONNECTED_COMPONENT_IN]]);;

let CONNECTED_COMPONENT_INTERMEDIATE_SUBSET = prove
 (`!t u a:real^N.
        connected_component u a SUBSET t /\ t SUBSET u
        ==> connected_component t a = connected_component u a`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(a:real^N) IN u` THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_UNIQUE THEN
    ASM_REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONNECTED_COMPONENT_REFL; IN]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM SET_TAC[];
    ASM_MESON_TAC[CONNECTED_COMPONENT_EQ_EMPTY; SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* The set of connected components of a set.                                 *)
(* ------------------------------------------------------------------------- *)

let components = new_definition
  `components s = {connected_component s x | x | x:real^N IN s}`;;

let COMPONENTS_TRANSLATION = prove
 (`!a s. components(IMAGE (\x. a + x) s) =
   IMAGE (IMAGE (\x. a + x)) (components s)`,
  REWRITE_TAC[components] THEN GEOM_TRANSLATE_TAC[] THEN SET_TAC[]);;

add_translation_invariants [COMPONENTS_TRANSLATION];;

let COMPONENTS_LINEAR_IMAGE = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
           ==> components(IMAGE f s) = IMAGE (IMAGE f) (components s)`,
  REWRITE_TAC[components] THEN GEOM_TRANSFORM_TAC[] THEN SET_TAC[]);;

add_linear_invariants [COMPONENTS_LINEAR_IMAGE];;

let IN_COMPONENTS = prove
 (`!u:real^N->bool s. s IN components u
    <=> ?x. x IN u /\ s = connected_component u x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[components] THEN EQ_TAC
  THENL [SET_TAC[];STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `x:real^N IN u` THEN SET_TAC[]]);;

let UNIONS_COMPONENTS = prove
 (`!u:real^N->bool. u = UNIONS (components u)`,
  REWRITE_TAC[EXTENSION] THEN REPEAT GEN_TAC THEN EQ_TAC
  THENL[DISCH_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
  EXISTS_TAC `connected_component (u:real^N->bool) x` THEN CONJ_TAC THENL
  [REWRITE_TAC[components] THEN SET_TAC[ASSUME `x:real^N IN u`];
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN SUBGOAL_THEN
  `?s:real^N->bool. connected s /\ s SUBSET u /\ x IN s` MP_TAC
  THENL[EXISTS_TAC `{x:real^N}` THEN ASM_REWRITE_TAC[CONNECTED_SING] THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]; SET_TAC[]]];
  REWRITE_TAC[IN_UNIONS] THEN STRIP_TAC THEN
  MATCH_MP_TAC (SET_RULE `!x:real^N s u. x IN s /\ s SUBSET u ==> x IN u`) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN STRIP_ASSUME_TAC
  (MESON[IN_COMPONENTS;ASSUME `t:real^N->bool IN components u`]
  `?y. t:real^N->bool = connected_component u y`) THEN
   ASM_REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]]);;

let PAIRWISE_DISJOINT_COMPONENTS = prove
 (`!u:real^N->bool. pairwise DISJOINT (components u)`,
  GEN_TAC THEN REWRITE_TAC[pairwise;DISJOINT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN STRIP_TAC THEN
  ASSERT_TAC `(?a. s:real^N->bool = connected_component u a) /\
  ?b. t:real^N->bool = connected_component u b`
  THENL [ASM_MESON_TAC[IN_COMPONENTS];
  ASM_MESON_TAC[CONNECTED_COMPONENT_NONOVERLAP]]);;

let IN_COMPONENTS_NONEMPTY = prove
 (`!s c. c IN components s ==> ~(c = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[components; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_EQ_EMPTY]);;

let IN_COMPONENTS_SUBSET = prove
 (`!s c. c IN components s ==> c SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[components; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]);;

let IN_COMPONENTS_CONNECTED = prove
 (`!s c. c IN components s ==> connected c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[components; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT]);;

let IN_COMPONENTS_MAXIMAL = prove
 (`!s c:real^N->bool.
        c IN components s <=>
        ~(c = {}) /\ c SUBSET s /\ connected c /\
        !c'. ~(c' = {}) /\ c SUBSET c' /\ c' SUBSET s /\ connected c'
             ==> c' = c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[components; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_EQ_EMPTY; CONNECTED_COMPONENT_SUBSET;
                    CONNECTED_CONNECTED_COMPONENT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_MESON_TAC[CONNECTED_COMPONENT_REFL; IN; SUBSET];
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(GSYM CONNECTED_COMPONENT_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `c':real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[SET_RULE `c' SUBSET c <=> c' UNION c = c`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC CONNECTED_UNION THEN ASM SET_TAC[]]);;

let JOINABLE_COMPONENTS_EQ = prove
 (`!s t c1 c2.
        connected t /\ t SUBSET s /\
        c1 IN components s /\ c2 IN components s /\
        ~(c1 INTER t = {}) /\ ~(c2 INTER t = {})
        ==> c1 = c2`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; components; FORALL_IN_GSPEC] THEN
  MESON_TAC[JOINABLE_CONNECTED_COMPONENT_EQ]);;

let CLOSED_IN_COMPONENT = prove
 (`!s c:real^N->bool.
        c IN components s ==> closed_in (subtopology euclidean s) c`,
  REWRITE_TAC[components; FORALL_IN_GSPEC; CLOSED_IN_CONNECTED_COMPONENT]);;

let CLOSED_COMPONENTS = prove
 (`!s c. closed s /\ c IN components s ==> closed c`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; components; FORALL_IN_GSPEC] THEN
  SIMP_TAC[CLOSED_CONNECTED_COMPONENT]);;

let COMPACT_COMPONENTS = prove
 (`!s c:real^N->bool. compact s /\ c IN components s ==> compact c`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
  MESON_TAC[CLOSED_COMPONENTS; IN_COMPONENTS_SUBSET; BOUNDED_SUBSET]);;

let CONTINUOUS_ON_COMPONENTS_GEN = prove
 (`!f:real^M->real^N s.
        (!c. c IN components s
             ==> open_in (subtopology euclidean s) c /\ f continuous_on c)
        ==> f continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_OPEN_IN_PREIMAGE_EQ] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{x | x IN s /\ (f:real^M->real^N) x IN t} =
    UNIONS {{x | x IN c /\ f x IN t} | c IN components s}`
  SUBST1_TAC THENL
   [CONV_TAC(LAND_CONV(SUBS_CONV
     [ISPEC `s:real^M->bool` UNIONS_COMPONENTS])) THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_UNIONS] THEN SET_TAC[];
    MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    ASM_MESON_TAC[OPEN_IN_TRANS]]);;

let CONTINUOUS_ON_COMPONENTS_FINITE = prove
 (`!f:real^M->real^N s.
        FINITE(components s) /\
        (!c. c IN components s ==> f continuous_on c)
        ==> f continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_CLOSED_IN_PREIMAGE_EQ] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{x | x IN s /\ (f:real^M->real^N) x IN t} =
    UNIONS {{x | x IN c /\ f x IN t} | c IN components s}`
  SUBST1_TAC THENL
   [CONV_TAC(LAND_CONV(SUBS_CONV
     [ISPEC `s:real^M->bool` UNIONS_COMPONENTS])) THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_UNIONS] THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_UNIONS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[CLOSED_IN_TRANS; CLOSED_IN_COMPONENT]]);;

let COMPONENTS_NONOVERLAP = prove
 (`!s c c'. c IN components s /\ c' IN components s
            ==> (c INTER c' = {} <=> ~(c = c'))`,
  REWRITE_TAC[components; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CONNECTED_COMPONENT_NONOVERLAP]);;

let COMPONENTS_EQ = prove
 (`!s c c'. c IN components s /\ c' IN components s
            ==> (c = c' <=> ~(c INTER c' = {}))`,
  MESON_TAC[COMPONENTS_NONOVERLAP]);;

let COMPONENTS_EQ_EMPTY = prove
 (`!s. components s = {} <=> s = {}`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[components; connected_component; IN_ELIM_THM] THEN
  SET_TAC[]);;

let COMPONENTS_EMPTY = prove
 (`components {} = {}`,
  REWRITE_TAC[COMPONENTS_EQ_EMPTY]);;

let CONNECTED_EQ_CONNECTED_COMPONENTS_EQ = prove
 (`!s. connected s <=>
       !c c'. c IN components s /\ c' IN components s ==> c = c'`,
  REWRITE_TAC[components; IN_ELIM_THM] THEN
  MESON_TAC[CONNECTED_EQ_CONNECTED_COMPONENT_EQ]);;

let COMPONENTS_EQ_SING,COMPONENTS_EQ_SING_EXISTS = (CONJ_PAIR o prove)
 (`(!s:real^N->bool. components s = {s} <=> connected s /\ ~(s = {})) /\
   (!s:real^N->bool. (?a. components s = {a}) <=> connected s /\ ~(s = {}))`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `s:real^N->bool` THEN
  MATCH_MP_TAC(TAUT `(p ==> q) /\ (q ==> r) /\ (r ==> p)
                     ==> (p <=> r) /\ (q <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[CONNECTED_EQ_CONNECTED_COMPONENTS_EQ] THEN
    ASM_MESON_TAC[IN_SING; COMPONENTS_EQ_EMPTY; NOT_INSERT_EMPTY];
    STRIP_TAC THEN ONCE_REWRITE_TAC[EXTENSION] THEN
    REWRITE_TAC[IN_SING] THEN
    REWRITE_TAC[components; IN_ELIM_THM] THEN
    ASM_MESON_TAC[CONNECTED_CONNECTED_COMPONENT_SET; MEMBER_NOT_EMPTY]]);;

let CONNECTED_EQ_COMPONENTS_SUBSET_SING = prove
 (`!s:real^N->bool. connected s <=> components s SUBSET {s}`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[COMPONENTS_EMPTY; CONNECTED_EMPTY; EMPTY_SUBSET] THEN
  REWRITE_TAC[SET_RULE `s SUBSET {a} <=> s = {} \/ s = {a}`] THEN
  ASM_REWRITE_TAC[COMPONENTS_EQ_EMPTY; COMPONENTS_EQ_SING]);;

let CONNECTED_EQ_COMPONENTS_SUBSET_SING_EXISTS = prove
 (`!s:real^N->bool. connected s <=> ?a. components s SUBSET {a}`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[COMPONENTS_EMPTY; CONNECTED_EMPTY; EMPTY_SUBSET] THEN
  REWRITE_TAC[SET_RULE `s SUBSET {a} <=> s = {} \/ s = {a}`] THEN
  ASM_REWRITE_TAC[COMPONENTS_EQ_EMPTY; COMPONENTS_EQ_SING_EXISTS]);;

let IN_COMPONENTS_SELF = prove
 (`!s:real^N->bool. s IN components s <=> connected s /\ ~(s = {})`,
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_CONNECTED];
    SIMP_TAC[GSYM COMPONENTS_EQ_SING; IN_SING]]);;

let COMPONENTS_MAXIMAL = prove
 (`!s t c:real^N->bool.
     c IN components s /\ connected t /\ t SUBSET s /\ ~(c INTER t = {})
     ==> t SUBSET c`,
  REWRITE_TAC[IMP_CONJ; components; FORALL_IN_GSPEC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_INTER; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CONNECTED_COMPONENT_EQ) THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]);;

let COMPONENTS_UNIQUE = prove
 (`!s:real^N->bool k.
        UNIONS k = s /\
        (!c. c IN k
             ==> connected c /\ ~(c = {}) /\
                 !c'. connected c' /\ c SUBSET c' /\ c' SUBSET s ==> c' = c)
        ==> components s = k`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `c:real^N->bool` THEN REWRITE_TAC[IN_COMPONENTS] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_UNIONS] THEN ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `connected_component s (x:real^N) = c`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_UNIQUE THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `c':real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[SET_RULE `c' SUBSET c <=> c' UNION c = c`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION; ASM SET_TAC[]] THEN
    ASM SET_TAC[];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; CONV_TAC SYM_CONV] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT; CONNECTED_COMPONENT_SUBSET] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let COMPONENTS_UNIQUE_EQ = prove
 (`!s:real^N->bool k.
        components s = k <=>
        UNIONS k = s /\
        (!c. c IN k
             ==> connected c /\ ~(c = {}) /\
                 !c'. connected c' /\ c SUBSET c' /\ c' SUBSET s ==> c' = c)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM); REWRITE_TAC[COMPONENTS_UNIQUE]] THEN
  REWRITE_TAC[GSYM UNIONS_COMPONENTS] THEN
  X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
    ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
    RULE_ASSUM_TAC(REWRITE_RULE[IN_COMPONENTS_MAXIMAL]) THEN
    ASM_MESON_TAC[SUBSET_EMPTY]]);;

let EXISTS_COMPONENT_SUPERSET = prove
 (`!s t:real^N->bool.
        t SUBSET s /\ ~(s = {}) /\ connected t
        ==> ?c. c IN components s /\ t SUBSET c`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
    ASM_MESON_TAC[COMPONENTS_EQ_EMPTY; MEMBER_NOT_EMPTY];
    FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^N` o
      GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    EXISTS_TAC `connected_component s (a:real^N)` THEN
    REWRITE_TAC[IN_COMPONENTS] THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[CONNECTED_COMPONENT_MAXIMAL]]]);;

let COMPONENTS_INTERMEDIATE_SUBSET = prove
 (`!s t u:real^N->bool.
        s IN components u /\ s SUBSET t /\ t SUBSET u
        ==> s IN components t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_COMPONENTS; LEFT_AND_EXISTS_THM] THEN
  MESON_TAC[CONNECTED_COMPONENT_INTERMEDIATE_SUBSET; SUBSET;
            CONNECTED_COMPONENT_REFL; IN; CONNECTED_COMPONENT_SUBSET]);;

let IN_COMPONENTS_UNIONS_COMPLEMENT = prove
 (`!s c:real^N->bool.
        c IN components s
        ==> s DIFF c = UNIONS(components s DELETE c)`,
  REWRITE_TAC[components; FORALL_IN_GSPEC;
              COMPLEMENT_CONNECTED_COMPONENT_UNIONS]);;

let CONNECTED_SUBSET_CLOPEN = prove
 (`!u s c:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) s /\
        connected c /\ c SUBSET u /\ ~(c INTER s = {})
        ==> c SUBSET s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED_IN]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o
    SPECL [`c INTER s:real^N->bool`; `c DIFF s:real^N->bool`]) THEN
  ASM_REWRITE_TAC[CONJ_ASSOC; SET_RULE `c DIFF s = {} <=> c SUBSET s`] THEN
  MATCH_MP_TAC(TAUT `p ==> ~(p /\ ~q) ==> q`) THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]]) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSED_IN_CLOSED]);
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN])] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[OPEN_IN_OPEN; CLOSED_IN_CLOSED] THENL
   [EXISTS_TAC `t:real^N->bool`; EXISTS_TAC `(:real^N) DIFF t`] THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ASM SET_TAC[]);;

let CLOPEN_UNIONS_COMPONENTS = prove
 (`!u s:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) s
        ==> ?k. k SUBSET components u /\ s = UNIONS k`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `{c:real^N->bool | c IN components u /\ ~(c INTER s = {})}` THEN
  REWRITE_TAC[SUBSET_RESTRICT] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `u:real^N->bool` UNIONS_COMPONENTS) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN SET_TAC[];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
    EXISTS_TAC `u:real^N->bool` THEN
    ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_SUBSET]]);;

let CLOPEN_IN_COMPONENTS = prove
 (`!u s:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) s /\
        connected s /\ ~(s = {})
        ==> s IN components u`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLOPEN_UNIONS_COMPONENTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `k:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^N->bool`) THEN
  ASM_CASES_TAC `k = {c:real^N->bool}` THENL
   [ASM_MESON_TAC[UNIONS_1; GSYM SING_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~p ==> p /\ q ==> r`) THEN
  SUBGOAL_THEN `?c':real^N->bool. c' IN k /\ ~(c = c')` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SET_RULE
     `a IN s /\ ~(s = {a}) ==> ?b. b IN s /\ ~(b = a)`];
    REWRITE_TAC[CONNECTED_EQ_CONNECTED_COMPONENTS_EQ] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:real^N->bool`; `c':real^N->bool`]) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THEN
    MATCH_MP_TAC COMPONENTS_INTERMEDIATE_SUBSET THEN
    EXISTS_TAC `u:real^N->bool` THEN
    MP_TAC(ISPEC `u:real^N->bool` UNIONS_COMPONENTS) THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Continuity implies uniform continuity on a compact domain.                *)
(* ------------------------------------------------------------------------- *)

let COMPACT_UNIFORMLY_EQUICONTINUOUS = prove
 (`!(fs:(real^M->real^N)->bool) s.
     (!x e. x IN s /\ &0 < e
            ==> ?d. &0 < d /\
                    (!f x'. f IN fs /\ x' IN s /\ dist (x',x) < d
                            ==> dist (f x',f x) < e)) /\
     compact s
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !f x x'. f IN fs /\ x IN s /\ x' IN s /\ dist (x',x) < d
                              ==> dist(f x',f x) < e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:real^M->real->real` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP HEINE_BOREL_LEMMA) THEN
  DISCH_THEN(MP_TAC o SPEC
    `{ ball(x:real^M,d x (e / &2)) | x IN s}`) THEN
  SIMP_TAC[FORALL_IN_GSPEC; OPEN_BALL; UNIONS_GSPEC; SUBSET; IN_ELIM_THM] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CENTRE_IN_BALL; REAL_HALF]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`f:real^M->real^N`; `u:real^M`; `v:real^M`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `v:real^M` th) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CHOOSE_THEN MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `u:real^M` th) THEN MP_TAC(SPEC `v:real^M` th)) THEN
  ASM_REWRITE_TAC[DIST_REFL] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^M` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[IN_BALL] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^M`; `e / &2`]) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(MP_TAC o SPEC `f:real^M->real^N` o CONJUNCT2) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `u:real^M` th) THEN
                        MP_TAC(SPEC `v:real^M` th)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NORM_ARITH);;

let COMPACT_UNIFORMLY_CONTINUOUS = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ compact s ==> f uniformly_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_on; uniformly_continuous_on] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`{f:real^M->real^N}`; `s:real^M->bool`]
        COMPACT_UNIFORMLY_EQUICONTINUOUS) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; IN_SING; FORALL_UNWIND_THM2] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A uniformly convergent limit of continuous functions is continuous.       *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_UNIFORM_LIMIT = prove
 (`!net f:A->real^M->real^N g s.
        ~(trivial_limit net) /\
        eventually (\n. (f n) continuous_on s) net /\
        (!e. &0 < e
             ==> eventually (\n. !x. x IN s ==> norm(f n x - g x) < e) net)
        ==> g continuous_on s`,
  REWRITE_TAC[continuous_on] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[IMP_IMP] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM EVENTUALLY_AND]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP EVENTUALLY_HAPPENS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `a:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `x:real^M`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:real^M` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
   MP_TAC(SPEC `x:real^M` th) THEN MP_TAC(SPEC `y:real^M` th)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `w <= x + y + z
    ==> x < e / &3 ==> y < e / &3 ==> z < e / &3 ==> w < e`) THEN
  REWRITE_TAC[dist] THEN
  SUBST1_TAC(VECTOR_ARITH
   `(g:real^M->real^N) y - g x =
    --(f (a:A) y - g y) + (f a x - g x) + (f a y - f a x)`) THEN
  MATCH_MP_TAC NORM_TRIANGLE_LE THEN REWRITE_TAC[NORM_NEG; REAL_LE_LADD] THEN
  MATCH_MP_TAC NORM_TRIANGLE_LE THEN REWRITE_TAC[NORM_NEG; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Topological stuff lifted from and dropped to R                            *)
(* ------------------------------------------------------------------------- *)

let OPEN_LIFT = prove
 (`!s. open(IMAGE lift s) <=>
        !x. x IN s ==> ?e. &0 < e /\ !x'. abs(x' - x) < e ==> x' IN s`,
  REWRITE_TAC[open_def; FORALL_LIFT; LIFT_IN_IMAGE_LIFT; DIST_LIFT]);;

let LIMPT_APPROACHABLE_LIFT = prove
 (`!x s. (lift x) limit_point_of (IMAGE lift s) <=>
         !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ abs(x' - x) < e`,
  REWRITE_TAC[LIMPT_APPROACHABLE; EXISTS_LIFT; LIFT_IN_IMAGE_LIFT;
              LIFT_EQ; DIST_LIFT]);;

let CLOSED_LIFT = prove
 (`!s. closed (IMAGE lift s) <=>
        !x. (!e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ abs(x' - x) < e)
            ==> x IN s`,
  GEN_TAC THEN REWRITE_TAC[CLOSED_LIMPT; LIMPT_APPROACHABLE] THEN
  ONCE_REWRITE_TAC[FORALL_LIFT] THEN
  REWRITE_TAC[LIMPT_APPROACHABLE_LIFT; LIFT_EQ; DIST_LIFT;
              EXISTS_LIFT; LIFT_IN_IMAGE_LIFT]);;

let CONTINUOUS_AT_LIFT_RANGE = prove
 (`!f x. (lift o f) continuous (at x) <=>
                !e. &0 < e
                    ==> ?d. &0 < d /\
                            (!x'. norm(x' - x) < d
                                  ==> abs(f x' - f x) < e)`,
  REWRITE_TAC[continuous_at; o_THM; DIST_LIFT] THEN REWRITE_TAC[dist]);;

let CONTINUOUS_ON_LIFT_RANGE = prove
 (`!f s. (lift o f) continuous_on s <=>
         !x. x IN s
             ==> !e. &0 < e
                     ==> ?d. &0 < d /\
                             (!x'. x' IN s /\ norm(x' - x) < d
                                   ==> abs(f x' - f x) < e)`,
  REWRITE_TAC[continuous_on; o_THM; DIST_LIFT] THEN REWRITE_TAC[dist]);;

let CONTINUOUS_LIFT_NORM_COMPOSE = prove
 (`!net f:A->real^N.
        f continuous net
        ==> (\x. lift(norm(f x))) continuous net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous; tendsto] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
  NORM_ARITH_TAC);;

let CONTINUOUS_ON_LIFT_NORM_COMPOSE = prove
 (`!f:real^M->real^N s.
        f continuous_on s
        ==> (\x. lift(norm(f x))) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_LIFT_NORM_COMPOSE]);;

let CONTINUOUS_AT_LIFT_NORM = prove
 (`!x. (lift o norm) continuous (at x)`,
  REWRITE_TAC[CONTINUOUS_AT_LIFT_RANGE; NORM_LIFT] THEN
  MESON_TAC[REAL_ABS_SUB_NORM; REAL_LET_TRANS]);;

let CONTINUOUS_ON_LIFT_NORM = prove
 (`!s. (lift o norm) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_LIFT_RANGE; NORM_LIFT] THEN
  MESON_TAC[REAL_ABS_SUB_NORM; REAL_LET_TRANS]);;

let CONTINUOUS_AT_LIFT_COMPONENT = prove
 (`!i a. 1 <= i /\ i <= dimindex(:N)
         ==> (\x:real^N. lift(x$i)) continuous (at a)`,
  SIMP_TAC[continuous_at; DIST_LIFT; GSYM VECTOR_SUB_COMPONENT] THEN
  MESON_TAC[dist; REAL_LET_TRANS; COMPONENT_LE_NORM]);;

let CONTINUOUS_ON_LIFT_COMPONENT = prove
 (`!i s. 1 <= i /\ i <= dimindex(:N)
         ==> (\x:real^N. lift(x$i)) continuous_on s`,
  SIMP_TAC[continuous_on; DIST_LIFT; GSYM VECTOR_SUB_COMPONENT] THEN
  MESON_TAC[dist; REAL_LET_TRANS; COMPONENT_LE_NORM]);;

let CONTINUOUS_AT_LIFT_INFNORM = prove
 (`!x:real^N. (lift o infnorm) continuous (at x)`,
  REWRITE_TAC[CONTINUOUS_AT; LIM_AT; o_THM; DIST_LIFT] THEN
  MESON_TAC[REAL_LET_TRANS; dist; REAL_ABS_SUB_INFNORM; INFNORM_LE_NORM]);;

let CONTINUOUS_AT_LIFT_DIST = prove
 (`!a:real^N x. (lift o (\x. dist(a,x))) continuous (at x)`,
  REWRITE_TAC[CONTINUOUS_AT_LIFT_RANGE] THEN
  MESON_TAC[NORM_ARITH `abs(dist(a:real^N,x) - dist(a,y)) <= norm(x - y)`;
            REAL_LET_TRANS]);;

let CONTINUOUS_ON_LIFT_DIST = prove
 (`!a s. (lift o (\x. dist(a,x))) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_LIFT_RANGE] THEN
  MESON_TAC[NORM_ARITH `abs(dist(a:real^N,x) - dist(a,y)) <= norm(x - y)`;
            REAL_LET_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Hence some handy theorems on distance, diameter etc. of/from a set.       *)
(* ------------------------------------------------------------------------- *)

let COMPACT_ATTAINS_SUP = prove
 (`!s. compact (IMAGE lift s) /\ ~(s = {})
       ==> ?x. x IN s /\ !y. y IN s ==> y <= x`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` BOUNDED_HAS_SUP) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `sup s` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CLOSED_LIFT; REAL_ARITH `s <= s - e <=> ~(&0 < e)`;
                REAL_ARITH `x <= s /\ ~(x <= s - e) ==> abs(x - s) < e`]);;

let COMPACT_ATTAINS_INF = prove
 (`!s. compact (IMAGE lift s) /\ ~(s = {})
       ==> ?x. x IN s /\ !y. y IN s ==> x <= y`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` BOUNDED_HAS_INF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `inf s` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CLOSED_LIFT; REAL_ARITH `s + e <= s <=> ~(&0 < e)`;
                REAL_ARITH `s <= x /\ ~(s + e <= x) ==> abs(x - s) < e`]);;

let CONTINUOUS_ATTAINS_SUP = prove
 (`!f:real^N->real s.
        compact s /\ ~(s = {}) /\ (lift o f) continuous_on s
        ==> ?x. x IN s /\ !y. y IN s ==> f(y) <= f(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE (f:real^N->real) s` COMPACT_ATTAINS_SUP) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; COMPACT_CONTINUOUS_IMAGE; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[IN_IMAGE]);;

let CONTINUOUS_ATTAINS_INF = prove
 (`!f:real^N->real s.
        compact s /\ ~(s = {}) /\ (lift o f) continuous_on s
        ==> ?x. x IN s /\ !y. y IN s ==> f(x) <= f(y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE (f:real^N->real) s` COMPACT_ATTAINS_INF) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; COMPACT_CONTINUOUS_IMAGE; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[IN_IMAGE]);;

let DISTANCE_ATTAINS_SUP = prove
 (`!s a. compact s /\ ~(s = {})
         ==> ?x. x IN s /\ !y. y IN s ==> dist(a,y) <= dist(a,x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ATTAINS_SUP THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_LIFT_RANGE] THEN REWRITE_TAC[dist] THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_ABS_SUB_NORM; NORM_NEG;
                VECTOR_ARITH `(a - x) - (a - y) = --(x - y):real^N`]);;

(* ------------------------------------------------------------------------- *)
(* For *minimal* distance, we only need closure, not compactness.            *)
(* ------------------------------------------------------------------------- *)

let DISTANCE_ATTAINS_INF = prove
 (`!s a:real^N.
        closed s /\ ~(s = {})
        ==> ?x. x IN s /\ !y. y IN s ==> dist(a,x) <= dist(a,y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real^N`) THEN
  MP_TAC(ISPECL [`\x:real^N. dist(a,x)`; `cball(a:real^N,dist(b,a)) INTER s`]
                CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_INTER; BOUNDED_INTER;
                 BOUNDED_CBALL; CLOSED_CBALL; GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[dist; CONTINUOUS_ON_LIFT_RANGE; IN_INTER; IN_CBALL] THEN
    ASM_MESON_TAC[REAL_LET_TRANS; REAL_ABS_SUB_NORM; NORM_NEG; REAL_LE_REFL;
            NORM_SUB; VECTOR_ARITH `(a - x) - (a - y) = --(x - y):real^N`];
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_INTER; IN_CBALL] THEN
    ASM_MESON_TAC[DIST_SYM; REAL_LE_TOTAL; REAL_LE_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* We can now extend limit compositions to consider the scalar multiplier.   *)
(* ------------------------------------------------------------------------- *)

let LIM_MUL = prove
 (`!net:(A)net f l:real^N c d.
        ((lift o c) --> lift d) net /\ (f --> l) net
        ==> ((\x. c(x) % f(x)) --> (d % l)) net`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`net:(A)net`; `\x (y:real^N). drop x % y`;
  `lift o (c:A->real)`; `f:A->real^N`; `lift d`; `l:real^N`] LIM_BILINEAR) THEN
  ASM_REWRITE_TAC[LIFT_DROP; o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[bilinear; linear; DROP_ADD; DROP_CMUL] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let LIM_VMUL = prove
 (`!net:(A)net c d v:real^N.
        ((lift o c) --> lift d) net ==> ((\x. c(x) % v) --> d % v) net`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_MUL THEN ASM_REWRITE_TAC[LIM_CONST]);;

let CONTINUOUS_VMUL = prove
 (`!net c v. (lift o c) continuous net ==> (\x. c(x) % v) continuous net`,
  REWRITE_TAC[continuous; LIM_VMUL; o_THM]);;

let CONTINUOUS_MUL = prove
 (`!net f c. (lift o c) continuous net /\ f continuous net
             ==> (\x. c(x) % f(x)) continuous net`,
  REWRITE_TAC[continuous; LIM_MUL; o_THM]);;

let CONTINUOUS_ON_VMUL = prove
 (`!s c v. (lift o c) continuous_on s ==> (\x. c(x) % v) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  SIMP_TAC[CONTINUOUS_VMUL]);;

let CONTINUOUS_ON_MUL = prove
 (`!s c f. (lift o c) continuous_on s /\ f continuous_on s
           ==> (\x. c(x) % f(x)) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  SIMP_TAC[CONTINUOUS_MUL]);;

let CONTINUOUS_LIFT_POW = prove
 (`!net f:A->real n.
        (\x. lift(f x)) continuous net
        ==> (\x. lift(f x pow n)) continuous net`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[LIFT_CMUL; real_pow; CONTINUOUS_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN ASM_REWRITE_TAC[o_DEF]);;

let CONTINUOUS_ON_LIFT_POW = prove
 (`!f:real^N->real s n.
        (\x. lift(f x)) continuous_on s
        ==> (\x. lift(f x pow n)) continuous_on s`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[LIFT_CMUL; real_pow; CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF]);;

let CONTINUOUS_LIFT_PRODUCT = prove
 (`!net:(A)net f (t:B->bool).
        FINITE t /\
        (!i. i IN t ==> (\x. lift(f x i)) continuous net)
        ==> (\x. lift(product t (f x))) continuous net`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC[PRODUCT_CLAUSES] THEN
  REWRITE_TAC[CONTINUOUS_CONST; LIFT_CMUL; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
  ASM_SIMP_TAC[o_DEF]);;

let CONTINUOUS_ON_LIFT_PRODUCT = prove
 (`!f:real^N->A->real s t.
        FINITE t /\

        (!i. i IN t ==> (\x. lift(f x i)) continuous_on s)
        ==> (\x. lift(product t (f x))) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_LIFT_PRODUCT]);;

(* ------------------------------------------------------------------------- *)
(* And so we have continuity of inverse.                                     *)
(* ------------------------------------------------------------------------- *)

let LIM_INV = prove
 (`!net:(A)net f l.
        ((lift o f) --> lift l) net /\ ~(l = &0)
        ==> ((lift o inv o f) --> lift(inv l)) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  ASM_CASES_TAC `trivial_limit(net:(A)net)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM; DIST_LIFT] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (abs(l) / &2) ((l pow 2 * e) / &2)`) THEN
  REWRITE_TAC[REAL_LT_MIN] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_ABS_NZ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; GSYM REAL_ABS_NZ; REAL_POW_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `b:A` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `abs(x - l) * &2 < abs l ==> ~(x = &0)`)) THEN
  ASM_SIMP_TAC[REAL_SUB_INV; REAL_ABS_DIV; REAL_LT_LDIV_EQ;
               GSYM REAL_ABS_NZ; REAL_ENTIRE] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs(x - y) * &2 < b * c ==> c * b <= d * &2 ==> abs(y - x) < d`)) THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_LE_LMUL_EQ] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_POW_2; REAL_MUL_ASSOC; GSYM REAL_ABS_NZ;
               REAL_LE_RMUL_EQ] THEN
  ASM_SIMP_TAC[REAL_ARITH `abs(x - y) * &2 < abs y ==> abs y <= &2 * abs x`]);;

let CONTINUOUS_INV = prove
 (`!net f. (lift o f) continuous net /\ ~(f(netlimit net) = &0)
           ==> (lift o inv o f) continuous net`,
  REWRITE_TAC[continuous; LIM_INV; o_THM]);;

let CONTINUOUS_AT_WITHIN_INV = prove
 (`!f s a:real^N.
        (lift o f) continuous (at a within s) /\ ~(f a = &0)
        ==> (lift o inv o f) continuous (at a within s)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `trivial_limit (at (a:real^N) within s)` THENL
   [ASM_REWRITE_TAC[continuous; LIM];
    ASM_SIMP_TAC[NETLIMIT_WITHIN; CONTINUOUS_INV]]);;

let CONTINUOUS_AT_INV = prove
 (`!f a. (lift o f) continuous at a /\ ~(f a = &0)
         ==> (lift o inv o f) continuous at a`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_AT_WITHIN_INV]);;

let CONTINUOUS_ON_INV = prove
 (`!f s. (lift o f) continuous_on s /\ (!x. x IN s ==> ~(f x = &0))
         ==> (lift o inv o f) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_AT_WITHIN_INV]);;

(* ------------------------------------------------------------------------- *)
(* More preservation properties for pasted sets (Cartesian products).        *)
(* ------------------------------------------------------------------------- *)

let LIM_PASTECART = prove
 (`!net f:A->real^M g:A->real^N.
        (f --> a) net /\ (g --> b) net
        ==> ((\x. pastecart (f x) (g x)) --> pastecart a b) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  ASM_CASES_TAC `trivial_limit(net:(A)net)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NET_DILEMMA) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  REWRITE_TAC[dist; PASTECART_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH
    `z <= x + y ==> x < e / &2 /\ y < e / &2 ==> z < e`) THEN
  REWRITE_TAC[NORM_PASTECART_LE]);;

let LIM_PASTECART_EQ = prove
 (`!net f:A->real^M g:A->real^N.
        ((\x. pastecart (f x) (g x)) --> pastecart a b) net <=>
        (f --> a) net /\ (g --> b) net`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[LIM_PASTECART] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o ISPEC `fstcart:real^(M,N)finite_sum->real^M` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ] LIM_LINEAR)) THEN
    REWRITE_TAC[LINEAR_FSTCART; FSTCART_PASTECART; ETA_AX];
    FIRST_ASSUM(MP_TAC o ISPEC `sndcart:real^(M,N)finite_sum->real^N` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ] LIM_LINEAR)) THEN
    REWRITE_TAC[LINEAR_SNDCART; SNDCART_PASTECART; ETA_AX]]);;

let CONTINUOUS_PASTECART = prove
 (`!net f:A->real^M g:A->real^N.
        f continuous net /\ g continuous net
        ==> (\x. pastecart (f x) (g x)) continuous net`,
  REWRITE_TAC[continuous; LIM_PASTECART]);;

let CONTINUOUS_ON_PASTECART = prove
 (`!f:real^M->real^N g:real^M->real^P s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. pastecart (f x) (g x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON; LIM_PASTECART]);;

let CONNECTED_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        connected s /\ connected t
        ==> connected (s PCROSS t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PCROSS; CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  DISCH_TAC THEN REWRITE_TAC[FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
  MAP_EVERY X_GEN_TAC [`x1:real^M`; `y1:real^N`; `x2:real^M`; `y2:real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(CONJUNCTS_THEN2
   (MP_TAC o SPECL [`x1:real^M`; `x2:real^M`])
   (MP_TAC o SPECL [`y1:real^N`; `y2:real^N`])) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; connected_component] THEN
  X_GEN_TAC `c2:real^N->bool` THEN STRIP_TAC THEN
  X_GEN_TAC `c1:real^M->bool` THEN STRIP_TAC THEN
  EXISTS_TAC
   `IMAGE (\x:real^M. pastecart x y1) c1 UNION
    IMAGE (\y:real^N. pastecart x2 y) c2` THEN
  REWRITE_TAC[IN_UNION] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN
    ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE; CONTINUOUS_ON_PASTECART;
                 CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; EXISTS_IN_IMAGE] THEN
    EXISTS_TAC `x2:real^M` THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; IN_UNION; FORALL_AND_THM; FORALL_IN_IMAGE;
                TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let CONNECTED_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        connected (s PCROSS t) <=>
        s = {} \/ t = {} \/ connected s /\ connected t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[PCROSS_EMPTY; CONNECTED_EMPTY] THEN
  EQ_TAC THEN SIMP_TAC[CONNECTED_PCROSS] THEN
  REWRITE_TAC[PCROSS] THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `connected (IMAGE fstcart
                     {pastecart (x:real^M) (y:real^N) | x IN s /\ y IN t})`
    MP_TAC THENL [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE; ALL_TAC];
    SUBGOAL_THEN `connected (IMAGE sndcart
                     {pastecart (x:real^M) (y:real^N) | x IN s /\ y IN t})`
    MP_TAC THENL [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE; ALL_TAC]] THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; IN_ELIM_PASTECART_THM;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let CLOSURE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        closure (s PCROSS t) = (closure s) PCROSS (closure t)`,
  REWRITE_TAC[EXTENSION; PCROSS; FORALL_PASTECART] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE; EXISTS_PASTECART; FORALL_PASTECART] THEN
  REWRITE_TAC[IN_ELIM_PASTECART_THM; PASTECART_INJ] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[dist; PASTECART_SUB] THEN EQ_TAC THENL
   [MESON_TAC[NORM_LE_PASTECART; REAL_LET_TRANS]; DISCH_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (MP_TAC o SPEC `e / &2`)) THEN
  ASM_MESON_TAC[REAL_HALF; NORM_PASTECART_LE; REAL_ARITH
    `z <= x + y /\ x < e / &2 /\ y < e / &2 ==> z < e`]);;

let LIMPT_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool x y.
        x limit_point_of s /\ y limit_point_of t
        ==> (pastecart x y) limit_point_of (s PCROSS t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PCROSS; LIMPT_APPROACHABLE; EXISTS_PASTECART] THEN
  REWRITE_TAC[IN_ELIM_PASTECART_THM; PASTECART_INJ; dist; PASTECART_SUB] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (MP_TAC o SPEC `e / &2`)) THEN
  ASM_MESON_TAC[REAL_HALF; NORM_PASTECART_LE; REAL_ARITH
    `z <= x + y /\ x < e / &2 /\ y < e / &2 ==> z < e`]);;

let CLOSED_IN_PCROSS = prove
 (`!s:real^M->bool s' t:real^N->bool t'.
        closed_in (subtopology euclidean s) s' /\
        closed_in (subtopology euclidean t) t'
        ==> closed_in (subtopology euclidean (s PCROSS t)) (s' PCROSS t')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s'':real^M->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `t'':real^N->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(s'':real^M->bool) PCROSS (t'':real^N->bool)` THEN
  ASM_SIMP_TAC[CLOSED_PCROSS; EXTENSION; FORALL_PASTECART] THEN
  REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS] THEN ASM SET_TAC[]);;

let CLOSED_IN_PCROSS_EQ = prove
 (`!s s':real^M->bool t t':real^N->bool.
        closed_in (subtopology euclidean (s PCROSS t)) (s' PCROSS t') <=>
        s' = {} \/ t' = {} \/
        closed_in (subtopology euclidean s) s' /\
        closed_in (subtopology euclidean t) t'`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s':real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CLOSED_IN_EMPTY] THEN
  ASM_CASES_TAC `t':real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CLOSED_IN_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[CLOSED_IN_PCROSS] THEN
  ASM_REWRITE_TAC[CLOSED_IN_INTER_CLOSURE; CLOSURE_PCROSS; INTER_PCROSS;
                  PCROSS_EQ; PCROSS_EQ_EMPTY]);;

let FRONTIER_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        frontier(s PCROSS t) = frontier s PCROSS closure t UNION
                               closure s PCROSS frontier t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[frontier; CLOSURE_PCROSS; INTERIOR_PCROSS; PCROSS_DIFF] THEN
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_DIFF; IN_UNION;
              PASTECART_IN_PCROSS] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence some useful properties follow quite easily.                         *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_SCALING = prove
 (`!s:real^N->bool c. connected s ==> connected (IMAGE (\x. c % x) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let CONNECTED_NEGATIONS = prove
 (`!s:real^N->bool. connected s ==> connected (IMAGE (--) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let CONNECTED_SUMS = prove
 (`!s t:real^N->bool.
        connected s /\ connected t ==> connected {x + y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CONNECTED_PCROSS) THEN
  DISCH_THEN(MP_TAC o ISPEC
   `\z. (fstcart z + sndcart z:real^N)` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] CONNECTED_CONTINUOUS_IMAGE)) THEN
  SIMP_TAC[CONTINUOUS_ON_ADD; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART;
           LINEAR_SNDCART; PCROSS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PASTECART] THEN
  REWRITE_TAC[PASTECART_INJ; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MESON_TAC[]);;

let COMPACT_SCALING = prove
 (`!s:real^N->bool c. compact s ==> compact (IMAGE (\x. c % x) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let COMPACT_NEGATIONS = prove
 (`!s:real^N->bool. compact s ==> compact (IMAGE (--) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let COMPACT_SUMS = prove
 (`!s:real^N->bool t.
        compact s /\ compact t ==> compact {x + y | x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x + y | x IN s /\ y IN t} =
                IMAGE (\z. fstcart z + sndcart z :real^N) (s PCROSS t)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; PCROSS] THEN
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_FST_SND];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[COMPACT_PCROSS] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL; SNDCART_ADD;
              SNDCART_CMUL] THEN
  CONJ_TAC THEN VECTOR_ARITH_TAC);;

let COMPACT_DIFFERENCES = prove
 (`!s:real^N->bool t.
        compact s /\ compact t ==> compact {x - y | x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x - y | x:real^N IN s /\ y IN t} =
                {x + y | x IN s /\ y IN (IMAGE (--) t)}`
    (fun th -> ASM_SIMP_TAC[th; COMPACT_SUMS; COMPACT_NEGATIONS]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `(x:real^N = --y) <=> (y = --x)`] THEN
  SIMP_TAC[VECTOR_SUB; GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  MESON_TAC[VECTOR_NEG_NEG]);;

let COMPACT_AFFINITY = prove
 (`!s a:real^N c.
        compact s ==> compact (IMAGE (\x. a + c % x) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; COMPACT_TRANSLATION; COMPACT_SCALING]);;

(* ------------------------------------------------------------------------- *)
(* Hence we get the following.                                               *)
(* ------------------------------------------------------------------------- *)

let COMPACT_SUP_MAXDISTANCE = prove
 (`!s:real^N->bool.
        compact s /\ ~(s = {})
        ==> ?x y. x IN s /\ y IN s /\
                  !u v. u IN s /\ v IN s ==> norm(u - v) <= norm(x - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{x - y:real^N | x IN s /\ y IN s}`; `vec 0:real^N`]
                DISTANCE_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_DIFFERENCES] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    REWRITE_TAC[IN_ELIM_THM; dist; VECTOR_SUB_RZERO; VECTOR_SUB_LZERO;
                NORM_NEG] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* We can state this in terms of diameter of a set.                          *)
(* ------------------------------------------------------------------------- *)

let diameter = new_definition
  `diameter s =
        if s = {} then &0
        else sup {norm(x - y) | x IN s /\ y IN s}`;;

let DIAMETER_BOUNDED = prove
 (`!s. bounded s
       ==> (!x:real^N y. x IN s /\ y IN s ==> norm(x - y) <= diameter s) /\
           (!d. &0 <= d /\ d < diameter s
                ==> ?x y. x IN s /\ y IN s /\ norm(x - y) > d)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[diameter; NOT_IN_EMPTY; REAL_LET_ANTISYM] THEN
  MP_TAC(SPEC `{norm(x - y:real^N) | x IN s /\ y IN s}` SUP) THEN
  ABBREV_TAC `b = sup {norm(x - y:real^N) | x IN s /\ y IN s}` THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[NOT_IN_EMPTY; real_gt] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC];
    MESON_TAC[REAL_NOT_LE]] THEN
  SIMP_TAC[VECTOR_SUB; LEFT_IMP_EXISTS_THM] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
  MESON_TAC[REAL_ARITH `x <= y + z /\ y <= b /\ z<= b ==> x <= b + b`;
            NORM_TRIANGLE; NORM_NEG]);;

let DIAMETER_BOUNDED_BOUND = prove
 (`!s x y. bounded s /\ x IN s /\ y IN s ==> norm(x - y) <= diameter s`,
  MESON_TAC[DIAMETER_BOUNDED]);;

let DIAMETER_COMPACT_ATTAINED = prove
 (`!s:real^N->bool.
        compact s /\ ~(s = {})
        ==> ?x y. x IN s /\ y IN s /\ (norm(x - y) = diameter s)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_SUP_MAXDISTANCE) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `s:real^N->bool` DIAMETER_BOUNDED) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPACT_EQ_BOUNDED_CLOSED]) THEN
  ASM_REWRITE_TAC[real_gt] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  ASM_MESON_TAC[NORM_POS_LE; REAL_NOT_LT]);;

let DIAMETER_TRANSLATION = prove
 (`!a s. diameter (IMAGE (\x. a + x) s) = diameter s`,
  REWRITE_TAC[diameter] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [DIAMETER_TRANSLATION];;

let DIAMETER_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x. norm(f x) = norm x)
        ==> diameter(IMAGE f s) = diameter s`,
  REWRITE_TAC[diameter] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[diameter; IMAGE_EQ_EMPTY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE] THEN
  ASM_MESON_TAC[LINEAR_SUB]);;

add_linear_invariants [DIAMETER_LINEAR_IMAGE];;

let DIAMETER_EMPTY = prove
 (`diameter {} = &0`,
  REWRITE_TAC[diameter]);;

let DIAMETER_SING = prove
 (`!a. diameter {a} = &0`,
  REWRITE_TAC[diameter; NOT_INSERT_EMPTY; IN_SING] THEN
  REWRITE_TAC[SET_RULE `{f x y | x = a /\ y = a} = {f a a }`] THEN
  REWRITE_TAC[SUP_SING; VECTOR_SUB_REFL; NORM_0]);;

let DIAMETER_POS_LE = prove
 (`!s:real^N->bool. bounded s ==> &0 <= diameter s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diameter] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MP_TAC(SPEC `{norm(x - y:real^N) | x IN s /\ y IN s}` SUP) THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `B:real` o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
    EXISTS_TAC `&2 * B` THEN
    ASM_SIMP_TAC[NORM_ARITH
      `norm x <= B /\ norm y <= B ==> norm(x - y) <= &2 * B`];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `a:real^N`] o CONJUNCT1) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0]]);;

let DIAMETER_SUBSET = prove
 (`!s t:real^N->bool. s SUBSET t /\ bounded t ==> diameter s <= diameter t`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[DIAMETER_EMPTY; DIAMETER_POS_LE] THEN
  ASM_REWRITE_TAC[diameter] THEN
  COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `B:real` o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  EXISTS_TAC `&2 * B` THEN
  ASM_SIMP_TAC[NORM_ARITH
    `norm x <= B /\ norm y <= B ==> norm(x - y) <= &2 * B`]);;

let DIAMETER_CLOSURE = prove
 (`!s:real^N->bool. bounded s ==> diameter(closure s) = diameter s`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIAMETER_SUBSET; BOUNDED_CLOSURE; CLOSURE_SUBSET] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  DISCH_TAC THEN MP_TAC(ISPEC `closure s:real^N->bool` DIAMETER_BOUNDED) THEN
  ABBREV_TAC `d = diameter(closure s) - diameter(s:real^N->bool)` THEN
  ASM_SIMP_TAC[BOUNDED_CLOSURE] THEN DISCH_THEN(MP_TAC o
    SPEC `diameter(closure(s:real^N->bool)) - d / &2` o CONJUNCT2) THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; NOT_EXISTS_THM] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIAMETER_POS_LE) THEN
  REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE; CONJ_ASSOC; AND_FORALL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `d / &4`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < d / &4 <=> &0 < d`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u:real^N` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))
   (X_CHOOSE_THEN `v:real^N` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIAMETER_BOUNDED) THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^N`; `v:real^N`] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC);;

let DIAMETER_SUBSET_CBALL_NONEMPTY = prove
 (`!s:real^N->bool.
       bounded s /\ ~(s = {}) ==> ?z. z IN s /\ s SUBSET cball(z,diameter s)`,
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `b:real^N` THEN
   DISCH_TAC THEN REWRITE_TAC[IN_CBALL; dist] THEN
   ASM_MESON_TAC[DIAMETER_BOUNDED]);;

let DIAMETER_SUBSET_CBALL = prove
 (`!s:real^N->bool. bounded s ==> ?z. s SUBSET cball(z,diameter s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_MESON_TAC[DIAMETER_SUBSET_CBALL_NONEMPTY; EMPTY_SUBSET]);;

let DIAMETER_EQ_0 = prove
 (`!s:real^N->bool.
        bounded s ==> (diameter s = &0 <=> s = {} \/ ?a. s = {a})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[DIAMETER_EMPTY; DIAMETER_SING] THEN
  REWRITE_TAC[SET_RULE
   `s = {} \/ (?a. s = {a}) <=> !a b. a IN s /\ b IN s ==> a = b`] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `b:real^N`]
        DIAMETER_BOUNDED_BOUND) THEN
  ASM_REWRITE_TAC[] THEN NORM_ARITH_TAC);;

let DIAMETER_LE = prove
 (`!s:real^N->bool.
        (~(s = {}) \/ &0 <= d) /\
        (!x y. x IN s /\ y IN s ==> norm(x - y) <= d) ==> diameter s <= d`,
  GEN_TAC THEN REWRITE_TAC[diameter] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_LE THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[FORALL_IN_GSPEC]]);;

let DIAMETER_CBALL = prove
 (`!a:real^N r. diameter(cball(a,r)) = if r < &0 then &0 else &2 * r`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[CBALL_EQ_EMPTY; DIAMETER_EMPTY]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIAMETER_LE THEN
    ASM_SIMP_TAC[CBALL_EQ_EMPTY; REAL_LE_MUL; REAL_POS; REAL_NOT_LT] THEN
    REWRITE_TAC[IN_CBALL] THEN NORM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((a + r % basis 1) - (a - r % basis 1):real^N)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `(a + r % b) - (a - r % b:real^N) =
                                (&2 * r) % b`] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
      REWRITE_TAC[BOUNDED_CBALL; IN_CBALL] THEN
      REWRITE_TAC[NORM_ARITH
       `dist(a:real^N,a + b) = norm b /\ dist(a,a - b) = norm b`] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
      ASM_REAL_ARITH_TAC]]);;

let DIAMETER_BALL = prove
 (`!a:real^N r. diameter(ball(a,r)) = if r < &0 then &0 else &2 * r`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[BALL_EMPTY; REAL_LT_IMP_LE; DIAMETER_EMPTY]; ALL_TAC] THEN
  ASM_CASES_TAC `r = &0` THEN
  ASM_SIMP_TAC[BALL_EMPTY; REAL_LE_REFL; DIAMETER_EMPTY; REAL_MUL_RZERO] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `diameter(cball(a:real^N,r))` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CLOSURE_BALL; DIAMETER_CLOSURE; BOUNDED_BALL];
    ASM_SIMP_TAC[DIAMETER_CBALL]]);;

let DIAMETER_SUMS = prove
 (`!s t:real^N->bool.
        bounded s /\ bounded t
        ==> diameter {x + y | x IN s /\ y IN t} <= diameter s + diameter t`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; SET_RULE `{f x y |x,y| F} = {}`;
               DIAMETER_EMPTY; REAL_ADD_LID; DIAMETER_POS_LE] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; SET_RULE `{f x y |x,y| F} = {}`;
               DIAMETER_EMPTY; REAL_ADD_RID; DIAMETER_POS_LE] THEN
  MATCH_MP_TAC DIAMETER_LE THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_GSPEC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(NORM_ARITH
   `norm(x - x') <= s /\ norm(y - y') <= t
    ==> norm((x + y) - (x' + y'):real^N) <= s + t`) THEN
  ASM_SIMP_TAC[DIAMETER_BOUNDED_BOUND]);;

let LEBESGUE_COVERING_LEMMA = prove
 (`!s:real^N->bool c.
        compact s /\ ~(c = {}) /\ s SUBSET UNIONS c /\ (!b. b IN c ==> open b)
        ==> ?d. &0 < d /\
                !t. t SUBSET s /\ diameter t <= d
                    ==> ?b. b IN c /\ t SUBSET b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HEINE_BOREL_LEMMA) THEN
  DISCH_THEN(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN ASM_SIMP_TAC[] THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `t:real^N->bool` DIAMETER_SUBSET_CBALL_NONEMPTY) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `b:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `cball(x:real^N,diameter(t:real^N->bool))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `ball(x:real^N,e)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
  MAP_EVERY UNDISCH_TAC [`&0 < e`; `diameter(t:real^N->bool) <= e / &2`] THEN
  NORM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Related results with closure as the conclusion.                           *)
(* ------------------------------------------------------------------------- *)

let CLOSED_SCALING = prove
 (`!s:real^N->bool c. closed s ==> closed (IMAGE (\x. c % x) s)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s :real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY; IMAGE_CLAUSES] THEN
  ASM_CASES_TAC `c = &0` THENL
   [SUBGOAL_THEN `IMAGE (\x:real^N. c % x) s = {(vec 0)}`
     (fun th -> REWRITE_TAC[th; CLOSED_SING]) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SING; VECTOR_MUL_LZERO] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSED_SEQUENTIAL_LIMITS; IN_IMAGE; SKOLEM_THM] THEN
  STRIP_TAC THEN X_GEN_TAC `x:num->real^N` THEN X_GEN_TAC `l:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num->real^N` MP_TAC) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `inv(c) % l :real^N` THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `\n:num. inv(c) % x n:real^N` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID];
    MATCH_MP_TAC LIM_CMUL THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[SYM(SPEC_ALL th)]) THEN
    ASM_REWRITE_TAC[ETA_AX]]);;

let CLOSED_NEGATIONS = prove
 (`!s:real^N->bool. closed s ==> closed (IMAGE (--) s)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `IMAGE (--) s = IMAGE (\x:real^N. --(&1) % x) s`
  SUBST1_TAC THEN SIMP_TAC[CLOSED_SCALING] THEN
  REWRITE_TAC[VECTOR_ARITH `--(&1) % x = --x`] THEN REWRITE_TAC[ETA_AX]);;

let COMPACT_CLOSED_SUMS = prove
 (`!s:real^N->bool t.
        compact s /\ closed t ==> closed {x + y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[compact; IN_ELIM_THM; CLOSED_SEQUENTIAL_LIMITS] THEN
  STRIP_TAC THEN X_GEN_TAC `f:num->real^N` THEN X_GEN_TAC `l:real^N` THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num->real^N` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check(is_imp o concl) o SPEC `a:num->real^N`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `la:real^N` (X_CHOOSE_THEN `sub:num->num`
        STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`la:real^N`; `l - la:real^N`] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `a + (b - a) = b:real^N`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `\n. (f o (sub:num->num)) n - (a o sub) n:real^N` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[VECTOR_ADD_SUB; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LIM_SUB THEN ASM_SIMP_TAC[LIM_SUBSEQUENCE; ETA_AX]);;

let CLOSED_COMPACT_SUMS = prove
 (`!s:real^N->bool t.
        closed s /\ compact t ==> closed {x + y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x + y:real^N | x IN s /\ y IN t} = {y + x | y IN t /\ x IN s}`
  SUBST1_TAC THEN  SIMP_TAC[COMPACT_CLOSED_SUMS] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[VECTOR_ADD_SYM]);;

let CLOSURE_SUMS = prove
 (`!s t:real^N->bool.
        bounded s \/ bounded t
        ==> closure {x + y | x IN s /\ y IN t} =
            {x + y | x IN closure s /\ y IN closure t}`,
  REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SUMS_SYM] THEN
  MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN
  SIMP_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; CLOSURE_SEQUENTIAL] THEN
  X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_DELETE; SKOLEM_THM; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(p /\ q) /\ r <=> q /\ p /\ r`] THEN
    ONCE_REWRITE_TAC[MESON[] `(?f x y. P f x y) <=> (?x y f. P f x y)`] THEN
    ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
    REWRITE_TAC[ETA_AX; UNWIND_THM2] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:num->real^N`; `b:num->real^N`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPEC `closure s:real^N->bool` compact) THEN
    ASM_REWRITE_TAC[COMPACT_CLOSURE] THEN
    DISCH_THEN(MP_TAC o SPEC `a:num->real^N`) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `r:num->num`] THEN STRIP_TAC THEN
    EXISTS_TAC `z - u:real^N` THEN
    EXISTS_TAC `(a:num->real^N) o (r:num->num)` THEN EXISTS_TAC `u:real^N` THEN
    ASM_REWRITE_TAC[o_THM] THEN
    CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
    EXISTS_TAC `(\n. ((\n. a n + b n) o (r:num->num)) n - (a o r) n)
                :num->real^N` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[o_DEF; VECTOR_ARITH `(a + b) - a:real^N = b`];
      MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC LIM_SUBSEQUENCE THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM;
                RIGHT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`x:real^N`; `y:real^N`; `a:num->real^N`; `b:num->real^N`] THEN
    STRIP_TAC THEN EXISTS_TAC `(\n. a n + b n):num->real^N` THEN
    ASM_SIMP_TAC[LIM_ADD] THEN ASM_MESON_TAC[]]);;

let COMPACT_CLOSED_DIFFERENCES = prove
 (`!s:real^N->bool t.
        compact s /\ closed t ==> closed {x - y | x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x - y | x:real^N IN s /\ y IN t} =
                {x + y | x IN s /\ y IN (IMAGE (--) t)}`
    (fun th -> ASM_SIMP_TAC[th; COMPACT_CLOSED_SUMS; CLOSED_NEGATIONS]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `(x:real^N = --y) <=> (y = --x)`] THEN
  SIMP_TAC[VECTOR_SUB; GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  MESON_TAC[VECTOR_NEG_NEG]);;

let CLOSED_COMPACT_DIFFERENCES = prove
 (`!s:real^N->bool t.
        closed s /\ compact t ==> closed {x - y | x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x - y | x:real^N IN s /\ y IN t} =
                {x + y | x IN s /\ y IN (IMAGE (--) t)}`
    (fun th -> ASM_SIMP_TAC[th; CLOSED_COMPACT_SUMS; COMPACT_NEGATIONS]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `(x:real^N = --y) <=> (y = --x)`] THEN
  SIMP_TAC[VECTOR_SUB; GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  MESON_TAC[VECTOR_NEG_NEG]);;

let CLOSED_TRANSLATION_EQ = prove
 (`!a s. closed (IMAGE (\x:real^N. a + x) s) <=> closed s`,
  REWRITE_TAC[closed] THEN GEOM_TRANSLATE_TAC[]);;

let CLOSED_TRANSLATION = prove
 (`!s a:real^N. closed s ==> closed (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[CLOSED_TRANSLATION_EQ]);;

add_translation_invariants [CLOSED_TRANSLATION_EQ];;

let COMPLETE_TRANSLATION_EQ = prove
 (`!a s. complete(IMAGE (\x:real^N. a + x) s) <=> complete s`,
  REWRITE_TAC[COMPLETE_EQ_CLOSED; CLOSED_TRANSLATION_EQ]);;

add_translation_invariants [COMPLETE_TRANSLATION_EQ];;

let TRANSLATION_UNIV = prove
 (`!a. IMAGE (\x. a + x) (:real^N) = (:real^N)`,
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN GEOM_TRANSLATE_TAC[]);;

let TRANSLATION_DIFF = prove
 (`!s t:real^N->bool.
        IMAGE (\x. a + x) (s DIFF t) =
        (IMAGE (\x. a + x) s) DIFF (IMAGE (\x. a + x) t)`,
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^N = a + y <=> y = x - a`] THEN
  REWRITE_TAC[UNWIND_THM2]);;

let CLOSURE_TRANSLATION = prove
 (`!a s. closure(IMAGE (\x:real^N. a + x) s) = IMAGE (\x. a + x) (closure s)`,
  REWRITE_TAC[CLOSURE_INTERIOR] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [CLOSURE_TRANSLATION];;

let FRONTIER_TRANSLATION = prove
 (`!a s. frontier(IMAGE (\x:real^N. a + x) s) = IMAGE (\x. a + x) (frontier s)`,
  REWRITE_TAC[frontier] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [FRONTIER_TRANSLATION];;

(* ------------------------------------------------------------------------- *)
(* Separation between points and sets.                                       *)
(* ------------------------------------------------------------------------- *)

let SEPARATE_POINT_CLOSED = prove
 (`!s a:real^N.
        closed s /\ ~(a IN s)
        ==> ?d. &0 < d /\ !x. x IN s ==> d <= dist(a,x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`] DISTANCE_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `b:real^N` THEN
  STRIP_TAC THEN EXISTS_TAC `dist(a:real^N,b)` THEN
  ASM_MESON_TAC[DIST_POS_LT]);;

let SEPARATE_COMPACT_CLOSED = prove
 (`!s t:real^N->bool.
        compact s /\ closed t /\ s INTER t = {}
        ==> ?d. &0 < d /\ !x y. x IN s /\ y IN t ==> d <= dist(x,y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{x - y:real^N | x IN s /\ y IN t}`; `vec 0:real^N`]
                SEPARATE_POINT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_CLOSED_DIFFERENCES; IN_ELIM_THM] THEN
  REWRITE_TAC[VECTOR_ARITH `vec 0 = x - y <=> x = y`] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
  MESON_TAC[NORM_ARITH `dist(vec 0,x - y) = dist(x,y)`]);;

let SEPARATE_CLOSED_COMPACT = prove
 (`!s t:real^N->bool.
        closed s /\ compact t /\ s INTER t = {}
        ==> ?d. &0 < d /\ !x y. x IN s /\ y IN t ==> d <= dist(x,y)`,
  ONCE_REWRITE_TAC[DIST_SYM; INTER_COMM] THEN
  MESON_TAC[SEPARATE_COMPACT_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* Representing sets as the union of a chain of compact sets.                *)
(* ------------------------------------------------------------------------- *)

let CLOSED_UNION_COMPACT_SUBSETS = prove
 (`!s. closed s
       ==> ?f:num->real^N->bool.
                (!n. compact(f n)) /\
                (!n. (f n) SUBSET s) /\
                (!n. (f n) SUBSET f(n + 1)) /\
                UNIONS {f n | n IN (:num)} = s /\
                (!k. compact k /\ k SUBSET s
                     ==> ?N. !n. n >= N ==> k SUBSET (f n))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\n. s INTER cball(vec 0:real^N,&n)` THEN
  ASM_SIMP_TAC[INTER_SUBSET; COMPACT_CBALL; CLOSED_INTER_COMPACT] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(SET_RULE
     `t SUBSET u ==> s INTER t SUBSET s INTER u`) THEN
    REWRITE_TAC[SUBSET_BALLS; DIST_REFL; GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV; IN_INTER] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_CBALL_0] THEN
    MESON_TAC[REAL_ARCH_SIMPLE];
    X_GEN_TAC `k:real^N->bool` THEN SIMP_TAC[SUBSET_INTER] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN DISCH_THEN
     (MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_CBALL) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `r:real` REAL_ARCH_SIMPLE) THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_GE] THEN

    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SUBSET_TRANS)) THEN
    REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC]);;

let OPEN_UNION_COMPACT_SUBSETS = prove
 (`!s. open s
       ==> ?f:num->real^N->bool.
                (!n. compact(f n)) /\
                (!n. (f n) SUBSET s) /\
                (!n. (f n) SUBSET interior(f(n + 1))) /\
                UNIONS {f n | n IN (:num)} = s /\
                (!k. compact k /\ k SUBSET s
                     ==> ?N. !n. n >= N ==> k SUBSET (f n))`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [DISCH_TAC THEN EXISTS_TAC `(\n. {}):num->real^N->bool` THEN
    ASM_SIMP_TAC[EMPTY_SUBSET; SUBSET_EMPTY; COMPACT_EMPTY] THEN
    REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; NOT_IN_EMPTY];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN STRIP_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(!f. p1 f /\ p3 f /\ p4 f ==> p5 f) /\
    (?f. p1 f /\ p2 f /\ p3 f /\ (p2 f ==> p4 f))
    ==> ?f. p1 f /\ p2 f /\ p3 f /\ p4 f /\ p5 f`) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `f:num->real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
    DISCH_THEN(MP_TAC o SPEC `{interior(f n):real^N->bool | n IN (:num)}`) THEN
    REWRITE_TAC[FORALL_IN_GSPEC; OPEN_INTERIOR] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SUBSET_TRANS)) THEN
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN ASM SET_TAC[];
      ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
      REWRITE_TAC[SIMPLE_IMAGE; EXISTS_FINITE_SUBSET_IMAGE] THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num->bool` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o SPEC `\n:num. n` o
        MATCH_MP UPPER_BOUND_FINITE_SET) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      REWRITE_TAC[GE] THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SUBSET_TRANS)) THEN
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `(f:num->real^N->bool) m` THEN
      REWRITE_TAC[INTERIOR_SUBSET] THEN
      SUBGOAL_THEN `!m n. m <= n ==> (f:num->real^N->bool) m SUBSET f n`
       (fun th -> ASM_MESON_TAC[th; LE_TRANS]) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
      ASM_MESON_TAC[SUBSET; ADD1; INTERIOR_SUBSET]];
    EXISTS_TAC
     `\n. cball(a,&n) DIFF
         {x + e | x IN (:real^N) DIFF s /\ e IN ball(vec 0,inv(&n + &1))}` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC COMPACT_DIFF THEN
      SIMP_TAC[COMPACT_CBALL; OPEN_SUMS; OPEN_BALL];
      GEN_TAC THEN MATCH_MP_TAC(SET_RULE
       `(UNIV DIFF s) SUBSET t ==> c DIFF t SUBSET s`) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:real^N`; `vec 0:real^N`] THEN
      ASM_REWRITE_TAC[VECTOR_ADD_RID; CENTRE_IN_BALL; REAL_LT_INV_EQ] THEN
      REAL_ARITH_TAC;
      GEN_TAC THEN REWRITE_TAC[INTERIOR_DIFF] THEN MATCH_MP_TAC(SET_RULE
       `s SUBSET s' /\ t' SUBSET t ==> (s DIFF t) SUBSET (s' DIFF t')`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[INTERIOR_CBALL; SUBSET; IN_BALL; IN_CBALL] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `{x + e | x IN (:real^N) DIFF s /\
                             e IN cball(vec 0,inv(&n + &2))}` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CLOSURE_MINIMAL THEN
          ASM_SIMP_TAC[CLOSED_COMPACT_SUMS; COMPACT_CBALL;
                       GSYM OPEN_CLOSED] THEN
          MATCH_MP_TAC(SET_RULE
           `t SUBSET t'
            ==> {f x y | x IN s /\ y IN t} SUBSET
                {f x y | x IN s /\ y IN t'}`) THEN
          REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL; GSYM REAL_OF_NUM_ADD] THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC(SET_RULE
           `t SUBSET t'
            ==> {f x y | x IN s /\ y IN t} SUBSET
                {f x y | x IN s /\ y IN t'}`) THEN
          REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL; GSYM REAL_OF_NUM_ADD] THEN
          GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
           `a < b ==> x <= a ==> x < b`) THEN
          MATCH_MP_TAC REAL_LT_INV2 THEN REAL_ARITH_TAC]];
      DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
      ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_DIFF] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV; IN_BALL_0] THEN
      REWRITE_TAC[VECTOR_ARITH `x:real^N = y + e <=> e = x - y`] THEN
      REWRITE_TAC[TAUT `(p /\ q) /\ r <=> r /\ p /\ q`; UNWIND_THM2] THEN
      REWRITE_TAC[MESON[] `~(?x. ~P x /\ Q x) <=> !x. Q x ==> P x`] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[SUBSET; IN_BALL; dist] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
      DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPEC `norm(x - a:real^N)` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N1 + N2:num` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        UNDISCH_TAC `norm(x - a:real^N) <= &N2` THEN
        REWRITE_TAC[dist; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        SUBGOAL_THEN `inv(&(N1 + N2) + &1) <= inv(&N1)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN
          ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]]]]);;
