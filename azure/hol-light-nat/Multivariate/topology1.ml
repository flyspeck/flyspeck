(* ========================================================================= *)
(* Elementary topology in Euclidean space.                                   *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

open Hol_core
open Card
open Products
open Permutations
open Floor
open Vectors
open Determinants

(* ------------------------------------------------------------------------- *)
(* General notion of a topology.                                             *)
(* ------------------------------------------------------------------------- *)

let istopology = new_definition
 `istopology L <=>
        {} IN L /\
        (!s t. s IN L /\ t IN L ==> (s INTER t) IN L) /\
        (!k. k SUBSET L ==> (UNIONS k) IN L)`;;

let topology_tybij_th = prove
 (`?t:(A->bool)->bool. istopology t`,
  EXISTS_TAC `UNIV:(A->bool)->bool` THEN REWRITE_TAC[istopology; IN_UNIV]);;

let topology_tybij =
  new_type_definition "topology" ("topology","open_in") topology_tybij_th;;

let ISTOPOLOGY_OPEN_IN = prove
 (`istopology(open_in top)`,
  MESON_TAC[topology_tybij]);;

let TOPOLOGY_EQ = prove
 (`!top1 top2. top1 = top2 <=> !s. open_in top1 s <=> open_in top2 s`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[ETA_AX] THEN MESON_TAC[topology_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Infer the "universe" from union of all sets in the topology.              *)
(* ------------------------------------------------------------------------- *)

let topspace = new_definition
 `topspace top = UNIONS {s | open_in top s}`;;

(* ------------------------------------------------------------------------- *)
(* Main properties of open sets.                                             *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_CLAUSES = prove
 (`!top:(A)topology.
        open_in top {} /\
        (!s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)) /\
        (!k. (!s. s IN k ==> open_in top s) ==> open_in top (UNIONS k))`,
  SIMP_TAC[IN; SUBSET; SIMP_RULE[istopology; IN; SUBSET] ISTOPOLOGY_OPEN_IN]);;

let OPEN_IN_SUBSET = prove
 (`!top s. open_in top s ==> s SUBSET (topspace top)`,
  REWRITE_TAC[topspace] THEN SET_TAC[]);;

let OPEN_IN_EMPTY = prove
 (`!top. open_in top {}`,
  REWRITE_TAC[OPEN_IN_CLAUSES]);;

let OPEN_IN_INTER = prove
 (`!top s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)`,
  REWRITE_TAC[OPEN_IN_CLAUSES]);;

let OPEN_IN_UNIONS = prove
 (`!top k. (!s. s IN k ==> open_in top s) ==> open_in top (UNIONS k)`,
  REWRITE_TAC[OPEN_IN_CLAUSES]);;

let OPEN_IN_UNION = prove
 (`!top s t. open_in top s /\ open_in top t ==> open_in top (s UNION t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM SET_TAC[]);;

let OPEN_IN_TOPSPACE = prove
 (`!top. open_in top (topspace top)`,
  SIMP_TAC[topspace; OPEN_IN_UNIONS; IN_ELIM_THM]);;

let OPEN_IN_INTERS = prove
 (`!top s:(A->bool)->bool.
        FINITE s /\ ~(s = {}) /\ (!t. t IN s ==> open_in top t)
        ==> open_in top (INTERS s)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INTERS_INSERT; IMP_IMP; NOT_INSERT_EMPTY; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `f:(A->bool)->bool`] THEN
  ASM_CASES_TAC `f:(A->bool)->bool = {}` THEN
  ASM_SIMP_TAC[INTERS_0; INTER_UNIV] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[]);;

let OPEN_IN_SUBOPEN = prove
 (`!top s:A->bool.
        open_in top s <=>
        !x. x IN s ==> ?t. open_in top t /\ x IN t /\ t SUBSET s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[GSYM FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_UNIONS) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Closed sets.                                                              *)
(* ------------------------------------------------------------------------- *)

let closed_in = new_definition
 `closed_in top s <=>
        s SUBSET (topspace top) /\ open_in top (topspace top DIFF s)`;;

let CLOSED_IN_SUBSET = prove
 (`!top s. closed_in top s ==> s SUBSET (topspace top)`,
  MESON_TAC[closed_in]);;

let CLOSED_IN_EMPTY = prove
 (`!top. closed_in top {}`,
  REWRITE_TAC[closed_in; EMPTY_SUBSET; DIFF_EMPTY; OPEN_IN_TOPSPACE]);;

let CLOSED_IN_TOPSPACE = prove
 (`!top. closed_in top (topspace top)`,
  REWRITE_TAC[closed_in; SUBSET_REFL; DIFF_EQ_EMPTY; OPEN_IN_EMPTY]);;

let CLOSED_IN_UNION = prove
 (`!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s UNION t)`,
  SIMP_TAC[closed_in; UNION_SUBSET; OPEN_IN_INTER;
           SET_RULE `u DIFF (s UNION t) = (u DIFF s) INTER (u DIFF t)`]);;

let CLOSED_IN_INTERS = prove
 (`!top k:(A->bool)->bool.
        ~(k = {}) /\ (!s. s IN k ==> closed_in top s)
        ==> closed_in top (INTERS k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[closed_in] THEN REPEAT STRIP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace top DIFF INTERS k :A->bool =
                UNIONS {topspace top DIFF s | s IN k}` SUBST1_TAC
  THENL [ALL_TAC; MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM SET_TAC[]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  REWRITE_TAC[IN_UNIONS; IN_INTERS; IN_DIFF; EXISTS_IN_IMAGE] THEN
  MESON_TAC[]);;

let CLOSED_IN_INTER = prove
 (`!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC CLOSED_IN_INTERS THEN ASM SET_TAC[]);;

let OPEN_IN_CLOSED_IN_EQ = prove
 (`!top s. open_in top s <=>
           s SUBSET topspace top /\ closed_in top (topspace top DIFF s)`,
  REWRITE_TAC[closed_in; SET_RULE `(u DIFF s) SUBSET u`] THEN
  REWRITE_TAC[SET_RULE `u DIFF (u DIFF s) = u INTER s`] THEN
  MESON_TAC[OPEN_IN_SUBSET; SET_RULE `s SUBSET t ==> t INTER s = s`]);;

let OPEN_IN_CLOSED_IN = prove
 (`!s. s SUBSET topspace top
       ==> (open_in top s <=> closed_in top (topspace top DIFF s))`,
  SIMP_TAC[OPEN_IN_CLOSED_IN_EQ]);;

let OPEN_IN_DIFF = prove
 (`!top s t:A->bool.
      open_in top s /\ closed_in top t ==> open_in top (s DIFF t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s DIFF t :A->bool = s INTER (topspace top DIFF t)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_MESON_TAC[closed_in]]);;

let CLOSED_IN_DIFF = prove
 (`!top s t:A->bool.
        closed_in top s /\ open_in top t ==> closed_in top (s DIFF t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s DIFF t :A->bool = s INTER (topspace top DIFF t)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_INTER THEN ASM_MESON_TAC[OPEN_IN_CLOSED_IN_EQ]]);;

let CLOSED_IN_UNIONS = prove
 (`!top s. FINITE s /\ (!t. t IN s ==> closed_in top t)
           ==> closed_in top (UNIONS s)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_INSERT; UNIONS_0; CLOSED_IN_EMPTY; IN_INSERT] THEN
  MESON_TAC[CLOSED_IN_UNION]);;

(* ------------------------------------------------------------------------- *)
(* Subspace topology.                                                        *)
(* ------------------------------------------------------------------------- *)

let subtopology = new_definition
 `subtopology top u = topology {s INTER u | open_in top s}`;;

let ISTOPLOGY_SUBTOPOLOGY = prove
 (`!top u:A->bool. istopology {s INTER u | open_in top s}`,
  REWRITE_TAC[istopology; SET_RULE
   `{s INTER u | open_in top s} =
    IMAGE (\s. s INTER u) {s | open_in top s}`] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[SUBSET_IMAGE; IN_IMAGE; IN_ELIM_THM; SUBSET] THEN
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `{}:A->bool` THEN REWRITE_TAC[OPEN_IN_EMPTY; INTER_EMPTY];
    SIMP_TAC[SET_RULE `(s INTER u) INTER t INTER u = (s INTER t) INTER u`] THEN
    ASM_MESON_TAC[OPEN_IN_INTER];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:(A->bool)->bool`; `g:(A->bool)->bool`] THEN
    STRIP_TAC THEN EXISTS_TAC `UNIONS g :A->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_UNIONS; INTER_UNIONS] THEN SET_TAC[]]);;

let OPEN_IN_SUBTOPOLOGY = prove
 (`!top u s. open_in (subtopology top u) s <=>
                ?t. open_in top t /\ s = t INTER u`,
  REWRITE_TAC[subtopology] THEN
  SIMP_TAC[REWRITE_RULE[CONJUNCT2 topology_tybij] ISTOPLOGY_SUBTOPOLOGY] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM]);;

let TOPSPACE_SUBTOPOLOGY = prove
 (`!top u. topspace(subtopology top u) = topspace top INTER u`,
  REWRITE_TAC[topspace; OPEN_IN_SUBTOPOLOGY; INTER_UNIONS] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM]);;

let CLOSED_IN_SUBTOPOLOGY = prove
 (`!top u s. closed_in (subtopology top u) s <=>
                ?t:A->bool. closed_in top t /\ s = t INTER u`,
  REWRITE_TAC[closed_in; TOPSPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[SUBSET_INTER; OPEN_IN_SUBTOPOLOGY; RIGHT_AND_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `topspace top DIFF t :A->bool` THEN
  ASM_SIMP_TAC[CLOSED_IN_TOPSPACE; OPEN_IN_DIFF; CLOSED_IN_DIFF;
               OPEN_IN_TOPSPACE] THEN
  ASM SET_TAC[]);;

let OPEN_IN_SUBTOPOLOGY_EMPTY = prove
 (`!top s. open_in (subtopology top {}) s <=> s = {}`,
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; INTER_EMPTY] THEN
  MESON_TAC[OPEN_IN_EMPTY]);;

let CLOSED_IN_SUBTOPOLOGY_EMPTY = prove
 (`!top s. closed_in (subtopology top {}) s <=> s = {}`,
  REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY; INTER_EMPTY] THEN
  MESON_TAC[CLOSED_IN_EMPTY]);;

let OPEN_IN_SUBTOPOLOGY_REFL = prove
 (`!top u:A->bool. open_in (subtopology top u) u <=> u SUBSET topspace top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    DISCH_TAC THEN EXISTS_TAC `topspace top:A->bool` THEN
    REWRITE_TAC[OPEN_IN_TOPSPACE] THEN ASM SET_TAC[]]);;

let CLOSED_IN_SUBTOPOLOGY_REFL = prove
 (`!top u:A->bool. closed_in (subtopology top u) u <=> u SUBSET topspace top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
    ASM_SIMP_TAC[CLOSED_IN_SUBSET];
    DISCH_TAC THEN EXISTS_TAC `topspace top:A->bool` THEN
    REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN ASM SET_TAC[]]);;

let SUBTOPOLOGY_SUPERSET = prove
 (`!top s:A->bool. topspace top SUBSET s ==> subtopology top s = top`,
  REPEAT GEN_TAC THEN SIMP_TAC[TOPOLOGY_EQ; OPEN_IN_SUBTOPOLOGY] THEN
  DISCH_TAC THEN X_GEN_TAC `u:A->bool` THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
    DISCH_THEN(fun th -> MP_TAC th THEN
      ASSUME_TAC(MATCH_MP OPEN_IN_SUBSET th)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[];
    DISCH_TAC THEN EXISTS_TAC `u:A->bool` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]]);;

let SUBTOPOLOGY_TOPSPACE = prove
 (`!top. subtopology top (topspace top) = top`,
  SIMP_TAC[SUBTOPOLOGY_SUPERSET; SUBSET_REFL]);;

let SUBTOPOLOGY_UNIV = prove
 (`!top. subtopology top UNIV = top`,
  SIMP_TAC[SUBTOPOLOGY_SUPERSET; SUBSET_UNIV]);;

let OPEN_IN_IMP_SUBSET = prove
 (`!top s t. open_in (subtopology top s) t ==> t SUBSET s`,
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN SET_TAC[]);;

let CLOSED_IN_IMP_SUBSET = prove
 (`!top s t. closed_in (subtopology top s) t ==> t SUBSET s`,
  REWRITE_TAC[closed_in; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]);;

let OPEN_IN_SUBTOPOLOGY_UNION = prove
 (`!top s t u:A->bool.
        open_in (subtopology top t) s /\ open_in (subtopology top u) s
        ==> open_in (subtopology top (t UNION u)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s':A->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `t':A->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s' INTER t':A->bool` THEN ASM_SIMP_TAC[OPEN_IN_INTER] THEN
  ASM SET_TAC[]);;

let CLOSED_IN_SUBTOPOLOGY_UNION = prove
 (`!top s t u:A->bool.
        closed_in (subtopology top t) s /\ closed_in (subtopology top u) s
        ==> closed_in (subtopology top (t UNION u)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s':A->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `t':A->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s' INTER t':A->bool` THEN ASM_SIMP_TAC[CLOSED_IN_INTER] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The universal Euclidean versions are what we use most of the time.        *)
(* ------------------------------------------------------------------------- *)

let open_def = new_definition
  `open s <=> !x. x IN s ==> ?e. &0 < e /\ !x'. dist(x',x) < e ==> x' IN s`;;

let closed = new_definition
  `closed(s:real^N->bool) <=> open(UNIV DIFF s)`;;

let euclidean = new_definition
 `euclidean = topology open`;;

let OPEN_EMPTY = prove
 (`open {}`,
  REWRITE_TAC[open_def; NOT_IN_EMPTY]);;

let OPEN_UNIV = prove
 (`open(:real^N)`,
  REWRITE_TAC[open_def; IN_UNIV] THEN MESON_TAC[REAL_LT_01]);;

let OPEN_INTER = prove
 (`!s t. open s /\ open t ==> open (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[open_def; AND_FORALL_THM; IN_INTER] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `d1:real`) (X_CHOOSE_TAC `d2:real`)) THEN
  MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN
  ASM_MESON_TAC[REAL_LT_TRANS]);;

let OPEN_UNIONS = prove
 (`(!s. s IN f ==> open s) ==> open(UNIONS f)`,
  REWRITE_TAC[open_def; IN_UNIONS] THEN MESON_TAC[]);;

let OPEN_EXISTS_IN = prove
 (`!P Q:A->real^N->bool.
        (!a. P a ==> open {x | Q a x}) ==> open {x | ?a. P a /\ Q a x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(UNIONS {{x | Q (a:A) (x:real^N)} | P a})` MP_TAC THENL
   [MATCH_MP_TAC OPEN_UNIONS THEN ASM_REWRITE_TAC[FORALL_IN_GSPEC];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN
    SET_TAC[]]);;

let OPEN_EXISTS = prove
 (`!Q:A->real^N->bool. (!a. open {x | Q a x}) ==> open {x | ?a. Q a x}`,
  MP_TAC(ISPEC `\x:A. T` OPEN_EXISTS_IN) THEN REWRITE_TAC[]);;

let OPEN_IN = prove
 (`!s:real^N->bool. open s <=> open_in euclidean s`,
  GEN_TAC THEN REWRITE_TAC[euclidean] THEN CONV_TAC SYM_CONV THEN
  AP_THM_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 topology_tybij)] THEN
  REWRITE_TAC[REWRITE_RULE[IN] istopology] THEN
  REWRITE_TAC[OPEN_EMPTY; OPEN_INTER; SUBSET] THEN
  MESON_TAC[IN; OPEN_UNIONS]);;

let TOPSPACE_EUCLIDEAN = prove
 (`topspace euclidean = (:real^N)`,
  REWRITE_TAC[topspace; EXTENSION; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[OPEN_UNIV; IN_UNIV; OPEN_IN]);;

let TOPSPACE_EUCLIDEAN_SUBTOPOLOGY = prove
 (`!s. topspace (subtopology euclidean s) = s`,
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; TOPSPACE_SUBTOPOLOGY; INTER_UNIV]);;

let OPEN_IN_REFL = prove
 (`!s:real^N->bool. open_in (subtopology euclidean s) s`,
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV]);;

let CLOSED_IN_REFL = prove
 (`!s:real^N->bool. closed_in (subtopology euclidean s) s`,
  REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV]);;

let CLOSED_IN = prove
 (`!s:real^N->bool. closed s <=> closed_in euclidean s`,
  REWRITE_TAC[closed; closed_in; TOPSPACE_EUCLIDEAN; OPEN_IN; SUBSET_UNIV]);;

let OPEN_UNION = prove
 (`!s t. open s /\ open t ==> open(s UNION t)`,
  REWRITE_TAC[OPEN_IN; OPEN_IN_UNION]);;

let OPEN_SUBOPEN = prove
 (`!s. open s <=> !x. x IN s ==> ?t. open t /\ x IN t /\ t SUBSET s`,
  REWRITE_TAC[OPEN_IN; GSYM OPEN_IN_SUBOPEN]);;

let CLOSED_EMPTY = prove
 (`closed {}`,
  REWRITE_TAC[CLOSED_IN; CLOSED_IN_EMPTY]);;

let CLOSED_UNIV = prove
 (`closed(UNIV:real^N->bool)`,
  REWRITE_TAC[CLOSED_IN; GSYM TOPSPACE_EUCLIDEAN; CLOSED_IN_TOPSPACE]);;

let CLOSED_UNION = prove
 (`!s t. closed s /\ closed t ==> closed(s UNION t)`,
  REWRITE_TAC[CLOSED_IN; CLOSED_IN_UNION]);;

let CLOSED_INTER = prove
 (`!s t. closed s /\ closed t ==> closed(s INTER t)`,
  REWRITE_TAC[CLOSED_IN; CLOSED_IN_INTER]);;

let CLOSED_INTERS = prove
 (`!f. (!s:real^N->bool. s IN f ==> closed s) ==> closed(INTERS f)`,
  REWRITE_TAC[CLOSED_IN] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
  ASM_SIMP_TAC[CLOSED_IN_INTERS; INTERS_0] THEN
  REWRITE_TAC[GSYM TOPSPACE_EUCLIDEAN; CLOSED_IN_TOPSPACE]);;

let CLOSED_FORALL_IN = prove
 (`!P Q:A->real^N->bool.
        (!a. P a ==> closed {x | Q a x}) ==> closed {x | !a. P a ==> Q a x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closed(INTERS {{x | Q (a:A) (x:real^N)} | P a})` MP_TAC THENL
   [MATCH_MP_TAC CLOSED_INTERS THEN ASM_REWRITE_TAC[FORALL_IN_GSPEC];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[INTERS_GSPEC] THEN
    SET_TAC[]]);;

let CLOSED_FORALL = prove
 (`!Q:A->real^N->bool. (!a. closed {x | Q a x}) ==> closed {x | !a. Q a x}`,
  MP_TAC(ISPEC `\x:A. T` CLOSED_FORALL_IN) THEN REWRITE_TAC[]);;

let OPEN_CLOSED = prove
 (`!s:real^N->bool. open s <=> closed(UNIV DIFF s)`,
  SIMP_TAC[OPEN_IN; CLOSED_IN; TOPSPACE_EUCLIDEAN; SUBSET_UNIV;
           OPEN_IN_CLOSED_IN_EQ]);;

let OPEN_DIFF = prove
 (`!s t. open s /\ closed t ==> open(s DIFF t)`,
  REWRITE_TAC[OPEN_IN; CLOSED_IN; OPEN_IN_DIFF]);;

let CLOSED_DIFF = prove
 (`!s t. closed s /\ open t ==> closed(s DIFF t)`,
  REWRITE_TAC[OPEN_IN; CLOSED_IN; CLOSED_IN_DIFF]);;

let OPEN_INTERS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> open t) ==> open(INTERS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INTERS_INSERT; INTERS_0; OPEN_UNIV; IN_INSERT] THEN
  MESON_TAC[OPEN_INTER]);;

let CLOSED_UNIONS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> closed t) ==> closed(UNIONS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_INSERT; UNIONS_0; CLOSED_EMPTY; IN_INSERT] THEN
  MESON_TAC[CLOSED_UNION]);;

(* ------------------------------------------------------------------------- *)
(* Open and closed balls and spheres.                                        *)
(* ------------------------------------------------------------------------- *)

let ball = new_definition
  `ball(x,e) = { y | dist(x,y) < e}`;;

let cball = new_definition
  `cball(x,e) = { y | dist(x,y) <= e}`;;

let sphere = new_definition
  `sphere(x,e) = { y | dist(x,y) = e}`;;

let IN_BALL = prove
 (`!x y e. y IN ball(x,e) <=> dist(x,y) < e`,
  REWRITE_TAC[ball; IN_ELIM_THM]);;

let IN_CBALL = prove
 (`!x y e. y IN cball(x,e) <=> dist(x,y) <= e`,
  REWRITE_TAC[cball; IN_ELIM_THM]);;

let IN_SPHERE = prove
 (`!x y e. y IN sphere(x,e) <=> dist(x,y) = e`,
  REWRITE_TAC[sphere; IN_ELIM_THM]);;

let IN_BALL_0 = prove
 (`!x e. x IN ball(vec 0,e) <=> norm(x) < e`,
  REWRITE_TAC[IN_BALL; dist; VECTOR_SUB_LZERO; NORM_NEG]);;

let IN_CBALL_0 = prove
 (`!x e. x IN cball(vec 0,e) <=> norm(x) <= e`,
  REWRITE_TAC[IN_CBALL; dist; VECTOR_SUB_LZERO; NORM_NEG]);;

let IN_SPHERE_0 = prove
 (`!x e. x IN sphere(vec 0,e) <=> norm(x) = e`,
  REWRITE_TAC[IN_SPHERE; dist; VECTOR_SUB_LZERO; NORM_NEG]);;

let BALL_TRIVIAL = prove
 (`!x. ball(x,&0) = {}`,
  REWRITE_TAC[EXTENSION; IN_BALL; IN_SING; NOT_IN_EMPTY] THEN NORM_ARITH_TAC);;

let CBALL_TRIVIAL = prove
 (`!x. cball(x,&0) = {x}`,
  REWRITE_TAC[EXTENSION; IN_CBALL; IN_SING; NOT_IN_EMPTY] THEN NORM_ARITH_TAC);;

let CENTRE_IN_CBALL = prove
 (`!x e. x IN cball(x,e) <=> &0 <= e`,
  MESON_TAC[IN_CBALL; DIST_REFL]);;

let BALL_SUBSET_CBALL = prove
 (`!x e. ball(x,e) SUBSET cball(x,e)`,
  REWRITE_TAC[IN_BALL; IN_CBALL; SUBSET] THEN REAL_ARITH_TAC);;

let SPHERE_SUBSET_CBALL = prove
 (`!x e. sphere(x,e) SUBSET cball(x,e)`,
  REWRITE_TAC[IN_SPHERE; IN_CBALL; SUBSET] THEN REAL_ARITH_TAC);;

let SUBSET_BALL = prove
 (`!x d e. d <= e ==> ball(x,d) SUBSET ball(x,e)`,
  REWRITE_TAC[SUBSET; IN_BALL] THEN MESON_TAC[REAL_LTE_TRANS]);;

let SUBSET_CBALL = prove
 (`!x d e. d <= e ==> cball(x,d) SUBSET cball(x,e)`,
  REWRITE_TAC[SUBSET; IN_CBALL] THEN MESON_TAC[REAL_LE_TRANS]);;

let BALL_MAX_UNION = prove
 (`!a r s. ball(a,max r s) = ball(a,r) UNION ball(a,s)`,
  REWRITE_TAC[IN_BALL; IN_UNION; EXTENSION] THEN REAL_ARITH_TAC);;

let BALL_MIN_INTER = prove
 (`!a r s. ball(a,min r s) = ball(a,r) INTER ball(a,s)`,
  REWRITE_TAC[IN_BALL; IN_INTER; EXTENSION] THEN REAL_ARITH_TAC);;

let CBALL_MAX_UNION = prove
 (`!a r s. cball(a,max r s) = cball(a,r) UNION cball(a,s)`,
  REWRITE_TAC[IN_CBALL; IN_UNION; EXTENSION] THEN REAL_ARITH_TAC);;

let CBALL_MIN_INTER = prove
 (`!x d e. cball(x,min d e) = cball(x,d) INTER cball(x,e)`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_CBALL] THEN REAL_ARITH_TAC);;

let BALL_TRANSLATION = prove
 (`!a x r. ball(a + x,r) = IMAGE (\y. a + y) (ball(x,r))`,
  REWRITE_TAC[ball] THEN GEOM_TRANSLATE_TAC[]);;

let CBALL_TRANSLATION = prove
 (`!a x r. cball(a + x,r) = IMAGE (\y. a + y) (cball(x,r))`,
  REWRITE_TAC[cball] THEN GEOM_TRANSLATE_TAC[]);;

let SPHERE_TRANSLATION = prove
 (`!a x r. sphere(a + x,r) = IMAGE (\y. a + y) (sphere(x,r))`,
  REWRITE_TAC[sphere] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants
  [BALL_TRANSLATION; CBALL_TRANSLATION; SPHERE_TRANSLATION];;

let BALL_LINEAR_IMAGE = prove
 (`!f:real^M->real^N x r.
        linear f /\ (!y. ?x. f x = y) /\ (!x. norm(f x) = norm x)
        ==> ball(f x,r) = IMAGE f (ball(x,r))`,
  REWRITE_TAC[ball] THEN GEOM_TRANSFORM_TAC[]);;

let CBALL_LINEAR_IMAGE = prove
 (`!f:real^M->real^N x r.
        linear f /\ (!y. ?x. f x = y) /\ (!x. norm(f x) = norm x)
        ==> cball(f x,r) = IMAGE f (cball(x,r))`,
  REWRITE_TAC[cball] THEN GEOM_TRANSFORM_TAC[]);;

let SPHERE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N x r.
        linear f /\ (!y. ?x. f x = y) /\ (!x. norm(f x) = norm x)
        ==> sphere(f x,r) = IMAGE f (sphere(x,r))`,
  REWRITE_TAC[sphere] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants
  [BALL_LINEAR_IMAGE; CBALL_LINEAR_IMAGE; SPHERE_LINEAR_IMAGE];;

let BALL_SCALING = prove
 (`!c. &0 < c ==> !x r. ball(c % x,c * r) = IMAGE (\x. c % x) (ball(x,r))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SURJECTIVE_SCALING; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  REWRITE_TAC[IN_BALL; DIST_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_LT_LMUL_EQ]);;

let CBALL_SCALING = prove
 (`!c. &0 < c ==> !x r. cball(c % x,c * r) = IMAGE (\x. c % x) (cball(x,r))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SURJECTIVE_SCALING; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  REWRITE_TAC[IN_CBALL; DIST_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_LE_LMUL_EQ]);;

add_scaling_theorems [BALL_SCALING; CBALL_SCALING];;

let CBALL_DIFF_BALL = prove
 (`!a r. cball(a,r) DIFF ball(a,r) = sphere(a,r)`,
  REWRITE_TAC[ball; cball; sphere; EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

let BALL_UNION_SPHERE = prove
 (`!a r. ball(a,r) UNION sphere(a,r) = cball(a,r)`,
  REWRITE_TAC[ball; cball; sphere; EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

let SPHERE_UNION_BALL = prove
 (`!a r. sphere(a,r) UNION ball(a,r)  = cball(a,r)`,
  REWRITE_TAC[ball; cball; sphere; EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

let CBALL_DIFF_SPHERE = prove
 (`!a r. cball(a,r) DIFF sphere(a,r) = ball(a,r)`,
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_SPHERE; IN_BALL; IN_CBALL] THEN
  REAL_ARITH_TAC);;

let OPEN_BALL = prove
 (`!x e. open(ball(x,e))`,
  REWRITE_TAC[open_def; ball; IN_ELIM_THM] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  MESON_TAC[REAL_SUB_LT; REAL_LT_SUB_LADD; REAL_ADD_SYM; REAL_LET_TRANS;
            DIST_TRIANGLE_ALT]);;

let CENTRE_IN_BALL = prove
 (`!x e. x IN ball(x,e) <=> &0 < e`,
  MESON_TAC[IN_BALL; DIST_REFL]);;

let OPEN_CONTAINS_BALL = prove
 (`!s. open s <=> !x. x IN s ==> ?e. &0 < e /\ ball(x,e) SUBSET s`,
  REWRITE_TAC[open_def; SUBSET; IN_BALL] THEN REWRITE_TAC[DIST_SYM]);;

let OPEN_CONTAINS_BALL_EQ = prove
 (`!s. open s ==> (!x. x IN s <=> ?e. &0 < e /\ ball(x,e) SUBSET s)`,
  MESON_TAC[OPEN_CONTAINS_BALL; SUBSET; CENTRE_IN_BALL]);;

let BALL_EQ_EMPTY = prove
 (`!x e. (ball(x,e) = {}) <=> e <= &0`,
  REWRITE_TAC[EXTENSION; IN_BALL; NOT_IN_EMPTY; REAL_NOT_LT] THEN
  MESON_TAC[DIST_POS_LE; REAL_LE_TRANS; DIST_REFL]);;

let BALL_EMPTY = prove
 (`!x e. e <= &0 ==> ball(x,e) = {}`,
  REWRITE_TAC[BALL_EQ_EMPTY]);;

let OPEN_CONTAINS_CBALL = prove
 (`!s. open s <=> !x. x IN s ==> ?e. &0 < e /\ cball(x,e) SUBSET s`,
  GEN_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SUBSET_TRANS; BALL_SUBSET_CBALL]] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  SUBGOAL_THEN `e / &2 < e` (fun th -> ASM_MESON_TAC[th; REAL_LET_TRANS]) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

let OPEN_CONTAINS_CBALL_EQ = prove
 (`!s. open s ==> (!x. x IN s <=> ?e. &0 < e /\ cball(x,e) SUBSET s)`,
  MESON_TAC[OPEN_CONTAINS_CBALL; SUBSET; REAL_LT_IMP_LE; CENTRE_IN_CBALL]);;

let SPHERE_EQ_EMPTY = prove
 (`!a:real^N r. sphere(a,r) = {} <=> r < &0`,
  REWRITE_TAC[sphere; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; CONV_TAC NORM_ARITH] THEN
  MESON_TAC[VECTOR_CHOOSE_DIST; REAL_NOT_LE]);;

let SPHERE_EMPTY = prove
 (`!a:real^N r. r < &0 ==> sphere(a,r) = {}`,
  REWRITE_TAC[SPHERE_EQ_EMPTY]);;

let NEGATIONS_BALL = prove
 (`!r. IMAGE (--) (ball(vec 0:real^N,r)) = ball(vec 0,r)`,
  GEN_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_BALL_0; NORM_NEG] THEN MESON_TAC[VECTOR_NEG_NEG]);;

let NEGATIONS_CBALL = prove
 (`!r. IMAGE (--) (cball(vec 0:real^N,r)) = cball(vec 0,r)`,
  GEN_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_CBALL_0; NORM_NEG] THEN MESON_TAC[VECTOR_NEG_NEG]);;

let NEGATIONS_SPHERE = prove
 (`!r. IMAGE (--) (sphere(vec 0:real^N,r)) = sphere(vec 0,r)`,
  GEN_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_NEG] THEN MESON_TAC[VECTOR_NEG_NEG]);;

let ORTHOGONAL_TRANSFORMATION_BALL = prove
 (`!f:real^N->real^N r.
    orthogonal_transformation f ==> IMAGE f (ball(vec 0,r)) = ball(vec 0,r)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL_0] THEN
  MESON_TAC[ORTHOGONAL_TRANSFORMATION_INVERSE; ORTHOGONAL_TRANSFORMATION]);;

let ORTHOGONAL_TRANSFORMATION_CBALL = prove
 (`!f:real^N->real^N r.
    orthogonal_transformation f ==> IMAGE f (cball(vec 0,r)) = cball(vec 0,r)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_CBALL_0] THEN
  MESON_TAC[ORTHOGONAL_TRANSFORMATION_INVERSE; ORTHOGONAL_TRANSFORMATION]);;

let ORTHOGONAL_TRANSFORMATION_SPHERE = prove
 (`!f:real^N->real^N r.
    orthogonal_transformation f
    ==> IMAGE f (sphere(vec 0,r)) = sphere(vec 0,r)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN
  MESON_TAC[ORTHOGONAL_TRANSFORMATION_INVERSE; ORTHOGONAL_TRANSFORMATION]);;

(* ------------------------------------------------------------------------- *)
(* Basic "localization" results are handy for connectedness.                 *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_OPEN = prove
 (`!s:real^N->bool u.
        open_in (subtopology euclidean u) s <=> ?t. open t /\ (s = u INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM OPEN_IN] THEN
  REWRITE_TAC[INTER_ACI]);;

let OPEN_IN_INTER_OPEN = prove
 (`!s t u:real^N->bool.
        open_in (subtopology euclidean u) s /\ open t
        ==> open_in (subtopology euclidean u) (s INTER t)`,
  REWRITE_TAC[OPEN_IN_OPEN] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[INTER_ASSOC] THEN ASM_MESON_TAC[OPEN_INTER]);;

let OPEN_IN_OPEN_INTER = prove
 (`!u s. open s ==> open_in (subtopology euclidean u) (u INTER s)`,
  REWRITE_TAC[OPEN_IN_OPEN] THEN MESON_TAC[]);;

let OPEN_OPEN_IN_TRANS = prove
 (`!s t. open s /\ open t /\ t SUBSET s
         ==> open_in (subtopology euclidean s) t`,
  MESON_TAC[OPEN_IN_OPEN_INTER; SET_RULE `t SUBSET s ==> t = s INTER t`]);;

let OPEN_SUBSET = prove
 (`!s t:real^N->bool.
        s SUBSET t /\ open s ==> open_in (subtopology euclidean t) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM SET_TAC[]);;

let CLOSED_IN_CLOSED = prove
 (`!s:real^N->bool u.
    closed_in (subtopology euclidean u) s <=> ?t. closed t /\ (s = u INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY; GSYM CLOSED_IN] THEN
  REWRITE_TAC[INTER_ACI]);;

let CLOSED_SUBSET_EQ = prove
 (`!u s:real^N->bool.
        closed s ==> (closed_in (subtopology euclidean u) s <=> s SUBSET u)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM SET_TAC[]]);;

let CLOSED_IN_INTER_CLOSED = prove
 (`!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\ closed t
        ==> closed_in (subtopology euclidean u) (s INTER t)`,
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[INTER_ASSOC] THEN ASM_MESON_TAC[CLOSED_INTER]);;

let CLOSED_IN_CLOSED_INTER = prove
 (`!u s. closed s ==> closed_in (subtopology euclidean u) (u INTER s)`,
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN MESON_TAC[]);;

let CLOSED_SUBSET = prove
 (`!s t:real^N->bool.
        s SUBSET t /\ closed s ==> closed_in (subtopology euclidean t) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM SET_TAC[]);;

let OPEN_IN_SUBSET_TRANS = prove
 (`!s t u:real^N->bool.
        open_in (subtopology euclidean u) s /\ s SUBSET t /\ t SUBSET u
        ==> open_in (subtopology euclidean t) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN; LEFT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

let CLOSED_IN_SUBSET_TRANS = prove
 (`!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\ s SUBSET t /\ t SUBSET u
        ==> closed_in (subtopology euclidean t) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSED; LEFT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

let open_in = prove
 (`!u s:real^N->bool.
        open_in (subtopology euclidean u) s <=>
          s SUBSET u /\
          !x. x IN s ==> ?e. &0 < e /\
                             !x'. x' IN u /\ dist(x',x) < e ==> x' IN s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM OPEN_IN] THEN EQ_TAC THENL
   [REWRITE_TAC[open_def] THEN ASM SET_TAC[INTER_SUBSET; IN_INTER];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `d:real^N->real`) THEN
  EXISTS_TAC `UNIONS {b | ?x:real^N. (b = ball(x,d x)) /\ x IN s}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_UNIONS THEN
    ASM_SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; OPEN_BALL];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_MESON_TAC[SUBSET; DIST_REFL; DIST_SYM; IN_BALL]]);;

let OPEN_IN_CONTAINS_BALL = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean t) s <=>
        s SUBSET t /\
        !x. x IN s ==> ?e. &0 < e /\ ball(x,e) INTER t SUBSET s`,
  REWRITE_TAC[open_in; INTER; SUBSET; IN_ELIM_THM; IN_BALL] THEN
  MESON_TAC[DIST_SYM]);;

let OPEN_IN_CONTAINS_CBALL = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean t) s <=>
        s SUBSET t /\
        !x. x IN s ==> ?e. &0 < e /\ cball(x,e) INTER t SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  AP_TERM_TAC THEN REWRITE_TAC[IN_BALL; IN_INTER; SUBSET; IN_CBALL] THEN
  MESON_TAC[REAL_ARITH `&0 < e ==> &0 < e / &2 /\ (x <= e / &2 ==> x < e)`;
            REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* These "transitivity" results are handy too.                               *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_TRANS = prove
 (`!s t u. open_in (subtopology euclidean t) s /\
           open_in (subtopology euclidean u) t
           ==> open_in (subtopology euclidean u) s`,
  ASM_MESON_TAC[OPEN_IN_OPEN; OPEN_IN; OPEN_INTER; INTER_ASSOC]);;

let OPEN_IN_TRANS_EQ = prove
 (`!s t:real^N->bool.
        (!u. open_in (subtopology euclidean t) u
             ==> open_in (subtopology euclidean s) t)
        <=> open_in (subtopology euclidean s) t`,
  MESON_TAC[OPEN_IN_TRANS; OPEN_IN_REFL]);;

let OPEN_IN_OPEN_TRANS = prove
 (`!s t. open_in (subtopology euclidean t) s /\ open t ==> open s`,
  REWRITE_TAC[ONCE_REWRITE_RULE[GSYM SUBTOPOLOGY_UNIV] OPEN_IN] THEN
  REWRITE_TAC[OPEN_IN_TRANS]);;

let CLOSED_IN_TRANS = prove
 (`!s t u. closed_in (subtopology euclidean t) s /\
           closed_in (subtopology euclidean u) t
           ==> closed_in (subtopology euclidean u) s`,
  ASM_MESON_TAC[CLOSED_IN_CLOSED; CLOSED_IN; CLOSED_INTER; INTER_ASSOC]);;

let CLOSED_IN_TRANS_EQ = prove
 (`!s t:real^N->bool.
        (!u. closed_in (subtopology euclidean t) u
             ==> closed_in (subtopology euclidean s) t)
        <=> closed_in (subtopology euclidean s) t`,
  MESON_TAC[CLOSED_IN_TRANS; CLOSED_IN_REFL]);;

let CLOSED_IN_CLOSED_TRANS = prove
 (`!s t. closed_in (subtopology euclidean t) s /\ closed t ==> closed s`,
  REWRITE_TAC[ONCE_REWRITE_RULE[GSYM SUBTOPOLOGY_UNIV] CLOSED_IN] THEN
  REWRITE_TAC[CLOSED_IN_TRANS]);;

let OPEN_IN_SUBTOPOLOGY_INTER_SUBSET = prove
 (`!s u v. open_in (subtopology euclidean u) (u INTER s) /\ v SUBSET u
           ==> open_in (subtopology euclidean v) (v INTER s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN; LEFT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

let OPEN_IN_OPEN_EQ = prove
 (`!s t. open s
         ==> (open_in (subtopology euclidean s) t <=> open t /\ t SUBSET s)`,
  MESON_TAC[OPEN_OPEN_IN_TRANS; OPEN_IN_OPEN_TRANS; open_in]);;

let CLOSED_IN_CLOSED_EQ = prove
 (`!s t. closed s
         ==> (closed_in (subtopology euclidean s) t <=>
              closed t /\ t SUBSET s)`,
  MESON_TAC[CLOSED_SUBSET; CLOSED_IN_CLOSED_TRANS; closed_in;
            TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]);;

(* ------------------------------------------------------------------------- *)
(* Also some invariance theorems for relative topology.                      *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_TRANSLATION_EQ = prove
 (`!a s t. open_in (subtopology euclidean (IMAGE (\x. a + x) t))
                   (IMAGE (\x. a + x) s) <=>
           open_in (subtopology euclidean t) s`,
  REWRITE_TAC[open_in] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [OPEN_IN_TRANSLATION_EQ];;

let CLOSED_IN_TRANSLATION_EQ = prove
 (`!a s t. closed_in (subtopology euclidean (IMAGE (\x. a + x) t))
                   (IMAGE (\x. a + x) s) <=>
           closed_in (subtopology euclidean t) s`,
  REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [CLOSED_IN_TRANSLATION_EQ];;

let OPEN_IN_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s t.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> (open_in (subtopology euclidean (IMAGE f t)) (IMAGE f s) <=>
               open_in (subtopology euclidean t) s)`,
  REWRITE_TAC[open_in; FORALL_IN_IMAGE; IMP_CONJ; SUBSET] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SET_RULE
   `(!x y. f x = f y ==> x = y) ==> (!x s. f x IN IMAGE f s <=> x IN s)`)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_BOUNDED_POS) THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_BOUNDED_BELOW_POS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `B2:real` THEN STRIP_TAC THEN
  X_GEN_TAC `B1:real` THEN STRIP_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM o MATCH_MP LINEAR_SUB) THEN
  ASM_REWRITE_TAC[dist; IMP_IMP] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `e / B1:real`; EXISTS_TAC `e * B2:real`] THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(REAL_ARITH
     `norm(f x) <= B1 * norm(x) /\ norm(x) * B1 < e ==> norm(f x) < e`) THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ];
    MATCH_MP_TAC(REAL_ARITH
     `norm x <= norm (f x :real^N) / B2 /\ norm(f x) / B2 < e
      ==> norm x < e`) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ]]);;

add_linear_invariants [OPEN_IN_INJECTIVE_LINEAR_IMAGE];;

let CLOSED_IN_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s t.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> (closed_in (subtopology euclidean (IMAGE f t)) (IMAGE f s) <=>
               closed_in (subtopology euclidean t) s)`,
  REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [CLOSED_IN_INJECTIVE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Connectedness.                                                            *)
(* ------------------------------------------------------------------------- *)

let connected = new_definition
  `connected s <=>
      ~(?e1 e2. open e1 /\ open e2 /\ s SUBSET (e1 UNION e2) /\
                (e1 INTER e2 INTER s = {}) /\
                ~(e1 INTER s = {}) /\ ~(e2 INTER s = {}))`;;

let CONNECTED_CLOSED = prove
 (`!s:real^N->bool.
        connected s <=>
        ~(?e1 e2. closed e1 /\ closed e2 /\ s SUBSET (e1 UNION e2) /\
                  (e1 INTER e2 INTER s = {}) /\
                  ~(e1 INTER s = {}) /\ ~(e2 INTER s = {}))`,
  GEN_TAC THEN REWRITE_TAC[connected] THEN AP_TERM_TAC THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(:real^N) DIFF v`; `(:real^N) DIFF u`] THEN
  ASM_REWRITE_TAC[GSYM closed; GSYM OPEN_CLOSED] THEN ASM SET_TAC[]);;

let CONNECTED_OPEN_IN = prove
 (`!s. connected s <=>
           ~(?e1 e2.
                 open_in (subtopology euclidean s) e1 /\
                 open_in (subtopology euclidean s) e2 /\
                 s SUBSET e1 UNION e2 /\
                 e1 INTER e2 = {} /\
                 ~(e1 = {}) /\
                 ~(e2 = {}))`,
  GEN_TAC THEN REWRITE_TAC[connected; OPEN_IN_OPEN] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV UNWIND_CONV) THEN
  AP_TERM_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  SET_TAC[]);;

let CONNECTED_OPEN_IN_EQ = prove
 (`!s. connected s <=>
           ~(?e1 e2.
                 open_in (subtopology euclidean s) e1 /\
                 open_in (subtopology euclidean s) e2 /\
                 e1 UNION e2 = s /\ e1 INTER e2 = {} /\
                 ~(e1 = {}) /\ ~(e2 = {}))`,
  GEN_TAC THEN REWRITE_TAC[CONNECTED_OPEN_IN] THEN
  AP_TERM_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[OPEN_IN_CLOSED_IN_EQ;
   TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]) THEN
  ASM SET_TAC[]);;

let CONNECTED_CLOSED_IN = prove
 (`!s. connected s <=>
           ~(?e1 e2.
                 closed_in (subtopology euclidean s) e1 /\
                 closed_in (subtopology euclidean s) e2 /\
                 s SUBSET e1 UNION e2 /\
                 e1 INTER e2 = {} /\
                 ~(e1 = {}) /\
                 ~(e2 = {}))`,
  GEN_TAC THEN REWRITE_TAC[CONNECTED_CLOSED; CLOSED_IN_CLOSED] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV UNWIND_CONV) THEN
  AP_TERM_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  SET_TAC[]);;

let CONNECTED_CLOSED_IN_EQ = prove
 (`!s. connected s <=>
           ~(?e1 e2.
                 closed_in (subtopology euclidean s) e1 /\
                 closed_in (subtopology euclidean s) e2 /\

                 e1 UNION e2 = s /\ e1 INTER e2 = {} /\
                 ~(e1 = {}) /\ ~(e2 = {}))`,
  GEN_TAC THEN REWRITE_TAC[CONNECTED_CLOSED_IN] THEN
  AP_TERM_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]) THEN
  ASM SET_TAC[]);;

let CONNECTED_CLOPEN = prove
 (`!s. connected s <=>
        !t. open_in (subtopology euclidean s) t /\
            closed_in (subtopology euclidean s) t ==> t = {} \/ t = s`,
  GEN_TAC THEN REWRITE_TAC[connected; OPEN_IN_OPEN; CLOSED_IN_CLOSED] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINDER_CONV) [GSYM EXISTS_DIFF] THEN
  ONCE_REWRITE_TAC[TAUT `(~a <=> b) <=> (a <=> ~b)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; GSYM CONJ_ASSOC; DE_MORGAN_THM] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> b /\ a /\ c /\ d`] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN REWRITE_TAC[GSYM closed] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[TAUT `(a /\ b) /\ (c /\ d) /\ e <=> a /\ c /\ b /\ d /\ e`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let CONNECTED_CLOSED_SET = prove
 (`!s:real^N->bool.
        closed s
        ==> (connected s <=>
             ~(?e1 e2. closed e1 /\ closed e2 /\ ~(e1 = {}) /\ ~(e2 = {}) /\
                       e1 UNION e2 = s /\ e1 INTER e2 = {}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[CONNECTED_CLOSED; CONTRAPOS_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    SIMP_TAC[] THEN SET_TAC[];
    REWRITE_TAC[CONNECTED_CLOSED_IN; CONTRAPOS_THM; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[CLOSED_IN_CLOSED; LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN REWRITE_TAC[IMP_IMP] THEN
    MAP_EVERY X_GEN_TAC
     [`e1:real^N->bool`; `e2:real^N->bool`;
      `u:real^N->bool`; `v:real^N->bool`] THEN
    STRIP_TAC THEN MAP_EVERY (C UNDISCH_THEN SUBST_ALL_TAC)
     [`e1:real^N->bool = s INTER u`;
      `e2:real^N->bool = s INTER v`] THEN
    MAP_EVERY EXISTS_TAC
     [`s INTER u:real^N->bool`; `s INTER v:real^N->bool`] THEN
    ASM_SIMP_TAC[CLOSED_INTER] THEN ASM SET_TAC[]]);;

let CONNECTED_OPEN_SET = prove
 (`!s:real^N->bool.
        open s
        ==> (connected s <=>
             ~(?e1 e2. open e1 /\ open e2 /\ ~(e1 = {}) /\ ~(e2 = {}) /\
                       e1 UNION e2 = s /\ e1 INTER e2 = {}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[connected; CONTRAPOS_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    SIMP_TAC[] THEN SET_TAC[];
    REWRITE_TAC[CONNECTED_OPEN_IN; CONTRAPOS_THM; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[OPEN_IN_OPEN; LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN REWRITE_TAC[IMP_IMP] THEN
    MAP_EVERY X_GEN_TAC
     [`e1:real^N->bool`; `e2:real^N->bool`;
      `u:real^N->bool`; `v:real^N->bool`] THEN
    STRIP_TAC THEN MAP_EVERY (C UNDISCH_THEN SUBST_ALL_TAC)
     [`e1:real^N->bool = s INTER u`;
      `e2:real^N->bool = s INTER v`] THEN
    MAP_EVERY EXISTS_TAC
     [`s INTER u:real^N->bool`; `s INTER v:real^N->bool`] THEN
    ASM_SIMP_TAC[OPEN_INTER] THEN ASM SET_TAC[]]);;

let CONNECTED_EMPTY = prove
 (`connected {}`,
  REWRITE_TAC[connected; INTER_EMPTY]);;

let CONNECTED_SING = prove
 (`!a. connected{a}`,
  REWRITE_TAC[connected] THEN SET_TAC[]);;

let CONNECTED_UNIONS = prove
 (`!P:(real^N->bool)->bool.
        (!s. s IN P ==> connected s) /\ ~(INTERS P = {})
        ==> connected(UNIONS P)`,
  GEN_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN
  STRIP_TAC THEN UNDISCH_TAC `~(INTERS P :real^N->bool = {})` THEN
  PURE_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTERS] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:real^N) IN e1 \/ a IN e2` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[];
    UNDISCH_TAC `~(e2 INTER UNIONS P:real^N->bool = {})`;
    UNDISCH_TAC `~(e1 INTER UNIONS P:real^N->bool = {})`] THEN
  PURE_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N`
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `!t:real^N->bool. t IN P ==> a IN t` THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`]) THEN
  ASM SET_TAC[]);;

let CONNECTED_UNION = prove
 (`!s t:real^N->bool.
        connected s /\ connected t /\ ~(s INTER t = {})
        ==> connected (s UNION t)`,
  REWRITE_TAC[GSYM UNIONS_2; GSYM INTERS_2] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_UNIONS THEN
  ASM SET_TAC[]);;

let CONNECTED_DIFF_OPEN_FROM_CLOSED = prove
 (`!s t u:real^N->bool.
        s SUBSET t /\ t SUBSET u /\
        open s /\ closed t /\ connected u /\ connected(t DIFF s)
        ==> connected(u DIFF s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N->bool`; `w:real^N->bool`] THEN STRIP_TAC THEN
  UNDISCH_TAC `connected(t DIFF s:real^N->bool)` THEN SIMP_TAC[connected] THEN
  MAP_EVERY EXISTS_TAC [`v:real^N->bool`; `w:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`v:real^N->bool`; `w:real^N->bool`] THEN
  MATCH_MP_TAC(MESON[]
   `(!v w. P v w ==> P w v) /\ (!w v. P v w /\ Q w ==> F)
    ==> !w v. P v w ==> ~(Q v) /\ ~(Q w)`) THEN
  CONJ_TAC THENL [SIMP_TAC[CONJ_ACI; INTER_ACI; UNION_ACI]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected]) THEN SIMP_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`v UNION s:real^N->bool`; `w DIFF t:real^N->bool`] THEN
  ASM_SIMP_TAC[OPEN_UNION; OPEN_DIFF] THEN ASM SET_TAC[]);;

let CONNECTED_DISJOINT_UNIONS_OPEN_UNIQUE = prove
 (`!f:(real^N->bool)->bool f'.
         pairwise DISJOINT f /\ pairwise DISJOINT f' /\
        (!s. s IN f ==> open s /\ connected s /\ ~(s = {})) /\
        (!s. s IN f' ==> open s /\ connected s /\ ~(s = {})) /\
        UNIONS f = UNIONS f'
        ==> f = f'`,
  GEN_REWRITE_TAC (funpow 2 BINDER_CONV o RAND_CONV) [EXTENSION] THEN
  MATCH_MP_TAC(MESON[]
   `(!s t. P s t ==> P t s) /\ (!s t x. P s t /\ x IN s ==> x IN t)
    ==> (!s t. P s t ==> (!x. x IN s <=> x IN t))`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN GEN_TAC THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?t a:real^N. t IN f' /\ a IN s /\ a IN t` STRIP_ASSUME_TAC
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s:real^N->bool = t` (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[EXTENSION] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t))
   [`s:real^N->bool`; `t:real^N->bool`;
    `f:(real^N->bool)->bool`; `f':(real^N->bool)->bool`] THEN
  MATCH_MP_TAC(MESON[]
   `(!f f' s t. P f f' s t ==> P f' f t s) /\
    (!f f' s t x. P f f' s t /\ x IN s ==> x IN t)
    ==> (!f' f t s. P f f' s t ==> (!x. x IN s <=> x IN t))`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPLICATE_TAC 4 GEN_TAC THEN X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN
  UNDISCH_TAC
   `!s:real^N->bool. s IN f ==> open s /\ connected s /\ ~(s = {})` THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_CASES_TAC `(b:real^N) IN t` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `connected(s:real^N->bool)` THEN
  REWRITE_TAC[connected] THEN
  MAP_EVERY EXISTS_TAC
   [`t:real^N->bool`; `UNIONS(f' DELETE (t:real^N->bool))`] THEN
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[];
    MATCH_MP_TAC OPEN_UNIONS THEN ASM_SIMP_TAC[IN_DELETE];
    REWRITE_TAC[GSYM UNIONS_INSERT] THEN ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE `t INTER u = {} ==> t INTER u INTER s = {}`) THEN
    REWRITE_TAC[INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_DELETE; GSYM DISJOINT] THEN ASM_MESON_TAC[pairwise];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let CONNECTED_FROM_CLOSED_UNION_AND_INTER = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ connected(s UNION t) /\ connected(s INTER t)
        ==> connected s /\ connected t`,
  MATCH_MP_TAC(MESON[]
   `(!s t. P s t ==> P t s) /\ (!s t. P s t ==> Q s)
    ==> !s t. P s t ==> Q s /\ Q t`) THEN
  CONJ_TAC THENL [SIMP_TAC[UNION_COMM; INTER_COMM]; REPEAT STRIP_TAC] THEN
  ASM_SIMP_TAC[CONNECTED_CLOSED_SET] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
  STRIP_TAC THEN ASM_CASES_TAC
   `~(s INTER t SUBSET (u:real^N->bool)) /\ ~(s INTER t SUBSET v)`
  THENL
   [UNDISCH_TAC `connected(s INTER t:real^N->bool)` THEN
    ASM_SIMP_TAC[CONNECTED_CLOSED] THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `connected(s UNION t:real^N->bool)` THEN
    ASM_SIMP_TAC[CONNECTED_CLOSED] THENL
     [MAP_EVERY EXISTS_TAC [`t UNION u:real^N->bool`; `v:real^N->bool`] THEN
      ASM_SIMP_TAC[CLOSED_UNION] THEN ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`t UNION v:real^N->bool`; `u:real^N->bool`] THEN
      ASM_SIMP_TAC[CLOSED_UNION] THEN ASM SET_TAC[]]]);;

let CONNECTED_FROM_OPEN_UNION_AND_INTER = prove
 (`!s t:real^N->bool.
        open s /\ open t /\ connected(s UNION t) /\ connected(s INTER t)
        ==> connected s /\ connected t`,
  MATCH_MP_TAC(MESON[]
   `(!s t. P s t ==> P t s) /\ (!s t. P s t ==> Q s)
    ==> !s t. P s t ==> Q s /\ Q t`) THEN
  CONJ_TAC THENL [SIMP_TAC[UNION_COMM; INTER_COMM]; REPEAT STRIP_TAC] THEN
  ASM_SIMP_TAC[CONNECTED_OPEN_SET] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
  STRIP_TAC THEN ASM_CASES_TAC
   `~(s INTER t SUBSET (u:real^N->bool)) /\ ~(s INTER t SUBSET v)`
  THENL
   [UNDISCH_TAC `connected(s INTER t:real^N->bool)` THEN
    ASM_SIMP_TAC[connected] THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `connected(s UNION t:real^N->bool)` THEN
    ASM_SIMP_TAC[connected] THENL
     [MAP_EVERY EXISTS_TAC [`t UNION u:real^N->bool`; `v:real^N->bool`] THEN
      ASM_SIMP_TAC[OPEN_UNION] THEN ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`t UNION v:real^N->bool`; `u:real^N->bool`] THEN
      ASM_SIMP_TAC[OPEN_UNION] THEN ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Sort of induction principle for connected sets.                           *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_INDUCTION = prove
 (`!P Q s:real^N->bool.
        connected s /\
        (!t a. open_in (subtopology euclidean s) t /\ a IN t
               ==> ?z. z IN t /\ P z) /\
        (!a. a IN s
             ==> ?t. open_in (subtopology euclidean s) t /\ a IN t /\
                     !x y. x IN t /\ y IN t /\ P x /\ P y /\ Q x ==> Q y)
        ==> !a b. a IN s /\ b IN s /\ P a /\ P b /\ Q a ==> Q b`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_OPEN_IN]) THEN
  REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC
   [`{b:real^N | ?t. open_in (subtopology euclidean s) t /\ b IN t /\
                     !x. x IN t /\ P x ==> Q x}`;
    `{b:real^N | ?t. open_in (subtopology euclidean s) t /\ b IN t /\
                     !x. x IN t /\ P x ==> ~(Q x)}`] THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `c:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `c:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
    X_GEN_TAC `c:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N`) THEN ASM SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    X_GEN_TAC `c:real^N` THEN DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t INTER u:real^N->bool`; `c:real^N`]) THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let CONNECTED_EQUIVALENCE_RELATION_GEN = prove
 (`!P R s:real^N->bool.
        connected s /\
        (!x y. R x y ==> R y x) /\
        (!x y z. R x y /\ R y z ==> R x z) /\
        (!t a. open_in (subtopology euclidean s) t /\ a IN t
               ==> ?z. z IN t /\ P z) /\
        (!a. a IN s
             ==> ?t. open_in (subtopology euclidean s) t /\ a IN t /\
                     !x y. x IN t /\ y IN t /\ P x /\ P y ==> R x y)
        ==> !a b. a IN s /\ b IN s /\ P a /\ P b ==> R a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a:real^N. a IN s /\ P a
               ==> !b c. b IN s /\ c IN s /\ P b /\ P c /\ R a b ==> R a c`
  MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONNECTED_INDUCTION THEN
  ASM_MESON_TAC[]);;

let CONNECTED_INDUCTION_SIMPLE = prove
 (`!P s:real^N->bool.
        connected s /\
        (!a. a IN s
             ==> ?t. open_in (subtopology euclidean s) t /\ a IN t /\
                     !x y. x IN t /\ y IN t /\ P x ==> P y)
        ==> !a b. a IN s /\ b IN s /\ P a ==> P b`,
  MP_TAC(ISPEC `\x:real^N. T` CONNECTED_INDUCTION) THEN
  REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN MESON_TAC[]);;

let CONNECTED_EQUIVALENCE_RELATION = prove
 (`!R s:real^N->bool.
        connected s /\
        (!x y. R x y ==> R y x) /\
        (!x y z. R x y /\ R y z ==> R x z) /\
        (!a. a IN s
             ==> ?t. open_in (subtopology euclidean s) t /\ a IN t /\
                     !x. x IN t ==> R a x)
        ==> !a b. a IN s /\ b IN s ==> R a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a:real^N. a IN s ==> !b c. b IN s /\ c IN s /\ R a b ==> R a c`
  MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONNECTED_INDUCTION_SIMPLE THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Limit points.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("limit_point_of",(12,"right"));;

let limit_point_of = new_definition
 `x limit_point_of s <=>
        !t. x IN t /\ open t ==> ?y. ~(y = x) /\ y IN s /\ y IN t`;;

let LIMPT_SUBSET = prove
 (`!x s t. x limit_point_of s /\ s SUBSET t ==> x limit_point_of t`,
  REWRITE_TAC[limit_point_of; SUBSET] THEN MESON_TAC[]);;

let LIMPT_APPROACHABLE = prove
 (`!x s. x limit_point_of s <=>
                !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ dist(x',x) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[limit_point_of] THEN
  MESON_TAC[open_def; DIST_SYM; OPEN_BALL; CENTRE_IN_BALL; IN_BALL]);;

let LIMPT_APPROACHABLE_LE = prove
 (`!x s. x limit_point_of s <=>
                !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ dist(x',x) <= e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  MATCH_MP_TAC(TAUT `(~a <=> ~b) ==> (a <=> b)`) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> c ==> ~(a /\ b)`; APPROACHABLE_LT_LE]);;

let LIMPT_UNIV = prove
 (`!x:real^N. x limit_point_of UNIV`,
  GEN_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE; IN_UNIV] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?c:real^N. norm(c) = e / &2` CHOOSE_TAC THENL
   [ASM_SIMP_TAC[VECTOR_CHOOSE_SIZE; REAL_HALF; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `x + c:real^N` THEN
  REWRITE_TAC[dist; VECTOR_EQ_ADDR] THEN ASM_REWRITE_TAC[VECTOR_ADD_SUB] THEN
  SUBGOAL_THEN `&0 < e / &2 /\ e / &2 < e`
   (fun th -> ASM_MESON_TAC[th; NORM_0; REAL_LT_REFL]) THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

let CLOSED_LIMPT = prove
 (`!s. closed s <=> !x. x limit_point_of s ==> x IN s`,
  REWRITE_TAC[closed] THEN ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN
  REWRITE_TAC[limit_point_of; IN_DIFF; IN_UNIV; SUBSET] THEN MESON_TAC[]);;

let LIMPT_EMPTY = prove
 (`!x. ~(x limit_point_of {})`,
  REWRITE_TAC[LIMPT_APPROACHABLE; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_01]);;

let NO_LIMIT_POINT_IMP_CLOSED = prove
 (`!s. ~(?x. x limit_point_of s) ==> closed s`,
  MESON_TAC[CLOSED_LIMPT]);;

let CLOSED_POSITIVE_ORTHANT = prove
 (`closed {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                          ==> &0 <= x$i}`,
  REWRITE_TAC[CLOSED_LIMPT; LIMPT_APPROACHABLE] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `--(x:real^N $ i)`) THEN
  ASM_REWRITE_TAC[REAL_LT_RNEG; REAL_ADD_LID; NOT_EXISTS_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  MATCH_MP_TAC(TAUT `(a ==> ~c) ==> ~(a /\ b /\ c)`) THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!b. abs x <= b /\ b <= a ==> ~(a + x < &0)`) THEN
  EXISTS_TAC `abs((y - x :real^N)$i)` THEN
  ASM_SIMP_TAC[dist; COMPONENT_LE_NORM] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; REAL_ARITH
   `x < &0 /\ &0 <= y ==> abs(x) <= abs(y - x)`]);;

let FINITE_SET_AVOID = prove
 (`!a:real^N s. FINITE s
                ==> ?d. &0 < d /\ !x. x IN s /\ ~(x = a) ==> d <= dist(a,x)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `s:real^N->bool`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `x:real^N = a` THEN REWRITE_TAC[IN_INSERT] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `min d (dist(a:real^N,x))` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; GSYM DIST_NZ; REAL_MIN_LE] THEN
  ASM_MESON_TAC[REAL_LE_REFL]);;

let LIMIT_POINT_FINITE = prove
 (`!s a. FINITE s ==> ~(a limit_point_of s)`,
  REWRITE_TAC[LIMPT_APPROACHABLE; GSYM REAL_NOT_LE] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM; REAL_NOT_LE;
    REAL_NOT_LT; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN
  MESON_TAC[FINITE_SET_AVOID; DIST_SYM]);;

let LIMPT_SING = prove
 (`!x y:real^N. ~(x limit_point_of {y})`,
  SIMP_TAC[LIMIT_POINT_FINITE; FINITE_SING]);;

let LIMIT_POINT_UNION = prove
 (`!s t x:real^N. x limit_point_of (s UNION t) <=>
                  x limit_point_of s \/ x limit_point_of t`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[LIMPT_SUBSET; SUBSET_UNION]] THEN
  REWRITE_TAC[LIMPT_APPROACHABLE; IN_UNION] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~a ==> b) ==> a \/ b`) THEN
  REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min d e`) THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_MESON_TAC[]);;

let LIMPT_INSERT = prove
 (`!s x y:real^N. x limit_point_of (y INSERT s) <=> x limit_point_of s`,
  ONCE_REWRITE_TAC[SET_RULE `y INSERT s = {y} UNION s`] THEN
  REWRITE_TAC[LIMIT_POINT_UNION] THEN
  SIMP_TAC[FINITE_SING; LIMIT_POINT_FINITE]);;

let LIMPT_OF_LIMPTS = prove
 (`!x:real^N s.
     x limit_point_of {y | y limit_point_of s} ==> x limit_point_of s`,
  REWRITE_TAC[LIMPT_APPROACHABLE; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dist(y:real^N,x)`) THEN
  ASM_SIMP_TAC[DIST_POS_LT] THEN MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC);;

let CLOSED_LIMPTS = prove
 (`!s. closed {x:real^N | x limit_point_of s}`,
  REWRITE_TAC[CLOSED_LIMPT; IN_ELIM_THM; LIMPT_OF_LIMPTS]);;

let DISCRETE_IMP_CLOSED = prove
 (`!s:real^N->bool e.
        &0 < e /\
        (!x y. x IN s /\ y IN s /\ norm(y - x) < e ==> y = x)
        ==> closed s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^N. ~(x limit_point_of s)`
    (fun th -> MESON_TAC[th; CLOSED_LIMPT]) THEN
  GEN_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  REWRITE_TAC[REAL_HALF; ASSUME `&0 < e`] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (e / &2) (dist(x:real^N,y))`) THEN
  ASM_SIMP_TAC[REAL_LT_MIN; DIST_POS_LT; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `z:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_NORM_ARITH_TAC);;

let LIMPT_OF_UNIV = prove
 (`!x. x limit_point_of (:real^N)`,
  GEN_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE; IN_UNIV] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `e / &2`] VECTOR_CHOOSE_DIST) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC NORM_ARITH);;

let LIMPT_OF_OPEN_IN = prove
 (`!s t x:real^N.
        open_in (subtopology euclidean s) t /\ x limit_point_of s /\ x IN t
        ==> x limit_point_of t`,
  REWRITE_TAC[open_in; SUBSET; LIMPT_APPROACHABLE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min d e / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let LIMPT_OF_OPEN = prove
 (`!s x:real^N. open s /\ x IN s ==> x limit_point_of s`,
  REWRITE_TAC[OPEN_IN] THEN ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
  MESON_TAC[LIMPT_OF_OPEN_IN; LIMPT_OF_UNIV]);;

let OPEN_IN_SING = prove
 (`!s a. open_in (subtopology euclidean s) {a} <=>
         a IN s /\ ~(a limit_point_of s)`,
  REWRITE_TAC[open_in; LIMPT_APPROACHABLE; SING_SUBSET; IN_SING] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Interior of a set.                                                        *)
(* ------------------------------------------------------------------------- *)

let interior = new_definition
  `interior s = {x | ?t. open t /\ x IN t /\ t SUBSET s}`;;

let INTERIOR_EQ = prove
 (`!s. (interior s = s) <=> open s`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; interior; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [OPEN_SUBOPEN] THEN MESON_TAC[SUBSET]);;

let INTERIOR_OPEN = prove
 (`!s. open s ==> (interior s = s)`,
  MESON_TAC[INTERIOR_EQ]);;

let INTERIOR_EMPTY = prove
 (`interior {} = {}`,
  SIMP_TAC[INTERIOR_OPEN; OPEN_EMPTY]);;

let INTERIOR_UNIV = prove
 (`interior(:real^N) = (:real^N)`,
  SIMP_TAC[INTERIOR_OPEN; OPEN_UNIV]);;

let OPEN_INTERIOR = prove
 (`!s. open(interior s)`,
  GEN_TAC THEN REWRITE_TAC[interior] THEN GEN_REWRITE_TAC I [OPEN_SUBOPEN] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERIOR_INTERIOR = prove
 (`!s. interior(interior s) = interior s`,
  MESON_TAC[INTERIOR_EQ; OPEN_INTERIOR]);;

let INTERIOR_SUBSET = prove
 (`!s. (interior s) SUBSET s`,
  REWRITE_TAC[SUBSET; interior; IN_ELIM_THM] THEN MESON_TAC[]);;

let SUBSET_INTERIOR = prove
 (`!s t. s SUBSET t ==> (interior s) SUBSET (interior t)`,
  REWRITE_TAC[interior; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERIOR_MAXIMAL = prove
 (`!s t. t SUBSET s /\ open t ==> t SUBSET (interior s)`,
  REWRITE_TAC[interior; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERIOR_MAXIMAL_EQ = prove
 (`!s t:real^N->bool. open s ==> (s SUBSET interior t <=> s SUBSET t)`,
  MESON_TAC[INTERIOR_MAXIMAL; SUBSET_TRANS; INTERIOR_SUBSET]);;

let INTERIOR_UNIQUE = prove
 (`!s t. t SUBSET s /\ open t /\ (!t'. t' SUBSET s /\ open t' ==> t' SUBSET t)
         ==> (interior s = t)`,
  MESON_TAC[SUBSET_ANTISYM; INTERIOR_MAXIMAL; INTERIOR_SUBSET;
            OPEN_INTERIOR]);;

let IN_INTERIOR = prove
 (`!x s. x IN interior s <=> ?e. &0 < e /\ ball(x,e) SUBSET s`,
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  MESON_TAC[OPEN_CONTAINS_BALL; SUBSET_TRANS; CENTRE_IN_BALL; OPEN_BALL]);;

let OPEN_SUBSET_INTERIOR = prove
 (`!s t. open s ==> (s SUBSET interior t <=> s SUBSET t)`,
  MESON_TAC[INTERIOR_MAXIMAL; INTERIOR_SUBSET; SUBSET_TRANS]);;

let INTERIOR_INTER = prove
 (`!s t:real^N->bool. interior(s INTER t) = interior s INTER interior t`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN REWRITE_TAC[INTER_SUBSET];
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
    MATCH_MP_TAC(SET_RULE
      `s SUBSET s' /\ t SUBSET t' ==> s INTER t SUBSET s' INTER t'`) THEN
    REWRITE_TAC[INTERIOR_SUBSET]]);;

let INTERIOR_FINITE_INTERS = prove
 (`!s:(real^N->bool)->bool.
        FINITE s ==> interior(INTERS s) = INTERS(IMAGE interior s)`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INTERS_0; INTERS_INSERT; INTERIOR_UNIV; IMAGE_CLAUSES] THEN
  SIMP_TAC[INTERIOR_INTER]);;

let INTERIOR_INTERS_SUBSET = prove
 (`!f. interior(INTERS f) SUBSET INTERS (IMAGE interior f)`,
  REWRITE_TAC[SUBSET; IN_INTERIOR; IN_INTERS; FORALL_IN_IMAGE] THEN
  MESON_TAC[]);;

let UNION_INTERIOR_SUBSET = prove
 (`!s t:real^N->bool.
        interior s UNION interior t SUBSET interior(s UNION t)`,
  SIMP_TAC[INTERIOR_MAXIMAL_EQ; OPEN_UNION; OPEN_INTERIOR] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `s SUBSET s' /\ t SUBSET t' ==> (s UNION t) SUBSET (s' UNION t')`) THEN
  REWRITE_TAC[INTERIOR_SUBSET]);;

let INTERIOR_EQ_EMPTY = prove
 (`!s:real^N->bool. interior s = {} <=> !t. open t /\ t SUBSET s ==> t = {}`,
  MESON_TAC[INTERIOR_MAXIMAL_EQ; SUBSET_EMPTY;
            OPEN_INTERIOR; INTERIOR_SUBSET]);;

let INTERIOR_EQ_EMPTY_ALT = prove
 (`!s:real^N->bool.
        interior s = {} <=>
        !t. open t /\ ~(t = {}) ==> ~(t DIFF s = {})`,
  GEN_TAC THEN REWRITE_TAC[INTERIOR_EQ_EMPTY] THEN SET_TAC[]);;

let INTERIOR_LIMIT_POINT = prove
 (`!s x:real^N. x IN interior s ==> x limit_point_of s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_INTERIOR; IN_ELIM_THM; SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN X_GEN_TAC `d:real` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `min d e / &2`] VECTOR_CHOOSE_DIST) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC;
    CONV_TAC (RAND_CONV SYM_CONV) THEN REWRITE_TAC[GSYM DIST_EQ_0];
    ONCE_REWRITE_TAC[DIST_SYM]] THEN
  ASM_REAL_ARITH_TAC);;

let INTERIOR_SING = prove
 (`!a:real^N. interior {a} = {}`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
  MESON_TAC[INTERIOR_LIMIT_POINT; LIMPT_SING]);;

let INTERIOR_CLOSED_UNION_EMPTY_INTERIOR = prove
 (`!s t:real^N->bool.
        closed(s) /\ interior(t) = {}
        ==> interior(s UNION t) = interior(s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET_INTERIOR; SUBSET_UNION] THEN
  REWRITE_TAC[SUBSET; IN_INTERIOR; IN_INTER; IN_UNION] THEN
  X_GEN_TAC `x:real^N` THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) limit_point_of s`
   (fun th -> ASM_MESON_TAC[CLOSED_LIMPT; th]) THEN
  REWRITE_TAC[IN_INTERIOR; NOT_IN_EMPTY; LIMPT_APPROACHABLE] THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?z:real^N. ~(z IN t) /\ ~(z = y) /\ dist(z,y) < d /\ dist(x,z) < e`
   (fun th -> ASM_MESON_TAC[th; IN_BALL]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_INTERIOR; NOT_IN_EMPTY; NOT_EXISTS_THM] THEN
  ABBREV_TAC `k = min d (e - dist(x:real^N,y))` THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^N. dist(y,w) = k / &2` CHOOSE_TAC THENL
   [ASM_SIMP_TAC[VECTOR_CHOOSE_DIST; REAL_HALF; REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`w:real^N`; `k / &4`]) THEN
  ASM_SIMP_TAC[SUBSET; NOT_FORALL_THM; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH;
               NOT_IMP; IN_BALL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  ASM_NORM_ARITH_TAC);;

let INTERIOR_UNION_EQ_EMPTY = prove
 (`!s t:real^N->bool.
        closed s \/ closed t
        ==> (interior(s UNION t) = {} <=>
             interior s = {} /\ interior t = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[SUBSET_UNION; SUBSET_INTERIOR; SUBSET_EMPTY];
    ASM_MESON_TAC[UNION_COMM; INTERIOR_CLOSED_UNION_EMPTY_INTERIOR]]);;

let INTERIOR_UNIONS_OPEN_SUBSETS = prove
 (`!s:real^N->bool. UNIONS {t | open t /\ t SUBSET s} = interior s`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTERIOR_UNIQUE THEN
  SIMP_TAC[OPEN_UNIONS; IN_ELIM_THM] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Closure of a set.                                                         *)
(* ------------------------------------------------------------------------- *)

let closure = new_definition
  `closure s = s UNION {x | x limit_point_of s}`;;

let CLOSURE_INTERIOR = prove
 (`!s:real^N->bool. closure s = UNIV DIFF (interior (UNIV DIFF s))`,
  REWRITE_TAC[EXTENSION; closure; IN_UNION; IN_DIFF; IN_UNIV; interior;
              IN_ELIM_THM; limit_point_of; SUBSET] THEN
  MESON_TAC[]);;

let INTERIOR_CLOSURE = prove
 (`!s:real^N->bool. interior s = UNIV DIFF (closure (UNIV DIFF s))`,
  let lemma = prove(`!s t. UNIV DIFF (UNIV DIFF t) = t`,SET_TAC[]) in
  REWRITE_TAC[CLOSURE_INTERIOR; lemma]);;

let CLOSED_CLOSURE = prove
 (`!s. closed(closure s)`,
  let lemma = prove(`UNIV DIFF (UNIV DIFF s) = s`,SET_TAC[]) in
  REWRITE_TAC[closed; CLOSURE_INTERIOR; lemma; OPEN_INTERIOR]);;

let CLOSURE_HULL = prove
 (`!s. closure s = closed hull s`,
  GEN_TAC THEN MATCH_MP_TAC(GSYM HULL_UNIQUE) THEN
  REWRITE_TAC[CLOSED_CLOSURE; SUBSET] THEN
  REWRITE_TAC[closure; IN_UNION; IN_ELIM_THM; CLOSED_LIMPT] THEN
  MESON_TAC[limit_point_of]);;

let CLOSURE_EQ = prove
 (`!s. (closure s = s) <=> closed s`,
  SIMP_TAC[CLOSURE_HULL; HULL_EQ; CLOSED_INTERS]);;

let CLOSURE_CLOSED = prove
 (`!s. closed s ==> (closure s = s)`,
  MESON_TAC[CLOSURE_EQ]);;

let CLOSURE_CLOSURE = prove
 (`!s. closure(closure s) = closure s`,
  REWRITE_TAC[CLOSURE_HULL; HULL_HULL]);;

let CLOSURE_SUBSET = prove
 (`!s. s SUBSET (closure s)`,
  REWRITE_TAC[CLOSURE_HULL; HULL_SUBSET]);;

let SUBSET_CLOSURE = prove
 (`!s t. s SUBSET t ==> (closure s) SUBSET (closure t)`,
  REWRITE_TAC[CLOSURE_HULL; HULL_MONO]);;

let CLOSURE_UNION = prove
 (`!s t:real^N->bool. closure(s UNION t) = closure s UNION closure t`,
  REWRITE_TAC[LIMIT_POINT_UNION; closure] THEN SET_TAC[]);;

let CLOSURE_INTER_SUBSET = prove
 (`!s t. closure(s INTER t) SUBSET closure(s) INTER closure(t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET_INTER] THEN
  CONJ_TAC THEN MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[]);;

let CLOSURE_INTERS_SUBSET = prove
 (`!f. closure(INTERS f) SUBSET INTERS(IMAGE closure f)`,
  REWRITE_TAC[SET_RULE `s SUBSET INTERS f <=> !t. t IN f ==> s SUBSET t`] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN ASM SET_TAC[]);;

let CLOSURE_MINIMAL = prove
 (`!s t. s SUBSET t /\ closed t ==> (closure s) SUBSET t`,
  REWRITE_TAC[HULL_MINIMAL; CLOSURE_HULL]);;

let CLOSURE_MINIMAL_EQ = prove
 (`!s t:real^N->bool. closed t ==> (closure s SUBSET t <=> s SUBSET t)`,
  MESON_TAC[SUBSET_TRANS; CLOSURE_SUBSET; CLOSURE_MINIMAL]);;

let CLOSURE_UNIQUE = prove
 (`!s t. s SUBSET t /\ closed t /\
         (!t'. s SUBSET t' /\ closed t' ==> t SUBSET t')
         ==> (closure s = t)`,
  REWRITE_TAC[CLOSURE_HULL; HULL_UNIQUE]);;

let CLOSURE_EMPTY = prove
 (`closure {} = {}`,
  SIMP_TAC[CLOSURE_CLOSED; CLOSED_EMPTY]);;

let CLOSURE_UNIV = prove
 (`closure(:real^N) = (:real^N)`,
  SIMP_TAC[CLOSURE_CLOSED; CLOSED_UNIV]);;

let CLOSURE_UNIONS = prove
 (`!f. FINITE f ==> closure(UNIONS f) = UNIONS {closure s | s IN f}`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; SET_RULE `{f x | x IN {}} = {}`;
     SET_RULE `{f x | x IN a INSERT s} = (f a) INSERT {f x | x IN s}`] THEN
  SIMP_TAC[CLOSURE_EMPTY; CLOSURE_UNION]);;

let CLOSURE_EQ_EMPTY = prove
 (`!s. closure s = {} <=> s = {}`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[CLOSURE_EMPTY] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> t = {} ==> s = {}`) THEN
  REWRITE_TAC[CLOSURE_SUBSET]);;

let CLOSURE_SUBSET_EQ = prove
 (`!s:real^N->bool. closure s SUBSET s <=> closed s`,
  GEN_TAC THEN REWRITE_TAC[GSYM CLOSURE_EQ] THEN
  MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN SET_TAC[]);;

let OPEN_INTER_CLOSURE_EQ_EMPTY = prove
 (`!s t:real^N->bool.
        open s ==> (s INTER (closure t) = {} <=> s INTER t = {})`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MP_TAC(ISPEC `t:real^N->bool` CLOSURE_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[CLOSURE_INTERIOR] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s INTER (UNIV DIFF t) = {}`) THEN
  ASM_SIMP_TAC[OPEN_SUBSET_INTERIOR] THEN ASM SET_TAC[]);;

let OPEN_INTER_CLOSURE_SUBSET = prove
 (`!s t:real^N->bool.
        open s ==> (s INTER (closure t)) SUBSET closure(s INTER t)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[SUBSET; IN_INTER; closure; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIMPT_APPROACHABLE]) THEN
  DISCH_THEN(MP_TAC o SPEC `min d e`) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; IN_INTER] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]);;

let CLOSURE_OPEN_INTER_SUPERSET = prove
 (`!s t:real^N->bool.
        open s /\ s SUBSET closure t ==> closure(s INTER t) = closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET_CLOSURE; INTER_SUBSET] THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
  W(MP_TAC o PART_MATCH (rand o rand)
    OPEN_INTER_CLOSURE_SUBSET o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN ASM SET_TAC[]);;

let CLOSURE_COMPLEMENT = prove
 (`!s:real^N->bool. closure(UNIV DIFF s) = UNIV DIFF interior(s)`,
  REWRITE_TAC[SET_RULE `s = UNIV DIFF t <=> UNIV DIFF s = t`] THEN
  REWRITE_TAC[GSYM INTERIOR_CLOSURE]);;

let INTERIOR_COMPLEMENT = prove
 (`!s:real^N->bool. interior(UNIV DIFF s) = UNIV DIFF closure(s)`,
  REWRITE_TAC[SET_RULE `s = UNIV DIFF t <=> UNIV DIFF s = t`] THEN
  REWRITE_TAC[GSYM CLOSURE_INTERIOR]);;

let CONNECTED_INTERMEDIATE_CLOSURE = prove
 (`!s t:real^N->bool.
        connected s /\ s SUBSET t /\ t SUBSET closure s ==> connected t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `v:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASSUME_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[GSYM DE_MORGAN_THM] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(closure s) SUBSET ((:real^N) DIFF u)` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[GSYM OPEN_CLOSED];
      ALL_TAC];
    SUBGOAL_THEN `(closure s) SUBSET ((:real^N) DIFF v)` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[GSYM OPEN_CLOSED];
      ALL_TAC]] THEN
  ASM SET_TAC[]);;

let CONNECTED_CLOSURE = prove
 (`!s:real^N->bool. connected s ==> connected(closure s)`,
  MESON_TAC[CONNECTED_INTERMEDIATE_CLOSURE; CLOSURE_SUBSET; SUBSET_REFL]);;

let CONNECTED_UNION_STRONG = prove
 (`!s t:real^N->bool.
        connected s /\ connected t /\ ~(closure s INTER t = {})
        ==> connected(s UNION t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `p:real^N`) THEN
  SUBGOAL_THEN `s UNION t = ((p:real^N) INSERT s) UNION t` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let INTERIOR_DIFF = prove
 (`!s t. interior(s DIFF t) = interior(s) DIFF closure(t)`,
  ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
  REWRITE_TAC[INTERIOR_INTER; CLOSURE_INTERIOR] THEN SET_TAC[]);;

let LIMPT_OF_CLOSURE = prove
 (`!x:real^N s. x limit_point_of closure s <=> x limit_point_of s`,
  REWRITE_TAC[closure; IN_UNION; IN_ELIM_THM; LIMIT_POINT_UNION] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT `(q ==> p) ==> (p \/ q <=> p)`) THEN
  REWRITE_TAC[LIMPT_OF_LIMPTS]);;

let CLOSED_IN_LIMPT = prove
 (`!s t. closed_in (subtopology euclidean t) s <=>
         s SUBSET t /\ !x:real^N. x limit_point_of s /\ x IN t ==> x IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSED] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[IN_INTER] THEN
    ASM_MESON_TAC[CLOSED_LIMPT; LIMPT_SUBSET; INTER_SUBSET];
    STRIP_TAC THEN EXISTS_TAC `closure s :real^N->bool` THEN
    REWRITE_TAC[CLOSED_CLOSURE] THEN REWRITE_TAC[closure] THEN
    ASM SET_TAC[]]);;

let CLOSED_IN_INTER_CLOSURE = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean s) t <=> s INTER closure t = t`,
  REWRITE_TAC[closure; CLOSED_IN_LIMPT] THEN SET_TAC[]);;

let INTERIOR_CLOSURE_IDEMP = prove
 (`!s:real^N->bool.
        interior(closure(interior(closure s))) = interior(closure s)`,
  GEN_TAC THEN MATCH_MP_TAC INTERIOR_UNIQUE THEN
  ASM_MESON_TAC[OPEN_INTERIOR; CLOSURE_SUBSET; CLOSURE_CLOSURE; SUBSET_TRANS;
                OPEN_SUBSET_INTERIOR;SUBSET_CLOSURE; INTERIOR_SUBSET]);;

let CLOSURE_INTERIOR_IDEMP = prove
 (`!s:real^N->bool.
        closure(interior(closure(interior s))) = closure(interior s)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `s = t <=> UNIV DIFF s = UNIV DIFF t`] THEN
  REWRITE_TAC[GSYM INTERIOR_COMPLEMENT; GSYM CLOSURE_COMPLEMENT] THEN
  REWRITE_TAC[INTERIOR_CLOSURE_IDEMP]);;

let NOWHERE_DENSE_UNION = prove
 (`!s t:real^N->bool.
        interior(closure(s UNION t)) = {} <=>
        interior(closure s) = {} /\ interior(closure t) = {}`,
  SIMP_TAC[CLOSURE_UNION; INTERIOR_UNION_EQ_EMPTY; CLOSED_CLOSURE]);;

let NOWHERE_DENSE = prove
 (`!s:real^N->bool.
        interior(closure s) = {} <=>
        !t. open t /\ ~(t = {})
            ==> ?u. open u /\ ~(u = {}) /\ u SUBSET t /\ u INTER s = {}`,
  GEN_TAC THEN REWRITE_TAC[INTERIOR_EQ_EMPTY_ALT] THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THENL
   [EXISTS_TAC `t DIFF closure s:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_DIFF; CLOSED_CLOSURE] THEN
    MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`u:real^N->bool`; `s:real^N->bool`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM SET_TAC[]]);;

let INTERIOR_CLOSURE_INTER_OPEN = prove
 (`!s t:real^N->bool.
        open s /\ open t
        ==> interior(closure(s INTER t)) =
            interior(closure s) INTER interior(closure t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_RULE
   `u = s INTER t <=> s INTER t SUBSET u /\ u SUBSET s /\ u SUBSET t`] THEN
  SIMP_TAC[SUBSET_INTERIOR; SUBSET_CLOSURE; INTER_SUBSET] THEN
  MATCH_MP_TAC INTERIOR_MAXIMAL THEN SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
  REWRITE_TAC[SET_RULE `s SUBSET t <=> s INTER (UNIV DIFF t) = {}`;
              GSYM INTERIOR_COMPLEMENT] THEN
  REWRITE_TAC[GSYM INTERIOR_INTER] THEN
  REWRITE_TAC[INTERIOR_EQ_EMPTY] THEN
  X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u INTER s:real^N->bool`; `t:real^N->bool`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `s:real^N->bool`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
  ASM_SIMP_TAC[OPEN_INTER] THEN ASM SET_TAC[]);;

let CLOSURE_INTERIOR_UNION_CLOSED = prove
 (`!s t:real^N->bool.
        closed s /\ closed t
        ==> closure(interior(s UNION t)) =
            closure(interior s) UNION closure(interior t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[closed] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTERIOR_CLOSURE_INTER_OPEN) THEN
  REWRITE_TAC[CLOSURE_COMPLEMENT; INTERIOR_COMPLEMENT;
              SET_RULE `(UNIV DIFF s) INTER (UNIV DIFF t) =
                        UNIV DIFF (s UNION t)`] THEN
  SET_TAC[]);;

let REGULAR_OPEN_INTER = prove
 (`!s t:real^N->bool.
        interior(closure s) = s /\ interior(closure t) = t
        ==> interior(closure(s INTER t)) = s INTER t`,
  MESON_TAC[INTERIOR_CLOSURE_INTER_OPEN; OPEN_INTERIOR]);;

let REGULAR_CLOSED_UNION = prove
 (`!s t:real^N->bool.
        closure(interior s) = s /\ closure(interior t) = t
        ==> closure(interior(s UNION t)) = s UNION t`,
  MESON_TAC[CLOSURE_INTERIOR_UNION_CLOSED; CLOSED_CLOSURE]);;

let DIFF_CLOSURE_SUBSET = prove
 (`!s t:real^N->bool. closure(s) DIFF closure t SUBSET closure(s DIFF t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^N) DIFF closure t`; `s:real^N->bool`]
        OPEN_INTER_CLOSURE_SUBSET) THEN
  REWRITE_TAC[SET_RULE `(UNIV DIFF t) INTER s = s DIFF t`] THEN
  REWRITE_TAC[GSYM closed; CLOSED_CLOSURE] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN
  MATCH_MP_TAC(SET_RULE `t SUBSET u ==> s DIFF u SUBSET s DIFF t`) THEN
  REWRITE_TAC[CLOSURE_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Frontier (aka boundary).                                                  *)
(* ------------------------------------------------------------------------- *)

let frontier = new_definition
  `frontier s = (closure s) DIFF (interior s)`;;

let FRONTIER_CLOSED = prove
 (`!s. closed(frontier s)`,
  SIMP_TAC[frontier; CLOSED_DIFF; CLOSED_CLOSURE; OPEN_INTERIOR]);;

let FRONTIER_CLOSURES = prove
 (`!s:real^N->bool. frontier s = (closure s) INTER (closure(UNIV DIFF s))`,
  let lemma = prove(`s DIFF (UNIV DIFF t) = s INTER t`,SET_TAC[]) in
  REWRITE_TAC[frontier; INTERIOR_CLOSURE; lemma]);;

let FRONTIER_STRADDLE = prove
 (`!a:real^N s.
     a IN frontier s <=>
        !e. &0 < e ==> (?x. x IN s /\ dist(a,x) < e) /\
                       (?x. ~(x IN s) /\ dist(a,x) < e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRONTIER_CLOSURES; IN_INTER] THEN
  REWRITE_TAC[closure; IN_UNION; IN_ELIM_THM; limit_point_of;
              IN_UNIV; IN_DIFF] THEN
  ASM_MESON_TAC[IN_BALL; SUBSET; OPEN_CONTAINS_BALL;
                CENTRE_IN_BALL; OPEN_BALL; DIST_REFL]);;

let FRONTIER_SUBSET_CLOSED = prove
 (`!s. closed s ==> (frontier s) SUBSET s`,
  MESON_TAC[frontier; CLOSURE_CLOSED; SUBSET_DIFF]);;

let FRONTIER_EMPTY = prove
 (`frontier {} = {}`,
  REWRITE_TAC[frontier; CLOSURE_EMPTY; EMPTY_DIFF]);;

let FRONTIER_UNIV = prove
 (`frontier(:real^N) = {}`,
  REWRITE_TAC[frontier; CLOSURE_UNIV; INTERIOR_UNIV] THEN SET_TAC[]);;

let FRONTIER_SUBSET_EQ = prove
 (`!s:real^N->bool. (frontier s) SUBSET s <=> closed s`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[FRONTIER_SUBSET_CLOSED] THEN
  REWRITE_TAC[frontier] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `s DIFF t SUBSET u ==> t SUBSET u ==> s SUBSET u`)) THEN
  REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET_EQ]);;

let FRONTIER_COMPLEMENT = prove
 (`!s:real^N->bool. frontier(UNIV DIFF s) = frontier s`,
  REWRITE_TAC[frontier; CLOSURE_COMPLEMENT; INTERIOR_COMPLEMENT] THEN
  SET_TAC[]);;

let FRONTIER_DISJOINT_EQ = prove
 (`!s. (frontier s) INTER s = {} <=> open s`,
  ONCE_REWRITE_TAC[GSYM FRONTIER_COMPLEMENT; OPEN_CLOSED] THEN
  REWRITE_TAC[GSYM FRONTIER_SUBSET_EQ] THEN SET_TAC[]);;

let FRONTIER_INTER_SUBSET = prove
 (`!s t. frontier(s INTER t) SUBSET frontier(s) UNION frontier(t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frontier; INTERIOR_INTER] THEN
  MATCH_MP_TAC(SET_RULE
   `cst SUBSET cs INTER ct
    ==> cst DIFF (s INTER t) SUBSET (cs DIFF s) UNION (ct DIFF t)`) THEN
  REWRITE_TAC[CLOSURE_INTER_SUBSET]);;

let FRONTIER_UNION_SUBSET = prove
 (`!s t:real^N->bool. frontier(s UNION t) SUBSET frontier s UNION frontier t`,
  ONCE_REWRITE_TAC[GSYM FRONTIER_COMPLEMENT] THEN
  REWRITE_TAC[SET_RULE `u DIFF (s UNION t) = (u DIFF s) INTER (u DIFF t)`] THEN
  REWRITE_TAC[FRONTIER_INTER_SUBSET]);;

let FRONTIER_INTERIORS = prove
 (`!s. frontier s = (:real^N) DIFF interior(s) DIFF interior((:real^N) DIFF s)`,
  REWRITE_TAC[frontier; CLOSURE_INTERIOR] THEN SET_TAC[]);;

let FRONTIER_FRONTIER_SUBSET = prove
 (`!s:real^N->bool. frontier(frontier s) SUBSET frontier s`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [frontier] THEN
  SIMP_TAC[CLOSURE_CLOSED; FRONTIER_CLOSED] THEN SET_TAC[]);;

let INTERIOR_FRONTIER = prove
 (`!s:real^N->bool.
        interior(frontier s) = interior(closure s) DIFF closure(interior s)`,
  ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
  REWRITE_TAC[GSYM INTERIOR_COMPLEMENT; GSYM INTERIOR_INTER; frontier] THEN
  GEN_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let INTERIOR_FRONTIER_EMPTY = prove
 (`!s:real^N->bool. open s \/ closed s ==> interior(frontier s) = {}`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[INTERIOR_FRONTIER] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED; INTERIOR_OPEN] THEN
  REWRITE_TAC[SET_RULE `s DIFF t = {} <=> s SUBSET t`] THEN
  REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET]);;

let FRONTIER_FRONTIER = prove
 (`!s:real^N->bool. open s \/ closed s ==> frontier(frontier s) = frontier s`,
  GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [frontier] THEN
  SIMP_TAC[INTERIOR_FRONTIER_EMPTY; CLOSURE_CLOSED; FRONTIER_CLOSED] THEN
  REWRITE_TAC[DIFF_EMPTY]);;

let FRONTIER_FRONTIER_FRONTIER = prove
 (`!s:real^N->bool. frontier(frontier(frontier s)) = frontier(frontier s)`,
  SIMP_TAC[FRONTIER_FRONTIER; FRONTIER_CLOSED]);;

let UNION_FRONTIER = prove
 (`!s t:real^N->bool.
        frontier(s) UNION frontier(t) =
        frontier(s UNION t) UNION
        frontier(s INTER t) UNION
        frontier(s) INTER frontier(t)`,
  let lemma = prove
   (`!s t x. x IN frontier s /\ x IN interior t ==> x IN frontier(s INTER t)`,
    REWRITE_TAC[FRONTIER_STRADDLE; IN_INTER; IN_INTERIOR; SUBSET; IN_BALL] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `d:real`)) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `min d e:real`) THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_MESON_TAC[]) in
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; UNION_SUBSET;
              FRONTIER_UNION_SUBSET; FRONTIER_INTER_SUBSET;
              SET_RULE `s INTER t SUBSET s UNION t`] THEN
  REWRITE_TAC[GSYM UNION_SUBSET] THEN REWRITE_TAC[SUBSET; IN_UNION] THEN
  MATCH_MP_TAC(MESON[]
   `(!s t x. P s x ==> R x s t) /\ (!s t x. R x s t <=> R x t s)
    ==> (!s t x. P s x \/ P t x ==> R x s t)`) THEN
  CONJ_TAC THENL [REPEAT STRIP_TAC; REWRITE_TAC[UNION_COMM; INTER_COMM]] THEN
  ASM_CASES_TAC `(x:real^N) IN frontier t` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (RAND_CONV o RAND_CONV)
        [FRONTIER_INTERIORS]) THEN
  REWRITE_TAC[DE_MORGAN_THM; IN_DIFF; IN_UNIV] THEN
  GEN_REWRITE_TAC RAND_CONV [DISJ_SYM] THEN MATCH_MP_TAC MONO_OR THEN
  ASM_SIMP_TAC[lemma] THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM FRONTIER_COMPLEMENT] THEN
  SIMP_TAC[lemma; SET_RULE
    `UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)`]);;

let CONNECTED_INTER_FRONTIER = prove
 (`!s t:real^N->bool.
        connected s /\ ~(s INTER t = {}) /\ ~(s DIFF t = {})
        ==> ~(s INTER frontier t = {})`,
  REWRITE_TAC[FRONTIER_INTERIORS] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_OPEN_IN]) THEN
  REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC
   [`s INTER interior t:real^N->bool`;
    `s INTER (interior((:real^N) DIFF t))`] THEN
  SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_INTERIOR] THEN
  MAP_EVERY (MP_TAC o C ISPEC INTERIOR_SUBSET)
   [`t:real^N->bool`; `(:real^N) DIFF t`] THEN
  ASM SET_TAC[]);;

let INTERIOR_CLOSED_EQ_EMPTY_AS_FRONTIER = prove
 (`!s:real^N->bool.
        closed s /\ interior s = {} <=> ?t. open t /\ s = frontier t`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `(:real^N) DIFF s` THEN
    ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; FRONTIER_COMPLEMENT] THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; DIFF_EMPTY];
    ASM_SIMP_TAC[FRONTIER_CLOSED; INTERIOR_FRONTIER_EMPTY]]);;

let FRONTIER_UNION = prove
 (`!s t:real^N->bool.
        closure s INTER closure t = {}
        ==> frontier(s UNION t) = frontier(s) UNION frontier(t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[FRONTIER_UNION_SUBSET] THEN
  GEN_REWRITE_TAC RAND_CONV [frontier] THEN
  REWRITE_TAC[CLOSURE_UNION] THEN MATCH_MP_TAC(SET_RULE
   `(fs SUBSET cs /\ ft SUBSET ct) /\ k INTER fs = {} /\ k INTER ft = {}
    ==> (fs UNION ft) SUBSET (cs UNION ct) DIFF k`) THEN
  CONJ_TAC THENL [REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[UNION_COMM] THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[INTER_COMM])] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `s INTER t = {} ==> s' SUBSET s /\ s' INTER u INTER (UNIV DIFF t) = {}
      ==> u INTER s' = {}`)) THEN
  REWRITE_TAC[frontier; SUBSET_DIFF; GSYM INTERIOR_COMPLEMENT] THEN
  REWRITE_TAC[GSYM INTERIOR_INTER; SET_RULE
   `(s UNION t) INTER (UNIV DIFF t) = s DIFF t`] THEN
  MATCH_MP_TAC(SET_RULE
    `ti SUBSET si ==> (c DIFF si) INTER ti = {}`) THEN
  SIMP_TAC[SUBSET_INTERIOR; SUBSET_DIFF]);;

let CLOSURE_UNION_FRONTIER = prove
 (`!s:real^N->bool. closure s = s UNION frontier s`,
  GEN_TAC THEN REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN
  SET_TAC[]);;

let FRONTIER_INTERIOR_SUBSET = prove
 (`!s:real^N->bool. frontier(interior s) SUBSET frontier s`,
  GEN_TAC THEN REWRITE_TAC[frontier; INTERIOR_INTERIOR] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF u SUBSET t DIFF u`) THEN
  SIMP_TAC[SUBSET_CLOSURE; INTERIOR_SUBSET]);;

let FRONTIER_CLOSURE_SUBSET = prove
 (`!s:real^N->bool. frontier(closure s) SUBSET frontier s`,
  GEN_TAC THEN REWRITE_TAC[frontier; CLOSURE_CLOSURE] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> u DIFF t SUBSET u DIFF s`) THEN
  SIMP_TAC[SUBSET_INTERIOR; CLOSURE_SUBSET]);;

let SET_DIFF_FRONTIER = prove
 (`!s:real^N->bool. s DIFF frontier s = interior s`,
  GEN_TAC THEN REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN
  SET_TAC[]);;

let FRONTIER_INTER_SUBSET_INTER = prove
 (`!s t:real^N->bool.
        frontier(s INTER t) SUBSET closure s INTER frontier t UNION
                                   frontier s INTER closure t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frontier; INTERIOR_INTER] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
        CLOSURE_INTER_SUBSET) THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A variant of nets (slightly non-standard but good for our purposes).      *)
(* ------------------------------------------------------------------------- *)

let net_tybij = new_type_definition "net" ("mk_net","netord")
 (prove
   (`?g:A->A->bool. !x y. (!z. g z x ==> g z y) \/ (!z. g z y ==> g z x)`,
    EXISTS_TAC `\x:A y:A. F` THEN REWRITE_TAC[]));;

let NET = prove
 (`!n x y. (!z. netord n z x ==> netord n z y) \/
           (!z. netord n z y ==> netord n z x)`,
   REWRITE_TAC[net_tybij; ETA_AX]);;

let OLDNET = prove
 (`!n x y. netord n x x /\ netord n y y
           ==> ?z. netord n z z /\
                   !w. netord n w z ==> netord n w x /\ netord n w y`,
  MESON_TAC[NET]);;

let NET_DILEMMA = prove
 (`!net. (?a. (?x. netord net x a) /\ (!x. netord net x a ==> P x)) /\
         (?b. (?x. netord net x b) /\ (!x. netord net x b ==> Q x))
         ==> ?c. (?x. netord net x c) /\ (!x. netord net x c ==> P x /\ Q x)`,
  MESON_TAC[NET]);;

(* ------------------------------------------------------------------------- *)
(* Common nets and the "within" modifier for nets.                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("within",(14,"right"));;
parse_as_infix("in_direction",(14,"right"));;

let at = new_definition
  `at a = mk_net(\x y. &0 < dist(x,a) /\ dist(x,a) <= dist(y,a))`;;

let at_infinity = new_definition
  `at_infinity = mk_net(\x y. norm(x) >= norm(y))`;;

let at_posinfinity = new_definition
  `at_posinfinity = mk_net(\x y:real. x >= y)`;;

let at_neginfinity = new_definition
  `at_neginfinity = mk_net(\x y:real. x <= y)`;;

let sequentially = new_definition
  `sequentially = mk_net(\m:num n. m >= n)`;;

let within = new_definition
  `net within s = mk_net(\x y. netord net x y /\ x IN s)`;;

let in_direction = new_definition
  `a in_direction v = (at a) within {b | ?c. &0 <= c /\ (b - a = c % v)}`;;

(* ------------------------------------------------------------------------- *)
(* Prove that they are all nets.                                             *)
(* ------------------------------------------------------------------------- *)

let NET_PROVE_TAC[def] =
  REWRITE_TAC[GSYM FUN_EQ_THM; def] THEN
  REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[GSYM(CONJUNCT2 net_tybij)];;

let AT = prove
 (`!a:real^N x y.
        netord(at a) x y <=> &0 < dist(x,a) /\ dist(x,a) <= dist(y,a)`,
  GEN_TAC THEN NET_PROVE_TAC[at] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS; REAL_LET_TRANS]);;

let AT_INFINITY = prove
 (`!x y. netord at_infinity x y <=> norm(x) >= norm(y)`,
  NET_PROVE_TAC[at_infinity] THEN
  REWRITE_TAC[real_ge; REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS]);;

let AT_POSINFINITY = prove
 (`!x y. netord at_posinfinity x y <=> x >= y`,
  NET_PROVE_TAC[at_posinfinity] THEN
  REWRITE_TAC[real_ge; REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS]);;

let AT_NEGINFINITY = prove
 (`!x y. netord at_neginfinity x y <=> x <= y`,
  NET_PROVE_TAC[at_neginfinity] THEN
  REWRITE_TAC[real_ge; REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS]);;

let SEQUENTIALLY = prove
 (`!m n. netord sequentially m n <=> m >= n`,
  NET_PROVE_TAC[sequentially] THEN REWRITE_TAC[GE; LE_REFL] THEN
  MESON_TAC[LE_CASES; LE_REFL; LE_TRANS]);;

let WITHIN = prove
 (`!n s x y. netord(n within s) x y <=> netord n x y /\ x IN s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[within; GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 net_tybij); ETA_AX] THEN
  MESON_TAC[NET]);;

let IN_DIRECTION = prove
 (`!a v x y. netord(a in_direction v) x y <=>
                &0 < dist(x,a) /\ dist(x,a) <= dist(y,a) /\
                 ?c. &0 <= c /\ (x - a = c % v)`,
  REWRITE_TAC[WITHIN; AT; in_direction; IN_ELIM_THM; CONJ_ACI]);;

let WITHIN_UNIV = prove
 (`!x:real^N. at x within UNIV = at x`,
  REWRITE_TAC[within; at; IN_UNIV] THEN REWRITE_TAC[ETA_AX; net_tybij]);;

let WITHIN_WITHIN = prove
 (`!net s t. (net within s) within t = net within (s INTER t)`,
  ONCE_REWRITE_TAC[within] THEN
  REWRITE_TAC[WITHIN; IN_INTER; GSYM CONJ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Identify trivial limits, where we can't approach arbitrarily closely.     *)
(* ------------------------------------------------------------------------- *)

let trivial_limit = new_definition
  `trivial_limit net <=>
     (!a:A b. a = b) \/
     ?a:A b. ~(a = b) /\ !x. ~(netord(net) x a) /\ ~(netord(net) x b)`;;

let TRIVIAL_LIMIT_WITHIN = prove
 (`!a:real^N. trivial_limit (at a within s) <=> ~(a limit_point_of s)`,
  REWRITE_TAC[trivial_limit; LIMPT_APPROACHABLE_LE; WITHIN; AT; DIST_NZ] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [MESON_TAC[REAL_LT_01; REAL_LT_REFL; VECTOR_CHOOSE_DIST;
                DIST_REFL; REAL_LT_IMP_LE];
      DISCH_THEN(X_CHOOSE_THEN `b:real^N` (X_CHOOSE_THEN `c:real^N`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `&0 < dist(a,b:real^N) \/ &0 < dist(a,c:real^N)` MP_TAC THEN
      ASM_MESON_TAC[DIST_TRIANGLE; DIST_SYM; GSYM DIST_NZ; GSYM DIST_EQ_0;
                    REAL_ARITH `x <= &0 + &0 ==> ~(&0 < x)`]];
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN DISJ2_TAC THEN
    EXISTS_TAC `a:real^N` THEN
    SUBGOAL_THEN `?b:real^N. dist(a,b) = e` MP_TAC THENL
     [ASM_SIMP_TAC[VECTOR_CHOOSE_DIST; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_MESON_TAC[REAL_NOT_LE; DIST_REFL; DIST_NZ; DIST_SYM]]);;

let TRIVIAL_LIMIT_AT = prove
 (`!a. ~(trivial_limit (at a))`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[TRIVIAL_LIMIT_WITHIN; LIMPT_UNIV]);;

let TRIVIAL_LIMIT_AT_INFINITY = prove
 (`~(trivial_limit at_infinity)`,
  REWRITE_TAC[trivial_limit; AT_INFINITY; real_ge] THEN
  MESON_TAC[REAL_LE_REFL; VECTOR_CHOOSE_SIZE; REAL_LT_01; REAL_LT_LE]);;

let TRIVIAL_LIMIT_AT_POSINFINITY = prove
 (`~(trivial_limit at_posinfinity)`,
  REWRITE_TAC[trivial_limit; AT_POSINFINITY; DE_MORGAN_THM] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM; real_ge; REAL_NOT_LE] THEN
  MESON_TAC[REAL_LT_TOTAL; REAL_LT_ANTISYM]);;

let TRIVIAL_LIMIT_AT_NEGINFINITY = prove
 (`~(trivial_limit at_neginfinity)`,
  REWRITE_TAC[trivial_limit; AT_NEGINFINITY; DE_MORGAN_THM] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM; real_ge; REAL_NOT_LE] THEN
  MESON_TAC[REAL_LT_TOTAL; REAL_LT_ANTISYM]);;

let TRIVIAL_LIMIT_SEQUENTIALLY = prove
 (`~(trivial_limit sequentially)`,
  REWRITE_TAC[trivial_limit; SEQUENTIALLY] THEN
  MESON_TAC[GE_REFL; NOT_SUC]);;

let LIM_WITHIN_CLOSED_TRIVIAL = prove
 (`!a s. closed s /\ ~(a IN s) ==> trivial_limit (at a within s)`,
  REWRITE_TAC[TRIVIAL_LIMIT_WITHIN] THEN MESON_TAC[CLOSED_LIMPT]);;

let NONTRIVIAL_LIMIT_WITHIN = prove
 (`!net s. trivial_limit net ==> trivial_limit(net within s)`,
  REWRITE_TAC[trivial_limit; WITHIN] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some property holds "sufficiently close" to the limit point.              *)
(* ------------------------------------------------------------------------- *)

let eventually = new_definition
 `eventually p net <=>
        trivial_limit net \/
        ?y. (?x. netord net x y) /\ (!x. netord net x y ==> p x)`;;

let EVENTUALLY_HAPPENS = prove
 (`!net p. eventually p net ==> trivial_limit net \/ ?x. p x`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_WITHIN_LE = prove
 (`!s a:real^M p.
     eventually p (at a within s) <=>
        ?d. &0 < d /\ !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) <= d ==> p(x)`,
  REWRITE_TAC[eventually; AT; WITHIN; TRIVIAL_LIMIT_WITHIN] THEN
  REWRITE_TAC[LIMPT_APPROACHABLE_LE; DIST_NZ] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[REAL_LTE_TRANS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `(a ==> b) ==> ~a \/ b`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?b:real^M. dist(a,b) = d` MP_TAC THENL
   [ASM_SIMP_TAC[VECTOR_CHOOSE_DIST; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^M` THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_MESON_TAC[REAL_NOT_LE; DIST_REFL; DIST_NZ; DIST_SYM]);;

let EVENTUALLY_WITHIN = prove
 (`!s a:real^M p.
     eventually p (at a within s) <=>
        ?d. &0 < d /\ !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) < d ==> p(x)`,
  REWRITE_TAC[EVENTUALLY_WITHIN_LE] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`] THEN
  REWRITE_TAC[APPROACHABLE_LT_LE]);;

let EVENTUALLY_AT = prove
 (`!a p. eventually p (at a) <=>
         ?d. &0 < d /\ !x. &0 < dist(x,a) /\ dist(x,a) < d ==> p(x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[EVENTUALLY_WITHIN; IN_UNIV]);;

let EVENTUALLY_SEQUENTIALLY = prove
 (`!p. eventually p sequentially <=> ?N. !n. N <= n ==> p n`,
  REWRITE_TAC[eventually; SEQUENTIALLY; GE; LE_REFL;
    TRIVIAL_LIMIT_SEQUENTIALLY] THEN  MESON_TAC[LE_REFL]);;

let EVENTUALLY_AT_INFINITY = prove
 (`!p. eventually p at_infinity <=> ?b. !x. norm(x) >= b ==> p x`,
  REWRITE_TAC[eventually; AT_INFINITY; TRIVIAL_LIMIT_AT_INFINITY] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MESON_TAC[real_ge; REAL_LE_REFL; VECTOR_CHOOSE_SIZE;
    REAL_ARITH `&0 <= b \/ (!x. x >= &0 ==> x >= b)`]);;

let EVENTUALLY_AT_POSINFINITY = prove
 (`!p. eventually p at_posinfinity <=> ?b. !x. x >= b ==> p x`,
  REWRITE_TAC[eventually; TRIVIAL_LIMIT_AT_POSINFINITY; AT_POSINFINITY] THEN
  MESON_TAC[REAL_ARITH `x >= x`]);;

let EVENTUALLY_AT_NEGINFINITY = prove
 (`!p. eventually p at_neginfinity <=> ?b. !x. x <= b ==> p x`,
  REWRITE_TAC[eventually; TRIVIAL_LIMIT_AT_NEGINFINITY; AT_NEGINFINITY] THEN
  MESON_TAC[REAL_LE_REFL]);;

let EVENTUALLY_AT_INFINITY_POS = prove
 (`!p:real^N->bool.
        eventually p at_infinity <=> ?b. &0 < b /\ !x. norm x >= b ==> p x`,
  GEN_TAC THEN REWRITE_TAC[EVENTUALLY_AT_INFINITY; real_ge] THEN
  MESON_TAC[REAL_ARITH `&0 < abs b + &1 /\ (abs b + &1 <= x ==> b <= x)`]);;

let ALWAYS_EVENTUALLY = prove
 (`(!x. p x) ==> eventually p net`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[eventually; trivial_limit] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for "eventually".                                      *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_AND = prove
 (`!net:(A net) p q.
        eventually (\x. p x /\ q x) net <=>
        eventually p net /\ eventually q net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eventually] THEN
  ASM_CASES_TAC `trivial_limit(net:(A net))` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN SIMP_TAC[NET_DILEMMA] THEN MESON_TAC[]);;

let EVENTUALLY_MONO = prove
 (`!net:(A net) p q.
        (!x. p x ==> q x) /\ eventually p net
        ==> eventually q net`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_MP = prove
 (`!net:(A net) p q.
        eventually (\x. p x ==> q x) net /\ eventually p net
        ==> eventually q net`,
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_FALSE = prove
 (`!net. eventually (\x. F) net <=> trivial_limit net`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_TRUE = prove
 (`!net. eventually (\x. T) net <=> T`,
  REWRITE_TAC[eventually; trivial_limit] THEN MESON_TAC[]);;

let NOT_EVENTUALLY = prove
 (`!net p. (!x. ~(p x)) /\ ~(trivial_limit net) ==> ~(eventually p net)`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_FORALL = prove
 (`!net:(A net) p s:B->bool.
        FINITE s /\ ~(s = {})
        ==> (eventually (\x. !a. a IN s ==> p a x) net <=>
             !a. a IN s ==> eventually (p a) net)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[FORALL_IN_INSERT; EVENTUALLY_AND; ETA_AX] THEN
  MAP_EVERY X_GEN_TAC [`b:B`; `t:B->bool`] THEN
  ASM_CASES_TAC `t:B->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; EVENTUALLY_TRUE]);;

let FORALL_EVENTUALLY = prove
 (`!net:(A net) p s:B->bool.
        FINITE s /\ ~(s = {})
        ==> ((!a. a IN s ==> eventually (p a) net) <=>
             eventually (\x. !a. a IN s ==> p a x) net)`,
  SIMP_TAC[EVENTUALLY_FORALL]);;

(* ------------------------------------------------------------------------- *)
(* Limits, defined as vacuously true when the limit is trivial.              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("-->",(12,"right"));;

let tendsto = new_definition
  `(f --> l) net <=> !e. &0 < e ==> eventually (\x. dist(f(x),l) < e) net`;;

let lim = new_definition
 `lim net f = @l. (f --> l) net`;;

let LIM = prove
 (`(f --> l) net <=>
        trivial_limit net \/
        !e. &0 < e ==> ?y. (?x. netord(net) x y) /\
                           !x. netord(net) x y ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; eventually] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Show that they yield usual definitions in the various cases.              *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_LE = prove
 (`!f:real^M->real^N l a s.
        (f --> l)(at a within s) <=>
           !e. &0 < e ==> ?d. &0 < d /\
                              !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) <= d
                                   ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_WITHIN_LE]);;

let LIM_WITHIN = prove
 (`!f:real^M->real^N l a s.
      (f --> l) (at a within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) < d
                    ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_WITHIN] THEN MESON_TAC[]);;

let LIM_AT_LE = prove
 (`!f l a. (f --> l) (at a) <=>
           !e. &0 < e
               ==> ?d. &0 < d /\
                       !x. &0 < dist(x,a) /\ dist(x,a) <= d
                           ==> dist (f x,l) < e`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[LIM_WITHIN_LE; IN_UNIV]);;

let LIM_AT = prove
 (`!f l:real^N a:real^M.
      (f --> l) (at a) <=>
              !e. &0 < e
                  ==> ?d. &0 < d /\ !x. &0 < dist(x,a) /\ dist(x,a) < d
                          ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_AT] THEN MESON_TAC[]);;

let LIM_AT_INFINITY = prove
 (`!f l. (f --> l) at_infinity <=>
               !e. &0 < e ==> ?b. !x. norm(x) >= b ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_AT_INFINITY] THEN MESON_TAC[]);;

let LIM_AT_INFINITY_POS = prove
 (`!f l. (f --> l) at_infinity <=>
         !e. &0 < e ==> ?b. &0 < b /\ !x. norm x >= b ==> dist(f x,l) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_AT_INFINITY] THEN
  MESON_TAC[REAL_ARITH `&0 < abs b + &1 /\ (x >= abs b + &1 ==> x >= b)`]);;

let LIM_AT_POSINFINITY = prove
 (`!f l. (f --> l) at_posinfinity <=>
               !e. &0 < e ==> ?b. !x. x >= b ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_AT_POSINFINITY] THEN MESON_TAC[]);;

let LIM_AT_NEGINFINITY = prove
 (`!f l. (f --> l) at_neginfinity <=>
               !e. &0 < e ==> ?b. !x. x <= b ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_AT_NEGINFINITY] THEN MESON_TAC[]);;

let LIM_SEQUENTIALLY = prove
 (`!s l. (s --> l) sequentially <=>
          !e. &0 < e ==> ?N. !n. N <= n ==> dist(s(n),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_SEQUENTIALLY] THEN MESON_TAC[]);;

let LIM_EVENTUALLY = prove
 (`!net f l. eventually (\x. f x = l) net ==> (f --> l) net`,
  REWRITE_TAC[eventually; LIM] THEN MESON_TAC[DIST_REFL]);;

let LIM_POSINFINITY_SEQUENTIALLY = prove
 (`!f l. (f --> l) at_posinfinity ==> ((\n. f(&n)) --> l) sequentially`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIM_AT_POSINFINITY; LIM_SEQUENTIALLY] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  MP_TAC(ISPEC `B:real` REAL_ARCH_SIMPLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC);;

let LIM_INFINITY_POSINFINITY_LIFT = prove
 (`!f l:real^N. (f --> l) at_infinity ==> ((f o lift) --> l) at_posinfinity`,
  REWRITE_TAC[LIM_AT_INFINITY; LIM_AT_POSINFINITY; o_THM] THEN
  REWRITE_TAC[FORALL_DROP; NORM_REAL; GSYM drop; LIFT_DROP] THEN
  MESON_TAC[REAL_ARITH `x >= b ==> abs(x) >= b`]);;

(* ------------------------------------------------------------------------- *)
(* The expected monotonicity property.                                       *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_EMPTY = prove
 (`!f l x. (f --> l) (at x within {})`,
  REWRITE_TAC[LIM_WITHIN; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_01]);;

let LIM_WITHIN_SUBSET = prove
 (`!f l a s.
    (f --> l) (at a within s) /\ t SUBSET s ==> (f --> l) (at a within t)`,
  REWRITE_TAC[LIM_WITHIN; SUBSET] THEN MESON_TAC[]);;

let LIM_UNION = prove
 (`!f x l s t.
        (f --> l) (at x within s) /\ (f --> l) (at x within t)
        ==> (f --> l) (at x within (s UNION t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_WITHIN; IN_UNION] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `e:real` THEN ASM_CASES_TAC `&0 < e` THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `d1:real`) (X_CHOOSE_TAC `d2:real`)) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_MESON_TAC[REAL_LT_MIN]);;

let LIM_UNION_UNIV = prove
 (`!f x l s t.
        (f --> l) (at x within s) /\ (f --> l) (at x within t) /\
        s UNION t = (:real^N)
        ==> (f --> l) (at x)`,
  MESON_TAC[LIM_UNION; WITHIN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Composition of limits.                                                    *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPOSE_WITHIN = prove
 (`!net f:A->real^N g:real^N->real^P s y z.
    (f --> y) net /\
    eventually (\w. f w IN s /\ (f w = y ==> g y = z)) net /\
    (g --> z) (at y within s)
    ==> ((g o f) --> z) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto; CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[LEFT_AND_FORALL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EVENTUALLY_WITHIN; GSYM DIST_NZ; o_DEF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  ASM_MESON_TAC[DIST_REFL]);;

let LIM_COMPOSE_AT = prove
 (`!net f:A->real^N g:real^N->real^P y z.
    (f --> y) net /\
    eventually (\w. f w = y ==> g y = z) net /\
    (g --> z) (at y)
    ==> ((g o f) --> z) net`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`net:(A)net`; `f:A->real^N`; `g:real^N->real^P`;
                 `(:real^N)`; `y:real^N`; `z:real^P`]
        LIM_COMPOSE_WITHIN) THEN
  ASM_REWRITE_TAC[IN_UNIV; WITHIN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Interrelations between restricted and unrestricted limits.                *)
(* ------------------------------------------------------------------------- *)

let LIM_AT_WITHIN = prove
 (`!f l a s. (f --> l)(at a) ==> (f --> l)(at a within s)`,
  REWRITE_TAC[LIM_AT; LIM_WITHIN] THEN MESON_TAC[]);;

let LIM_WITHIN_OPEN = prove
 (`!f l a:real^M s.
     a IN s /\ open s ==> ((f --> l)(at a within s) <=> (f --> l)(at a))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[LIM_AT_WITHIN] THEN
  REWRITE_TAC[LIM_AT; LIM_WITHIN] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^M` o GEN_REWRITE_RULE I [open_def]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_LT_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* More limit point characterizations.                                       *)
(* ------------------------------------------------------------------------- *)

let LIMPT_SEQUENTIAL_INJ = prove
 (`!x:real^N s.
      x limit_point_of s <=>
             ?f. (!n. f(n) IN (s DELETE x)) /\
                 (!m n. f m = f n <=> m = n) /\
                 (f --> x) sequentially`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIMPT_APPROACHABLE; LIM_SEQUENTIALLY; IN_DELETE] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[GE; LE_REFL]] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `y:real->real^N` THEN DISCH_TAC THEN
  (STRIP_ASSUME_TAC o  prove_recursive_functions_exist num_RECURSION)
   `(z 0 = y (&1)) /\
    (!n. z (SUC n):real^N = y(min (inv(&2 pow (SUC n))) (dist(z n,x))))` THEN
  EXISTS_TAC `z:num->real^N` THEN
  SUBGOAL_THEN
   `!n. z(n) IN s /\ ~(z n:real^N = x) /\ dist(z n,x) < inv(&2 pow n)`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[REAL_LT_01] THEN FIRST_X_ASSUM(MP_TAC o SPEC
     `min (inv(&2 pow (SUC n))) (dist(z n:real^N,x))`) THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_INV_EQ; REAL_LT_POW2; DIST_POS_LT];
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[EQ_SYM_EQ] THEN
      SUBGOAL_THEN `!m n:num. m < n ==> dist(z n:real^N,x) < dist(z m,x)`
       (fun th -> MESON_TAC[th; REAL_LT_REFL; LT_REFL]) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; GEN_TAC THEN ASM_REWRITE_TAC[]] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC
       `min (inv(&2 pow (SUC n))) (dist(z n:real^N,x))`) THEN
      ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_INV_EQ; REAL_LT_POW2; DIST_POS_LT];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS] THEN
      X_GEN_TAC `N:num` THEN REWRITE_TAC[REAL_POW_INV] THEN DISCH_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_LT_TRANS)) THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&2 pow n)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[REAL_LT_POW2] THEN MATCH_MP_TAC REAL_POW_MONO THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]]);;

let LIMPT_SEQUENTIAL = prove
 (`!x:real^N s.
      x limit_point_of s <=>
             ?f. (!n. f(n) IN (s DELETE x)) /\ (f --> x) sequentially`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[LIMPT_SEQUENTIAL_INJ] THEN MESON_TAC[];
    REWRITE_TAC[LIMPT_APPROACHABLE; LIM_SEQUENTIALLY; IN_DELETE] THEN
    MESON_TAC[GE; LE_REFL]]);;

let [LIMPT_INFINITE_OPEN; LIMPT_INFINITE_BALL; LIMPT_INFINITE_CBALL] =
    (CONJUNCTS o prove)
 (`(!s x:real^N.
        x limit_point_of s <=> !t. x IN t /\ open t ==> INFINITE(s INTER t)) /\
   (!s x:real^N.
        x limit_point_of s <=> !e. &0 < e ==> INFINITE(s INTER ball(x,e))) /\
   (!s x:real^N.
        x limit_point_of s <=> !e. &0 < e ==> INFINITE(s INTER cball(x,e)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (r ==> s) /\ (s ==> q) /\ (p ==> r)
    ==> (p <=> q) /\ (p <=> r) /\ (p <=> s)`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[limit_point_of; INFINITE; SET_RULE
     `(?y. ~(y = x) /\ y IN s /\ y IN t) <=> ~(s INTER t SUBSET {x})`] THEN
    MESON_TAC[FINITE_SUBSET; FINITE_SING];
    MESON_TAC[INFINITE_SUPERSET; BALL_SUBSET_CBALL;
              SET_RULE `t SUBSET u ==> s INTER t SUBSET s INTER u`];
    MESON_TAC[INFINITE_SUPERSET; OPEN_CONTAINS_CBALL;
              SET_RULE `t SUBSET u ==> s INTER t SUBSET s INTER u`];
    REWRITE_TAC[LIMPT_SEQUENTIAL_INJ; IN_DELETE; FORALL_AND_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:num->real^N` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[DIST_SYM] IN_BALL)] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MATCH_MP_TAC INFINITE_SUPERSET THEN
    EXISTS_TAC `IMAGE (f:num->real^N) (from N)` THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_FROM; IN_INTER] THEN
    ASM_MESON_TAC[INFINITE_IMAGE_INJ; INFINITE_FROM]]);;

let INFINITE_OPEN_IN = prove
 (`!u s:real^N->bool.
      open_in (subtopology euclidean u) s /\ (?x. x IN s /\ x limit_point_of u)
      ==> INFINITE s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool` o
        GEN_REWRITE_RULE I [LIMPT_INFINITE_OPEN]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Condensation points.                                                      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("condensation_point_of",(12,"right"));;

let condensation_point_of = new_definition
 `x condensation_point_of s <=>
        !t. x IN t /\ open t ==> ~COUNTABLE(s INTER t)`;;

let CONDENSATION_POINT_OF_SUBSET = prove
 (`!x:real^N s t.
        x condensation_point_of s /\ s SUBSET t ==> x condensation_point_of t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[condensation_point_of] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
  ASM SET_TAC[]);;

let CONDENSATION_POINT_IMP_LIMPT = prove
 (`!x s. x condensation_point_of s ==> x limit_point_of s`,
  REWRITE_TAC[condensation_point_of; LIMPT_INFINITE_OPEN; INFINITE] THEN
  MESON_TAC[FINITE_IMP_COUNTABLE]);;

let CONDENSATION_POINT_INFINITE_BALL,CONDENSATION_POINT_INFINITE_CBALL =
  (CONJ_PAIR o prove)
 (`(!s x:real^N.
        x condensation_point_of s <=>
        !e. &0 < e ==> ~COUNTABLE(s INTER ball(x,e))) /\
   (!s x:real^N.
        x condensation_point_of s <=>
        !e. &0 < e ==> ~COUNTABLE(s INTER cball(x,e)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (q ==> r) /\ (r ==> p)
    ==> (p <=> q) /\ (p <=> r)`) THEN
  REWRITE_TAC[condensation_point_of] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[OPEN_BALL; CENTRE_IN_BALL];
    MESON_TAC[BALL_SUBSET_CBALL; COUNTABLE_SUBSET;
              SET_RULE `t SUBSET u ==> s INTER t SUBSET s INTER u`];
    MESON_TAC[COUNTABLE_SUBSET; OPEN_CONTAINS_CBALL;
              SET_RULE `t SUBSET u ==> s INTER t SUBSET s INTER u`]]);;
