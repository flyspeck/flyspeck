(* ========================================================================= *)
(* Some analytic concepts for R instead of R^1.                              *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)
open Hol_core
open Floor
open Card
open Products
open Binomial
open Vectors
open Determinants
open Topology
open Convex
open Paths
open Derivatives
open Polytope
open Integration
open Measure
open Complexes
open Canal
open Transcendentals

(* ------------------------------------------------------------------------- *)
(* Open-ness and closedness of a set of reals.                               *)
(* ------------------------------------------------------------------------- *)

let real_open = new_definition
  `real_open s <=>
      !x. x IN s ==> ?e. &0 < e /\ !x'. abs(x' - x) < e ==> x' IN s`;;

let real_closed = new_definition
 `real_closed s <=> real_open((:real) DIFF s)`;;

let euclideanreal = new_definition
 `euclideanreal = topology real_open`;;

let REAL_OPEN_EMPTY = prove
 (`real_open {}`,
  REWRITE_TAC[real_open; NOT_IN_EMPTY]);;

let REAL_OPEN_UNIV = prove
 (`real_open(:real)`,
  REWRITE_TAC[real_open; IN_UNIV] THEN MESON_TAC[REAL_LT_01]);;

let REAL_OPEN_INTER = prove
 (`!s t. real_open s /\ real_open t ==> real_open (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_open; AND_FORALL_THM; IN_INTER] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `d1:real`) (X_CHOOSE_TAC `d2:real`)) THEN
  MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN
  ASM_MESON_TAC[REAL_LT_TRANS]);;

let REAL_OPEN_UNIONS = prove
 (`(!s. s IN f ==> real_open s) ==> real_open(UNIONS f)`,
  REWRITE_TAC[real_open; IN_UNIONS] THEN MESON_TAC[]);;

let REAL_OPEN_IN = prove
 (`!s. real_open s <=> open_in euclideanreal s`,
  GEN_TAC THEN REWRITE_TAC[euclideanreal] THEN CONV_TAC SYM_CONV THEN
  AP_THM_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 topology_tybij)] THEN
  REWRITE_TAC[REWRITE_RULE[IN] istopology] THEN
  REWRITE_TAC[REAL_OPEN_EMPTY; REAL_OPEN_INTER; SUBSET] THEN
  MESON_TAC[IN; REAL_OPEN_UNIONS]);;

let TOPSPACE_EUCLIDEANREAL = prove
 (`topspace euclideanreal = (:real)`,
  REWRITE_TAC[topspace; EXTENSION; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[REAL_OPEN_UNIV; IN_UNIV; REAL_OPEN_IN]);;

let TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY = prove
 (`!s. topspace (subtopology euclideanreal s) = s`,
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; TOPSPACE_SUBTOPOLOGY; INTER_UNIV]);;

let REAL_CLOSED_IN = prove
 (`!s. real_closed s <=> closed_in euclideanreal s`,
  REWRITE_TAC[real_closed; closed_in; TOPSPACE_EUCLIDEANREAL;
              REAL_OPEN_IN; SUBSET_UNIV]);;

let REAL_OPEN_UNION = prove
 (`!s t. real_open s /\ real_open t ==> real_open(s UNION t)`,
  REWRITE_TAC[REAL_OPEN_IN; OPEN_IN_UNION]);;

let REAL_OPEN_SUBREAL_OPEN = prove
 (`!s. real_open s <=> !x. x IN s ==> ?t. real_open t /\ x IN t /\ t SUBSET s`,
  REWRITE_TAC[REAL_OPEN_IN; GSYM OPEN_IN_SUBOPEN]);;

let REAL_CLOSED_EMPTY = prove
 (`real_closed {}`,
  REWRITE_TAC[REAL_CLOSED_IN; CLOSED_IN_EMPTY]);;

let REAL_CLOSED_UNIV = prove
 (`real_closed(:real)`,
  REWRITE_TAC[REAL_CLOSED_IN; GSYM TOPSPACE_EUCLIDEANREAL; CLOSED_IN_TOPSPACE]);;

let REAL_CLOSED_UNION = prove
 (`!s t. real_closed s /\ real_closed t ==> real_closed(s UNION t)`,
  REWRITE_TAC[REAL_CLOSED_IN; CLOSED_IN_UNION]);;

let REAL_CLOSED_INTER = prove
 (`!s t. real_closed s /\ real_closed t ==> real_closed(s INTER t)`,
  REWRITE_TAC[REAL_CLOSED_IN; CLOSED_IN_INTER]);;

let REAL_CLOSED_INTERS = prove
 (`!f. (!s. s IN f ==> real_closed s) ==> real_closed(INTERS f)`,
  REWRITE_TAC[REAL_CLOSED_IN] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f:(real->bool)->bool = {}` THEN
  ASM_SIMP_TAC[CLOSED_IN_INTERS; INTERS_0] THEN
  REWRITE_TAC[GSYM TOPSPACE_EUCLIDEANREAL; CLOSED_IN_TOPSPACE]);;

let REAL_OPEN_REAL_CLOSED = prove
 (`!s. real_open s <=> real_closed(UNIV DIFF s)`,
  SIMP_TAC[REAL_OPEN_IN; REAL_CLOSED_IN; TOPSPACE_EUCLIDEANREAL; SUBSET_UNIV;
           OPEN_IN_CLOSED_IN_EQ]);;

let REAL_OPEN_DIFF = prove
 (`!s t. real_open s /\ real_closed t ==> real_open(s DIFF t)`,
  REWRITE_TAC[REAL_OPEN_IN; REAL_CLOSED_IN; OPEN_IN_DIFF]);;

let REAL_CLOSED_DIFF = prove
 (`!s t. real_closed s /\ real_open t ==> real_closed(s DIFF t)`,
  REWRITE_TAC[REAL_OPEN_IN; REAL_CLOSED_IN; CLOSED_IN_DIFF]);;

let REAL_OPEN_INTERS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> real_open t) ==> real_open(INTERS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INTERS_INSERT; INTERS_0; REAL_OPEN_UNIV; IN_INSERT] THEN
  MESON_TAC[REAL_OPEN_INTER]);;

let REAL_CLOSED_UNIONS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> real_closed t) ==> real_closed(UNIONS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_INSERT; UNIONS_0; REAL_CLOSED_EMPTY; IN_INSERT] THEN
  MESON_TAC[REAL_CLOSED_UNION]);;

let REAL_OPEN = prove
 (`!s. real_open s <=> open(IMAGE lift s)`,
  REWRITE_TAC[real_open; open_def; FORALL_IN_IMAGE; FORALL_LIFT; DIST_LIFT;
              LIFT_IN_IMAGE_LIFT]);;

let REAL_CLOSED = prove
 (`!s. real_closed s <=> closed(IMAGE lift s)`,
  GEN_TAC THEN REWRITE_TAC[real_closed; REAL_OPEN; closed] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF; IN_UNIV] THEN
  MESON_TAC[LIFT_DROP]);;

let REAL_CLOSED_HALFSPACE_LE = prove
 (`!a. real_closed {x | x <= a}`,
  GEN_TAC THEN SUBGOAL_THEN `closed {x | drop x <= a}` MP_TAC THENL
   [REWRITE_TAC[drop; CLOSED_HALFSPACE_COMPONENT_LE]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[REAL_CLOSED] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

let REAL_CLOSED_HALFSPACE_GE = prove
 (`!a. real_closed {x | x >= a}`,
  GEN_TAC THEN SUBGOAL_THEN `closed {x | drop x >= a}` MP_TAC THENL
   [REWRITE_TAC[drop; CLOSED_HALFSPACE_COMPONENT_GE]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[REAL_CLOSED] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

let REAL_OPEN_HALFSPACE_LT = prove
 (`!a. real_open {x | x < a}`,
  GEN_TAC THEN SUBGOAL_THEN `open {x | drop x < a}` MP_TAC THENL
   [REWRITE_TAC[drop; OPEN_HALFSPACE_COMPONENT_LT]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[REAL_OPEN] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

let REAL_OPEN_HALFSPACE_GT = prove
 (`!a. real_open {x | x > a}`,
  GEN_TAC THEN SUBGOAL_THEN `open {x | drop x > a}` MP_TAC THENL
   [REWRITE_TAC[drop; OPEN_HALFSPACE_COMPONENT_GT]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[REAL_OPEN] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Compactness of a set of reals.                                            *)
(* ------------------------------------------------------------------------- *)

let real_bounded = new_definition
 `real_bounded s <=> ?B. !x. x IN s ==> abs(x) <= B`;;

let REAL_BOUNDED = prove
 (`real_bounded s <=> bounded(IMAGE lift s)`,
  REWRITE_TAC[BOUNDED_LIFT; real_bounded]);;

let REAL_BOUNDED_POS = prove
 (`!s. real_bounded s <=> ?B. &0 < B /\ !x. x IN s ==> abs(x) <= B`,
  REWRITE_TAC[real_bounded] THEN
  MESON_TAC[REAL_ARITH `&0 < &1 + abs B /\ (x <= B ==> x <= &1 + abs B)`]);;

let REAL_BOUNDED_POS_LT = prove
 (`!s. real_bounded s <=> ?b. &0 < b /\ !x. x IN s ==> abs(x) < b`,
  REWRITE_TAC[real_bounded] THEN
  MESON_TAC[REAL_LT_IMP_LE;
            REAL_ARITH `&0 < &1 + abs(y) /\ (x <= y ==> x < &1 + abs(y))`]);;

let REAL_BOUNDED_SUBSET = prove
 (`!s t. real_bounded t /\ s SUBSET t ==> real_bounded s`,
  MESON_TAC[REAL_BOUNDED; BOUNDED_SUBSET; IMAGE_SUBSET]);;

let REAL_BOUNDED_UNION = prove
 (`!s t. real_bounded(s UNION t) <=> real_bounded s /\ real_bounded t`,
  REWRITE_TAC[REAL_BOUNDED; IMAGE_UNION; BOUNDED_UNION]);;

let real_compact = new_definition
 `real_compact s <=> compact(IMAGE lift s)`;;

let REAL_COMPACT_IMP_BOUNDED = prove
 (`!s. real_compact s ==> real_bounded s`,
  REWRITE_TAC[real_compact; REAL_BOUNDED; COMPACT_IMP_BOUNDED]);;

let REAL_COMPACT_IMP_CLOSED = prove
 (`!s. real_compact s ==> real_closed s`,
  REWRITE_TAC[real_compact; REAL_CLOSED; COMPACT_IMP_CLOSED]);;

let REAL_COMPACT_EQ_BOUNDED_CLOSED = prove
 (`!s. real_compact s <=> real_bounded s /\ real_closed s`,
  REWRITE_TAC[real_compact; REAL_BOUNDED; REAL_CLOSED] THEN
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED]);;

let REAL_COMPACT_UNION = prove
 (`!s t. real_compact s /\ real_compact t ==> real_compact(s UNION t)`,
  REWRITE_TAC[real_compact; IMAGE_UNION; COMPACT_UNION]);;

let REAL_COMPACT_ATTAINS_INF = prove
 (`!s. real_compact s /\ ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> x <= y`,
  REWRITE_TAC[real_compact; COMPACT_ATTAINS_INF]);;

let REAL_COMPACT_ATTAINS_SUP = prove
 (`!s. real_compact s /\ ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> y <= x`,
  REWRITE_TAC[real_compact; COMPACT_ATTAINS_SUP]);;

(* ------------------------------------------------------------------------- *)
(* Limits of functions with real range.                                      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("--->",(12,"right"));;

let tendsto_real = new_definition
  `(f ---> l) net <=> !e. &0 < e ==> eventually (\x. abs(f(x) - l) < e) net`;;

let reallim = new_definition
 `reallim net f = @l. (f ---> l) net`;;

let TENDSTO_REAL = prove
 (`(s ---> l) = ((lift o s) --> lift l)`,
  REWRITE_TAC[FUN_EQ_THM; tendsto; tendsto_real; o_THM; DIST_LIFT]);;

let REAL_TENDSTO = prove
 (`(s --> l) = (drop o s ---> drop l)`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP; ETA_AX]);;

let REALLIM_COMPLEX = prove
 (`(s ---> l) = ((Cx o s) --> Cx(l))`,
  REWRITE_TAC[FUN_EQ_THM; tendsto; tendsto_real; o_THM; dist;
              GSYM CX_SUB; COMPLEX_NORM_CX]);;

let REALLIM_UNIQUE = prove
 (`!net f l l'.
         ~trivial_limit net /\ (f ---> l) net /\ (f ---> l') net ==> l = l'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_UNIQUE) THEN REWRITE_TAC[LIFT_EQ]);;

let REALLIM_CONST = prove
 (`!net a. ((\x. a) ---> a) net`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIM_CONST]);;

let REALLIM_LMUL = prove
 (`!f l c. (f ---> l) net ==> ((\x. c * f x) ---> c * l) net`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_CMUL; LIM_CMUL]);;

let REALLIM_RMUL = prove
 (`!f l c. (f ---> l) net ==> ((\x. f x * c) ---> l * c) net`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REALLIM_LMUL]);;

let REALLIM_LMUL_EQ = prove
 (`!net f l c.
        ~(c = &0) ==> (((\x. c * f x) ---> c * l) net <=> (f ---> l) net)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[REALLIM_LMUL] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c:real` o MATCH_MP REALLIM_LMUL) THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_LID; ETA_AX]);;

let REALLIM_RMUL_EQ = prove
 (`!net f l c.
        ~(c = &0) ==> (((\x. f x * c) ---> l * c) net <=> (f ---> l) net)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REALLIM_LMUL_EQ]);;

let REALLIM_NEG = prove
 (`!net f l. (f ---> l) net ==> ((\x. --(f x)) ---> --l) net`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_NEG; LIM_NEG]);;

let REALLIM_NEG_EQ = prove
 (`!net f l. ((\x. --(f x)) ---> --l) net <=> (f ---> l) net`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_NEG; LIM_NEG_EQ]);;

let REALLIM_ADD = prove
 (`!net:(A)net f g l m.
    (f ---> l) net /\ (g ---> m) net ==> ((\x. f(x) + g(x)) ---> l + m) net`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_ADD; LIM_ADD]);;

let REALLIM_SUB = prove
 (`!net:(A)net f g l m.
    (f ---> l) net /\ (g ---> m) net ==> ((\x. f(x) - g(x)) ---> l - m) net`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_SUB; LIM_SUB]);;

let REALLIM_MUL = prove
 (`!net:(A)net f g l m.
    (f ---> l) net /\ (g ---> m) net ==> ((\x. f(x) * g(x)) ---> l * m) net`,
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF; CX_MUL; LIM_COMPLEX_MUL]);;

let REALLIM_INV = prove
 (`!net f l.
         (f ---> l) net /\ ~(l = &0) ==> ((\x. inv(f x)) ---> inv l) net`,
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF; CX_INV; LIM_COMPLEX_INV; GSYM CX_INJ]);;

let REALLIM_DIV = prove
 (`!net:(A)net f g l m.
    (f ---> l) net /\ (g ---> m) net /\ ~(m = &0)
    ==> ((\x. f(x) / g(x)) ---> l / m) net`,
  SIMP_TAC[real_div; REALLIM_MUL; REALLIM_INV]);;

let REALLIM_ABS = prove
 (`!net f l. (f ---> l) net ==> ((\x. abs(f x)) ---> abs l) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto_real] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let REALLIM_POW = prove
 (`!net f l n. (f ---> l) net ==> ((\x. f x pow n) ---> l pow n) net`,
  REPLICATE_TAC 3 GEN_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[real_pow; REALLIM_CONST; REALLIM_MUL]);;

let REALLIM_MAX = prove
 (`!net:(A)net f g l m.
    (f ---> l) net /\ (g ---> m) net
    ==> ((\x. max (f x) (g x)) ---> max l m) net`,
  REWRITE_TAC[REAL_ARITH `max x y = inv(&2) * ((x + y) + abs(x - y))`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_LMUL THEN
  ASM_SIMP_TAC[REALLIM_ADD; REALLIM_ABS; REALLIM_SUB]);;

let REALLIM_MIN = prove
 (`!net:(A)net f g l m.
    (f ---> l) net /\ (g ---> m) net
    ==> ((\x. min (f x) (g x)) ---> min l m) net`,
  REWRITE_TAC[REAL_ARITH `min x y = inv(&2) * ((x + y) - abs(x - y))`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_LMUL THEN
  ASM_SIMP_TAC[REALLIM_ADD; REALLIM_ABS; REALLIM_SUB]);;

let REALLIM_NULL = prove
 (`!net f l. (f ---> l) net <=> ((\x. f(x) - l) ---> &0) net`,
  REWRITE_TAC[tendsto_real; REAL_SUB_RZERO]);;

let REALLIM_NULL_ADD = prove
 (`!net:(A)net f g.
    (f ---> &0) net /\ (g ---> &0) net ==> ((\x. f(x) + g(x)) ---> &0) net`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REALLIM_ADD) THEN
  REWRITE_TAC[REAL_ADD_LID]);;

let REALLIM_NULL_LMUL = prove
 (`!net f c. (f ---> &0) net ==> ((\x. c * f x) ---> &0) net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP REALLIM_LMUL) THEN
  REWRITE_TAC[REAL_MUL_RZERO]);;

let REALLIM_NULL_RMUL = prove
 (`!net f c. (f ---> &0) net ==> ((\x. f x * c) ---> &0) net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP REALLIM_RMUL) THEN
  REWRITE_TAC[REAL_MUL_LZERO]);;

let REALLIM_NULL_POW = prove
 (`!net f n. (f ---> &0) net /\ ~(n = 0) ==> ((\x. f x pow n) ---> &0) net`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o SPEC `n:num` o MATCH_MP REALLIM_POW) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_POW_ZERO]);;

let REALLIM_NULL_LMUL_EQ = prove
 (`!net f c.
        ~(c = &0) ==> (((\x. c * f x) ---> &0) net <=> (f ---> &0) net)`,
  MESON_TAC[REALLIM_LMUL_EQ; REAL_MUL_RZERO]);;

let REALLIM_NULL_RMUL_EQ = prove
 (`!net f c.
        ~(c = &0) ==> (((\x. f x * c) ---> &0) net <=> (f ---> &0) net)`,
  MESON_TAC[REALLIM_RMUL_EQ; REAL_MUL_LZERO]);;

let REALLIM_NULL_NEG = prove
 (`!net f. ((\x. --(f x)) ---> &0) net <=> (f ---> &0) net`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ARITH `--x = --(&1) * x`] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL_EQ THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let REALLIM_RE = prove
 (`!net f l. (f --> l) net ==> ((Re o f) ---> Re l) net`,
  REWRITE_TAC[REALLIM_COMPLEX] THEN
  REWRITE_TAC[tendsto; dist; o_THM; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[GSYM RE_SUB; eventually] THEN
  MESON_TAC[REAL_LET_TRANS; COMPLEX_NORM_GE_RE_IM]);;

let REALLIM_IM = prove
 (`!net f l. (f --> l) net ==> ((Im o f) ---> Im l) net`,
  REWRITE_TAC[REALLIM_COMPLEX] THEN
  REWRITE_TAC[tendsto; dist; o_THM; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[GSYM IM_SUB; eventually] THEN
  MESON_TAC[REAL_LET_TRANS; COMPLEX_NORM_GE_RE_IM]);;

let REALLIM_TRANSFORM_EVENTUALLY = prove
 (`!net f g l.
        eventually (\x. f x = g x) net /\ (f ---> l) net ==> (g ---> l) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  SIMP_TAC[o_THM]);;

let REALLIM_TRANSFORM = prove
 (`!net f g l.
        ((\x. f x - g x) ---> &0) net /\ (f ---> l) net ==> (g ---> l) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF; LIFT_NUM; LIFT_SUB; LIM_TRANSFORM]);;

let REALLIM_TRANSFORM_EQ = prove
 (`!net f:A->real g l.
     ((\x. f x - g x) ---> &0) net ==> ((f ---> l) net <=> (g ---> l) net)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF; LIFT_NUM; LIFT_SUB; LIM_TRANSFORM_EQ]);;

let REAL_SEQ_OFFSET = prove
 (`!f l k. (f ---> l) sequentially ==> ((\i. f (i + k)) ---> l) sequentially`,
  REPEAT GEN_TAC THEN SIMP_TAC[TENDSTO_REAL; o_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_OFFSET) THEN SIMP_TAC[]);;

let REAL_SEQ_OFFSET_REV = prove
 (`!f l k. ((\i. f (i + k)) ---> l) sequentially ==> (f ---> l) sequentially`,
  SIMP_TAC[TENDSTO_REAL; o_DEF] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SEQ_OFFSET_REV THEN EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[]);;

let REALLIM_TRANSFORM_STRADDLE = prove
 (`!f g h a.
        eventually (\n. f(n) <= g(n)) net /\ (f ---> a) net /\
        eventually (\n. g(n) <= h(n)) net /\ (h ---> a) net
        ==> (g ---> a) net`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RIGHT_AND_FORALL_THM; tendsto_real; AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  REAL_ARITH_TAC);;

let REALLIM_TRANSFORM_BOUND = prove
 (`!f g. eventually (\n. abs(f n) <= g n) net /\ (g ---> &0) net
         ==> (f ---> &0) net`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RIGHT_AND_FORALL_THM; tendsto_real; AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  REAL_ARITH_TAC);;

let REAL_CONVERGENT_IMP_BOUNDED = prove
 (`!s l. (s ---> l) sequentially ==> real_bounded (IMAGE s (:num))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_BOUNDED; TENDSTO_REAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONVERGENT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV] THEN
  REWRITE_TAC[o_DEF; NORM_LIFT]);;

let REALLIM = prove
 (`(f ---> l) net <=>
        trivial_limit net \/
        !e. &0 < e ==> ?y. (?x. netord(net) x y) /\
                           !x. netord(net) x y ==> abs(f(x) -l) < e`,
  REWRITE_TAC[tendsto_real; eventually] THEN MESON_TAC[]);;

let REALLIM_NULL_ABS = prove
 (`!net f. ((\x. abs(f x)) ---> &0) net <=> (f ---> &0) net`,
  REWRITE_TAC[REALLIM; REAL_SUB_RZERO; REAL_ABS_ABS]);;

let REALLIM_WITHIN_LE = prove
 (`!f:real^N->real l a s.
        (f ---> l) (at a within s) <=>
           !e. &0 < e ==> ?d. &0 < d /\
                              !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) <= d
                                   ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_WITHIN_LE]);;

let REALLIM_WITHIN = prove
 (`!f:real^N->real l a s.
      (f ---> l) (at a within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) < d
                    ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_WITHIN] THEN MESON_TAC[]);;

let REALLIM_AT = prove
 (`!f l a:real^N.
      (f ---> l) (at a) <=>
              !e. &0 < e
                  ==> ?d. &0 < d /\ !x. &0 < dist(x,a) /\ dist(x,a) < d
                          ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_AT] THEN MESON_TAC[]);;

let REALLIM_AT_INFINITY = prove
 (`!f l. (f ---> l) at_infinity <=>
               !e. &0 < e ==> ?b. !x. norm(x) >= b ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_AT_INFINITY] THEN MESON_TAC[]);;

let REALLIM_AT_INFINITY_COMPLEX_0 = prove
 (`!f l. (f ---> l) at_infinity <=> ((f o inv) ---> l) (at(Cx(&0)))`,
  REWRITE_TAC[REALLIM_COMPLEX; LIM_AT_INFINITY_COMPLEX_0] THEN
  REWRITE_TAC[o_ASSOC]);;

let REALLIM_SEQUENTIALLY = prove
 (`!s l. (s ---> l) sequentially <=>
          !e. &0 < e ==> ?N. !n. N <= n ==> abs(s(n) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_SEQUENTIALLY] THEN MESON_TAC[]);;

let REALLIM_EVENTUALLY = prove
 (`!net f l. eventually (\x. f x = l) net ==> (f ---> l) net`,
  REWRITE_TAC[eventually; REALLIM] THEN
  MESON_TAC[REAL_ARITH `abs(x - x) = &0`]);;

let LIM_COMPONENTWISE = prove
 (`!net f:A->real^N.
        (f --> l) net <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> ((\x. (f x)$i) ---> l$i) net`,
  ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[TENDSTO_REAL; o_DEF]);;

let REALLIM_UBOUND = prove
 (`!(net:A net) f l b.
        (f ---> l) net /\
        ~trivial_limit net /\
        eventually (\x. f x <= b) net
        ==> l <= b`,
  REWRITE_TAC[FORALL_DROP; TENDSTO_REAL; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `net:A net` LIM_DROP_UBOUND) THEN
  EXISTS_TAC `lift o (f:A->real)` THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP]);;

let REALLIM_LBOUND = prove
 (`!(net:A net) f l b.
        (f ---> l) net /\
        ~trivial_limit net /\
        eventually (\x. b <= f x) net
        ==> b <= l`,
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG2] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `net:A net` REALLIM_UBOUND) THEN
  EXISTS_TAC `\a:A. --(f a:real)` THEN
  ASM_REWRITE_TAC[REALLIM_NEG_EQ]);;

let REALLIM_LE = prove
 (`!net f g l m.
           (f ---> l) net /\ (g ---> m) net /\
           ~trivial_limit net /\
           eventually (\x. f x <= g x) net
           ==> l <= m`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o MATCH_MP REALLIM_SUB o ONCE_REWRITE_RULE[CONJ_SYM]) MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP REALLIM_LBOUND));;

let REALLIM_CONST_EQ = prove
 (`!net:(A net) c d. ((\x. c) ---> d) net <=> trivial_limit net \/ c = d`,
  REWRITE_TAC[TENDSTO_REAL; LIM_CONST_EQ; o_DEF; LIFT_EQ]);;

let REALLIM_SUM = prove
 (`!net f:A->B->real l s.
        FINITE s /\ (!i. i IN s ==> ((f i) ---> (l i)) net)
        ==> ((\x. sum s (\i. f i x)) ---> sum s l) net`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; REALLIM_CONST; REALLIM_ADD; IN_INSERT; ETA_AX]);;

let REALLIM_NULL_COMPARISON = prove
 (`!net:(A)net f g.
        eventually (\x. abs(f x) <= g x) net /\ (g ---> &0) net
        ==> (f ---> &0) net`,
  REWRITE_TAC[TENDSTO_REAL; LIFT_NUM; o_DEF] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `g:A->real` THEN ASM_REWRITE_TAC[NORM_LIFT]);;

(* ------------------------------------------------------------------------- *)
(* Real series.                                                              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("real_sums",(12,"right"));;

let real_sums = new_definition
 `(f real_sums l) s <=> ((\n. sum (s INTER (0..n)) f) ---> l) sequentially`;;

let real_infsum = new_definition
 `real_infsum s f = @l. (f real_sums l) s`;;

let real_summable = new_definition
 `real_summable s f = ?l. (f real_sums l) s`;;

let REAL_SUMS = prove
 (`(f real_sums l) = ((lift o f) sums (lift l))`,
  REWRITE_TAC[FUN_EQ_THM; sums; real_sums; TENDSTO_REAL] THEN
  SIMP_TAC[LIFT_SUM; FINITE_INTER_NUMSEG; o_DEF]);;

let REAL_SUMS_RE = prove
 (`!f l s. (f sums l) s ==> ((Re o f) real_sums (Re l)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sums; sums] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_RE) THEN
  SIMP_TAC[o_DEF; RE_VSUM; FINITE_INTER_NUMSEG]);;

let REAL_SUMS_IM = prove
 (`!f l s. (f sums l) s ==> ((Im o f) real_sums (Im l)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sums; sums] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_IM) THEN
  SIMP_TAC[o_DEF; IM_VSUM; FINITE_INTER_NUMSEG]);;

let REAL_SUMS_COMPLEX = prove
 (`!f l s. (f real_sums l) s <=> ((Cx o f) sums (Cx l)) s`,
  REWRITE_TAC[real_sums; sums; REALLIM_COMPLEX] THEN
  SIMP_TAC[o_DEF; VSUM_CX; FINITE_INTER; FINITE_NUMSEG]);;

let REAL_SUMMABLE = prove
 (`real_summable s f <=> summable s (lift o f)`,
  REWRITE_TAC[real_summable; summable; REAL_SUMS; GSYM EXISTS_LIFT]);;

let REAL_SUMMABLE_COMPLEX = prove
 (`real_summable s f <=> summable s (Cx o f)`,
  REWRITE_TAC[real_summable; summable; REAL_SUMS_COMPLEX] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:complex`) THEN EXISTS_TAC `Re l` THEN
  SUBGOAL_THEN `Cx(Re l) = l` (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM REAL] THEN MATCH_MP_TAC REAL_SERIES THEN
  MAP_EVERY EXISTS_TAC [`Cx o (f:num->real)`; `s:num->bool`] THEN
  ASM_REWRITE_TAC[o_THM; REAL_CX]);;

let REAL_SERIES_CAUCHY = prove
 (`(?l. (f real_sums l) s) <=>
   (!e. &0 < e ==> ?N. !m n. m >= N ==> abs(sum(s INTER (m..n)) f) < e)`,
  REWRITE_TAC[REAL_SUMS; SERIES_CAUCHY; GSYM EXISTS_LIFT] THEN
  SIMP_TAC[NORM_REAL; GSYM drop; DROP_VSUM; FINITE_INTER_NUMSEG] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]);;

let REAL_SUMS_SUMMABLE = prove
 (`!f l s. (f real_sums l) s ==> real_summable s f`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[]);;

let REAL_SUMS_INFSUM = prove
 (`!f s. (f real_sums (real_infsum s f)) s <=> real_summable s f`,
  REWRITE_TAC[real_infsum; real_summable] THEN MESON_TAC[]);;

let REAL_INFSUM_COMPLEX = prove
 (`!f s. real_summable s f ==> real_infsum s f = Re(infsum s (Cx o f))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_SUMS_INFSUM; REAL_SUMS_COMPLEX] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFSUM_UNIQUE) THEN
  MESON_TAC[RE_CX]);;

let REAL_SERIES_FROM = prove
 (`!f l k. (f real_sums l) (from k) = ((\n. sum(k..n) f) ---> l) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sums] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; numseg; from; IN_ELIM_THM; IN_INTER] THEN ARITH_TAC);;

let REAL_SERIES_UNIQUE = prove
 (`!f l l' s. (f real_sums l) s /\ (f real_sums l') s ==> l = l'`,
  REWRITE_TAC[real_sums] THEN
  MESON_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; REALLIM_UNIQUE]);;

let REAL_INFSUM_UNIQUE = prove
 (`!f l s. (f real_sums l) s ==> real_infsum s f = l`,
  MESON_TAC[REAL_SERIES_UNIQUE; REAL_SUMS_INFSUM; real_summable]);;

let REAL_SERIES_FINITE = prove
 (`!f s. FINITE s ==> (f real_sums (sum s f)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[num_FINITE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[real_sums; REALLIM_SEQUENTIALLY] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `n:num` THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `s INTER (0..m) = s`
   (fun th -> ASM_REWRITE_TAC[th; REAL_SUB_REFL; REAL_ABS_NUM]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[LE_TRANS]);;

let REAL_SUMMABLE_IFF_EVENTUALLY = prove
 (`!f g k. (?N. !n. N <= n /\ n IN k ==> f n = g n)
           ==> (real_summable k f <=> real_summable k g)`,
  REWRITE_TAC[REAL_SUMMABLE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUMMABLE_IFF_EVENTUALLY THEN REWRITE_TAC[o_THM] THEN
  ASM_MESON_TAC[]);;

let REAL_SUMMABLE_EQ_EVENTUALLY = prove
 (`!f g k. (?N. !n. N <= n /\ n IN k ==> f n = g n) /\ real_summable k f
           ==> real_summable k g`,
  MESON_TAC[REAL_SUMMABLE_IFF_EVENTUALLY]);;

let REAL_SUMMABLE_IFF_COFINITE = prove
 (`!f s t. FINITE((s DIFF t) UNION (t DIFF s))
           ==> (real_summable s f <=> real_summable t f)`,
  SIMP_TAC[REAL_SUMMABLE] THEN MESON_TAC[SUMMABLE_IFF_COFINITE]);;

let REAL_SUMMABLE_EQ_COFINITE = prove
 (`!f s t. FINITE((s DIFF t) UNION (t DIFF s)) /\ real_summable s f
           ==> real_summable t f`,
  MESON_TAC[REAL_SUMMABLE_IFF_COFINITE]);;

let REAL_SUMMABLE_FROM_ELSEWHERE = prove
 (`!f m n. real_summable (from m) f ==> real_summable (from n) f`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_SUMMABLE_EQ_COFINITE) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..(m+n)` THEN
  SIMP_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_UNION; IN_DIFF; IN_FROM] THEN
  ARITH_TAC);;

let REAL_SERIES_GOESTOZERO = prove
 (`!s x. real_summable s x
         ==> !e. &0 < e
                 ==> eventually (\n. n IN s ==> abs(x n) < e) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_SUMMABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SERIES_GOESTOZERO) THEN
  REWRITE_TAC[o_THM; NORM_LIFT]);;

let REAL_SUMMABLE_IMP_TOZERO = prove
 (`!f:num->real k.
       real_summable k f
       ==> ((\n. if n IN k then f(n) else &0) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_SUMMABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_IMP_TOZERO) THEN
  REWRITE_TAC[TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF; GSYM LIFT_NUM; GSYM COND_RAND]);;

let REAL_SUMMABLE_IMP_BOUNDED = prove
 (`!f:num->real k. real_summable k f ==> real_bounded (IMAGE f k)`,
  REWRITE_TAC[REAL_BOUNDED; REAL_SUMMABLE; GSYM IMAGE_o;
              SUMMABLE_IMP_BOUNDED]);;

let REAL_SUMMABLE_IMP_REAL_SUMS_BOUNDED = prove
 (`!f:num->real k.
       real_summable (from k) f ==> real_bounded { sum(k..n) f | n IN (:num) }`,
  REWRITE_TAC[real_summable; real_sums; LEFT_IMP_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_CONVERGENT_IMP_BOUNDED) THEN
  REWRITE_TAC[FROM_INTER_NUMSEG; SIMPLE_IMAGE]);;

let REAL_SERIES_0 = prove
 (`!s. ((\n. &0) real_sums (&0)) s`,
  REWRITE_TAC[real_sums; SUM_0; REALLIM_CONST]);;

let REAL_SERIES_ADD = prove
 (`!x x0 y y0 s.
     (x real_sums x0) s /\ (y real_sums y0) s
     ==> ((\n. x n + y n) real_sums (x0 + y0)) s`,
  SIMP_TAC[real_sums; FINITE_INTER_NUMSEG; SUM_ADD; REALLIM_ADD]);;

let REAL_SERIES_SUB = prove
 (`!x x0 y y0 s.
     (x real_sums x0) s /\ (y real_sums y0) s
     ==> ((\n. x n - y n) real_sums (x0 - y0)) s`,
  SIMP_TAC[real_sums; FINITE_INTER_NUMSEG; SUM_SUB; REALLIM_SUB]);;

let REAL_SERIES_LMUL = prove
 (`!x x0 c s. (x real_sums x0) s ==> ((\n. c * x n) real_sums (c * x0)) s`,
  SIMP_TAC[real_sums; FINITE_INTER_NUMSEG; SUM_LMUL; REALLIM_LMUL]);;

let REAL_SERIES_RMUL = prove
 (`!x x0 c s. (x real_sums x0) s ==> ((\n. x n * c) real_sums (x0 * c)) s`,
  SIMP_TAC[real_sums; FINITE_INTER_NUMSEG; SUM_RMUL; REALLIM_RMUL]);;

let REAL_SERIES_NEG = prove
 (`!x x0 s. (x real_sums x0) s ==> ((\n. --(x n)) real_sums (--x0)) s`,
  SIMP_TAC[real_sums; FINITE_INTER_NUMSEG; SUM_NEG; REALLIM_NEG]);;

let REAL_SUMS_IFF = prove
 (`!f g k. (!x. x IN k ==> f x = g x)
           ==> ((f real_sums l) k <=> (g real_sums l) k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_sums] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_INTER]);;

let REAL_SUMS_EQ = prove
 (`!f g k. (!x. x IN k ==> f x = g x) /\ (f real_sums l) k
           ==> (g real_sums l) k`,
  MESON_TAC[REAL_SUMS_IFF]);;

let REAL_SERIES_FINITE_SUPPORT = prove
 (`!f s k.
     FINITE (s INTER k) /\ (!x. ~(x IN s INTER k) ==> f x = &0)
     ==> (f real_sums sum(s INTER k) f) k`,
  REWRITE_TAC[real_sums; REALLIM_SEQUENTIALLY] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPEC `\x:num. x` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `sum (k INTER (0..n)) (f:num->real) = sum(s INTER k) f`
   (fun th -> ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM; th]) THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  ASM_SIMP_TAC[SUBSET; IN_INTER; IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[IN_INTER; LE_TRANS]);;

let REAL_SERIES_DIFFS = prove
 (`!f k. (f ---> &0) sequentially
         ==> ((\n. f(n) - f(n + 1)) real_sums f(k)) (from k)`,
  REWRITE_TAC[real_sums; FROM_INTER_NUMSEG; SUM_DIFFS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. (f:num->real) k - f(n + 1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `k:num` THEN
    SIMP_TAC[];
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_SUB_RZERO] THEN
    MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
    MATCH_MP_TAC REAL_SEQ_OFFSET THEN ASM_REWRITE_TAC[]]);;

let REAL_SERIES_TRIVIAL = prove
 (`!f. (f real_sums &0) {}`,
  REWRITE_TAC[real_sums; INTER_EMPTY; SUM_CLAUSES; REALLIM_CONST]);;

let REAL_SERIES_RESTRICT = prove
 (`!f k l:real.
        ((\n. if n IN k then f(n) else &0) real_sums l) (:num) <=>
        (f real_sums l) k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sums] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; INTER_UNIV] THEN GEN_TAC THEN
  MATCH_MP_TAC(MESON[] `sum s f = sum t f /\ sum t f = sum t g
                        ==> sum s f = sum t g`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN SET_TAC[];
    MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[IN_INTER]]);;

let REAL_SERIES_SUM = prove
 (`!f l k s. FINITE s /\ s SUBSET k /\ (!x. ~(x IN s) ==> f x = &0) /\
             sum s f = l ==> (f real_sums l) k`,
  REPEAT STRIP_TAC THEN EXPAND_TAC "l" THEN
  SUBGOAL_THEN `s INTER k = s:num->bool` ASSUME_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC [REAL_SERIES_FINITE_SUPPORT]]);;

let REAL_SUMS_REINDEX = prove
 (`!k a l n.
     ((\x. a(x + k)) real_sums l) (from n) <=> (a real_sums l) (from(n + k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sums; FROM_INTER_NUMSEG] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_OFFSET] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  ASM_MESON_TAC[ARITH_RULE `N + k:num <= n ==> n = (n - k) + k /\ N <= n - k`;
                ARITH_RULE `N + k:num <= n ==> N <= n + k`]);;

let REAL_INFSUM = prove
 (`!f s. real_summable s f ==> real_infsum s f = drop(infsum s (lift o f))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_SUMS_INFSUM; REAL_SUMS] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFSUM_UNIQUE) THEN
  MESON_TAC[LIFT_DROP]);;

let REAL_PARTIAL_SUMS_LE_INFSUM = prove
 (`!f s n.
        (!i. i IN s ==> &0 <= f i) /\ real_summable s f
        ==> sum (s INTER (0..n)) f <= real_infsum s f`,
  REPEAT GEN_TAC THEN SIMP_TAC[REAL_INFSUM] THEN
  REWRITE_TAC[REAL_SUMMABLE] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o BINDER_CONV o RAND_CONV o RAND_CONV)
   [GSYM LIFT_DROP] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(MP_TAC o MATCH_MP
    PARTIAL_SUMS_DROP_LE_INFSUM) THEN
  SIMP_TAC[DROP_VSUM; FINITE_INTER; FINITE_NUMSEG; o_DEF; LIFT_DROP; ETA_AX]);;

let REAL_PARTIAL_SUMS_LE_INFSUM_GEN = prove
 (`!f s t. FINITE t /\ t SUBSET s /\
           (!i. i IN s ==> &0 <= f i) /\ real_summable s f
           ==> sum t f <= real_infsum s f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\n:num. n` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  TRANS_TAC REAL_LE_TRANS `sum (s INTER (0..n)) f` THEN
  ASM_SIMP_TAC[REAL_PARTIAL_SUMS_LE_INFSUM] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_SIMP_TAC[IN_INTER; IN_DIFF; FINITE_INTER; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG; IN_INTER; LE_0] THEN ASM SET_TAC[]);;

let REAL_SERIES_TERMS_TOZERO = prove
 (`!f l n. (f real_sums l) (from n) ==> (f ---> &0) sequentially`,
  REWRITE_TAC[REAL_SUMS; TENDSTO_REAL; LIFT_NUM; SERIES_TERMS_TOZERO]);;

let REAL_SERIES_LE = prove
 (`!f g s y z.
        (f real_sums y) s /\ (g real_sums z) s /\
        (!i. i IN s ==> f(i) <= g(i))
        ==> y <= z`,
  REWRITE_TAC[REAL_SUMS] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[LIFT_DROP] `x = drop(lift x)`] THEN
  MATCH_MP_TAC SERIES_DROP_LE THEN
  MAP_EVERY EXISTS_TAC [`lift o (f:num->real)`; `lift o (g:num->real)`] THEN
  ASM_SIMP_TAC[o_THM; LIFT_DROP] THEN ASM_MESON_TAC[]);;

let REAL_SERIES_POS = prove
 (`!f s y.
        (f real_sums y) s /\ (!i. i IN s ==> &0 <= f(i))
        ==> &0 <= y`,
  REWRITE_TAC[REAL_SUMS] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM LIFT_DROP] THEN
  MATCH_MP_TAC SERIES_DROP_POS THEN
  EXISTS_TAC `lift o (f:num->real)` THEN
  ASM_SIMP_TAC[o_THM; LIFT_DROP] THEN ASM_MESON_TAC[]);;

let REAL_SERIES_BOUND = prove
 (`!f g s a b.
        (f real_sums a) s /\ (g real_sums b) s /\
        (!i. i IN s ==> abs(f i) <= g i)
        ==> abs(a) <= b`,
  REWRITE_TAC[REAL_SUMS; GSYM NORM_LIFT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SERIES_BOUND THEN
  EXISTS_TAC `lift o (f:num->real)` THEN
  REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

let REAL_SERIES_COMPARISON_BOUND = prove
 (`!f g s a.
        (g real_sums a) s /\ (!i. i IN s ==> abs(f i) <= g i)
        ==> ?l. (f real_sums l) s /\ abs(l) <= a`,
  REWRITE_TAC[REAL_SUMS; GSYM EXISTS_LIFT; GSYM NORM_LIFT] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
  MATCH_MP_TAC SERIES_COMPARISON_BOUND THEN
  EXISTS_TAC `lift o (g:num->real)` THEN
  ASM_SIMP_TAC[o_THM; LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Similar combining theorems just for summability.                          *)
(* ------------------------------------------------------------------------- *)

let REAL_SUMMABLE_0 = prove
 (`!s. real_summable s (\n. &0)`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_0]);;

let REAL_SUMMABLE_ADD = prove
 (`!x y s. real_summable s x /\ real_summable s y
           ==> real_summable s (\n. x n + y n)`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_ADD]);;

let REAL_SUMMABLE_SUB = prove
 (`!x y s. real_summable s x /\ real_summable s y
           ==> real_summable s (\n. x n - y n)`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_SUB]);;

let REAL_SUMMABLE_LMUL = prove
 (`!s x c. real_summable s x ==> real_summable s (\n. c * x n)`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_LMUL]);;

let REAL_SUMMABLE_RMUL = prove
 (`!s x c. real_summable s x ==> real_summable s (\n. x n * c)`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_RMUL]);;

let REAL_SUMMABLE_NEG = prove
 (`!x s. real_summable s x ==> real_summable s (\n. --(x n))`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_NEG]);;

let REAL_SUMMABLE_IFF = prove
 (`!f g k. (!x. x IN k ==> f x = g x)
           ==> (real_summable k f <=> real_summable k g)`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SUMS_IFF]);;

let REAL_SUMMABLE_EQ = prove
 (`!f g k. (!x. x IN k ==> f x = g x) /\ real_summable k f
           ==> real_summable k g`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SUMS_EQ]);;

let REAL_SERIES_SUBSET = prove
 (`!x s t l.
        s SUBSET t /\
        ((\i. if i IN s then x i else &0) real_sums l) t
        ==> (x real_sums l) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[real_sums] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET; FINITE_INTER_NUMSEG] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN SET_TAC[]);;

let REAL_SUMMABLE_SUBSET = prove
 (`!x s t.
        s SUBSET t /\
        real_summable t (\i. if i IN s then x i else &0)
        ==> real_summable s x`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_SUBSET]);;

let REAL_SUMMABLE_TRIVIAL = prove
 (`!f. real_summable {} f`,
  GEN_TAC THEN REWRITE_TAC[real_summable] THEN EXISTS_TAC `&0` THEN
  REWRITE_TAC[REAL_SERIES_TRIVIAL]);;

let REAL_SUMMABLE_RESTRICT = prove
 (`!f k.
        real_summable (:num) (\n. if n IN k then f(n) else &0) <=>
        real_summable k f`,
  REWRITE_TAC[real_summable; REAL_SERIES_RESTRICT]);;

let REAL_SUMS_FINITE_DIFF = prove
 (`!f t s l.
        t SUBSET s /\ FINITE t /\ (f real_sums l) s
        ==> (f real_sums (l - sum t f)) (s DIFF t)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o ISPEC `f:num->real` o MATCH_MP REAL_SERIES_FINITE) THEN
  ONCE_REWRITE_TAC[GSYM REAL_SERIES_RESTRICT] THEN
  REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_SUB) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN REWRITE_TAC[IN_DIFF] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num` o GEN_REWRITE_RULE I [SUBSET]) THEN
  MAP_EVERY ASM_CASES_TAC [`(x:num) IN s`; `(x:num) IN t`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let REAL_SUMS_FINITE_UNION = prove
 (`!f s t l.
        FINITE t /\ (f real_sums l) s
        ==> (f real_sums (l + sum (t DIFF s) f)) (s UNION t)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:num->bool` o MATCH_MP FINITE_DIFF) THEN
  DISCH_THEN(MP_TAC o ISPEC `f:num->real` o MATCH_MP REAL_SERIES_FINITE) THEN
  ONCE_REWRITE_TAC[GSYM REAL_SERIES_RESTRICT] THEN
  REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_ADD) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION] THEN
  MAP_EVERY ASM_CASES_TAC [`(x:num) IN s`; `(x:num) IN t`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let REAL_SUMS_OFFSET = prove
 (`!f l m n.
        (f real_sums l) (from m) /\ m < n
        ==> (f real_sums (l - sum(m..(n-1)) f)) (from n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `from n = from m DIFF (m..(n-1))` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_FROM; IN_DIFF; IN_NUMSEG] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_SUMS_FINITE_DIFF THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    SIMP_TAC[SUBSET; IN_FROM; IN_NUMSEG]]);;

let REAL_SUMS_OFFSET_REV = prove
 (`!f l m n.
        (f real_sums l) (from m) /\ n < m
        ==> (f real_sums (l + sum(n..m-1) f)) (from n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `from m`; `n..m-1`; `l:real`]
                REAL_SUMS_FINITE_UNION) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN MATCH_MP_TAC EQ_IMP THEN
  BINOP_TAC THENL [AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_FROM; IN_NUMSEG] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Similar combining theorems for infsum.                                    *)
(* ------------------------------------------------------------------------- *)

let REAL_INFSUM_0 = prove
 (`real_infsum s (\i. &0) = &0`,
  MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN REWRITE_TAC[REAL_SERIES_0]);;

let REAL_INFSUM_ADD = prove
 (`!x y s. real_summable s x /\ real_summable s y
           ==> real_infsum s (\i. x i + y i) =
               real_infsum s x + real_infsum s y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
  MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[REAL_SUMS_INFSUM]);;

let REAL_INFSUM_SUB = prove
 (`!x y s. real_summable s x /\ real_summable s y
           ==> real_infsum s (\i. x i - y i) =
               real_infsum s x - real_infsum s y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
  MATCH_MP_TAC REAL_SERIES_SUB THEN ASM_REWRITE_TAC[REAL_SUMS_INFSUM]);;

let REAL_INFSUM_LMUL = prove
 (`!s x c. real_summable s x
           ==> real_infsum s (\n. c * x n) = c * real_infsum s x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
  MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[REAL_SUMS_INFSUM]);;

let REAL_INFSUM_RMUL = prove
 (`!s x c. real_summable s x
           ==> real_infsum s (\n. x n * c) = real_infsum s x * c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
  MATCH_MP_TAC REAL_SERIES_RMUL THEN ASM_REWRITE_TAC[REAL_SUMS_INFSUM]);;

let REAL_INFSUM_NEG = prove
 (`!s x. real_summable s x
         ==> real_infsum s (\n. --(x n)) = --(real_infsum s x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
  MATCH_MP_TAC REAL_SERIES_NEG THEN ASM_REWRITE_TAC[REAL_SUMS_INFSUM]);;

let REAL_INFSUM_EQ = prove
 (`!f g k. real_summable k f /\ real_summable k g /\
           (!x. x IN k ==> f x = g x)
           ==> real_infsum k f = real_infsum k g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_infsum] THEN AP_TERM_TAC THEN
  ABS_TAC THEN ASM_MESON_TAC[REAL_SUMS_EQ; REAL_SUMS_INFSUM]);;

let REAL_INFSUM_RESTRICT = prove
 (`!k a. real_infsum (:num) (\n. if n IN k then a n else &0) =
         real_infsum k a`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:num->real`; `k:num->bool`] REAL_SUMMABLE_RESTRICT) THEN
  ASM_CASES_TAC `real_summable k a` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
    ASM_REWRITE_TAC[REAL_SERIES_RESTRICT; REAL_SUMS_INFSUM];
    RULE_ASSUM_TAC(REWRITE_RULE[real_summable; NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[real_infsum]]);;

(* ------------------------------------------------------------------------- *)
(* Convergence tests for real series.                                        *)
(* ------------------------------------------------------------------------- *)

let REAL_SERIES_CAUCHY_UNIFORM = prove
 (`!P:A->bool f k.
        (?l. !e. &0 < e
                 ==> ?N. !n x. N <= n /\ P x
                               ==> abs(sum(k INTER (0..n)) (f x) -
                                        l x) < e) <=>
        (!e. &0 < e ==> ?N. !m n x. N <= m /\ P x
                                    ==> abs(sum(k INTER (m..n)) (f x)) < e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:A->bool`; `\x:A n:num. lift(f x n)`; `k:num->bool`]
        SERIES_CAUCHY_UNIFORM) THEN
  SIMP_TAC[VSUM_REAL; FINITE_INTER; FINITE_NUMSEG] THEN
  REWRITE_TAC[NORM_LIFT; o_DEF; LIFT_DROP; ETA_AX] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `l:A->real`) THEN
    EXISTS_TAC `lift o (l:A->real)` THEN
    ASM_SIMP_TAC[o_THM; DIST_LIFT];
    DISCH_THEN(X_CHOOSE_TAC `l:A->real^1`) THEN
    EXISTS_TAC `drop o (l:A->real^1)` THEN
    ASM_SIMP_TAC[SUM_VSUM; FINITE_INTER; FINITE_NUMSEG] THEN
    REWRITE_TAC[o_THM; GSYM DROP_SUB; GSYM ABS_DROP] THEN
    SIMP_TAC[GSYM dist; VSUM_REAL; FINITE_INTER; FINITE_NUMSEG] THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]]);;

let REAL_SERIES_COMPARISON = prove
 (`!f g s. (?l. (g real_sums l) s) /\
           (?N. !n. n >= N /\ n IN s ==> abs(f n) <= g n)
           ==> ?l. (f real_sums l) s`,
  REWRITE_TAC[REAL_SUMS; GSYM EXISTS_LIFT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_COMPARISON THEN
  EXISTS_TAC `g:num->real` THEN
  REWRITE_TAC[NORM_LIFT; o_THM] THEN ASM_MESON_TAC[]);;

let REAL_SUMMABLE_COMPARISON = prove
 (`!f g s. real_summable s g /\
           (?N. !n. n >= N /\ n IN s ==> abs(f n) <= g n)
           ==> real_summable s f`,
  REWRITE_TAC[real_summable; REAL_SERIES_COMPARISON]);;

let REAL_SERIES_COMPARISON_UNIFORM = prove
 (`!f g P s. (?l. (g real_sums l) s) /\
             (?N. !n x. N <= n /\ n IN s /\ P x ==> abs(f x n) <= g n)
             ==> ?l:A->real.
                    !e. &0 < e
                        ==> ?N. !n x. N <= n /\ P x
                                      ==> abs(sum(s INTER (0..n)) (f x) -
                                               l x) < e`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[GE; REAL_SERIES_CAUCHY; REAL_SERIES_CAUCHY_UNIFORM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `N1:num`)) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:A`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs (sum (s INTER (m .. n)) g)` THEN CONJ_TAC THENL
   [SIMP_TAC[GSYM LIFT_SUM; FINITE_INTER_NUMSEG; NORM_LIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs(a)`) THEN
    MATCH_MP_TAC SUM_ABS_LE THEN
    REWRITE_TAC[FINITE_INTER_NUMSEG; IN_INTER; IN_NUMSEG] THEN
    ASM_MESON_TAC[ARITH_RULE `N1 + N2:num <= m /\ m <= x ==> N1 <= x`];
    ASM_MESON_TAC[ARITH_RULE `N1 + N2:num <= m ==> N2 <= m`]]);;

let REAL_SERIES_RATIO = prove
 (`!c a s N.
      c < &1 /\
      (!n. n >= N ==> abs(a(SUC n)) <= c * abs(a(n)))
      ==> ?l:real. (a real_sums l) s`,
  REWRITE_TAC[REAL_SUMS; GSYM EXISTS_LIFT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_RATIO THEN
  REWRITE_TAC[o_THM; NORM_LIFT] THEN ASM_MESON_TAC[]);;

let BOUNDED_PARTIAL_REAL_SUMS = prove
 (`!f:num->real k.
        real_bounded { sum(k..n) f | n IN (:num) }
        ==> real_bounded { sum(m..n) f | m IN (:num) /\ n IN (:num) }`,
  REWRITE_TAC[REAL_BOUNDED] THEN
  REWRITE_TAC[SET_RULE `IMAGE f {g x | P x} = {f(g x) | P x}`;
    SET_RULE `IMAGE f {g x y | P x /\ Q y} = {f(g x y) | P x /\ Q y}`] THEN
  SIMP_TAC[LIFT_SUM; FINITE_INTER; FINITE_NUMSEG] THEN
  REWRITE_TAC[BOUNDED_PARTIAL_SUMS]);;

let REAL_SERIES_DIRICHLET = prove
 (`!f:num->real g N k m.
        real_bounded { sum (m..n) f | n IN (:num)} /\
        (!n. N <= n ==> g(n + 1) <= g(n)) /\
        (g ---> &0) sequentially
        ==> real_summable (from k) (\n. g(n) * f(n))`,
  REWRITE_TAC[REAL_SUMMABLE; REAL_BOUNDED; TENDSTO_REAL] THEN
  REWRITE_TAC[LIFT_NUM; LIFT_CMUL; o_DEF] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_DIRICHLET THEN
  MAP_EVERY EXISTS_TAC [`N:num`; `m:num`] THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  SIMP_TAC[VSUM_REAL; FINITE_INTER; FINITE_NUMSEG] THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
  ASM_REWRITE_TAC[SET_RULE `{lift(f x) | P x} = IMAGE lift {f x | P x}`]);;

let REAL_SERIES_ABSCONV_IMP_CONV = prove
 (`!x:num->real k. real_summable k (\n. abs(x n)) ==> real_summable k x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\n:num. abs(x n)` THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

let REAL_SUMS_GP = prove
 (`!n x. abs(x) < &1
         ==> ((\k. x pow k) real_sums (x pow n / (&1 - x))) (from n)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`n:num`; `Cx x`] SUMS_GP) THEN
  ASM_REWRITE_TAC[REAL_SUMS_COMPLEX; GSYM CX_SUB; GSYM CX_POW; GSYM CX_DIV;
                  o_DEF; COMPLEX_NORM_CX]);;

let REAL_SUMMABLE_GP = prove
 (`!x k. abs(x) < &1 ==> real_summable k (\n. x pow n)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`Cx x`; `k:num->bool`] SUMMABLE_GP) THEN
  ASM_REWRITE_TAC[REAL_SUMMABLE_COMPLEX] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX; o_DEF; CX_POW]);;

let REAL_SUMMABLE_ZETA_INTEGER = prove
 (`!n m. 2 <= m ==> real_summable (from n) (\k. inv(&k pow m))`,
  REWRITE_TAC[REAL_SUMMABLE_COMPLEX; CX_INV; CX_POW;
              SUMMABLE_ZETA_INTEGER; o_DEF]);;

let REAL_ABEL_LEMMA = prove
 (`!a M r r0.
        &0 <= r /\ r < r0 /\
        (!n. n IN k ==> abs(a n) * r0 pow n <= M)
        ==> real_summable k (\n. abs(a(n)) * r pow n)`,
  REWRITE_TAC[REAL_SUMMABLE_COMPLEX] THEN
  REWRITE_TAC[o_DEF; CX_MUL; CX_ABS] THEN REWRITE_TAC[GSYM CX_MUL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABEL_LEMMA THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_MESON_TAC[]);;

let REAL_POWER_SERIES_CONV_IMP_ABSCONV = prove
 (`!a k w z.
        real_summable k (\n. a(n) * z pow n) /\ abs(w) < abs(z)
        ==> real_summable k (\n. abs(a(n) * w pow n))`,
  REWRITE_TAC[REAL_SUMMABLE_COMPLEX; o_DEF; CX_MUL; CX_ABS; CX_POW] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POWER_SERIES_CONV_IMP_ABSCONV THEN
  EXISTS_TAC `Cx z` THEN ASM_REWRITE_TAC[COMPLEX_NORM_CX]);;

let POWER_REAL_SERIES_CONV_IMP_ABSCONV_WEAK = prove
 (`!a k w z.
        real_summable k (\n. a(n) * z pow n) /\ abs(w) < abs(z)
        ==> real_summable k (\n. abs(a n) * w pow n)`,
  REWRITE_TAC[REAL_SUMMABLE_COMPLEX; o_DEF; CX_MUL; CX_ABS; CX_POW] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POWER_SERIES_CONV_IMP_ABSCONV_WEAK THEN
  EXISTS_TAC `Cx z` THEN ASM_REWRITE_TAC[COMPLEX_NORM_CX]);;

(* ------------------------------------------------------------------------- *)
(* Nets for real limit.                                                      *)
(* ------------------------------------------------------------------------- *)

let atreal = new_definition
 `atreal a = mk_net(\x y. &0 < abs(x - a) /\ abs(x - a) <= abs(y - a))`;;

let ATREAL = prove
 (`!a x y.
        netord(atreal a) x y <=> &0 < abs(x - a) /\ abs(x - a) <= abs(y - a)`,
  GEN_TAC THEN NET_PROVE_TAC[atreal] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS; REAL_LET_TRANS]);;

let WITHINREAL_UNIV = prove
 (`!x. atreal x within (:real) = atreal x`,
  REWRITE_TAC[within; atreal; IN_UNIV] THEN REWRITE_TAC[ETA_AX; net_tybij]);;

let TRIVIAL_LIMIT_ATREAL = prove
 (`!a. ~(trivial_limit (atreal a))`,
  X_GEN_TAC `a:real` THEN SIMP_TAC[trivial_limit; ATREAL; DE_MORGAN_THM] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:real`; `c:real`] THEN
  ASM_CASES_TAC `b:real = c` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM NOT_EXISTS_THM] THEN
  SUBGOAL_THEN `~(b:real = a) \/ ~(c = a)` DISJ_CASES_TAC THENL
   [ASM_MESON_TAC[];
    EXISTS_TAC `(a + b) / &2` THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `(a + c) / &2` THEN ASM_REAL_ARITH_TAC]);;

let NETLIMIT_WITHINREAL = prove
 (`!a s. ~(trivial_limit (atreal a within s))
         ==> (netlimit (atreal a within s) = a)`,
  REWRITE_TAC[trivial_limit; netlimit; ATREAL; WITHIN; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x. ~(&0 < abs(x - a) /\ abs(x - a) <= abs(a - a) /\ x IN s)`
  ASSUME_TAC THENL [REAL_ARITH_TAC; ASM_MESON_TAC[]]);;

let NETLIMIT_ATREAL = prove
 (`!a. netlimit(atreal a) = a`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  MATCH_MP_TAC NETLIMIT_WITHINREAL THEN
  SIMP_TAC[TRIVIAL_LIMIT_ATREAL; WITHINREAL_UNIV]);;

let EVENTUALLY_WITHINREAL_LE = prove
 (`!s a p.
     eventually p (atreal a within s) <=>
        ?d. &0 < d /\
            !x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) <= d ==> p(x)`,
  REWRITE_TAC[eventually; ATREAL; WITHIN; trivial_limit] THEN
  REWRITE_TAC[MESON[REAL_LT_01; REAL_LT_REFL] `~(!a b:real. a = b)`] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN(X_CHOOSE_THEN `b:real` MP_TAC)) THENL
     [DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
       `~(b = c) ==> &0 < abs(b - a) \/ &0 < abs(c - a)`)) THEN
      ASM_MESON_TAC[];
      MESON_TAC[REAL_LTE_TRANS]];
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `?x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) <= d` THENL
     [DISJ2_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `b:real`) THEN
      EXISTS_TAC `b:real` THEN ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL];
      DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`a + d:real`; `a:real`] THEN
      ASM_SIMP_TAC[REAL_ADD_SUB; REAL_EQ_ADD_LCANCEL_0; REAL_LT_IMP_NZ] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real` THEN
      ASM_CASES_TAC `(x:real) IN s` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC]]);;

let EVENTUALLY_WITHINREAL = prove
 (`!s a p.
     eventually p (atreal a within s) <=>
        ?d. &0 < d /\ !x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) < d ==> p(x)`,
  REWRITE_TAC[EVENTUALLY_WITHINREAL_LE] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`] THEN
  REWRITE_TAC[APPROACHABLE_LT_LE]);;

let EVENTUALLY_ATREAL = prove
 (`!a p. eventually p (atreal a) <=>
         ?d. &0 < d /\ !x. &0 < abs(x - a) /\ abs(x - a) < d ==> p(x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Usual limit results with real domain and either vector or real range.     *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHINREAL_LE = prove
 (`!f:real->real^N l a s.
        (f --> l) (atreal a within s) <=>
           !e. &0 < e ==> ?d. &0 < d /\
                              !x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) <= d
                                   ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_WITHINREAL_LE]);;

let LIM_WITHINREAL = prove
 (`!f:real->real^N l a s.
      (f --> l) (atreal a within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) < d
                    ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_WITHINREAL] THEN MESON_TAC[]);;

let LIM_ATREAL = prove
 (`!f l:real^N a.
      (f --> l) (atreal a) <=>
              !e. &0 < e
                  ==> ?d. &0 < d /\ !x. &0 < abs(x - a) /\ abs(x - a) < d
                          ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_ATREAL] THEN MESON_TAC[]);;

let REALLIM_WITHINREAL_LE = prove
 (`!f l a s.
        (f ---> l) (atreal a within s) <=>
           !e. &0 < e ==> ?d. &0 < d /\
                              !x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) <= d
                                   ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_WITHINREAL_LE]);;

let REALLIM_WITHINREAL = prove
 (`!f l a s.
      (f ---> l) (atreal a within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) < d
                    ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_WITHINREAL] THEN MESON_TAC[]);;

let REALLIM_ATREAL = prove
 (`!f l a.
      (f ---> l) (atreal a) <=>
              !e. &0 < e
                  ==> ?d. &0 < d /\ !x. &0 < abs(x - a) /\ abs(x - a) < d
                          ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_ATREAL] THEN MESON_TAC[]);;

let REALLIM_AT_POSINFINITY = prove
 (`!f l. (f ---> l) at_posinfinity <=>
               !e. &0 < e ==> ?b. !x. x >= b ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_AT_POSINFINITY] THEN MESON_TAC[]);;

let REALLIM_AT_NEGINFINITY = prove
 (`!f l. (f ---> l) at_neginfinity <=>
               !e. &0 < e ==> ?b. !x. x <= b ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_AT_NEGINFINITY] THEN MESON_TAC[]);;

let LIM_ATREAL_WITHINREAL = prove
 (`!f l a s. (f --> l) (atreal a) ==> (f --> l) (atreal a within s)`,
  REWRITE_TAC[LIM_ATREAL; LIM_WITHINREAL] THEN MESON_TAC[]);;

let REALLIM_ATREAL_WITHINREAL = prove
 (`!f l a s. (f ---> l) (atreal a) ==> (f ---> l) (atreal a within s)`,
  REWRITE_TAC[REALLIM_ATREAL; REALLIM_WITHINREAL] THEN MESON_TAC[]);;

let REALLIM_WITHIN_SUBSET = prove
 (`!f l a s t. (f ---> l) (at a within s) /\ t SUBSET s
               ==> (f ---> l) (at a within t)`,
  REWRITE_TAC[REALLIM_WITHIN; SUBSET] THEN MESON_TAC[]);;

let REALLIM_WITHINREAL_SUBSET = prove
 (`!f l a s t. (f ---> l) (atreal a within s) /\ t SUBSET s
               ==> (f ---> l) (atreal a within t)`,
  REWRITE_TAC[REALLIM_WITHINREAL; SUBSET] THEN MESON_TAC[]);;

let LIM_WITHINREAL_SUBSET = prove
 (`!f l a s t. (f --> l) (atreal a within s) /\ t SUBSET s
               ==> (f --> l) (atreal a within t)`,
  REWRITE_TAC[LIM_WITHINREAL; SUBSET] THEN MESON_TAC[]);;

let REALLIM_ATREAL_ID = prove
 (`((\x. x) ---> a) (atreal a)`,
  REWRITE_TAC[REALLIM_ATREAL] THEN MESON_TAC[]);;

let REALLIM_WITHINREAL_ID = prove
 (`!a. ((\x. x) ---> a) (atreal a within s)`,
  REWRITE_TAC[REALLIM_WITHINREAL] THEN MESON_TAC[]);;

let LIM_TRANSFORM_WITHINREAL_SET = prove
 (`!f a s t.
        eventually (\x. x IN s <=> x IN t) (atreal a)
        ==> ((f --> l) (atreal a within s) <=> (f --> l) (atreal a within t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVENTUALLY_ATREAL; LIM_WITHINREAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d k:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_MESON_TAC[]);;

let REALLIM_TRANSFORM_WITHIN_SET = prove
 (`!f a s t.
        eventually (\x. x IN s <=> x IN t) (at a)
        ==> ((f ---> l) (at a within s) <=> (f ---> l) (at a within t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVENTUALLY_AT; REALLIM_WITHIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d k:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_MESON_TAC[]);;

let REALLIM_TRANSFORM_WITHINREAL_SET = prove
 (`!f a s t.
        eventually (\x. x IN s <=> x IN t) (atreal a)
        ==> ((f ---> l) (atreal a within s) <=>
             (f ---> l) (atreal a within t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVENTUALLY_ATREAL; REALLIM_WITHINREAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d k:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_MESON_TAC[]);;

let REALLIM_COMPOSE_WITHIN = prove
 (`!net:A net f g s y z.
    (f ---> y) net /\
    eventually (\w. f w IN s /\ (f w = y ==> g y = z)) net /\
    (g ---> z) (atreal y within s)
    ==> ((g o f) ---> z) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto_real; CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[LEFT_AND_FORALL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EVENTUALLY_WITHINREAL; GSYM DIST_NZ; o_DEF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `(f:A->real) x = y` THEN
  ASM_MESON_TAC[REAL_ARITH `abs(x - y) = &0 <=> x = y`;
                REAL_ARITH `&0 < abs(x - y) <=> ~(x = y)`]);;

let REALLIM_COMPOSE_AT = prove
 (`!net:A net f g y z.
    (f ---> y) net /\
    eventually (\w. f w = y ==> g y = z) net /\
    (g ---> z) (atreal y)
    ==> ((g o f) ---> z) net`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`net:A net`; `f:A->real`; `g:real->real`;
                 `(:real)`; `y:real`; `z:real`]
        REALLIM_COMPOSE_WITHIN) THEN
  ASM_REWRITE_TAC[IN_UNIV; WITHINREAL_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Some real limits involving transcendentals.                               *)
(* ------------------------------------------------------------------------- *)

let REALLIM_1_OVER_N = prove
 (`((\n. inv(&n)) ---> &0) sequentially`,
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF; CX_INV; LIM_INV_N]);;

let REALLIM_1_OVER_POW = prove
 (`!k. 1 <= k ==> ((\n. inv(&n pow k)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. inv(&n pow 1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_ABS_NUM] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT; MATCH_MP_TAC REAL_POW_MONO] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; LE_1];
    REWRITE_TAC[REAL_POW_1; REALLIM_1_OVER_N]]);;

let REALLIM_LOG_OVER_N = prove
 (`((\n. log(&n) / &n) ---> &0) sequentially`,
  REWRITE_TAC[REALLIM_COMPLEX] THEN MP_TAC LIM_LOG_OVER_N THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  SIMP_TAC[o_DEF; CX_DIV; CX_LOG; REAL_OF_NUM_LT;
           ARITH_RULE `1 <= n ==> 0 < n`]);;

let REALLIM_1_OVER_LOG = prove
 (`((\n. inv(log(&n))) ---> &0) sequentially`,
  REWRITE_TAC[REALLIM_COMPLEX] THEN MP_TAC LIM_1_OVER_LOG THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[o_DEF; complex_div; COMPLEX_MUL_LID; CX_INV] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  SIMP_TAC[CX_LOG; REAL_OF_NUM_LT; ARITH_RULE `1 <= n ==> 0 < n`]);;

let REALLIM_POWN = prove
 (`!z. abs(z) < &1 ==> ((\n. z pow n) ---> &0) sequentially`,
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF; CX_POW] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_POWN THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX]);;

let REALLIM_X_TIMES_LOG = prove
 (`((\x. x * log x) ---> &0) (atreal(&0) within {x | &0 <= x})`,
  MP_TAC LIM_Z_TIMES_CLOG THEN
  REWRITE_TAC[REALLIM_WITHINREAL; LIM_AT] THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_SUB_RZERO; dist; COMPLEX_SUB_RZERO] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  ASM_CASES_TAC `&0 < d` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real` THEN
  ASM_CASES_TAC `x = &0` THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Cx x`) THEN
  ASM_SIMP_TAC[COMPLEX_NORM_MUL; GSYM CX_LOG; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Relations between limits at real and complex limit points.                *)
(* ------------------------------------------------------------------------- *)

let TRIVIAL_LIMIT_WITHINREAL_WITHIN = prove
 (`trivial_limit(atreal x within s) <=>
        trivial_limit(at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC[trivial_limit; AT; WITHIN; ATREAL] THEN
  REWRITE_TAC[FORALL_LIFT; EXISTS_LIFT; LIFT_EQ; DIST_LIFT] THEN
  REWRITE_TAC[IN_IMAGE_LIFT_DROP; LIFT_DROP]);;

let TRIVIAL_LIMIT_WITHINREAL_WITHINCOMPLEX = prove
 (`trivial_limit(atreal x within s) <=>
        trivial_limit(at (Cx x) within (real INTER IMAGE Cx s))`,
  REWRITE_TAC[trivial_limit; AT; WITHIN; ATREAL] THEN
  REWRITE_TAC[SET_RULE `x IN real INTER s <=> real x /\ x IN s`] THEN
  REWRITE_TAC[TAUT `~(p /\ x /\ q) /\ ~(r /\ x /\ s) <=>
                    x ==> ~(p /\ q) /\ ~(r /\ s)`] THEN
  REWRITE_TAC[FORALL_REAL;
    MESON[IN_IMAGE; CX_INJ] `Cx x IN IMAGE Cx s <=> x IN s`] THEN
  REWRITE_TAC[dist; GSYM CX_SUB; o_THM; RE_CX; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC(TAUT `~p /\ ~q /\ (r <=> s) ==> (p \/ r <=> q \/ s)`) THEN
  REPEAT CONJ_TAC THEN TRY EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN CONV_TAC REAL_RING;
    DISCH_THEN(MP_TAC o SPECL [`Cx(&0)`; `Cx(&1)`]) THEN
    CONV_TAC COMPLEX_RING;
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`Cx a`; `Cx b`] THEN ASM_REWRITE_TAC[CX_INJ] THEN
    ASM_REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX];
    MAP_EVERY X_GEN_TAC [`a:complex`; `b:complex`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?d. &0 < d /\
          !z. &0 < abs(z - x) /\ abs(z - x) <= d ==> ~(z IN s)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(MESON[] `!a b. P a \/ P b ==> ?x. P x`) THEN
      MAP_EVERY EXISTS_TAC [`norm(a - Cx x)`; `norm(b - Cx x)`] THEN
      ASM_REWRITE_TAC[TAUT `a ==> ~b <=> ~(a /\ b)`] THEN
      UNDISCH_TAC `~(a:complex = b)` THEN NORM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`x + d:real`; `x - d:real`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> ~(x + d = x - d)`;
                 REAL_ARITH `&0 < d ==> abs((x + d) - x) = d`;
                 REAL_ARITH `&0 < d ==> abs(x - d - x) = d`] THEN
    ASM_MESON_TAC[]]);;

let LIM_WITHINREAL_WITHINCOMPLEX = prove
 (`(f --> a) (atreal x within s) <=>
   ((f o Re) --> a) (at(Cx x) within (real INTER IMAGE Cx s))`,
  REWRITE_TAC[LIM_WITHINREAL; LIM_WITHIN] THEN
  REWRITE_TAC[SET_RULE `x IN real INTER s <=> real x /\ x IN s`] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_REAL;
    MESON[IN_IMAGE; CX_INJ] `Cx x IN IMAGE Cx s <=> x IN s`] THEN
  REWRITE_TAC[dist; GSYM CX_SUB; o_THM; RE_CX; COMPLEX_NORM_CX]);;

let LIM_ATREAL_ATCOMPLEX = prove
 (`(f --> a) (atreal x) <=> ((f o Re) --> a) (at (Cx x) within real)`,
  REWRITE_TAC[LIM_ATREAL; LIM_WITHIN] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_REAL; IN; dist; GSYM CX_SUB; COMPLEX_NORM_CX;
              o_THM; RE_CX]);;

(* ------------------------------------------------------------------------- *)
(* Simpler theorems relating limits in real and real^1.                      *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHINREAL_WITHIN = prove
 (`(f --> a) (atreal x within s) <=>
        ((f o drop) --> a) (at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC[LIM_WITHINREAL; LIM_WITHIN] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; DIST_LIFT; o_THM; LIFT_DROP]);;

let LIM_ATREAL_AT = prove
 (`(f --> a) (atreal x) <=> ((f o drop) --> a) (at (lift x))`,
  REWRITE_TAC[LIM_ATREAL; LIM_AT; FORALL_LIFT] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; DIST_LIFT; o_THM; LIFT_DROP]);;

let REALLIM_WITHINREAL_WITHIN = prove
 (`(f ---> a) (atreal x within s) <=>
        ((f o drop) ---> a) (at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC[REALLIM_WITHINREAL; REALLIM_WITHIN] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; DIST_LIFT; o_THM; LIFT_DROP]);;

let REALLIM_ATREAL_AT = prove
 (`(f ---> a) (atreal x) <=> ((f o drop) ---> a) (at (lift x))`,
  REWRITE_TAC[REALLIM_ATREAL; REALLIM_AT; FORALL_LIFT] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; DIST_LIFT; o_THM; LIFT_DROP]);;

let REALLIM_WITHIN_OPEN = prove
 (`!f:real^N->real l a s.
        a IN s /\ open s
        ==> ((f ---> l) (at a within s) <=> (f ---> l) (at a))`,
  REWRITE_TAC[TENDSTO_REAL; LIM_WITHIN_OPEN]);;

let LIM_WITHIN_REAL_OPEN = prove
 (`!f:real->real^N l a s.
        a IN s /\ real_open s
        ==> ((f --> l) (atreal a within s) <=> (f --> l) (atreal a))`,
  REWRITE_TAC[LIM_WITHINREAL_WITHIN; LIM_ATREAL_AT; REAL_OPEN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_WITHIN_OPEN THEN ASM SET_TAC[]);;

let REALLIM_WITHIN_REAL_OPEN = prove
 (`!f l a s.
        a IN s /\ real_open s
        ==> ((f ---> l) (atreal a within s) <=> (f ---> l) (atreal a))`,
  REWRITE_TAC[TENDSTO_REAL; LIM_WITHIN_REAL_OPEN]);;

(* ------------------------------------------------------------------------- *)
(* Additional congruence rules for simplifying limits.                       *)
(* ------------------------------------------------------------------------- *)

let LIM_CONG_WITHINREAL = prove
 (`(!x. ~(x = a) ==> f x = g x)
   ==> (((\x. f x) --> l) (atreal a within s) <=>
        ((g --> l) (atreal a within s)))`,
  SIMP_TAC[LIM_WITHINREAL; GSYM REAL_ABS_NZ; REAL_SUB_0]);;

let LIM_CONG_ATREAL = prove
 (`(!x. ~(x = a) ==> f x = g x)
   ==> (((\x. f x) --> l) (atreal a) <=> ((g --> l) (atreal a)))`,
  SIMP_TAC[LIM_ATREAL; GSYM REAL_ABS_NZ; REAL_SUB_0]);;

extend_basic_congs [LIM_CONG_WITHINREAL; LIM_CONG_ATREAL];;

let REALLIM_CONG_WITHIN = prove
 (`(!x. ~(x = a) ==> f x = g x)
   ==> (((\x. f x) ---> l) (at a within s) <=> ((g ---> l) (at a within s)))`,
  REWRITE_TAC[REALLIM_WITHIN; GSYM DIST_NZ] THEN SIMP_TAC[]);;

let REALLIM_CONG_AT = prove
 (`(!x. ~(x = a) ==> f x = g x)
   ==> (((\x. f x) ---> l) (at a) <=> ((g ---> l) (at a)))`,
  REWRITE_TAC[REALLIM_AT; GSYM DIST_NZ] THEN SIMP_TAC[]);;

extend_basic_congs [REALLIM_CONG_WITHIN; REALLIM_CONG_AT];;

let REALLIM_CONG_WITHINREAL = prove
 (`(!x. ~(x = a) ==> f x = g x)
   ==> (((\x. f x) ---> l) (atreal a within s) <=>
        ((g ---> l) (atreal a within s)))`,
  SIMP_TAC[REALLIM_WITHINREAL; GSYM REAL_ABS_NZ; REAL_SUB_0]);;

let REALLIM_CONG_ATREAL = prove
 (`(!x. ~(x = a) ==> f x = g x)
   ==> (((\x. f x) ---> l) (atreal a) <=> ((g ---> l) (atreal a)))`,
  SIMP_TAC[REALLIM_ATREAL; GSYM REAL_ABS_NZ; REAL_SUB_0]);;

extend_basic_congs [REALLIM_CONG_WITHINREAL; REALLIM_CONG_ATREAL];;

(* ------------------------------------------------------------------------- *)
(* Real version of Abel limit theorem.                                       *)
(* ------------------------------------------------------------------------- *)

let REAL_ABEL_LIMIT_THEOREM = prove
 (`!s a. real_summable s a
         ==> (!r. abs(r) < &1 ==> real_summable s (\i. a i * r pow i)) /\
             ((\r. real_infsum s  (\i. a i * r pow i)) ---> real_infsum s a)
             (atreal (&1) within {z | z <= &1})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`&1`; `s:num->bool`; `Cx o (a:num->real)`]
        ABEL_LIMIT_THEOREM) THEN
  ASM_REWRITE_TAC[GSYM REAL_SUMMABLE_COMPLEX; REAL_LT_01] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Cx r`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_SUMMABLE_COMPLEX] THEN
    REWRITE_TAC[o_DEF; CX_MUL; CX_POW];
    DISCH_TAC] THEN
  REWRITE_TAC[REALLIM_COMPLEX; LIM_WITHINREAL_WITHINCOMPLEX] THEN
  MATCH_MP_TAC LIM_TRANSFORM_WITHIN THEN
  EXISTS_TAC `\z. infsum s (\i. (Cx o a) i * z pow i)` THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [REWRITE_TAC[IMP_CONJ; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
    REWRITE_TAC[IN; FORALL_REAL] THEN X_GEN_TAC `r:real` THEN
    REWRITE_TAC[CX_INJ; UNWIND_THM1; dist; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `r <= &1 ==> (&0 < abs(r - &1) <=> r < &1)`] THEN
    REPEAT DISCH_TAC THEN SUBGOAL_THEN `abs(r) < &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_INFSUM_COMPLEX; o_THM; RE_CX] THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM REAL; o_DEF; CX_MUL; CX_POW] THEN
    MATCH_MP_TAC(ISPEC `sequentially` REAL_LIM) THEN
    EXISTS_TAC `\n. vsum(s INTER (0..n)) (\i. Cx(a i) * Cx r pow i)` THEN
    REWRITE_TAC[SEQUENTIALLY; TRIVIAL_LIMIT_SEQUENTIALLY; GSYM sums] THEN
    SIMP_TAC[GSYM CX_POW; GSYM CX_MUL; REAL_VSUM; FINITE_INTER; FINITE_NUMSEG;
             SUMS_INFSUM; REAL_CX; GE] THEN
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[LE_REFL]] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    ASM_SIMP_TAC[GSYM REAL_SUMMABLE_COMPLEX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INFSUM_COMPLEX] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_WITHIN]) THEN
  REWRITE_TAC[LIM_WITHIN] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LID; IN_ELIM_THM; IN_INTER; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  REWRITE_TAC[IMP_CONJ; IN; FORALL_REAL] THEN
  REWRITE_TAC[CX_INJ; UNWIND_THM1; dist; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `r <= &1 ==> (&0 < abs(r - &1) <=> r < &1)`] THEN
  REPEAT DISCH_TAC THEN SUBGOAL_THEN `abs(r) < &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `Cx r`) THEN
  REWRITE_TAC[CX_INJ; UNWIND_THM1; dist; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH `b = a ==> norm(x - a) < e ==> norm(x - b) < e`) THEN
  REWRITE_TAC[GSYM REAL] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REAL_LIM) THEN
  EXISTS_TAC `\n. vsum(s INTER (0..n)) (Cx o a)` THEN
  REWRITE_TAC[SEQUENTIALLY; TRIVIAL_LIMIT_SEQUENTIALLY; GSYM sums] THEN
  SIMP_TAC[GSYM CX_POW; GSYM CX_MUL; REAL_VSUM; FINITE_INTER; FINITE_NUMSEG;
           SUMS_INFSUM; REAL_CX; GE; o_DEF] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[LE_REFL]] THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  ASM_SIMP_TAC[GSYM REAL_SUMMABLE_COMPLEX]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of a function into the reals.                                  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("real_continuous",(12,"right"));;

let real_continuous = new_definition
  `f real_continuous net <=> (f ---> f(netlimit net)) net`;;

let REAL_CONTINUOUS_TRIVIAL_LIMIT = prove
 (`!f net. trivial_limit net ==> f real_continuous net`,
  SIMP_TAC[real_continuous; REALLIM]);;

let REAL_CONTINUOUS_WITHIN = prove
 (`!f x:real^N s.
        f real_continuous (at x within s) <=>
                (f ---> f(x)) (at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_continuous] THEN
  ASM_CASES_TAC `trivial_limit(at(x:real^N) within s)` THENL
   [ASM_REWRITE_TAC[REALLIM]; ASM_SIMP_TAC[NETLIMIT_WITHIN]]);;

let REAL_CONTINUOUS_AT = prove
 (`!f x. f real_continuous (at x) <=> (f ---> f(x)) (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHIN; IN_UNIV]);;

let REAL_CONTINUOUS_WITHINREAL = prove
 (`!f x s. f real_continuous (atreal x within s) <=>
                (f ---> f(x)) (atreal x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_continuous] THEN
  ASM_CASES_TAC `trivial_limit(atreal x within s)` THENL
   [ASM_REWRITE_TAC[REALLIM]; ASM_SIMP_TAC[NETLIMIT_WITHINREAL]]);;

let REAL_CONTINUOUS_ATREAL = prove
 (`!f x. f real_continuous (atreal x) <=> (f ---> f(x)) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; IN_UNIV]);;

let CONTINUOUS_WITHINREAL = prove
 (`!f x s. f continuous (atreal x within s) <=>
                 (f --> f(x)) (atreal x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous] THEN
  ASM_CASES_TAC `trivial_limit(atreal x within s)` THENL
   [ASM_REWRITE_TAC[LIM]; ASM_SIMP_TAC[NETLIMIT_WITHINREAL]]);;

let CONTINUOUS_ATREAL = prove
 (`!f x. f continuous (atreal x) <=> (f --> f(x)) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_WITHINREAL; IN_UNIV]);;

let real_continuous_within = prove
 (`f real_continuous (at x within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    (!x'. x' IN s /\ dist(x',x) < d ==> abs(f x' - f x) < e)`,
  REWRITE_TAC[REAL_CONTINUOUS_WITHIN; REALLIM_WITHIN] THEN
  REWRITE_TAC[GSYM DIST_NZ] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN
  ASM_MESON_TAC[REAL_ARITH `abs(x - x) = &0`]);;

let real_continuous_at = prove
 (`f real_continuous (at x) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    (!x'. dist(x',x) < d ==> abs(f x' - f x) < e)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[real_continuous_within; IN_UNIV]);;

let real_continuous_withinreal = prove
 (`f real_continuous (atreal x within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    (!x'. x' IN s /\ abs(x' - x) < d ==> abs(f x' - f x) < e)`,
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL] THEN
  REWRITE_TAC[REAL_ARITH `&0 < abs(x - y) <=> ~(x = y)`] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN
  ASM_MESON_TAC[REAL_ARITH `abs(x - x) = &0`]);;

let real_continuous_atreal = prove
 (`f real_continuous (atreal x) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    (!x'. abs(x' - x) < d ==> abs(f x' - f x) < e)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[real_continuous_withinreal; IN_UNIV]);;

let REAL_CONTINUOUS_AT_WITHIN = prove
 (`!f s x. f real_continuous (at x)
           ==> f real_continuous (at x within s)`,
  REWRITE_TAC[real_continuous_within; real_continuous_at] THEN
  MESON_TAC[]);;

let REAL_CONTINUOUS_ATREAL_WITHINREAL = prove
 (`!f s x. f real_continuous (atreal x)
           ==> f real_continuous (atreal x within s)`,
  REWRITE_TAC[real_continuous_withinreal; real_continuous_atreal] THEN
  MESON_TAC[]);;

let REAL_CONTINUOUS_WITHINREAL_SUBSET = prove
 (`!f s t. f real_continuous (atreal x within s) /\ t SUBSET s
             ==> f real_continuous (atreal x within t)`,
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL_SUBSET]);;

let REAL_CONTINUOUS_WITHIN_SUBSET = prove
 (`!f s t. f real_continuous (at x within s) /\ t SUBSET s
             ==> f real_continuous (at x within t)`,
  REWRITE_TAC[REAL_CONTINUOUS_WITHIN; REALLIM_WITHIN_SUBSET]);;

let CONTINUOUS_WITHINREAL_SUBSET = prove
 (`!f s t. f continuous (atreal x within s) /\ t SUBSET s
             ==> f continuous (atreal x within t)`,
  REWRITE_TAC[CONTINUOUS_WITHINREAL; LIM_WITHINREAL_SUBSET]);;

let continuous_withinreal = prove
 (`f continuous (atreal x within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    (!x'. x' IN s /\ abs(x' - x) < d ==> dist(f x',f x) < e)`,
  REWRITE_TAC[CONTINUOUS_WITHINREAL; LIM_WITHINREAL] THEN
  REWRITE_TAC[REAL_ARITH `&0 < abs(x - y) <=> ~(x = y)`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `d:real` THEN
  ASM_CASES_TAC `&0 < d` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[DIST_REFL]);;

let continuous_atreal = prove
 (`f continuous (atreal x) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    (!x'. abs(x' - x) < d ==> dist(f x',f x) < e)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[continuous_withinreal; IN_UNIV]);;

let CONTINUOUS_ATREAL_WITHINREAL = prove
 (`!f x s. f continuous (atreal x) ==> f continuous (atreal x within s)`,
  SIMP_TAC[continuous_atreal; continuous_withinreal] THEN MESON_TAC[]);;

let CONTINUOUS_CX_ATREAL = prove
 (`!x. Cx continuous (atreal x)`,
  GEN_TAC THEN REWRITE_TAC[continuous_atreal; dist] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; GSYM CX_SUB] THEN MESON_TAC[]);;

let CONTINUOUS_CX_WITHINREAL = prove
 (`!s x. Cx continuous (atreal x within s)`,
  SIMP_TAC[CONTINUOUS_ATREAL_WITHINREAL; CONTINUOUS_CX_ATREAL]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic combining theorems.                                            *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_CONST = prove
 (`!net c. (\x. c) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_CONST]);;

let REAL_CONTINUOUS_LMUL = prove
 (`!f c net. f real_continuous net ==> (\x. c * f(x)) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_LMUL]);;

let REAL_CONTINUOUS_RMUL = prove
 (`!f c net. f real_continuous net ==> (\x. f(x) * c) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_RMUL]);;

let REAL_CONTINUOUS_NEG = prove
 (`!f net. f real_continuous net ==> (\x. --(f x)) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_NEG]);;

let REAL_CONTINUOUS_ADD = prove
 (`!f g net. f real_continuous net /\ g real_continuous net
           ==> (\x. f(x) + g(x)) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_ADD]);;

let REAL_CONTINUOUS_SUB = prove
 (`!f g net. f real_continuous net /\ g real_continuous net
           ==> (\x. f(x) - g(x)) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_SUB]);;

let REAL_CONTINUOUS_MUL = prove
 (`!net f g.
     f real_continuous net /\ g real_continuous net
     ==> (\x. f(x) * g(x)) real_continuous net`,
  SIMP_TAC[real_continuous; REALLIM_MUL]);;

let REAL_CONTINUOUS_INV = prove
 (`!net f.
    f real_continuous net /\ ~(f(netlimit net) = &0)
    ==> (\x. inv(f x)) real_continuous net`,
  SIMP_TAC[real_continuous; REALLIM_INV]);;

let REAL_CONTINUOUS_DIV = prove
 (`!net f g.
    f real_continuous net /\ g real_continuous net /\ ~(g(netlimit net) = &0)
    ==> (\x. f(x) / g(x)) real_continuous net`,
  SIMP_TAC[real_continuous; REALLIM_DIV]);;

let REAL_CONTINUOUS_POW = prove
 (`!net f n. f real_continuous net ==> (\x. f(x) pow n) real_continuous net`,
  SIMP_TAC[real_continuous; REALLIM_POW]);;

let REAL_CONTINUOUS_ABS = prove
 (`!net f. f real_continuous net ==> (\x. abs(f(x))) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_ABS]);;

let REAL_CONTINUOUS_MAX = prove
 (`!f g net. f real_continuous net /\ g real_continuous net
           ==> (\x. max (f x) (g x)) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_MAX]);;

let REAL_CONTINUOUS_MIN = prove
 (`!f g net. f real_continuous net /\ g real_continuous net
           ==> (\x. min (f x) (g x)) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_MIN]);;

(* ------------------------------------------------------------------------- *)
(* Some of these without netlimit, but with many different cases.            *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_WITHIN_ID = prove
 (`!x s. (\x. x) real_continuous (atreal x within s)`,
  REWRITE_TAC[real_continuous_withinreal] THEN MESON_TAC[]);;

let REAL_CONTINUOUS_AT_ID = prove
 (`!x. (\x. x) real_continuous (atreal x)`,
  REWRITE_TAC[real_continuous_atreal] THEN MESON_TAC[]);;

let REAL_CONTINUOUS_INV_WITHIN = prove
 (`!f s a. f real_continuous (at a within s) /\ ~(f a = &0)
           ==> (\x. inv(f x)) real_continuous (at a within s)`,
  MESON_TAC[REAL_CONTINUOUS_INV; REAL_CONTINUOUS_TRIVIAL_LIMIT;
            NETLIMIT_WITHIN]);;

let REAL_CONTINUOUS_INV_AT = prove
 (`!f a. f real_continuous (at a) /\ ~(f a = &0)
         ==> (\x. inv(f x)) real_continuous (at a)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_INV_WITHIN]);;

let REAL_CONTINUOUS_INV_WITHINREAL = prove
 (`!f s a. f real_continuous (atreal a within s) /\ ~(f a = &0)
           ==> (\x. inv(f x)) real_continuous (atreal a within s)`,
  MESON_TAC[REAL_CONTINUOUS_INV; REAL_CONTINUOUS_TRIVIAL_LIMIT;
            NETLIMIT_WITHINREAL]);;

let REAL_CONTINUOUS_INV_ATREAL = prove
 (`!f a. f real_continuous (atreal a) /\ ~(f a = &0)
         ==> (\x. inv(f x)) real_continuous (atreal a)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_INV_WITHINREAL]);;

let REAL_CONTINUOUS_DIV_WITHIN = prove
 (`!f s a. f real_continuous (at a within s) /\
           g real_continuous (at a within s) /\ ~(g a = &0)
           ==> (\x. f x / g x) real_continuous (at a within s)`,
  MESON_TAC[REAL_CONTINUOUS_DIV; REAL_CONTINUOUS_TRIVIAL_LIMIT;
            NETLIMIT_WITHIN]);;

let REAL_CONTINUOUS_DIV_AT = prove
 (`!f a. f real_continuous (at a) /\
         g real_continuous (at a) /\ ~(g a = &0)
         ==> (\x. f x / g x) real_continuous (at a)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_DIV_WITHIN]);;

let REAL_CONTINUOUS_DIV_WITHINREAL = prove
 (`!f s a. f real_continuous (atreal a within s) /\
           g real_continuous (atreal a within s) /\ ~(g a = &0)
           ==> (\x. f x / g x) real_continuous (atreal a within s)`,
  MESON_TAC[REAL_CONTINUOUS_DIV; REAL_CONTINUOUS_TRIVIAL_LIMIT;
            NETLIMIT_WITHINREAL]);;

let REAL_CONTINUOUS_DIV_ATREAL = prove
 (`!f a. f real_continuous (atreal a) /\
         g real_continuous (atreal a) /\ ~(g a = &0)
         ==> (\x. f x / g x) real_continuous (atreal a)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_DIV_WITHINREAL]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real->real) o (real->real) functions.                     *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_WITHINREAL_COMPOSE = prove
 (`!f g x s. f real_continuous (atreal x within s) /\
             g real_continuous (atreal (f x) within IMAGE f s)
             ==> (g o f) real_continuous (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_continuous_withinreal; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let REAL_CONTINUOUS_ATREAL_COMPOSE = prove
 (`!f g x. f real_continuous (atreal x) /\ g real_continuous (atreal (f x))
           ==> (g o f) real_continuous (atreal x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_continuous_atreal; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real->real) o (real^N->real) functions.                   *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_WITHIN_COMPOSE = prove
 (`!f g x s. f real_continuous (at x within s) /\
             g real_continuous (atreal (f x) within IMAGE f s)
             ==> (g o f) real_continuous (at x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_continuous_withinreal; real_continuous_within;
              o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let REAL_CONTINUOUS_AT_COMPOSE = prove
 (`!f g x. f real_continuous (at x) /\
           g real_continuous (atreal (f x) within IMAGE f (:real^N))
           ==> (g o f) real_continuous (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHIN_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real^N->real) o (real^M->real^N) functions.               *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_CONTINUOUS_WITHIN_COMPOSE = prove
 (`!f g x s. f continuous (at x within s) /\
             g real_continuous (at (f x) within IMAGE f s)
             ==> (g o f) real_continuous (at x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_continuous_within; continuous_within; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let REAL_CONTINUOUS_CONTINUOUS_AT_COMPOSE = prove
 (`!f g x. f continuous (at x) /\
           g real_continuous (at (f x) within IMAGE f (:real^N))
           ==> (g o f) real_continuous (at x)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[WITHIN_WITHIN; INTER_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_WITHIN_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real^N->real) o (real->real^N) functions.                 *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE = prove
 (`!f g x s. f continuous (atreal x within s) /\
             g real_continuous (at (f x) within IMAGE f s)
             ==> (g o f) real_continuous (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_continuous_within; continuous_withinreal;
              real_continuous_withinreal; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let REAL_CONTINUOUS_CONTINUOUS_ATREAL_COMPOSE = prove
 (`!f g x. f continuous (atreal x) /\
           g real_continuous (at (f x) within IMAGE f (:real))
           ==> (g o f) real_continuous (atreal x)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real->real^N) o (real->real) functions.                   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_REAL_CONTINUOUS_WITHINREAL_COMPOSE = prove
 (`!f g x s. f real_continuous (atreal x within s) /\
             g continuous (atreal (f x) within IMAGE f s)
             ==> (g o f) continuous (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_continuous_within; continuous_withinreal;
              real_continuous_withinreal; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let CONTINUOUS_REAL_CONTINUOUS_ATREAL_COMPOSE = prove
 (`!f g x. f real_continuous (atreal x) /\
           g continuous (atreal (f x) within IMAGE f (:real))
           ==> (g o f) continuous (atreal x)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[WITHIN_WITHIN; INTER_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_REAL_CONTINUOUS_WITHINREAL_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real^M->real^N) o (real->real^M) functions.               *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHINREAL_COMPOSE = prove
 (`!f g x s. f continuous (atreal x within s) /\
             g continuous (at (f x) within IMAGE f s)
             ==> (g o f) continuous (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[continuous_within; continuous_withinreal; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let CONTINUOUS_ATREAL_COMPOSE = prove
 (`!f g x. f continuous (atreal x) /\
           g continuous (at (f x) within IMAGE f (:real))
           ==> (g o f) continuous (atreal x)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[WITHIN_WITHIN; INTER_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_WITHINREAL_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real->real^N) o (real^M->real) functions.                 *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_REAL_CONTINUOUS_WITHIN_COMPOSE = prove
 (`!f g x s. f real_continuous (at x within s) /\
             g continuous (atreal (f x) within IMAGE f s)
             ==> (g o f) continuous (at x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[continuous_within; real_continuous_within; continuous_withinreal;
              o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let CONTINUOUS_REAL_CONTINUOUS_AT_COMPOSE = prove
 (`!f g x. f real_continuous (at x) /\
           g continuous (atreal (f x) within IMAGE f (:real^M))
           ==> (g o f) continuous (at x)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[WITHIN_WITHIN; INTER_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_REAL_CONTINUOUS_WITHIN_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of a real->real function on a set.                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("real_continuous_on",(12,"right"));;

let real_continuous_on = new_definition
  `f real_continuous_on s <=>
        !x. x IN s ==> !e. &0 < e
                           ==> ?d. &0 < d /\
                                   !x'. x' IN s /\ abs(x' - x) < d
                                        ==> abs(f(x') - f(x)) < e`;;

let REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN = prove
 (`!f s. f real_continuous_on s <=>
              !x. x IN s ==> f real_continuous (atreal x within s)`,
  REWRITE_TAC[real_continuous_on; real_continuous_withinreal]);;

let REAL_CONTINUOUS_ON_SUBSET = prove
 (`!f s t. f real_continuous_on s /\ t SUBSET s ==> f real_continuous_on t`,
  REWRITE_TAC[real_continuous_on; SUBSET] THEN MESON_TAC[]);;

let REAL_CONTINUOUS_ON_COMPOSE = prove
 (`!f g s. f real_continuous_on s /\ g real_continuous_on (IMAGE f s)
           ==> (g o f) real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  MESON_TAC[IN_IMAGE; REAL_CONTINUOUS_WITHINREAL_COMPOSE]);;

let REAL_CONTINUOUS_ON = prove
 (`!f s. f real_continuous_on s <=>
          (lift o f o drop) continuous_on (IMAGE lift s)`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHINREAL; CONTINUOUS_WITHIN;
              FORALL_IN_IMAGE; REALLIM_WITHINREAL_WITHIN; TENDSTO_REAL] THEN
  REWRITE_TAC[o_THM; LIFT_DROP]);;

let REAL_CONTINUOUS_ON_CONST = prove
 (`!s c. (\x. c) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_CONST]);;

let REAL_CONTINUOUS_ON_ID = prove
 (`!s. (\x. x) real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHIN_ID]);;

let REAL_CONTINUOUS_ON_LMUL = prove
 (`!f c s. f real_continuous_on s ==> (\x. c * f(x)) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_LMUL]);;

let REAL_CONTINUOUS_ON_RMUL = prove
 (`!f c s. f real_continuous_on s ==> (\x. f(x) * c) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_RMUL]);;

let REAL_CONTINUOUS_ON_NEG = prove
 (`!f s. f real_continuous_on s
         ==> (\x. --(f x)) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_NEG]);;

let REAL_CONTINUOUS_ON_ADD = prove
 (`!f g s. f real_continuous_on s /\ g real_continuous_on s
           ==> (\x. f(x) + g(x)) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_ADD]);;

let REAL_CONTINUOUS_ON_SUB = prove
 (`!f g s. f real_continuous_on s /\ g real_continuous_on s
           ==> (\x. f(x) - g(x)) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_SUB]);;

let REAL_CONTINUOUS_ON_MUL = prove
 (`!f g s. f real_continuous_on s /\ g real_continuous_on s
           ==> (\x. f(x) * g(x)) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_MUL]);;

let REAL_CONTINUOUS_ON_POW = prove
 (`!f n s. f real_continuous_on s
           ==> (\x. f(x) pow n) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_POW]);;

let REAL_CONTINUOUS_ON_INV = prove
 (`!f s. f real_continuous_on s /\  (!x. x IN s ==> ~(f x = &0))
         ==> (\x. inv(f x)) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
           REAL_CONTINUOUS_INV_WITHINREAL]);;

let REAL_CONTINUOUS_ON_DIV = prove
 (`!f g s.
        f real_continuous_on s /\
        g real_continuous_on s /\
        (!x. x IN s ==> ~(g x = &0))
        ==> (\x. f x / g x) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
           REAL_CONTINUOUS_DIV_WITHINREAL]);;

let REAL_CONTINUOUS_ON_ABS = prove
 (`!f s. f real_continuous_on s ==> (\x. abs(f x)) real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  SIMP_TAC[REAL_CONTINUOUS_ABS]);;

let REAL_CONTINUOUS_ON_EQ = prove
 (`!f g s. (!x. x IN s ==> f(x) = g(x)) /\ f real_continuous_on s
           ==> g real_continuous_on s`,
  SIMP_TAC[real_continuous_on; IMP_CONJ]);;

let REAL_CONTINUOUS_ON_UNION = prove
 (`!f s t.
         real_closed s /\ real_closed t /\
         f real_continuous_on s /\ f real_continuous_on t
         ==> f real_continuous_on (s UNION t)`,
  REWRITE_TAC[REAL_CLOSED; REAL_CONTINUOUS_ON; IMAGE_UNION;
              CONTINUOUS_ON_UNION]);;

let REAL_CONTINUOUS_ON_UNION_OPEN = prove
 (`!f s t.
         real_open s /\ real_open t /\
         f real_continuous_on s /\ f real_continuous_on t
         ==> f real_continuous_on (s UNION t)`,
  REWRITE_TAC[REAL_OPEN; REAL_CONTINUOUS_ON; IMAGE_UNION;
              CONTINUOUS_ON_UNION_OPEN]);;

let REAL_CONTINUOUS_ON_CASES = prove
 (`!P f g s t.
        real_closed s /\ real_closed t /\
        f real_continuous_on s /\ g real_continuous_on t /\
        (!x. x IN s /\ ~P x \/ x IN t /\ P x ==> f x = g x)
        ==> (\x. if P x then f x else g x) real_continuous_on (s UNION t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_UNION THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THENL
   [EXISTS_TAC `f:real->real`; EXISTS_TAC `g:real->real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let REAL_CONTINUOUS_ON_CASES_OPEN = prove
 (`!P f g s t.
        real_open s /\ real_open t /\
        f real_continuous_on s /\ g real_continuous_on t /\
        (!x. x IN s /\ ~P x \/ x IN t /\ P x ==> f x = g x)
        ==> (\x. if P x then f x else g x) real_continuous_on (s UNION t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_UNION_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THENL
   [EXISTS_TAC `f:real->real`; EXISTS_TAC `g:real->real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let REAL_CONTINUOUS_ON_SUM = prove
 (`!t f s.
         FINITE s /\ (!a. a IN s ==> f a real_continuous_on t)
         ==> (\x. sum s (\a. f a x)) real_continuous_on t`,
  REPEAT GEN_TAC THEN SIMP_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_SUM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_VSUM) THEN
  REWRITE_TAC[]);;

let REALLIM_CONTINUOUS_FUNCTION = prove
 (`!f net g l.
        f continuous (atreal l) /\ (g ---> l) net
        ==> ((\x. f(g x)) --> f l) net`,
  REWRITE_TAC[tendsto_real; tendsto; continuous_atreal; eventually] THEN
  MESON_TAC[]);;

let LIM_REAL_CONTINUOUS_FUNCTION = prove
 (`!f net g l.
        f real_continuous (at l) /\ (g --> l) net
        ==> ((\x. f(g x)) ---> f l) net`,
  REWRITE_TAC[tendsto_real; tendsto; real_continuous_at; eventually] THEN
  MESON_TAC[]);;

let REALLIM_REAL_CONTINUOUS_FUNCTION = prove
 (`!f net g l.
        f real_continuous (atreal l) /\ (g ---> l) net
        ==> ((\x. f(g x)) ---> f l) net`,
  REWRITE_TAC[tendsto_real; real_continuous_atreal; eventually] THEN
  MESON_TAC[]);;

let REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT = prove
 (`!f s. real_open s
         ==> (f real_continuous_on s <=>
              !x. x IN s ==> f real_continuous atreal x)`,
  SIMP_TAC[REAL_CONTINUOUS_ATREAL; REAL_CONTINUOUS_WITHINREAL;
        REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REALLIM_WITHIN_REAL_OPEN]);;

let REAL_CONTINUOUS_ATTAINS_SUP = prove
 (`!f s. real_compact s /\ ~(s = {}) /\ f real_continuous_on s
         ==> ?x. x IN s /\ (!y. y IN s ==> f y <= f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(f:real->real) o drop`; `IMAGE lift s`]
        CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[GSYM REAL_CONTINUOUS_ON; GSYM real_compact] THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_THM; LIFT_DROP]);;

let REAL_CONTINUOUS_ATTAINS_INF = prove
 (`!f s. real_compact s /\ ~(s = {}) /\ f real_continuous_on s
         ==> ?x. x IN s /\ (!y. y IN s ==> f x <= f y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(f:real->real) o drop`; `IMAGE lift s`]
        CONTINUOUS_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[GSYM REAL_CONTINUOUS_ON; GSYM real_compact] THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_THM; LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Real version of uniform continuity.                                       *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("real_uniformly_continuous_on",(12,"right"));;

let real_uniformly_continuous_on = new_definition
  `f real_uniformly_continuous_on s <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. x IN s /\ x' IN s /\ abs(x' - x) < d
                           ==> abs(f x' - f x) < e`;;

let REAL_UNIFORMLY_CONTINUOUS_ON = prove
 (`!f s. f real_uniformly_continuous_on s <=>
          (lift o f o drop) uniformly_continuous_on (IMAGE lift s)`,
  REWRITE_TAC[real_uniformly_continuous_on; uniformly_continuous_on] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_THM; DIST_LIFT; LIFT_DROP]);;

let REAL_UNIFORMLY_CONTINUOUS_IMP_REAL_CONTINUOUS = prove
 (`!f s. f real_uniformly_continuous_on s ==> f real_continuous_on s`,
  REWRITE_TAC[real_uniformly_continuous_on; real_continuous_on] THEN
  MESON_TAC[]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY = prove
 (`!f s. f real_uniformly_continuous_on s <=>
                !x y. (!n. x(n) IN s) /\ (!n. y(n) IN s) /\
                      ((\n. x(n) - y(n)) ---> &0) sequentially
                      ==> ((\n. f(x(n)) - f(y(n))) ---> &0) sequentially`,
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON] THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY; REAL_TENDSTO] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; IN_IMAGE_LIFT_DROP; DROP_SUB; DROP_VEC] THEN
  REWRITE_TAC[FORALL_LIFT_FUN; o_THM; LIFT_DROP]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_SUBSET = prove
 (`!f s t. f real_uniformly_continuous_on s /\ t SUBSET s
           ==> f real_uniformly_continuous_on t`,
  REWRITE_TAC[real_uniformly_continuous_on; SUBSET] THEN MESON_TAC[]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_COMPOSE = prove
 (`!f g s. f real_uniformly_continuous_on s /\
           g real_uniformly_continuous_on (IMAGE f s)
           ==> (g o f) real_uniformly_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON] THEN
  SUBGOAL_THEN
   `IMAGE lift (IMAGE f s) = IMAGE (lift o f o drop) (IMAGE lift s)`
  SUBST1_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP UNIFORMLY_CONTINUOUS_ON_COMPOSE)] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_CONST = prove
 (`!s c. (\x. c) real_uniformly_continuous_on s`,
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY; o_DEF;
              REAL_SUB_REFL; REALLIM_CONST]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_LMUL = prove
 (`!f c s. f real_uniformly_continuous_on s
           ==> (\x. c * f(x)) real_uniformly_continuous_on s`,
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON] THEN
  REWRITE_TAC[o_DEF; LIFT_CMUL; UNIFORMLY_CONTINUOUS_ON_CMUL]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_RMUL = prove
 (`!f c s. f real_uniformly_continuous_on s
           ==> (\x. f(x) * c) real_uniformly_continuous_on s`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON_LMUL]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_ID = prove
 (`!s. (\x. x) real_uniformly_continuous_on s`,
  REWRITE_TAC[real_uniformly_continuous_on] THEN MESON_TAC[]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_NEG = prove
 (`!f s. f real_uniformly_continuous_on s
         ==> (\x. --(f x)) real_uniformly_continuous_on s`,
  ONCE_REWRITE_TAC[REAL_ARITH `--x = -- &1 * x`] THEN
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON_LMUL]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_ADD = prove
 (`!f g s. f real_uniformly_continuous_on s /\
           g real_uniformly_continuous_on s
           ==> (\x. f(x) + g(x)) real_uniformly_continuous_on s`,
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON; o_DEF; LIFT_ADD] THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_ADD]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_SUB = prove
 (`!f g s. f real_uniformly_continuous_on s /\
           g real_uniformly_continuous_on s
           ==> (\x. f(x) - g(x)) real_uniformly_continuous_on s`,
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON; o_DEF; LIFT_SUB] THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SUB]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_SUM = prove
 (`!t f s.
         FINITE s /\ (!a. a IN s ==> f a real_uniformly_continuous_on t)
         ==> (\x. sum s (\a. f a x)) real_uniformly_continuous_on t`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[REAL_UNIFORMLY_CONTINUOUS_ON; o_DEF; LIFT_SUM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP UNIFORMLY_CONTINUOUS_ON_VSUM) THEN
  REWRITE_TAC[]);;

let REAL_COMPACT_UNIFORMLY_CONTINUOUS = prove
 (`!f s. f real_continuous_on s /\ real_compact s
         ==> f real_uniformly_continuous_on s`,
  REWRITE_TAC[real_compact; REAL_CONTINUOUS_ON; REAL_UNIFORMLY_CONTINUOUS_ON;
              COMPACT_UNIFORMLY_CONTINUOUS]);;

let REAL_COMPACT_CONTINUOUS_IMAGE = prove
 (`!f s. f real_continuous_on s /\ real_compact s
         ==> real_compact (IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_compact; REAL_CONTINUOUS_ON] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_CONTINUOUS_IMAGE) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP]);;

let REAL_DINI = prove
 (`!f g s.
        real_compact s /\ (!n. (f n) real_continuous_on s) /\
        g real_continuous_on s /\
        (!x. x IN s ==> ((\n. (f n x)) ---> g x) sequentially) /\
        (!n x. x IN s ==> f n x <= f (n + 1) x)
        ==> !e. &0 < e
                ==> eventually (\n. !x. x IN s ==> abs(f n x - g x) < e)
                               sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n:num. lift o f n o drop`; `lift o g o drop`;
                 `IMAGE lift s`] DINI) THEN
  ASM_REWRITE_TAC[GSYM real_compact; GSYM REAL_CONTINUOUS_ON] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; o_DEF; LIFT_DROP; REAL_TENDSTO] THEN
  ASM_SIMP_TAC[GSYM LIFT_SUB; NORM_LIFT]);;

(* ------------------------------------------------------------------------- *)
(* Continuity versus componentwise continuity.                               *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_COMPONENTWISE = prove
 (`!net f:A->real^N.
        f continuous net <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. (f x)$i) real_continuous net`,
  REWRITE_TAC[real_continuous; continuous; LIM_COMPONENTWISE]);;

let REAL_CONTINUOUS_COMPLEX_COMPONENTS_AT = prove
 (`!z. Re real_continuous (at z) /\ Im real_continuous (at z)`,
  GEN_TAC THEN MP_TAC(ISPECL
   [`at(z:complex)`; `\z:complex. z`] CONTINUOUS_COMPONENTWISE) THEN
  REWRITE_TAC[CONTINUOUS_AT_ID; DIMINDEX_2; FORALL_2] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; ETA_AX]);;

let REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN = prove
 (`!s z. Re real_continuous (at z within s) /\
         Im real_continuous (at z within s)`,
  MESON_TAC[REAL_CONTINUOUS_COMPLEX_COMPONENTS_AT;
              REAL_CONTINUOUS_AT_WITHIN]);;

let REAL_CONTINUOUS_NORM_AT = prove
 (`!z. norm real_continuous (at z)`,
  REWRITE_TAC[real_continuous_at; dist] THEN
  GEN_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN NORM_ARITH_TAC);;

let REAL_CONTINUOUS_NORM_WITHIN = prove
 (`!s z. norm real_continuous (at z within s)`,
  MESON_TAC[REAL_CONTINUOUS_NORM_AT; REAL_CONTINUOUS_AT_WITHIN]);;

let REAL_CONTINUOUS_DIST_AT = prove
 (`!a z. (\x. dist(a,x)) real_continuous (at z)`,
  REWRITE_TAC[real_continuous_at; dist] THEN
  GEN_TAC THEN GEN_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN NORM_ARITH_TAC);;

let REAL_CONTINUOUS_DIST_WITHIN = prove
 (`!a s z. (\x. dist(a,x)) real_continuous (at z within s)`,
  MESON_TAC[REAL_CONTINUOUS_DIST_AT; REAL_CONTINUOUS_AT_WITHIN]);;

(* ------------------------------------------------------------------------- *)
(* Derivative of real->real function.                                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("has_real_derivative",(12,"right"));;
parse_as_infix ("real_differentiable",(12,"right"));;
parse_as_infix ("real_differentiable_on",(12,"right"));;

let has_real_derivative = new_definition
 `(f has_real_derivative f') net <=>
        ((\x. inv(x - netlimit net) *
              (f x - (f(netlimit net) + f' * (x - netlimit net))))
         ---> &0) net`;;

let real_differentiable = new_definition
 `f real_differentiable net <=> ?f'. (f has_real_derivative f') net`;;

let real_derivative = new_definition
 `real_derivative f x = @f'. (f has_real_derivative f') (atreal x)`;;

let higher_real_derivative = define
 `higher_real_derivative 0 f = f /\
  (!n. higher_real_derivative (SUC n) f =
                real_derivative (higher_real_derivative n f))`;;

let real_differentiable_on = new_definition
 `f real_differentiable_on s <=>
     !x. x IN s ==> ?f'. (f has_real_derivative f') (atreal x within s)`;;

(* ------------------------------------------------------------------------- *)
(* Basic limit definitions in the useful cases.                              *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_WITHINREAL = prove
 (`(f has_real_derivative f') (atreal a within s) <=>
           ((\x. (f x - f a) / (x - a)) ---> f') (atreal a within s)`,
  REWRITE_TAC[has_real_derivative] THEN
  ASM_CASES_TAC `trivial_limit(atreal a within s)` THENL
   [ASM_REWRITE_TAC[REALLIM]; ALL_TAC] THEN
  ASM_SIMP_TAC[NETLIMIT_WITHINREAL] THEN
  GEN_REWRITE_TAC RAND_CONV [REALLIM_NULL] THEN
  REWRITE_TAC[REALLIM_WITHINREAL; REAL_SUB_RZERO] THEN
  SIMP_TAC[REAL_FIELD
   `&0 < abs(x - a) ==> (fy - fa) / (x - a) - f' =
                        inv(x - a) * (fy - (fa + f' * (x - a)))`]);;

let HAS_REAL_DERIVATIVE_ATREAL = prove
 (`(f has_real_derivative f') (atreal a) <=>
           ((\x. (f x - f a) / (x - a)) ---> f') (atreal a)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL]);;

(* ------------------------------------------------------------------------- *)
(* Relation to Frechet derivative.                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_FRECHET_DERIVATIVE_WITHIN = prove
 (`(f has_real_derivative f') (atreal x within s) <=>
        ((lift o f o drop) has_derivative (\x. f' % x))
        (at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC[has_derivative_within; HAS_REAL_DERIVATIVE_WITHINREAL] THEN
  REWRITE_TAC[o_THM; LIFT_DROP; LIM_WITHIN; REALLIM_WITHINREAL] THEN
  SIMP_TAC[LINEAR_COMPOSE_CMUL; LINEAR_ID; IMP_CONJ] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; DIST_LIFT; GSYM LIFT_SUB; LIFT_DROP;
    NORM_ARITH `dist(x,vec 0) = norm x`; GSYM LIFT_CMUL; GSYM LIFT_ADD;
    NORM_LIFT] THEN
  SIMP_TAC[REAL_FIELD
   `&0 < abs(y - x)
    ==> fy - (fx + f' * (y - x)) = (y - x) * ((fy - fx) / (y - x) - f')`] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_ASSOC; REAL_ABS_INV; REAL_ABS_ABS] THEN
  SIMP_TAC[REAL_LT_IMP_NZ; REAL_MUL_LINV; REAL_MUL_LID]);;

let HAS_REAL_FRECHET_DERIVATIVE_AT = prove
 (`(f has_real_derivative f') (atreal x) <=>
        ((lift o f o drop) has_derivative (\x. f' % x)) (at (lift x))`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV; GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN] THEN
  REWRITE_TAC[IMAGE_LIFT_UNIV]);;

let HAS_REAL_VECTOR_DERIVATIVE_WITHIN = prove
 (`(f has_real_derivative f') (atreal x within s) <=>
        ((lift o f o drop) has_vector_derivative (lift f'))
        (at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC[has_vector_derivative; HAS_REAL_FRECHET_DERIVATIVE_WITHIN] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_LIFT; GSYM LIFT_CMUL] THEN
  REWRITE_TAC[LIFT_DROP; LIFT_EQ; REAL_MUL_SYM]);;

let HAS_REAL_VECTOR_DERIVATIVE_AT = prove
 (`(f has_real_derivative f') (atreal x) <=>
        ((lift o f o drop) has_vector_derivative (lift f')) (at (lift x))`,
  REWRITE_TAC[has_vector_derivative; HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_LIFT; GSYM LIFT_CMUL] THEN
  REWRITE_TAC[LIFT_DROP; LIFT_EQ; REAL_MUL_SYM]);;

let REAL_DIFFERENTIABLE_AT = prove
 (`!f a. f real_differentiable (atreal x) <=>
         (lift o f o drop) differentiable (at(lift x))`,
  REWRITE_TAC[real_differentiable; HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  REWRITE_TAC[differentiable; has_derivative; LINEAR_SCALING] THEN
  REWRITE_TAC[LINEAR_1; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2]);;

let REAL_DIFFERENTIABLE_WITHIN = prove
 (`!f a s.
        f real_differentiable (atreal x within s) <=>
        (lift o f o drop) differentiable (at(lift x) within IMAGE lift s)`,
  REWRITE_TAC[real_differentiable; HAS_REAL_FRECHET_DERIVATIVE_WITHIN] THEN
  REWRITE_TAC[differentiable; has_derivative; LINEAR_SCALING] THEN
  REWRITE_TAC[LINEAR_1; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2]);;

(* ------------------------------------------------------------------------- *)
(* Relation to complex derivative.                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_COMPLEX_DERIVATIVE_WITHIN = prove
 (`(f has_real_derivative f') (atreal a within s) <=>
        ((Cx o f o Re) has_complex_derivative (Cx f'))
                (at (Cx a) within {z | real z /\ Re z IN s})`,
  REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL; HAS_COMPLEX_DERIVATIVE_WITHIN;
              LIM_WITHIN; IN_ELIM_THM; IMP_CONJ; FORALL_REAL] THEN
  REWRITE_TAC[RE_CX; dist; GSYM CX_SUB; COMPLEX_NORM_CX; o_THM; GSYM CX_DIV;
              REALLIM_WITHINREAL] THEN
  MESON_TAC[]);;

let HAS_REAL_COMPLEX_DERIVATIVE_AT = prove
 (`(f has_real_derivative f') (atreal a) <=>
       ((Cx o f o Re) has_complex_derivative (Cx f')) (at (Cx a) within real)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE = prove
 (`!f s. f real_differentiable_on s <=>
         !x. x IN s ==> f real_differentiable (atreal x within s)`,
  REWRITE_TAC[real_differentiable_on; real_differentiable]);;

let REAL_DIFFERENTIABLE_ON_REAL_OPEN = prove
 (`!f s. real_open s
         ==> (f real_differentiable_on s <=>
              !x. x IN s ==> ?f'. (f has_real_derivative f') (atreal x))`,
  REWRITE_TAC[real_differentiable_on; HAS_REAL_DERIVATIVE_WITHINREAL;
              HAS_REAL_DERIVATIVE_ATREAL] THEN
  SIMP_TAC[REALLIM_WITHIN_REAL_OPEN]);;

let REAL_DIFFERENTIABLE_ON_IMP_DIFFERENTIABLE_WITHIN = prove
 (`!f s x. f real_differentiable_on s /\ x IN s
           ==> f real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE]);;

let REAL_DIFFERENTIABLE_ON_IMP_DIFFERENTIABLE_ATREAL = prove
 (`!f s x. f real_differentiable_on s /\ real_open s /\ x IN s
           ==> f real_differentiable (atreal x)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ON_REAL_OPEN; real_differentiable]);;

let HAS_COMPLEX_REAL_DERIVATIVE_WITHIN_GEN = prove
 (`!f g h s d.
        &0 < d /\ x IN s /\
        (h has_complex_derivative Cx(g))
        (at (Cx x) within {z | real z /\ Re(z) IN s}) /\
        (!y. y IN s /\ abs(y - x) < d ==>  h(Cx y) = Cx(f y))
        ==> (f has_real_derivative g) (atreal x within s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`h:complex->complex`; `d:real`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; o_THM; REAL_CX; RE_CX; dist] THEN
  X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Re w`) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o GEN_REWRITE_RULE I [REAL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CX_SUB; COMPLEX_NORM_CX]) THEN
  ASM_REWRITE_TAC[RE_CX]);;

let HAS_COMPLEX_REAL_DERIVATIVE_AT_GEN = prove
 (`!f g h d.
        &0 < d /\
        (h has_complex_derivative Cx(g)) (at (Cx x) within real) /\
        (!y. abs(y - x) < d ==>  h(Cx y) = Cx(f y))
        ==> (f has_real_derivative g) (atreal x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_WITHIN_GEN THEN
  MAP_EVERY EXISTS_TAC [`h:complex->complex`; `d:real`] THEN
  ASM_REWRITE_TAC[IN_UNIV; ETA_AX; SET_RULE `{x | r x} = r`]);;

let HAS_COMPLEX_REAL_DERIVATIVE_WITHIN = prove
 (`!f g h s.
        x IN s /\
        (h has_complex_derivative Cx(g))
        (at (Cx x) within {z | real z /\ Re(z) IN s}) /\
        (!y. y IN s ==>  h(Cx y) = Cx(f y))
        ==> (f has_real_derivative g) (atreal x within s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_WITHIN_GEN THEN
  MAP_EVERY EXISTS_TAC [`h:complex->complex`; `&1`] THEN
  ASM_SIMP_TAC[REAL_LT_01]);;

let HAS_COMPLEX_REAL_DERIVATIVE_AT = prove
 (`!f g h.
        (h has_complex_derivative Cx(g)) (at (Cx x) within real) /\
        (!y. h(Cx y) = Cx(f y))
        ==> (f has_real_derivative g) (atreal x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_WITHIN THEN
  EXISTS_TAC `h:complex->complex` THEN
  ASM_REWRITE_TAC[IN_UNIV; ETA_AX; SET_RULE `{x | r x} = r`]);;

(* ------------------------------------------------------------------------- *)
(* Caratheodory characterization.                                            *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_CARATHEODORY_ATREAL = prove
 (`!f f' z.
        (f has_real_derivative f') (atreal z) <=>
        ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\
            g real_continuous atreal z /\ g(z) = f'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_RING `w' - z':real = a <=> w' = z' + a`] THEN
  SIMP_TAC[GSYM FUN_EQ_THM; HAS_REAL_DERIVATIVE_ATREAL;
           REAL_CONTINUOUS_ATREAL] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `\w. if w = z then f':real else (f(w) - f(z)) / (w - z)` THEN
    ASM_SIMP_TAC[FUN_EQ_THM; COND_RAND; COND_RATOR; REAL_SUB_REFL] THEN
    CONV_TAC REAL_FIELD;
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_RING `(z + a) - (z + b * (w - w)):real = a`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      REALLIM_TRANSFORM)) THEN
    SIMP_TAC[REALLIM_CONST; REAL_FIELD
     `~(w = z) ==> x - (x * (w - z)) / (w - z) = &0`]]);;

let HAS_REAL_DERIVATIVE_CARATHEODORY_WITHINREAL = prove
 (`!f f' z s.
        (f has_real_derivative f') (atreal z within s) <=>
        ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\
            g real_continuous (atreal z within s) /\ g(z) = f'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_RING `w' - z':real = a <=> w' = z' + a`] THEN
  SIMP_TAC[GSYM FUN_EQ_THM; HAS_REAL_DERIVATIVE_WITHINREAL;
           REAL_CONTINUOUS_WITHINREAL] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `\w. if w = z then f':real else (f(w) - f(z)) / (w - z)` THEN
    ASM_SIMP_TAC[FUN_EQ_THM; COND_RAND; COND_RATOR; REAL_SUB_REFL] THEN
    CONV_TAC REAL_FIELD;
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_RING `(z + a) - (z + b * (w - w)):real = a`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      REALLIM_TRANSFORM)) THEN
    SIMP_TAC[REALLIM_CONST; REAL_FIELD
     `~(w = z) ==> x - (x * (w - z)) / (w - z) = &0`]]);;

let REAL_DIFFERENTIABLE_CARATHEODORY_ATREAL = prove
 (`!f z. f real_differentiable atreal z <=>
         ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\ g real_continuous atreal z`,
  SIMP_TAC[real_differentiable; HAS_REAL_DERIVATIVE_CARATHEODORY_ATREAL] THEN
  MESON_TAC[]);;

let REAL_DIFFERENTIABLE_CARATHEODORY_WITHINREAL = prove
 (`!f z s.
      f real_differentiable (atreal z within s) <=>
      ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\
          g real_continuous (atreal z within s)`,
  SIMP_TAC[real_differentiable;
           HAS_REAL_DERIVATIVE_CARATHEODORY_WITHINREAL] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Property of being an interval (equivalent to convex or connected).        *)
(* ------------------------------------------------------------------------- *)

let is_realinterval = new_definition
 `is_realinterval s <=>
        !a b c. a IN s /\ b IN s /\ a <= c /\ c <= b ==> c IN s`;;

let IS_REALINTERVAL_IS_INTERVAL = prove
 (`!s. is_realinterval s <=> is_interval(IMAGE lift s)`,
  REWRITE_TAC[IS_INTERVAL_1; is_realinterval] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[LIFT_DROP; IN_IMAGE; EXISTS_DROP; UNWIND_THM1] THEN
  REWRITE_TAC[GSYM FORALL_DROP]);;

let IS_REALINTERVAL_CONVEX = prove
 (`!s. is_realinterval s <=> convex(IMAGE lift s)`,
  REWRITE_TAC[IS_REALINTERVAL_IS_INTERVAL; IS_INTERVAL_CONVEX_1]);;

let IS_REALINTERVAL_CONNECTED = prove
 (`!s. is_realinterval s <=> connected(IMAGE lift s)`,
  REWRITE_TAC[IS_REALINTERVAL_IS_INTERVAL; IS_INTERVAL_CONNECTED_1]);;

let TRIVIAL_LIMIT_WITHIN_REALINTERVAL = prove
 (`!s x. is_realinterval s /\ x IN s
         ==> (trivial_limit(atreal x within s) <=> s = {x})`,
  REWRITE_TAC[TRIVIAL_LIMIT_WITHINREAL_WITHIN; IS_REALINTERVAL_CONVEX] THEN
  REWRITE_TAC[FORALL_DROP; GSYM IN_IMAGE_LIFT_DROP; LIFT_DROP] THEN
  SIMP_TAC[TRIVIAL_LIMIT_WITHIN_CONVEX] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE_LIFT_DROP; IN_SING] THEN
  MESON_TAC[LIFT_DROP]);;

let IS_REALINTERVAL_EMPTY = prove
 (`is_realinterval {}`,
  REWRITE_TAC[is_realinterval; NOT_IN_EMPTY]);;

let IS_REALINTERVAL_UNION = prove
 (`!s t. is_realinterval s /\ is_realinterval t /\ ~(s INTER t = {})
         ==> is_realinterval(s UNION t)`,
  REWRITE_TAC[is_realinterval; IN_UNION; IN_INTER;
              NOT_IN_EMPTY; EXTENSION] THEN
  MESON_TAC[REAL_LE_TRANS; REAL_LE_TOTAL]);;

let IS_REALINTERVAL_UNIV = prove
 (`is_realinterval (:real)`,
  REWRITE_TAC[is_realinterval; IN_UNIV]);;

let IS_REAL_INTERVAL_CASES = prove
 (`!s. is_realinterval s <=>
        s = {} \/
        s = (:real) \/
        (?a. s = {x | a < x}) \/
        (?a. s = {x | a <= x}) \/
        (?b. s = {x | x <= b}) \/
        (?b. s = {x | x < b}) \/
        (?a b. s = {x | a < x /\ x < b}) \/
        (?a b. s = {x | a < x /\ x <= b}) \/
        (?a b. s = {x | a <= x /\ x < b}) \/
        (?a b. s = {x | a <= x /\ x <= b})`,
  REWRITE_TAC[IS_REALINTERVAL_IS_INTERVAL; IS_INTERVAL_1_CASES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE_LIFT_DROP; IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM FORALL_DROP; IN_UNIV; NOT_IN_EMPTY]);;

let REAL_CONVEX = prove
 (`!s. is_realinterval s <=>
       !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ u + v = &1
                 ==> (u * x + v * y) IN s`,
  REWRITE_TAC[IS_REALINTERVAL_CONVEX; convex] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE_LIFT_DROP; DROP_ADD; DROP_CMUL; LIFT_DROP]);;

let REAL_CONVEX_ALT = prove
 (`!s. is_realinterval s <=>
       !x y u. x IN s /\ y IN s /\ &0 <= u /\ u <= &1
                 ==> ((&1 - u) * x + u * y) IN s`,
  REWRITE_TAC[IS_REALINTERVAL_CONVEX; CONVEX_ALT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE_LIFT_DROP; DROP_ADD; DROP_CMUL; LIFT_DROP]);;

let REAL_MIDPOINT_IN_CONVEX = prove
 (`!s x y. is_realinterval s /\ x IN s /\ y IN s ==> ((x + y) / &2) IN s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `(x + y) / &2 = inv(&2) * x + inv(&2) * y`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [REAL_CONVEX]) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some relations with the complex numbers can also be useful.               *)
(* ------------------------------------------------------------------------- *)

let IS_REALINTERVAL_CONVEX_COMPLEX = prove
 (`!s. is_realinterval s <=> convex {z | real z /\ Re z IN s}`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM IMAGE_CX; IS_REALINTERVAL_CONVEX] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o ISPEC `Cx o drop` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] CONVEX_LINEAR_IMAGE)) THEN
    REWRITE_TAC[GSYM IMAGE_o; GSYM o_ASSOC] THEN
    ONCE_REWRITE_TAC[IMAGE_o] THEN REWRITE_TAC[IMAGE_LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; o_THM; CX_ADD; CX_MUL; DROP_ADD; DROP_CMUL;
                COMPLEX_CMUL];
    DISCH_THEN(MP_TAC o ISPEC `lift o Re` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] CONVEX_LINEAR_IMAGE)) THEN
    REWRITE_TAC[GSYM IMAGE_o; GSYM o_ASSOC] THEN
    ONCE_REWRITE_TAC[IMAGE_o] THEN
    REWRITE_TAC[o_DEF; RE_CX; SET_RULE `IMAGE (\x. x) s = s`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; o_THM; RE_CMUL;
                RE_ADD; RE_MUL_CX; LIFT_ADD; LIFT_CMUL]]);;

(* ------------------------------------------------------------------------- *)
(* The same tricks to define closed and open intervals.                      *)
(* ------------------------------------------------------------------------- *)

let open_real_interval = new_definition
  `open_real_interval(a:real,b:real) = {x:real | a < x /\ x < b}`;;

let closed_real_interval = define
  `closed_real_interval[a:real,b:real] = {x:real | a <= x /\ x <= b}`;;

make_overloadable "real_interval" `:A`;;

overload_interface("real_interval",`open_real_interval`);;
overload_interface("real_interval",`closed_real_interval`);;

let real_interval = prove
 (`real_interval(a,b) = {x | a < x /\ x < b} /\
   real_interval[a,b] = {x | a <= x /\ x <= b}`,
  REWRITE_TAC[open_real_interval; closed_real_interval]);;

let IN_REAL_INTERVAL = prove
 (`!a b x. (x IN real_interval[a,b] <=> a <= x /\ x <= b) /\
           (x IN real_interval(a,b) <=> a < x /\ x < b)`,
  REWRITE_TAC[real_interval; IN_ELIM_THM]);;

let REAL_INTERVAL_INTERVAL = prove
 (`real_interval[a,b] = IMAGE drop (interval[lift a,lift b]) /\
   real_interval(a,b) = IMAGE drop (interval(lift a,lift b))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTERVAL_1; IN_REAL_INTERVAL] THEN
  REWRITE_TAC[EXISTS_LIFT; LIFT_DROP; UNWIND_THM1]);;

let INTERVAL_REAL_INTERVAL = prove
 (`interval[a,b] = IMAGE lift (real_interval[drop a,drop b]) /\
   interval(a,b) = IMAGE lift (real_interval(drop a,drop b))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTERVAL_1; IN_REAL_INTERVAL] THEN
  REWRITE_TAC[EXISTS_DROP; LIFT_DROP; UNWIND_THM1]);;

let EMPTY_AS_REAL_INTERVAL = prove
 (`{} = real_interval[&1,&0]`,
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; LIFT_NUM; GSYM EMPTY_AS_INTERVAL] THEN
  REWRITE_TAC[IMAGE_CLAUSES]);;

let IMAGE_LIFT_REAL_INTERVAL = prove
 (`IMAGE lift (real_interval[a,b]) = interval[lift a,lift b] /\
   IMAGE lift (real_interval(a,b)) = interval(lift a,lift b)`,
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; GSYM IMAGE_o; o_DEF; LIFT_DROP] THEN
  SET_TAC[]);;

let IMAGE_DROP_INTERVAL = prove
 (`IMAGE drop (interval[a,b]) = real_interval[drop a,drop b] /\
   IMAGE drop (interval(a,b)) = real_interval(drop a,drop b)`,
  REWRITE_TAC[INTERVAL_REAL_INTERVAL; GSYM IMAGE_o; o_DEF; LIFT_DROP] THEN
  SET_TAC[]);;

let SUBSET_REAL_INTERVAL = prove
 (`!a b c d.
        (real_interval[a,b] SUBSET real_interval[c,d] <=>
                b < a \/ c <= a /\ a <= b /\ b <= d) /\
        (real_interval[a,b] SUBSET real_interval(c,d) <=>
                b < a \/ c < a /\ a <= b /\ b < d) /\
        (real_interval(a,b) SUBSET real_interval[c,d] <=>
                b <= a \/ c <= a /\ a < b /\ b <= d) /\
        (real_interval(a,b) SUBSET real_interval(c,d) <=>
                b <= a \/ c <= a /\ a < b /\ b <= d)`,
  let lemma = prove
   (`IMAGE drop s SUBSET IMAGE drop t <=> s SUBSET t`,
    SET_TAC[LIFT_DROP]) in
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; lemma; SUBSET_INTERVAL_1] THEN
  REWRITE_TAC[LIFT_DROP]);;

let REAL_INTERVAL_OPEN_SUBSET_CLOSED = prove
 (`!a b. real_interval(a,b) SUBSET real_interval[a,b]`,
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let REAL_INTERVAL_EQ_EMPTY = prove
 (`(!a b. real_interval[a,b] = {} <=> b < a) /\
   (!a b. real_interval(a,b) = {} <=> b <= a)`,
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; LIFT_DROP]);;

let REAL_INTERVAL_NE_EMPTY = prove
 (`(!a b. ~(real_interval[a,b] = {}) <=> a <= b) /\
   (!a b. ~(real_interval(a,b) = {}) <=> a < b)`,
  REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_NOT_LE; REAL_NOT_LT]);;

let REAL_OPEN_CLOSED_INTERVAL = prove
 (`!a b. real_interval(a,b) = real_interval[a,b] DIFF {a,b}`,
  SIMP_TAC[EXTENSION; IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

let REAL_CLOSED_OPEN_INTERVAL = prove
 (`!a b. a <= b ==> real_interval[a,b] = real_interval(a,b) UNION {a,b}`,
  SIMP_TAC[EXTENSION; IN_UNION; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

let REAL_CLOSED_REAL_INTERVAL = prove
 (`!a b. real_closed(real_interval[a,b])`,
  REWRITE_TAC[REAL_CLOSED; IMAGE_LIFT_REAL_INTERVAL; CLOSED_INTERVAL]);;

let REAL_OPEN_REAL_INTERVAL = prove
 (`!a b. real_open(real_interval(a,b))`,
  REWRITE_TAC[REAL_OPEN; IMAGE_LIFT_REAL_INTERVAL; OPEN_INTERVAL]);;

let REAL_INTERVAL_SING = prove
 (`!a. real_interval[a,a] = {a} /\ real_interval(a,a) = {}`,
  REWRITE_TAC[EXTENSION; IN_SING; NOT_IN_EMPTY; IN_REAL_INTERVAL] THEN
  REAL_ARITH_TAC);;

let REAL_COMPACT_INTERVAL = prove
 (`!a b. real_compact(real_interval[a,b])`,
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; real_compact] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP; IMAGE_ID; COMPACT_INTERVAL]);;

let IS_REALINTERVAL_INTERVAL = prove
 (`!a b. is_realinterval(real_interval(a,b)) /\
         is_realinterval(real_interval[a,b])`,
  REWRITE_TAC[is_realinterval; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let REAL_BOUNDED_REAL_INTERVAL = prove
 (`(!a b. real_bounded(real_interval[a,b])) /\
   (!a b. real_bounded(real_interval(a,b)))`,
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; REAL_BOUNDED; BOUNDED_INTERVAL]);;

let ENDS_IN_REAL_INTERVAL = prove
 (`(!a b. a IN real_interval[a,b] <=> ~(real_interval[a,b] = {})) /\
   (!a b. b IN real_interval[a,b] <=> ~(real_interval[a,b] = {})) /\
   (!a b. ~(a IN real_interval(a,b))) /\
   (!a b. ~(b IN real_interval(a,b)))`,
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN REAL_ARITH_TAC);;

let IMAGE_AFFINITY_REAL_INTERVAL = prove
 (`!a b m c.
         IMAGE (\x. m * x + c) (real_interval[a,b]) =
         (if real_interval[a,b] = {}
          then {}
          else if &0 <= m
               then real_interval[m * a + c,m * b + c]
               else real_interval[m * b + c,m * a + c])`,
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; GSYM IMAGE_o; o_DEF; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[FORALL_DROP; LIFT_DROP; GSYM DROP_CMUL; GSYM DROP_ADD] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  REWRITE_TAC[IMAGE_o; IMAGE_AFFINITY_INTERVAL] THEN
  MESON_TAC[IMAGE_CLAUSES]);;

let IMAGE_STRETCH_REAL_INTERVAL = prove
 (`!a b m.
         IMAGE (\x. m * x) (real_interval[a,b]) =
         (if real_interval[a,b] = {}
          then {}
          else if &0 <= m
               then real_interval[m * a,m * b]
               else real_interval[m * b,m * a])`,
  ONCE_REWRITE_TAC[REAL_ARITH `m * x = m * x + &0`] THEN
  REWRITE_TAC[IMAGE_AFFINITY_REAL_INTERVAL]);;

let REAL_INTERVAL_TRANSLATION = prove
 (`(!c a b. real_interval[c + a,c + b] =
            IMAGE (\x. c + x) (real_interval[a,b])) /\
   (!c a b. real_interval(c + a,c + b) =
            IMAGE (\x. c + x) (real_interval(a,b)))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[REAL_ARITH `c + x:real = y <=> x = y - c`; EXISTS_REFL] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let IN_REAL_INTERVAL_REFLECT = prove
 (`(!a b x. --x IN real_interval[--b,--a] <=> x IN real_interval[a,b]) /\
   (!a b x. --x IN real_interval(--b,--a) <=> x IN real_interval(a,b))`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let REFLECT_REAL_INTERVAL = prove
 (`(!a b. IMAGE (--) (real_interval[a,b]) = real_interval[--b,--a]) /\
   (!a b. IMAGE (--) (real_interval(a,b)) = real_interval(--b,--a))`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_REAL_INTERVAL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x:real = --y <=> --x = y`] THEN
  REWRITE_TAC[UNWIND_THM1] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Real continuity and differentiability.                                    *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_CONTINUOUS = prove
 (`f real_continuous net <=> (Cx o f) continuous net`,
  REWRITE_TAC[real_continuous; continuous; REALLIM_COMPLEX; o_THM]);;

let REAL_CONTINUOUS_CONTINUOUS1 = prove
 (`f real_continuous net <=> (lift o f) continuous net`,
  REWRITE_TAC[real_continuous; continuous; TENDSTO_REAL; o_THM]);;

let REAL_CONTINUOUS_CONTINUOUS_ATREAL = prove
 (`f real_continuous (atreal x) <=> (lift o f o drop) continuous (at(lift x))`,
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL_AT; CONTINUOUS_AT;
              TENDSTO_REAL; o_THM; LIFT_DROP]);;

let REAL_CONTINUOUS_CONTINUOUS_WITHINREAL = prove
 (`f real_continuous (atreal x within s) <=>
   (lift o f o drop) continuous (at(lift x) within IMAGE lift s)`,
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL_WITHIN] THEN
  REWRITE_TAC[TENDSTO_REAL; CONTINUOUS_WITHIN; o_THM; LIFT_DROP]);;

let REAL_COMPLEX_CONTINUOUS_WITHINREAL = prove
 (`f real_continuous (atreal x within s) <=>
       (Cx o f o Re) continuous (at (Cx x) within (real INTER IMAGE Cx s))`,
  REWRITE_TAC[real_continuous; continuous; REALLIM_COMPLEX;
         LIM_WITHINREAL_WITHINCOMPLEX; NETLIMIT_WITHINREAL; GSYM o_ASSOC] THEN
  ASM_CASES_TAC `trivial_limit(at(Cx x) within (real INTER IMAGE Cx s))` THENL
   [ASM_REWRITE_TAC[LIM];
    ASM_SIMP_TAC[TRIVIAL_LIMIT_WITHINREAL_WITHINCOMPLEX;
        NETLIMIT_WITHIN; NETLIMIT_WITHINREAL; RE_CX; o_THM]]);;

let REAL_COMPLEX_CONTINUOUS_ATREAL = prove
 (`f real_continuous (atreal x) <=>
       (Cx o f o Re) continuous (at (Cx x) within real)`,
  REWRITE_TAC[real_continuous; continuous; REALLIM_COMPLEX;
              LIM_ATREAL_ATCOMPLEX; NETLIMIT_ATREAL; GSYM o_ASSOC] THEN
  ASM_CASES_TAC `trivial_limit(at(Cx x) within real)` THENL
   [ASM_REWRITE_TAC[LIM];
    ASM_SIMP_TAC[NETLIMIT_WITHIN; RE_CX; o_THM]]);;

let CONTINUOUS_CONTINUOUS_WITHINREAL = prove
 (`!f x s. f continuous (atreal x within s) <=>
           (f o drop) continuous (at (lift x) within IMAGE lift s)`,
  REWRITE_TAC[REALLIM_WITHINREAL_WITHIN; CONTINUOUS_WITHIN;
          CONTINUOUS_WITHINREAL; o_DEF; LIFT_DROP; LIM_WITHINREAL_WITHIN]);;

let CONTINUOUS_CONTINUOUS_ATREAL = prove
 (`!f x. f continuous (atreal x) <=> (f o drop) continuous (at (lift x))`,
  REWRITE_TAC[REALLIM_ATREAL_AT; CONTINUOUS_AT;
          CONTINUOUS_ATREAL; o_DEF; LIFT_DROP; LIM_ATREAL_AT]);;

let REAL_CONTINUOUS_REAL_CONTINUOUS_WITHINREAL = prove
 (`!f x s. f real_continuous (atreal x within s) <=>
           (f o drop) real_continuous (at (lift x) within IMAGE lift s)`,
  REWRITE_TAC[REALLIM_WITHINREAL_WITHIN; REAL_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHINREAL; o_DEF; LIFT_DROP;
              LIM_WITHINREAL_WITHIN]);;

let REAL_CONTINUOUS_REAL_CONTINUOUS_ATREAL = prove
 (`!f x. f real_continuous (atreal x) <=>
         (f o drop) real_continuous (at (lift x))`,
  REWRITE_TAC[REALLIM_ATREAL_AT; REAL_CONTINUOUS_AT;
          REAL_CONTINUOUS_ATREAL; o_DEF; LIFT_DROP; LIM_ATREAL_AT]);;
let HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL = prove
 (`!f f' x s. (f has_real_derivative f') (atreal x within s)
              ==> f real_continuous (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN;
              REAL_COMPLEX_CONTINUOUS_WITHINREAL] THEN
  DISCH_THEN(MP_TAC o
    MATCH_MP HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_WITHIN) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_IMAGE] THEN
  MESON_TAC[REAL; RE_CX; REAL_CX; IN]);;

let REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL = prove
 (`!f x s. f real_differentiable (atreal x within s)
           ==> f real_continuous (atreal x within s)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL;
            real_differentiable]);;

let HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL = prove
 (`!f f' x. (f has_real_derivative f') (atreal x)
            ==> f real_continuous (atreal x)`,
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_AT;
              REAL_COMPLEX_CONTINUOUS_ATREAL;
              HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_WITHIN]);;

let REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL = prove
 (`!f x. f real_differentiable atreal x ==> f real_continuous atreal x`,
  MESON_TAC[HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL; real_differentiable]);;

let REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON = prove
 (`!f s. f real_differentiable_on s ==> f real_continuous_on s`,
  REWRITE_TAC[real_differentiable_on;
              REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  MESON_TAC[REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL;
            real_differentiable]);;

let REAL_CONTINUOUS_AT_COMPONENT = prove
 (`!i a. 1 <= i /\ i <= dimindex(:N)
         ==> (\x:real^N. x$i) real_continuous at a`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF;
              CONTINUOUS_AT_LIFT_COMPONENT]);;

let REAL_CONTINUOUS_AT_TRANSLATION = prove
 (`!a z f:real^N->real.
    f real_continuous at (a + z) <=> (\x. f(a + x)) real_continuous at z`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF; CONTINUOUS_AT_TRANSLATION]);;

add_translation_invariants [REAL_CONTINUOUS_AT_TRANSLATION];;

let REAL_CONTINUOUS_AT_LINEAR_IMAGE = prove
 (`!h:real^N->real^N z f:real^N->real.
        linear h /\ (!x. norm(h x) = norm x)
        ==> (f real_continuous at (h z) <=> (\x. f(h x)) real_continuous at z)`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF;
              CONTINUOUS_AT_LINEAR_IMAGE]);;

add_linear_invariants [REAL_CONTINUOUS_AT_LINEAR_IMAGE];;

let REAL_CONTINUOUS_AT_ARG = prove
 (`!z. ~(real z /\ &0 <= Re z) ==> Arg real_continuous (at z)`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS; CONTINUOUS_AT_ARG]);;

(* ------------------------------------------------------------------------- *)
(* More basics about real derivatives.                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_WITHIN_SUBSET = prove
 (`!f s t x. (f has_real_derivative f') (atreal x within s) /\ t SUBSET s
             ==> (f has_real_derivative f') (atreal x within t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
   HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET) THEN ASM SET_TAC[]);;

let REAL_DIFFERENTIABLE_ON_SUBSET = prove
 (`!f s t. f real_differentiable_on s /\ t SUBSET s
           ==> f real_differentiable_on t`,
  REWRITE_TAC[real_differentiable_on] THEN
  MESON_TAC[SUBSET; HAS_REAL_DERIVATIVE_WITHIN_SUBSET]);;

let REAL_DIFFERENTIABLE_WITHIN_SUBSET = prove
 (`!f s t. f real_differentiable (atreal x within s) /\ t SUBSET s
           ==> f real_differentiable (atreal x within t)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_WITHIN_SUBSET]);;

let HAS_REAL_DERIVATIVE_ATREAL_WITHIN = prove
 (`!f f' x s. (f has_real_derivative f') (atreal x)
              ==> (f has_real_derivative f') (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN;
              HAS_REAL_COMPLEX_DERIVATIVE_AT] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
     HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET) THEN ASM SET_TAC[]);;

let HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN = prove
 (`!f f' a s.
         a IN s /\ real_open s
         ==> ((f has_real_derivative f') (atreal a within s) <=>
              (f has_real_derivative f') (atreal a))`,
  REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_WITHINREAL; HAS_REAL_DERIVATIVE_ATREAL;
               REALLIM_WITHIN_REAL_OPEN]);;

let REAL_DIFFERENTIABLE_ATREAL_WITHIN = prove
 (`!f s z. f real_differentiable (atreal z)
           ==> f real_differentiable (atreal z within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN]);;

let HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN = prove
 (`!f f' g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ abs(x' - x) < d ==> f x' = g x') /\
       (f has_real_derivative f') (atreal x within s)
       ==> (g has_real_derivative f') (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE
    [TAUT `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> d ==> e`]
    HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[IN_ELIM_THM; REAL_CX; RE_CX] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
   `dist(a,b) < d ==> z <= norm(a - b) ==> z < d`)) THEN
  W(MP_TAC o PART_MATCH (rand o rand) COMPLEX_NORM_GE_RE_IM o rand o snd) THEN
  SIMP_TAC[RE_SUB; RE_CX]);;

let HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL = prove
 (`!f f' g x d.
       &0 < d /\ (!x'. abs(x' - x) < d ==> f x' = g x') /\
       (f has_real_derivative f') (atreal x)
       ==> (g has_real_derivative f') (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN; IN_UNIV]);;

let HAS_REAL_DERIVATIVE_ZERO_CONSTANT = prove
 (`!f s.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative (&0)) (atreal x within s))
        ==> ?c. !x. x IN s ==> f(x) = c`,
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Cx o f o Re`; `{z | real z /\ Re z IN s}`]
    HAS_COMPLEX_DERIVATIVE_ZERO_CONSTANT) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IMP_CONJ; FORALL_REAL; RE_CX; o_THM] THEN
  ASM_REWRITE_TAC[GSYM IS_REALINTERVAL_CONVEX_COMPLEX] THEN MESON_TAC[RE_CX]);;

let HAS_REAL_DERIVATIVE_ZERO_UNIQUE = prove
 (`!f s c a.
        is_realinterval s /\ a IN s /\ f a = c /\
        (!x. x IN s ==> (f has_real_derivative (&0)) (atreal x within s))
        ==> !x. x IN s ==> f(x) = c`,
  MESON_TAC[HAS_REAL_DERIVATIVE_ZERO_CONSTANT]);;

let REAL_DIFF_CHAIN_WITHIN = prove
 (`!f g f' g' x s.
        (f has_real_derivative f') (atreal x within s) /\
        (g has_real_derivative g') (atreal (f x) within (IMAGE f s))
        ==> ((g o f) has_real_derivative (g' * f'))(atreal x within s)`,
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Cx o (g o f) o Re = (Cx o g o Re) o (Cx o f o Re)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_DEF; RE_CX]; ALL_TAC] THEN
  REWRITE_TAC[CX_MUL] THEN MATCH_MP_TAC COMPLEX_DIFF_CHAIN_WITHIN THEN
  ASM_REWRITE_TAC[o_THM; RE_CX] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_ELIM_THM; o_THM; REAL_CX; RE_CX] THEN SET_TAC[]);;

let REAL_DIFF_CHAIN_ATREAL = prove
 (`!f g f' g' x.
        (f has_real_derivative f') (atreal x) /\
        (g has_real_derivative g') (atreal (f x))
        ==> ((g o f) has_real_derivative (g' * f')) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  ASM_MESON_TAC[REAL_DIFF_CHAIN_WITHIN; SUBSET_UNIV;
                HAS_REAL_DERIVATIVE_WITHIN_SUBSET]);;

let HAS_REAL_DERIVATIVE_CHAIN = prove
 (`!P f g.
        (!x. P x ==> (g has_real_derivative g'(x)) (atreal x))
        ==> (!x s. (f has_real_derivative f') (atreal x within s) /\ P(f x)
                   ==> ((\x. g(f x)) has_real_derivative f' * g'(f x))
                       (atreal x within s)) /\
            (!x. (f has_real_derivative f') (atreal x) /\ P(f x)
                 ==> ((\x. g(f x)) has_real_derivative f' * g'(f x))
                     (atreal x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM o_DEF] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_MESON_TAC[REAL_DIFF_CHAIN_WITHIN; REAL_DIFF_CHAIN_ATREAL;
                HAS_REAL_DERIVATIVE_ATREAL_WITHIN]);;

let HAS_REAL_DERIVATIVE_CHAIN_UNIV = prove
 (`!f g. (!x. (g has_real_derivative g'(x)) (atreal x))
         ==> (!x s. (f has_real_derivative f') (atreal x within s)
                    ==> ((\x. g(f x)) has_real_derivative f' * g'(f x))
                        (atreal x within s)) /\
             (!x. (f has_real_derivative f') (atreal x)
                  ==> ((\x. g(f x)) has_real_derivative f' * g'(f x))
                      (atreal x))`,
  MP_TAC(SPEC `\x:real. T` HAS_REAL_DERIVATIVE_CHAIN) THEN SIMP_TAC[]);;

let REAL_DERIVATIVE_UNIQUE_ATREAL = prove
 (`!f z f' f''.
        (f has_real_derivative f') (atreal z) /\
        (f has_real_derivative f'') (atreal z)
        ==> f' = f''`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  DISCH_THEN(MP_TAC o C AP_THM `vec 1:real^1`) THEN
  REWRITE_TAC[VECTOR_MUL_RCANCEL; VEC_EQ; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Some handy theorems about the actual differentition function.             *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_DERIVATIVE = prove
 (`!f f' x. (f has_real_derivative f') (atreal x)
            ==> real_derivative f x = f'`,
  REWRITE_TAC[real_derivative] THEN
  MESON_TAC[REAL_DERIVATIVE_UNIQUE_ATREAL]);;

let HAS_REAL_DERIVATIVE_DIFFERENTIABLE = prove
 (`!f x. (f has_real_derivative (real_derivative f x)) (atreal x) <=>
         f real_differentiable atreal x`,
  REWRITE_TAC[real_differentiable; real_derivative] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetical combining theorems.                                          *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_LMUL_WITHIN = prove
 (`!f f' c x s.
        (f has_real_derivative f') (atreal x within s)
        ==> ((\x. c * f(x)) has_real_derivative (c * f')) (atreal x within s)`,
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  REWRITE_TAC[o_DEF; CX_MUL; HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN]);;

let HAS_REAL_DERIVATIVE_LMUL_ATREAL = prove
 (`!f f' c x.
        (f has_real_derivative f') (atreal x)
        ==> ((\x. c * f(x)) has_real_derivative (c * f')) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_LMUL_WITHIN]);;

let HAS_REAL_DERIVATIVE_RMUL_WITHIN = prove
 (`!f f' c x s.
        (f has_real_derivative f') (atreal x within s)
        ==> ((\x. f(x) * c) has_real_derivative (f' * c)) (atreal x within s)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_LMUL_WITHIN]);;

let HAS_REAL_DERIVATIVE_RMUL_ATREAL = prove
 (`!f f' c x.
        (f has_real_derivative f') (atreal x)
        ==> ((\x. f(x) * c) has_real_derivative (f' * c)) (atreal x)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_LMUL_ATREAL]);;

let HAS_REAL_DERIVATIVE_CDIV_WITHIN = prove
 (`!f f' c x s.
        (f has_real_derivative f') (atreal x within s)
        ==> ((\x. f(x) / c) has_real_derivative (f' / c)) (atreal x within s)`,
  SIMP_TAC[real_div; HAS_REAL_DERIVATIVE_RMUL_WITHIN]);;

let HAS_REAL_DERIVATIVE_CDIV_ATREAL = prove
 (`!f f' c x.
        (f has_real_derivative f') (atreal x)
        ==> ((\x. f(x) / c) has_real_derivative (f' / c)) (atreal x)`,
  SIMP_TAC[real_div; HAS_REAL_DERIVATIVE_RMUL_ATREAL]);;

let HAS_REAL_DERIVATIVE_ID = prove
 (`!net. ((\x. x) has_real_derivative &1) net`,
  REWRITE_TAC[has_real_derivative; TENDSTO_REAL;
              REAL_ARITH `x - (a + &1 * (x - a)) = &0`] THEN
  REWRITE_TAC[REAL_MUL_RZERO; LIM_CONST; o_DEF]);;

let HAS_REAL_DERIVATIVE_CONST = prove
 (`!c net. ((\x. c) has_real_derivative &0) net`,
  REWRITE_TAC[has_real_derivative; REAL_MUL_LZERO; REAL_ADD_RID; REAL_SUB_REFL;
              REAL_MUL_RZERO; REALLIM_CONST]);;

let HAS_REAL_DERIVATIVE_NEG = prove
 (`!f f' net. (f has_real_derivative f') net
            ==> ((\x. --(f(x))) has_real_derivative (--f')) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_derivative] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_NEG) THEN
  REWRITE_TAC[REAL_NEG_0; REAL_ARITH
   `a * (--b - (--c + --d * e:real)) = --(a * (b - (c + d * e)))`]);;

let HAS_REAL_DERIVATIVE_ADD = prove
 (`!f f' g g' net.
        (f has_real_derivative f') net /\ (g has_real_derivative g') net
        ==> ((\x. f(x) + g(x)) has_real_derivative (f' + g')) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_derivative] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_ADD) THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; REAL_ADD_RID] THEN
  REWRITE_TAC[REAL_ARITH
   `(fx - (fa + f' * (x - a))) + (gx - (ga + g' * (x - a))):real =
    (fx + gx) - ((fa + ga) + (f' + g') * (x - a))`]);;

let HAS_REAL_DERIVATIVE_SUB = prove
 (`!f f' g g' net.
        (f has_real_derivative f') net /\ (g has_real_derivative g') net
        ==> ((\x. f(x) - g(x)) has_real_derivative (f' - g')) net`,
  SIMP_TAC[real_sub; HAS_REAL_DERIVATIVE_ADD; HAS_REAL_DERIVATIVE_NEG]);;

let HAS_REAL_DERIVATIVE_MUL_WITHIN = prove
 (`!f f' g g' x s.
        (f has_real_derivative f') (atreal x within s) /\
        (g has_real_derivative g') (atreal x within s)
        ==> ((\x. f(x) * g(x)) has_real_derivative
             (f(x) * g' + f' * g(x))) (atreal x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_MUL_WITHIN) THEN
  REWRITE_TAC[o_DEF; CX_MUL; CX_ADD; RE_CX]);;

let HAS_REAL_DERIVATIVE_MUL_ATREAL = prove
 (`!f f' g g' x.
        (f has_real_derivative f') (atreal x) /\
        (g has_real_derivative g') (atreal x)
        ==> ((\x. f(x) * g(x)) has_real_derivative
             (f(x) * g' + f' * g(x))) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_MUL_WITHIN]);;

let HAS_REAL_DERIVATIVE_POW_WITHIN = prove
 (`!f f' x s n. (f has_real_derivative f') (atreal x within s)
                ==> ((\x. f(x) pow n) has_real_derivative
                     (&n * f(x) pow (n - 1) * f')) (atreal x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o
    MATCH_MP HAS_COMPLEX_DERIVATIVE_POW_WITHIN) THEN
  REWRITE_TAC[o_DEF; CX_MUL; CX_POW; RE_CX]);;

let HAS_REAL_DERIVATIVE_POW_ATREAL = prove
 (`!f f' x n. (f has_real_derivative f') (atreal x)
              ==> ((\x. f(x) pow n) has_real_derivative
                   (&n * f(x) pow (n - 1) * f')) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_POW_WITHIN]);;

let HAS_REAL_DERIVATIVE_INV_BASIC = prove
 (`!x. ~(x = &0)
         ==> ((inv) has_real_derivative (--inv(x pow 2))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_AT] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN THEN
  EXISTS_TAC `inv:complex->complex` THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_INV_BASIC; CX_INJ; CX_NEG; CX_INV;
               CX_POW; HAS_COMPLEX_DERIVATIVE_AT_WITHIN] THEN
  SIMP_TAC[IN; FORALL_REAL; IMP_CONJ; o_DEF; REAL_CX; RE_CX; CX_INV] THEN
  MESON_TAC[REAL_LT_01]);;

let HAS_REAL_DERIVATIVE_INV_WITHIN = prove
 (`!f f' x s. (f has_real_derivative f') (atreal x within s) /\
              ~(f x = &0)
              ==> ((\x. inv(f(x))) has_real_derivative (--f' / f(x) pow 2))
                  (atreal x within s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `~(g = &0) ==> --f / g pow 2 = --inv(g pow 2) * f`] THEN
  MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_INV_BASIC]);;

let HAS_REAL_DERIVATIVE_INV_ATREAL = prove
 (`!f f' x. (f has_real_derivative f') (atreal x) /\
            ~(f x = &0)
            ==> ((\x. inv(f(x))) has_real_derivative (--f' / f(x) pow 2))
                (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_INV_WITHIN]);;

let HAS_REAL_DERIVATIVE_DIV_WITHIN = prove
 (`!f f' g g' x s.
        (f has_real_derivative f') (atreal x within s) /\
        (g has_real_derivative g') (atreal x within s) /\
        ~(g(x) = &0)
        ==> ((\x. f(x) / g(x)) has_real_derivative
             (f' * g(x) - f(x) * g') / g(x) pow 2) (atreal x within s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT2 th) THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_INV_WITHIN) THEN
  UNDISCH_TAC `(f has_real_derivative f') (atreal x within s)` THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_MUL_WITHIN) THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;

let HAS_REAL_DERIVATIVE_DIV_ATREAL = prove
 (`!f f' g g' x.
        (f has_real_derivative f') (atreal x) /\
        (g has_real_derivative g') (atreal x) /\
        ~(g(x) = &0)
        ==> ((\x. f(x) / g(x)) has_real_derivative
             (f' * g(x) - f(x) * g') / g(x) pow 2) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_DIV_WITHIN]);;

let HAS_REAL_DERIVATIVE_SUM = prove
 (`!f net s.
         FINITE s /\ (!a. a IN s ==> (f a has_real_derivative f' a) net)
         ==> ((\x. sum s (\a. f a x)) has_real_derivative (sum s f'))
             net`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; SUM_CLAUSES] THEN
  SIMP_TAC[HAS_REAL_DERIVATIVE_CONST; HAS_REAL_DERIVATIVE_ADD; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Same thing just for real differentiability.                               *)
(* ------------------------------------------------------------------------- *)

let REAL_DIFFERENTIABLE_CONST = prove
 (`!c net. (\z. c) real_differentiable net`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_CONST]);;

let REAL_DIFFERENTIABLE_ID = prove
 (`!net. (\z. z) real_differentiable net`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_ID]);;

let REAL_DIFFERENTIABLE_NEG = prove
 (`!f net.
        f real_differentiable net
        ==> (\z. --(f z)) real_differentiable net`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_NEG]);;

let REAL_DIFFERENTIABLE_ADD = prove
 (`!f g net.
        f real_differentiable net /\
        g real_differentiable net
        ==> (\z. f z + g z) real_differentiable net`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_ADD]);;

let REAL_DIFFERENTIABLE_SUB = prove
 (`!f g net.
        f real_differentiable net /\
        g real_differentiable net
        ==> (\z. f z - g z) real_differentiable net`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_SUB]);;

let REAL_DIFFERENTIABLE_INV_WITHIN = prove
 (`!f z s.
        f real_differentiable (atreal z within s) /\ ~(f z = &0)
        ==> (\z. inv(f z)) real_differentiable (atreal z within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_INV_WITHIN]);;

let REAL_DIFFERENTIABLE_MUL_WITHIN = prove
 (`!f g z s.
        f real_differentiable (atreal z within s) /\
        g real_differentiable (atreal z within s)
        ==> (\z. f z * g z) real_differentiable (atreal z within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_MUL_WITHIN]);;

let REAL_DIFFERENTIABLE_DIV_WITHIN = prove
 (`!f g z s.
        f real_differentiable (atreal z within s) /\
        g real_differentiable (atreal z within s) /\
        ~(g z = &0)
        ==> (\z. f z / g z) real_differentiable (atreal z within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_DIV_WITHIN]);;

let REAL_DIFFERENTIABLE_POW_WITHIN = prove
 (`!f n z s.
        f real_differentiable (atreal z within s)
        ==> (\z. f z pow n) real_differentiable (atreal z within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_POW_WITHIN]);;

let REAL_DIFFERENTIABLE_TRANSFORM_WITHIN = prove
 (`!f g x s d.
        &0 < d /\
        x IN s /\
        (!x'. x' IN s /\ abs(x' - x) < d ==> f x' = g x') /\
        f real_differentiable (atreal x within s)
        ==> g real_differentiable (atreal x within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN]);;

let REAL_DIFFERENTIABLE_TRANSFORM = prove
 (`!f g s. (!x. x IN s ==> f x = g x) /\ f real_differentiable_on s
           ==> g real_differentiable_on s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[real_differentiable_on; GSYM real_differentiable] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`f:real->real`; `&1`] THEN
  ASM_SIMP_TAC[REAL_LT_01]);;

let REAL_DIFFERENTIABLE_EQ = prove
 (`!f g s. (!x. x IN s ==> f x = g x)
           ==> (f real_differentiable_on s <=> g real_differentiable_on s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_TRANSFORM]);;

let REAL_DIFFERENTIABLE_INV_ATREAL = prove
 (`!f z.
        f real_differentiable atreal z /\ ~(f z = &0)
        ==> (\z. inv(f z)) real_differentiable atreal z`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_INV_ATREAL]);;

let REAL_DIFFERENTIABLE_MUL_ATREAL = prove
 (`!f g z.
        f real_differentiable atreal z /\
        g real_differentiable atreal z
        ==> (\z. f z * g z) real_differentiable atreal z`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_MUL_ATREAL]);;

let REAL_DIFFERENTIABLE_DIV_ATREAL = prove
 (`!f g z.
        f real_differentiable atreal z /\
        g real_differentiable atreal z /\
        ~(g z = &0)
        ==> (\z. f z / g z) real_differentiable atreal z`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_DIV_ATREAL]);;

let REAL_DIFFERENTIABLE_POW_ATREAL = prove
 (`!f n z.
        f real_differentiable atreal z
        ==> (\z. f z pow n) real_differentiable atreal z`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_POW_ATREAL]);;

let REAL_DIFFERENTIABLE_TRANSFORM_ATREAL = prove
 (`!f g x d.
        &0 < d /\
        (!x'. abs(x' - x) < d ==> f x' = g x') /\
        f real_differentiable atreal x
        ==> g real_differentiable atreal x`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL]);;

let REAL_DIFFERENTIABLE_COMPOSE_WITHIN = prove
 (`!f g x s.
         f real_differentiable (atreal x within s) /\
         g real_differentiable (atreal (f x) within IMAGE f s)
         ==> (g o f) real_differentiable (atreal x within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[REAL_DIFF_CHAIN_WITHIN]);;

let REAL_DIFFERENTIABLE_COMPOSE_ATREAL = prove
 (`!f g x.
         f real_differentiable (atreal x) /\
         g real_differentiable (atreal (f x))
         ==> (g o f) real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[REAL_DIFF_CHAIN_ATREAL]);;
