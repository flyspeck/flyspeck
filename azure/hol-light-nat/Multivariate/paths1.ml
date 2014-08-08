(* ========================================================================= *)
(* Paths, connectedness, homotopy, simple connectedness & contractibility.   *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

open Hol_core
open Card
open Vectors
open Determinants
open Topology
open Convex

(* ------------------------------------------------------------------------- *)
(* Paths and arcs.                                                           *)
(* ------------------------------------------------------------------------- *)

let path = new_definition
 `!g:real^1->real^N. path g <=> g continuous_on interval[vec 0,vec 1]`;;

let pathstart = new_definition
 `pathstart (g:real^1->real^N) = g(vec 0)`;;

let pathfinish = new_definition
 `pathfinish (g:real^1->real^N) = g(vec 1)`;;

let path_image = new_definition
 `path_image (g:real^1->real^N) = IMAGE g (interval[vec 0,vec 1])`;;

let reversepath = new_definition
 `reversepath (g:real^1->real^N) = \x. g(vec 1 - x)`;;

let joinpaths = new_definition
 `(g1 ++ g2) = \x. if drop x <= &1 / &2 then g1(&2 % x)
                   else g2(&2 % x - vec 1)`;;

let simple_path = new_definition
 `simple_path (g:real^1->real^N) <=>
        path g /\
        !x y. x IN interval[vec 0,vec 1] /\
              y IN interval[vec 0,vec 1] /\
              g x = g y
              ==> x = y \/ x = vec 0 /\ y = vec 1 \/ x = vec 1 /\ y = vec 0`;;

let arc = new_definition
 `arc (g:real^1->real^N) <=>
        path g /\
        !x y. x IN interval [vec 0,vec 1] /\
              y IN interval [vec 0,vec 1] /\
              g x = g y
              ==> x = y`;;

(* ------------------------------------------------------------------------- *)
(* Invariance theorems.                                                      *)
(* ------------------------------------------------------------------------- *)

let PATH_EQ = prove
 (`!p q. (!t. t IN interval[vec 0,vec 1] ==> p t = q t) /\ path p
         ==> path q`,
  REWRITE_TAC[path; CONTINUOUS_ON_EQ]);;

let PATH_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N g.
     path g /\ f continuous_on path_image g ==> path(f o g)`,
  REWRITE_TAC[path; path_image; CONTINUOUS_ON_COMPOSE]);;

let PATH_TRANSLATION_EQ = prove
 (`!a g:real^1->real^N. path((\x. a + x) o g) <=> path g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path] THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `(g:real^1->real^N) = (\x. --a + x) o (\x. a + x) o g`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN VECTOR_ARITH_TAC; ALL_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]);;

add_translation_invariants [PATH_TRANSLATION_EQ];;

let PATH_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N g.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (path(f o g) <=> path g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^N->real^M` STRIP_ASSUME_TAC o
        MATCH_MP LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  REWRITE_TAC[path] THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `g:real^1->real^M = h o (f:real^M->real^N) o g`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[o_ASSOC; I_O_ID]; ALL_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON]);;

add_linear_invariants [PATH_LINEAR_IMAGE_EQ];;

let PATHSTART_TRANSLATION = prove
 (`!a g. pathstart((\x. a + x) o g) = a + pathstart g`,
  REWRITE_TAC[pathstart; o_THM]);;

add_translation_invariants [PATHSTART_TRANSLATION];;

let PATHSTART_LINEAR_IMAGE_EQ = prove
 (`!f g. linear f ==> pathstart(f o g) = f(pathstart g)`,
  REWRITE_TAC[pathstart; o_THM]);;

add_linear_invariants [PATHSTART_LINEAR_IMAGE_EQ];;

let PATHFINISH_TRANSLATION = prove
 (`!a g. pathfinish((\x. a + x) o g) = a + pathfinish g`,
  REWRITE_TAC[pathfinish; o_THM]);;

add_translation_invariants [PATHFINISH_TRANSLATION];;

let PATHFINISH_LINEAR_IMAGE = prove
 (`!f g. linear f ==> pathfinish(f o g) = f(pathfinish g)`,
  REWRITE_TAC[pathfinish; o_THM]);;

add_linear_invariants [PATHFINISH_LINEAR_IMAGE];;

let PATH_IMAGE_TRANSLATION = prove
 (`!a g. path_image((\x. a + x) o g) = IMAGE (\x. a + x) (path_image g)`,
  REWRITE_TAC[path_image; IMAGE_o]);;

add_translation_invariants [PATH_IMAGE_TRANSLATION];;

let PATH_IMAGE_LINEAR_IMAGE = prove
 (`!f g. linear f ==> path_image(f o g) = IMAGE f (path_image g)`,
  REWRITE_TAC[path_image; IMAGE_o]);;

add_linear_invariants [PATH_IMAGE_LINEAR_IMAGE];;

let REVERSEPATH_TRANSLATION = prove
 (`!a g. reversepath((\x. a + x) o g) = (\x. a + x) o reversepath g`,
  REWRITE_TAC[FUN_EQ_THM; reversepath; o_THM]);;

add_translation_invariants [REVERSEPATH_TRANSLATION];;

let REVERSEPATH_LINEAR_IMAGE = prove
 (`!f g. linear f ==> reversepath(f o g) = f o reversepath g`,
  REWRITE_TAC[FUN_EQ_THM; reversepath; o_THM]);;

add_linear_invariants [REVERSEPATH_LINEAR_IMAGE];;

let JOINPATHS_TRANSLATION = prove
 (`!a:real^N g1 g2. ((\x. a + x) o g1) ++ ((\x. a + x) o g2) =
                    (\x. a + x) o (g1 ++ g2)`,
  REWRITE_TAC[joinpaths; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[o_THM]);;

add_translation_invariants [JOINPATHS_TRANSLATION];;

let JOINPATHS_LINEAR_IMAGE = prove
 (`!f g1 g2. linear f ==> (f o g1) ++ (f o g2) = f o (g1 ++ g2)`,
  REWRITE_TAC[joinpaths; FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[o_THM]);;

add_linear_invariants [JOINPATHS_LINEAR_IMAGE];;

let SIMPLE_PATH_TRANSLATION_EQ = prove
 (`!a g:real^1->real^N. simple_path((\x. a + x) o g) <=> simple_path g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_path; PATH_TRANSLATION_EQ] THEN
  REWRITE_TAC[o_THM; VECTOR_ARITH `a + x:real^N = a + y <=> x = y`]);;

add_translation_invariants [SIMPLE_PATH_TRANSLATION_EQ];;

let SIMPLE_PATH_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N g.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (simple_path(f o g) <=> simple_path g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_path; PATH_TRANSLATION_EQ] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[PATH_LINEAR_IMAGE_EQ]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

add_linear_invariants [SIMPLE_PATH_LINEAR_IMAGE_EQ];;

let ARC_TRANSLATION_EQ = prove
 (`!a g:real^1->real^N. arc((\x. a + x) o g) <=> arc g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[arc; PATH_TRANSLATION_EQ] THEN
  REWRITE_TAC[o_THM; VECTOR_ARITH `a + x:real^N = a + y <=> x = y`]);;

add_translation_invariants [ARC_TRANSLATION_EQ];;

let ARC_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N g.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (arc(f o g) <=> arc g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arc; PATH_TRANSLATION_EQ] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[PATH_LINEAR_IMAGE_EQ]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

add_linear_invariants [ARC_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Basic lemmas about paths.                                                 *)
(* ------------------------------------------------------------------------- *)

let ARC_IMP_SIMPLE_PATH = prove
 (`!g. arc g ==> simple_path g`,
  REWRITE_TAC[arc; simple_path] THEN MESON_TAC[]);;

let ARC_IMP_PATH = prove
 (`!g. arc g ==> path g`,
  REWRITE_TAC[arc] THEN MESON_TAC[]);;

let SIMPLE_PATH_IMP_PATH = prove
 (`!g. simple_path g ==> path g`,
  REWRITE_TAC[simple_path] THEN MESON_TAC[]);;

let SIMPLE_PATH_CASES = prove
 (`!g:real^1->real^N. simple_path g ==> arc g \/ pathfinish g = pathstart g`,
  REWRITE_TAC[simple_path; arc; pathfinish; pathstart] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(g:real^1->real^N) (vec 0) = g(vec 1)` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^1`; `v:real^1`]) THEN
  ASM_MESON_TAC[]);;

let SIMPLE_PATH_IMP_ARC = prove
 (`!g:real^1->real^N.
        simple_path g /\ ~(pathfinish g = pathstart g) ==> arc g`,
  MESON_TAC[SIMPLE_PATH_CASES]);;

let ARC_DISTINCT_ENDS = prove
 (`!g:real^1->real^N. arc g ==> ~(pathfinish g = pathstart g)`,
  GEN_TAC THEN REWRITE_TAC[arc; pathfinish; pathstart] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a /\ b /\ ~d ==> ~c`] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[GSYM DROP_EQ; IN_INTERVAL_1; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let ARC_SIMPLE_PATH = prove
 (`!g:real^1->real^N.
        arc g <=> simple_path g /\ ~(pathfinish g = pathstart g)`,
  MESON_TAC[SIMPLE_PATH_CASES; ARC_IMP_SIMPLE_PATH; ARC_DISTINCT_ENDS]);;

let SIMPLE_PATH_EQ_ARC = prove
 (`!g. ~(pathstart g = pathfinish g) ==> (simple_path g <=> arc g)`,
  SIMP_TAC[ARC_SIMPLE_PATH]);;

let PATH_IMAGE_NONEMPTY = prove
 (`!g. ~(path_image g = {})`,
  REWRITE_TAC[path_image; IMAGE_EQ_EMPTY; INTERVAL_EQ_EMPTY] THEN
  SIMP_TAC[DIMINDEX_1; CONJ_ASSOC; LE_ANTISYM; UNWIND_THM1; VEC_COMPONENT;
           ARITH; REAL_OF_NUM_LT]);;

let PATHSTART_IN_PATH_IMAGE = prove
 (`!g. (pathstart g) IN path_image g`,
  GEN_TAC THEN REWRITE_TAC[pathstart; path_image] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS]);;

let PATHFINISH_IN_PATH_IMAGE = prove
 (`!g. (pathfinish g) IN path_image g`,
  GEN_TAC THEN REWRITE_TAC[pathfinish; path_image] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC);;

let CONNECTED_PATH_IMAGE = prove
 (`!g. path g ==> connected(path_image g)`,
  REWRITE_TAC[path; path_image] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERVAL]);;

let COMPACT_PATH_IMAGE = prove
 (`!g. path g ==> compact(path_image g)`,
  REWRITE_TAC[path; path_image] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL]);;

let BOUNDED_PATH_IMAGE = prove
 (`!g. path g ==> bounded(path_image g)`,
  MESON_TAC[COMPACT_PATH_IMAGE; COMPACT_IMP_BOUNDED]);;

let CLOSED_PATH_IMAGE = prove
 (`!g. path g ==> closed(path_image g)`,
  MESON_TAC[COMPACT_PATH_IMAGE; COMPACT_IMP_CLOSED]);;

let CONNECTED_SIMPLE_PATH_IMAGE = prove
 (`!g. simple_path g ==> connected(path_image g)`,
  MESON_TAC[CONNECTED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH]);;

let COMPACT_SIMPLE_PATH_IMAGE = prove
 (`!g. simple_path g ==> compact(path_image g)`,
  MESON_TAC[COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH]);;

let BOUNDED_SIMPLE_PATH_IMAGE = prove
 (`!g. simple_path g ==> bounded(path_image g)`,
  MESON_TAC[BOUNDED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH]);;

let CLOSED_SIMPLE_PATH_IMAGE = prove
 (`!g. simple_path g ==> closed(path_image g)`,
  MESON_TAC[CLOSED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH]);;

let CONNECTED_ARC_IMAGE = prove
 (`!g. arc g ==> connected(path_image g)`,
  MESON_TAC[CONNECTED_PATH_IMAGE; ARC_IMP_PATH]);;

let COMPACT_ARC_IMAGE = prove
 (`!g. arc g ==> compact(path_image g)`,
  MESON_TAC[COMPACT_PATH_IMAGE; ARC_IMP_PATH]);;

let BOUNDED_ARC_IMAGE = prove
 (`!g. arc g ==> bounded(path_image g)`,
  MESON_TAC[BOUNDED_PATH_IMAGE; ARC_IMP_PATH]);;

let CLOSED_ARC_IMAGE = prove
 (`!g. arc g ==> closed(path_image g)`,
  MESON_TAC[CLOSED_PATH_IMAGE; ARC_IMP_PATH]);;

let PATHSTART_COMPOSE = prove
 (`!f p. pathstart(f o p) = f(pathstart p)`,
  REWRITE_TAC[pathstart; o_THM]);;

let PATHFINISH_COMPOSE = prove
 (`!f p. pathfinish(f o p) = f(pathfinish p)`,
  REWRITE_TAC[pathfinish; o_THM]);;

let PATH_IMAGE_COMPOSE = prove
 (`!f p. path_image (f o p) = IMAGE f (path_image p)`,
  REWRITE_TAC[path_image; IMAGE_o]);;

let PATH_COMPOSE_JOIN = prove
 (`!f p q. f o (p ++ q) = (f o p) ++ (f o q)`,
  REWRITE_TAC[joinpaths; o_DEF; FUN_EQ_THM] THEN MESON_TAC[]);;

let PATH_COMPOSE_REVERSEPATH = prove
 (`!f p. f o reversepath p = reversepath(f o p)`,
  REWRITE_TAC[reversepath; o_DEF; FUN_EQ_THM] THEN MESON_TAC[]);;

let JOIN_PATHS_EQ = prove
 (`!p q:real^1->real^N.
   (!t. t IN interval[vec 0,vec 1] ==> p t = p' t) /\
   (!t. t IN interval[vec 0,vec 1] ==> q t = q' t)
   ==> !t. t IN interval[vec 0,vec 1] ==> (p ++ q) t = (p' ++ q') t`,
  REWRITE_TAC[joinpaths; IN_INTERVAL_1; DROP_VEC] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_SUB; DROP_VEC] THEN
  ASM_REAL_ARITH_TAC);;

let CARD_EQ_SIMPLE_PATH_IMAGE = prove
 (`!g. simple_path g ==> path_image g =_c (:real)`,
  SIMP_TAC[CONNECTED_CARD_EQ_IFF_NONTRIVIAL; CONNECTED_SIMPLE_PATH_IMAGE] THEN
  GEN_TAC THEN REWRITE_TAC[simple_path; path_image] THEN MATCH_MP_TAC(SET_RULE
   `(?u v. u IN s /\ v IN s /\ ~(u = a) /\ ~(v = a) /\ ~(u = v))
    ==> P /\ (!x y. x IN s /\ y IN s /\ f x = f y
                    ==> x = y \/ x = a /\ y = b \/ x = b /\ y = a)
        ==> ~(?c. IMAGE f s SUBSET {c})`) THEN
  MAP_EVERY EXISTS_TAC [`lift(&1 / &3)`; `lift(&1 / &2)`] THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; GSYM LIFT_NUM; LIFT_EQ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let INFINITE_SIMPLE_PATH_IMAGE = prove
 (`!g. simple_path g ==> INFINITE(path_image g)`,
  MESON_TAC[CARD_EQ_SIMPLE_PATH_IMAGE; INFINITE; FINITE_IMP_COUNTABLE;
            UNCOUNTABLE_REAL; CARD_COUNTABLE_CONG]);;

let CARD_EQ_ARC_IMAGE = prove
 (`!g. arc g ==> path_image g =_c (:real)`,
  MESON_TAC[ARC_IMP_SIMPLE_PATH; CARD_EQ_SIMPLE_PATH_IMAGE]);;

let INFINITE_ARC_IMAGE = prove
 (`!g. arc g ==> INFINITE(path_image g)`,
  MESON_TAC[ARC_IMP_SIMPLE_PATH; INFINITE_SIMPLE_PATH_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Simple paths with the endpoints removed.                                  *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_PATH_ENDLESS = prove
 (`!c:real^1->real^N.
        simple_path c
        ==> path_image c DIFF {pathstart c,pathfinish c} =
            IMAGE c (interval(vec 0,vec 1))`,
  REWRITE_TAC[simple_path; path_image; pathstart; pathfinish] THEN
  REWRITE_TAC[OPEN_CLOSED_INTERVAL_1; path] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x y. x IN s /\ y IN s /\ c x = c y
           ==> x = y \/ x = a /\ y = b \/ x = b /\ y = a) /\
    a IN s /\ b IN s
    ==>  IMAGE c s DIFF {c a,c b} = IMAGE c (s DIFF {a,b})`) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL]);;

let CONNECTED_SIMPLE_PATH_ENDLESS = prove
 (`!c:real^1->real^N.
        simple_path c
        ==> connected(path_image c DIFF {pathstart c,pathfinish c})`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIMPLE_PATH_ENDLESS] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  SIMP_TAC[CONVEX_INTERVAL; CONVEX_CONNECTED] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[simple_path; path]) THEN
  ASM_REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED]);;

let NONEMPTY_SIMPLE_PATH_ENDLESS = prove
 (`!c:real^1->real^N.
      simple_path c ==> ~(path_image c DIFF {pathstart c,pathfinish c} = {})`,
  SIMP_TAC[SIMPLE_PATH_ENDLESS; IMAGE_EQ_EMPTY; INTERVAL_EQ_EMPTY_1] THEN
  REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The operations on paths.                                                  *)
(* ------------------------------------------------------------------------- *)

let JOINPATHS = prove
 (`!g1 g2. pathfinish g1 = pathstart g2
           ==> g1 ++ g2 = \x. if drop x < &1 / &2 then g1(&2 % x)
                              else g2 (&2 % x - vec 1)`,
  REWRITE_TAC[pathstart; pathfinish] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[joinpaths; FUN_EQ_THM] THEN
  X_GEN_TAC `x:real^1` THEN ASM_CASES_TAC `drop x = &1 / &2` THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `lift`) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_REFL; GSYM LIFT_CMUL; REAL_LT_REFL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[LIFT_NUM; VECTOR_SUB_REFL];
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC]);;

let REVERSEPATH_REVERSEPATH = prove
 (`!g:real^1->real^N. reversepath(reversepath g) = g`,
  REWRITE_TAC[reversepath; ETA_AX;
              VECTOR_ARITH `vec 1 - (vec 1 - x):real^1 = x`]);;

let PATHSTART_REVERSEPATH = prove
 (`pathstart(reversepath g) = pathfinish g`,
  REWRITE_TAC[pathstart; reversepath; pathfinish; VECTOR_SUB_RZERO]);;

let PATHFINISH_REVERSEPATH = prove
 (`pathfinish(reversepath g) = pathstart g`,
  REWRITE_TAC[pathstart; reversepath; pathfinish; VECTOR_SUB_REFL]);;

let PATHSTART_JOIN = prove
 (`!g1 g2. pathstart(g1 ++ g2) = pathstart g1`,
  REWRITE_TAC[joinpaths; pathstart; pathstart; DROP_VEC; VECTOR_MUL_RZERO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let PATHFINISH_JOIN = prove
 (`!g1 g2. pathfinish(g1 ++ g2) = pathfinish g2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[joinpaths; pathfinish; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

let PATH_IMAGE_REVERSEPATH = prove
 (`!g:real^1->real^N. path_image(reversepath g) = path_image g`,
  SUBGOAL_THEN `!g:real^1->real^N.
      path_image(reversepath g) SUBSET path_image g`
   (fun th -> MESON_TAC[th; REVERSEPATH_REVERSEPATH; SUBSET_ANTISYM]) THEN
  REWRITE_TAC[SUBSET; path_image; FORALL_IN_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->real^N`; `x:real^1`] THEN
  DISCH_TAC THEN REWRITE_TAC[reversepath; IN_IMAGE] THEN
  EXISTS_TAC `vec 1 - x:real^1` THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC);;

let PATH_REVERSEPATH = prove
 (`!g:real^1->real^N. path(reversepath g) <=> path g`,
  SUBGOAL_THEN `!g:real^1->real^N. path g ==> path(reversepath g)`
   (fun th -> MESON_TAC[th; REVERSEPATH_REVERSEPATH]) THEN
  GEN_TAC THEN REWRITE_TAC[path; reversepath] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
  REWRITE_TAC[DROP_VEC; DROP_SUB] THEN REAL_ARITH_TAC);;

let PATH_JOIN = prove
 (`!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2
        ==> (path(g1 ++ g2) <=> path g1 /\ path g2)`,
  REWRITE_TAC[path; pathfinish; pathstart] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(g1:real^1->real^N) = (\x. g1 (&2 % x)) o (\x. &1 / &2 % x)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
        VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID] THEN
      MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `(g1 ++ g2):real^1->real^N` THEN CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE; joinpaths; IN_INTERVAL_1; DROP_CMUL] THEN
        SIMP_TAC[DROP_VEC; REAL_ARITH `&1 / &2 * x <= &1 / &2 <=> x <= &1`];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_CMUL] THEN
      REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN
       `(g2:real^1->real^N) =
        (\x. g2 (&2 % x - vec 1)) o (\x. &1 / &2 % (x + vec 1))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
        VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST;
               CONTINUOUS_ON_ADD] THEN
      MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `(g1 ++ g2):real^1->real^N` THEN CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE; joinpaths; IN_INTERVAL_1; DROP_CMUL] THEN
        REWRITE_TAC[DROP_VEC; DROP_ADD; REAL_ARITH
         `&1 / &2 * (x + &1) <= &1 / &2 <=> x <= &0`] THEN
        SIMP_TAC[REAL_ARITH `&0 <= x ==> (x <= &0 <=> x = &0)`; LIFT_NUM;
          VECTOR_MUL_ASSOC; GSYM LIFT_EQ; LIFT_DROP; GSYM LIFT_CMUL] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_REWRITE_TAC[VECTOR_ADD_LID; VECTOR_MUL_LID] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[VECTOR_ARITH `(x + vec 1) - vec 1 = x`];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_CMUL] THEN
      REWRITE_TAC[DROP_VEC; DROP_ADD] THEN REAL_ARITH_TAC];
    STRIP_TAC THEN
    SUBGOAL_THEN `interval[vec 0,vec 1] =
                  interval[vec 0,lift(&1 / &2)] UNION
                  interval[lift(&1 / &2),vec 1]`
    SUBST1_TAC THENL
     [SIMP_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_UNION THEN REWRITE_TAC[CLOSED_INTERVAL] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
     [EXISTS_TAC `\x. (g1:real^1->real^N) (&2 % x)`;
      EXISTS_TAC `\x. (g2:real^1->real^N) (&2 % x - vec 1)`] THEN
    REWRITE_TAC[joinpaths] THEN SIMP_TAC[IN_INTERVAL_1; LIFT_DROP] THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID] THEN
      ONCE_REWRITE_TAC[VECTOR_ARITH `&2 % (x:real^1) = &2 % x + vec 0`] THEN
      REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
      REWRITE_TAC[REAL_POS; INTERVAL_EQ_EMPTY_1; LIFT_DROP; DROP_VEC] THEN
      REWRITE_TAC[GSYM LIFT_CMUL; VECTOR_ADD_RID; VECTOR_MUL_RZERO] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[LIFT_NUM];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SIMP_TAC[REAL_ARITH `&1 / &2 <= x ==> (x <= &1 / &2 <=> x = &1 / &2)`;
               GSYM LIFT_EQ; LIFT_DROP; GSYM LIFT_CMUL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
      ASM_REWRITE_TAC[LIFT_NUM] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM LIFT_CMUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[LIFT_NUM; VECTOR_SUB_REFL];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
             CONTINUOUS_ON_ID] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `&2 % x - vec 1 = &2 % x + --vec 1`] THEN
    REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
    REWRITE_TAC[REAL_POS; INTERVAL_EQ_EMPTY_1; LIFT_DROP; DROP_VEC] THEN
    REWRITE_TAC[GSYM LIFT_CMUL; VECTOR_ADD_RID; VECTOR_MUL_RZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[LIFT_NUM] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `&2 % x + --x = x /\ x + --x = vec 0`]]);;

let PATH_JOIN_IMP = prove
 (`!g1 g2:real^1->real^N.
        path g1 /\ path g2 /\ pathfinish g1 = pathstart g2
        ==> path(g1 ++ g2)`,
  MESON_TAC[PATH_JOIN]);;

let PATH_IMAGE_JOIN_SUBSET = prove
 (`!g1 g2:real^1->real^N.
        path_image(g1 ++ g2) SUBSET (path_image g1 UNION path_image g2)`,
  REWRITE_TAC[path_image; FORALL_IN_IMAGE; SUBSET] THEN
  GEN_TAC THEN GEN_TAC THEN X_GEN_TAC `x:real^1` THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_UNION; IN_IMAGE; DROP_VEC; joinpaths] THEN
  STRIP_TAC THEN ASM_CASES_TAC `drop x <= &1 / &2` THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN EXISTS_TAC `&2 % x:real^1` THEN REWRITE_TAC[DROP_CMUL];
    DISJ2_TAC THEN EXISTS_TAC `&2 % x - vec 1:real^1` THEN
    REWRITE_TAC[DROP_CMUL; DROP_SUB; DROP_VEC]] THEN
  ASM_REAL_ARITH_TAC);;

let SUBSET_PATH_IMAGE_JOIN = prove
 (`!g1 g2:real^1->real^N s.
        path_image g1 SUBSET s /\ path_image g2 SUBSET s
        ==> path_image(g1 ++ g2) SUBSET s`,
  MP_TAC PATH_IMAGE_JOIN_SUBSET THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  SET_TAC[]);;

let PATH_IMAGE_JOIN = prove
 (`!g1 g2. pathfinish g1 = pathstart g2
           ==> path_image(g1 ++ g2) = path_image g1 UNION path_image g2`,
  REWRITE_TAC[pathfinish; pathstart] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[PATH_IMAGE_JOIN_SUBSET] THEN
  REWRITE_TAC[path_image; SUBSET; FORALL_AND_THM; IN_UNION; TAUT
                `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; joinpaths] THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_IMAGE; DROP_VEC] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^1` THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `(&1 / &2) % x:real^1` THEN
    ASM_REWRITE_TAC[DROP_CMUL; REAL_ARITH
     `&1 / &2 * x <= &1 / &2 <=> x <= &1`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID];
    EXISTS_TAC `(&1 / &2) % (x + vec 1):real^1` THEN
    ASM_REWRITE_TAC[DROP_CMUL; DROP_ADD; DROP_VEC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID; VECTOR_ARITH `(x + vec 1) - vec 1 = x`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> (&1 / &2 * (x + &1) <= &1 / &2 <=>
                                          x = &0)`] THEN
    REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP; LIFT_NUM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_LID; DROP_VEC]] THEN
  ASM_REAL_ARITH_TAC);;

let NOT_IN_PATH_IMAGE_JOIN = prove
 (`!g1 g2 x. ~(x IN path_image g1) /\ ~(x IN path_image g2)
             ==> ~(x IN path_image(g1 ++ g2))`,
  MESON_TAC[PATH_IMAGE_JOIN_SUBSET; SUBSET; IN_UNION]);;

let ARC_REVERSEPATH = prove
 (`!g. arc g ==> arc(reversepath g)`,
  GEN_TAC THEN SIMP_TAC[arc; PATH_REVERSEPATH] THEN
  REWRITE_TAC[arc; reversepath] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vec 1 - x:real^1`; `vec 1 - y:real^1`]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_SUB; DROP_VEC] THEN
  REAL_ARITH_TAC);;

let SIMPLE_PATH_REVERSEPATH = prove
 (`!g. simple_path g ==> simple_path (reversepath g)`,
  GEN_TAC THEN SIMP_TAC[simple_path; PATH_REVERSEPATH] THEN
  REWRITE_TAC[simple_path; reversepath] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vec 1 - x:real^1`; `vec 1 - y:real^1`]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_SUB; DROP_VEC] THEN
  REAL_ARITH_TAC);;

let SIMPLE_PATH_JOIN_LOOP = prove
 (`!g1 g2:real^1->real^N.
        arc g1 /\ arc g2 /\
        pathfinish g1 = pathstart g2 /\
        pathfinish g2 = pathstart g1 /\
        (path_image g1 INTER path_image g2) SUBSET
            {pathstart g1,pathstart g2}
        ==> simple_path(g1 ++ g2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[arc; simple_path] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c /\ d ==> f) /\
    (a' /\ b' /\ c /\ d /\ e ==> g)
    ==> (a /\ a') /\ (b /\ b') /\ c /\ d /\ e ==> f /\ g`) THEN
  CONJ_TAC THENL [MESON_TAC[PATH_JOIN]; ALL_TAC] THEN
  REWRITE_TAC[arc; simple_path; SUBSET; IN_INTER; pathstart;
    pathfinish; IN_INTERVAL_1; DROP_VEC; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G2") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G0")) THEN
  MATCH_MP_TAC DROP_WLOG_LE THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[joinpaths] THEN
  MAP_EVERY ASM_CASES_TAC [`drop x <= &1 / &2`; `drop y <= &1 / &2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [REMOVE_THEN "G1" (MP_TAC o SPECL [`&2 % x:real^1`; `&2 % y:real^1`]) THEN
    ASM_REWRITE_TAC[DROP_CMUL; DROP_VEC; DROP_SUB] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th) THEN VECTOR_ARITH_TAC;
    ALL_TAC;
    ASM_REAL_ARITH_TAC;
    REMOVE_THEN "G2" (MP_TAC o SPECL
     [`&2 % x:real^1 - vec 1`; `&2 % y:real^1 - vec 1`]) THEN
    ASM_REWRITE_TAC[DROP_CMUL; DROP_VEC; DROP_SUB] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th) THEN VECTOR_ARITH_TAC] THEN
  REMOVE_THEN "G0" (MP_TAC o SPEC `(g1:real^1->real^N) (&2 % x)`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[path_image; IN_IMAGE] THEN EXISTS_TAC `&2 % x:real^1` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[path_image; IN_IMAGE] THEN
      EXISTS_TAC `&2 % y:real^1 - vec 1` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ2_TAC THEN DISJ1_TAC;
    DISJ1_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `&1 / &2 % vec 1:real^1`] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&2 % x:real^1 = vec 0` MP_TAC THENL
     [ALL_TAC; VECTOR_ARITH_TAC] THEN
    REMOVE_THEN "G1" MATCH_MP_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_MUL_RZERO]) THEN
    UNDISCH_TAC `T` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 % y:real^1 - vec 1 = vec 1` MP_TAC THENL
     [ALL_TAC; VECTOR_ARITH_TAC] THEN
    REMOVE_THEN "G2" MATCH_MP_TAC;
    SUBGOAL_THEN `&2 % x:real^1 = vec 1` MP_TAC THENL
     [ALL_TAC; VECTOR_ARITH_TAC] THEN
    REMOVE_THEN "G1" MATCH_MP_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `&2 % y:real^1 - vec 1 = vec 0` MP_TAC THENL
     [ALL_TAC; VECTOR_ARITH_TAC] THEN
    REMOVE_THEN "G2" MATCH_MP_TAC] THEN
  (REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
    [ALL_TAC; ASM_MESON_TAC[]] THEN
   ASM_REWRITE_TAC[DROP_CMUL; DROP_SUB; DROP_VEC] THEN
   ASM_REAL_ARITH_TAC));;

let ARC_JOIN = prove
 (`!g1 g2:real^1->real^N.
        arc g1 /\ arc g2 /\
        pathfinish g1 = pathstart g2 /\
        (path_image g1 INTER path_image g2) SUBSET {pathstart g2}
        ==> arc(g1 ++ g2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[arc; simple_path] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c /\ d ==> f) /\
    (a' /\ b' /\ c /\ d ==> g)
    ==> (a /\ a') /\ (b /\ b') /\ c /\ d ==> f /\ g`) THEN
  CONJ_TAC THENL [MESON_TAC[PATH_JOIN]; ALL_TAC] THEN
  REWRITE_TAC[arc; simple_path; SUBSET; IN_INTER; pathstart;
    pathfinish; IN_INTERVAL_1; DROP_VEC; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G2") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G0")) THEN
  MATCH_MP_TAC DROP_WLOG_LE THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[joinpaths] THEN
  MAP_EVERY ASM_CASES_TAC [`drop x <= &1 / &2`; `drop y <= &1 / &2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [REMOVE_THEN "G1" (MP_TAC o SPECL [`&2 % x:real^1`; `&2 % y:real^1`]) THEN
    ASM_REWRITE_TAC[DROP_CMUL; DROP_VEC; DROP_SUB] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC;
    ASM_REAL_ARITH_TAC;
    REMOVE_THEN "G2" (MP_TAC o SPECL
     [`&2 % x:real^1 - vec 1`; `&2 % y:real^1 - vec 1`]) THEN
    ASM_REWRITE_TAC[DROP_CMUL; DROP_VEC; DROP_SUB] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    VECTOR_ARITH_TAC] THEN
  REMOVE_THEN "G0" (MP_TAC o SPEC `(g1:real^1->real^N) (&2 % x)`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[path_image; IN_IMAGE] THEN EXISTS_TAC `&2 % x:real^1` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[path_image; IN_IMAGE] THEN
      EXISTS_TAC `&2 % y:real^1 - vec 1` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `x:real^1 = &1 / &2 % vec 1` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `&2 % x:real^1 = vec 1` MP_TAC THENL
     [ALL_TAC; VECTOR_ARITH_TAC] THEN
    REMOVE_THEN "G1" MATCH_MP_TAC;
    SUBGOAL_THEN `&2 % y:real^1 - vec 1 = vec 0` MP_TAC THENL
     [ALL_TAC; VECTOR_ARITH_TAC] THEN
    REMOVE_THEN "G2" MATCH_MP_TAC] THEN
  (REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
    [ALL_TAC; ASM_MESON_TAC[]] THEN
   ASM_REWRITE_TAC[DROP_CMUL; DROP_SUB; DROP_VEC] THEN
   ASM_REAL_ARITH_TAC));;

let REVERSEPATH_JOINPATHS = prove
 (`!g1 g2. pathfinish g1 = pathstart g2
           ==> reversepath(g1 ++ g2) = reversepath g2 ++ reversepath g1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[reversepath; joinpaths; pathfinish; pathstart; FUN_EQ_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real^1` THEN
  REWRITE_TAC[DROP_VEC; DROP_SUB; REAL_ARITH
   `&1 - x <= &1 / &2 <=> &1 / &2 <= x`] THEN
  ASM_CASES_TAC `t = lift(&1 / &2)` THENL
   [ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_REFL; GSYM LIFT_NUM; GSYM LIFT_SUB;
                    GSYM LIFT_CMUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[LIFT_NUM];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM DROP_EQ]) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH
     `~(x = &1 / &2) ==> (&1 / &2 <= x <=> ~(x <= &1 / &2))`] THEN
    ASM_CASES_TAC `drop t <= &1 / &2` THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Some reversed and "if and only if" versions of joining theorems.          *)
(* ------------------------------------------------------------------------- *)

let PATH_JOIN_PATH_ENDS = prove
 (`!g1 g2:real^1->real^N.
        path g2 /\ path(g1 ++ g2) ==> pathfinish g1 = pathstart g2`,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(NORM_ARITH
   `pathfinish g1:real^N = pathstart g2 \/
    &0 < dist(pathfinish g1,pathstart g2)`) THEN
  ASM_REWRITE_TAC[path; continuous_on; joinpaths] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  REWRITE_TAC[pathstart; pathfinish] THEN
  ABBREV_TAC `e = dist((g1:real^1->real^N)(vec 1),g2(vec 0:real^1))` THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o SPEC `vec 0:real^1`) (MP_TAC o SPEC `lift(&1 / &2)`)) THEN
  REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; LIFT_DROP; REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM LIFT_CMUL; IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1"))) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2"))) THEN
  REMOVE_THEN "2" (MP_TAC o SPEC `lift(min (&1 / &2) (min d1 d2) / &2)`) THEN
  REWRITE_TAC[LIFT_DROP; DIST_LIFT; DIST_0; NORM_REAL; GSYM drop] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "1" (MP_TAC o SPEC
   `lift(&1 / &2 + min (&1 / &2) (min d1 d2) / &4)`) THEN
  REWRITE_TAC[LIFT_DROP; DIST_LIFT] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_CMUL; LIFT_ADD; REAL_ADD_LDISTRIB] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM] THEN
  REWRITE_TAC[VECTOR_ADD_SUB; REAL_ARITH `&2 * x / &4 = x / &2`] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC);;

let PATH_JOIN_EQ = prove
 (`!g1 g2:real^1->real^N.
        path g1 /\ path g2
        ==> (path(g1 ++ g2) <=> pathfinish g1 = pathstart g2)`,
  MESON_TAC[PATH_JOIN_PATH_ENDS; PATH_JOIN_IMP]);;

let SIMPLE_PATH_JOIN_IMP = prove
 (`!g1 g2:real^1->real^N.
        simple_path(g1 ++ g2) /\ pathfinish g1 = pathstart g2
        ==> arc g1 /\ arc g2 /\
            path_image g1 INTER path_image g2 SUBSET
            {pathstart g1, pathstart g2}`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `path(g1:real^1->real^N) /\ path(g2:real^1->real^N)` THENL
   [ALL_TAC; ASM_MESON_TAC[PATH_JOIN; SIMPLE_PATH_IMP_PATH]] THEN
  REWRITE_TAC[simple_path; pathstart; pathfinish; arc] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THENL
   [MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`&1 / &2 % x:real^1`; `&1 / &2 % y:real^1`]) THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; joinpaths; DROP_CMUL] THEN
    REPEAT(COND_CASES_TAC THEN TRY ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; VECTOR_MUL_LID; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`&1 / &2 % (x + vec 1):real^1`; `&1 / &2 % (y + vec 1):real^1`]) THEN
    ASM_SIMP_TAC[JOINPATHS; pathstart; pathfinish] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_ADD; DROP_CMUL] THEN
    REPEAT(COND_CASES_TAC THEN TRY ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_ARITH `(a + b) - b:real^N = a`] THEN
    ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; VECTOR_MUL_LID; DROP_VEC;
                    DROP_ADD] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SET_RULE
     `s INTER t SUBSET u <=> !x. x IN s ==> x IN t ==> x IN u`] THEN
    REWRITE_TAC[path_image; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `y:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    SUBST1_TAC(SYM(ASSUME
     `(g1:real^1->real^N)(vec 1) = g2(vec 0:real^1)`)) THEN
    MATCH_MP_TAC(SET_RULE `x = a \/ x = b ==> f x IN {f a,f b}`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`&1 / &2 % x:real^1`; `&1 / &2 % (y + vec 1):real^1`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_ADD] THEN
      REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [joinpaths] THEN
      ASM_SIMP_TAC[JOINPATHS; pathstart; pathfinish] THEN
      REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_VEC] THEN
      REPEAT(COND_CASES_TAC THEN TRY ASM_REAL_ARITH_TAC) THEN
      REWRITE_TAC[VECTOR_ARITH `&2 % &1 / &2 % x:real^N = x`] THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(a + b) - b:real^N = a`];
      REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_ADD; DROP_VEC] THEN
      ASM_REAL_ARITH_TAC]]);;

let SIMPLE_PATH_JOIN_LOOP_EQ = prove
 (`!g1 g2:real^1->real^N.
        pathfinish g2 = pathstart g1 /\
        pathfinish g1 = pathstart g2
        ==> (simple_path(g1 ++ g2) <=>
             arc g1 /\ arc g2 /\
             path_image g1 INTER path_image g2 SUBSET
             {pathstart g1, pathstart g2})`,
  MESON_TAC[SIMPLE_PATH_JOIN_IMP; SIMPLE_PATH_JOIN_LOOP]);;

let ARC_JOIN_EQ = prove
 (`!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2
        ==> (arc(g1 ++ g2) <=>
             arc g1 /\ arc g2 /\
             path_image g1 INTER path_image g2 SUBSET {pathstart g2})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[ARC_JOIN] THEN
  GEN_REWRITE_TAC LAND_CONV [ARC_SIMPLE_PATH] THEN
  REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_JOIN] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g1:real^1->real^N`; `g2:real^1->real^N`]
        SIMPLE_PATH_JOIN_IMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((pathstart g1:real^N) IN path_image g2)`
   (fun th -> MP_TAC th THEN ASM SET_TAC[]) THEN
  REWRITE_TAC[path_image; IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_path]) THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^1`; `lift(&1 / &2) + inv(&2) % u`] o
    CONJUNCT2) THEN
  REWRITE_TAC[GSYM DROP_EQ; IN_INTERVAL_1; DROP_ADD; DROP_VEC;
              DROP_CMUL; LIFT_DROP; joinpaths] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_IMP_NZ;
               REAL_ARITH `&0 <= x ==> &0 < &1 / &2 + &1 / &2 * x`] THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 + &1 / &2 * u = &1 <=> u = &1`] THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 <= u ==> (&1 / &2 + &1 / &2 * u <= &1 / &2 <=> u = &0)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  ASM_SIMP_TAC[REAL_ARITH `u <= &1 ==> &1 / &2 + &1 / &2 * u <= &1`] THEN
  REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM; LIFT_DROP] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; GSYM LIFT_CMUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM] THEN
    ASM_REWRITE_TAC[VEC_EQ] THEN ARITH_TAC;
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; GSYM LIFT_CMUL] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[LIFT_NUM; VECTOR_MUL_LID; VECTOR_ADD_SUB] THEN
    ASM_MESON_TAC[]]);;

let ARC_JOIN_EQ_ALT = prove
 (`!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2
        ==> (arc(g1 ++ g2) <=>
             arc g1 /\ arc g2 /\
             path_image g1 INTER path_image g2 = {pathstart g2})`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARC_JOIN_EQ] THEN
  MP_TAC(ISPEC `g1:real^1->real^N` PATHFINISH_IN_PATH_IMAGE) THEN
  MP_TAC(ISPEC `g2:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reassociating a joined path doesn't matter for various properties.        *)
(* ------------------------------------------------------------------------- *)

let PATH_ASSOC = prove
 (`!p q r:real^1->real^N.
        pathfinish p = pathstart q /\ pathfinish q = pathstart r
        ==> (path(p ++ (q ++ r)) <=> path((p ++ q) ++ r))`,
  SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN] THEN CONV_TAC TAUT);;

let SIMPLE_PATH_ASSOC = prove
 (`!p q r:real^1->real^N.
        pathfinish p = pathstart q /\ pathfinish q = pathstart r
        ==> (simple_path(p ++ (q ++ r)) <=> simple_path((p ++ q) ++ r))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `pathstart(p:real^1->real^N) = pathfinish r` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SIMPLE_PATH_EQ_ARC; PATHSTART_JOIN; PATHFINISH_JOIN]] THEN
  ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_JOIN; PATHFINISH_JOIN;
               ARC_JOIN_EQ; PATH_IMAGE_JOIN] THEN
  MAP_EVERY ASM_CASES_TAC
   [`arc(p:real^1->real^N)`; `arc(q:real^1->real^N)`;
    `arc(r:real^1->real^N)`] THEN
  ASM_REWRITE_TAC[UNION_OVER_INTER; UNION_SUBSET;
                  ONCE_REWRITE_RULE[INTER_COMM] UNION_OVER_INTER] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS)) THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t PATHSTART_IN_PATH_IMAGE) THEN
                      MP_TAC(ISPEC t PATHFINISH_IN_PATH_IMAGE))
   [`p:real^1->real^N`; `q:real^1->real^N`; `r:real^1->real^N`] THEN
  ASM SET_TAC[]);;

let ARC_ASSOC = prove
 (`!p q r:real^1->real^N.
        pathfinish p = pathstart q /\ pathfinish q = pathstart r
        ==> (arc(p ++ (q ++ r)) <=> arc((p ++ q) ++ r))`,
  SIMP_TAC[ARC_SIMPLE_PATH; SIMPLE_PATH_ASSOC] THEN
  SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN]);;

(* ------------------------------------------------------------------------- *)
(* In the case of a loop, neither does symmetry.                             *)
(* ------------------------------------------------------------------------- *)

let PATH_SYM = prove
 (`!p q. pathfinish p = pathstart q /\ pathfinish q = pathstart p
         ==> (path(p ++ q) <=> path(q ++ p))`,
  SIMP_TAC[PATH_JOIN; CONJ_ACI]);;

let SIMPLE_PATH_SYM = prove
 (`!p q. pathfinish p = pathstart q /\ pathfinish q = pathstart p
         ==> (simple_path(p ++ q) <=> simple_path(q ++ p))`,
  SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; INTER_ACI; CONJ_ACI; INSERT_AC]);;

let PATH_IMAGE_SYM = prove
 (`!p q. pathfinish p = pathstart q /\ pathfinish q = pathstart p
         ==> path_image(p ++ q) = path_image(q ++ p)`,
  SIMP_TAC[PATH_IMAGE_JOIN; UNION_ACI]);;

(* ------------------------------------------------------------------------- *)
(* Reparametrizing a closed curve to start at some chosen point.             *)
(* ------------------------------------------------------------------------- *)

let shiftpath = new_definition
  `shiftpath a (f:real^1->real^N) =
        \x. if drop(a + x) <= &1 then f(a + x)
            else f(a + x - vec 1)`;;

let SHIFTPATH_TRANSLATION = prove
 (`!a t g. shiftpath t ((\x. a + x) o g) = (\x. a + x) o shiftpath t g`,
  REWRITE_TAC[FUN_EQ_THM; shiftpath; o_THM] THEN MESON_TAC[]);;

add_translation_invariants [SHIFTPATH_TRANSLATION];;

let SHIFTPATH_LINEAR_IMAGE = prove
 (`!f t g. linear f ==> shiftpath t (f o g) = f o shiftpath t g`,
  REWRITE_TAC[FUN_EQ_THM; shiftpath; o_THM] THEN MESON_TAC[]);;

add_linear_invariants [SHIFTPATH_LINEAR_IMAGE];;

let PATHSTART_SHIFTPATH = prove
 (`!a g. drop a <= &1 ==> pathstart(shiftpath a g) = g(a)`,
  SIMP_TAC[pathstart; shiftpath; VECTOR_ADD_RID]);;

let PATHFINISH_SHIFTPATH = prove
 (`!a g. &0 <= drop a /\ pathfinish g = pathstart g
         ==> pathfinish(shiftpath a g) = g(a)`,
  SIMP_TAC[pathfinish; shiftpath; pathstart; DROP_ADD; DROP_VEC] THEN
  REWRITE_TAC[VECTOR_ARITH `a + vec 1 - vec 1 = a`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> (x + &1 <= &1 <=> x = &0)`] THEN
  SIMP_TAC[DROP_EQ_0; VECTOR_ADD_LID] THEN MESON_TAC[]);;

let ENDPOINTS_SHIFTPATH = prove
 (`!a g. pathfinish g = pathstart g /\ a IN interval[vec 0,vec 1]
         ==> pathfinish(shiftpath a g) = g a /\
             pathstart(shiftpath a g) = g a`,
  SIMP_TAC[IN_INTERVAL_1; DROP_VEC;
           PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH]);;

let CLOSED_SHIFTPATH = prove
 (`!a g. pathfinish g = pathstart g /\ a IN interval[vec 0,vec 1]
         ==> pathfinish(shiftpath a g) = pathstart(shiftpath a g)`,
  SIMP_TAC[IN_INTERVAL_1; PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH;
           DROP_VEC]);;

let PATH_SHIFTPATH = prove
 (`!g a. path g /\ pathfinish g:real^N = pathstart g /\
         a IN interval[vec 0,vec 1]
         ==> path(shiftpath a g)`,
  REWRITE_TAC[shiftpath; path] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `interval[vec 0,vec 1] = interval[vec 0,vec 1 - a:real^1] UNION
                            interval[vec 1 - a,vec 1]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
    REWRITE_TAC[DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_UNION THEN REWRITE_TAC[CLOSED_INTERVAL] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
   [EXISTS_TAC `(\x. g(a + x)):real^1->real^N` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_VEC; DROP_SUB] THEN
    SIMP_TAC[REAL_ARITH `a + x <= &1 <=> x <= &1 - a`];
    EXISTS_TAC `(\x. g(a + x - vec 1)):real^1->real^N` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_VEC; DROP_SUB] THEN
    SIMP_TAC[REAL_ARITH `&1 - a <= x ==> (a + x <= &1 <=> a + x = &1)`] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    REWRITE_TAC[VECTOR_ARITH `a + x - vec 1 = (a + x) - vec 1`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_SIMP_TAC[GSYM LIFT_EQ; LIFT_ADD; LIFT_NUM; LIFT_DROP] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; COND_ID]] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
  SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID;
           CONTINUOUS_ON_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC; DROP_ADD] THEN
  REAL_ARITH_TAC);;

let SHIFTPATH_SHIFTPATH = prove
 (`!g a x. a IN interval[vec 0,vec 1] /\ pathfinish g = pathstart g /\
           x IN interval[vec 0,vec 1]
           ==> shiftpath (vec 1 - a) (shiftpath a g) x = g x`,
  REWRITE_TAC[shiftpath; pathfinish; pathstart] THEN
  REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_VEC] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
  REWRITE_TAC[DROP_VEC] THEN REPEAT STRIP_TAC THENL
   [ALL_TAC;
    AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `x:real^1 = vec 0` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[VECTOR_ARITH `a + vec 1 - a + vec 0:real^1 = vec 1`]]);;

let PATH_IMAGE_SHIFTPATH = prove
 (`!a g:real^1->real^N.
        a IN interval[vec 0,vec 1] /\ pathfinish g = pathstart g
        ==> path_image(shiftpath a g) = path_image g`,
  REWRITE_TAC[IN_INTERVAL_1; pathfinish; pathstart] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  REWRITE_TAC[path_image; shiftpath; FORALL_IN_IMAGE; SUBSET] THEN
  REWRITE_TAC[IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_IMAGE] THENL
   [EXISTS_TAC `a + x:real^1`;
    EXISTS_TAC `a + x - vec 1:real^1`;
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_SUB; DROP_ADD] THEN
  TRY REAL_ARITH_TAC THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `drop a <= drop x` THENL
   [EXISTS_TAC `x - a:real^1` THEN
    REWRITE_TAC[VECTOR_ARITH `a + x - a:real^1 = x`; DROP_SUB] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `vec 1 + x - a:real^1` THEN
    REWRITE_TAC[VECTOR_ARITH `a + (v + x - a) - v:real^1 = x`] THEN
    REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_VEC] THEN
    ASM_CASES_TAC `x:real^1 = vec 0` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `a + v + x - a:real^1 = v + x`] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_RID; DROP_VEC; COND_ID] THEN
    ASM_REWRITE_TAC[REAL_ARITH `a + &1 + x - a <= &1 <=> x <= &0`] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN
    TRY(COND_CASES_TAC THEN POP_ASSUM MP_TAC) THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let SIMPLE_PATH_SHIFTPATH = prove
 (`!g a. simple_path g /\ pathfinish g = pathstart g /\
         a IN interval[vec 0,vec 1]
         ==> simple_path(shiftpath a g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_path] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ c /\ d ==> e) /\ (b /\ c /\ d ==> f)
    ==>  (a /\ b) /\ c /\ d ==> e /\ f`) THEN
  CONJ_TAC THENL [MESON_TAC[PATH_SHIFTPATH]; ALL_TAC] THEN
  REWRITE_TAC[simple_path; shiftpath; IN_INTERVAL_1; DROP_VEC;
              DROP_ADD; DROP_SUB] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_VEC; GSYM DROP_EQ] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Choosing a sub-path of an existing path.                                  *)
(* ------------------------------------------------------------------------- *)

let subpath = new_definition
 `subpath u v g = \x. g(u + drop(v - u) % x)`;;

let SUBPATH_SCALING_LEMMA = prove
 (`!u v.
    IMAGE (\x. u + drop(v - u) % x) (interval[vec 0,vec 1]) = segment[u,v]`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; SEGMENT_1] THEN
  REWRITE_TAC[DROP_SUB; REAL_SUB_LE; INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  BINOP_TAC THEN REWRITE_TAC[GSYM LIFT_EQ_CMUL; VECTOR_MUL_RZERO] THEN
  REWRITE_TAC[LIFT_DROP; LIFT_SUB] THEN VECTOR_ARITH_TAC);;

let PATH_IMAGE_SUBPATH_GEN = prove
 (`!u v g:real^1->real^N. path_image(subpath u v g) = IMAGE g (segment[u,v])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_image; subpath] THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  REWRITE_TAC[IMAGE_o; SUBPATH_SCALING_LEMMA]);;

let PATH_IMAGE_SUBPATH = prove
 (`!u v g:real^1->real^N.
        drop u <= drop v
        ==> path_image(subpath u v g) = IMAGE g (interval[u,v])`,
  SIMP_TAC[PATH_IMAGE_SUBPATH_GEN; SEGMENT_1]);;

let PATH_SUBPATH = prove
 (`!u v g:real^1->real^N.
        path g /\ u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1]
        ==> path(subpath u v g)`,
  REWRITE_TAC[path; subpath] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
  SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID;
           CONTINUOUS_ON_CONST] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBPATH_SCALING_LEMMA; SEGMENT_1] THEN
  COND_CASES_TAC THEN REWRITE_TAC[SUBSET_INTERVAL_1] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
  REAL_ARITH_TAC);;

let PATHSTART_SUBPATH = prove
 (`!u v g:real^1->real^N. pathstart(subpath u v g) = g(u)`,
  REWRITE_TAC[pathstart; subpath; VECTOR_MUL_RZERO; VECTOR_ADD_RID]);;

let PATHFINISH_SUBPATH = prove
 (`!u v g:real^1->real^N. pathfinish(subpath u v g) = g(v)`,
  REWRITE_TAC[pathfinish; subpath; GSYM LIFT_EQ_CMUL] THEN
  REWRITE_TAC[LIFT_DROP; VECTOR_ARITH `u + v - u:real^N = v`]);;

let SUBPATH_TRIVIAL = prove
 (`!g. subpath (vec 0) (vec 1) g = g`,
  REWRITE_TAC[subpath; VECTOR_SUB_RZERO; DROP_VEC; VECTOR_MUL_LID;
              VECTOR_ADD_LID; ETA_AX]);;

let SUBPATH_REVERSEPATH = prove
 (`!g. subpath (vec 1) (vec 0) g = reversepath g`,
  REWRITE_TAC[subpath; reversepath; VECTOR_SUB_LZERO; DROP_NEG; DROP_VEC] THEN
  REWRITE_TAC[VECTOR_ARITH `a + -- &1 % b:real^N = a - b`]);;

let REVERSEPATH_SUBPATH = prove
 (`!g u v. reversepath(subpath u v g) = subpath v u g`,
  REWRITE_TAC[reversepath; subpath; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[DROP_SUB; VECTOR_SUB_LDISTRIB] THEN
  REWRITE_TAC[GSYM LIFT_EQ_CMUL; LIFT_SUB; LIFT_DROP] THEN
  VECTOR_ARITH_TAC);;

let SUBPATH_TRANSLATION = prove
 (`!a g u v. subpath u v ((\x. a + x) o g) = (\x. a + x) o subpath u v g`,
  REWRITE_TAC[FUN_EQ_THM; subpath; o_THM]);;

add_translation_invariants [SUBPATH_TRANSLATION];;

let SUBPATH_LINEAR_IMAGE = prove
 (`!f g u v. linear f ==> subpath u v (f o g) = f o subpath u v g`,
  REWRITE_TAC[FUN_EQ_THM; subpath; o_THM]);;

add_linear_invariants [SUBPATH_LINEAR_IMAGE];;

let SIMPLE_PATH_SUBPATH_EQ = prove
 (`!g u v. simple_path(subpath u v g) <=>
           path(subpath u v g) /\ ~(u = v) /\
           (!x y. x IN segment[u,v] /\ y IN segment[u,v] /\ g x = g y
                  ==> x = y \/ x = u /\ y = v \/ x = v /\ y = u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_path; subpath] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM SUBPATH_SCALING_LEMMA] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[VECTOR_ARITH `u + a % x = u <=> a % x = vec 0`;
              VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_MUL_LCANCEL] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_ADD; DROP_SUB;
              REAL_RING `u + (v - u) * y = v <=> v = u \/ y = &1`] THEN
  REWRITE_TAC[REAL_SUB_0; DROP_EQ; GSYM DROP_VEC] THEN
  ASM_CASES_TAC `v:real^1 = u` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_SUB_REFL; DROP_VEC; VECTOR_MUL_LZERO] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`lift(&1 / &2)`; `lift(&3 / &4)`]) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; GSYM DROP_EQ; LIFT_DROP] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let ARC_SUBPATH_EQ = prove
 (`!g u v. arc(subpath u v g) <=>
           path(subpath u v g) /\ ~(u = v) /\
           (!x y. x IN segment[u,v] /\ y IN segment[u,v] /\ g x = g y
                  ==> x = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[arc; subpath] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM SUBPATH_SCALING_LEMMA] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[VECTOR_ARITH `u + a % x = u + a % y <=> a % (x - y) = vec 0`;
              VECTOR_MUL_EQ_0; DROP_EQ_0; VECTOR_SUB_EQ] THEN
  ASM_CASES_TAC `v:real^1 = u` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; DROP_VEC; VECTOR_MUL_LZERO] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`lift(&1 / &2)`; `lift(&3 / &4)`]) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; GSYM DROP_EQ; LIFT_DROP] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let SIMPLE_PATH_SUBPATH = prove
 (`!g u v. simple_path g /\
           u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
           ~(u = v)
           ==> simple_path(subpath u v g)`,
  SIMP_TAC[SIMPLE_PATH_SUBPATH_EQ; PATH_SUBPATH; SIMPLE_PATH_IMP_PATH] THEN
  REWRITE_TAC[simple_path] THEN GEN_TAC THEN
  REWRITE_TAC[FORALL_LIFT] THEN MATCH_MP_TAC REAL_WLOG_LT THEN
  REWRITE_TAC[FORALL_DROP; LIFT_DROP] THEN
  CONJ_TAC THENL [MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  SIMP_TAC[SEGMENT_1; REAL_LT_IMP_LE] THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^1`; `y:real^1`]) THEN
  SUBGOAL_THEN
   `!x:real^1. x IN interval[u,v] ==> x IN interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUBSET; SUBSET_INTERVAL_1] THEN
    ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC; REAL_LE_TRANS];
    ASM_SIMP_TAC[]] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
  REWRITE_TAC[DROP_VEC; GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC);;

let ARC_SIMPLE_PATH_SUBPATH = prove
 (`!g u v. simple_path g /\
           u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
           ~(g u = g v)
           ==> arc(subpath u v g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
  ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  ASM_MESON_TAC[SIMPLE_PATH_SUBPATH]);;

let ARC_SUBPATH_ARC = prove
 (`!u v g. arc g /\
           u IN interval [vec 0,vec 1] /\ v IN interval [vec 0,vec 1] /\
           ~(u = v)
           ==> arc(subpath u v g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
  ASM_MESON_TAC[ARC_IMP_SIMPLE_PATH; arc]);;

let ARC_SIMPLE_PATH_SUBPATH_INTERIOR = prove
 (`!g u v. simple_path g /\
           u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
           ~(u = v) /\ abs(drop u - drop v) < &1
           ==> arc(subpath u v g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_path]) THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^1`; `v:real^1`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC);;

let PATH_IMAGE_SUBPATH_SUBSET = prove
 (`!u v g:real^1->real^N.
        path g /\ u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1]
        ==> path_image(subpath u v g) SUBSET path_image g`,
  SIMP_TAC[PATH_IMAGE_SUBPATH_GEN] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[path_image] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  SIMP_TAC[SEGMENT_CONVEX_HULL; SUBSET_HULL; CONVEX_INTERVAL] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]);;

let JOIN_SUBPATHS_MIDDLE = prove
 (`!p:real^1->real^N.
   subpath (vec 0) (lift(&1 / &2)) p ++ subpath (lift(&1 / &2)) (vec 1) p = p`,
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[joinpaths; subpath] THEN COND_CASES_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_SUB; DROP_CMUL; LIFT_DROP;
              DROP_VEC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some additional lemmas about choosing sub-paths.                          *)
(* ------------------------------------------------------------------------- *)

let EXISTS_SUBPATH_OF_PATH = prove
 (`!g a b:real^N.
        path g /\ a IN path_image g /\ b IN path_image g
        ==> ?h. path h /\ pathstart h = a /\ pathfinish h = b /\
                path_image h SUBSET path_image g`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; path_image; FORALL_IN_IMAGE] THEN
  GEN_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN
  EXISTS_TAC `subpath u v (g:real^1->real^N)` THEN
  ASM_REWRITE_TAC[GSYM path_image; PATH_IMAGE_SUBPATH_GEN] THEN
  ASM_SIMP_TAC[PATH_SUBPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  REWRITE_TAC[path_image] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  SIMP_TAC[SEGMENT_CONVEX_HULL; SUBSET_HULL; CONVEX_INTERVAL] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]);;

let EXISTS_SUBPATH_OF_ARC_NOENDS = prove
 (`!g a b:real^N.
        arc g /\ a IN path_image g /\ b IN path_image g /\
        {a,b} INTER {pathstart g,pathfinish g} = {}
        ==> ?h. path h /\ pathstart h = a /\ pathfinish h = b /\
                path_image h SUBSET
                (path_image g) DIFF {pathstart g,pathfinish g}`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; path_image; FORALL_IN_IMAGE] THEN
  GEN_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `subpath u v (g:real^1->real^N)` THEN
  ASM_SIMP_TAC[PATH_SUBPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
               ARC_IMP_PATH; GSYM path_image; PATH_IMAGE_SUBPATH_GEN] THEN
  REWRITE_TAC[path_image; pathstart; pathfinish] THEN
  REWRITE_TAC[SET_RULE
   `s SUBSET t DIFF {a,b} <=> s SUBSET t /\ ~(a IN s) /\ ~(b IN s)`] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  SUBGOAL_THEN `~(vec 0 IN segment[u:real^1,v]) /\ ~(vec 1 IN segment[u,v])`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
    REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    SIMP_TAC[REAL_ARITH `a <= b ==> (b <= a <=> a = b)`] THEN
    REWRITE_TAC[GSYM DROP_VEC; DROP_EQ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[arc; pathstart; pathfinish]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^1,v] SUBSET interval[vec 0,vec 1]` MP_TAC THENL
   [SIMP_TAC[SEGMENT_CONVEX_HULL; SUBSET_HULL; CONVEX_INTERVAL] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[arc; pathstart; pathfinish]) THEN
  SUBGOAL_THEN `(vec 0:real^1) IN interval[vec 0,vec 1] /\
                (vec 1:real^1) IN interval[vec 0,vec 1]`
  MP_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL];
    ASM SET_TAC[]]);;

let EXISTS_SUBARC_OF_ARC_NOENDS = prove
 (`!g a b:real^N.
        arc g /\ a IN path_image g /\ b IN path_image g /\ ~(a = b) /\
        {a,b} INTER {pathstart g,pathfinish g} = {}
        ==> ?h. arc h /\ pathstart h = a /\ pathfinish h = b /\
                path_image h SUBSET
                (path_image g) DIFF {pathstart g,pathfinish g}`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; path_image; FORALL_IN_IMAGE] THEN
  GEN_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `v:real^1` THEN REPEAT DISCH_TAC THEN
  EXISTS_TAC `subpath u v (g:real^1->real^N)` THEN
  ASM_SIMP_TAC[PATH_SUBPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
               ARC_IMP_PATH; GSYM path_image; PATH_IMAGE_SUBPATH_GEN] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
    ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH];
    ALL_TAC] THEN
  REWRITE_TAC[path_image; pathstart; pathfinish] THEN
  REWRITE_TAC[SET_RULE
   `s SUBSET t DIFF {a,b} <=> s SUBSET t /\ ~(a IN s) /\ ~(b IN s)`] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  SUBGOAL_THEN `~(vec 0 IN segment[u:real^1,v]) /\ ~(vec 1 IN segment[u,v])`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
    REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    SIMP_TAC[REAL_ARITH `a <= b ==> (b <= a <=> a = b)`] THEN
    REWRITE_TAC[GSYM DROP_VEC; DROP_EQ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[arc; pathstart; pathfinish]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^1,v] SUBSET interval[vec 0,vec 1]` MP_TAC THENL
   [SIMP_TAC[SEGMENT_CONVEX_HULL; SUBSET_HULL; CONVEX_INTERVAL] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[arc; pathstart; pathfinish]) THEN
  SUBGOAL_THEN `(vec 0:real^1) IN interval[vec 0,vec 1] /\
                (vec 1:real^1) IN interval[vec 0,vec 1]`
  MP_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL];
    ASM SET_TAC[]]);;

let EXISTS_ARC_PSUBSET_SIMPLE_PATH = prove
 (`!g:real^1->real^N.
        simple_path g /\ closed s /\ s PSUBSET path_image g
        ==> ?h. arc h /\
                s SUBSET path_image h /\
                path_image h SUBSET path_image g`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP SIMPLE_PATH_CASES) THENL
   [EXISTS_TAC `g:real^1->real^N` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [path_image] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `(h:real^1->real^N) = shiftpath u g` THEN
  SUBGOAL_THEN
   `simple_path(h:real^1->real^N) /\
    pathstart h = (g:real^1->real^N) u /\
    pathfinish h = (g:real^1->real^N) u /\
    path_image h = path_image g`
  MP_TAC THENL
   [EXPAND_TAC "h" THEN
    ASM_MESON_TAC[SIMPLE_PATH_SHIFTPATH; PATH_IMAGE_SHIFTPATH;
                  PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH;
                  IN_INTERVAL_1; DROP_VEC];
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_THEN `pathstart(h:real^1->real^N) = (g:real^1->real^N) u`
        (SUBST_ALL_TAC o SYM)] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (interval[vec 0,vec 1]))
            {x:real^1 | x IN interval[vec 0,vec 1] /\
                        (h x) IN ((:real^N) DIFF s)}`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_SIMP_TAC[GSYM path; GSYM closed; SIMPLE_PATH_IMP_PATH];
    REWRITE_TAC[open_in] THEN DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `vec 0:real^1` th) THEN MP_TAC(SPEC `vec 1:real^1` th)) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
  REWRITE_TAC[DIST_REAL; VEC_COMPONENT; REAL_SUB_RZERO] THEN
  SIMP_TAC[GSYM drop] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[pathfinish]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[pathstart]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `subpath (lift(min d1 (&1 / &4))) (lift(&1 - min d2 (&1 / &4)))
            (h:real^1->real^N)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH_INTERIOR THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP; LIFT_EQ] THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> t INTER s SUBSET u ==> s SUBSET u`)) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IMP_CONJ] THEN
    SIMP_TAC[PATH_IMAGE_SUBPATH; LIFT_DROP;
             REAL_ARITH `min d1 (&1 / &4) <= &1 - min d2 (&1 / &4)`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; path_image; IN_INTERVAL_1; DROP_VEC] THEN
    X_GEN_TAC `x:real^1` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^1` THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC PATH_IMAGE_SUBPATH_SUBSET THEN
    ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC]);;

let EXISTS_DOUBLE_ARC = prove
 (`!g:real^1->real^N a b.
        simple_path g /\ pathfinish g = pathstart g /\
        a IN path_image g /\ b IN path_image g /\ ~(a = b)
        ==> ?u d. arc u /\ arc d /\
                  pathstart u = a /\ pathfinish u = b /\
                  pathstart d = b /\ pathfinish d = a /\
                  (path_image u) INTER (path_image d) = {a,b} /\
                  (path_image u) UNION (path_image d) = path_image g`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; path_image] THEN
  ONCE_REWRITE_TAC[FORALL_IN_IMAGE] THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN REWRITE_TAC[GSYM path_image] THEN
  X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `h = shiftpath u (g:real^1->real^N)` THEN
  SUBGOAL_THEN
   `simple_path(h:real^1->real^N) /\
    pathstart h = g u /\
    pathfinish h = g u /\
    path_image h = path_image g`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    ASM_SIMP_TAC[SIMPLE_PATH_SHIFTPATH; PATH_IMAGE_SHIFTPATH] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    EXPAND_TAC "h" THEN
    ASM_SIMP_TAC[PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH];
    UNDISCH_THEN `path_image h :real^N->bool = path_image g`
     (SUBST_ALL_TAC o SYM)] THEN
  UNDISCH_TAC `(b:real^N) IN path_image h` THEN
  REWRITE_TAC[IN_IMAGE; path_image; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN REWRITE_TAC[GSYM path_image] THEN
  MAP_EVERY EXISTS_TAC
   [`subpath (vec 0) v (h:real^1->real^N)`;
    `subpath v (vec 1) (h:real^1->real^N)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  UNDISCH_THEN `b = (h:real^1->real^N) v` SUBST_ALL_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]
   (ASSUME `(v:real^1) IN interval[vec 0,vec 1]`)) THEN
  ASM_SIMP_TAC[ARC_SIMPLE_PATH_SUBPATH; IN_INTERVAL_1; DROP_VEC;
               REAL_LE_REFL; REAL_POS; PATH_IMAGE_SUBPATH] THEN
  REWRITE_TAC[GSYM IMAGE_UNION; path_image] THEN
  UNDISCH_THEN `(h:real^1->real^N)(vec 0) = (g:real^1->real^N) u`
   (SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN
   `interval[vec 0,v] UNION interval[v,vec 1] = interval[vec 0:real^1,vec 1]`
  ASSUME_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[IMAGE_SUBSET] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x y. x IN (s UNION t) /\ y IN (s UNION t) /\ f x = f y
             ==> x = y \/ x = vec 0 /\ y = vec 1 \/ x = vec 1 /\ y = vec 0) /\
      (f(vec 0) = f(vec 1)) /\ (vec 0) IN s /\ (vec 1) IN t /\
      s INTER t = {c}
      ==> IMAGE f s INTER IMAGE f t = {f (vec 0), f c}`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[simple_path]) THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY; IN_INTER; IN_UNION] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_VEC] THEN ASM_REAL_ARITH_TAC);;

let SUBPATH_TO_FRONTIER_EXPLICIT = prove
 (`!g:real^1->real^N s.
        path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?u. u IN interval[vec 0,vec 1] /\
                (!x. &0 <= drop x /\ drop x < drop u ==> g x IN interior s) /\
                ~(g u IN interior s) /\
                (u = vec 0 \/ g u IN closure s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{u | lift u IN interval[vec 0,vec 1] /\
                     g(lift u) IN closure((:real^N) DIFF s)}`
         COMPACT_ATTAINS_INF) THEN
  SIMP_TAC[LIFT_DROP; SET_RULE
   `(!x. lift(drop x) = x) ==> IMAGE lift {x | P(lift x)} = {x | P x}`] THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[path; pathstart; pathfinish; SUBSET;
                                path_image; FORALL_IN_IMAGE]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        REWRITE_TAC[BOUNDED_INTERVAL] THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
        ASM_REWRITE_TAC[CLOSED_CLOSURE; CLOSED_INTERVAL]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[LIFT_NUM] THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_DROP; FORALL_DROP; IN_ELIM_THM; LIFT_DROP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^1` THEN
  REWRITE_TAC[CLOSURE_COMPLEMENT; IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[subpath; VECTOR_SUB_RZERO; VECTOR_ADD_LID] THEN
  ASM_REWRITE_TAC[GSYM LIFT_EQ_CMUL; LIFT_DROP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; GSYM DROP_EQ] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE BINDER_CONV
     [TAUT `a /\ ~b ==> c <=> a /\ ~c ==> b`]) THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o SPEC `x:real^1`) THEN DISCH_TAC] THEN
  ASM_CASES_TAC `drop u = &0` THEN
  ASM_REWRITE_TAC[frontier; IN_DIFF; CLOSURE_APPROACHABLE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[path; pathstart; pathfinish]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_on]) THEN
  DISCH_THEN(MP_TAC o SPEC `u:real^1`) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `lift(max (&0) (drop u - d / &2))`) THEN
  REWRITE_TAC[LIFT_DROP; DIST_REAL; GSYM drop] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC
   (MESON[] `P a ==> dist(a,y) < e ==> ?x. P x /\ dist(x,y) < e`) THEN
  MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN ASM_ARITH_TAC);;

let SUBPATH_TO_FRONTIER_STRONG = prove
 (`!g:real^1->real^N s.
        path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?u. u IN interval[vec 0,vec 1] /\
                 ~(pathfinish(subpath (vec 0) u g) IN interior s) /\
                (u = vec 0 \/
                 (!x. x IN interval[vec 0,vec 1] /\ ~(x = vec 1)
                      ==> (subpath (vec 0) u g x) IN interior s) /\
                 pathfinish(subpath (vec 0) u g) IN closure s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUBPATH_TO_FRONTIER_EXPLICIT) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^1` THEN
  REWRITE_TAC[subpath; pathfinish; VECTOR_SUB_RZERO; VECTOR_ADD_LID] THEN
  ASM_CASES_TAC `u:real^1 = vec 0` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO] THEN
  ASM_REWRITE_TAC[GSYM LIFT_EQ_CMUL; LIFT_DROP] THEN
  X_GEN_TAC `x:real^1` THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_VEC] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  ASM_SIMP_TAC[DROP_CMUL; REAL_LE_MUL] THEN
  REWRITE_TAC[REAL_ARITH `u * x < u <=> &0 < u * (&1 - x)`] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_SUB_LT] THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN
  ASM_REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP; LIFT_NUM]);;

let SUBPATH_TO_FRONTIER = prove
 (`!g:real^1->real^N s.
        path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?u. u IN interval[vec 0,vec 1] /\
                pathfinish(subpath (vec 0) u g) IN frontier s /\
                (path_image(subpath (vec 0) u g) DELETE
                 pathfinish(subpath (vec 0) u g))
                SUBSET interior s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[frontier; IN_DIFF] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUBPATH_TO_FRONTIER_STRONG) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^1` THEN
  ASM_CASES_TAC `u:real^1 = vec 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart]) THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
    REWRITE_TAC[subpath; path_image; VECTOR_SUB_REFL; DROP_VEC;
                VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
    SET_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; path_image; FORALL_IN_IMAGE; IN_DELETE; IMP_CONJ] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; pathfinish] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_MESON_TAC[]]);;

let EXISTS_PATH_SUBPATH_TO_FRONTIER = prove
 (`!g:real^1->real^N s.
        path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?h. path h /\ pathstart h = pathstart g /\
                (path_image h) SUBSET (path_image g) /\
                (path_image h DELETE (pathfinish h)) SUBSET interior s /\
                pathfinish h IN frontier s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SUBPATH_TO_FRONTIER) THEN
  EXISTS_TAC `subpath (vec 0) u (g:real^1->real^N)` THEN
  ASM_SIMP_TAC[PATH_SUBPATH; IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL;
               PATHSTART_SUBPATH; PATH_IMAGE_SUBPATH_SUBSET] THEN
  REWRITE_TAC[pathstart]);;

let EXISTS_PATH_SUBPATH_TO_FRONTIER_CLOSED = prove
 (`!g:real^1->real^N s.
        closed s /\ path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?h. path h /\ pathstart h = pathstart g /\
                (path_image h) SUBSET (path_image g) INTER s /\
                pathfinish h IN frontier s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EXISTS_PATH_SUBPATH_TO_FRONTIER) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[SUBSET_INTER] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
   `(pathfinish h:real^N) INSERT (path_image h DELETE pathfinish h)` THEN
  CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[INSERT_SUBSET]] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[frontier; CLOSURE_EQ; IN_DIFF];
    ASM_MESON_TAC[SUBSET_TRANS; INTERIOR_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Special case of straight-line paths.                                      *)
(* ------------------------------------------------------------------------- *)

let linepath = new_definition
 `linepath(a,b) = \x. (&1 - drop x) % a + drop x % b`;;

let LINEPATH_TRANSLATION = prove
 (`!a b c. linepath(a + b,a + c) = (\x. a + x) o linepath(b,c)`,
  REWRITE_TAC[linepath; o_THM; FUN_EQ_THM] THEN VECTOR_ARITH_TAC);;

add_translation_invariants [LINEPATH_TRANSLATION];;

let LINEPATH_LINEAR_IMAGE = prove
 (`!f. linear f ==> !b c. linepath(f b,f c) = f o linepath(b,c)`,
  REWRITE_TAC[linepath; o_THM; FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_ADD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_CMUL) THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

add_linear_invariants [LINEPATH_LINEAR_IMAGE];;

let PATHSTART_LINEPATH = prove
 (`!a b. pathstart(linepath(a,b)) = a`,
  REWRITE_TAC[linepath; pathstart; DROP_VEC] THEN VECTOR_ARITH_TAC);;

let PATHFINISH_LINEPATH = prove
 (`!a b. pathfinish(linepath(a,b)) = b`,
  REWRITE_TAC[linepath; pathfinish; DROP_VEC] THEN VECTOR_ARITH_TAC);;

let CONTINUOUS_LINEPATH_AT = prove
 (`!a b x. linepath(a,b) continuous (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linepath] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - u) % x + y = x + u % --x + y`] THEN
  MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_VMUL THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_AT_ID]);;

let CONTINUOUS_ON_LINEPATH = prove
 (`!a b s. linepath(a,b) continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_LINEPATH_AT]);;

let PATH_LINEPATH = prove
 (`!a b. path(linepath(a,b))`,
  REWRITE_TAC[path; CONTINUOUS_ON_LINEPATH]);;

let PATH_IMAGE_LINEPATH = prove
 (`!a b. path_image(linepath (a,b)) = segment[a,b]`,
  REWRITE_TAC[segment; path_image; linepath] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTERVAL] THEN
  SIMP_TAC[DIMINDEX_1; FORALL_1; VEC_COMPONENT; ARITH] THEN
  REWRITE_TAC[EXISTS_LIFT; GSYM drop; LIFT_DROP] THEN MESON_TAC[]);;

let REVERSEPATH_LINEPATH = prove
 (`!a b. reversepath(linepath(a,b)) = linepath(b,a)`,
  REWRITE_TAC[reversepath; linepath; DROP_SUB; DROP_VEC; FUN_EQ_THM] THEN
  VECTOR_ARITH_TAC);;

let ARC_LINEPATH = prove
 (`!a b. ~(a = b) ==> arc(linepath(a,b))`,
  REWRITE_TAC[arc; PATH_LINEPATH] THEN REWRITE_TAC[linepath] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(&1 - x) % a + x % b:real^N = (&1 - y) % a + y % b <=>
    (x - y) % (a - b) = vec 0`] THEN
  SIMP_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; DROP_EQ; REAL_SUB_0]);;

let SIMPLE_PATH_LINEPATH = prove
 (`!a b. ~(a = b) ==> simple_path(linepath(a,b))`,
  MESON_TAC[ARC_IMP_SIMPLE_PATH; ARC_LINEPATH]);;

let SIMPLE_PATH_LINEPATH_EQ = prove
 (`!a b:real^N. simple_path(linepath(a,b)) <=> ~(a = b)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[SIMPLE_PATH_LINEPATH] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[simple_path] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[linepath; GSYM VECTOR_ADD_RDISTRIB] THEN
  DISCH_THEN(MP_TAC o SPECL [`lift(&0)`; `lift(&1 / &2)`]) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; GSYM DROP_EQ; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let ARC_LINEPATH_EQ = prove
 (`!a b. arc(linepath(a,b)) <=> ~(a = b)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[ARC_LINEPATH] THEN
  MESON_TAC[SIMPLE_PATH_LINEPATH_EQ; ARC_IMP_SIMPLE_PATH]);;

let LINEPATH_REFL = prove
 (`!a. linepath(a,a) = \x. a`,
  REWRITE_TAC[linepath; VECTOR_ARITH `(&1 - u) % x + u % x:real^N = x`]);;

let SHIFTPATH_TRIVIAL = prove
 (`!t a. shiftpath t (linepath(a,a)) = linepath(a,a)`,
  REWRITE_TAC[shiftpath; LINEPATH_REFL; COND_ID]);;

let SUBPATH_REFL = prove
 (`!g a. subpath a a g = linepath(g a,g a)`,
  REWRITE_TAC[subpath; linepath; VECTOR_SUB_REFL; DROP_VEC; VECTOR_MUL_LZERO;
              FUN_EQ_THM; VECTOR_ADD_RID] THEN
  VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bounding a point away from a path.                                        *)
(* ------------------------------------------------------------------------- *)

let NOT_ON_PATH_BALL = prove
 (`!g z:real^N.
        path g /\ ~(z IN path_image g)
        ==> ?e. &0 < e /\ ball(z,e) INTER (path_image g) = {}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`path_image g:real^N->bool`; `z:real^N`]
     DISTANCE_ATTAINS_INF) THEN
  REWRITE_TAC[PATH_IMAGE_NONEMPTY] THEN
  ASM_SIMP_TAC[COMPACT_PATH_IMAGE; COMPACT_IMP_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `dist(z:real^N,a)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIST_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_BALL; IN_INTER] THEN
  ASM_MESON_TAC[REAL_NOT_LE]);;

let NOT_ON_PATH_CBALL = prove
 (`!g z:real^N.
        path g /\ ~(z IN path_image g)
        ==> ?e. &0 < e /\ cball(z,e) INTER (path_image g) = {}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NOT_ON_PATH_BALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `s INTER u = {} ==> t SUBSET s ==> t INTER u = {}`)) THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Homeomorphisms of arc images.                                             *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHISM_ARC = prove
 (`!g:real^1->real^N.
     arc g ==> ?h. homeomorphism (interval[vec 0,vec 1],path_image g) (g,h)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
  ASM_REWRITE_TAC[path_image; COMPACT_INTERVAL; GSYM path; GSYM arc]);;

let HOMEOMORPHIC_ARC_IMAGE_INTERVAL = prove
 (`!g:real^1->real^N a b:real^1.
      arc g /\ drop a < drop b ==> (path_image g) homeomorphic interval[a,b]`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `interval[vec 0:real^1,vec 1]` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    EXISTS_TAC `g:real^1->real^N` THEN ASM_SIMP_TAC[HOMEOMORPHISM_ARC];
    MATCH_MP_TAC HOMEOMORPHIC_CLOSED_INTERVALS THEN
    ASM_REWRITE_TAC[INTERVAL_NE_EMPTY_1; DROP_VEC; REAL_LT_01]]);;

let HOMEOMORPHIC_ARC_IMAGES = prove
 (`!g:real^1->real^M h:real^1->real^N.
        arc g /\ arc h ==> (path_image g) homeomorphic (path_image h)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `interval[vec 0:real^1,vec 1]` THEN
  CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM]] THEN
  MATCH_MP_TAC HOMEOMORPHIC_ARC_IMAGE_INTERVAL THEN
  ASM_REWRITE_TAC[DROP_VEC; REAL_LT_01]);;

let HOMEOMORPHIC_ARC_IMAGE_SEGMENT = prove
 (`!g:real^1->real^N a b:real^M.
        arc g /\ ~(a = b) ==> (path_image g) homeomorphic segment[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH] THEN
  MATCH_MP_TAC HOMEOMORPHIC_ARC_IMAGES THEN
  ASM_REWRITE_TAC[ARC_LINEPATH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Path component, considered as a "joinability" relation (from Tom Hales).  *)
(* ------------------------------------------------------------------------- *)

let path_component = new_definition
 `path_component s x y <=>
        ?g. path g /\ path_image g SUBSET s /\
            pathstart g = x /\ pathfinish g = y`;;

let PATH_COMPONENT_IN = prove
 (`!s x y. path_component s x y ==> x IN s /\ y IN s`,
  REWRITE_TAC[path_component; path_image; pathstart; pathfinish] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_LE_REFL; REAL_POS]);;

let PATH_COMPONENT_REFL = prove
 (`!s x:real^N. x IN s ==> path_component s x x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_component] THEN
  EXISTS_TAC `(\u. x):real^1->real^N` THEN
  REWRITE_TAC[pathstart; pathfinish; path_image; path;
              CONTINUOUS_ON_CONST; IMAGE; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let PATH_COMPONENT_REFL_EQ = prove
 (`!s x:real^N. path_component s x x <=> x IN s`,
  MESON_TAC[PATH_COMPONENT_IN; PATH_COMPONENT_REFL]);;

let PATH_COMPONENT_SYM = prove
 (`!s x y:real^N. path_component s x y ==> path_component s y x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_component] THEN
  MESON_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
            PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH]);;

let PATH_COMPONENT_SYM_EQ = prove
 (`!s x y. path_component s x y <=> path_component s y x`,
  MESON_TAC[PATH_COMPONENT_SYM]);;

let PATH_COMPONENT_TRANS = prove
 (`!s x y:real^N.
    path_component s x y /\ path_component s y z ==> path_component s x z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_component] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `g1:real^1->real^N`) (X_CHOOSE_TAC `g2:real^1->real^N`)) THEN
  EXISTS_TAC `g1 ++ g2 :real^1->real^N` THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; UNION_SUBSET;
               PATHSTART_JOIN; PATHFINISH_JOIN]);;

let PATH_COMPONENT_OF_SUBSET = prove
 (`!s t x. s SUBSET t /\ path_component s x y ==> path_component t x y`,
  REWRITE_TAC[path_component] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Can also consider it as a set, as the name suggests.                      *)
(* ------------------------------------------------------------------------- *)

let PATH_COMPONENT_SET = prove
 (`!s x. path_component s x =
            { y | ?g. path g /\ path_image g SUBSET s /\
                      pathstart g = x /\ pathfinish g = y }`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REWRITE_TAC[IN; path_component]);;

let PATH_COMPONENT_SUBSET = prove
 (`!s x. (path_component s x) SUBSET s`,
  REWRITE_TAC[SUBSET; IN] THEN MESON_TAC[PATH_COMPONENT_IN; IN]);;

let PATH_COMPONENT_EQ_EMPTY = prove
 (`!s x. path_component s x = {} <=> ~(x IN s)`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
  MESON_TAC[IN; PATH_COMPONENT_REFL; PATH_COMPONENT_IN]);;

let PATH_COMPONENT_EMPTY = prove
 (`!x. path_component {} x = {}`,
  REWRITE_TAC[PATH_COMPONENT_EQ_EMPTY; NOT_IN_EMPTY]);;

let UNIONS_PATH_COMPONENT = prove
 (`!s:real^N->bool. UNIONS {path_component s x |x| x IN s} = s`,
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; PATH_COMPONENT_SUBSET] THEN
  REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
  ASM_REWRITE_TAC[PATH_COMPONENT_REFL_EQ]);;

let PATH_COMPONENT_TRANSLATION = prove
 (`!a s x. path_component (IMAGE (\x. a + x) s) (a + x) =
                IMAGE (\x. a + x) (path_component s x)`,
  REWRITE_TAC[PATH_COMPONENT_SET] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [PATH_COMPONENT_TRANSLATION];;

let PATH_COMPONENT_LINEAR_IMAGE = prove
 (`!f s x. linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
           ==> path_component (IMAGE f s) (f x) =
               IMAGE f (path_component s x)`,
  REWRITE_TAC[PATH_COMPONENT_SET] THEN
  GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [PATH_COMPONENT_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Path connectedness of a space.                                            *)
(* ------------------------------------------------------------------------- *)

let path_connected = new_definition
 `path_connected s <=>
        !x y. x IN s /\ y IN s
              ==> ?g. path g /\ (path_image g) SUBSET s /\
                      pathstart g = x /\ pathfinish g = y`;;

let PATH_CONNECTED_IFF_PATH_COMPONENT = prove
 (`!s. path_connected s <=> !x y. x IN s /\ y IN s ==> path_component s x y`,
  REWRITE_TAC[path_connected; path_component]);;

let PATH_CONNECTED_COMPONENT_SET = prove
 (`!s. path_connected s <=> !x. x IN s ==> path_component s x = s`,
  REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT; GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[PATH_COMPONENT_SUBSET] THEN SET_TAC[]);;

let PATH_COMPONENT_MONO = prove
 (`!s t x. s SUBSET t ==> (path_component s x) SUBSET (path_component t x)`,
  REWRITE_TAC[PATH_COMPONENT_SET] THEN SET_TAC[]);;

let PATH_COMPONENT_MAXIMAL = prove
 (`!s t x. x IN t /\ path_connected t /\ t SUBSET s
           ==> t SUBSET (path_component s x)`,
  REWRITE_TAC[path_connected; PATH_COMPONENT_SET; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let PATH_COMPONENT_EQ = prove
 (`!s x y. y IN path_component s x
           ==> path_component s y = path_component s x`,
  REWRITE_TAC[EXTENSION; IN] THEN
  MESON_TAC[PATH_COMPONENT_SYM; PATH_COMPONENT_TRANS]);;

let PATH_COMPONENT_PATH_IMAGE_PATHSTART = prove
 (`!p x:real^N.
        path p /\ x IN path_image p
        ==> path_component (path_image p) (pathstart p) x`,
  REWRITE_TAC[path_image; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^1 = vec 0` THENL
   [ASM_REWRITE_TAC[pathstart] THEN MATCH_MP_TAC PATH_COMPONENT_REFL THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    REWRITE_TAC[DROP_VEC; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[path_component] THEN
  EXISTS_TAC `\y. (p:real^1->real^N)(drop x % y)` THEN
  ASM_REWRITE_TAC[path; path_image; pathstart; pathfinish] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path]) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET);
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN REWRITE_TAC[IMAGE_o] THEN
    MATCH_MP_TAC IMAGE_SUBSET;
    AP_TERM_TAC THEN REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC] THEN
    REWRITE_TAC[REAL_MUL_RID]] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
  SIMP_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC; REAL_LE_MUL] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

let PATH_CONNECTED_PATH_IMAGE = prove
 (`!p:real^1->real^N. path p ==> path_connected(path_image p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC PATH_COMPONENT_TRANS THEN
  EXISTS_TAC `pathstart p :real^N` THEN
  ASM_MESON_TAC[PATH_COMPONENT_PATH_IMAGE_PATHSTART; PATH_COMPONENT_SYM]);;

let PATH_CONNECTED_PATH_COMPONENT = prove
 (`!s x:real^N. path_connected(path_component s x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_connected; IN] THEN
  MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `path_component s y (z:real^N)` MP_TAC THENL
   [ASM_MESON_TAC[PATH_COMPONENT_SYM; PATH_COMPONENT_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[path_component] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^1->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `path_component s (x:real^N) = path_component s y`
  SUBST1_TAC THENL [ASM_MESON_TAC[PATH_COMPONENT_EQ; IN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^1->real^N`; `w:real^N`]
     PATH_COMPONENT_PATH_IMAGE_PATHSTART) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PATH_COMPONENT_MONO) THEN
  REWRITE_TAC[SUBSET; IN] THEN MESON_TAC[]);;

let PATH_COMPONENT = prove
 (`!s x y:real^N.
        path_component s x y <=>
        ?t. path_connected t /\ t SUBSET s /\ x IN t /\ y IN t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `path_component s (x:real^N)` THEN
    REWRITE_TAC[PATH_CONNECTED_PATH_COMPONENT; PATH_COMPONENT_SUBSET] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PATH_COMPONENT_IN) THEN
    ASM_SIMP_TAC[IN; PATH_COMPONENT_REFL_EQ];
    REWRITE_TAC[path_component] THEN ASM_MESON_TAC[path_connected; SUBSET]]);;

let PATH_COMPONENT_PATH_COMPONENT = prove
 (`!s x:real^N.
        path_component (path_component s x) x = path_component s x`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN s` THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    SIMP_TAC[PATH_COMPONENT_MONO; PATH_COMPONENT_SUBSET] THEN
    MATCH_MP_TAC PATH_COMPONENT_MAXIMAL THEN
    REWRITE_TAC[SUBSET_REFL; PATH_CONNECTED_PATH_COMPONENT] THEN
    ASM_REWRITE_TAC[IN; PATH_COMPONENT_REFL_EQ];
    MATCH_MP_TAC(SET_RULE `s = {} /\ t = {} ==> s = t`) THEN
    ASM_REWRITE_TAC[PATH_COMPONENT_EQ_EMPTY] THEN
    ASM_MESON_TAC[SUBSET; PATH_COMPONENT_SUBSET]]);;

let PATH_CONNECTED_LINEPATH = prove
 (`!s a b:real^N. segment[a,b] SUBSET s ==> path_component s a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_component] THEN
  EXISTS_TAC `linepath(a:real^N,b)` THEN
  ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_LINEPATH] THEN
  ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH]);;

let PATH_COMPONENT_DISJOINT = prove
 (`!s a b. DISJOINT (path_component s a) (path_component s b) <=>
             ~(a IN path_component s b)`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN] THEN MESON_TAC[PATH_COMPONENT_SYM; PATH_COMPONENT_TRANS]);;

let PATH_COMPONENT_EQ_EQ = prove
 (`!s x y:real^N.
        path_component s x = path_component s y <=>
        ~(x IN s) /\ ~(y IN s) \/
        x IN s /\ y IN s /\ path_component s x y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(y:real^N) IN s` THENL
   [ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN
      ASM_MESON_TAC[PATH_COMPONENT_TRANS; PATH_COMPONENT_REFL;
                    PATH_COMPONENT_SYM];
      ASM_MESON_TAC[PATH_COMPONENT_EQ_EMPTY]];
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM PATH_COMPONENT_EQ_EMPTY]) THEN
    ASM_REWRITE_TAC[PATH_COMPONENT_EQ_EMPTY] THEN
    ONCE_REWRITE_TAC[PATH_COMPONENT_SYM_EQ] THEN
    ASM_REWRITE_TAC[EMPTY] THEN ASM_MESON_TAC[PATH_COMPONENT_EQ_EMPTY]]);;

let PATH_COMPONENT_UNIQUE = prove
 (`!s c x:real^N.
        x IN c /\ c SUBSET s /\ path_connected c /\
        (!c'. x IN c' /\ c' SUBSET s /\ path_connected c'
              ==> c' SUBSET c)
        ==> path_component s x = c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[PATH_COMPONENT_SUBSET; PATH_CONNECTED_PATH_COMPONENT] THEN
    REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[PATH_COMPONENT_REFL_EQ] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC PATH_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]]);;

let PATH_COMPONENT_INTERMEDIATE_SUBSET = prove
 (`!t u a:real^N.
        path_component u a SUBSET t /\ t SUBSET u
        ==> path_component t a = path_component u a`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(a:real^N) IN u` THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_COMPONENT_UNIQUE THEN
    ASM_REWRITE_TAC[PATH_CONNECTED_PATH_COMPONENT] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[PATH_COMPONENT_REFL; IN]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_COMPONENT_MAXIMAL THEN
    ASM SET_TAC[];
    ASM_MESON_TAC[PATH_COMPONENT_EQ_EMPTY; SUBSET]]);;

let COMPLEMENT_PATH_COMPONENT_UNIONS = prove
 (`!s x:real^N.
     s DIFF path_component s x =
     UNIONS({path_component s y | y | y IN s} DELETE (path_component s x))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM UNIONS_PATH_COMPONENT] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s DELETE a ==> DISJOINT a x)
     ==> UNIONS s DIFF a = UNIONS (s DELETE a)`) THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC; IN_DELETE] THEN
  SIMP_TAC[PATH_COMPONENT_DISJOINT; PATH_COMPONENT_EQ_EQ] THEN
  MESON_TAC[IN; SUBSET; PATH_COMPONENT_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* General "locally connected implies connected" type results.               *)
(* ------------------------------------------------------------------------- *)

let OPEN_GENERAL_COMPONENT = prove
 (`!c. (!s x y. c s x y ==> x IN s /\ y IN s) /\
       (!s x y. c s x y ==> c s y x) /\
       (!s x y z. c s x y /\ c s y z ==> c s x z) /\
       (!s t x y. s SUBSET t /\ c s x y ==> c t x y) /\
       (!s x y e. y IN ball(x,e) /\ ball(x,e) SUBSET s
                  ==> c (ball(x,e)) x y)
       ==> !s x:real^N. open s ==> open(c s x)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IN") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SYM") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "TRANS") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SUBSET") (LABEL_TAC "BALL")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL; SUBSET; IN_BALL] THEN
  DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[SUBSET; IN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN s /\ y IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN s`)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REMOVE_THEN "TRANS" MATCH_MP_TAC THEN EXISTS_TAC `y:real^N` THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "SUBSET" MATCH_MP_TAC THEN
  EXISTS_TAC `ball(y:real^N,e)` THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  REMOVE_THEN "BALL" MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_MESON_TAC[]);;

let OPEN_NON_GENERAL_COMPONENT = prove
 (`!c. (!s x y. c s x y ==> x IN s /\ y IN s) /\
       (!s x y. c s x y ==> c s y x) /\
       (!s x y z. c s x y /\ c s y z ==> c s x z) /\
       (!s t x y. s SUBSET t /\ c s x y ==> c t x y) /\
       (!s x y e. y IN ball(x,e) /\ ball(x,e) SUBSET s
                  ==> c (ball(x,e)) x y)
       ==> !s x:real^N. open s ==> open(s DIFF c s x)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IN") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SYM") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "TRANS") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SUBSET") (LABEL_TAC "BALL")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL; SUBSET; IN_BALL] THEN
  DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o REWRITE_RULE[IN])) THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN s`)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[IN] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
  REMOVE_THEN "TRANS" MATCH_MP_TAC THEN EXISTS_TAC `z:real^N` THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "SUBSET" MATCH_MP_TAC THEN
  EXISTS_TAC `ball(y:real^N,e)` THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  REMOVE_THEN "SYM" MATCH_MP_TAC THEN
  REMOVE_THEN "BALL" MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_MESON_TAC[]);;

let GENERAL_CONNECTED_OPEN = prove
 (`!c. (!s x y. c s x y ==> x IN s /\ y IN s) /\
       (!s x y. c s x y ==> c s y x) /\
       (!s x y z. c s x y /\ c s y z ==> c s x z) /\
       (!s t x y. s SUBSET t /\ c s x y ==> c t x y) /\
       (!s x y e. y IN ball(x,e) /\ ball(x,e) SUBSET s
                  ==> c (ball(x,e)) x y)
       ==> !s x y:real^N. open s /\ connected s /\ x IN s /\ y IN s
                          ==> c s x y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected]) THEN
  REWRITE_TAC[IN] THEN REWRITE_TAC[NOT_EXISTS_THM; LEFT_IMP_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`c (s:real^N->bool) (x:real^N):real^N->bool`;
    `s DIFF (c (s:real^N->bool) (x:real^N))`] THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ c /\ d /\ e /\ (f ==> g)
                     ==> ~(a /\ b /\ c /\ d /\ e /\ ~f) ==> g`) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `c:(real^N->bool)->real^N->real^N->bool`
        OPEN_GENERAL_COMPONENT) THEN ASM_MESON_TAC[];
    MP_TAC(SPEC `c:(real^N->bool)->real^N->real^N->bool`
        OPEN_NON_GENERAL_COMPONENT) THEN ASM_MESON_TAC[];
    SET_TAC[];
    SET_TAC[];
    ALL_TAC;
    ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^N` THEN
  ASM_REWRITE_TAC[IN_INTER] THEN REWRITE_TAC[IN] THEN
  FIRST_ASSUM(MATCH_MP_TAC o
    SPECL [`ball(x:real^N,e)`; `s:real^N->bool`]) THEN
  ASM_MESON_TAC[CENTRE_IN_BALL]);;

(* ------------------------------------------------------------------------- *)
(* Some useful lemmas about path-connectedness.                              *)
(* ------------------------------------------------------------------------- *)

let CONVEX_IMP_PATH_CONNECTED = prove
 (`!s:real^N->bool. convex s ==> path_connected s`,
  REWRITE_TAC[CONVEX_ALT; path_connected] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `\u. (&1 - drop u) % x + drop u % y:real^N` THEN
  ASM_SIMP_TAC[pathstart; pathfinish; DROP_VEC; path; path_image;
               SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; GSYM FORALL_DROP] THEN
  CONJ_TAC THENL [ALL_TAC; CONJ_TAC THEN VECTOR_ARITH_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
  REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP; LIFT_NUM] THEN
  SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]);;

let PATH_CONNECTED_UNIV = prove
 (`path_connected(:real^N)`,
  SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_UNIV]);;

let IS_INTERVAL_PATH_CONNECTED = prove
 (`!s. is_interval s ==> path_connected s`,
  SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; IS_INTERVAL_CONVEX]);;

let PATH_CONNECTED_INTERVAL = prove
 (`(!a b:real^N. path_connected(interval[a,b])) /\
   (!a b:real^N. path_connected(interval(a,b)))`,
  SIMP_TAC[IS_INTERVAL_PATH_CONNECTED; IS_INTERVAL_INTERVAL]);;

let PATH_COMPONENT_UNIV = prove
 (`!x. path_component(:real^N) x = (:real^N)`,
  MESON_TAC[PATH_CONNECTED_COMPONENT_SET; PATH_CONNECTED_UNIV; IN_UNIV]);;

let PATH_CONNECTED_IMP_CONNECTED = prove
 (`!s:real^N->bool. path_connected s ==> connected s`,
  GEN_TAC THEN
  REWRITE_TAC[path_connected; CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `path_image(g:real^1->real^N)` THEN
  ASM_MESON_TAC[CONNECTED_PATH_IMAGE; PATHSTART_IN_PATH_IMAGE;
                PATHFINISH_IN_PATH_IMAGE]);;

let OPEN_PATH_COMPONENT = prove
 (`!s x:real^N. open s ==> open(path_component s x)`,
  MATCH_MP_TAC OPEN_GENERAL_COMPONENT THEN
  REWRITE_TAC[PATH_COMPONENT_IN; PATH_COMPONENT_SYM; PATH_COMPONENT_TRANS;
              PATH_COMPONENT_OF_SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[PATH_CONNECTED_IFF_PATH_COMPONENT]
   (MATCH_MP CONVEX_IMP_PATH_CONNECTED (SPEC_ALL CONVEX_BALL))) THEN
  ASM_MESON_TAC[CENTRE_IN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE; NOT_IN_EMPTY]);;

let OPEN_NON_PATH_COMPONENT = prove
 (`!s x:real^N. open s ==> open(s DIFF path_component s x)`,
  MATCH_MP_TAC OPEN_NON_GENERAL_COMPONENT THEN
  REWRITE_TAC[PATH_COMPONENT_IN; PATH_COMPONENT_SYM; PATH_COMPONENT_TRANS;
              PATH_COMPONENT_OF_SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[PATH_CONNECTED_IFF_PATH_COMPONENT]
   (MATCH_MP CONVEX_IMP_PATH_CONNECTED (SPEC_ALL CONVEX_BALL))) THEN
  ASM_MESON_TAC[CENTRE_IN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE; NOT_IN_EMPTY]);;

let PATH_CONNECTED_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ path_connected s ==> path_connected (IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_connected] THEN STRIP_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN
  ASM_REWRITE_TAC[path; path_image; pathstart; pathfinish] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:real^M->real^N) o (g:real^1->real^M)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM_REWRITE_TAC[o_DEF] THEN ASM SET_TAC[]]);;

let HOMEOMORPHIC_PATH_CONNECTEDNESS = prove
 (`!s t. s homeomorphic t ==> (path_connected s <=> path_connected t)`,
  REWRITE_TAC[homeomorphic; homeomorphism] THEN
  MESON_TAC[PATH_CONNECTED_CONTINUOUS_IMAGE]);;

let PATH_CONNECTED_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
     path_connected s /\ linear f ==> path_connected(IMAGE f s)`,
  SIMP_TAC[LINEAR_CONTINUOUS_ON; PATH_CONNECTED_CONTINUOUS_IMAGE]);;

let PATH_CONNECTED_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (path_connected (IMAGE f s) <=> path_connected s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE PATH_CONNECTED_LINEAR_IMAGE));;

add_linear_invariants [PATH_CONNECTED_LINEAR_IMAGE_EQ];;

let PATH_CONNECTED_EMPTY = prove
 (`path_connected {}`,
  REWRITE_TAC[path_connected; NOT_IN_EMPTY]);;

let PATH_CONNECTED_SING = prove
 (`!a:real^N. path_connected {a}`,
  GEN_TAC THEN REWRITE_TAC[path_connected; IN_SING] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `linepath(a:real^N,a)` THEN
  ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[SEGMENT_REFL; PATH_IMAGE_LINEPATH; SUBSET_REFL]);;

let PATH_CONNECTED_UNION = prove
 (`!s t. path_connected s /\ path_connected t /\ ~(s INTER t = {})
         ==> path_connected (s UNION t)`,
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
  REWRITE_TAC[IN_INTER; IN_UNION] THEN
  MESON_TAC[PATH_COMPONENT_OF_SUBSET; SUBSET_UNION; PATH_COMPONENT_TRANS]);;

let PATH_CONNECTED_TRANSLATION = prove
 (`!a s. path_connected s ==> path_connected (IMAGE (\x:real^N. a + x) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]);;

let PATH_CONNECTED_TRANSLATION_EQ = prove
 (`!a s. path_connected (IMAGE (\x:real^N. a + x) s) <=> path_connected s`,
  REWRITE_TAC[path_connected] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [PATH_CONNECTED_TRANSLATION_EQ];;

let PATH_CONNECTED_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        path_connected s /\ path_connected t
        ==> path_connected (s PCROSS t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS; path_connected] THEN DISCH_TAC THEN
  REWRITE_TAC[FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
  MAP_EVERY X_GEN_TAC [`x1:real^M`; `y1:real^N`; `x2:real^M`; `y2:real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(CONJUNCTS_THEN2
   (MP_TAC o SPECL [`x1:real^M`; `x2:real^M`])
   (MP_TAC o SPECL [`y1:real^N`; `y2:real^N`])) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:real^1->real^N` THEN STRIP_TAC THEN
  X_GEN_TAC `g:real^1->real^M` THEN STRIP_TAC THEN
  EXISTS_TAC `(\t. pastecart (x1:real^M) ((h:real^1->real^N) t)) ++
              (\t. pastecart ((g:real^1->real^M) t) (y2:real^N))` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish; path]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[path_image; FORALL_IN_IMAGE; SUBSET]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_JOIN_IMP THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
      REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
      ASM_REWRITE_TAC[pathstart; pathfinish]];
    MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
    ASM_SIMP_TAC[path_image; FORALL_IN_IMAGE; SUBSET; IN_ELIM_PASTECART_THM];
    REWRITE_TAC[PATHSTART_JOIN] THEN ASM_REWRITE_TAC[pathstart];
    REWRITE_TAC[PATHFINISH_JOIN] THEN ASM_REWRITE_TAC[pathfinish]]);;

let PATH_CONNECTED_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        path_connected(s PCROSS t) <=>
        s = {} \/ t = {} \/ path_connected s /\ path_connected t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; PATH_CONNECTED_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; PATH_CONNECTED_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[PATH_CONNECTED_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
                    `(s:real^M->bool) PCROSS (t:real^N->bool)`]
       PATH_CONNECTED_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
                   `(s:real^M->bool) PCROSS (t:real^N->bool)`]
       PATH_CONNECTED_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let PATH_CONNECTED_SCALING = prove
 (`!s:real^N->bool c.
        path_connected s ==> path_connected (IMAGE (\x. c % x) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let PATH_CONNECTED_NEGATIONS = prove
 (`!s:real^N->bool.
        path_connected s ==> path_connected (IMAGE (--) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let PATH_CONNECTED_SUMS = prove
 (`!s t:real^N->bool.
        path_connected s /\ path_connected t
        ==> path_connected {x + y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP PATH_CONNECTED_PCROSS) THEN
  DISCH_THEN(MP_TAC o ISPEC
   `\z. (fstcart z + sndcart z:real^N)` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      PATH_CONNECTED_CONTINUOUS_IMAGE)) THEN
  SIMP_TAC[CONTINUOUS_ON_ADD; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART;
           LINEAR_SNDCART; PCROSS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PASTECART] THEN
  REWRITE_TAC[PASTECART_INJ; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MESON_TAC[]);;

let IS_INTERVAL_PATH_CONNECTED_1 = prove
 (`!s:real^1->bool. is_interval s <=> path_connected s`,
  MESON_TAC[CONVEX_IMP_PATH_CONNECTED; PATH_CONNECTED_IMP_CONNECTED;
            IS_INTERVAL_CONNECTED_1; IS_INTERVAL_CONVEX_1]);;

(* ------------------------------------------------------------------------- *)
(* Bounds on components of a continuous image.                               *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_PATH_COMPONENTS = prove
 (`!f:real^M->real^N s.
        f continuous_on s
        ==> {path_component (IMAGE f s) y | y | y IN IMAGE f s}
            <=_c {path_component s x | x | x IN s}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LE_C] THEN
  SIMP_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC; FORALL_IN_IMAGE] THEN EXISTS_TAC
   `\c. path_component (IMAGE (f:real^M->real^N) s) (f(@x. x IN c))` THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN EXISTS_TAC `x:real^M` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_COMPONENT_EQ THEN
  REWRITE_TAC[IN] THEN ONCE_REWRITE_TAC[PATH_COMPONENT] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) (path_component s x)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; PATH_COMPONENT_SUBSET;
                  PATH_CONNECTED_PATH_COMPONENT];
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[PATH_COMPONENT_SUBSET];
    ALL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN] THEN
  ASM_MESON_TAC[PATH_COMPONENT_REFL_EQ]);;

let CARD_LE_CONNECTED_COMPONENTS = prove
 (`!f:real^M->real^N s.
        f continuous_on s
        ==> {connected_component (IMAGE f s) y | y | y IN IMAGE f s}
            <=_c {connected_component s x | x | x IN s}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LE_C] THEN
  SIMP_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC; FORALL_IN_IMAGE] THEN EXISTS_TAC
   `\c. connected_component (IMAGE (f:real^M->real^N) s) (f(@x. x IN c))` THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN EXISTS_TAC `x:real^M` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
  REWRITE_TAC[IN] THEN ONCE_REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) (connected_component s x)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; CONNECTED_COMPONENT_SUBSET;
                  CONNECTED_CONNECTED_COMPONENT];
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[CONNECTED_COMPONENT_SUBSET];
    ALL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_REFL_EQ]);;

let CARD_LE_COMPONENTS = prove
 (`!f:real^M->real^N s.
        f continuous_on s ==> components(IMAGE f s) <=_c components s`,
  REWRITE_TAC[components; CARD_LE_CONNECTED_COMPONENTS]);;

(* ------------------------------------------------------------------------- *)
(* More stuff about segments.                                                *)
(* ------------------------------------------------------------------------- *)

let SEGMENT_OPEN_SUBSET_CLOSED = prove
 (`!a b. segment(a,b) SUBSET segment[a,b]`,
  REWRITE_TAC[CONJUNCT2(SPEC_ALL segment)] THEN SET_TAC[]);;

let BOUNDED_SEGMENT = prove
 (`(!a b:real^N. bounded(segment[a,b])) /\
   (!a b:real^N. bounded(segment(a,b)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(MESON[BOUNDED_SUBSET]
   `bounded s /\ t SUBSET s ==> bounded s /\ bounded t`) THEN
  REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED] THEN
  MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
  SIMP_TAC[COMPACT_INSERT; COMPACT_EMPTY]);;

let SEGMENT_IMAGE_INTERVAL = prove
 (`(!a b. segment[a,b] =
          IMAGE (\u. (&1 - drop u) % a + drop u % b)
                (interval[vec 0,vec 1])) /\
   (!a b. ~(a = b)
          ==> segment(a,b) =
                IMAGE (\u. (&1 - drop u) % a + drop u % b)
                (interval(vec 0,vec 1)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTERVAL_1; IN_SEGMENT] THEN
  ASM_REWRITE_TAC[GSYM EXISTS_DROP; DROP_VEC] THEN MESON_TAC[]);;

let CLOSURE_SEGMENT = prove
 (`(!a b:real^N. closure(segment[a,b]) = segment[a,b]) /\
   (!a b:real^N. closure(segment(a,b)) = if a = b then {} else segment[a,b])`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[CLOSURE_EQ; COMPACT_IMP_CLOSED; SEGMENT_CONVEX_HULL;
                  COMPACT_CONVEX_HULL; COMPACT_INSERT; COMPACT_EMPTY];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; CLOSURE_EMPTY] THEN
  ASM_SIMP_TAC[SEGMENT_IMAGE_INTERVAL] THEN
  ASM_SIMP_TAC[CONV_RULE(RAND_CONV SYM_CONV) (SPEC_ALL CLOSURE_OPEN_INTERVAL);
               INTERVAL_EQ_EMPTY_1; DROP_VEC; REAL_ARITH `~(&1 <= &0)`] THEN
  SUBGOAL_THEN
   `(\u. (&1 - drop u) % a + drop u % (b:real^N)) =
    (\x. a + x) o (\u. drop u % (b - a))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o; CLOSURE_TRANSLATION] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CLOSURE_INJECTIVE_LINEAR_IMAGE THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL; VECTOR_SUB_EQ; DROP_EQ] THEN
  REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC);;

let CLOSED_SEGMENT = prove
 (`(!a b:real^N. closed(segment[a,b])) /\
   (!a b:real^N. closed(segment(a,b)) <=> a = b)`,
  REWRITE_TAC[GSYM CLOSURE_EQ; CLOSURE_SEGMENT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[SEGMENT_REFL] THEN
  MESON_TAC[ENDS_NOT_IN_SEGMENT; ENDS_IN_SEGMENT]);;

let COMPACT_SEGMENT = prove
 (`(!a b:real^N. compact(segment[a,b])) /\
   (!a b:real^N. compact(segment(a,b)) <=> a = b)`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_SEGMENT; BOUNDED_SEGMENT]);;

let AFFINE_HULL_SEGMENT = prove
 (`(!a b:real^N. affine hull (segment [a,b]) = affine hull {a,b}) /\
   (!a b:real^N. affine hull (segment(a,b)) =
                 if a = b then {} else affine hull {a,b})`,
  REWRITE_TAC[SEGMENT_CONVEX_HULL; AFFINE_HULL_CONVEX_HULL] THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM AFFINE_HULL_CLOSURE] THEN
  REWRITE_TAC[CLOSURE_SEGMENT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[AFFINE_HULL_EMPTY] THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL; AFFINE_HULL_CONVEX_HULL]);;

let SEGMENT_AS_BALL = prove
 (`(!a b. segment[a:real^N,b] =
         affine hull {a,b} INTER cball(inv(&2) % (a + b),norm(b - a) / &2)) /\
   (!a b. segment(a:real^N,b) =
         affine hull {a,b} INTER ball(inv(&2) % (a + b),norm(b - a) / &2))`,
  REPEAT STRIP_TAC THEN
  (ASM_CASES_TAC `b:real^N = a` THEN
   ASM_REWRITE_TAC[SEGMENT_REFL; VECTOR_SUB_REFL; NORM_0] THEN
   CONV_TAC REAL_RAT_REDUCE_CONV THEN
   REWRITE_TAC[BALL_TRIVIAL; CBALL_TRIVIAL] THENL
    [REWRITE_TAC[INTER_EMPTY; INSERT_AC] THEN
     REWRITE_TAC[VECTOR_ARITH `&1 / &2 % (a + a) = a`] THEN
     REWRITE_TAC[SET_RULE `a = b INTER a <=> a SUBSET b`; HULL_SUBSET];
     ASM_REWRITE_TAC[EXTENSION; IN_SEGMENT; IN_INTER; AFFINE_HULL_2] THEN
     X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
     REWRITE_TAC[REAL_ARITH `u + v:real = &1 <=> u = &1 - v`] THEN
     REWRITE_TAC[UNWIND_THM2] THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
     AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
     X_GEN_TAC `u:real` THEN REWRITE_TAC[] THEN
     ASM_CASES_TAC `y:real^N = (&1 - u) % a + u % b` THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_BALL; IN_CBALL; dist; VECTOR_ARITH
      `&1 / &2 % (a + b) - ((&1 - u) % a + u % b):real^N =
       (&1 / &2 - u) % (b - a)`] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_LT_MUL_EQ; REAL_LE_MUL_EQ; NORM_POS_LT;
     VECTOR_SUB_EQ; REAL_ARITH `a * n < n / &2 <=> &0 < n * (inv(&2) - a)`;
              REAL_ARITH `a * n <= n / &2 <=> &0 <= n * (inv(&2) - a)`] THEN
    REAL_ARITH_TAC]));;

let CONVEX_SEGMENT = prove
 (`(!a b. convex(segment[a,b])) /\ (!a b. convex(segment(a,b)))`,
  REWRITE_TAC[SEGMENT_AS_BALL] THEN
  SIMP_TAC[CONVEX_INTER; CONVEX_BALL; CONVEX_CBALL;
           AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL]);;

let RELATIVE_INTERIOR_SEGMENT = prove
 (`(!a b:real^N.
      relative_interior(segment[a,b]) = if a = b then {a} else segment(a,b)) /\
   (!a b:real^N. relative_interior(segment(a,b)) = segment(a,b))`,
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = b` THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; RELATIVE_INTERIOR_EMPTY] THEN
    REWRITE_TAC[RELATIVE_INTERIOR_EQ; OPEN_IN_OPEN] THEN
    ASM_REWRITE_TAC[AFFINE_HULL_SEGMENT] THEN
    EXISTS_TAC `ball(inv(&2) % (a + b):real^N,norm(b - a) / &2)` THEN
    REWRITE_TAC[OPEN_BALL; SEGMENT_AS_BALL];
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; RELATIVE_INTERIOR_SING] THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`] (CONJUNCT2 CLOSURE_SEGMENT)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR_CLOSURE THEN
    REWRITE_TAC[CONVEX_SEGMENT]]);;

let PATH_CONNECTED_SEGMENT = prove
 (`(!a b. path_connected(segment[a,b])) /\
   (!a b. path_connected(segment(a,b)))`,
  SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_SEGMENT]);;

let CONNECTED_SEGMENT = prove
 (`(!a b. connected(segment[a,b])) /\ (!a b. connected(segment(a,b)))`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_SEGMENT]);;

let CONVEX_SEMIOPEN_SEGMENT = prove
 (`(!a b:real^N. convex(segment[a,b] DELETE a)) /\
   (!a b:real^N. convex(segment[a,b] DELETE b))`,
  MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN
  CONJ_TAC THENL [MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:real^N = a` THEN
  ASM_SIMP_TAC[SEGMENT_REFL; SET_RULE `{a} DELETE a = {}`; CONVEX_EMPTY] THEN
  REWRITE_TAC[CONVEX_ALT; IN_DELETE] THEN
  SIMP_TAC[REWRITE_RULE[CONVEX_ALT] CONVEX_SEGMENT] THEN
  REWRITE_TAC[IN_SEGMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC;
                  GSYM VECTOR_ADD_ASSOC] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `x % a + y % b + z % a + w % b:real^N = a <=>
    (&1 - x - z) % a = (w + y) % b`] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_ARITH
   `&1 - (&1 - u) * (&1 - v) - u * (&1 - w) =
    u * w + (&1 - u) * v`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; REAL_ARITH
   `&0 <= x /\ &0 <= y ==> (x + y = &0 <=> x = &0 /\ y = &0)`] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_ARITH `&1 - x = &0 <=> x = &1`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `(u = &0 \/ w = &0) /\ (u = &1 \/ v = &0)
    ==> u = &0 /\ v = &0 \/ u = &1 /\ w = &0 \/ v = &0 /\ w = &0`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  ASM_MESON_TAC[VECTOR_ARITH `(&1 - &0) % a + &0 % b:real^N = a`]);;

let PATH_CONNECTED_SEMIOPEN_SEGMENT = prove
 (`(!a b:real^N. path_connected(segment[a,b] DELETE a)) /\
   (!a b:real^N. path_connected(segment[a,b] DELETE b))`,
  SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_SEMIOPEN_SEGMENT]);;

let CONNECTED_SEMIOPEN_SEGMENT = prove
 (`(!a b:real^N. connected(segment[a,b] DELETE a)) /\
   (!a b:real^N. connected(segment[a,b] DELETE b))`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_SEMIOPEN_SEGMENT]);;

let SEGMENT_EQ_EMPTY = prove
 (`(!a b:real^N. ~(segment[a,b] = {})) /\
   (!a b:real^N. segment(a,b) = {} <=> a = b)`,
  REWRITE_TAC[SEGMENT_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL] THEN
  ASM_MESON_TAC[NOT_IN_EMPTY; MIDPOINT_IN_SEGMENT]);;

let FINITE_SEGMENT = prove
 (`(!a b:real^N. FINITE(segment[a,b]) <=> a = b) /\
   (!a b:real^N. FINITE(segment(a,b)) <=> a = b)`,
  REWRITE_TAC[open_segment; SET_RULE `s DIFF {a,b} = s DELETE a DELETE b`] THEN
  REWRITE_TAC[FINITE_DELETE] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; FINITE_SING] THEN
  REWRITE_TAC[SEGMENT_IMAGE_INTERVAL] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) FINITE_IMAGE_INJ_EQ o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % a + u % b:real^N = (&1 - v) % a + v % b <=>
      (u - v) % (b - a) = vec 0`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; REAL_SUB_0; DROP_EQ];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FINITE_INTERVAL_1] THEN
    REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC]);;

let SEGMENT_EQ_SING = prove
 (`(!a b c:real^N. segment[a,b] = {c} <=> a = c /\ b = c) /\
   (!a b c:real^N. ~(segment(a,b) = {c}))`,
  REWRITE_TAC[SEGMENT_CONVEX_HULL; CONVEX_HULL_EQ_SING] THEN
  CONJ_TAC THENL [SET_TAC[]; REPEAT GEN_TAC] THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; NOT_INSERT_EMPTY] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] (CONJUNCT2 FINITE_SEGMENT)) THEN
  ASM_REWRITE_TAC[FINITE_SING]);;

let SUBSET_SEGMENT_OPEN_CLOSED = prove
 (`!a b c d:real^N.
        segment(a,b) SUBSET segment(c,d) <=>
        a = b \/ segment[a,b] SUBSET segment[c,d]`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ASM_CASES_TAC `a:real^N = b` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUBSET_CLOSURE) THEN
    ASM_REWRITE_TAC[CLOSURE_SEGMENT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[SUBSET_EMPTY; SEGMENT_EQ_EMPTY];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN
  REWRITE_TAC[SEGMENT_REFL; EMPTY_SUBSET] THEN
  ABBREV_TAC `m:real^N = d - c` THEN POP_ASSUM MP_TAC THEN
  GEOM_NORMALIZE_TAC `m:real^N` THEN
  SIMP_TAC[VECTOR_SUB_EQ; SEGMENT_REFL; SEGMENT_EQ_SING; SEGMENT_EQ_EMPTY;
           SET_RULE `s SUBSET {a} <=> s = {a} \/ s = {}`; SUBSET_REFL] THEN
  X_GEN_TAC `m:real^N` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN POP_ASSUM MP_TAC THEN
  GEOM_ORIGIN_TAC `c:real^N` THEN GEOM_BASIS_MULTIPLE_TAC 1 `d:real^N` THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  SIMP_TAC[VECTOR_SUB_RZERO; NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
  ASM_REWRITE_TAC[real_abs; REAL_MUL_RID] THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `collinear{vec 0:real^N,&1 % basis 1,x} /\
                collinear{vec 0:real^N,&1 % basis 1,y}`
  MP_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {a,c,b}`] THEN
    CONJ_TAC THEN MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN
    REWRITE_TAC[BETWEEN_IN_SEGMENT] THEN
    ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SIMP_TAC[COLLINEAR_LEMMA_ALT; BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL;
           VECTOR_ARITH `&1 % x:real^N = vec 0 <=> x = vec 0`] THEN
  REWRITE_TAC[IMP_CONJ; VECTOR_MUL_ASSOC; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real` THEN REWRITE_TAC[REAL_MUL_RID] THEN
  DISCH_THEN SUBST_ALL_TAC THEN X_GEN_TAC `b:real` THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  SUBST1_TAC(VECTOR_ARITH `vec 0:real^N = &0 % basis 1`) THEN
  ASM_SIMP_TAC[SEGMENT_SCALAR_MULTIPLE; VECTOR_MUL_RCANCEL; BASIS_NONZERO;
               DIMINDEX_GE_1; LE_REFL; SET_RULE
                `(!x y. x % v = y % v <=> x = y)
                 ==> ({x % v | P x} SUBSET {x % v | Q x} <=>
                      {x | P x} SUBSET {x | Q x})`] THEN
  REWRITE_TAC[REAL_ARITH `a <= x /\ x <= b \/ b <= x /\ x <= a <=>
                          min a b <= x /\ x <= max a b`;
              REAL_ARITH `a < x /\ x < b \/ b < x /\ x < a <=>
                          min a b < x /\ x < max a b`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `x:real` THEN
  FIRST_X_ASSUM(fun th -> MAP_EVERY (MP_TAC o C SPEC th)
        [`min (a:real) b`; `max (a:real) b`]) THEN
  REAL_ARITH_TAC);;

let SUBSET_SEGMENT = prove
 (`(!a b c d:real^N.
        segment[a,b] SUBSET segment[c,d] <=>
        a IN segment[c,d] /\ b IN segment[c,d]) /\
   (!a b c d:real^N.
        segment[a,b] SUBSET segment(c,d) <=>
        a IN segment(c,d) /\ b IN segment(c,d)) /\
   (!a b c d:real^N.
        segment(a,b) SUBSET segment[c,d] <=>
        a = b \/ a IN segment[c,d] /\ b IN segment[c,d]) /\
   (!a b c d:real^N.
        segment(a,b) SUBSET segment(c,d) <=>
        a = b \/ a IN segment[c,d] /\ b IN segment[c,d])`,
  MATCH_MP_TAC(TAUT `(a /\ b) /\ (a /\ b ==> c) ==> a /\ b /\ c`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SEGMENT_CONVEX_HULL] THEN
    SIMP_TAC[SUBSET_HULL; CONVEX_SEGMENT] THEN SET_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_SEGMENT_OPEN_CLOSED] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `closure(segment(a:real^N,b)) SUBSET segment[c,d]` THEN
    CONJ_TAC THENL [SIMP_TAC[CLOSURE_MINIMAL_EQ; CLOSED_SEGMENT]; ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_SEGMENT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[EMPTY_SUBSET]]);;

let INTERIOR_SEGMENT = prove
 (`(!a b:real^N. interior(segment[a,b]) =
                 if 2 <= dimindex(:N) then {} else segment(a,b)) /\
   (!a b:real^N. interior(segment(a,b)) =
                 if 2 <= dimindex(:N) then {} else segment(a,b))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `2 <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(SET_RULE `t SUBSET s /\ s = {} ==> s = {} /\ t = {}`) THEN
    SIMP_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET_INTERIOR] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC EMPTY_INTERIOR_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN FIRST_ASSUM
     (MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS)) THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC;
    ASM_CASES_TAC `a:real^N = b` THEN
    ASM_SIMP_TAC[SEGMENT_REFL; INTERIOR_EMPTY; EMPTY_INTERIOR_FINITE;
                 FINITE_SING] THEN
    SUBGOAL_THEN
     `affine hull (segment[a,b]) = (:real^N) /\
      affine hull (segment(a,b)) = (:real^N)`
     (fun th -> ASM_SIMP_TAC[th; GSYM RELATIVE_INTERIOR_INTERIOR;
                             RELATIVE_INTERIOR_SEGMENT]) THEN
    ASM_REWRITE_TAC[AFFINE_HULL_SEGMENT] THEN
    MATCH_MP_TAC AFFINE_INDEPENDENT_SPAN_GT THEN
    REWRITE_TAC[AFFINE_INDEPENDENT_2] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC]);;

let SEGMENT_EQ = prove
 (`(!a b c d:real^N.
        segment[a,b] = segment[c,d] <=> {a,b} = {c,d}) /\
   (!a b c d:real^N.
        ~(segment[a,b] = segment(c,d))) /\
   (!a b c d:real^N.
        ~(segment(a,b) = segment[c,d])) /\
   (!a b c d:real^N.
        segment(a,b) = segment(c,d) <=> a = b /\ c = d \/ {a,b} = {c,d})`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN(fun th -> MP_TAC th THEN
       MP_TAC(AP_TERM `\s:real^N->bool. s DIFF relative_interior s` th)) THEN
      REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[SEGMENT_REFL]) THEN
      SIMP_TAC[ENDS_IN_SEGMENT; open_segment; SET_RULE
        `a IN s /\ b IN s ==> s DIFF (s DIFF {a,b}) = {a,b}`] THEN
      ASM SET_TAC[SEGMENT_EQ_SING];
      SIMP_TAC[SEGMENT_CONVEX_HULL]];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `closed:(real^N->bool)->bool`) THEN
    REWRITE_TAC[CONJUNCT1 CLOSED_SEGMENT] THEN
    REWRITE_TAC[GSYM CLOSURE_EQ; CLOSURE_SEGMENT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM SET_TAC[SEGMENT_EQ_EMPTY];
      REWRITE_TAC[open_segment; ENDS_IN_SEGMENT; SET_RULE
       `s = s DIFF {a,b} <=> ~(a IN s) /\ ~(b IN s)`]];
    DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REPEAT GEN_TAC THEN ASM_CASES_TAC `c:real^N = d` THEN
    ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY; SEGMENT_REFL] THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONV_TAC(BINOP_CONV SYM_CONV)THEN
    ASM_CASES_TAC `a:real^N = b` THEN
    ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY; SEGMENT_REFL] THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_SEGMENT_OPEN_CLOSED] THEN
    ASM_REWRITE_TAC[SUBSET_ANTISYM_EQ]]);;

let COLLINEAR_SEGMENT = prove
 (`(!a b:real^N. collinear(segment[a,b])) /\
   (!a b:real^N. collinear(segment(a,b)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; CONVEX_HULL_SUBSET_AFFINE_HULL];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COLLINEAR_SUBSET) THEN
    REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED]]);;

let INTER_SEGMENT = prove
 (`!a b c:real^N.
        b IN segment[a,c] \/ ~collinear{a,b,c}
        ==> segment[a,b] INTER segment[b,c] = {b}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c:real^N = a` THENL
   [ASM_SIMP_TAC[SEGMENT_REFL; IN_SING; INTER_IDEMPOT; INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`{a:real^N,c}`; `b:real^N`; `{a:real^N}`; `{c:real^N}`]
        CONVEX_HULL_EXCHANGE_INTER) THEN
    ASM_REWRITE_TAC[AFFINE_INDEPENDENT_2] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[INSERT_AC]] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[SET_RULE `~(a = c) ==> {a} INTER {c} = {}`] THEN
    REWRITE_TAC[CONVEX_HULL_SING];
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `~(s INTER t = {b})
      ==> b IN s /\ b IN t
          ==> ?a. ~(a = b) /\ a IN s /\ b IN s /\ a IN t /\ b IN t`)) THEN
    ANTS_TAC THENL [REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
    REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:real^N` THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
    MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `d:real^N` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SIMP_TAC[INSERT_AC]]);;

let SUBSET_CONTINUOUS_IMAGE_SEGMENT_1 = prove
 (`!f:real^N->real^1 a b.
        f continuous_on segment[a,b]
        ==> segment[f a,f b] SUBSET IMAGE f (segment[a,b])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONNECTED_CONTINUOUS_IMAGE)) THEN
  REWRITE_TAC[CONNECTED_SEGMENT] THEN
  REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_CONVEX_1] THEN
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
  MESON_TAC[IN_IMAGE; ENDS_IN_SEGMENT]);;

let CONTINUOUS_INJECTIVE_IMAGE_SEGMENT_1 = prove
 (`!f:real^N->real^1 a b.
        f continuous_on segment[a,b] /\
        (!x y. x IN segment[a,b] /\ y IN segment[a,b] /\ f x = f y ==> x = y)
        ==> IMAGE f (segment[a,b]) = segment[f a,f b]`,
  let lemma = prove
   (`!a b c:real^1.
      ~(a = b) /\ ~(a IN segment(c,b)) /\ ~(b IN segment(a,c))
      ==> c IN segment[a,b]`,
    REWRITE_TAC[FORALL_LIFT; SEGMENT_1; LIFT_DROP] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[SEGMENT_1; LIFT_EQ] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP]) THEN
    ASM_REAL_ARITH_TAC) in
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real^1->real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^1`; `g:real^1->real^N`;
                 `segment[a:real^N,b]`]
        CONTINUOUS_ON_INVERSE) THEN
  ASM_REWRITE_TAC[COMPACT_SEGMENT] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET_CONTINUOUS_IMAGE_SEGMENT_1]; DISCH_TAC] THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL] THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `c:real^N` THEN
  DISCH_TAC THEN MATCH_MP_TAC lemma THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_SEGMENT]; DISCH_TAC] THEN
  ONCE_REWRITE_TAC[segment] THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^1`; `c:real^N`; `b:real^N`]
        SUBSET_CONTINUOUS_IMAGE_SEGMENT_1) THEN
    SUBGOAL_THEN `segment[c:real^N,b] SUBSET segment[a,b]` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; REWRITE_TAC[SUBSET]] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^N->real^1) a`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `d:real^N` THEN ASM_CASES_TAC `d:real^N = a` THENL
     [ASM_MESON_TAC[BETWEEN_ANTISYM; BETWEEN_IN_SEGMENT];
      ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]];
    MP_TAC(ISPECL [`f:real^N->real^1`; `a:real^N`; `c:real^N`]
        SUBSET_CONTINUOUS_IMAGE_SEGMENT_1) THEN
    SUBGOAL_THEN `segment[a:real^N,c] SUBSET segment[a,b]` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; REWRITE_TAC[SUBSET]] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^N->real^1) b`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `d:real^N` THEN ASM_CASES_TAC `d:real^N = b` THENL
     [ASM_MESON_TAC[BETWEEN_ANTISYM; BETWEEN_IN_SEGMENT; BETWEEN_SYM];
      ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]]]);;

let CONTINUOUS_INJECTIVE_IMAGE_OPEN_SEGMENT_1 = prove
 (`!f:real^N->real^1 a b.
        f continuous_on segment[a,b] /\
        (!x y. x IN segment[a,b] /\ y IN segment[a,b] /\ f x = f y ==> x = y)
        ==> IMAGE f (segment(a,b)) = segment(f a,f b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[segment] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_INJECTIVE_IMAGE_SEGMENT_1) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`(f:real^N->real^1) a`; `(f:real^1->real^1) b`]
    ENDS_IN_SEGMENT) THEN
  ASM SET_TAC[]);;

let CONTINUOUS_IVT_LOCAL_EXTREMUM = prove
 (`!f:real^N->real^1 a b.
        f continuous_on segment[a,b] /\ ~(a = b) /\ f(a) = f(b)
         ==> ?z. z IN segment(a,b) /\
                 ((!w. w IN segment[a,b] ==> drop(f w) <= drop(f z)) \/
                  (!w. w IN segment[a,b] ==> drop(f z) <= drop(f w)))`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (MP_TAC o ISPECL
            [`drop o (f:real^N->real^1)`; `segment[a:real^N,b]`])
            [CONTINUOUS_ATTAINS_SUP; CONTINUOUS_ATTAINS_INF] THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
  REWRITE_TAC[COMPACT_SEGMENT; SEGMENT_EQ_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(d:real^N) IN segment(a,b)` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(c:real^N) IN segment(a,b)` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `midpoint(a:real^N,b)` THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT]; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CONJUNCT2 segment]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [segment])) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[REAL_LE_ANTISYM; DROP_EQ]);;

let FRONTIER_UNIONS_SUBSET_CLOSURE = prove
 (`!f:(real^N->bool)->bool.
        frontier(UNIONS f) SUBSET closure(UNIONS {frontier t | t IN f})`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [frontier] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; CLOSURE_APPROACHABLE] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[EXISTS_IN_UNIONS; EXISTS_IN_GSPEC; RIGHT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN
  ASM_CASES_TAC `(t:real^N->bool) IN f` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:real^N) IN t` THENL
   [DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[frontier; DIST_REFL; IN_DIFF] THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    SPEC_TAC(`x:real^N`,`z:real^N`) THEN
    REWRITE_TAC[CONTRAPOS_THM; GSYM SUBSET] THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`segment[x:real^N,y]`; `t:real^N->bool`]
        CONNECTED_INTER_FRONTIER) THEN
    SIMP_TAC[CONNECTED_SEGMENT; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
    ASM_MESON_TAC[DIST_IN_CLOSED_SEGMENT; DIST_SYM; REAL_LET_TRANS]]);;

let FRONTIER_UNIONS_SUBSET = prove
 (`!f:(real^N->bool)->bool.
        FINITE f ==> frontier(UNIONS f) SUBSET UNIONS {frontier t | t IN f}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[]
   `s SUBSET closure t /\ closure t = t ==> s SUBSET t`) THEN
  REWRITE_TAC[FRONTIER_UNIONS_SUBSET_CLOSURE; CLOSURE_EQ] THEN
  MATCH_MP_TAC CLOSED_UNIONS THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE; FRONTIER_CLOSED]);;

let CLOSURE_CONVEX_INTER_AFFINE = prove
 (`!s t:real^N->bool.
      convex s /\ affine t /\ ~(relative_interior s INTER t = {})
      ==> closure(s INTER t) = closure(s) INTER t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[];
    TRANS_TAC SUBSET_TRANS `closure t:real^N->bool` THEN
    SIMP_TAC[SUBSET_CLOSURE; INTER_SUBSET] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; CLOSED_AFFINE; SUBSET_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^N` MP_TAC o
        GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[AFFINE_EQ_SUBSPACE] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(REWRITE_RULE[SUBSET]
    RELATIVE_INTERIOR_SUBSET)) THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
  STRIP_TAC THEN ASM_CASES_TAC `x:real^N = vec 0` THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `x IN closure(segment(vec 0:real^N,x))` MP_TAC THENL
   [ASM_REWRITE_TAC[CLOSURE_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> x IN t`) THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN REWRITE_TAC[SUBSET_INTER] THEN
  CONJ_TAC THENL
   [TRANS_TAC SUBSET_TRANS `relative_interior s:real^N->bool` THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN
    MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SUBSET; IN_SEGMENT; VECTOR_MUL_RZERO; VECTOR_ADD_LID;
                 SUBSPACE_MUL; LEFT_IMP_EXISTS_THM]]);;

let RELATIVE_FRONTIER_CONVEX_INTER_AFFINE = prove
 (`!s t:real^N->bool.
        convex s /\ affine t /\ ~(interior s INTER t = {})
        ==> relative_frontier(s INTER t) = frontier s INTER t`,
  SIMP_TAC[relative_frontier; RELATIVE_INTERIOR_CONVEX_INTER_AFFINE;
           frontier] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(relative_interior s INTER t:real^N->bool = {})`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[CLOSURE_CONVEX_INTER_AFFINE] THEN SET_TAC[]]);;

let CONNECTED_COMPONENT_1_GEN = prove
 (`!s a b:real^N.
        dimindex(:N) = 1
        ==> (connected_component s a b <=> segment[a,b] SUBSET s)`,
  SIMP_TAC[connected_component; GSYM CONNECTED_CONVEX_1_GEN] THEN
 MESON_TAC[CONVEX_CONTAINS_SEGMENT; SUBSET; CONVEX_SEGMENT;
            ENDS_IN_SEGMENT]);;

let CONNECTED_COMPONENT_1 = prove
 (`!s a b:real^1. connected_component s a b <=> segment[a,b] SUBSET s`,
  SIMP_TAC[CONNECTED_COMPONENT_1_GEN; DIMINDEX_1]);;

(* ------------------------------------------------------------------------- *)
(* An injective function into R is a homeomorphism and so an open map.       *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_INTO_1D_EQ_HOMEOMORPHISM = prove
 (`!f:real^N->real^1 s.
        f continuous_on s /\ path_connected s
        ==>  ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
              ?g. homeomorphism (s,IMAGE f s) (f,g))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE];
    REWRITE_TAC[homeomorphism] THEN MESON_TAC[]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^1->real^N` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[homeomorphism; FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `is_interval (IMAGE (f:real^N->real^1) s)` ASSUME_TAC THENL
   [REWRITE_TAC[IS_INTERVAL_PATH_CONNECTED_1] THEN
    ASM_MESON_TAC[PATH_CONNECTED_CONTINUOUS_IMAGE];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_on; IMP_CONJ; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ABBREV_TAC `y = (f:real^N->real^1) x` THEN
  ABBREV_TAC `t = IMAGE (f:real^N->real^1) s` THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?a b d. a IN s /\ b IN s /\ &0 < d /\
            ball(y,d) INTER t SUBSET segment[(f:real^N->real^1) a,f b]`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^1->bool`; `y:real^1`]
        INTERVAL_CONTAINS_COMPACT_NEIGHBOURHOOD) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[INTERVAL_SUBSET_IS_INTERVAL] THEN
    REWRITE_TAC[SET_RULE
     `P /\ y IN s /\ (s = {} \/ a IN t /\ b IN t) /\ R <=>
      a IN t /\ b IN t /\ P /\ y IN s /\ R`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[SEGMENT_1; IN_INTERVAL_1] THEN
    MESON_TAC[REAL_LE_TRANS];
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
   DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^N` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
    `(g:real^1->real^N) continuous_on segment[(f:real^N->real^1) a,f b]`
   MP_TAC THENL
    [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
     EXISTS_TAC `IMAGE (f:real^N->real^1) (path_image p)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC CONTINUOUS_ON_INVERSE THEN
       ASM_SIMP_TAC[COMPACT_PATH_IMAGE] THEN CONJ_TAC THENL
        [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
       SUBGOAL_THEN `convex(IMAGE (f:real^N->real^1) (path_image p))`
       MP_TAC THENL
        [REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1; IS_INTERVAL_CONNECTED_1] THEN
         MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
         ASM_SIMP_TAC[CONNECTED_PATH_IMAGE] THEN
         ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
         REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
         CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
         ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]]];
     REWRITE_TAC[continuous_on] THEN
     DISCH_THEN(MP_TAC o SPEC `y:real^1`) THEN ANTS_TAC THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
       ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN ASM SET_TAC[];
       ALL_TAC] THEN
     DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `min d k` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
     X_GEN_TAC `x':real^N` THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
     ASM_REWRITE_TAC[IN_INTER; IN_BALL] THEN
     ONCE_REWRITE_TAC[DIST_SYM] THEN ASM SET_TAC[]]]);;

let INJECTIVE_INTO_1D_IMP_OPEN_MAP = prove
 (`!f:real^N->real^1 s t.
        f continuous_on s /\ path_connected s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        open_in (subtopology euclidean s) t
        ==> open_in (subtopology euclidean (IMAGE f s)) (IMAGE f t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
  ASM_MESON_TAC[INJECTIVE_INTO_1D_EQ_HOMEOMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* Injective function on an interval is strictly increasing or decreasing.   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_INJECTIVE_IFF_MONOTONIC = prove
 (`!f:real^1->real^1 s.
        f continuous_on s /\ is_interval s
        ==> ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
             (!x y. x IN s /\ y IN s /\ drop x < drop y
                    ==> drop(f x) < drop(f y)) \/
             (!x y. x IN s /\ y IN s /\ drop x < drop y
                    ==> drop(f y) < drop(f x)))`,
  let lemma = prove
   (`!s f:real^1->real^1.
        f continuous_on s /\ is_interval s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> !u v w. u IN s /\ v IN s /\ w IN s /\
                    drop u < drop v /\ drop v < drop w /\
                    drop(f u) <= drop(f v) /\ drop(f w) <= drop(f v) ==> F`,
    REWRITE_TAC[IS_INTERVAL_CONVEX_1; CONVEX_CONTAINS_SEGMENT] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `u:real^1`; `w:real^1`]
        CONTINUOUS_INJECTIVE_IMAGE_SEGMENT_1) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^1->real^1) v`) THEN
    MATCH_MP_TAC(TAUT `p /\ ~q ==> (p <=> q) ==> F`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[SEGMENT_1] THEN
      COND_CASES_TAC THENL
       [ASM_SIMP_TAC[IN_INTERVAL_1; REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1] THEN DISCH_TAC THENL
       [SUBGOAL_THEN `drop(f(w:real^1)) = drop(f v)` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[DROP_EQ; REAL_LT_REFL]];
        SUBGOAL_THEN `drop(f(u:real^1)) = drop(f v)` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[DROP_EQ; REAL_LT_REFL]]]])
  and tac s1 s2 =
   let [l1;l2] = map (map (fun x -> mk_var(x,`:real^1`)) o explode) [s1;s2] in
   REPEAT(FIRST_X_ASSUM(fun th ->
     MP_TAC(ISPECL l1 th) THEN MP_TAC(ISPECL l2 th))) THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC in
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM DROP_EQ] THEN
    MESON_TAC[REAL_LT_TOTAL; REAL_LT_REFL]] THEN
  DISCH_TAC THEN MATCH_MP_TAC(MESON[]
   `(!a b c d. ~(~P a b /\ ~Q c d)) ==> (!x y. P x y) \/ (!x y. Q x y)`) THEN
  MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`; `c:real^1`; `d:real^1`] THEN
  REWRITE_TAC[NOT_IMP; REAL_NOT_LT] THEN STRIP_TAC THEN
  REPEAT
   (FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_LE_LT]) THEN
    REWRITE_TAC[DROP_EQ] THEN STRIP_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[REAL_LT_REFL]]) THEN
  MP_TAC(ISPEC `s:real^1->bool` lemma) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
   MP_TAC(SPEC `(--) o (f:real^1->real^1)` th) THEN
   MP_TAC(SPEC `f:real^1->real^1` th)) THEN
  ASM_REWRITE_TAC[o_THM; VECTOR_ARITH `--x:real^N = --y <=> x = y`] THEN
  DISCH_TAC THEN REWRITE_TAC[NOT_IMP; DROP_NEG; REAL_LE_NEG2] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_COMPOSE;LINEAR_CONTINUOUS_ON; LINEAR_NEGATION];
    DISCH_TAC] THEN
  ASM_CASES_TAC `drop d <= drop a` THENL [tac "cab" "cdb"; ALL_TAC] THEN
  ASM_CASES_TAC `drop b <= drop c` THENL [tac "abd" "acd"; ALL_TAC] THEN
  ASM_CASES_TAC `c:real^1 = a /\ d:real^1 = b` THENL
   [ASM_MESON_TAC[REAL_LT_ANTISYM]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
   `~(c = a /\ d = b)
    ==> (c = a ==> d = b) /\ (d = b ==> c = a) /\
        (~(c = a) /\ ~(d = b) ==> F) ==> F`)) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN SIMP_TAC[GSYM DROP_EQ] THEN tac "adb" "abd";
    DISCH_THEN SUBST_ALL_TAC THEN SIMP_TAC[GSYM DROP_EQ] THEN tac "acb" "cab";
    REWRITE_TAC[GSYM DROP_EQ] THEN STRIP_TAC] THEN
  ASM_CASES_TAC `drop a <= drop c` THENL [tac "acb" "acd"; tac "cab" "cad"]);;

(* ------------------------------------------------------------------------- *)
(* Some uncountability results for relevant sets.                            *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_SEGMENT = prove
 (`(!a b:real^N. ~(a = b) ==> segment[a,b] =_c (:real)) /\
   (!a b:real^N. ~(a = b) ==> segment(a,b) =_c (:real))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SEGMENT_IMAGE_INTERVAL] THENL
   [TRANS_TAC CARD_EQ_TRANS `interval[vec 0:real^1,vec 1]`;
    TRANS_TAC CARD_EQ_TRANS `interval(vec 0:real^1,vec 1)`] THEN
  SIMP_TAC[CARD_EQ_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
  MATCH_MP_TAC CARD_EQ_IMAGE THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; VECTOR_ARITH
   `(&1 - x) % a + x % b:real^N = (&1 - y) % a + y % b <=>
    (x - y) % (a - b) = vec 0`] THEN
  SIMP_TAC[REAL_SUB_0; DROP_EQ]);;

let UNCOUNTABLE_SEGMENT = prove
 (`(!a b:real^N. ~(a = b) ==> ~COUNTABLE(segment[a,b])) /\
   (!a b:real^N. ~(a = b) ==> ~COUNTABLE(segment(a,b)))`,
  SIMP_TAC[CARD_EQ_REAL_IMP_UNCOUNTABLE; CARD_EQ_SEGMENT]);;

let CARD_EQ_PATH_CONNECTED = prove
 (`!s a b:real^N.
        path_connected s /\ a IN s /\ b IN s /\ ~(a = b) ==> s =_c (:real)`,
  MESON_TAC[CARD_EQ_CONNECTED; PATH_CONNECTED_IMP_CONNECTED]);;

let UNCOUNTABLE_PATH_CONNECTED = prove
 (`!s a b:real^N.
        path_connected s /\ a IN s /\ b IN s /\ ~(a = b) ==> ~COUNTABLE s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CARD_EQ_REAL_IMP_UNCOUNTABLE THEN
  MATCH_MP_TAC CARD_EQ_PATH_CONNECTED THEN
  ASM_MESON_TAC[]);;

let CARD_EQ_CONVEX = prove
 (`!s a b:real^N.
        convex s /\ a IN s /\ b IN s /\ ~(a = b) ==> s =_c (:real)`,
  MESON_TAC[CARD_EQ_PATH_CONNECTED; CONVEX_IMP_PATH_CONNECTED]);;

let UNCOUNTABLE_CONVEX = prove
 (`!s a b:real^N.
        convex s /\ a IN s /\ b IN s /\ ~(a = b) ==> ~COUNTABLE s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CARD_EQ_REAL_IMP_UNCOUNTABLE THEN
  MATCH_MP_TAC CARD_EQ_CONVEX THEN
  ASM_MESON_TAC[]);;

let CARD_EQ_NONEMPTY_INTERIOR = prove
 (`!s:real^N->bool. ~(interior s = {}) ==> s =_c (:real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
    SIMP_TAC[CARD_LE_UNIV; CARD_EQ_IMP_LE; CARD_EQ_EUCLIDEAN];
    TRANS_TAC CARD_LE_TRANS `interior(s:real^N->bool)` THEN
    SIMP_TAC[CARD_LE_SUBSET; INTERIOR_SUBSET] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[CARD_EQ_SYM] CARD_EQ_IMP_LE) THEN
    MATCH_MP_TAC CARD_EQ_OPEN THEN ASM_REWRITE_TAC[OPEN_INTERIOR]]);;

let UNCOUNTABLE_NONEMPTY_INTERIOR = prove
 (`!s:real^N->bool. ~(interior s = {}) ==> ~(COUNTABLE s)`,
  SIMP_TAC[CARD_EQ_NONEMPTY_INTERIOR; CARD_EQ_REAL_IMP_UNCOUNTABLE]);;

let COUNTABLE_EMPTY_INTERIOR = prove
 (`!s:real^N->bool. COUNTABLE s ==> interior s = {}`,
  MESON_TAC[UNCOUNTABLE_NONEMPTY_INTERIOR]);;

let FINITE_EMPTY_INTERIOR = prove
 (`!s:real^N->bool. FINITE s ==> interior s = {}`,
  SIMP_TAC[COUNTABLE_EMPTY_INTERIOR; FINITE_IMP_COUNTABLE]);;

let [CONNECTED_FINITE_IFF_SING;
     CONNECTED_FINITE_IFF_COUNTABLE;
     CONNECTED_INFINITE_IFF_CARD_EQ] = (CONJUNCTS o prove)
 (`(!s:real^N->bool. connected s ==> (FINITE s <=> s = {} \/ ?a. s = {a})) /\
   (!s:real^N->bool. connected s ==> (FINITE s <=> COUNTABLE s)) /\
   (!s:real^N->bool. connected s ==> (INFINITE s <=> s =_c (:real)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  ASM_CASES_TAC `connected(s:real^N->bool)` THEN
  ASM_REWRITE_TAC[INFINITE] THEN MATCH_MP_TAC(TAUT
   `(f ==> c) /\ (r ==> ~c) /\ (s ==> f) /\ (~s ==> r)
    ==> (f <=> s) /\ (f <=> c) /\ (~f <=> r)`) THEN
  REWRITE_TAC[FINITE_IMP_COUNTABLE] THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_EQ_REAL_IMP_UNCOUNTABLE; FINITE_INSERT; FINITE_EMPTY] THEN
  MATCH_MP_TAC CARD_EQ_CONNECTED THEN ASM SET_TAC[]);;

let CLOSED_AS_FRONTIER_OF_SUBSET = prove
 (`!s:real^N->bool. closed s <=> ?t. t SUBSET s /\ s = frontier t`,
  GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[FRONTIER_CLOSED]] THEN
  DISCH_TAC THEN MP_TAC(ISPEC `s:real^N->bool` SEPARABLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN
  SIMP_TAC[frontier] THEN STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `s SUBSET c /\ c SUBSET s /\ i = {} ==> s = c DIFF i`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_CLOSURE; CLOSURE_CLOSED];
    ASM_MESON_TAC[UNCOUNTABLE_NONEMPTY_INTERIOR]]);;

let CLOSED_AS_FRONTIER = prove
 (`!s:real^N->bool. closed s <=> ?t. s = frontier t`,
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[CLOSED_AS_FRONTIER_OF_SUBSET]; MESON_TAC[FRONTIER_CLOSED]]);;

let CARD_EQ_CLOSED = prove
 (`!s:real^N->bool. closed s ==> s <=_c (:num) \/ s =_c (:real)`,
  let slemma = prove
   (`!s:real^N->bool.
          ~COUNTABLE s
          ==> ?x y. ~(x = y) /\ x IN s /\ y IN s /\
                    x condensation_point_of s /\
                    y condensation_point_of s`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CARD_EQ_CONDENSATION_POINTS_IN_SET) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_INFINITE_CONG) THEN
    REWRITE_TAC[INFINITE] THEN
    MATCH_MP_TAC(TAUT `q /\ (p ==> s) ==> (p <=> q) ==> s`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_IMP_COUNTABLE]; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`2`; `{x:real^N | x IN s /\ x condensation_point_of s}`]
          CHOOSE_SUBSET_STRONG) THEN
    ASM_REWRITE_TAC[HAS_SIZE_CONV `s HAS_SIZE 2`; RIGHT_AND_EXISTS_THM] THEN
    DISCH_THEN(CHOOSE_THEN MP_TAC) THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FORALL_IN_INSERT; NOT_IN_EMPTY]) THEN
    ASM_REWRITE_TAC[]) in
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM COUNTABLE_ALT] THEN
  ASM_CASES_TAC `COUNTABLE(s:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n t:real^N->bool.
        closed t /\ ~COUNTABLE t
        ==> ?l r. (compact l /\ ~COUNTABLE l) /\ (compact r /\ ~COUNTABLE r) /\
                  l INTER r = {} /\ l SUBSET t /\ r SUBSET t /\
                  diameter l <= inv(&2 pow n) /\
                  diameter r <= inv(&2 pow n)`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o MATCH_MP slemma)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`t INTER cball(a:real^N,min (inv(&2 pow (SUC n))) (dist(a,b) / &3))`;
     `t INTER cball(b:real^N,min (inv(&2 pow (SUC n))) (dist(a,b) / &3))`] THEN
    ASM_SIMP_TAC[CLOSED_INTER_COMPACT; COMPACT_CBALL] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I
       [CONDENSATION_POINT_INFINITE_CBALL]) THEN
      REWRITE_TAC[REAL_LT_MIN; REAL_LT_INV_EQ; REAL_LT_POW2] THEN
      UNDISCH_TAC `~(a:real^N = b)` THEN CONV_TAC NORM_ARITH;
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I
       [CONDENSATION_POINT_INFINITE_CBALL]) THEN
      REWRITE_TAC[REAL_LT_MIN; REAL_LT_INV_EQ; REAL_LT_POW2] THEN
      UNDISCH_TAC `~(a:real^N = b)` THEN CONV_TAC NORM_ARITH;
      MATCH_MP_TAC(SET_RULE
       `(!x. ~(x IN t /\ x IN u)) ==> (s INTER t) INTER (s INTER u) = {}`) THEN
      REWRITE_TAC[IN_CBALL; REAL_LE_MIN] THEN
      UNDISCH_TAC `~(a:real^N = b)` THEN CONV_TAC NORM_ARITH;
      SET_TAC[];
      SET_TAC[];
      MATCH_MP_TAC DIAMETER_LE THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LT_POW2] THEN
      REWRITE_TAC[IN_INTER; IN_CBALL; REAL_LE_MIN; real_pow; REAL_INV_MUL] THEN
      CONV_TAC NORM_ARITH;
      MATCH_MP_TAC DIAMETER_LE THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LT_POW2] THEN
      REWRITE_TAC[IN_INTER; IN_CBALL; REAL_LE_MIN; real_pow; REAL_INV_MUL] THEN
      CONV_TAC NORM_ARITH];
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`l:num->(real^N->bool)->(real^N->bool)`;
      `r:num->(real^N->bool)->(real^N->bool)`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `!b. ?x:num->real^N->bool.
          (x 0 = s) /\ (!n. x(SUC n) = if b(n) then r n (x n) else l n (x n))`
    MP_TAC THENL
     [GEN_TAC THEN
      W(ACCEPT_TAC o prove_recursive_functions_exist num_RECURSION o
        snd o dest_exists o snd);
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM]] THEN
    X_GEN_TAC `x:(num->bool)->num->real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
     [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
      SIMP_TAC[CARD_LE_UNIV; CARD_EQ_EUCLIDEAN; CARD_EQ_IMP_LE];
      TRANS_TAC CARD_LE_TRANS `(:num->bool)` THEN
      SIMP_TAC[CARD_EQ_REAL; CARD_EQ_IMP_LE]] THEN
    REWRITE_TAC[le_c; IN_UNIV] THEN
    SUBGOAL_THEN
     `!b n. closed((x:(num->bool)->num->real^N->bool) b n) /\
            ~COUNTABLE(x b n)`
    MP_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
    MP_TAC(GEN `b:num->bool` (ISPEC `(x:(num->bool)->num->real^N->bool) b`
          DECREASING_CLOSED_NEST_SING)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP MONO_FORALL) THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[FORALL_AND_THM] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[COUNTABLE_EMPTY];
        GEN_TAC THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
        REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[];
        MAP_EVERY X_GEN_TAC [`b:num->bool`; `e:real`] THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
        ASM_REWRITE_TAC[REAL_POW_INV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
        EXISTS_TAC `SUC m` THEN ASM_SIMP_TAC[] THEN
        REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP
         (REWRITE_RULE[TAUT `p /\ q /\ r ==> s <=> q /\ r ==> p ==> s`]
          DIAMETER_BOUNDED_BOUND)) THEN
        ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
        UNDISCH_TAC `inv(&2 pow m) < e` THEN MATCH_MP_TAC(NORM_ARITH
         `d <= i ==> i < e ==> norm(x - y) <= d ==> dist(x:real^N,y) < e`) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `f:(num->bool)->real^N` THEN STRIP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `b:num->bool` THEN
      REWRITE_TAC[SET_RULE `x IN s <=> {x} SUBSET s`] THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
      REWRITE_TAC[SUBSET; INTERS_GSPEC; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      SIMP_TAC[FORALL_UNWIND_THM2] THEN GEN_TAC THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`b:num->bool`; `c:num->bool`] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [FUN_EQ_THM] THEN
      REWRITE_TAC[NOT_FORALL_THM] THEN ONCE_REWRITE_TAC[num_WOP] THEN
      SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC(SET_RULE
       `!f g. INTERS f = {a} /\ INTERS g = {b} /\
              (?s t. s IN f /\ t IN g /\ s INTER t = {})
              ==> ~(a = b)`) THEN
      EXISTS_TAC `{t | ?n. t = (x:(num->bool)->num->real^N->bool) b n}` THEN
      EXISTS_TAC `{t | ?n. t = (x:(num->bool)->num->real^N->bool) c n}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `(x:(num->bool)->num->real^N->bool) b (SUC k)` THEN
      EXISTS_TAC `(x:(num->bool)->num->real^N->bool) c (SUC k)` THEN
      REPEAT(CONJ_TAC THENL [MESON_TAC[]; ALL_TAC]) THEN ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN
       `!i. i <= k ==> (x:(num->bool)->num->real^N->bool) b i = x c i`
      MP_TAC THENL
       [INDUCT_TAC THEN ASM_SIMP_TAC[LE_SUC_LT; LT_IMP_LE];
        DISCH_THEN(MP_TAC o SPEC `k:num`)] THEN
      REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [TAUT `~(p <=> q) <=> (q <=> ~p)`]) THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_MESON_TAC[INTER_COMM]]]);;

let CONDENSATION_POINTS_EQ_EMPTY,CARD_EQ_CONDENSATION_POINTS =
 (CONJ_PAIR o prove)
 (`(!s:real^N->bool.
        {x | x condensation_point_of s} = {} <=> COUNTABLE s) /\
   (!s:real^N->bool.
        {x | x condensation_point_of s} =_c (:real) <=> ~(COUNTABLE s))`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(r ==> p) /\ (~r ==> q) /\ (p ==> ~q)
    ==> (p <=> r) /\ (q <=> ~r)`) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    REWRITE_TAC[condensation_point_of] THEN
    ASM_MESON_TAC[COUNTABLE_SUBSET; INTER_SUBSET; IN_UNIV; OPEN_UNIV];
    DISCH_TAC THEN MATCH_MP_TAC(REWRITE_RULE
     [TAUT `p ==> q \/ r <=> p /\ ~q ==> r`] CARD_EQ_CLOSED) THEN
    REWRITE_TAC[CLOSED_CONDENSATION_POINTS; GSYM COUNTABLE_ALT] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CARD_EQ_CONDENSATION_POINTS_IN_SET) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_COUNTABLE_CONG) THEN
    ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_FINITE_CONG) THEN
    REWRITE_TAC[FINITE_EMPTY; GSYM INFINITE; real_INFINITE]]);;

let UNCOUNTABLE_HAS_CONDENSATION_POINT = prove
 (`!s:real^N->bool. ~COUNTABLE s ==> ?x. x condensation_point_of s`,
  REWRITE_TAC[GSYM CONDENSATION_POINTS_EQ_EMPTY] THEN SET_TAC[]);;

let CARD_EQ_PERFECT_SET = prove
 (`!s:real^N->bool.
        closed s /\ (!x. x IN s ==> x limit_point_of s) /\ ~(s = {})
        ==> s =_c (:real)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP CARD_EQ_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM COUNTABLE; GSYM ge_c]) THEN
  MP_TAC(ISPECL [`IMAGE (\x:real^N. s DELETE x) s`; `s:real^N->bool`]
    BAIRE) THEN ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  SIMP_TAC[OPEN_IN_DELETE; OPEN_IN_REFL] THEN
  MATCH_MP_TAC(TAUT `p /\ ~q ==> (p ==> q) ==> r`) THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:real^N = y` THEN
    ASM_SIMP_TAC[IN_CLOSURE_DELETE] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[IN_DELETE];
    REWRITE_TAC[INTERS_IMAGE; IN_DELETE] THEN
    SUBGOAL_THEN `{y:real^N | !x. x IN s ==> y IN s /\ ~(y = x)} = {}`
    SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[CLOSURE_EMPTY; SUBSET_EMPTY]]]);;

(* ------------------------------------------------------------------------- *)
(* Density of sets with small complement, including irrationals.             *)
(* ------------------------------------------------------------------------- *)

let COSMALL_APPROXIMATION = prove
 (`!s. ((:real) DIFF s) <_c (:real)
       ==> !x e. &0 < e ==> ?y. y IN s /\ abs(y - x) < e`,
  let lemma = prove
   (`!s. ((:real^1) DIFF s) <_c (:real)
         ==> !x e. &0 < e ==> ?y. y IN s /\ norm(y - x) < e`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
      `~({x | P x} SUBSET UNIV DIFF s) ==> ?x. x IN s /\ P x`) THEN
    MP_TAC(ISPEC `ball(x:real^1,e)` CARD_EQ_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
    REWRITE_TAC[CARD_NOT_LE] THEN
    REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[DIST_SYM] dist); GSYM ball] THEN
    TRANS_TAC CARD_LTE_TRANS `(:real)` THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[CARD_EQ_SYM] CARD_EQ_IMP_LE]) in
  REWRITE_TAC[FORALL_DROP_IMAGE; FORALL_DROP; EXISTS_DROP] THEN
  REWRITE_TAC[GSYM IMAGE_DROP_UNIV; GSYM DROP_SUB; GSYM ABS_DROP] THEN
  REWRITE_TAC[DROP_IN_IMAGE_DROP] THEN REWRITE_TAC[GSYM FORALL_DROP] THEN
  SIMP_TAC[GSYM IMAGE_DIFF_INJ; DROP_EQ] THEN GEN_TAC THEN
  DISCH_TAC THEN MATCH_MP_TAC lemma THEN POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CARD_LT_CONG THEN
  REWRITE_TAC[IMAGE_DROP_UNIV; CARD_EQ_REFL] THEN
  MATCH_MP_TAC CARD_EQ_IMAGE THEN SIMP_TAC[DROP_EQ]);;

let COCOUNTABLE_APPROXIMATION = prove
 (`!s. COUNTABLE((:real) DIFF s)
       ==> !x e. &0 < e ==> ?y. y IN s /\ abs(y - x) < e`,
  GEN_TAC THEN REWRITE_TAC[COUNTABLE; ge_c] THEN DISCH_TAC THEN
  MATCH_MP_TAC COSMALL_APPROXIMATION THEN
  TRANS_TAC CARD_LET_TRANS `(:num)` THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC CARD_LTE_TRANS `(:num->bool)` THEN SIMP_TAC[CANTOR_THM_UNIV] THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  REWRITE_TAC[CARD_EQ_REAL]);;

let IRRATIONAL_APPROXIMATION = prove
 (`!x e. &0 < e ==> ?y. ~(rational y) /\ abs(y - x) < e`,
  REWRITE_TAC[SET_RULE `~rational y <=> y IN UNIV DIFF rational`] THEN
  MATCH_MP_TAC COCOUNTABLE_APPROXIMATION THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF (UNIV DIFF s) = s`; COUNTABLE_RATIONAL]);;

let OPEN_SET_COSMALL_COORDINATES = prove
 (`!P. (!i. 1 <= i /\ i <= dimindex(:N)
            ==> (:real) DIFF {x | P i x} <_c (:real))
       ==> !s:real^N->bool.
              open s /\ ~(s = {})
              ==> ?x. x IN s /\ !i. 1 <= i /\ i <= dimindex(:N) ==> P i (x$i)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> ?y:real. P i y /\ abs(y - (a:real^N)$i) < d / &(dimindex(:N))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COSMALL_APPROXIMATION) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1];
    REWRITE_TAC[LAMBDA_SKOLEM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_CBALL; dist] THEN
    W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    MATCH_MP_TAC SUM_BOUND_GEN THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1] THEN
    ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; CARD_NUMSEG_1]]);;

let OPEN_SET_COCOUNTABLE_COORDINATES = prove
 (`!P. (!i. 1 <= i /\ i <= dimindex(:N)
            ==> COUNTABLE((:real) DIFF {x | P i x}))
       ==> !s:real^N->bool.
              open s /\ ~(s = {})
              ==> ?x. x IN s /\ !i. 1 <= i /\ i <= dimindex(:N) ==> P i (x$i)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC OPEN_SET_COSMALL_COORDINATES THEN
  REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LET_TRANS `(:num)` THEN ASM_SIMP_TAC[GSYM COUNTABLE_ALT] THEN
  TRANS_TAC CARD_LTE_TRANS `(:num->bool)` THEN SIMP_TAC[CANTOR_THM_UNIV] THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  REWRITE_TAC[CARD_EQ_REAL]);;

let OPEN_SET_IRRATIONAL_COORDINATES = prove
 (`!s:real^N->bool.
        open s /\ ~(s = {})
        ==> ?x. x IN s /\ !i. 1 <= i /\ i <= dimindex(:N) ==> ~rational(x$i)`,
  MATCH_MP_TAC OPEN_SET_COCOUNTABLE_COORDINATES THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF {x | ~P x} = P`; COUNTABLE_RATIONAL]);;

let CLOSURE_COSMALL_COORDINATES = prove
 (`!P. (!i. 1 <= i /\ i <= dimindex(:N)
            ==> (:real) DIFF {x | P i x} <_c (:real))
       ==> closure {x | !i. 1 <= i /\ i <= dimindex (:N) ==> P i (x$i)} =
           (:real^N)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `e:real`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_SET_COSMALL_COORDINATES) THEN
  DISCH_THEN(MP_TAC o SPEC `ball(x:real^N,e)`) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE; IN_BALL] THEN
  MESON_TAC[DIST_SYM]);;

let CLOSURE_COCOUNTABLE_COORDINATES = prove
 (`!P. (!i. 1 <= i /\ i <= dimindex(:N)
            ==> COUNTABLE((:real) DIFF {x | P i x}))
       ==> closure {x | !i. 1 <= i /\ i <= dimindex (:N) ==> P i (x$i)} =
           (:real^N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_COSMALL_COORDINATES THEN
  REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LET_TRANS `(:num)` THEN ASM_SIMP_TAC[GSYM COUNTABLE_ALT] THEN
  TRANS_TAC CARD_LTE_TRANS `(:num->bool)` THEN SIMP_TAC[CANTOR_THM_UNIV] THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  REWRITE_TAC[CARD_EQ_REAL]);;

let CLOSURE_IRRATIONAL_COORDINATES = prove
 (`closure {x | !i. 1 <= i /\ i <= dimindex (:N) ==> ~rational(x$i)} =
   (:real^N)`,
  MATCH_MP_TAC CLOSURE_COCOUNTABLE_COORDINATES THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF {x | ~P x} = P`; COUNTABLE_RATIONAL]);;
