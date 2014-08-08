open Hol_core
open Card
open Floor
open Vectors
open Determinants
open Topology
open Convex
include Paths4

(* ------------------------------------------------------------------------- *)
(* Contractible sets.                                                        *)
(* ------------------------------------------------------------------------- *)

let contractible = new_definition
 `contractible s <=> ?a. homotopic_with (\x. T) (s,s) (\x. x) (\x. a)`;;

let CONTRACTIBLE_IMP_SIMPLY_CONNECTED = prove
 (`!s:real^N->bool. contractible s ==> simply_connected s`,
  GEN_TAC THEN REWRITE_TAC[contractible] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SIMPLY_CONNECTED_EMPTY] THEN
  ASM_REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ALL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  DISCH_TAC THEN REWRITE_TAC[homotopic_loops; PCROSS] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  X_GEN_TAC `p:real^1->real^N` THEN
  REWRITE_TAC[path; path_image; pathfinish; pathstart] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  REWRITE_TAC[homotopic_with; SUBSET; FORALL_IN_IMAGE; PCROSS] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(h o (\y. pastecart (fstcart y) (p(sndcart y):real^N)))
              :real^(1,1)finite_sum->real^N` THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; linepath; o_THM] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC VECTOR_ARITH] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE [IMP_CONJ]
     CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART]);;

let CONTRACTIBLE_IMP_CONNECTED = prove
 (`!s:real^N->bool. contractible s ==> connected s`,
  SIMP_TAC[CONTRACTIBLE_IMP_SIMPLY_CONNECTED;
           SIMPLY_CONNECTED_IMP_CONNECTED]);;

let CONTRACTIBLE_IMP_PATH_CONNECTED = prove
 (`!s:real^N->bool. contractible s ==> path_connected s`,
  SIMP_TAC[CONTRACTIBLE_IMP_SIMPLY_CONNECTED;
           SIMPLY_CONNECTED_IMP_PATH_CONNECTED]);;

let NULLHOMOTOPIC_THROUGH_CONTRACTIBLE = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        contractible t
        ==> ?c. homotopic_with (\h. T) (s,u) (g o f) (\x. c)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [contractible]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N` MP_TAC) THEN
  DISCH_THEN(MP_TAC o ISPECL [`g:real^N->real^P`; `u:real^P->bool`] o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o ISPECL [`f:real^M->real^N`; `s:real^M->bool`] o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT)) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN
  EXISTS_TAC `(g:real^N->real^P) b` THEN ASM_REWRITE_TAC[]);;

let NULLHOMOTOPIC_INTO_CONTRACTIBLE = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ contractible t
        ==> ?c. homotopic_with (\h. T) (s,t) f (\x. c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) = (\x. x) o f` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM; FUN_EQ_THM];
    MATCH_MP_TAC NULLHOMOTOPIC_THROUGH_CONTRACTIBLE THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    SET_TAC[]]);;

let NULLHOMOTOPIC_FROM_CONTRACTIBLE = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ contractible s
        ==> ?c. homotopic_with (\h. T) (s,t) f (\x. c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) = f o (\x. x)` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM; FUN_EQ_THM];
    MATCH_MP_TAC NULLHOMOTOPIC_THROUGH_CONTRACTIBLE THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    SET_TAC[]]);;

let HOMOTOPIC_THROUGH_CONTRACTIBLE = prove
 (`!f1:real^M->real^N g1:real^N->real^P f2 g2 s t u.
        f1 continuous_on s /\ IMAGE f1 s SUBSET t /\
        g1 continuous_on t /\ IMAGE g1 t SUBSET u /\
        f2 continuous_on s /\ IMAGE f2 s SUBSET t /\
        g2 continuous_on t /\ IMAGE g2 t SUBSET u /\
        contractible t /\ path_connected u
        ==> homotopic_with (\h. T) (s,u) (g1 o f1) (g2 o f2)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`f1:real^M->real^N`; `g1:real^N->real^P`; `s:real^M->bool`;
    `t:real^N->bool`; `u:real^P->bool`]
    NULLHOMOTOPIC_THROUGH_CONTRACTIBLE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `c1:real^P` THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET th) THEN
                       MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN MP_TAC(ISPECL
   [`f2:real^M->real^N`; `g2:real^N->real^P`; `s:real^M->bool`;
    `t:real^N->bool`; `u:real^P->bool`]
   NULLHOMOTOPIC_THROUGH_CONTRACTIBLE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `c2:real^P` THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET th) THEN
                       MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
  REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN FIRST_X_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [PATH_CONNECTED_IFF_PATH_COMPONENT]) THEN
  ASM SET_TAC[]);;

let HOMOTOPIC_INTO_CONTRACTIBLE = prove
 (`!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on s /\ IMAGE g s SUBSET t /\
        contractible t
        ==> homotopic_with (\h. T) (s,t) f g`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(f:real^M->real^N) = (\x. x) o f /\ (g:real^M->real^N) = (\x. x) o g`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL [REWRITE_TAC[o_THM; FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_THROUGH_CONTRACTIBLE THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  ASM_SIMP_TAC[IMAGE_ID; SUBSET_REFL; CONTRACTIBLE_IMP_PATH_CONNECTED]);;

let HOMOTOPIC_FROM_CONTRACTIBLE = prove
 (`!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on s /\ IMAGE g s SUBSET t /\
        contractible s /\ path_connected t
        ==> homotopic_with (\h. T) (s,t) f g`,
  REPEAT STRIP_TAC THEN
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(f:real^M->real^N) = f o (\x. x) /\ (g:real^M->real^N) = g o (\x. x)`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL [REWRITE_TAC[o_THM; FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_THROUGH_CONTRACTIBLE THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  ASM_REWRITE_TAC[IMAGE_ID; SUBSET_REFL]);;

let HOMOTOPY_EQUIVALENT_CONTRACTIBLE_SETS = prove
 (`!s:real^M->bool t:real^N->bool.
        contractible s /\ contractible t /\ (s = {} <=> t = {})
        ==> s homotopy_equivalent t`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT; HOMEOMORPHIC_EMPTY] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `b:real^N` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  STRIP_TAC THEN REWRITE_TAC[homotopy_equivalent] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^M` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  EXISTS_TAC `(\x. b):real^M->real^N` THEN
  EXISTS_TAC `(\y. a):real^N->real^M` THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  CONJ_TAC THEN MATCH_MP_TAC HOMOTOPIC_INTO_CONTRACTIBLE THEN
  ASM_REWRITE_TAC[o_DEF; IMAGE_ID; I_DEF; SUBSET_REFL; CONTINUOUS_ON_ID;
                  CONTINUOUS_ON_CONST] THEN
  ASM SET_TAC[]);;

let STARLIKE_IMP_CONTRACTIBLE_GEN = prove
 (`!P s.
        (!a t. a IN s /\ &0 <= t /\ t <= &1 ==> P(\x. (&1 - t) % x + t % a)) /\
        starlike s
        ==> ?a:real^N. homotopic_with P (s,s) (\x. x) (\x. a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[starlike] THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
  REWRITE_TAC[segment; SUBSET; FORALL_IN_GSPEC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
  REWRITE_TAC[homotopic_with; PCROSS] THEN
  EXISTS_TAC `\y:real^(1,N)finite_sum.
             (&1 - drop(fstcart y)) % sndcart y +
             drop(fstcart y) % a` THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC; IN_INTERVAL_1;
    SUBSET; FORALL_IN_IMAGE; REAL_SUB_RZERO; REAL_SUB_REFL; FORALL_IN_GSPEC;
    VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  SIMP_TAC[o_DEF; LIFT_DROP; ETA_AX; LIFT_SUB; CONTINUOUS_ON_SUB;
           CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON; ETA_AX;
           LINEAR_FSTCART; LINEAR_SNDCART]);;

let STARLIKE_IMP_CONTRACTIBLE = prove
 (`!s:real^N->bool. starlike s ==> contractible s`,
  SIMP_TAC[contractible; STARLIKE_IMP_CONTRACTIBLE_GEN]);;

let CONTRACTIBLE_UNIV = prove
 (`contractible(:real^N)`,
  SIMP_TAC[STARLIKE_IMP_CONTRACTIBLE; STARLIKE_UNIV]);;

let STARLIKE_IMP_SIMPLY_CONNECTED = prove
 (`!s:real^N->bool. starlike s ==> simply_connected s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTRACTIBLE_IMP_SIMPLY_CONNECTED THEN
  MATCH_MP_TAC STARLIKE_IMP_CONTRACTIBLE THEN ASM_REWRITE_TAC[]);;

let CONVEX_IMP_SIMPLY_CONNECTED = prove
 (`!s:real^N->bool. convex s ==> simply_connected s`,
  MESON_TAC[CONVEX_IMP_STARLIKE; STARLIKE_IMP_SIMPLY_CONNECTED;
            SIMPLY_CONNECTED_EMPTY]);;

let STARLIKE_IMP_PATH_CONNECTED = prove
 (`!s:real^N->bool. starlike s ==> path_connected s`,
  MESON_TAC[STARLIKE_IMP_SIMPLY_CONNECTED;
            SIMPLY_CONNECTED_IMP_PATH_CONNECTED]);;

let STARLIKE_IMP_CONNECTED = prove
 (`!s:real^N->bool. starlike s ==> connected s`,
  MESON_TAC[STARLIKE_IMP_PATH_CONNECTED; PATH_CONNECTED_IMP_CONNECTED]);;

let IS_INTERVAL_SIMPLY_CONNECTED_1 = prove
 (`!s:real^1->bool. is_interval s <=> simply_connected s`,
  MESON_TAC[SIMPLY_CONNECTED_IMP_PATH_CONNECTED; IS_INTERVAL_PATH_CONNECTED_1;
            CONVEX_IMP_SIMPLY_CONNECTED; IS_INTERVAL_CONVEX_1]);;

let CONTRACTIBLE_EMPTY = prove
 (`contractible {}`,
  SIMP_TAC[contractible; HOMOTOPIC_WITH; PCROSS_EMPTY; NOT_IN_EMPTY] THEN
  REWRITE_TAC[CONTINUOUS_ON_EMPTY] THEN SET_TAC[]);;

let CONTRACTIBLE_CONVEX_TWEAK_BOUNDARY_POINTS = prove
 (`!s t:real^N->bool.
        convex s /\ relative_interior s SUBSET t /\ t SUBSET closure s
        ==> contractible t`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[SUBSET_EMPTY; CLOSURE_EMPTY; CONTRACTIBLE_EMPTY] THEN
  STRIP_TAC THEN MATCH_MP_TAC STARLIKE_IMP_CONTRACTIBLE THEN
  MATCH_MP_TAC STARLIKE_CONVEX_TWEAK_BOUNDARY_POINTS THEN ASM_MESON_TAC[]);;

let CONVEX_IMP_CONTRACTIBLE = prove
 (`!s:real^N->bool. convex s ==> contractible s`,
  MESON_TAC[CONVEX_IMP_STARLIKE; CONTRACTIBLE_EMPTY;
            STARLIKE_IMP_CONTRACTIBLE]);;

let CONTRACTIBLE_SING = prove
 (`!a:real^N. contractible {a}`,
  SIMP_TAC[CONVEX_IMP_CONTRACTIBLE; CONVEX_SING]);;

let IS_INTERVAL_CONTRACTIBLE_1 = prove
 (`!s:real^1->bool. is_interval s <=> contractible s`,
  MESON_TAC[CONTRACTIBLE_IMP_PATH_CONNECTED; IS_INTERVAL_PATH_CONNECTED_1;
            CONVEX_IMP_CONTRACTIBLE; IS_INTERVAL_CONVEX_1]);;

let CONTRACTIBLE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        contractible s /\ contractible t ==> contractible(s PCROSS t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contractible; homotopic_with] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `h:real^(1,M)finite_sum->real^M`] THEN
  REPEAT DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`b:real^N`; `k:real^(1,N)finite_sum->real^N`] THEN
  REPEAT DISCH_TAC THEN
  EXISTS_TAC `pastecart (a:real^M) (b:real^N)` THEN
  EXISTS_TAC `\z. pastecart
                   ((h:real^(1,M)finite_sum->real^M)
                    (pastecart (fstcart z) (fstcart(sndcart z))))
                   ((k:real^(1,N)finite_sum->real^N)
                    (pastecart (fstcart z) (sndcart(sndcart z))))` THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
               FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[CONTINUOUS_ON_PASTECART; LINEAR_CONTINUOUS_ON;
           LINEAR_FSTCART; LINEAR_SNDCART; CONTINUOUS_ON_ID;
           GSYM o_DEF; CONTINUOUS_ON_COMPOSE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART] THEN
  SIMP_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART]);;

let CONTRACTIBLE_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        contractible(s PCROSS t) <=>
        s = {} \/ t = {} \/ contractible s /\ contractible t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CONTRACTIBLE_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CONTRACTIBLE_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[CONTRACTIBLE_PCROSS] THEN
  REWRITE_TAC[contractible; homotopic_with; LEFT_IMP_EXISTS_THM] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC
   [`a:real^M`; `b:real^N`;
    `h:real^(1,(M,N)finite_sum)finite_sum->real^(M,N)finite_sum`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^M) IN s /\ (b:real^N) IN t` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM PASTECART_IN_PCROSS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `a:real^M` THEN
    EXISTS_TAC
     `fstcart o
      (h:real^(1,(M,N)finite_sum)finite_sum->real^(M,N)finite_sum) o
      (\z. pastecart (fstcart z) (pastecart (sndcart z) b))`;
    EXISTS_TAC `b:real^N` THEN
    EXISTS_TAC
     `sndcart o
      (h:real^(1,(M,N)finite_sum)finite_sum->real^(M,N)finite_sum) o
      (\z. pastecart (fstcart z) (pastecart a (sndcart z)))`] THEN
  ASM_REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                  SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; o_THM] THEN
  (CONJ_TAC THENL
    [ALL_TAC;  ASM_MESON_TAC[PASTECART_FST_SND; PASTECART_IN_PCROSS]]) THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
           LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS]);;

let HOMOTOPY_EQUIVALENT_EMPTY = prove
 (`(!s. (s:real^M->bool) homotopy_equivalent ({}:real^N->bool) <=> s = {}) /\
   (!t. ({}:real^M->bool) homotopy_equivalent (t:real^N->bool) <=> t = {})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  SIMP_TAC[HOMOTOPY_EQUIVALENT_CONTRACTIBLE_SETS; CONTRACTIBLE_EMPTY] THEN
  REWRITE_TAC[homotopy_equivalent] THEN SET_TAC[]);;

let HOMOTOPY_DOMINATED_CONTRACTIBILITY = prove
 (`!f:real^M->real^N g s t.
        f continuous_on s /\
        IMAGE f s SUBSET t /\
        g continuous_on t /\
        IMAGE g t SUBSET s /\
        homotopic_with (\x. T) (t,t) (f o g) I /\
        contractible s
        ==> contractible t`,
  REPEAT GEN_TAC THEN SIMP_TAC[contractible; I_DEF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`; `t:real^N->bool`]
        NULLHOMOTOPIC_FROM_CONTRACTIBLE) THEN
  ASM_REWRITE_TAC[contractible; I_DEF] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `(f:real^M->real^N) o (g:real^N->real^M)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. (b:real^N)) = (\x. b) o (g:real^N->real^M)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[]);;

let HOMOTOPY_EQUIVALENT_CONTRACTIBILITY = prove
 (`!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t ==> (contractible s <=> contractible t)`,
  REWRITE_TAC[homotopy_equivalent] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
   (REWRITE_RULE[CONJ_ASSOC] HOMOTOPY_DOMINATED_CONTRACTIBILITY)) THEN
  ASM_MESON_TAC[]);;

let HOMOTOPY_EQUIVALENT_SING = prove
 (`!s:real^M->bool a:real^N.
        s homotopy_equivalent {a} <=> ~(s = {}) /\ contractible s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[HOMOTOPY_EQUIVALENT_EMPTY; NOT_INSERT_EMPTY] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPY_EQUIVALENT_CONTRACTIBILITY) THEN
    REWRITE_TAC[CONTRACTIBLE_SING];
    DISCH_TAC THEN MATCH_MP_TAC HOMOTOPY_EQUIVALENT_CONTRACTIBLE_SETS THEN
    ASM_REWRITE_TAC[CONTRACTIBLE_SING; NOT_INSERT_EMPTY]]);;

let HOMEOMORPHIC_CONTRACTIBLE_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> (contractible s <=> contractible t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPY_EQUIVALENT_CONTRACTIBILITY THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT]);;

let HOMEOMORPHIC_CONTRACTIBLE = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ contractible s ==> contractible t`,
  MESON_TAC[HOMEOMORPHIC_CONTRACTIBLE_EQ]);;

let CONTRACTIBLE_TRANSLATION = prove
 (`!a:real^N s. contractible (IMAGE (\x. a + x) s) <=> contractible s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_CONTRACTIBLE_EQ THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION]);;

add_translation_invariants [CONTRACTIBLE_TRANSLATION];;

let CONTRACTIBLE_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (contractible (IMAGE f s) <=> contractible s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_CONTRACTIBLE_EQ THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ;
                HOMEOMORPHIC_REFL]);;

add_linear_invariants [CONTRACTIBLE_INJECTIVE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Homeomorphisms between punctured spheres and affine sets.                 *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_PUNCTURED_AFFINE_SPHERE_AFFINE = prove
 (`!a r b t:real^N->bool p:real^M->bool.
        &0 < r /\ b IN sphere(a,r) /\ affine t /\ a IN t /\ b IN t /\
        affine p /\ aff_dim t = aff_dim p + &1
        ==> ((sphere(a:real^N,r) INTER t) DELETE b) homeomorphic p`,
  GEOM_ORIGIN_TAC `a:real^N` THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  REWRITE_TAC[sphere; DIST_0; IN_ELIM_THM] THEN
  SIMP_TAC[CONJ_ASSOC; NORM_ARITH
   `&0 < r /\ norm(b:real^N) = r <=> norm(b) = r /\ ~(b = vec 0)`] THEN
  GEOM_NORMALIZE_TAC `b:real^N` THEN REWRITE_TAC[] THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `b:real^N` THEN
  SIMP_TAC[NORM_MUL; real_abs; NORM_BASIS; LE_REFL; DIMINDEX_GE_1] THEN
  X_GEN_TAC `b:real` THEN REWRITE_TAC[REAL_MUL_RID; VECTOR_MUL_EQ_0] THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_LID] THEN
  ASM_CASES_TAC `r = &1` THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(K ALL_TAC) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `subspace(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_EQ_SUBSPACE]; ALL_TAC] THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `{x:real^N | x$1 = &0} INTER t` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HOMEOMORPHIC_AFFINE_SETS THEN
    ASM_SIMP_TAC[AFFINE_INTER; AFFINE_STANDARD_HYPERPLANE] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    MP_TAC(ISPECL [`basis 1:real^N`; `&0`; `t:real^N->bool`]
        AFF_DIM_AFFINE_INTER_HYPERPLANE) THEN
    ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(t INTER {x:real^N | x$1 = &0} = {})` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      EXISTS_TAC `vec 0:real^N` THEN ASM_REWRITE_TAC[VEC_COMPONENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(t SUBSET {v:real^N | v$1 = &0})` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `basis 1:real^N`) THEN
      ASM_SIMP_TAC[IN_ELIM_THM; BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]] THEN
  SUBGOAL_THEN
   `({x:real^N | norm x = &1} INTER t) DELETE (basis 1) =
    {x | norm x = &1 /\ ~(x$1 = &1)} INTER t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `s DELETE a = s' ==> (s INTER t) DELETE a = s' INTER t`) THEN
    MATCH_MP_TAC(SET_RULE
     `Q a /\ (!x. P x /\ Q x ==> x = a)
      ==> {x | P x} DELETE a = {x | P x /\ ~Q x}`) THEN
    SIMP_TAC[BASIS_COMPONENT; CART_EQ; DIMINDEX_GE_1; LE_REFL] THEN
    REWRITE_TAC[NORM_EQ_SQUARE; REAL_POS; REAL_POW_ONE] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    ASM_SIMP_TAC[dot; SUM_CLAUSES_LEFT; DIMINDEX_GE_1] THEN
    REWRITE_TAC[REAL_ARITH `&1 * &1 + s = &1 <=> s = &0`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
      SUM_POS_EQ_0_NUMSEG)) THEN
    REWRITE_TAC[REAL_LE_SQUARE; REAL_ENTIRE] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphic; HOMEOMORPHISM] THEN MAP_EVERY ABBREV_TAC
   [`f = \x:real^N. &2 % basis 1 + &2 / (&1 - x$1) % (x - basis 1)`;
    `g = \y:real^N.
           basis 1 + &4 / (norm y pow 2 + &4) % (y - &2 % basis 1)`] THEN
  MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[CONTINUOUS_ON_SUBSET; INTER_SUBSET]
     `f continuous_on s ==> f continuous_on (s INTER t)`) THEN
    EXPAND_TAC "f" THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[o_DEF; real_div; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
    SIMP_TAC[REAL_SUB_0; IN_ELIM_THM] THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN
    REWRITE_TAC[LE_REFL; DIMINDEX_GE_1];
    MATCH_MP_TAC(SET_RULE
     `IMAGE f s SUBSET s' /\ IMAGE f t SUBSET t
      ==> IMAGE f (s INTER t) SUBSET (s' INTER t)`) THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[SUBSPACE_ADD; SUBSPACE_MUL; SUBSPACE_SUB] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             LE_REFL; DIMINDEX_GE_1; VECTOR_SUB_COMPONENT] THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC(MESON[CONTINUOUS_ON_SUBSET; INTER_SUBSET]
     `f continuous_on s ==> f continuous_on (s INTER t)`) THEN
    EXPAND_TAC "g" THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[o_DEF; real_div; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
    SIMP_TAC[LIFT_ADD; REAL_POW_LE; NORM_POS_LE; REAL_ARITH
     `&0 <= x ==> ~(x + &4 = &0)`] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[REAL_POW_2; LIFT_CMUL; CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM; GSYM o_DEF];
    MATCH_MP_TAC(SET_RULE
     `IMAGE f s SUBSET s' /\ IMAGE f t SUBSET t
      ==> IMAGE f (s INTER t) SUBSET (s' INTER t)`) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[NORM_EQ_SQUARE; REAL_POS] THEN EXPAND_TAC "g" THEN
    CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[SUBSPACE_ADD; SUBSPACE_MUL; SUBSPACE_SUB]] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH
     `b + a % (y - &2 % b):real^N = (&1 - &2 * a) % b + a % y`] THEN
    REWRITE_TAC[NORM_POW_2; VECTOR_ARITH
     `(a + b:real^N) dot (a + b) = (a dot a + b dot b) + &2 * a dot b`] THEN
    ASM_SIMP_TAC[DOT_LMUL; DOT_RMUL; DOT_BASIS; BASIS_COMPONENT; LE_REFL;
                VECTOR_ADD_COMPONENT; DIMINDEX_GE_1; VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; GSYM REAL_POW_2] THEN
    SUBGOAL_THEN `~((y:real^N) dot y + &4 = &0)` MP_TAC THENL
     [MESON_TAC[DOT_POS_LE; REAL_ARITH `&0 <= x ==> ~(x + &4 = &0)`];
      CONV_TAC REAL_FIELD];
    SUBGOAL_THEN
     `!x. norm x = &1 /\ ~(x$1 = &1)
          ==> norm((f:real^N->real^N) x) pow 2 = &4 * (&1 + x$1) / (&1 - x$1)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "f" THEN
      REWRITE_TAC[VECTOR_ARITH
       `a % b + m % (x - b):real^N = (a - m) % b + m % x`] THEN
      REWRITE_TAC[NORM_POW_2; VECTOR_ARITH
       `(a + b:real^N) dot (a + b) = (a dot a + b dot b) + &2 * a dot b`] THEN
      SIMP_TAC[DOT_LMUL; DOT_RMUL; DOT_BASIS; BASIS_COMPONENT;
               DIMINDEX_GE_1; LE_REFL; VECTOR_MUL_COMPONENT] THEN
      ASM_REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_2; REAL_MUL_RID;
                      REAL_POW_ONE] THEN
      UNDISCH_TAC `~((x:real^N)$1 = &1)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_FIELD
     `~(x = &1)
      ==> &4 * (&1 + x) / (&1 - x) + &4 = &8 / (&1 - x)`] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN
    REWRITE_TAC[REAL_ARITH `&4 * inv(&8) * x = x / &2`] THEN
    EXPAND_TAC "f" THEN
    REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH
     `b + a % (x - b):real^N = x <=> (&1 - a) % (x - b) = vec 0`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~((x:real^N)$1 = &1)` THEN CONV_TAC REAL_FIELD;
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `~((y:real^N) dot y + &4 = &0)` ASSUME_TAC THENL
     [MESON_TAC[DOT_POS_LE; REAL_ARITH `&0 <= x ==> ~(x + &4 = &0)`];
      ALL_TAC] THEN
    SUBGOAL_THEN `((g:real^N->real^N) y)$1 =
                  (y dot y - &4) / (y dot y + &4)` ASSUME_TAC THENL
     [EXPAND_TAC "g" THEN REWRITE_TAC[VECTOR_ADD_COMPONENT] THEN
      REWRITE_TAC[VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
      ASM_SIMP_TAC[BASIS_COMPONENT; LE_REFL; NORM_POW_2; DIMINDEX_GE_1] THEN
      UNDISCH_TAC `~((y:real^N) dot y + &4 = &0)` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "g" THEN SIMP_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH
     `b + a % (x - b):real^N = x <=> (&1 - a) % (x - b) = vec 0`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; NORM_POW_2] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~((y:real^N) dot y + &4 = &0)` THEN CONV_TAC REAL_FIELD]);;

let HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN = prove
 (`!s:real^N->bool t:real^M->bool a.
        convex s /\ bounded s /\ a IN relative_frontier s /\
        affine t /\ aff_dim s = aff_dim t + &1
        ==> (relative_frontier s DELETE a) homeomorphic t`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_GE; INT_ARITH
   `--(&1):int <= s ==> ~(--(&1) = s + &1)`] THEN
  MP_TAC(ISPECL [`(:real^N)`; `aff_dim(s:real^N->bool)`]
    CHOOSE_AFFINE_SUBSET) THEN REWRITE_TAC[SUBSET_UNIV] THEN
  REWRITE_TAC[AFF_DIM_GE; AFF_DIM_LE_UNIV; AFF_DIM_UNIV; AFFINE_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_EQ_MINUS1]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:real^N->bool`; `ball(z:real^N,&1) INTER t`]
        HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS) THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `ball(z:real^N,&1)`]
        (ONCE_REWRITE_RULE[INTER_COMM] AFF_DIM_CONVEX_INTER_OPEN)) THEN
  MP_TAC(ISPECL [`ball(z:real^N,&1)`; `t:real^N->bool`]
        RELATIVE_FRONTIER_CONVEX_INTER_AFFINE) THEN
  ASM_SIMP_TAC[CONVEX_INTER; BOUNDED_INTER; BOUNDED_BALL; CONVEX_BALL;
               AFFINE_IMP_CONVEX; INTERIOR_OPEN; OPEN_BALL;
               FRONTIER_BALL; REAL_LT_01] THEN
  SUBGOAL_THEN `~(ball(z:real^N,&1) INTER t = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01];
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN SIMP_TAC[]] THEN
  REWRITE_TAC[homeomorphic; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM homeomorphic] THEN
  TRANS_TAC HOMEOMORPHIC_TRANS
    `(sphere(z,&1) INTER t) DELETE (h:real^N->real^N) a` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM]) THEN
    REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; DELETE_SUBSET];
      ASM SET_TAC[];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; DELETE_SUBSET];
      ASM SET_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_AFFINE_SPHERE_AFFINE THEN
    ASM_REWRITE_TAC[REAL_LT_01; GSYM IN_INTER] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM]) THEN
    ASM SET_TAC[]]);;

let HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE = prove
 (`!a r b:real^N t:real^M->bool.
    &0 < r /\ b IN sphere(a,r) /\ affine t /\ aff_dim(t) + &1 = &(dimindex(:N))
    ==> (sphere(a:real^N,r) DELETE b) homeomorphic t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cball(a:real^N,r)`; `t:real^M->bool`; `b:real^N`]
        HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_CBALL; REAL_LT_IMP_NZ; AFF_DIM_CBALL;
               CONVEX_CBALL; BOUNDED_CBALL]);;

let HOMEOMORPHIC_PUNCTURED_SPHERE_HYPERPLANE = prove
 (`!a r b c d.
        &0 < r /\ b IN sphere(a,r) /\ ~(c = vec 0)
        ==> (sphere(a:real^N,r) DELETE b) homeomorphic
             {x:real^N | c dot x = d}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE THEN
  ASM_SIMP_TAC[AFFINE_HYPERPLANE; AFF_DIM_HYPERPLANE] THEN INT_ARITH_TAC);;

let HOMEOMORPHIC_PUNCTURED_SPHERE_UNIV = prove
 (`!a r b.
        &0 < r /\ b IN sphere(a,r) /\ dimindex(:N) = dimindex(:M) + 1
        ==> (sphere(a:real^N,r) DELETE b) homeomorphic (:real^M)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `{x:real^N | basis 1 dot x = &0}` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_HYPERPLANE_UNIV; BASIS_NONZERO; LE_REFL;
               DIMINDEX_GE_1; HOMEOMORPHIC_PUNCTURED_SPHERE_HYPERPLANE]);;

let CONTRACTIBLE_PUNCTURED_SPHERE = prove
 (`!a r b:real^N.
        &0 < r /\ b IN sphere(a,r) ==> contractible(sphere(a,r) DELETE b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `contractible {x:real^N | basis 1 dot x = &0}` MP_TAC THENL
   [SIMP_TAC[CONVEX_IMP_CONTRACTIBLE; CONVEX_HYPERPLANE];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMEOMORPHIC_CONTRACTIBLE) THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_HYPERPLANE THEN
    ASM_SIMP_TAC[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1]]);;

(* ------------------------------------------------------------------------- *)
(* When dealing with AR, ANR and ANR later, it's useful to know that any set *)
(* at all is homeomorphic to a closed subset of a convex set, and if the     *)
(* set is locally compact we can take the convex set to be the universe.     *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_CLOSED_IN_CONVEX = prove
 (`!s:real^M->bool.
        aff_dim s < &(dimindex(:N))
        ==> ?u t:real^N->bool.
                convex u /\
                ~(u = {}) /\
                closed_in (subtopology euclidean u) t /\
                s homeomorphic t`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(:real^N)`; `{}:real^N->bool`] THEN
    REWRITE_TAC[CONVEX_UNIV; UNIV_NOT_EMPTY; CLOSED_IN_EMPTY] THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY])] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^M` MP_TAC) THEN
  GEOM_ORIGIN_TAC `a:real^M` THEN
  SIMP_TAC[AFF_DIM_DIM_0; HULL_INC; INT_OF_NUM_LT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{x:real^N | x$1 = &0}`; `dim(s:real^M->bool)`]
        CHOOSE_SUBSPACE_OF_SUBSPACE) THEN
  SIMP_TAC[DIM_SPECIAL_HYPERPLANE; DIMINDEX_GE_1; LE_REFL; SUBSET; IN_ELIM_THM;
           SPAN_OF_SUBSPACE; SUBSPACE_SPECIAL_HYPERPLANE] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`span s:real^M->bool`; `t:real^N->bool`]
    ISOMETRIES_SUBSPACES) THEN
  ASM_REWRITE_TAC[SUBSPACE_SPAN; DIM_SPAN; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^M->real^N`; `k:real^N->real^M`] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `&1`; `basis 1:real^N`;
                 `{x:real^N | basis 1 dot x = &0}`]
        HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE) THEN
  SIMP_TAC[AFFINE_HYPERPLANE; AFF_DIM_HYPERPLANE; BASIS_NONZERO;
           DIMINDEX_GE_1; LE_REFL; REAL_LT_01; IN_SPHERE_0; NORM_BASIS] THEN
  ANTS_TAC THENL [INT_ARITH_TAC; ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM]] THEN
  SIMP_TAC[DOT_BASIS; DIMINDEX_GE_1; LE_REFL; homeomorphic] THEN
  REWRITE_TAC[HOMEOMORPHISM; LEFT_IMP_EXISTS_THM; IN_ELIM_THM;
              SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; IN_DELETE] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `ball(vec 0,&1) UNION
              IMAGE ((f:real^N->real^N) o (h:real^M->real^N)) s` THEN
  EXISTS_TAC `IMAGE ((f:real^N->real^N) o (h:real^M->real^N)) s` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_INTERMEDIATE_BALL THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `&1`] THEN
    REWRITE_TAC[SUBSET_UNION; UNION_SUBSET; BALL_SUBSET_CBALL] THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_CBALL_0] THEN
    ASM_MESON_TAC[SPAN_SUPERSET; REAL_LE_REFL];
    REWRITE_TAC[NOT_IN_EMPTY; IMAGE_o] THEN ASM SET_TAC[];
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN
    EXISTS_TAC `sphere(vec 0:real^N,&1)` THEN
    REWRITE_TAC[CLOSED_SPHERE] THEN MATCH_MP_TAC(SET_RULE
     `b INTER t = {} /\ s SUBSET t ==> s = (b UNION s) INTER t`) THEN
    REWRITE_TAC[GSYM CBALL_DIFF_SPHERE] THEN
    CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[SUBSET]] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM; IN_SPHERE_0] THEN
    ASM_MESON_TAC[SPAN_SUPERSET];
    MAP_EVERY EXISTS_TAC
     [`(k:real^N->real^M) o (g:real^N->real^N)`;
      `(f:real^N->real^N) o (h:real^M->real^N)`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM; IMAGE_o] THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON]) THEN
    TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     CONTINUOUS_ON_SUBSET))) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; IN_DELETE] THEN
    MP_TAC(ISPEC `s:real^M->bool` SPAN_INC) THEN ASM SET_TAC[]]);;

let LOCALLY_COMPACT_HOMEOMORPHIC_CLOSED = prove
 (`!s:real^M->bool.
        locally compact s /\ dimindex(:M) < dimindex(:N)
        ==> ?t:real^N->bool. closed t /\ s homeomorphic t`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `?t:real^(M,1)finite_sum->bool h.
            closed t /\ homeomorphism (s,t) (h,fstcart)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOCALLY_COMPACT_HOMEOMORPHISM_PROJECTION_CLOSED];
    ALL_TAC] THEN
  ABBREV_TAC
   `f:real^(M,1)finite_sum->real^N =
        \x. lambda i. if i <= dimindex(:M) then x$i
                      else x$(dimindex(:M)+1)` THEN
  ABBREV_TAC
   `g:real^N->real^(M,1)finite_sum = (\x. lambda i. x$i)` THEN
  EXISTS_TAC `IMAGE (f:real^(M,1)finite_sum->real^N) t` THEN
  SUBGOAL_THEN `linear(f:real^(M,1)finite_sum->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[linear; CART_EQ] THEN
    SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(g:real^N->real^(M,1)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[linear; CART_EQ] THEN
    SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (g:real^N->real^(M,1)finite_sum)((f:real^(M,1)finite_sum->real^N) x) =
        x`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["f"; "g"] THEN FIRST_ASSUM(MP_TAC o MATCH_MP
     (ARITH_RULE `m < n ==> !i. i <= m + 1 ==> i <= n`)) THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    REWRITE_TAC[ARITH_RULE `i <= n + 1 <=> i <= n \/ i = n + 1`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CLOSED_INJECTIVE_LINEAR_IMAGE]; ALL_TAC] THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `t:real^(M,1)finite_sum->bool` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[homeomorphic]; ALL_TAC] THEN
  REWRITE_TAC[homeomorphic; HOMEOMORPHISM] THEN MAP_EVERY EXISTS_TAC
   [`f:real^(M,1)finite_sum->real^N`; `g:real^N->real^(M,1)finite_sum`] THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Simple connectedness of a union. This is essentially a stripped-down      *)
(* version of the Seifert - Van Kampen theorem.                              *)
(* ------------------------------------------------------------------------- *)

let SIMPLY_CONNECTED_UNION = prove
 (`!s t:real^N->bool.
    open_in (subtopology euclidean (s UNION t)) s /\
    open_in (subtopology euclidean (s UNION t)) t /\
    simply_connected s /\ simply_connected t /\
    path_connected (s INTER t) /\ ~(s INTER t = {})
    ==> simply_connected (s UNION t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool`
   (STRIP_ASSUME_TAC o GSYM)) MP_TAC) THEN
   DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^N->bool`
   (STRIP_ASSUME_TAC o GSYM)) MP_TAC) THEN
  SIMP_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_PATH; PATH_CONNECTED_UNION] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(pathstart p:real^N) IN s UNION t` MP_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]; REWRITE_TAC[IN_UNION]] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN
  MAP_EVERY (fun s -> let x = mk_var(s,`:real^N->bool`) in SPEC_TAC(x,x))
   ["v"; "u"; "t"; "s"] THEN
  MATCH_MP_TAC(MESON[]
   `(!s t u v. x IN s ==> P x s t u v) /\
    (!x s t u v. P x s t u v ==> P x t s v u)
    ==> (!s t u v. x IN s \/ x IN t ==>  P x s t u v)`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[UNION_COMM; INTER_COMM] THEN
    MATCH_MP_TAC MONO_IMP THEN SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `?e. &0 < e /\
        !x y. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1] /\
              norm(x - y) < e
              ==> path_image(subpath x y p) SUBSET (s:real^N->bool) \/
                  path_image(subpath x y p) SUBSET t`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `path_image(p:real^1->real^N)` HEINE_BOREL_LEMMA) THEN
    ASM_SIMP_TAC[COMPACT_PATH_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `{u:real^N->bool,v}`) THEN
    SIMP_TAC[UNIONS_2; EXISTS_IN_INSERT; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`p:real^1->real^N`; `interval[vec 0:real^1,vec 1]`]
        COMPACT_UNIFORMLY_CONTINUOUS) THEN
    ASM_REWRITE_TAC[GSYM path; COMPACT_INTERVAL; uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[dist] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^1->real^N) x`) THEN
    ANTS_TAC THENL [REWRITE_TAC[path_image] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!p'. p SUBSET b /\
           (s UNION t) INTER u = s /\ (s UNION t) INTER v = t /\
           p SUBSET p' /\ p' SUBSET s UNION t
           ==>  (b SUBSET u \/ b SUBSET v) ==> p SUBSET s \/ p SUBSET t`) THEN
    EXISTS_TAC `path_image(p:real^1->real^N)` THEN
    ASM_SIMP_TAC[PATH_IMAGE_SUBPATH_SUBSET] THEN
    REWRITE_TAC[PATH_IMAGE_SUBPATH_GEN; SUBSET; FORALL_IN_IMAGE] THEN
    SUBGOAL_THEN `segment[x,y] SUBSET ball(x:real^1,d)` MP_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; CENTRE_IN_BALL] THEN
      ASM_REWRITE_TAC[IN_BALL; EMPTY_SUBSET; CONVEX_BALL; dist];
      REWRITE_TAC[IN_BALL; dist; SUBSET] THEN STRIP_TAC THEN
      X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [SEGMENT_1]) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
      ASM_REAL_ARITH_TAC];
    MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `N:num` THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `!n. n <= N /\ p(lift(&n / &N)) IN s
        ==> ?q. path(q:real^1->real^N) /\ path_image q SUBSET s /\
                homotopic_paths (s UNION t)
                                (subpath (vec 0) (lift(&n / &N)) p) q`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `N:num`) THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_OF_NUM_EQ; LE_REFL; LIFT_NUM] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[pathfinish]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^N` MP_TAC) THEN
    REWRITE_TAC[SUBPATH_TRIVIAL] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_PATHS_TRANS) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN
    ASM_MESON_TAC[SUBSET_UNION]] THEN
  SUBGOAL_THEN
   `!n. n < N
        ==> path_image(subpath (lift(&n / &N)) (lift(&(SUC n) / &N)) p)
              SUBSET (s:real^N->bool) \/
            path_image(subpath (lift(&n / &N)) (lift(&(SUC n) / &N)) p)
              SUBSET t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; GSYM LIFT_SUB; DROP_VEC;
                NORM_REAL; GSYM drop;
                REAL_ARITH `abs(a / c - b / c) = abs((b - a) / c)`] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUC; REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ;
                 REAL_OF_NUM_LT; LE_1; REAL_ARITH `(x + &1) - x = &1`] THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_LZERO; REAL_ABS_INV;
      REAL_ABS_NUM; REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[REAL_ARITH `&0 / x = &0`; LIFT_NUM] THEN
    EXISTS_TAC `linepath((p:real^1->real^N)(vec 0),p(vec 0))` THEN
    REWRITE_TAC[SUBPATH_REFL; HOMOTOPIC_PATHS_REFL] THEN
    REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
    UNDISCH_TAC `(pathstart p:real^N) IN s` THEN REWRITE_TAC[pathstart] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\m. m < n /\ (p(lift(&m / &N)):real^N) IN s` num_MAX) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THENL [EXISTS_TAC `0`; MESON_TAC[LT_IMP_LE]] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 / x = &0`; LIFT_NUM; LE_1] THEN
    ASM_MESON_TAC[pathstart];
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `?q. path q /\
        path_image(q:real^1->real^N) SUBSET s /\
        homotopic_paths (s UNION t) (subpath (vec 0) (lift (&m / &N)) p) q`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. m < i /\ i <= n
        ==> path_image(subpath (lift(&m / &N)) (lift(&i / &N)) p) SUBSET s \/
            path_image(subpath (lift(&m / &N)) (lift(&i / &N)) p) SUBSET
                 (t:real^N->bool)`
  MP_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[CONJUNCT1 LT] THEN
    X_GEN_TAC `i:num` THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_CASES_TAC `i:num = m` THENL
     [DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]] THEN
    SUBGOAL_THEN
     `p(lift(&i / &N)) IN t /\ ~((p(lift(&i / &N)):real^N) IN s)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `x IN s UNION t /\ ~(x IN s) ==> x IN t /\ ~(x IN s)`) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `s SUBSET t ==> x IN s ==> x IN t`)) THEN
        REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                     LE_1; REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC;
        SUBGOAL_THEN `i < n /\ ~(i:num <= m)` MP_TAC THENL
         [ASM_ARITH_TAC; ASM_MESON_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `path_image(subpath (lift(&i / &N)) (lift (&(SUC i) / &N)) p) SUBSET s \/
      path_image(subpath (lift(&i / &N)) (lift (&(SUC i) / &N)) p) SUBSET
        (t:real^N->bool)`
    MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `~(x IN s)
      ==> (x IN p /\ x IN q) /\ (q UNION p = r)
          ==> p SUBSET s \/ p SUBSET t
              ==> q SUBSET s \/ q SUBSET t
                  ==> r SUBSET s \/ r SUBSET t`)) THEN
    SIMP_TAC[PATH_IMAGE_SUBPATH_GEN; FUN_IN_IMAGE; ENDS_IN_SEGMENT] THEN
    REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC UNION_SEGMENT THEN
    ASM_SIMP_TAC[SEGMENT_1; LIFT_DROP; REAL_LE_DIV2_EQ; REAL_OF_NUM_LT;
                 LE_1; REAL_OF_NUM_LE; LT_IMP_LE; IN_INTERVAL_1] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[LE_REFL]] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `(q:real^1->real^N) ++
                subpath (lift(&m / &N)) (lift (&n / &N)) p` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PATH_JOIN_IMP THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH) THEN
      ASM_SIMP_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
      DISCH_TAC THEN MATCH_MP_TAC PATH_SUBPATH THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                   LE_1; REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
      EXISTS_TAC `subpath (vec 0) (lift(&m / &N)) (p:real^1->real^N) ++
                  subpath (lift(&m / &N)) (lift(&n / &N)) p` THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
        MATCH_MP_TAC HOMOTOPIC_JOIN_SUBPATHS THEN
        ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
        MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
        ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
        MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN
        EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_UNION] THEN
        ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL] THEN
        MATCH_MP_TAC PATH_SUBPATH] THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                   LE_1; REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC];
    SUBGOAL_THEN
     `(p(lift(&m / &N)):real^N) IN t /\ (p(lift(&n / &N)):real^N) IN t`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE;
                    PATHSTART_SUBPATH; PATHFINISH_SUBPATH; SUBSET];
      ALL_TAC] THEN
    UNDISCH_TAC `path_connected(s INTER t:real^N->bool)` THEN
    REWRITE_TAC[path_connected] THEN DISCH_THEN(MP_TAC o SPECL
     [`p(lift(&m / &N)):real^N`; `p(lift(&n / &N)):real^N`]) THEN
    ASM_REWRITE_TAC[IN_INTER; SUBSET_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^1->real^N` STRIP_ASSUME_TAC) THEN
    UNDISCH_THEN
     `!p. path p /\ path_image p SUBSET t /\ pathfinish p:real^N = pathstart p
          ==> homotopic_paths t p (linepath (pathstart p,pathstart p))`
     (MP_TAC o SPEC `subpath (lift(&m / &N)) (lift(&n / &N)) p ++
                     reversepath(r:real^1->real^N)`) THEN
    ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_REVERSEPATH] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SUBSET_PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH] THEN
      MATCH_MP_TAC PATH_JOIN_IMP THEN
      ASM_SIMP_TAC[PATH_REVERSEPATH; PATHFINISH_SUBPATH;
                   PATHSTART_REVERSEPATH] THEN
      MATCH_MP_TAC PATH_SUBPATH THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                   LE_1; REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
     DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS)) THEN
     ASM_REWRITE_TAC[PATHFINISH_LINEPATH; PATHSTART_SUBPATH;
       PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_REVERSEPATH] THEN
     DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_PATHS_LOOP_PARTS)) THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH) THEN
     REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
     REPLICATE_TAC 2 (DISCH_THEN(ASSUME_TAC o SYM)) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     EXISTS_TAC `(q:real^1->real^N) ++ r` THEN
     ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; UNION_SUBSET] THEN
     MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
     EXISTS_TAC `subpath (vec 0) (lift(&m / &N)) (p:real^1->real^N) ++
                 subpath (lift(&m / &N)) (lift(&n / &N)) p` THEN
     CONJ_TAC THENL
      [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
       MATCH_MP_TAC HOMOTOPIC_JOIN_SUBPATHS THEN
       ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
       ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
       ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                    LE_1; REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
       ASM_ARITH_TAC;
       MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
       ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
       MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN
       EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_UNION]]]);;

(* ------------------------------------------------------------------------- *)
(* Covering spaces and lifting results for them.                             *)
(* ------------------------------------------------------------------------- *)

let covering_space = new_definition
 `covering_space(c,(p:real^M->real^N)) s <=>
        p continuous_on c /\ IMAGE p c = s /\
        !x. x IN s
            ==> ?t. x IN t /\ open_in (subtopology euclidean s) t /\
                    ?v. UNIONS v = {x | x IN c /\ p(x) IN t} /\
                        (!u. u IN v ==> open_in (subtopology euclidean c) u) /\
                        pairwise DISJOINT v /\
                        (!u. u IN v ==> ?q. homeomorphism (u,t) (p,q))`;;

let COVERING_SPACE_IMP_CONTINUOUS = prove
 (`!p:real^M->real^N c s. covering_space (c,p) s ==> p continuous_on c`,
  SIMP_TAC[covering_space]);;

let COVERING_SPACE_IMP_SURJECTIVE = prove
 (`!p:real^M->real^N c s. covering_space (c,p) s ==> IMAGE p c = s`,
  SIMP_TAC[covering_space]);;

let HOMEOMORPHISM_IMP_COVERING_SPACE = prove
 (`!f:real^M->real^N g s t.
        homeomorphism (s,t) (f,g) ==> covering_space (s,f) t`,
  REWRITE_TAC[homeomorphism] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[covering_space] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `t:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
  EXISTS_TAC `{s:real^M->bool}` THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; UNIONS_1; PAIRWISE_SING] THEN
  ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `g:real^N->real^M`] THEN
  ASM_REWRITE_TAC[homeomorphism]);;

let COVERING_SPACE_LOCAL_HOMEOMORPHISM = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> !x. x IN c
                ==> ?t u. x IN t /\ open_in (subtopology euclidean c) t /\
                          p(x) IN u /\ open_in (subtopology euclidean s) u /\
                          ?q. homeomorphism (t,u) (p,q)`,
  REWRITE_TAC[covering_space] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^M->real^N) x`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^M) IN UNIONS v` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[IN_UNIONS]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^M->bool` THEN
  STRIP_TAC THEN EXISTS_TAC `t:real^N->bool` THEN ASM_SIMP_TAC[]);;

let COVERING_SPACE_LOCAL_HOMEOMORPHISM_ALT = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> !y. y IN s
                ==> ?x t u. p(x) = y /\
                            x IN t /\ open_in (subtopology euclidean c) t /\
                            y IN u /\ open_in (subtopology euclidean s) u /\
                            ?q. homeomorphism (t,u) (p,q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x. x IN c /\ (p:real^M->real^N) x = y` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:real^M` o MATCH_MP
     COVERING_SPACE_LOCAL_HOMEOMORPHISM) THEN
    ASM_MESON_TAC[]]);;

let COVERING_SPACE_OPEN_MAP = prove
 (`!p:real^M->real^N c s t.
        covering_space (c,p) s /\
        open_in (subtopology euclidean c) t
        ==> open_in (subtopology euclidean s) (IMAGE p t)`,
  REWRITE_TAC[covering_space] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:real^N` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `vs:(real^M->bool)->bool`
   (STRIP_ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN
   `?x. x IN {x | x IN c /\ (p:real^M->real^N) x IN u} /\ x IN t /\ p x = y`
  MP_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `v:real^M->bool`)) THEN
  ASM_REWRITE_TAC[homeomorphism] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:real^N->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (p:real^M->real^N) (t INTER v)` THEN CONJ_TAC THENL
   [ALL_TAC; ASM SET_TAC[]] THEN
  SUBGOAL_THEN
   `IMAGE (p:real^M->real^N) (t INTER v) =
    {z | z IN u /\ q z IN (t INTER v)}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_ON_OPEN]) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
  MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
  EXISTS_TAC `c:real^M->bool` THEN
  CONJ_TAC THENL [MATCH_MP_TAC OPEN_IN_INTER; ASM_MESON_TAC[open_in]] THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV]);;

let COVERING_SPACE_QUOTIENT_MAP = prove
 (`!p:real^M->real^N c s.
    covering_space (c,p) s
    ==> !u. u SUBSET s
            ==> (open_in (subtopology euclidean c) {x | x IN c /\ p x IN u} <=>
                 open_in (subtopology euclidean s) u)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  MATCH_MP_TAC OPEN_MAP_IMP_QUOTIENT_MAP THEN
  CONJ_TAC THENL [ASM_MESON_TAC[COVERING_SPACE_IMP_CONTINUOUS]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  ASM_MESON_TAC[COVERING_SPACE_OPEN_MAP]);;

let COVERING_SPACE_LOCALLY = prove
 (`!P Q p:real^M->real^N c s.
        covering_space (c,p) s /\ (!t. t SUBSET c /\ P t ==> Q(IMAGE p t)) /\
        locally P c
        ==> locally Q s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  MATCH_MP_TAC LOCALLY_OPEN_MAP_IMAGE THEN
  EXISTS_TAC `P:(real^M->bool)->bool` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[COVERING_SPACE_IMP_CONTINUOUS]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  ASM_MESON_TAC[COVERING_SPACE_OPEN_MAP]);;

let COVERING_SPACE_LOCALLY_EQ = prove
 (`!P Q p:real^M->real^N c s.
        covering_space (c,p) s /\
        (!t. t SUBSET c /\ P t ==> Q(IMAGE p t)) /\
        (!q u. u SUBSET s /\ q continuous_on u /\ Q u ==> P(IMAGE q u))

        ==> (locally Q s <=> locally P c)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[COVERING_SPACE_LOCALLY]] THEN
  REWRITE_TAC[locally] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`v:real^M->bool`; `x:real^M`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [covering_space]) THEN
  DISCH_THEN(MP_TAC o SPEC `(p:real^M->real^N) x` o last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[covering_space; FUN_IN_IMAGE; OPEN_IN_IMP_SUBSET; SUBSET];
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` MP_TAC)] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:real^M->bool` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M->bool`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`IMAGE (p:real^M->real^N) (u INTER v)`; `(p:real^M->real^N) x`]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; IN_INTER] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[COVERING_SPACE_OPEN_MAP; OPEN_IN_INTER]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool`
   (X_CHOOSE_THEN `w':real^N->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:real^N->real^M` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (q:real^N->real^M) w` THEN
  EXISTS_TAC `IMAGE (q:real^N->real^M) w'` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`p:real^M->real^N`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[homeomorphism] THEN

    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
    ASM SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
      ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC[]];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let COVERING_SPACE_LOCALLY_COMPACT_EQ = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> (locally compact s <=> locally compact c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COVERING_SPACE_LOCALLY_EQ THEN
  EXISTS_TAC `p:real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[covering_space]) THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; COMPACT_CONTINUOUS_IMAGE]);;

let COVERING_SPACE_LOCALLY_CONNECTED_EQ = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> (locally connected s <=> locally connected c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COVERING_SPACE_LOCALLY_EQ THEN
  EXISTS_TAC `p:real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[covering_space]) THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; CONNECTED_CONTINUOUS_IMAGE]);;

let COVERING_SPACE_LOCALLY_PATH_CONNECTED_EQ = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> (locally path_connected s <=> locally path_connected c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COVERING_SPACE_LOCALLY_EQ THEN
  EXISTS_TAC `p:real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[covering_space]) THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; PATH_CONNECTED_CONTINUOUS_IMAGE]);;

let COVERING_SPACE_LOCALLY_COMPACT = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ locally compact c
        ==> locally compact s`,
  MESON_TAC[COVERING_SPACE_LOCALLY_COMPACT_EQ]);;

let COVERING_SPACE_LOCALLY_CONNECTED = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ locally connected c ==> locally connected s`,
  MESON_TAC[COVERING_SPACE_LOCALLY_CONNECTED_EQ]);;

let COVERING_SPACE_LOCALLY_PATH_CONNECTED = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ locally path_connected c
        ==> locally path_connected s`,
  MESON_TAC[COVERING_SPACE_LOCALLY_PATH_CONNECTED_EQ]);;

let COVERING_SPACE_LIFT_UNIQUE_GEN = prove
 (`!p:real^M->real^N f:real^P->real^N g1 g2 c s t u a x.
        covering_space (c,p) s /\
        f continuous_on t /\ IMAGE f t SUBSET s /\
        g1 continuous_on t /\ IMAGE g1 t SUBSET c /\
        (!x. x IN t ==> f(x) = p(g1 x)) /\
        g2 continuous_on t /\ IMAGE g2 t SUBSET c /\
        (!x. x IN t ==> f(x) = p(g2 x)) /\
        u IN components t /\ a IN u /\ g1(a) = g2(a) /\ x IN u
        ==> g1(x) = g2(x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  UNDISCH_TAC `(x:real^P) IN u` THEN SPEC_TAC(`x:real^P`,`x:real^P`) THEN
  MATCH_MP_TAC(SET_RULE
   `(?a. a IN u /\ g a = z) /\
    ({x | x IN u /\ g x = z} = {} \/ {x | x IN u /\ g x = z} = u)
    ==> !x. x IN u ==> g x = z`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[VECTOR_SUB_EQ]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^P` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `(g1:real^P->real^M) x` o
        MATCH_MP COVERING_SPACE_LOCAL_HOMEOMORPHISM) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`v:real^M->bool`; `w:real^N->bool`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_SUB_EQ]) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->real^M` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{x | x IN u /\ (g1:real^P->real^M) x IN v} INTER
                {x | x IN u /\ (g2:real^P->real^M) x IN v}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ONCE_REWRITE_TAC[SET_RULE
       `{x | x IN u /\ g x IN v} =
        {x | x IN u /\ g x IN (v INTER IMAGE g u)}`] THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_IMP_OPEN_IN THEN
      (CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC]) THEN
      UNDISCH_TAC `open_in (subtopology euclidean c) (v:real^M->bool)` THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER; VECTOR_SUB_EQ] THEN
      ASM SET_TAC[]];
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]]);;

let COVERING_SPACE_LIFT_UNIQUE = prove
 (`!p:real^M->real^N f:real^P->real^N g1 g2 c s t a x.
        covering_space (c,p) s /\
        f continuous_on t /\ IMAGE f t SUBSET s /\
        g1 continuous_on t /\ IMAGE g1 t SUBSET c /\
        (!x. x IN t ==> f(x) = p(g1 x)) /\
        g2 continuous_on t /\ IMAGE g2 t SUBSET c /\
        (!x. x IN t ==> f(x) = p(g2 x)) /\
        connected t /\ a IN t /\ g1(a) = g2(a) /\ x IN t
        ==> g1(x) = g2(x)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`p:real^M->real^N`; `f:real^P->real^N`;
    `g1:real^P->real^M`; `g2:real^P->real^M`;
    `c:real^M->bool`; `s:real^N->bool`; `t:real^P->bool`; `t:real^P->bool`;
    `a:real^P`; `x:real^P`] COVERING_SPACE_LIFT_UNIQUE_GEN) THEN
  ASM_REWRITE_TAC[IN_COMPONENTS_SELF] THEN ASM SET_TAC[]);;

let COVERING_SPACE_LIFT_UNIQUE_IDENTITY = prove
 (`!p:real^M->real^N c f s a.
     covering_space (c,p) s /\
     path_connected c /\
     f continuous_on c /\ IMAGE f c SUBSET c /\
     (!x. x IN c ==> p(f x) = p x) /\
     a IN c /\ f(a) = a
     ==> !x. x IN c ==> f x = x`,
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `x:real^M`]) THEN
  ASM_REWRITE_TAC[path; path_image; pathstart; pathfinish] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`p:real^M->real^N`; `(p:real^M->real^N) o (g:real^1->real^M)`;
    `(f:real^M->real^M) o (g:real^1->real^M)`; `g:real^1->real^M`;
    `c:real^M->bool`; `s:real^N->bool`;
    `interval[vec 0:real^1,vec 1]`;
    `vec 0:real^1`; `vec 1:real^1`]
   COVERING_SPACE_LIFT_UNIQUE) THEN
  ASM_REWRITE_TAC[o_THM; IMAGE_o] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; CONNECTED_INTERVAL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [covering_space]) THEN
  STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SET_RULE
   `IMAGE p c = s ==> !x. x IN c ==> p(x) IN s`)) THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]);;

let COVERING_SPACE_LIFT_HOMOTOPY = prove
 (`!p:real^M->real^N c s (h:real^(1,P)finite_sum->real^N) f u.
        covering_space (c,p) s /\
        h continuous_on (interval[vec 0,vec 1] PCROSS u) /\
        IMAGE h (interval[vec 0,vec 1] PCROSS u) SUBSET s /\
        (!y. y IN u ==> h (pastecart (vec 0) y) = p(f y)) /\
        f continuous_on u /\ IMAGE f u SUBSET c
        ==> ?k. k continuous_on (interval[vec 0,vec 1] PCROSS u) /\
                IMAGE k (interval[vec 0,vec 1] PCROSS u) SUBSET c /\
                (!y. y IN u ==> k(pastecart (vec 0) y) = f y) /\
                (!z. z IN interval[vec 0,vec 1] PCROSS u ==> h z = p(k z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN u
        ==> ?v. open_in (subtopology euclidean u) v /\ y IN v /\
                ?k:real^(1,P)finite_sum->real^M.
                    k continuous_on (interval[vec 0,vec 1] PCROSS v) /\
                    IMAGE k (interval[vec 0,vec 1] PCROSS v) SUBSET c /\
                    (!y. y IN v ==> k(pastecart (vec 0) y) = f y) /\
                    (!z. z IN interval[vec 0,vec 1] PCROSS v
                         ==> h z :real^N = p(k z))`
  MP_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [RIGHT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`v:real^P->real^P->bool`; `fs:real^P->real^(1,P)finite_sum->real^M`] THEN
    DISCH_THEN(LABEL_TAC "*") THEN
    MP_TAC(ISPECL
     [`fs:real^P->real^(1,P)finite_sum->real^M`;
      `(\x. interval[vec 0,vec 1] PCROSS (v x))
        :real^P->real^(1,P)finite_sum->bool`;
      `(interval[vec 0,vec 1] PCROSS u):real^(1,P)finite_sum->bool`;
      `u:real^P->bool`]
      PASTING_LEMMA_EXISTS) THEN
    ASM_SIMP_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `k:real^(1,P)finite_sum->real^M` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS; SUBSET] THEN
      REPEAT CONJ_TAC THEN TRY(X_GEN_TAC `t:real^1`) THEN
      X_GEN_TAC `y:real^P` THEN STRIP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL
         [`pastecart (t:real^1) (y:real^P)`; `y:real^P`]);
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`pastecart (vec 0:real^1) (y:real^P)`; `y:real^P`]);
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`pastecart (t:real^1) (y:real^P)`; `y:real^P`])] THEN
      ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_INTER; ENDS_IN_UNIT_INTERVAL] THEN
      DISCH_THEN SUBST1_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `y:real^P`) THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS]] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; UNIONS_GSPEC; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^P`] THEN STRIP_TAC THEN
      EXISTS_TAC `y:real^P` THEN ASM_SIMP_TAC[PASTECART_IN_PCROSS];
      X_GEN_TAC `y:real^P` THEN DISCH_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `y:real^P`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^P->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(:real^1) PCROSS (t:real^P->bool)` THEN
      ASM_SIMP_TAC[REWRITE_RULE[GSYM PCROSS] OPEN_PCROSS; OPEN_UNIV] THEN
      REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS;
                    IN_INTER; IN_UNIV] THEN
      REPEAT GEN_TAC THEN CONV_TAC TAUT;
      REWRITE_TAC[FORALL_PASTECART; IN_INTER; PASTECART_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC
       [`x:real^P`; `z:real^P`; `t:real^1`; `y:real^P`] THEN
      REWRITE_TAC[CONJ_ACI] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o
        ISPECL [`h:real^(1,P)finite_sum->real^N`;
                `(fs:real^P->real^(1,P)finite_sum->real^M) x`;
                `(fs:real^P->real^(1,P)finite_sum->real^M) z`;
                `interval[vec 0:real^1,vec 1] PCROSS {y:real^P}`;
                `pastecart (vec 0:real^1) (y:real^P)`;
                `pastecart (t:real^1) (y:real^P)`] o
        MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_UNIQUE)) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_SING; ENDS_IN_UNIT_INTERVAL] THEN
      SIMP_TAC[REWRITE_RULE[GSYM PCROSS] CONNECTED_PCROSS;
               CONNECTED_INTERVAL; CONNECTED_SING] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[FORALL_PASTECART; SUBSET; PASTECART_IN_PCROSS] THEN
        ASM_SIMP_TAC[IN_SING];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS)) THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[FORALL_PASTECART; SUBSET; PASTECART_IN_PCROSS] THEN
        ASM_SIMP_TAC[IN_SING];
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> (p /\ q /\ r) /\ s`] THEN
      CONJ_TAC THENL
       [REMOVE_THEN "*" (MP_TAC o SPEC `x:real^P`);
        REMOVE_THEN "*" (MP_TAC o SPEC `z:real^P`)] THEN
      ASM_REWRITE_TAC[FORALL_IN_GSPEC; SUBSET; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[FORALL_PASTECART; SUBSET; PASTECART_IN_PCROSS] THEN
      ASM_SIMP_TAC[IN_SING]]] THEN
  X_GEN_TAC `y:real^P` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o last o CONJUNCTS o
    GEN_REWRITE_RULE I [covering_space]) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `uu:real^N->real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!t. t IN interval[vec 0,vec 1]
        ==> ?k n i:real^N.
                open_in (subtopology euclidean (interval[vec 0,vec 1])) k /\
                open_in (subtopology euclidean u) n /\
                t IN k /\ y IN n /\ i IN s /\
                IMAGE (h:real^(1,P)finite_sum->real^N) (k PCROSS n) SUBSET uu i`
  MP_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^(1,P)finite_sum->real^N) (pastecart t y) IN s`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o ONCE_REWRITE_RULE[FORALL_IN_IMAGE] o
        GEN_REWRITE_RULE I [SUBSET]) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `open_in (subtopology euclidean (interval[vec 0,vec 1] PCROSS u))
              {z | z IN (interval[vec 0,vec 1] PCROSS u) /\
                   (h:real^(1,P)finite_sum->real^N) z IN
                   uu(h(pastecart t y))}`
    MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        PASTECART_IN_INTERIOR_SUBTOPOLOGY)) THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real^1`; `y:real^P`]) THEN
    ASM_SIMP_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^1->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:real^P->bool` THEN
    STRIP_TAC THEN
    EXISTS_TAC `(h:real^(1,P)finite_sum->real^N) (pastecart t y)` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [OPEN_IN_OPEN] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[MESON[]
   `(?x y. (P y /\ x = f y) /\ Q x) <=> ?y. P y /\ Q(f y)`] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`kk:real^1->real^1->bool`; `nn:real^1->real^P->bool`;
    `xx:real^1->real^N`] THEN
  DISCH_THEN(LABEL_TAC "+") THEN
  MP_TAC(ISPEC `interval[vec 0:real^1,vec 1] PCROSS {y:real^P}`
    COMPACT_IMP_HEINE_BOREL) THEN
  SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; COMPACT_SING] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE ((\i. kk i PCROSS nn i):real^1->real^(1,P)finite_sum->bool)
          (interval[vec 0,vec 1])`) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; OPEN_PCROSS] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; IN_SING] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `z:real^P`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; PASTECART_IN_PCROSS] THEN
    ASM_MESON_TAC[IN_INTER];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
    REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `tk:real^1->bool` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `n = INTERS (IMAGE (nn:real^1->real^P->bool) tk)` THEN
  SUBGOAL_THEN `(y:real^P) IN n /\ open n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN CONJ_TAC THENL
     [REWRITE_TAC[INTERS_IMAGE; IN_ELIM_THM];
      MATCH_MP_TAC OPEN_INTERS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[FINITE_IMAGE]] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REMOVE_THEN "+" (MP_TAC o SPEC `t:real^1`) THEN
    (ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[IN_INTER]]);
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`interval[vec 0:real^1,vec 1]`; `IMAGE (kk:real^1->real^1->bool) tk`]
   LEBESGUE_COVERING_LEMMA) THEN
  REWRITE_TAC[COMPACT_INTERVAL; FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
  MATCH_MP_TAC(TAUT
   `q /\ (p ==> ~q) /\ (q ==> (r ==> s) ==> t)
    ==> (~p /\ q /\ r ==> s) ==> t`) THEN
  SIMP_TAC[UNIONS_0; IMAGE_CLAUSES; SUBSET_EMPTY; UNIT_INTERVAL_NONEMPTY] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [UNIONS_IMAGE]) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; IMP_CONJ; IN_SING] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; PASTECART_IN_PCROSS] THEN
    MESON_TAC[];
    DISCH_TAC] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `d:real` REAL_ARCH_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. n <= N
        ==> ?v k:real^(1,P)finite_sum->real^M.
                open_in (subtopology euclidean u) v /\
                y IN v /\
                k continuous_on interval[vec 0,lift(&n / &N)] PCROSS v /\
                IMAGE k (interval[vec 0,lift(&n / &N)] PCROSS v) SUBSET c /\
                (!y. y IN v ==> k (pastecart (vec 0) y) = f y) /\
                (!z. z IN interval[vec 0,lift(&n / &N)] PCROSS v
                     ==> h z:real^N = p (k z))`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_OF_NUM_EQ; LIFT_NUM]] THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[real_div; REAL_MUL_LZERO; LIFT_NUM] THEN
    EXISTS_TAC `u:real^P->bool` THEN
    EXISTS_TAC `(f o sndcart):real^(1,P)finite_sum->real^M` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; INTERVAL_SING] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_SING; o_THM] THEN
    ASM_REWRITE_TAC[FORALL_UNWIND_THM2; SNDCART_PASTECART] THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    SIMP_TAC[SNDCART_PASTECART];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN ASM_CASES_TAC `SUC m <= N` THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC m <= N ==> m <= N`; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`v:real^P->bool`; `k:real^(1,P)finite_sum->real^M`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC o SPEC `interval[lift(&m / &N),lift(&(SUC m) / &N)]`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIAMETER_INTERVAL; SUBSET_INTERVAL_1] THEN
    REWRITE_TAC[LIFT_DROP; DROP_VEC; INTERVAL_EQ_EMPTY_1;
                GSYM LIFT_SUB; NORM_LIFT] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ; REAL_OF_NUM_LT; LE_1;
                 REAL_FIELD `&0 < x ==> a / x - b / x = (a - b) / x`] THEN
    SIMP_TAC[GSYM NOT_LE; ARITH_RULE `m <= SUC m`; REAL_OF_NUM_SUB] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_LE_DIV; REAL_POS;
                 REAL_ABS_NUM; ARITH_RULE `SUC m - m = 1`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 / n = inv(n)`; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    ASM_REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "+" (MP_TAC o SPEC `t:real^1`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(xx:real^1->real^N) t`) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:(real^M->bool)->bool` MP_TAC) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC
   `(k:real^(1,P)finite_sum->real^M) (pastecart (lift(&m / &N)) y)`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC(TAUT
   `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [IN_INTER])) THEN
  SUBGOAL_THEN
   `lift(&m / &N) IN interval[vec 0,lift (&m / &N)] /\
    lift(&m / &N) IN interval[lift(&m / &N),lift(&(SUC m) / &N)]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; LE_1; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart(lift(&m / &N)) (y:real^P)`) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (SET_RULE `IMAGE h s SUBSET t ==> x IN s ==> h x IN t`)) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTER] THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_DIV; REAL_LE_LDIV_EQ;
                 REAL_POS; REAL_OF_NUM_LT; LE_1; DROP_VEC] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `w:real^M->bool`) MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^M->bool` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `p':real^N->real^M`) THEN
    DISCH_TAC THEN UNDISCH_THEN `(w:real^M->bool) IN vv` (K ALL_TAC)] THEN
  ABBREV_TAC `w' = (uu:real^N->real^N->bool)(xx(t:real^1))` THEN
  SUBGOAL_THEN
   `?n'. open_in (subtopology euclidean u) n' /\ y IN n' /\
         IMAGE (k:real^(1,P)finite_sum->real^M) ({lift(&m / &N)} PCROSS n')
         SUBSET w`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `{z | z IN v /\ ((k:real^(1,P)finite_sum->real^M) o
                     pastecart (lift(&m / &N))) z IN w}` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IN_SING; o_THM] THEN
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `v:real^P->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `c:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
               CONTINUOUS_ON_ID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET));
      REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`))] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?q q':real^P->bool.
        open_in (subtopology euclidean u) q /\
        closed_in (subtopology euclidean u) q' /\
        y IN q /\ y IN q' /\ q SUBSET q' /\
        q SUBSET (u INTER nn(t:real^1)) INTER n' INTER v /\
        q' SUBSET (u INTER nn(t:real^1)) INTER n' INTER v`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE
     `y IN q /\ y IN q' /\ q SUBSET q' /\ q SUBSET s /\ q' SUBSET s <=>
      y IN q /\ q SUBSET q' /\ q' SUBSET s`] THEN
    UNDISCH_TAC `open_in (subtopology euclidean u) (v:real^P->bool)` THEN
    UNDISCH_TAC `open_in (subtopology euclidean u) (n':real^P->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `vo:real^P->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `vx:real^P->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `nn(t:real^1) INTER vo INTER vx:real^P->bool`
      OPEN_CONTAINS_CBALL) THEN
    ASM_SIMP_TAC[OPEN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `y:real^P`) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u INTER ball(y:real^P,e)` THEN
    EXISTS_TAC `u INTER cball(y:real^P,e)` THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN
    CONJ_TAC THENL [MESON_TAC[OPEN_BALL]; ALL_TAC] THEN
    CONJ_TAC THENL [MESON_TAC[CLOSED_CBALL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN
    MP_TAC(ISPECL [`y:real^P`; `e:real`] BALL_SUBSET_CBALL) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  EXISTS_TAC `q:real^P->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`\x:real^(1,P)finite_sum.
       x IN interval[vec 0,lift(&m / &N)] PCROSS (q':real^P->bool)`;
    `k:real^(1,P)finite_sum->real^M`;
    `(p':real^N->real^M) o (h:real^(1,P)finite_sum->real^N)`;
    `interval[vec 0,lift(&m / &N)] PCROSS (q':real^P->bool)`;
    `interval[lift(&m / &N),lift(&(SUC m) / &N)] PCROSS (q':real^P->bool)`]
   CONTINUOUS_ON_CASES_LOCAL) THEN
  REWRITE_TAC[TAUT `~(p /\ ~p)`] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CLOSED_IN_CLOSED] THEN
      EXISTS_TAC `interval[vec 0,lift(&m / &N)] PCROSS (:real^P)` THEN
      SIMP_TAC[CLOSED_PCROSS; CLOSED_INTERVAL; CLOSED_UNIV] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; FORALL_PASTECART] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN CONV_TAC TAUT;
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC
       `interval[lift(&m / &N),lift(&(SUC m) / &N)] PCROSS (:real^P)` THEN
      SIMP_TAC[CLOSED_PCROSS; CLOSED_INTERVAL; CLOSED_UNIV] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; FORALL_PASTECART] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN CONV_TAC TAUT;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET))
      THENL
       [ALL_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`))] THEN
      MATCH_MP_TAC PCROSS_MONO THEN
      (CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]]) THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC;
                      SUBSET_INTER] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_DIV2_EQ; REAL_OF_NUM_LT;
                   LE_1] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1;
                   REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      DISJ2_TAC THEN ARITH_TAC;
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `z:real^P`] THEN
      ASM_CASES_TAC `(z:real^P) IN q'` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN DISCH_THEN(MP_TAC o MATCH_MP
       (REAL_ARITH `(b <= x /\ x <= c) /\ (a <= x /\ x <= b) ==> x = b`)) THEN
      REWRITE_TAC[DROP_EQ; o_THM] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
       `(!x. x IN w ==> p' (p x) = x)
        ==> h z = p(k z) /\ k z IN w
            ==> k z = p' (h z)`)) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING] THEN ASM SET_TAC[]]];
    SUBGOAL_THEN
     `interval[vec 0,lift(&m / &N)] UNION
      interval [lift(&m / &N),lift(&(SUC m) / &N)] =
      interval[vec 0,lift(&(SUC m) / &N)]`
    ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1] THEN GEN_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b /\ b <= c ==>
       (a <= x /\ x <= b \/ b <= x /\ x <= c <=> a <= x /\ x <= c)`) THEN
      SIMP_TAC[LIFT_DROP; DROP_VEC; REAL_LE_DIV; REAL_POS] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LT; REAL_OF_NUM_LE; LE_1] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `interval[vec 0,lift(&m / &N)] PCROSS (q':real^P->bool) UNION
      interval [lift(&m / &N),lift(&(SUC m) / &N)] PCROSS q' =
      interval[vec 0,lift(&(SUC m) / &N)] PCROSS q'`
    SUBST1_TAC THENL
     [SIMP_TAC[EXTENSION; IN_UNION; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[CONTINUOUS_ON_SUBSET]
     `t SUBSET s /\ (f continuous_on s ==> P f)
      ==> f continuous_on s ==> ?g. g continuous_on t /\ P g`) THEN
    ASM_SIMP_TAC[PCROSS_MONO; SUBSET_REFL] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `z:real^P`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^P) IN q'` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[PASTECART_IN_PCROSS]] THEN
      COND_CASES_TAC THEN REWRITE_TAC[o_THM] THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING] THEN ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
          CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `IMAGE p w' = w ==> x IN w' ==> p x IN w`))];
      X_GEN_TAC `z:real^P` THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN
      DISCH_TAC THEN REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL] THEN
      SUBGOAL_THEN `(z:real^P) IN q'` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[LIFT_DROP; DROP_VEC]] THEN
      SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN ASM SET_TAC[];
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `z:real^P`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^P) IN q'` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM SET_TAC[];
        REWRITE_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM MATCH_MP_TAC]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (SET_RULE `IMAGE h s SUBSET t ==> x IN s ==> h x IN t`)) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTER] THEN
    REPEAT(CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REAL_ARITH `a <= x /\ x <= b ==> b <= c ==> a <= x /\ x <= c`)) THEN
    ASM_SIMP_TAC[LIFT_DROP; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    ASM_REWRITE_TAC[DROP_VEC; REAL_MUL_LID; REAL_OF_NUM_LE]]);;

let COVERING_SPACE_LIFT_HOMOTOPIC_FUNCTION = prove
 (`!p:real^M->real^N c s f f' g u:real^P->bool.
        covering_space (c,p) s /\
        g continuous_on u /\ IMAGE g u SUBSET c /\
        (!y. y IN u ==> p(g y) = f y) /\
        homotopic_with (\x. T) (u,s) f f'
        ==> ?g'. g' continuous_on u /\ IMAGE g' u SUBSET c /\
                 (!y. y IN u ==> p(g' y) = f' y)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `h:real^(1,P)finite_sum->real^N`
    STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  FIRST_ASSUM(MP_TAC o
    ISPECL [`h:real^(1,P)finite_sum->real^N`;
            `g:real^P->real^M`; `u:real^P->bool`] o
    MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_HOMOTOPY)) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^(1,P)finite_sum->real^M`
        STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(k:real^(1,P)finite_sum->real^M) o
              (\x. pastecart (vec 1) x)` THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
             CONTINUOUS_ON_ID] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS;
                ENDS_IN_UNIT_INTERVAL];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS;
                ENDS_IN_UNIT_INTERVAL];
    ASM_MESON_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL]]);;

let COVERING_SPACE_LIFT_INESSENTIAL_FUNCTION = prove
 (`!p:real^M->real^N c s f a u:real^P->bool.
        covering_space (c,p) s /\ homotopic_with (\x. T) (u,s) f (\x. a)
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\
                (!y. y IN u ==> p(g y) = f y)`,
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `u:real^P->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; IMAGE_CLAUSES; EMPTY_SUBSET;
                  CONTINUOUS_ON_EMPTY] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE
     [TAUT `a /\ b /\ c /\ d /\ e ==> f <=> a /\ e ==> b /\ c /\ d ==> f`]
     COVERING_SPACE_LIFT_HOMOTOPIC_FUNCTION)) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  SUBGOAL_THEN `?b. b IN c /\ (p:real^M->real^N) b = a` CHOOSE_TAC THENL
   [ASM SET_TAC[];
    EXISTS_TAC `(\x. b):real^P->real^M`] THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[]);;

let COVERING_SPACE_LIFT_HOMOTOPY_ALT = prove
 (`!p:real^M->real^N c s (h:real^(P,1)finite_sum->real^N) f u.
        covering_space (c,p) s /\
        h continuous_on (u PCROSS interval[vec 0,vec 1]) /\
        IMAGE h (u PCROSS interval[vec 0,vec 1]) SUBSET s /\
        (!y. y IN u ==> h (pastecart y (vec 0)) = p(f y)) /\
        f continuous_on u /\ IMAGE f u SUBSET c
        ==> ?k. k continuous_on (u PCROSS interval[vec 0,vec 1]) /\
                IMAGE k (u PCROSS interval[vec 0,vec 1]) SUBSET c /\
                (!y. y IN u ==> k(pastecart y (vec 0)) = f y) /\
                (!z. z IN u PCROSS interval[vec 0,vec 1] ==> h z = p(k z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPECL
   [`(h:real^(P,1)finite_sum->real^N) o
     (\z. pastecart (sndcart z) (fstcart z))`;
    `f:real^P->real^M`; `u:real^P->bool`] o
      MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_HOMOTOPY)) THEN
  ASM_SIMP_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; LINEAR_CONTINUOUS_ON;
               LINEAR_FSTCART; LINEAR_SNDCART] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET));
      REWRITE_TAC[IMAGE_o] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`))] THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; FORALL_IN_PCROSS;
             FSTCART_PASTECART; SNDCART_PASTECART];
    DISCH_THEN(X_CHOOSE_THEN `k:real^(1,P)finite_sum->real^M`
        STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(k:real^(1,P)finite_sum->real^M) o
                (\z. pastecart (sndcart z) (fstcart z))` THEN
    ASM_SIMP_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                 FORALL_IN_PCROSS; PASTECART_IN_PCROSS] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; LINEAR_CONTINUOUS_ON;
               LINEAR_FSTCART; LINEAR_SNDCART] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET));
      REWRITE_TAC[IMAGE_o] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`));
      MAP_EVERY X_GEN_TAC [`x:real^P`; `t:real^1`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (t:real^1) (x:real^P)`)] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS;
                 FSTCART_PASTECART; SNDCART_PASTECART; FORALL_IN_PCROSS]]);;

let COVERING_SPACE_LIFT_PATH_STRONG = prove
 (`!p:real^M->real^N c s g a.
     covering_space (c,p) s /\
     path g /\ path_image g SUBSET s /\ pathstart g = p(a) /\ a IN c
     ==> ?h. path h /\ path_image h SUBSET c /\ pathstart h = a /\
             !t. t IN interval[vec 0,vec 1] ==> p(h t) = g t`,
  REWRITE_TAC[path_image; path; pathstart] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o
    ISPECL [`(g:real^1->real^N) o (fstcart:real^(1,P)finite_sum->real^1)`;
            `(\y. a):real^P->real^M`; `{arb:real^P}`] o
    MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_HOMOTOPY)) THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; o_THM; FSTCART_PASTECART] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o; CONTINUOUS_ON_CONST] THEN
    ASM_REWRITE_TAC[SET_RULE `IMAGE (\y. a) {b} SUBSET s <=> a IN s`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_FSTCART; LINEAR_CONTINUOUS_ON] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET));
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    SIMP_TAC[FSTCART_PASTECART] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `k:real^(1,P)finite_sum->real^M`
        STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(k:real^(1,P)finite_sum->real^M) o (\t. pastecart t arb)` THEN
    ASM_REWRITE_TAC[o_THM; IMAGE_o] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART;
               CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_SING];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`)) THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_SING];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (t:real^1) (arb:real^P)`) THEN
      ASM_SIMP_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; IN_SING]]]);;

let COVERING_SPACE_LIFT_PATH = prove
 (`!p:real^M->real^N c s g.
     covering_space (c,p) s /\ path g /\ path_image g SUBSET s
     ==> ?h. path h /\ path_image h SUBSET c /\
             !t. t IN interval[vec 0,vec 1] ==> p(h t) = g t`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `IMAGE g i SUBSET s ==> vec 0 IN i ==> g(vec 0) IN s`) o
   GEN_REWRITE_RULE LAND_CONV [path_image]) THEN
  REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real^M` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^M->real^N`; `c:real^M->bool`; `s:real^N->bool`;
                `g:real^1->real^N`; `a:real^M`]
    COVERING_SPACE_LIFT_PATH_STRONG) THEN
  ASM_REWRITE_TAC[pathstart] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let COVERING_SPACE_LIFT_HOMOTOPIC_PATHS = prove
 (`!p:real^M->real^N c s g1 g2 h1 h2.
     covering_space (c,p) s /\
     path g1 /\ path_image g1 SUBSET s /\
     path g2 /\ path_image g2 SUBSET s /\
     homotopic_paths s g1 g2 /\
     path h1 /\ path_image h1 SUBSET c /\
     (!t. t IN interval[vec 0,vec 1] ==> p(h1 t) = g1 t) /\
     path h2 /\ path_image h2 SUBSET c /\
     (!t. t IN interval[vec 0,vec 1] ==> p(h2 t) = g2 t) /\
     pathstart h1 = pathstart h2
     ==> homotopic_paths c h1 h2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMOTOPIC_PATHS] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_paths]) THEN
  REWRITE_TAC[homotopic_with; pathstart; pathfinish] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `h:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o ISPECL
   [`h:real^(1,1)finite_sum->real^N`; `(\x. pathstart h2):real^1->real^M`;
    `interval[vec 0:real^1,vec 1]`] o
   MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_HOMOTOPY_ALT)) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_CONST; SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[pathstart; ENDS_IN_UNIT_INTERVAL; PATHSTART_IN_PATH_IMAGE;
                  SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^(1,1)finite_sum->real^M` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[o_DEF] THEN
  MATCH_MP_TAC(TAUT `(p /\ q) /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o
      REWRITE_RULE[RIGHT_FORALL_IMP_THM] o
      ONCE_REWRITE_RULE[IMP_CONJ] o
      REWRITE_RULE[CONJ_ASSOC] o MATCH_MP
       (ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_UNIQUE)) THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THENL
     [MAP_EVERY EXISTS_TAC [`g1:real^1->real^N`; `vec 0:real^1`];
      MAP_EVERY EXISTS_TAC [`g2:real^1->real^N`; `vec 0:real^1`]] THEN
    ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_image; pathstart; pathfinish; path]) THEN
    ASM_REWRITE_TAC[CONNECTED_INTERVAL; pathstart; pathfinish] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN
    (REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
               CONTINUOUS_ON_ID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET));
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
      REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`));
      ASM_MESON_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL]] THEN
     SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; FORALL_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART; ENDS_IN_UNIT_INTERVAL]);
     STRIP_TAC THEN
     REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM] THEN CONJ_TAC THENL
      [ASM_MESON_TAC[pathstart; ENDS_IN_UNIT_INTERVAL]; ALL_TAC] THEN
     FIRST_ASSUM(MATCH_MP_TAC o
      REWRITE_RULE[RIGHT_FORALL_IMP_THM] o
      ONCE_REWRITE_RULE[IMP_CONJ] o
      REWRITE_RULE[CONJ_ASSOC] o MATCH_MP
       (ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_UNIQUE)) THEN
     MAP_EVERY EXISTS_TAC
      [`(\x. pathfinish g1):real^1->real^N`; `vec 0:real^1`] THEN
     ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL; CONNECTED_INTERVAL] THEN
     REWRITE_TAC[CONTINUOUS_ON_CONST; pathfinish] THEN
     REPEAT CONJ_TAC THENL
      [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
       ASM_MESON_TAC[SUBSET; pathfinish; PATHFINISH_IN_PATH_IMAGE];
       GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
       MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
       SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
                CONTINUOUS_ON_ID] THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
           CONTINUOUS_ON_SUBSET)) THEN
       SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; FORALL_IN_PCROSS;
                FSTCART_PASTECART; SNDCART_PASTECART; ENDS_IN_UNIT_INTERVAL];
       REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
       X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (t:real^1) (vec 1:real^1)` o
         REWRITE_RULE[FORALL_IN_IMAGE] o GEN_REWRITE_RULE I [SUBSET]) THEN
       ASM_REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL];
       ASM_MESON_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL];
       REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
       ASM_MESON_TAC[SUBSET; pathfinish; PATHFINISH_IN_PATH_IMAGE]]]);;

let COVERING_SPACE_MONODROMY = prove
 (`!p:real^M->real^N c s g1 g2 h1 h2.
     covering_space (c,p) s /\
     path g1 /\ path_image g1 SUBSET s /\
     path g2 /\ path_image g2 SUBSET s /\
     homotopic_paths s g1 g2 /\
     path h1 /\ path_image h1 SUBSET c /\
     (!t. t IN interval[vec 0,vec 1] ==> p(h1 t) = g1 t) /\
     path h2 /\ path_image h2 SUBSET c /\
     (!t. t IN interval[vec 0,vec 1] ==> p(h2 t) = g2 t) /\
     pathstart h1 = pathstart h2
     ==> pathfinish h1 = pathfinish h2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP COVERING_SPACE_LIFT_HOMOTOPIC_PATHS) THEN
  REWRITE_TAC[HOMOTOPIC_PATHS_IMP_PATHFINISH]);;

let COVERING_SPACE_LIFT_HOMOTOPIC_PATH = prove
 (`!p:real^M->real^N c s f f' g a b.
        covering_space (c,p) s /\
        homotopic_paths s f f' /\
        path g /\ path_image g SUBSET c /\
        pathstart g = a /\ pathfinish g = b /\
        (!t. t IN interval[vec 0,vec 1] ==> p(g t) = f t)
        ==> ?g'. path g' /\ path_image g' SUBSET c /\
                 pathstart g' = a /\ pathfinish g' = b /\
                 (!t. t IN interval[vec 0,vec 1] ==> p(g' t) = f' t)`,
  ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_SUBSET) THEN
  FIRST_ASSUM(MP_TAC o ISPECL [`f':real^1->real^N`; `a:real^M`] o
   MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_PATH_STRONG)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[pathstart; ENDS_IN_UNIT_INTERVAL;
                    HOMOTOPIC_PATHS_IMP_PATHSTART];
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g':real^1->real^M` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `pathfinish g:real^M = b`)) THEN
    FIRST_ASSUM(MATCH_MP_TAC o
     MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_MONODROMY)) THEN
    MAP_EVERY EXISTS_TAC [`f':real^1->real^N`; `f:real^1->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let COVERING_SPACE_INESSENTIAL_LOOP_LIFT_IS_LOOP = prove
 (`!p:real^M->real^N c s g h a.
        covering_space (c,p) s /\
        path g /\ path_image g SUBSET s /\ pathfinish g = pathstart g /\
        homotopic_paths s g (linepath(a,a)) /\
        path h /\ path_image h SUBSET c /\
        (!t. t IN interval[vec 0,vec 1] ==> p(h t) = g t)
        ==> pathfinish h = pathstart h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_SUBSET) THEN
  REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
  REWRITE_TAC[PATHSTART_LINEPATH] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    ISPECL [`g:real^1->real^N`; `linepath(a:real^N,a)`;
            `h:real^1->real^M`; `linepath(pathstart h:real^M,pathstart h)`] o
    MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_MONODROMY)) THEN
  ASM_REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
  ASM_REWRITE_TAC[SING_SUBSET; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LINEPATH_REFL] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[pathstart] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]]);;

let COVERING_SPACE_SIMPLY_CONNECTED_LOOP_LIFT_IS_LOOP = prove
 (`!p:real^M->real^N c s g h.
        covering_space (c,p) s /\ simply_connected s /\
        path g /\ path_image g SUBSET s /\ pathfinish g = pathstart g /\
        path h /\ path_image h SUBSET c /\
        (!t. t IN interval[vec 0,vec 1] ==> p(h t) = g t)
        ==> pathfinish h = pathstart h`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o
    MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_INESSENTIAL_LOOP_LIFT_IS_LOOP)) THEN
  EXISTS_TAC `g:real^1->real^N` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_PATH]);;

(* ------------------------------------------------------------------------- *)
(* Lifting of general functions to covering space                            *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_LIFT_GENERAL = prove
 (`!p:real^M->real^N c s f:real^P->real^N u a z.
        covering_space (c,p) s /\ a IN c /\ z IN u /\
        path_connected u /\ locally path_connected u /\
        f continuous_on u /\ IMAGE f u SUBSET s /\ f z = p a /\
        (!r. path r /\ path_image r SUBSET u /\
             pathstart r = z /\ pathfinish r = z
             ==> ?q. path q /\ path_image q SUBSET c /\
                     pathstart q = a /\ pathfinish q = a /\
                     homotopic_paths s (f o r) (p o q))
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\ g z = a /\
                (!y. y IN u ==> p(g y) = f y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN u
        ==> ?g h. path g /\ path_image g SUBSET u /\
                  pathstart g = z /\ pathfinish g = y /\
                  path h /\ path_image h SUBSET c /\ pathstart h = a /\
                  (!t. t IN interval[vec 0,vec 1]
                       ==> (p:real^M->real^N)(h t) = (f:real^P->real^N)(g t))`
   (LABEL_TAC "*")
  THENL
   [X_GEN_TAC `y:real^P` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
    DISCH_THEN(MP_TAC o SPECL [`z:real^P`; `y:real^P`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `g:real^1->real^P` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC  COVERING_SPACE_LIFT_PATH_STRONG THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[GSYM o_DEF] THEN
    ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE; PATHSTART_COMPOSE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?l. !y g h. path g /\ path_image g SUBSET u /\
                pathstart g = z /\ pathfinish g = y /\
                path h /\ path_image h SUBSET c /\ pathstart h = a /\
                (!t. t IN interval[vec 0,vec 1]
                     ==> (p:real^M->real^N)(h t) = (f:real^P->real^N)(g t))
                ==> pathfinish h = l y`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `y:real^P` THEN
    MATCH_MP_TAC(MESON[]
      `(!g h g' h'. P g h /\ P g' h' ==> f h = f h')
       ==> ?z. !g h. P g h ==> f h = z`) THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g ++ reversepath g'):real^1->real^P`) THEN
    ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
      PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
      SUBSET_PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^M` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o
     ISPECL [`(p:real^M->real^N) o (q:real^1->real^M)`;
             `(f:real^P->real^N) o (g ++ reversepath g')`;
             `q:real^1->real^M`; `pathstart q:real^M`; `pathfinish q:real^M`] o
      MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ]
       (ONCE_REWRITE_RULE[HOMOTOPIC_PATHS_SYM]
         COVERING_SPACE_LIFT_HOMOTOPIC_PATH))) THEN
    ASM_REWRITE_TAC[o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `q':real^1->real^M` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `path(h ++ reversepath h':real^1->real^M)` MP_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[PATH_JOIN_EQ; PATH_REVERSEPATH; PATHSTART_REVERSEPATH]] THEN
    MATCH_MP_TAC PATH_EQ THEN EXISTS_TAC `q':real^1->real^M` THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    STRIP_TAC THEN REWRITE_TAC[joinpaths] THEN COND_CASES_TAC THENL
     [FIRST_ASSUM(MP_TAC o
        ISPECL [`(f:real^P->real^N) o (g:real^1->real^P) o (\t. &2 % t)`;
                `q':real^1->real^M`;
                `(h:real^1->real^M) o (\t. &2 % t)`;
                `interval[vec 0,lift(&1 / &2)]`;
                `vec 0:real^1`; `t:real^1`] o
        MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_UNIQUE)) THEN
      REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
        EXISTS_TAC `(f:real^P->real^N) o (g ++ reversepath g')` THEN
        CONJ_TAC THENL
         [SIMP_TAC[IN_INTERVAL_1; LIFT_DROP; joinpaths; o_THM];
          ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN CONJ_TAC THENL
         [ASM_MESON_TAC[HOMOTOPIC_PATHS_IMP_PATH; path];
          REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
          REAL_ARITH_TAC];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
         `path_image ((f:real^P->real^N) o (g ++ reversepath g'))` THEN
        CONJ_TAC THENL[ALL_TAC; ASM_MESON_TAC[HOMOTOPIC_PATHS_IMP_SUBSET]] THEN
        REWRITE_TAC[path_image] THEN MATCH_MP_TAC(SET_RULE
         `(!x. x IN s ==> f x = g x) /\ s SUBSET t
          ==> IMAGE f s SUBSET IMAGE g t`) THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC; IN_INTERVAL_1] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[joinpaths; o_THM];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        ASM_REWRITE_TAC[GSYM path] THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
         `path_image(q':real^1->real^M)` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[path_image] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `t':real^1` THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(fun th ->
         W(MP_TAC o PART_MATCH (lhand o rand) th o rand o snd)) THEN
        ASM_SIMP_TAC[IN_INTERVAL_1; joinpaths; DROP_VEC] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        ASM_SIMP_TAC[GSYM path] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; LIFT_DROP] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `path_image(h:real^1->real^M)` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
        REWRITE_TAC[path_image; IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
        REWRITE_TAC[DROP_VEC; DROP_CMUL; LIFT_DROP] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `t':real^1` THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN STRIP_TAC THEN
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[CONNECTED_INTERVAL];
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM pathstart] THEN
        ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(ASSUME `pathstart h:real^M = a`)) THEN
        REWRITE_TAC[pathstart] THEN AP_TERM_TAC THEN
        REWRITE_TAC[VECTOR_MUL_RZERO];
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC];
      FIRST_ASSUM(MP_TAC o
        ISPECL [`(f:real^P->real^N) o reversepath(g':real^1->real^P) o
                 (\t. &2 % t - vec 1)`;
                `q':real^1->real^M`;
                `reversepath(h':real^1->real^M) o (\t. &2 % t - vec 1)`;
                `{t | &1 / &2 < drop t /\ drop t <= &1}`;
                `vec 1:real^1`; `t:real^1`] o
        MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_UNIQUE)) THEN
      REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
        EXISTS_TAC `(f:real^P->real^N) o (g ++ reversepath g')` THEN
        CONJ_TAC THENL
         [SIMP_TAC[IN_ELIM_THM; GSYM REAL_NOT_LE; joinpaths; o_THM];
          ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN CONJ_TAC THENL
         [ASM_MESON_TAC[HOMOTOPIC_PATHS_IMP_PATH; path];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
          REAL_ARITH_TAC];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
         `path_image ((f:real^P->real^N) o (g ++ reversepath g'))` THEN
        CONJ_TAC THENL[ALL_TAC; ASM_MESON_TAC[HOMOTOPIC_PATHS_IMP_SUBSET]] THEN
        REWRITE_TAC[path_image] THEN MATCH_MP_TAC(SET_RULE
         `(!x. x IN s ==> f x = g x) /\ s SUBSET t
          ==> IMAGE f s SUBSET IMAGE g t`) THEN
        SIMP_TAC[IN_ELIM_THM; GSYM REAL_NOT_LE; joinpaths; o_THM] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        ASM_REWRITE_TAC[GSYM path] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
         `path_image(q':real^1->real^M)` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[path_image] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `t':real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(fun th ->
         W(MP_TAC o PART_MATCH (lhand o rand) th o rand o snd)) THEN
        ASM_SIMP_TAC[IN_INTERVAL_1; joinpaths; DROP_VEC; GSYM REAL_NOT_LT] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID;
                 CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        ASM_SIMP_TAC[GSYM path; PATH_REVERSEPATH] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `path_image(reversepath h':real^1->real^M)` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[PATH_IMAGE_REVERSEPATH]] THEN
        REWRITE_TAC[path_image; IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `t':real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        REWRITE_TAC[reversepath] THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC; DROP_CMUL] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_1] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
        REWRITE_TAC[IN_ELIM_THM; DROP_VEC] THEN REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM pathfinish] THEN
        ASM_REWRITE_TAC[reversepath] THEN
        SUBST1_TAC(SYM(ASSUME `pathstart h':real^M = a`)) THEN
        REWRITE_TAC[pathstart] THEN AP_TERM_TAC THEN
        REWRITE_TAC[GSYM DROP_EQ; DROP_SUB; DROP_CMUL; DROP_VEC] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^P->real^M` THEN
  DISCH_THEN(LABEL_TAC "+") THEN
  MATCH_MP_TAC(TAUT `(q ==> p) /\ q ==> p /\ q`) THEN REPEAT CONJ_TAC THENL
   [STRIP_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^P` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `y:real^P`) THEN
    ASM_MESON_TAC[PATHFINISH_IN_PATH_IMAGE; SUBSET];
    FIRST_ASSUM(MP_TAC o SPECL
     [`z:real^P`; `linepath(z:real^P,z)`; `linepath(a:real^M,a)`]) THEN
    REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ASM_SIMP_TAC[LINEPATH_REFL; SING_SUBSET];
    X_GEN_TAC `y:real^P` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `y:real^P`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`g:real^1->real^P`; `h:real^1->real^M`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`y:real^P`; `g:real^1->real^P`; `h:real^1->real^M`]) THEN
    ASM_MESON_TAC[pathfinish; ENDS_IN_UNIT_INTERVAL]] THEN
  FIRST_ASSUM(fun th ->
   GEN_REWRITE_TAC I [MATCH_MP CONTINUOUS_ON_OPEN_GEN th]) THEN
  X_GEN_TAC `n:real^M->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:real^P` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `(f:real^P->real^N) y` o last o CONJUNCTS o
        GEN_REWRITE_RULE I [covering_space]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:(real^M->bool)->bool` MP_TAC) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `(l:real^P->real^M) y`) THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_UNIONS]] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':real^M->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `w':real^M->bool`) MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `w':real^M->bool` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `p':real^N->real^M`) THEN
  DISCH_TAC THEN UNDISCH_THEN `(w':real^M->bool) IN vv` (K ALL_TAC) THEN
  SUBGOAL_THEN
   `?v. y IN v /\ y IN u /\ IMAGE (f:real^P->real^N) v SUBSET w /\
        v SUBSET u /\ path_connected v /\ open_in (subtopology euclidean u) v`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LOCALLY_PATH_CONNECTED]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`{x | x IN u /\ (f:real^P->real^N) x IN w}`; `y:real^P`]) THEN
    ANTS_TAC THENL [ALL_TAC; MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(w':real^M->bool) SUBSET c /\ (w:real^N->bool) SUBSET s`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[open_in]; ALL_TAC] THEN
  EXISTS_TAC
   `v INTER
    {x | x IN u /\ (f:real^P->real^N) x IN
                   {x | x IN w /\ (p':real^N->real^M) x IN w' INTER n}}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `w:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `w':real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `open_in (subtopology euclidean c) (n:real^M->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `y':real^P` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
  DISCH_THEN(MP_TAC o SPECL [`y:real^P`; `y':real^P`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^1->real^P` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `y:real^P`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`pp:real^1->real^P`; `qq:real^1->real^M`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`y':real^P`; `(pp:real^1->real^P) ++ r`;
    `(qq:real^1->real^M) ++ ((p':real^N->real^M) o (f:real^P->real^N) o
                            (r:real^1->real^P))`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`y:real^P`; `pp:real^1->real^P`; `qq:real^1->real^M`]) THEN
  ASM_SIMP_TAC[o_THM; PATHSTART_JOIN; PATHFINISH_JOIN] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `path_image ((pp:real^1->real^P) ++ r) SUBSET u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN ASM SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[PATHFINISH_COMPOSE] THEN ASM_MESON_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[PATH_JOIN];
    ASM_SIMP_TAC[SUBSET_PATH_IMAGE_JOIN];
    MATCH_MP_TAC PATH_JOIN_IMP THEN ASM_SIMP_TAC[PATHSTART_COMPOSE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
             CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC[];
      REWRITE_TAC[pathfinish] THEN ASM SET_TAC[]];
    MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN ASM SET_TAC[];
    X_GEN_TAC `tt:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    STRIP_TAC THEN REWRITE_TAC[joinpaths; o_THM] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [ABBREV_TAC `t:real^1 = &2 % tt`;
      ABBREV_TAC `t:real^1 = &2 % tt - vec 1`] THEN
    (SUBGOAL_THEN `t IN interval[vec 0:real^1,vec 1]` ASSUME_TAC THENL
      [EXPAND_TAC "t" THEN
       REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_image]) THEN ASM SET_TAC[]]);;

let COVERING_SPACE_LIFT_STRONGER = prove
 (`!p:real^M->real^N c s f:real^P->real^N u a z.
        covering_space (c,p) s /\ a IN c /\ z IN u /\
        path_connected u /\ locally path_connected u /\
        f continuous_on u /\ IMAGE f u SUBSET s /\ f z = p a /\
        (!r. path r /\ path_image r SUBSET u /\
             pathstart r = z /\ pathfinish r = z
             ==> ?b. homotopic_paths s (f o r) (linepath(b,b)))
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\ g z = a /\
                (!y. y IN u ==> p(g y) = f y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_LIFT_GENERAL)) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real^1->real^P` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC  `r:real^1->real^P`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real^N`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHSTART_LINEPATH] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  EXISTS_TAC `linepath(a:real^M,a)` THEN
  REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_DEF; LINEPATH_REFL]) THEN
  ASM_REWRITE_TAC[o_DEF; LINEPATH_REFL]);;

let COVERING_SPACE_LIFT_STRONG = prove
 (`!p:real^M->real^N c s f:real^P->real^N u a z.
        covering_space (c,p) s /\ a IN c /\ z IN u /\
        simply_connected u /\ locally path_connected u /\
        f continuous_on u /\ IMAGE f u SUBSET s /\ f z = p a
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\ g z = a /\
                (!y. y IN u ==> p(g y) = f y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_LIFT_STRONGER)) THEN
  ASM_SIMP_TAC[SIMPLY_CONNECTED_IMP_PATH_CONNECTED] THEN
  X_GEN_TAC `r:real^1->real^P` THEN STRIP_TAC THEN
  EXISTS_TAC `(f:real^P->real^N) z` THEN
  SUBGOAL_THEN
   `linepath(f z,f z) = (f:real^P->real^N) o linepath(z,z)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF; LINEPATH_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_CONTINUOUS_IMAGE THEN
  EXISTS_TAC `u:real^P->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
   [SIMPLY_CONNECTED_EQ_HOMOTOPIC_PATHS]) THEN
  ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET]);;

let COVERING_SPACE_LIFT = prove
 (`!p:real^M->real^N c s f:real^P->real^N u.
        covering_space (c,p) s /\
        simply_connected u /\ locally path_connected u /\
        f continuous_on u /\ IMAGE f u SUBSET s
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\
                (!y. y IN u ==> p(g y) = f y)`,
  MP_TAC COVERING_SPACE_LIFT_STRONG THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
  ASM_CASES_TAC `u:real^P->bool = {}` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_EMPTY; IMAGE_CLAUSES; EMPTY_SUBSET;
                  NOT_IN_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^P`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^P->real^N) a`) THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_IMAGE]] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some additional lemmas about covering spaces.                             *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_COVERING_MAP_FIBRES = prove
 (`!p:real^M->real^N c s a b.
        covering_space (c,p) s /\ path_connected s /\ a IN s /\ b IN s
        ==> {x | x IN c /\ p(x) = a} =_c {x | x IN c /\ p(x) = b}`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; FORALL_AND_THM;
              TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 BINDER_CONV o LAND_CONV)
   [CONJ_SYM] THEN
  MATCH_MP_TAC(MESON[]
   `(!a b. P a b) ==> (!a b. P a b) /\ (!a b. P b a)`) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`] o
    GEN_REWRITE_RULE I [path_connected]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real^1->real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. ?h. z IN c /\ p z = a
            ==> path h /\ path_image h SUBSET c /\ pathstart h = z /\
                !t. t IN interval[vec 0,vec 1]
                    ==> (p:real^M->real^N)(h t) = g t`
  MP_TAC THENL
   [REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC COVERING_SPACE_LIFT_PATH_STRONG THEN
    REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `h:real^M->real^1->real^M` THEN DISCH_TAC] THEN
  REWRITE_TAC[le_c; IN_ELIM_THM] THEN
  EXISTS_TAC `\z. pathfinish((h:real^M->real^1->real^M) z)` THEN
  ASM_REWRITE_TAC[pathfinish] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[SUBSET; path_image; pathstart; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[pathfinish; ENDS_IN_UNIT_INTERVAL];
    MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`p:real^M->real^N`; `c:real^M->bool`; `s:real^N->bool`;
      `reversepath(g:real^1->real^N)`; `reversepath(g:real^1->real^N)`;
      `reversepath((h:real^M->real^1->real^M) x)`;
      `reversepath((h:real^M->real^1->real^M) y)`]
    COVERING_SPACE_MONODROMY) THEN
    ASM_SIMP_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                 HOMOTOPIC_PATHS_REFL] THEN
    ASM_REWRITE_TAC[pathfinish; reversepath; IN_INTERVAL_1; DROP_VEC] THEN
    REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`);
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^M`)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN ASM_REAL_ARITH_TAC]);;

let COVERING_SPACE_INJECTIVE = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ path_connected c /\ simply_connected s
        ==> (!x y. x IN c /\ y IN c /\ p x = p y ==> x = y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP COVERING_SPACE_IMP_CONTINUOUS) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^M` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_LIFT_PATH_STRONG)) THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `(p:real^M->real^N) o (g:real^1->real^M)` th) THEN
    MP_TAC(SPEC `(p:real^M->real^N) o linepath(x:real^M,x)` th)) THEN
  SUBGOAL_THEN
   `(path ((p:real^M->real^N) o linepath(x,x)) /\
     path (p o g)) /\
    (path_image (p o linepath(x:real^M,x)) SUBSET s /\
     path_image (p o g) SUBSET s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_SING; SEGMENT_REFL] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[PATH_IMAGE_COMPOSE; PATH_IMAGE_LINEPATH] THEN
      REWRITE_TAC[SEGMENT_REFL] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHSTART_LINEPATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^1->real^M` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real^1->real^M` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o
    SPECL [`(p:real^M->real^N) o linepath(x:real^M,x)`;
           `(p:real^M->real^N) o (g:real^1->real^M)`;
           `h1:real^1->real^M`; `h2:real^1->real^M`] o
  MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_MONODROMY)) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
        GEN_REWRITE_RULE I [SIMPLY_CONNECTED_EQ_HOMOTOPIC_PATHS]) THEN
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
    ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `pathfinish(linepath(x:real^M,x))` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[PATHFINISH_LINEPATH]];
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th])] THEN
  REWRITE_TAC[pathfinish] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_LIFT_UNIQUE))
  THENL
   [EXISTS_TAC `(p:real^M->real^N) o (h1:real^1->real^M)`;
    EXISTS_TAC `(p:real^M->real^N) o (h2:real^1->real^M)`] THEN
  MAP_EVERY EXISTS_TAC [`interval[vec 0:real^1,vec 1]`; `vec 0:real^1`] THEN
  REWRITE_TAC[CONNECTED_INTERVAL; ENDS_IN_UNIT_INTERVAL] THEN
  ASM_REWRITE_TAC[GSYM path; PATH_LINEPATH; GSYM path_image] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_THM]) THEN ASM_REWRITE_TAC[o_THM] THEN
  ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart]) THEN
  ASM_REWRITE_TAC[LINEPATH_REFL; PATH_IMAGE_COMPOSE] THEN
  (CONJ_TAC THENL
    [ASM_MESON_TAC[PATH_CONTINUOUS_IMAGE; CONTINUOUS_ON_SUBSET];
     ASM SET_TAC[]]));;

let COVERING_SPACE_HOMEOMORPHISM = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ path_connected c /\ simply_connected s
        ==> ?q. homeomorphism (c,s) (p,q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_INJECTIVE_OPEN_MAP THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[COVERING_SPACE_IMP_CONTINUOUS];
    ASM_MESON_TAC[COVERING_SPACE_IMP_SURJECTIVE];
    ASM_MESON_TAC[COVERING_SPACE_INJECTIVE];
    ASM_MESON_TAC[COVERING_SPACE_OPEN_MAP]]);;

(* ------------------------------------------------------------------------- *)
(* Results on finiteness of the number of sheets in a covering space.        *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_FIBRE_NO_LIMPT = prove
 (`!p:real^M->real^N c s a b.
        covering_space (c,p) s /\ a IN c
        ==> ~(a limit_point_of {x | x IN c /\ p x = b})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [covering_space]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^M->real^N) a`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:(real^M->bool)->bool` MP_TAC) THEN
  GEN_REWRITE_TAC I [IMP_CONJ] THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `t:real^M->bool`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:real^N->real^M` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  UNDISCH_TAC `open_in (subtopology euclidean c) (t:real^M->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^M->bool` o
        GEN_REWRITE_RULE I [LIMPT_INFINITE_OPEN]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[INFINITE]] THEN
  MATCH_MP_TAC(MESON[FINITE_SING; FINITE_SUBSET]
   `(?a. s SUBSET {a}) ==> FINITE s`) THEN
  ASM SET_TAC[]);;

let COVERING_SPACE_COUNTABLE_SHEETS = prove
 (`!p:real^M->real^N c s b.
        covering_space (c,p) s ==> COUNTABLE {x | x IN c /\ p x = b}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]
        UNCOUNTABLE_CONTAINS_LIMIT_POINT)) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[COVERING_SPACE_FIBRE_NO_LIMPT]);;

let COVERING_SPACE_FINITE_EQ_COMPACT_FIBRE = prove
 (`!p:real^M->real^N c s b.
        covering_space (c,p) s
        ==> (FINITE {x | x IN c /\ p x = b} <=>
             compact {x | x IN c /\ p x = b})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[FINITE_IMP_COMPACT] THEN
  DISCH_TAC THEN ASM_CASES_TAC `(b:real^N) IN s` THENL
   [ONCE_REWRITE_TAC[TAUT `p <=> (~p ==> F)`] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o
     SPEC `{x | x IN c /\ (p:real^M->real^N) x = b}` o
     GEN_REWRITE_RULE I [COMPACT_EQ_BOLZANO_WEIERSTRASS]) THEN
    ASM_REWRITE_TAC[INFINITE; SUBSET_REFL; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^M` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^M`; `b:real^N`] o
       MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_FIBRE_NO_LIMPT)) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `{x  | x IN c /\ (p:real^M->real^N) x = b} = {}`
     (fun th -> REWRITE_TAC[th; FINITE_EMPTY]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
    ASM SET_TAC[]]);;

let COVERING_SPACE_CLOSED_MAP = prove
 (`!p:real^M->real^N c s t.
        covering_space (c,p) s /\
        (!b. b IN s ==> FINITE {x | x IN c /\ p x = b}) /\
        closed_in (subtopology euclidean c) t
        ==> closed_in (subtopology euclidean s) (IMAGE p t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN]] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o last o CONJUNCTS o
    GEN_REWRITE_RULE I [covering_space]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `v:real^N->bool` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `uu:(real^M->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[UNIONS_0; NOT_IN_EMPTY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `INTERS {IMAGE (p:real^M->real^N) (u DIFF t) | u IN uu}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTERS THEN
    ASM_REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN
      SUBGOAL_THEN
       `!u. u IN uu ==> ?x. x IN u /\ (p:real^M->real^N) x = y`
      ASSUME_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `FINITE (IMAGE (\u. @x. x IN u /\ (p:real^M->real^N) x = y) uu)`
      MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          FINITE_SUBSET)) THEN ASM SET_TAC[];
        MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
        REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN ASM SET_TAC[]];
      X_GEN_TAC `u:real^M->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `v:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN EXISTS_TAC `u:real^M->bool` THEN
      ASM_SIMP_TAC[LEFT_EXISTS_AND_THM] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSED_IN_CLOSED]) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
      EXISTS_TAC `(:real^M) DIFF k` THEN
      ASM_REWRITE_TAC[GSYM closed] THEN ASM SET_TAC[]];
    REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `u:real^M->bool` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M->bool`)) THEN
    ASM_REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; INTERS_GSPEC; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_IMAGE]] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^M`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `q /\ r /\ ~s ==> ~(s <=> q /\ r)`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[IN_UNIONS] THEN ASM SET_TAC[]]);;

let COVERING_SPACE_FINITE_SHEETS_EQ_CLOSED_MAP_STRONG = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ (!b. b IN s ==> b limit_point_of s)
        ==> ((!b. b IN s ==> FINITE {x | x IN c /\ p x = b}) <=>
             (!t. closed_in (subtopology euclidean c) t
                  ==> closed_in (subtopology euclidean s) (IMAGE p t)))`,
  let lemma = prove
   (`!f:num->real^N.
          (!n. ~(s = v n) ==> DISJOINT s (v n))
          ==> (!n. f n IN v n) /\
              (!m n. v m = v n <=> m = n)
              ==> ?n. IMAGE f (:num) INTER s SUBSET {f n}`,
    ASM_CASES_TAC `?n. s = (v:num->real^N->bool) n` THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
        MP_TAC th THEN MATCH_MP_TAC MONO_EXISTS);
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[]] THEN
    ASM SET_TAC[]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC COVERING_SPACE_CLOSED_MAP THEN
    EXISTS_TAC `c:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MESON[INFINITE] `FINITE s <=> ~INFINITE s`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `b:real^N` o last o CONJUNCTS o
    GEN_REWRITE_RULE I [covering_space]) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `t:real^N->bool` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(b:real^N) limit_point_of t` MP_TAC THENL
   [MATCH_MP_TAC LIMPT_OF_OPEN_IN THEN ASM_MESON_TAC[];
    PURE_REWRITE_TAC[LIMPT_SEQUENTIAL_INJ]] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `INFINITE(vv:(real^M->bool)->bool)` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CARD_LE_INFINITE)) THEN REWRITE_TAC[le_c] THEN
    SUBGOAL_THEN
      `!x. ?v. x IN c /\ (p:real^M->real^N) x = b ==> v IN vv /\ x IN v`
    MP_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[SKOLEM_THM]] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^M->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `x:real^M` th) THEN MP_TAC(SPEC `y:real^M` th)) THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INFINITE_CARD_LE; le_c; INJECTIVE_ON_ALT] THEN
  REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:num->real^M->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN
    `!u. u IN vv ==> ?q:real^N->real^M. homeomorphism (u,t) (p,q)`
    (MP_TAC o GEN `n:num` o SPEC `(v:num->real^M->bool) n`) THEN
  ASM_REWRITE_TAC[SKOLEM_THM; homeomorphism; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->real^N->real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean s)
              (IMAGE (p:real^M->real^N) (IMAGE (\n. q n (y n:real^N)) (:num)))`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[CLOSED_IN_LIMPT; SUBSET; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `a:real^M`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LIMPT_OF_SEQUENCE_SUBSEQUENCE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(p:real^M->real^N) a = b` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC
       `(p:real^M->real^N) o (\n:num. q n (y n :real^N)) o (r:num->num)` THEN
      REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(GEN_ALL(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
        (fst(EQ_IMP_RULE(SPEC_ALL CONTINUOUS_ON_SEQUENTIALLY))))) THEN
        EXISTS_TAC `c:real^M->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[COVERING_SPACE_IMP_CONTINUOUS];
          REWRITE_TAC[o_DEF] THEN ASM SET_TAC[]];
        REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC LIM_SUBSEQUENCE THEN
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (REWRITE_RULE[IMP_CONJ_ALT] LIM_TRANSFORM_EVENTUALLY)) THEN
        MATCH_MP_TAC ALWAYS_EVENTUALLY THEN REWRITE_TAC[o_DEF] THEN
        ASM SET_TAC[]];
      SUBGOAL_THEN `?u. u IN vv /\ (a:real^M) IN u` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?w:real^M->bool. open w /\ u = c INTER w`
       (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))
      THENL [ASM_MESON_TAC[OPEN_IN_OPEN]; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIMPT_INFINITE_OPEN]) THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
       `INFINITE s ==> !k. s INTER k = s ==> INFINITE(s INTER k)`)) THEN
      DISCH_THEN(MP_TAC o SPEC `c:real^M->bool`) THEN ANTS_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[INTER_ASSOC]] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
      DISCH_THEN(MP_TAC o SPEC `c INTER w:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `(v:num->real^M->bool) n`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `\n. (q:num->real^N->real^M) n (y n)` o
        MATCH_MP lemma) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MESON_TAC[FINITE_SUBSET; FINITE_SING; INTER_COMM]];
    SUBGOAL_THEN
     `IMAGE (p:real^M->real^N) (IMAGE (\n. q n (y n:real^N)) (:num)) =
      IMAGE y (:num)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CLOSED_IN_LIMPT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `b:real^N`)) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[LIMPT_SEQUENTIAL_INJ] THEN
    EXISTS_TAC `y:num->real^N` THEN ASM SET_TAC[]]);;

let COVERING_SPACE_FINITE_SHEETS_EQ_CLOSED_MAP = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ connected s /\ ~(?a. s = {a})
        ==> ((!b. b IN s ==> FINITE {x | x IN c /\ p x = b}) <=>
             (!t. closed_in (subtopology euclidean c) t
                  ==> closed_in (subtopology euclidean s) (IMAGE p t)))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [SUBGOAL_THEN `c:real^M->bool = {}` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
      ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_EMPTY; CLOSED_IN_SUBTOPOLOGY_EMPTY;
                      IMAGE_EQ_EMPTY; NOT_IN_EMPTY]];
    MATCH_MP_TAC COVERING_SPACE_FINITE_SHEETS_EQ_CLOSED_MAP_STRONG THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONNECTED_IMP_PERFECT THEN ASM SET_TAC[]]);;

let COVERING_SPACE_FINITE_SHEETS_EQ_PROPER_MAP = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> ((!b. b IN s ==> FINITE {x | x IN c /\ p x = b}) <=>
             (!k. k SUBSET s /\ compact k
                  ==> compact {x | x IN c /\ p(x) IN k}))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE `s = t ==> s SUBSET t`)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP PROPER_MAP th]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC
   [GSYM(MATCH_MP COVERING_SPACE_FINITE_EQ_COMPACT_FIBRE th)]) THEN
  REWRITE_TAC[TAUT `(p <=> q /\ p) <=> (p ==> q)`] THEN
  ASM_MESON_TAC[COVERING_SPACE_CLOSED_MAP]);;

(* ------------------------------------------------------------------------- *)
(* Special cases where one or both of the sets is compact.                   *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_FINITE_SHEETS = prove
 (`!p:real^M->real^N c s b.
      covering_space (c,p) s /\ compact c ==> FINITE {x | x IN c /\ p x = b}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOLZANO_WEIERSTRASS_CONTRAPOS THEN
  EXISTS_TAC `c:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN
  ASM_MESON_TAC[COVERING_SPACE_FIBRE_NO_LIMPT]);;

let COVERING_SPACE_COMPACT = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> (compact c <=>
             compact s /\ (!b. b IN s ==> FINITE {x | x IN c /\ p x = b}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[covering_space; COMPACT_CONTINUOUS_IMAGE];
    MATCH_MP_TAC COVERING_SPACE_FINITE_SHEETS THEN ASM_MESON_TAC[];
    FIRST_ASSUM(MP_TAC o
      MATCH_MP COVERING_SPACE_FINITE_SHEETS_EQ_PROPER_MAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
    SET_TAC[]]);;


print_endline "paths.ml loaded"
