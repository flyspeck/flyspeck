open Hol_core
open Card
open Floor
open Vectors
open Determinants
open Topology
open Convex
include Paths3

(* ------------------------------------------------------------------------- *)
(* Homotopy of maps p,q : X->Y with property P of all intermediate maps.     *)
(* We often just want to require that it fixes some subset, but to take in   *)
(* the case of loop homotopy it's convenient to have a general property P.   *)
(* ------------------------------------------------------------------------- *)

let homotopic_with = new_definition
 `homotopic_with P (X,Y) p q <=>
   ?h:real^(1,M)finite_sum->real^N.
     h continuous_on (interval[vec 0,vec 1] PCROSS X) /\
     IMAGE h (interval[vec 0,vec 1] PCROSS X) SUBSET Y /\
     (!x. h(pastecart (vec 0) x) = p x) /\
     (!x. h(pastecart (vec 1) x) = q x) /\
     (!t. t IN interval[vec 0,vec 1] ==> P(\x. h(pastecart t x)))`;;

(* ------------------------------------------------------------------------- *)
(* We often want to just localize the ending function equality or whatever.  *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH = prove
 (`(!h k. (!x. x IN X ==> h x = k x) ==> (P h <=> P k))
   ==> (homotopic_with P (X,Y) p q <=>
        ?h:real^(1,M)finite_sum->real^N.
          h continuous_on (interval[vec 0,vec 1] PCROSS X) /\
          IMAGE h (interval[vec 0,vec 1] PCROSS X) SUBSET Y /\
          (!x. x IN X ==> h(pastecart (vec 0) x) = p x) /\
          (!x. x IN X ==> h(pastecart (vec 1) x) = q x) /\
          (!t. t IN interval[vec 0,vec 1] ==> P(\x. h(pastecart t x))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[homotopic_with; PCROSS] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    REWRITE_TAC[homotopic_with; PCROSS] THEN
     DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N`
      (fun th -> EXISTS_TAC
        `\y. if sndcart(y) IN X then (h:real^(1,M)finite_sum->real^N) y
             else if fstcart(y) = vec 0 then p(sndcart y)
             else q(sndcart y)` THEN
      MP_TAC th)) THEN
     REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VEC_EQ; ARITH_EQ] THEN
     REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
      [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
       SIMP_TAC[FORALL_IN_GSPEC; SNDCART_PASTECART];
       SIMP_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC; SUBSET] THEN
       SIMP_TAC[FORALL_IN_GSPEC; SNDCART_PASTECART];
       ASM_MESON_TAC[];
       ASM_MESON_TAC[];
       MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^1` THEN
       MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
       MATCH_MP_TAC EQ_IMP THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       SIMP_TAC[]]]);;

let HOMOTOPIC_WITH_EQ = prove
 (`!P X Y f g f' g':real^M->real^N.
        homotopic_with P (X,Y) f g /\
        (!x. x IN X ==> f' x = f x /\ g' x = g x) /\
        (!h k. (!x. x IN X ==> h x = k x) ==> (P h <=> P k))
        ==>  homotopic_with P (X,Y) f' g'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N`
   (fun th -> EXISTS_TAC
     `\y. if sndcart(y) IN X then (h:real^(1,M)finite_sum->real^N) y
          else if fstcart(y) = vec 0 then f'(sndcart y)
          else g'(sndcart y)` THEN
   MP_TAC th)) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VEC_EQ; ARITH_EQ] THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
    SIMP_TAC[FORALL_IN_PCROSS; SNDCART_PASTECART];
    SIMP_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS; SUBSET] THEN
    SIMP_TAC[FORALL_IN_PCROSS; SNDCART_PASTECART];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^1` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[]]);;

let HOMOTOPIC_WITH_EQUAL = prove
 (`!P f:real^M->real^N g s t.
        P f /\ P g /\
        f continuous_on s /\ IMAGE f s SUBSET t /\
        (!x. x IN s ==> g x = f x)
        ==> homotopic_with P (s,t) f g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_with] THEN
  EXISTS_TAC `\z:real^(1,M)finite_sum.
    if fstcart z = vec 1 then g(sndcart z):real^N else f(sndcart z)` THEN
  REWRITE_TAC[VEC_EQ; ARITH_EQ; SNDCART_PASTECART; FSTCART_PASTECART] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\z:real^(1,M)finite_sum. (f:real^M->real^N)(sndcart z)` THEN
    ASM_SIMP_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[COND_ID] THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; IMAGE_SNDCART_PCROSS] THEN
    ASM_REWRITE_TAC[UNIT_INTERVAL_NONEMPTY];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    REWRITE_TAC[ FSTCART_PASTECART; SNDCART_PASTECART] THEN
    CONJ_TAC THEN X_GEN_TAC `t:real^1` THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `t:real^1 = vec 1` THEN ASM_REWRITE_TAC[ETA_AX] THEN
    ASM SET_TAC[]]);;

let HOMOTOPIC_CONSTANT_MAPS = prove
 (`!s:real^M->bool t:real^N->bool a b.
        homotopic_with (\x. T) (s,t) (\x. a) (\x. b) <=>
        s = {} \/ path_component t a b`,
  REPEAT GEN_TAC THEN SIMP_TAC[HOMOTOPIC_WITH; path_component] THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; PCROSS_EMPTY; IMAGE_CLAUSES] THEN
  REWRITE_TAC[EMPTY_SUBSET; CONTINUOUS_ON_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PATH_IMAGE_NONEMPTY; SUBSET_EMPTY; PCROSS_EQ_EMPTY;
                  IMAGE_EQ_EMPTY; UNIT_INTERVAL_NONEMPTY] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N`
        STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?c:real^M. c IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `(h:real^(1,M)finite_sum->real^N) o (\t. pastecart t c)` THEN
    ASM_SIMP_TAC[pathstart; pathfinish; o_THM; PATH_IMAGE_COMPOSE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET));
      REWRITE_TAC[path_image]] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS];
    REWRITE_TAC[path; pathstart; path_image; pathfinish] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
     `(g:real^1->real^N) o (fstcart:real^(1,M)finite_sum->real^1)` THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; o_THM; IMAGE_o; IMAGE_FSTCART_PCROSS] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[LINEAR_FSTCART; LINEAR_CONTINUOUS_ON;
                 IMAGE_FSTCART_PCROSS]]);;

(* ------------------------------------------------------------------------- *)
(* Trivial properties.                                                       *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH_IMP_PROPERTY = prove
 (`!P X Y (f:real^M->real^N) g. homotopic_with P (X,Y) f g ==> P f /\ P g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN DISCH_THEN
   (fun th -> MP_TAC(SPEC `vec 0:real^1` th) THEN
              MP_TAC(SPEC `vec 1:real^1` th)) THEN
  ASM_SIMP_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL; ETA_AX]);;

let HOMOTOPIC_WITH_IMP_CONTINUOUS = prove
 (`!P X Y (f:real^M->real^N) g.
      homotopic_with P (X,Y) f g ==> f continuous_on X /\ g continuous_on X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N` MP_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `((h:real^(1,M)finite_sum->real^N) o (\x. pastecart (vec 0) x))
    continuous_on X /\
    ((h:real^(1,M)finite_sum->real^N) o (\x. pastecart (vec 1) x))
    continuous_on X`
  MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[o_DEF; ETA_AX]] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SIMP_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; IN_INTERVAL_1] THEN
  REWRITE_TAC[DROP_VEC; REAL_POS; REAL_LE_REFL]);;

let HOMOTOPIC_WITH_IMP_SUBSET = prove
 (`!P X Y (f:real^M->real^N) g.
      homotopic_with P (X,Y) f g ==> IMAGE f X SUBSET Y /\ IMAGE g X SUBSET Y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N` MP_TAC) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS; SUBSET] THEN DISCH_THEN
   (fun th -> MP_TAC(SPEC `vec 0:real^1` th) THEN
              MP_TAC(SPEC `vec 1:real^1` th)) THEN
  ASM_SIMP_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL]);;

let HOMOTOPIC_WITH_MONO = prove
 (`!P Q X Y f g:real^M->real^N.
        homotopic_with P (X,Y) f g /\
        (!h. h continuous_on X /\ IMAGE h X SUBSET Y /\ P h ==> Q h)
        ==> homotopic_with Q (X,Y) f g`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with; PCROSS] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
             CONTINUOUS_ON_CONST] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let HOMOTOPIC_WITH_SUBSET_LEFT = prove
 (`!P X Y Z f g.
        homotopic_with P (X,Y) f g /\ Z SUBSET X
        ==> homotopic_with P (Z,Y) f g`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with; PCROSS] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let HOMOTOPIC_WITH_SUBSET_RIGHT = prove
 (`!P X Y Z (f:real^M->real^N) g h.
        homotopic_with P (X,Y) f g /\ Y SUBSET Z
        ==> homotopic_with P (X,Z) f g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN
  ASM_MESON_TAC[SUBSET_TRANS]);;

let HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT = prove
 (`!p f:real^N->real^P g h:real^M->real^N W X Y.
        homotopic_with (\f. p(f o h)) (X,Y) f g /\
        h continuous_on W /\ IMAGE h W SUBSET X
        ==> homotopic_with p (W,Y) (f o h) (g o h)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with; o_DEF; PCROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^(1,N)finite_sum->real^P`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y:real^(1,M)finite_sum.
                (k:real^(1,N)finite_sum->real^P)
                (pastecart (fstcart y) (h(sndcart y)))` THEN
  ASM_REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE [IMP_CONJ]
      CONTINUOUS_ON_SUBSET));
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  SIMP_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT = prove
 (`!f:real^N->real^P g h:real^M->real^N W X Y.
        homotopic_with (\f. T) (X,Y) f g /\
        h continuous_on W /\ IMAGE h W SUBSET X
        ==> homotopic_with (\f. T) (W,Y) (f o h) (g o h)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `X:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT = prove
 (`!p f:real^M->real^N g h:real^N->real^P X Y Z.
        homotopic_with (\f. p(h o f)) (X,Y) f g /\
        h continuous_on Y /\ IMAGE h Y SUBSET Z
        ==> homotopic_with p (X,Z) (h o f) (h o g)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with; o_DEF] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^(1,M)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(h:real^N->real^P) o (k:real^(1,M)finite_sum->real^N)` THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE [IMP_CONJ]
      CONTINUOUS_ON_SUBSET));
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[]);;

let HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT = prove
 (`!f:real^M->real^N g h:real^N->real^P X Y Z.
        homotopic_with (\f. T) (X,Y) f g /\
        h continuous_on Y /\ IMAGE h Y SUBSET Z
        ==> homotopic_with (\f. T) (X,Z) (h o f) (h o g)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
  EXISTS_TAC `Y:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let HOMOTOPIC_WITH_PCROSS = prove
 (`!f:real^M->real^N f':real^P->real^Q g g' p p' q s s' t t'.
     homotopic_with p (s,t) f g /\
     homotopic_with p' (s',t') f' g' /\
     (!f g. p f /\ p' g ==> q(\x. pastecart (f(fstcart x)) (g(sndcart x))))
     ==> homotopic_with q (s PCROSS s',t PCROSS t')
          (\z. pastecart (f(fstcart z)) (f'(sndcart z)))
          (\z. pastecart (g(fstcart z)) (g'(sndcart z)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:real^(1,M)finite_sum->real^N` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `k':real^(1,P)finite_sum->real^Q` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC
   `\z:real^(1,(M,P)finite_sum)finite_sum.
        pastecart (k(pastecart (fstcart z) (fstcart(sndcart z))):real^N)
                  (k'(pastecart (fstcart z) (sndcart(sndcart z))):real^Q)` THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS]) THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS;
               FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS;
               IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
     SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
     GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
     MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
     SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART];
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN
     REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS;
                 IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
     ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART;
                  PASTECART_IN_PCROSS]]));;

let HOMOTOPIC_ON_EMPTY = prove
 (`!t f g. homotopic_with (\x. T) ({},t) f g`,
  SIMP_TAC[HOMOTOPIC_WITH; NOT_IN_EMPTY; PCROSS_EMPTY] THEN
  REWRITE_TAC[CONTINUOUS_ON_EMPTY; IMAGE_CLAUSES; EMPTY_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy with P is an equivalence relation (on continuous functions       *)
(* mapping X into Y that satisfy P, though this only affects reflexivity).   *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH_REFL = prove
 (`!P X Y (f:real^M->real^N).
      homotopic_with P (X,Y) f f <=>
      f continuous_on X /\ IMAGE f X SUBSET Y /\ P f`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[HOMOTOPIC_WITH_IMP_PROPERTY; HOMOTOPIC_WITH_IMP_CONTINUOUS;
              HOMOTOPIC_WITH_IMP_SUBSET];
    STRIP_TAC THEN REWRITE_TAC[homotopic_with; PCROSS]] THEN
  EXISTS_TAC `\y:real^(1,M)finite_sum. (f:real^M->real^N) (sndcart y)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_SIMP_TAC[SNDCART_PASTECART; ETA_AX; SUBSET; FORALL_IN_IMAGE;
               FORALL_IN_GSPEC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; SNDCART_PASTECART]);;

let HOMOTOPIC_WITH_SYM = prove
 (`!P X Y (f:real^M->real^N) g.
      homotopic_with P (X,Y) f g <=> homotopic_with P (X,Y) g f`,
  REPLICATE_TAC 3 GEN_TAC THEN MATCH_MP_TAC(MESON[]
   `(!x y. P x y ==> P y x) ==> (!x y. P x y <=> P y x)`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with; PCROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y:real^(1,M)finite_sum.
        (h:real^(1,M)finite_sum->real^N)
        (pastecart (vec 1 - fstcart y) (sndcart y))` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_SUB_RZERO] THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
             LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET));
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
    REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE h s SUBSET t ==> IMAGE g s SUBSET s
      ==> IMAGE h (IMAGE g s) SUBSET t`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC];
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[PASTECART_EQ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SIMP_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; IN_INTERVAL_1] THEN
  REWRITE_TAC[DROP_VEC; REAL_POS; REAL_LE_REFL; DROP_SUB] THEN
  ASM_REAL_ARITH_TAC);;

let HOMOTOPIC_WITH_TRANS = prove
 (`!P X Y (f:real^M->real^N) g h.
      homotopic_with P (X,Y) f g /\ homotopic_with P (X,Y) g h
      ==> homotopic_with P (X,Y) f h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with; PCROSS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k1:real^(1,M)finite_sum->real^N` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `k2:real^(1,M)finite_sum->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\y:real^(1,M)finite_sum.
        if drop(fstcart y) <= &1 / &2
        then (k1:real^(1,M)finite_sum->real^N)
             (pastecart (&2 % fstcart y) (sndcart y))
        else (k2:real^(1,M)finite_sum->real^N)
             (pastecart (&2 % fstcart y - vec 1) (sndcart y))` THEN
  REWRITE_TAC[FSTCART_PASTECART; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `&2 % x - x:real^N = x`; SNDCART_PASTECART] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `interval[vec 0:real^1,vec 1] =
      interval[vec 0,lift(&1 / &2)] UNION interval[lift(&1 / &2),vec 1]`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SET_RULE `{f x y | x IN s UNION t /\ y IN u} =
                          {f x y | x IN s /\ y IN u} UNION
                          {f x y | x IN t /\ y IN u}`] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
    ONCE_REWRITE_TAC[TAUT
     `a /\ b /\ c /\ d /\ e <=> (a /\ b) /\ (c /\ d) /\ e`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CLOSED_IN_CLOSED] THEN CONJ_TAC THENL
       [EXISTS_TAC `{ pastecart (t:real^1) (x:real^M) |
                      t IN interval[vec 0,lift(&1 / &2)] /\ x IN UNIV }`;
        EXISTS_TAC `{ pastecart (t:real^1) (x:real^M) |
                      t IN interval[lift(&1 / &2),vec 1] /\ x IN UNIV}`] THEN
      SIMP_TAC[REWRITE_RULE[PCROSS] CLOSED_PCROSS;
               CLOSED_INTERVAL; CLOSED_UNIV] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_INTER; TAUT
       `(x IN (s UNION t) /\ x IN u ==> x IN v) <=>
        (x IN u ==> x IN (s UNION t) ==> x IN v)`] THEN
      REWRITE_TAC[PASTECART_EQ; IN_ELIM_THM; IN_UNION] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_UNIV] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
       [CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB;
        CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART;
        LINEAR_SNDCART] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IN_ELIM_THM; PASTECART_EQ; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      REWRITE_TAC[MESON[] `(?t x. P t x /\ a = t /\ b = x) <=> P a b`] THEN
      SIMP_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC; DROP_CMUL; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
      REWRITE_TAC[FORALL_AND_THM; IMP_CONJ; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1] THEN
      SIMP_TAC[LIFT_DROP; DROP_VEC; REAL_ARITH
       `&1 / &2 <= t ==> (t <= &1 / &2 <=> t = &1 / &2)`] THEN
      SIMP_TAC[GSYM LIFT_EQ; LIFT_DROP; GSYM LIFT_CMUL; GSYM LIFT_NUM] THEN
      REWRITE_TAC[GSYM LIFT_SUB] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REWRITE_TAC[LIFT_NUM]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE k s SUBSET t ==> x IN s ==> k x IN t`)) THEN
    ASM_REWRITE_TAC[IN_ELIM_PASTECART_THM; IN_INTERVAL_1; DROP_VEC;
                    DROP_CMUL; DROP_SUB] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    STRIP_TAC THEN ASM_CASES_TAC `drop t <= &1 / &2` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
    ASM_REAL_ARITH_TAC]);;

let HOMOTOPIC_COMPOSE = prove
 (`!f f':real^M->real^N g g':real^N->real^P s t u.
        homotopic_with (\x. T) (s,t) f f' /\
        homotopic_with (\x. T) (t,u) g g'
        ==> homotopic_with (\x. T) (s,u) (g o f) (g' o f')`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `(g:real^N->real^P) o (f':real^M->real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT;
    MATCH_MP_TAC HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT] THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    ASSUME_TAC(MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS th) THEN
    ASSUME_TAC(MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET th))) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Two characterizations of homotopic triviality, one of which               *)
(* implicitly incorporates path-connectedness.                               *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_TRIVIALITY = prove
 (`!s:real^M->bool t:real^N->bool.
        (!f g. f continuous_on s /\ IMAGE f s SUBSET t /\
               g continuous_on s /\ IMAGE g s SUBSET t
               ==> homotopic_with (\x. T) (s,t) f g) <=>
        (s = {} \/ path_connected t) /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET t
             ==> ?c. homotopic_with (\x. T) (s,t) f (\x. c))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_EMPTY; HOMOTOPIC_WITH; NOT_IN_EMPTY;
                 PCROSS_EMPTY; IMAGE_CLAUSES; EMPTY_SUBSET];
    ASM_CASES_TAC `t:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[SUBSET_EMPTY; IMAGE_EQ_EMPTY; PATH_CONNECTED_EMPTY]] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (rand o rand) HOMOTOPIC_CONSTANT_MAPS o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; CONTINUOUS_ON_CONST] THEN
    ASM SET_TAC[];
    SUBGOAL_THEN `?c:real^N. c IN t` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; CONTINUOUS_ON_CONST];
    FIRST_X_ASSUM(fun th ->
      MP_TAC(ISPEC `g:real^M->real^N` th) THEN
      MP_TAC(ISPEC `f:real^M->real^N` th)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `c:real^N` THEN DISCH_TAC THEN
    X_GEN_TAC `d:real^N` THEN DISCH_TAC THEN
    TRANS_TAC HOMOTOPIC_WITH_TRANS `(\x. c):real^M->real^N` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
    TRANS_TAC HOMOTOPIC_WITH_TRANS `(\x. d):real^M->real^N` THEN
    ASM_REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
      REWRITE_RULE[PATH_CONNECTED_IFF_PATH_COMPONENT]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET)) THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy on a union of closed-open sets.                                  *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_ON_CLOPEN_UNIONS = prove
 (`!f:real^M->real^N g t u.
        (!s. s IN u
             ==> closed_in (subtopology euclidean (UNIONS u)) s /\
                 open_in (subtopology euclidean (UNIONS u)) s /\
                 homotopic_with (\x. T) (s,t) f g)
        ==> homotopic_with (\x. T) (UNIONS u,t) f g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?v. v SUBSET u /\ COUNTABLE v /\ UNIONS v :real^M->bool = UNIONS u`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LINDELOF_OPEN_IN THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)] THEN
  ASM_CASES_TAC `v:(real^M->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[HOMOTOPIC_ON_EMPTY; UNIONS_0] THEN
  MP_TAC(ISPEC `v:(real^M->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:num->real^M->bool` THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPEC `(f:num->real^M->bool) n`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MONO_FORALL) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[FORALL_AND_THM]] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [homotopic_with] THEN
  SIMP_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; HOMOTOPIC_WITH] THEN
  X_GEN_TAC `h:num->real^(1,M)finite_sum->real^N` THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`h:num->real^(1,M)finite_sum->real^N`;
    `(\n. interval[vec 0,vec 1] PCROSS (f n DIFF UNIONS {f m | m < n}))
     :num->real^(1,M)finite_sum->bool`;
    `(interval[vec 0,vec 1] PCROSS UNIONS(IMAGE f (:num)))
     :real^(1,M)finite_sum->bool`;
    `(:num)`] PASTING_LEMMA_EXISTS) THEN
  REWRITE_TAC[IN_UNIV; FORALL_AND_THM; INTER_PCROSS] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_GSPEC; SUBSET; IN_ELIM_THM; FORALL_PASTECART] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                  FORALL_IN_UNIONS; FORALL_IN_IMAGE; IN_UNIV; IMP_CONJ] THEN
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN X_GEN_TAC `y:real^M` THEN
      REWRITE_TAC[LEFT_FORALL_IMP_THM; IN_DIFF; IN_ELIM_THM] THEN
      GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN MESON_TAC[];
      X_GEN_TAC `n:num` THEN MATCH_MP_TAC OPEN_IN_PCROSS THEN
      REWRITE_TAC[OPEN_IN_REFL] THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_UNIONS THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      SIMP_TAC[FINITE_NUMSEG_LT; FINITE_IMAGE] THEN ASM SET_TAC[];
      X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(fun th ->
        MATCH_MP_TAC(MATCH_MP(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)
        (SPEC `n:num` th))) THEN
      REWRITE_TAC[SUBSET_PCROSS; SUBSET_REFL; SUBSET_DIFF];
      MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[INTER_ACI] THEN MESON_TAC[];
        REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN SET_TAC[]]];
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `g:real^(1,M)finite_sum->real^N` THEN
    REWRITE_TAC[INTER_ACI; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_IN_UNIONS; FORALL_IN_IMAGE; IMP_CONJ; SUBSET;
                RIGHT_FORALL_IMP_THM; IN_UNIV; FORALL_IN_PCROSS] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real^1` THEN DISCH_TAC; CONJ_TAC] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN X_GEN_TAC `y:real^M` THEN
    REWRITE_TAC[LEFT_FORALL_IMP_THM] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real^1`; `y:real^M`; `n:num`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^1`; `y:real^M`; `n:num`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`vec 1:real^1`; `y:real^M`; `n:num`])] THEN
    ASM_REWRITE_TAC[IN_INTER; UNIONS_IMAGE; IN_UNIV; IN_DIFF;
                    UNIONS_GSPEC; IN_ELIM_THM; ENDS_IN_UNIT_INTERVAL] THEN
    (ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [SUBSET]) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN ASM SET_TAC[]]);;

let INESSENTIAL_ON_CLOPEN_UNIONS = prove
 (`!f:real^M->real^N t u.
        path_connected t /\
        (!s. s IN u
             ==> closed_in (subtopology euclidean (UNIONS u)) s /\
                 open_in (subtopology euclidean (UNIONS u)) s /\
                 ?a. homotopic_with (\x. T) (s,t) f (\x. a))
        ==> ?a. homotopic_with (\x. T) (UNIONS u,t) f (\x. a)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `UNIONS u:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; HOMOTOPIC_ON_EMPTY] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [EMPTY_UNIONS]) THEN
  REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP] THEN
  X_GEN_TAC `c:real^M->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `IMAGE (\x. a) s SUBSET t ==> ~(s = {}) ==> a IN t`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `a:real^N` THEN
  MATCH_MP_TAC HOMOTOPIC_ON_CLOPEN_UNIONS THEN
  X_GEN_TAC `s:real^M->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^M->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[HOMOTOPIC_ON_EMPTY] THEN X_GEN_TAC `b:real^N` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
  REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN DISJ2_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `IMAGE (\x. a) s SUBSET t ==> ~(s = {}) ==> a IN t`)) THEN
  ASM_MESON_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy of paths, maintaining the same endpoints.                        *)
(* ------------------------------------------------------------------------- *)

let homotopic_paths = new_definition
 `homotopic_paths s p q =
     homotopic_with
       (\r. pathstart r = pathstart p /\ pathfinish r = pathfinish p)
       (interval[vec 0:real^1,vec 1],s)
       p q`;;

let HOMOTOPIC_PATHS = prove
 (`!s p q:real^1->real^N.
      homotopic_paths s p q <=>
      ?h. h continuous_on
          interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1] /\
          IMAGE h (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1])
          SUBSET s /\
          (!x. x IN interval[vec 0,vec 1] ==> h(pastecart (vec 0) x) = p x) /\
          (!x. x IN interval[vec 0,vec 1] ==> h(pastecart (vec 1) x) = q x) /\
          (!t. t IN interval[vec 0:real^1,vec 1]
               ==> pathstart(h o pastecart t) = pathstart p /\
                   pathfinish(h o pastecart t) = pathfinish p)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homotopic_paths] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HOMOTOPIC_WITH o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[pathstart; pathfinish; ENDS_IN_UNIT_INTERVAL];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let HOMOTOPIC_PATHS_IMP_PATHSTART = prove
 (`!s p q. homotopic_paths s p q ==> pathstart p = pathstart q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_paths] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN
  SIMP_TAC[]);;

let HOMOTOPIC_PATHS_IMP_PATHFINISH = prove
 (`!s p q. homotopic_paths s p q ==> pathfinish p = pathfinish q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_paths] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN
  SIMP_TAC[]);;

let HOMOTOPIC_PATHS_IMP_PATH = prove
 (`!s p q. homotopic_paths s p q ==> path p /\ path q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_paths] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
  SIMP_TAC[path]);;

let HOMOTOPIC_PATHS_IMP_SUBSET = prove
 (`!s p q.
     homotopic_paths s p q ==> path_image p SUBSET s /\ path_image q SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_paths] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  SIMP_TAC[path_image]);;

let HOMOTOPIC_PATHS_REFL = prove
 (`!s p. homotopic_paths s p p <=>
           path p /\ path_image p SUBSET s`,
  REWRITE_TAC[homotopic_paths; HOMOTOPIC_WITH_REFL; path; path_image]);;

let HOMOTOPIC_PATHS_SYM = prove
 (`!s p q. homotopic_paths s p q <=> homotopic_paths s q p`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_paths]) THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN ASM_SIMP_TAC[homotopic_paths]);;

let HOMOTOPIC_PATHS_TRANS = prove
 (`!s p q r.
        homotopic_paths s p q /\ homotopic_paths s q r
        ==> homotopic_paths s p r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN
   (fun th -> ASSUME_TAC(MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART th) THEN
              ASSUME_TAC(MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH th))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE BINOP_CONV [homotopic_paths]) THEN
  ASM_REWRITE_TAC[HOMOTOPIC_WITH_TRANS; homotopic_paths]);;

let HOMOTOPIC_PATHS_EQ = prove
 (`!p:real^1->real^N q s.
        path p /\ path_image p SUBSET s /\
        (!t. t IN interval[vec 0,vec 1] ==> p(t) = q(t))
        ==> homotopic_paths s p q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_paths] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  REPEAT(EXISTS_TAC `p:real^1->real^N`) THEN
  ASM_SIMP_TAC[HOMOTOPIC_WITH_REFL] THEN
  ASM_REWRITE_TAC[GSYM path; GSYM path_image] THEN
  REWRITE_TAC[pathstart; pathfinish] THEN
  MESON_TAC[ENDS_IN_UNIT_INTERVAL]);;

let HOMOTOPIC_PATHS_REPARAMETRIZE = prove
 (`!p:real^1->real^N q f:real^1->real^1.
        path p /\ path_image p SUBSET s /\
        (?f. f continuous_on interval[vec 0,vec 1] /\
             IMAGE f (interval[vec 0,vec 1]) SUBSET interval[vec 0,vec 1] /\
             f(vec 0) = vec 0 /\ f(vec 1) = vec 1 /\
             !t. t IN interval[vec 0,vec 1] ==> q(t) = p(f t))
        ==> homotopic_paths s p q`,
  REWRITE_TAC[path; path_image] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(p:real^1->real^N) o (f:real^1->real^1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_EQ THEN
    ASM_SIMP_TAC[o_THM; pathstart; pathfinish; o_THM;
                 IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
    REWRITE_TAC[path; path_image] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `(p:real^1->real^N) o (f:real^1->real^1)` THEN
      ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM SET_TAC[]];
    REWRITE_TAC[homotopic_paths; homotopic_with; PCROSS] THEN
    EXISTS_TAC `(p:real^1->real^N) o
                (\y. (&1 - drop(fstcart y)) % f(sndcart y) +
                     drop(fstcart y) % sndcart y)` THEN
    ASM_REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC;
                    pathstart; pathfinish] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VECTOR_ADD_LID;
                VECTOR_MUL_LID; VECTOR_ADD_RID] THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - u) % x + u % x:real^N = x`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX; LIFT_SUB] THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST; LINEAR_FSTCART;
                 LINEAR_SNDCART; CONTINUOUS_ON_SUB] THEN
        MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; SNDCART_PASTECART];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET))];
      ONCE_REWRITE_TAC[IMAGE_o] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE p i SUBSET s
        ==> IMAGE f x SUBSET i
            ==> IMAGE p (IMAGE f x) SUBSET s`))] THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; SNDCART_PASTECART;
             FSTCART_PASTECART] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] (CONJUNCT1(SPEC_ALL
      CONVEX_INTERVAL))) THEN
    ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC; SUBSET; IN_IMAGE]]);;

let HOMOTOPIC_PATHS_SUBSET = prove
 (`!s p q.
        homotopic_paths s p q /\ s SUBSET t
        ==> homotopic_paths t p q`,
  REWRITE_TAC[homotopic_paths; HOMOTOPIC_WITH_SUBSET_RIGHT]);;

(* ------------------------------------------------------------------------- *)
(* A slightly ad-hoc but useful lemma in constructing homotopies.            *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_JOIN_LEMMA = prove
 (`!p q:real^1->real^1->real^N.
  (\y. p (fstcart y) (sndcart y)) continuous_on
  (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) /\
  (\y. q (fstcart y) (sndcart y)) continuous_on
  (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) /\
  (!t. t IN interval[vec 0,vec 1] ==> pathfinish(p t) = pathstart(q t))
  ==> (\y. (p(fstcart y) ++ q(fstcart y)) (sndcart y)) continuous_on
      (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1])`,
  REWRITE_TAC[joinpaths; PCROSS] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_LE THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
    `(\y. p (fstcart y) (&2 % sndcart y)):real^(1,1)finite_sum->real^N =
     (\y. p (fstcart y) (sndcart y)) o
     (\y. pastecart (fstcart y) (&2 % sndcart y))`
    SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC];
    SUBGOAL_THEN
    `(\y. q (fstcart y) (&2 % sndcart y - vec 1)):real^(1,1)finite_sum->real^N =
     (\y. q (fstcart y) (sndcart y)) o
     (\y. pastecart (fstcart y) (&2 % sndcart y - vec 1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC];
    SIMP_TAC[o_DEF; LIFT_DROP; LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX];
    SIMP_TAC[IMP_CONJ; FORALL_IN_GSPEC; FSTCART_PASTECART; SNDCART_PASTECART;
             GSYM LIFT_EQ; LIFT_DROP; GSYM LIFT_CMUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_SIMP_TAC[LIFT_NUM; VECTOR_SUB_REFL]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  (CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_PASTECART; ALL_TAC]) THEN
  SIMP_TAC[CONTINUOUS_ON_CMUL; LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_SUB;
           CONTINUOUS_ON_CONST; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; IMP_CONJ] THEN
  SIMP_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_SUB; DROP_VEC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Congruence properties of homotopy w.r.t. path-combining operations.       *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_PATHS_REVERSEPATH = prove
 (`!s p q:real^1->real^N.
     homotopic_paths s (reversepath p) (reversepath q) <=>
     homotopic_paths s p q`,
  GEN_TAC THEN MATCH_MP_TAC(MESON[]
   `(!p. f(f p) = p) /\
    (!a b. homotopic_paths s a b ==> homotopic_paths s (f a) (f b))
    ==> !a b. homotopic_paths s (f a) (f b) <=>
              homotopic_paths s a b`) THEN
  REWRITE_TAC[REVERSEPATH_REVERSEPATH] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[homotopic_paths; homotopic_with; PCROSS; o_DEF] THEN DISCH_THEN
   (X_CHOOSE_THEN `h:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y:real^(1,1)finite_sum.
                 (h:real^(1,1)finite_sum->real^N)
                 (pastecart(fstcart y) (vec 1 - sndcart y))` THEN
  ASM_REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  ASM_SIMP_TAC[reversepath; pathstart; pathfinish; VECTOR_SUB_REFL;
               VECTOR_SUB_RZERO] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
               CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC;
        IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC];
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
     REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE h s SUBSET t ==> IMAGE g s SUBSET s
      ==> IMAGE h (IMAGE g s) SUBSET t`)) THEN
     SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC;
        IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
     REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC]);;

let HOMOTOPIC_PATHS_JOIN = prove
 (`!s p q p' q':real^1->real^N.
     homotopic_paths s p p' /\ homotopic_paths s q q' /\
     pathfinish p = pathstart q
     ==> homotopic_paths s (p ++ q) (p' ++ q')`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_paths; homotopic_with; PCROSS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k1:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `k2:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(\y. ((k1 o pastecart (fstcart y)) ++
                    (k2 o pastecart (fstcart y))) (sndcart y))
              :real^(1,1)finite_sum->real^N` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[PCROSS] HOMOTOPIC_JOIN_LEMMA) THEN
    ASM_REWRITE_TAC[o_DEF; PASTECART_FST_SND; ETA_AX] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_REWRITE_TAC[pathstart; pathfinish] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[ETA_AX; GSYM path_image; SET_RULE
      `(!x. x IN i ==> f x IN s) <=> IMAGE f i SUBSET s`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE; o_DEF] THEN ASM SET_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_REWRITE_TAC[joinpaths; o_DEF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  REWRITE_TAC[pathstart; pathfinish; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[VECTOR_ARITH `&2 % x - x:real^N = x`; VECTOR_MUL_RZERO]);;

let HOMOTOPIC_PATHS_CONTINUOUS_IMAGE = prove
 (`!f:real^1->real^M g h:real^M->real^N s t.
        homotopic_paths s f g /\
        h continuous_on s /\ IMAGE h s SUBSET t
        ==> homotopic_paths t (h o f) (h o g)`,
  REWRITE_TAC[homotopic_paths] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_MONO)) THEN
  SIMP_TAC[pathstart; pathfinish; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* Group properties for homotopy of paths (so taking equivalence classes     *)
(* under homotopy would give the fundamental group).                         *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_PATHS_RID = prove
 (`!s p. path p /\ path_image p SUBSET s
         ==> homotopic_paths s (p ++ linepath(pathfinish p,pathfinish p)) p`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_REPARAMETRIZE THEN
  ASM_REWRITE_TAC[joinpaths] THEN
  EXISTS_TAC `\t. if drop t <= &1 / &2 then &2 % t else vec 1` THEN
  ASM_REWRITE_TAC[DROP_VEC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; linepath; pathfinish;
              VECTOR_ARITH `(&1 - t) % x + t % x:real^N = x`] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `interval[vec 0:real^1,vec 1] =
      interval[vec 0,lift(&1 / &2)] UNION interval[lift(&1 / &2),vec 1]`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
      SIMP_TAC[CLOSED_INTERVAL; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST; IN_INTERVAL_1; DROP_VEC; LIFT_DROP;
               GSYM DROP_EQ; DROP_CMUL] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[DROP_CMUL; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC]);;

let HOMOTOPIC_PATHS_LID = prove
 (`!s p:real^1->real^N.
        path p /\ path_image p SUBSET s
        ==> homotopic_paths s (linepath(pathstart p,pathstart p) ++ p) p`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM HOMOTOPIC_PATHS_REVERSEPATH] THEN
  REWRITE_TAC[o_DEF; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
  SIMP_TAC[REVERSEPATH_JOINPATHS; REVERSEPATH_LINEPATH;
           PATHFINISH_LINEPATH] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `reversepath p :real^1->real^N`]
    HOMOTOPIC_PATHS_RID) THEN
  ASM_SIMP_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
               PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH]);;

let HOMOTOPIC_PATHS_ASSOC = prove
 (`!s p q r:real^1->real^N.
        path p /\ path_image p SUBSET s /\
        path q /\ path_image q SUBSET s /\
        path r /\ path_image r SUBSET s /\
        pathfinish p = pathstart q /\ pathfinish q = pathstart r
        ==> homotopic_paths s (p ++ (q ++ r)) ((p ++ q) ++ r)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_REPARAMETRIZE THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; UNION_SUBSET;
               PATHSTART_JOIN; PATHFINISH_JOIN] THEN
  REWRITE_TAC[joinpaths] THEN
  EXISTS_TAC `\t. if drop t <= &1 / &2 then inv(&2) % t
                  else if drop t <= &3 / &4 then t - lift(&1 / &4)
                  else &2 % t - vec 1` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_CASES_1 THEN
    SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; LIFT_DROP] THEN
    REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_CMUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_1 THEN
    SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID;
             CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_CMUL; GSYM LIFT_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    REWRITE_TAC[DROP_CMUL; DROP_VEC; LIFT_DROP; DROP_SUB] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[DROP_VEC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_RZERO];
    REWRITE_TAC[DROP_VEC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    VECTOR_ARITH_TAC;
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `drop t <= &1 / &2` THEN ASM_REWRITE_TAC[DROP_CMUL] THEN
    ASM_REWRITE_TAC[REAL_ARITH `inv(&2) * t <= &1 / &2 <=> t <= &1`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[REAL_MUL_LID] THEN
    ASM_CASES_TAC `drop t <= &3 / &4` THEN
    ASM_REWRITE_TAC[DROP_SUB; DROP_VEC; DROP_CMUL; LIFT_DROP;
                    REAL_ARITH `&2 * (t - &1 / &4) <= &1 / &2 <=> t <= &1 / &2`;
                    REAL_ARITH `&2 * t - &1 <= &1 / &2 <=> t <= &3 / &4`;
                    REAL_ARITH `t - &1 / &4 <= &1 / &2 <=> t <= &3 / &4`] THEN
    REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC; GSYM LIFT_CMUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM] THEN
    REWRITE_TAC[VECTOR_ARITH `a - b - b:real^N = a - &2 % b`]]);;

let HOMOTOPIC_PATHS_RINV = prove
 (`!s p:real^1->real^N.
        path p /\ path_image p SUBSET s
        ==> homotopic_paths s
              (p ++ reversepath p) (linepath(pathstart p,pathstart p))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
  REWRITE_TAC[homotopic_paths; homotopic_with; PCROSS] THEN
  EXISTS_TAC `(\y. (subpath (vec 0) (fstcart y) p ++
                    reversepath(subpath (vec 0) (fstcart y) p)) (sndcart y))
              : real^(1,1)finite_sum->real^N` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; SUBPATH_TRIVIAL] THEN
  REWRITE_TAC[ETA_AX; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
  REWRITE_TAC[REVERSEPATH_SUBPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[joinpaths] THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LE THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path; path_image]) THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[subpath; VECTOR_ADD_LID; VECTOR_SUB_RZERO] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
                 CONTINUOUS_ON_CMUL];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; FORALL_IN_GSPEC; IMP_CONJ] THEN
        REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC] THEN
        REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `drop x * &2 * &1 / &2` THEN CONJ_TAC THEN
        REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[subpath; VECTOR_ADD_LID; VECTOR_SUB_RZERO] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
                 CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; FORALL_IN_GSPEC; IMP_CONJ] THEN
        REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_CMUL; DROP_VEC; DROP_ADD;
         REAL_ARITH `t + (&0 - t) * (&2 * x - &1) =
                     t * &2 * (&1 - x)`] THEN
        REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_SUB_LE] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `drop x * &2 * &1 / &2` THEN CONJ_TAC THEN
        REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN
        ASM_REAL_ARITH_TAC];
      SIMP_TAC[o_DEF; LIFT_DROP; ETA_AX; LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
      REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[subpath] THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_SUB; DROP_VEC; DROP_ADD; DROP_CMUL;
                  LIFT_DROP] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; ETA_AX;
      SET_RULE `(!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t`] THEN
    REWRITE_TAC[GSYM path_image] THEN MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
    REWRITE_TAC[PATH_IMAGE_SUBPATH_GEN] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [path_image]) THEN
    MATCH_MP_TAC(SET_RULE
      `t SUBSET s /\ u SUBSET s
       ==> IMAGE p s SUBSET v
           ==> IMAGE p t SUBSET v /\ IMAGE p u SUBSET v`) THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_INTERVAL] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL];
    REWRITE_TAC[subpath; linepath; pathstart; joinpaths] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; DROP_VEC; VECTOR_MUL_LZERO] THEN
    REWRITE_TAC[VECTOR_ADD_RID; COND_ID] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[pathstart; PATHFINISH_LINEPATH; PATHSTART_LINEPATH]]);;

let HOMOTOPIC_PATHS_LINV = prove
 (`!s p:real^1->real^N.
        path p /\ path_image p SUBSET s
        ==> homotopic_paths s
              (reversepath p ++ p) (linepath(pathfinish p,pathfinish p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `reversepath p:real^1->real^N`]
        HOMOTOPIC_PATHS_RINV) THEN
  ASM_SIMP_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH] THEN
  REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
              REVERSEPATH_REVERSEPATH]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy of loops without requiring preservation of endpoints.            *)
(* ------------------------------------------------------------------------- *)

let homotopic_loops = new_definition
 `homotopic_loops s p q =
     homotopic_with
       (\r. pathfinish r = pathstart r)
       (interval[vec 0:real^1,vec 1],s)
       p q`;;

let HOMOTOPIC_LOOPS = prove
 (`!s p q:real^1->real^N.
      homotopic_loops s p q <=>
      ?h. h continuous_on
          interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1] /\
          IMAGE h (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1])
          SUBSET s /\
          (!x. x IN interval[vec 0,vec 1] ==> h(pastecart (vec 0) x) = p x) /\
          (!x. x IN interval[vec 0,vec 1] ==> h(pastecart (vec 1) x) = q x) /\
          (!t. t IN interval[vec 0:real^1,vec 1]
               ==> pathfinish(h o pastecart t) = pathstart(h o pastecart t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homotopic_loops] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HOMOTOPIC_WITH o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[pathstart; pathfinish; ENDS_IN_UNIT_INTERVAL];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let HOMOTOPIC_LOOPS_IMP_LOOP = prove
 (`!s p q. homotopic_loops s p q
           ==> pathfinish p = pathstart p /\
               pathfinish q = pathstart q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_loops] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN
  SIMP_TAC[]);;

let HOMOTOPIC_LOOPS_IMP_PATH = prove
 (`!s p q. homotopic_loops s p q ==> path p /\ path q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_loops] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
  SIMP_TAC[path]);;

let HOMOTOPIC_LOOPS_IMP_SUBSET = prove
 (`!s p q.
     homotopic_loops s p q ==> path_image p SUBSET s /\ path_image q SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_loops] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  SIMP_TAC[path_image]);;

let HOMOTOPIC_LOOPS_REFL = prove
 (`!s p. homotopic_loops s p p <=>
           path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p`,
  REWRITE_TAC[homotopic_loops; HOMOTOPIC_WITH_REFL; path; path_image]);;

let HOMOTOPIC_LOOPS_SYM = prove
 (`!s p q. homotopic_loops s p q <=> homotopic_loops s q p`,
  REWRITE_TAC[homotopic_loops; HOMOTOPIC_WITH_SYM]);;

let HOMOTOPIC_LOOPS_TRANS = prove
 (`!s p q r.
        homotopic_loops s p q /\ homotopic_loops s q r
        ==> homotopic_loops s p r`,
  REWRITE_TAC[homotopic_loops; HOMOTOPIC_WITH_TRANS]);;

let HOMOTOPIC_LOOPS_SUBSET = prove
 (`!s p q.
        homotopic_loops s p q /\ s SUBSET t
        ==> homotopic_loops t p q`,
  REWRITE_TAC[homotopic_loops; HOMOTOPIC_WITH_SUBSET_RIGHT]);;

let HOMOTOPIC_LOOPS_EQ = prove
 (`!p:real^1->real^N q s.
        path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
        (!t. t IN interval[vec 0,vec 1] ==> p(t) = q(t))
        ==> homotopic_loops s p q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_loops] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  REPEAT(EXISTS_TAC `p:real^1->real^N`) THEN
  ASM_SIMP_TAC[HOMOTOPIC_WITH_REFL] THEN
  ASM_REWRITE_TAC[GSYM path; GSYM path_image] THEN
  REWRITE_TAC[pathstart; pathfinish] THEN
  MESON_TAC[ENDS_IN_UNIT_INTERVAL]);;

let HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE = prove
 (`!f:real^1->real^M g h:real^M->real^N s t.
        homotopic_loops s f g /\
        h continuous_on s /\ IMAGE h s SUBSET t
        ==> homotopic_loops t (h o f) (h o g)`,
  REWRITE_TAC[homotopic_loops] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_MONO)) THEN
  SIMP_TAC[pathstart; pathfinish; o_THM]);;

let HOMOTOPIC_LOOPS_SHIFTPATH_SELF = prove
 (`!p:real^1->real^N t s.
        path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
        t IN interval[vec 0,vec 1]
        ==> homotopic_loops s p (shiftpath t p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMOTOPIC_LOOPS] THEN EXISTS_TAC
   `\z. shiftpath (drop t % fstcart z) (p:real^1->real^N) (sndcart z)` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; o_DEF] THEN
  REWRITE_TAC[GSYM LIFT_EQ_CMUL; VECTOR_MUL_RZERO; ETA_AX] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MATCH_MP_TAC(SET_RULE
     `IMAGE p t SUBSET u /\
      (!x. x IN s ==> IMAGE(shiftpath (f x) p) t = IMAGE p t)
      ==> (!x y. x IN s /\ y IN t ==> shiftpath (f x) p y  IN u)`) THEN
    ASM_REWRITE_TAC[GSYM path_image] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PATH_IMAGE_SHIFTPATH THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[REAL_LE_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[];
    SIMP_TAC[shiftpath; VECTOR_ADD_LID; IN_INTERVAL_1; DROP_VEC];
    REWRITE_TAC[LIFT_DROP];
    X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN MATCH_MP_TAC CLOSED_SHIFTPATH THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[REAL_LE_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[]] THEN
  REWRITE_TAC[shiftpath; DROP_ADD; DROP_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_LE THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_MUL; o_DEF; LIFT_DROP;
             LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
             CONTINUOUS_ON_CONST] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART] THEN
    REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1;
                 DROP_ADD; DROP_CMUL; DROP_VEC; REAL_LE_ADD; REAL_LE_MUL];
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_MUL; o_DEF; LIFT_DROP;
             LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
             CONTINUOUS_ON_CONST; CONTINUOUS_ON_SUB] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART] THEN
    REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; DROP_SUB;
                 DROP_ADD; DROP_CMUL; DROP_VEC; REAL_LE_ADD; REAL_LE_MUL] THEN
    SIMP_TAC[REAL_ARITH `&0 <= x + y - &1 <=> &1 <= x + y`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `t * x <= &1 * &1 /\ y <= &1 ==> t * x + y - &1 <= &1`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL2; REAL_POS];
    REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_CMUL; LIFT_DROP] THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CMUL; LINEAR_CONTINUOUS_ON;
             LINEAR_FSTCART; LINEAR_SNDCART];
    SIMP_TAC[GSYM LIFT_EQ; LIFT_ADD; LIFT_CMUL; LIFT_DROP; LIFT_NUM;
             VECTOR_ARITH `a + b - c:real^1 = (a + b) - c`] THEN
    ASM_MESON_TAC[VECTOR_SUB_REFL; pathstart; pathfinish]]);;

(* ------------------------------------------------------------------------- *)
(* Relations between the two variants of homotopy.                           *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS = prove
 (`!s p q. homotopic_paths s p q /\
           pathfinish p = pathstart p /\
           pathfinish q = pathstart p
           ==> homotopic_loops s p q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_paths; homotopic_loops] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_MONO) THEN
  ASM_SIMP_TAC[]);;

let HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL = prove
 (`!s p a:real^N.
        homotopic_loops s p (linepath(a,a))
        ==> homotopic_paths s p (linepath(pathstart p,pathstart p))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_loops]) THEN
  REWRITE_TAC[homotopic_with; PCROSS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:real^(1,1)finite_sum->real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN EXISTS_TAC
   `(p:real^1->real^N) ++ linepath(pathfinish p,pathfinish p)` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[HOMOTOPIC_PATHS_RID; HOMOTOPIC_PATHS_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN EXISTS_TAC
   `linepath(pathstart p,pathstart p) ++ (p:real^1->real^N) ++
    linepath(pathfinish p,pathfinish p)` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MP_TAC(ISPECL [`s:real^N->bool`;
       `(p:real^1->real^N) ++ linepath(pathfinish p,pathfinish p)`]
     HOMOTOPIC_PATHS_LID) THEN
    REWRITE_TAC[PATHSTART_JOIN] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_LINEPATH; PATHSTART_LINEPATH] THEN
    MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
    ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN EXISTS_TAC
   `((\u. (h:real^(1,1)finite_sum->real^N) (pastecart u (vec 0))) ++
     linepath(a,a) ++
     reversepath(\u. h (pastecart u (vec 0))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(MESON[HOMOTOPIC_PATHS_LID; HOMOTOPIC_PATHS_JOIN;
                       HOMOTOPIC_PATHS_TRANS; HOMOTOPIC_PATHS_SYM;
                       HOMOTOPIC_PATHS_RINV]
       `(path p /\ path(reversepath p)) /\
        (path_image p SUBSET s /\ path_image(reversepath p) SUBSET s) /\
        (pathfinish p = pathstart(linepath(b,b) ++ reversepath p) /\
         pathstart(reversepath p) = b) /\
        pathstart p = a
        ==> homotopic_paths s (p ++ linepath(b,b) ++ reversepath p)
                              (linepath(a,a))`) THEN
    REWRITE_TAC[PATHSTART_REVERSEPATH; PATHSTART_JOIN; PATH_REVERSEPATH;
                PATH_IMAGE_REVERSEPATH; PATHSTART_LINEPATH] THEN
    ASM_REWRITE_TAC[path; path_image; pathstart; pathfinish;
                    LINEPATH_REFL] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM;
               ENDS_IN_UNIT_INTERVAL];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          SUBSET_TRANS)) THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
      REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM;
               ENDS_IN_UNIT_INTERVAL]]] THEN
  REWRITE_TAC[homotopic_paths; homotopic_with; PCROSS] THEN
  EXISTS_TAC
   `\y:real^(1,1)finite_sum.
        (subpath (vec 0) (fstcart y) (\u. h(pastecart u (vec 0))) ++
         (\u. (h:real^(1,1)finite_sum->real^N) (pastecart (fstcart y) u)) ++
         subpath (fstcart y) (vec 0) (\u. h(pastecart u (vec 0))))
        (sndcart y)` THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; SUBPATH_TRIVIAL;
                  SUBPATH_REFL; SUBPATH_REVERSEPATH; ETA_AX;
                  PATHSTART_JOIN; PATHFINISH_JOIN;
                  PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                  PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[pathstart]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[PCROSS] HOMOTOPIC_JOIN_LEMMA) THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[PCROSS] HOMOTOPIC_JOIN_LEMMA) THEN
      ASM_REWRITE_TAC[PASTECART_FST_SND; ETA_AX] THEN CONJ_TAC THENL
       [ALL_TAC;
        RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
        REWRITE_TAC[PATHSTART_SUBPATH] THEN
        ASM_SIMP_TAC[pathstart; pathfinish]];
      RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
      REWRITE_TAC[PATHFINISH_SUBPATH; PATHSTART_JOIN] THEN
      ASM_SIMP_TAC[pathstart]] THEN
    REWRITE_TAC[subpath] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; VECTOR_SUB_LZERO; VECTOR_ADD_LID] THEN
    (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
       [CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ADD; CONTINUOUS_ON_MUL;
        LIFT_DROP; CONTINUOUS_ON_NEG; DROP_NEG; CONTINUOUS_ON_CONST;
        CONTINUOUS_ON_ID; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
        LIFT_NEG; o_DEF; ETA_AX] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1] THEN
    REWRITE_TAC[DROP_ADD; DROP_NEG; DROP_VEC; DROP_CMUL; REAL_POS] THEN
    SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; REAL_ARITH
     `t + --t * x = t * (&1 - x)`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `t * x <= t * &1 /\ &1 * t <= &1 * &1 ==> t * x <= &1`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;

    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; IMP_CONJ;
      RIGHT_FORALL_IMP_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    REWRITE_TAC[SET_RULE
     `(!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t`] THEN
    REWRITE_TAC[GSYM path_image; ETA_AX] THEN
    REPEAT(MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN CONJ_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      SUBSET_TRANS)) THEN
    REWRITE_TAC[path_image; subpath] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM] THEN
    SIMP_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC; DROP_CMUL; DROP_ADD] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_SUB_RZERO; REAL_POS] THEN
    REWRITE_TAC[REAL_ARITH `t + (&0 - t) * x = t * (&1 - x)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE] THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]);;

let HOMOTOPIC_LOOPS_CONJUGATE = prove
 (`!p q s:real^N->bool.
        path p /\ path_image p SUBSET s /\
        path q /\ path_image q SUBSET s /\
        pathfinish p = pathstart q /\ pathfinish q = pathstart q
        ==> homotopic_loops s (p ++ q ++ reversepath p) q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN EXISTS_TAC
   `linepath(pathstart q,pathstart q) ++ (q:real^1->real^N) ++
    linepath(pathstart q,pathstart q)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
    MP_TAC(ISPECL [`s:real^N->bool`;
       `(q:real^1->real^N) ++ linepath(pathfinish q,pathfinish q)`]
     HOMOTOPIC_PATHS_LID) THEN
    ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; UNION_SUBSET; SING_SUBSET;
                 PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH;
                 PATH_JOIN; PATH_IMAGE_JOIN; PATH_LINEPATH; SEGMENT_REFL] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_PATHS_TRANS) THEN
    ASM_MESON_TAC[HOMOTOPIC_PATHS_RID]] THEN
  REWRITE_TAC[homotopic_loops; homotopic_with; PCROSS] THEN
  EXISTS_TAC
   `(\y. (subpath (fstcart y) (vec 1) p ++ q ++ subpath (vec 1) (fstcart y) p)
         (sndcart y)):real^(1,1)finite_sum->real^N` THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; SUBPATH_TRIVIAL;
                  SUBPATH_REFL; SUBPATH_REVERSEPATH; ETA_AX;
                 PATHSTART_JOIN; PATHFINISH_JOIN;
                  PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                  PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  ASM_REWRITE_TAC[pathstart; pathfinish] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[path; path_image]) THEN
    MATCH_MP_TAC(REWRITE_RULE[PCROSS] HOMOTOPIC_JOIN_LEMMA) THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[PCROSS] HOMOTOPIC_JOIN_LEMMA) THEN
      REPEAT CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
        SIMP_TAC[SNDCART_PASTECART];
        ALL_TAC;
        REWRITE_TAC[PATHSTART_SUBPATH] THEN ASM_REWRITE_TAC[pathfinish]];
      REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_SUBPATH] THEN
      ASM_REWRITE_TAC[pathstart]] THEN
    REWRITE_TAC[subpath] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    (CONJ_TAC THENL
      [REWRITE_TAC[DROP_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
       SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST; LINEAR_FSTCART] THEN
       MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
       SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
       REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
       SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON;
                LINEAR_FSTCART];
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
       REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
       REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1] THEN
       REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_VEC; DROP_CMUL]])
    THENL
     [REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        TRY(MATCH_MP_TAC REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH `t + (&1 - t) * x <= &1 <=>
                                (&1 - t) * x <= (&1 - t) * &1`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH
         `x * (&1 - t) <= x * &1 /\ x <= &1
          ==> &0 <= &1 + (t - &1) * x`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH
         `a + (t - &1) * x <= a <=> &0 <= (&1 - t) * x`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[ETA_AX; GSYM path_image; SET_RULE
      `(!x. x IN i ==> f x IN s) <=> IMAGE f i SUBSET s`] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `path_image p:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PATH_IMAGE_SUBPATH_SUBSET THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]]);;

(* ------------------------------------------------------------------------- *)
(* Relating homotopy of trivial loops to path-connectedness.                 *)
(* ------------------------------------------------------------------------- *)

let PATH_COMPONENT_IMP_HOMOTOPIC_POINTS = prove
 (`!s a b:real^N.
        path_component s a b
        ==> homotopic_loops s (linepath(a,a)) (linepath(b,b))`,
  REWRITE_TAC[path_component; homotopic_loops; homotopic_with; PCROSS] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[pathstart; pathfinish; path_image; path] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y:real^(1,1)finite_sum. (g(fstcart y):real^N)` THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; linepath] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - x) % a + x % a:real^N = a`] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; FSTCART_PASTECART]);;

let HOMOTOPIC_LOOPS_IMP_PATH_COMPONENT_VALUE = prove
 (`!s p q:real^1->real^N t.
        homotopic_loops s p q /\ t IN interval[vec 0,vec 1]
        ==> path_component s (p t) (q t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[path_component; homotopic_loops; homotopic_with; PCROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,1)finite_sum->real^N` MP_TAC) THEN
  STRIP_TAC THEN
  EXISTS_TAC `\u. (h:real^(1,1)finite_sum->real^N) (pastecart u t)` THEN
  ASM_REWRITE_TAC[pathstart; pathfinish] THEN CONJ_TAC THENL
   [REWRITE_TAC[path] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      ASM SET_TAC[]];
    REWRITE_TAC[path_image] THEN ASM SET_TAC[]]);;

let HOMOTOPIC_POINTS_EQ_PATH_COMPONENT = prove
 (`!s a b:real^N.
        homotopic_loops s (linepath(a,a)) (linepath(b,b)) <=>
        path_component s a b`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  REWRITE_TAC[PATH_COMPONENT_IMP_HOMOTOPIC_POINTS] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^1` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    HOMOTOPIC_LOOPS_IMP_PATH_COMPONENT_VALUE)) THEN
  REWRITE_TAC[linepath; IN_INTERVAL_1; DROP_VEC; REAL_POS] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - &0) % a + &0 % b:real^N = a`]);;

let PATH_CONNECTED_EQ_HOMOTOPIC_POINTS = prove
 (`!s:real^N->bool.
        path_connected s <=>
        !a b. a IN s /\ b IN s
              ==> homotopic_loops s (linepath(a,a)) (linepath(b,b))`,
  GEN_TAC THEN REWRITE_TAC[HOMOTOPIC_POINTS_EQ_PATH_COMPONENT] THEN
  REWRITE_TAC[path_connected; path_component]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy of "nearby" function, paths and loops.                           *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH_LINEAR = prove
 (`!f g:real^M->real^N s t.
        f continuous_on s /\ g continuous_on s /\
        (!x. x IN s ==> segment[f x,g x] SUBSET t)
        ==> homotopic_with (\z. T) (s,t) f g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_with] THEN
  EXISTS_TAC
    `\y. ((&1 - drop(fstcart y)) % (f:real^M->real^N)(sndcart y) +
         drop(fstcart y) % g(sndcart y):real^N)` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_SUB_RZERO] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - t) % a + t % a:real^N = a`] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
  REWRITE_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; LIFT_SUB] THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON;
             LINEAR_FSTCART; ETA_AX] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    SIMP_TAC[SNDCART_PASTECART; FORALL_IN_PCROSS];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `u:real^M`] THEN STRIP_TAC THEN
    SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `u:real^M` THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `drop t` THEN
    ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC]]);;

let HOMOTOPIC_PATHS_LINEAR,HOMOTOPIC_LOOPS_LINEAR = (CONJ_PAIR o prove)
 (`(!g s:real^N->bool h.
        path g /\ path h /\
        pathstart h = pathstart g /\ pathfinish h = pathfinish g /\
        (!t x. t IN interval[vec 0,vec 1] ==> segment[g t,h t] SUBSET s)
        ==> homotopic_paths s g h) /\
   (!g s:real^N->bool h.
        path g /\ path h /\
        pathfinish g = pathstart g /\ pathfinish h = pathstart h /\
        (!t x. t IN interval[vec 0,vec 1] ==> segment[g t,h t] SUBSET s)
        ==> homotopic_loops s g h)`,
  CONJ_TAC THEN
 (REWRITE_TAC[pathstart; pathfinish] THEN
  REWRITE_TAC[SUBSET; RIGHT_IMP_FORALL_THM; IMP_IMP] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[homotopic_paths; homotopic_loops; homotopic_with; PCROSS] THEN
  EXISTS_TAC
   `\y:real^(1,1)finite_sum.
      ((&1 - drop(fstcart y)) % g(sndcart y) +
       drop(fstcart y) % h(sndcart y):real^N)` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
  ASM_REWRITE_TAC[pathstart; pathfinish; REAL_SUB_REFL; REAL_SUB_RZERO] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - t) % a + t % a:real^N = a`] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
  REWRITE_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; LIFT_SUB] THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON;
             LINEAR_FSTCART; ETA_AX] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    SIMP_TAC[SNDCART_PASTECART];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `u:real^1`] THEN STRIP_TAC THEN
    SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `u:real^1` THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `drop t` THEN
    ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC]]));;

let HOMOTOPIC_PATHS_NEARBY_EXPLICIT,
    HOMOTOPIC_LOOPS_NEARBY_EXPLICIT = (CONJ_PAIR o prove)
 (`(!g s:real^N->bool h.
        path g /\ path h /\
        pathstart h = pathstart g /\ pathfinish h = pathfinish g /\
        (!t x. t IN interval[vec 0,vec 1] /\ ~(x IN s)
               ==> norm(h t - g t) < norm(g t - x))
        ==> homotopic_paths s g h) /\
   (!g s:real^N->bool h.
        path g /\ path h /\
        pathfinish g = pathstart g /\ pathfinish h = pathstart h /\
        (!t x. t IN interval[vec 0,vec 1] /\ ~(x IN s)
               ==> norm(h t - g t) < norm(g t - x))
        ==> homotopic_loops s g h)`,
  ONCE_REWRITE_TAC[TAUT `p /\ ~q ==> r <=> p /\ ~r ==> q`] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_LINEAR;
    MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; segment; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `t:real^1` THEN
  ASM_REWRITE_TAC[REAL_NOT_LT] THEN
  MP_TAC(ISPECL [`(g:real^1->real^N) t`; `(h:real^1->real^N) t`]
      DIST_IN_CLOSED_SEGMENT) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  REWRITE_TAC[segment; FORALL_IN_GSPEC;
              ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
  ASM_MESON_TAC[]);;

let HOMOTOPIC_NEARBY_PATHS,HOMOTOPIC_NEARBY_LOOPS = (CONJ_PAIR o prove)
 (`(!g s:real^N->bool.
        path g /\ open s /\ path_image g SUBSET s
        ==> ?e. &0 < e /\
                !h. path h /\
                    pathstart h = pathstart g /\
                    pathfinish h = pathfinish g /\
                    (!t. t IN interval[vec 0,vec 1] ==> norm(h t - g t) < e)
                    ==> homotopic_paths s g h) /\
   (!g s:real^N->bool.
        path g /\ pathfinish g = pathstart g /\ open s /\ path_image g SUBSET s
        ==> ?e. &0 < e /\
                !h. path h /\
                    pathfinish h = pathstart h /\
                    (!t. t IN interval[vec 0,vec 1] ==> norm(h t - g t) < e)
                    ==> homotopic_loops s g h)`,
  CONJ_TAC THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`path_image g:real^N->bool`; `(:real^N) DIFF s`]
        SEPARATE_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_PATH_IMAGE; GSYM OPEN_CLOSED] THEN
  (ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_DIFF; IN_UNIV; dist]]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  REWRITE_TAC[REAL_NOT_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `h:real^1->real^N` THEN STRIP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_NEARBY_EXPLICIT;
    MATCH_MP_TAC HOMOTOPIC_LOOPS_NEARBY_EXPLICIT] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e:real` THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[path_image] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy of non-antipodal sphere maps.                                    *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_NON_MIDPOINT_SPHEREMAPS = prove
 (`!f g:real^M->real^N s a r.
        f continuous_on s /\ IMAGE f s SUBSET sphere(a,r) /\
        g continuous_on s /\ IMAGE g s SUBSET sphere(a,r) /\
        (!x. x IN s ==> ~(midpoint(f x,g x) = a))
    ==> homotopic_with (\x. T) (s,sphere(a,r)) f g`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r <= &0` THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    REPEAT(EXISTS_TAC `g:real^M->real^N`) THEN
    ASM_REWRITE_TAC[HOMOTOPIC_WITH_REFL] THEN
    SUBGOAL_THEN `?c:real^N. sphere(a,r) SUBSET {c}` MP_TAC THENL
     [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_CASES_TAC `r = &0` THEN
    ASM_SIMP_TAC[SPHERE_SING; SPHERE_EMPTY; REAL_LT_LE] THEN
    MESON_TAC[SUBSET_REFL; EMPTY_SUBSET];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `homotopic_with (\z. T) (s:real^M->bool,(:real^N) DELETE a) f g`
  MP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
    ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DELETE a <=> ~(a IN s)`] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET])) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_SPHERE; IMP_IMP] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    FIRST_X_ASSUM(MP_TAC o GSYM o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; MIDPOINT_BETWEEN] THEN
    MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o
    ISPECL [`\y:real^N. a + r / norm(y - a) % (y - a)`;
            `sphere(a:real^N,r)`] o
    MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
  REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[real_div; o_DEF; LIFT_CMUL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
      SIMP_TAC[IN_DELETE; NORM_EQ_0; VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_DELETE; IN_SPHERE] THEN
      REWRITE_TAC[NORM_ARITH `dist(a:real^N,a + b) = norm b`] THEN
      SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[real_abs; REAL_LE_RMUL; REAL_DIV_RMUL;
                   NORM_EQ_0; VECTOR_SUB_EQ; REAL_LT_IMP_LE]];
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; IN_SPHERE]) THEN
      ASM_SIMP_TAC[NORM_ARITH `norm(a - b:real^N) = dist(b,a)`] THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ] THEN REPEAT STRIP_TAC THEN
      VECTOR_ARITH_TAC]);;

let HOMOTOPIC_NON_ANTIPODAL_SPHEREMAPS = prove
 (`!f g:real^M->real^N s r.
        f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0,r) /\
        g continuous_on s /\ IMAGE g s SUBSET sphere(vec 0,r) /\
        (!x. x IN s ==> ~(f x = --g x))
    ==> homotopic_with (\x. T) (s,sphere(vec 0,r)) f g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_NON_MIDPOINT_SPHEREMAPS THEN
  ASM_REWRITE_TAC[midpoint; VECTOR_ARITH
   `inv(&2) % (a + b):real^N = vec 0 <=> a = --b`]);;

(* ------------------------------------------------------------------------- *)
(* Retracts, in a general sense, preserve (co)homotopic triviality.          *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPICALLY_TRIVIAL_RETRACTION_GEN = prove
 (`!P Q s:real^M->bool t:real^N->bool u:real^P->bool h k.
        (h continuous_on s /\ IMAGE h s = t /\
         k continuous_on t /\ IMAGE k t SUBSET s /\
         (!y. y IN t ==> h(k y) = y) /\
         (!f. f continuous_on u /\ IMAGE f u SUBSET t /\ Q f ==> P(k o f)) /\
         (!f. f continuous_on u /\ IMAGE f u SUBSET s /\ P f ==> Q(h o f)) /\
         (!h k. (!x. x IN u ==> h x = k x) ==> (Q h <=> Q k))) /\
        (!f g. f continuous_on u /\ IMAGE f u SUBSET s /\ P f /\
               g continuous_on u /\ IMAGE g u SUBSET s /\ P g
               ==> homotopic_with P (u,s)  f g)
        ==> (!f g. f continuous_on u /\ IMAGE f u SUBSET t /\ Q f /\
                   g continuous_on u /\ IMAGE g u SUBSET t /\ Q g
                   ==> homotopic_with Q (u,t) f g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`p:real^P->real^N`; `q:real^P->real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`(k:real^N->real^M) o (p:real^P->real^N)`;
    `(k:real^N->real^M) o (q:real^P->real^N)`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IMAGE_o] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE) THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
    ASM SET_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN MAP_EVERY EXISTS_TAC
   [`(h:real^M->real^N) o (k:real^N->real^M) o (p:real^P->real^N)`;
    `(h:real^M->real^N) o (k:real^N->real^M) o (q:real^P->real^N)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_MONO)) THEN
  ASM_SIMP_TAC[]);;

let HOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN = prove
 (`!P Q s:real^M->bool t:real^N->bool u:real^P->bool h k.
        (h continuous_on s /\ IMAGE h s = t /\
         k continuous_on t /\ IMAGE k t SUBSET s /\
         (!y. y IN t ==> h(k y) = y) /\
         (!f. f continuous_on u /\ IMAGE f u SUBSET t /\ Q f ==> P(k o f)) /\
         (!f. f continuous_on u /\ IMAGE f u SUBSET s /\ P f ==> Q(h o f)) /\
         (!h k. (!x. x IN u ==> h x = k x) ==> (Q h <=> Q k))) /\
        (!f. f continuous_on u /\ IMAGE f u SUBSET s /\ P f
             ==> ?c. homotopic_with P (u,s) f (\x. c))
        ==> (!f. f continuous_on u /\ IMAGE f u SUBSET t /\ Q f
                 ==> ?c. homotopic_with Q (u,t) f (\x. c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `p:real^P->real^N` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
    `(k:real^N->real^M) o (p:real^P->real^N)`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IMAGE_o] THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE) THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `c:real^M`)] THEN
  EXISTS_TAC `(h:real^M->real^N) c` THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN MAP_EVERY EXISTS_TAC
   [`(h:real^M->real^N) o (k:real^N->real^M) o (p:real^P->real^N)`;
    `(h:real^M->real^N) o ((\x. c):real^P->real^M)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_MONO)) THEN
  ASM_SIMP_TAC[]);;

let COHOMOTOPICALLY_TRIVIAL_RETRACTION_GEN = prove
 (`!P Q s:real^M->bool t:real^N->bool u:real^P->bool h k.
        (h continuous_on s /\ IMAGE h s = t /\
         k continuous_on t /\ IMAGE k t SUBSET s /\
         (!y. y IN t ==> h(k y) = y) /\
         (!f. f continuous_on t /\ IMAGE f t SUBSET u /\ Q f ==> P(f o h)) /\
         (!f. f continuous_on s /\ IMAGE f s SUBSET u /\ P f ==> Q(f o k)) /\
         (!h k. (!x. x IN t ==> h x = k x) ==> (Q h <=> Q k))) /\
        (!f g. f continuous_on s /\ IMAGE f s SUBSET u /\ P f /\
               g continuous_on s /\ IMAGE g s SUBSET u /\ P g
               ==> homotopic_with P (s,u) f g)
        ==> (!f g. f continuous_on t /\ IMAGE f t SUBSET u /\ Q f /\
                   g continuous_on t /\ IMAGE g t SUBSET u /\ Q g
                   ==> homotopic_with Q (t,u) f g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`p:real^N->real^P`; `q:real^N->real^P`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`(p:real^N->real^P) o (h:real^M->real^N)`;
    `(q:real^N->real^P) o (h:real^M->real^N)`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IMAGE_o] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE) THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
    ASM SET_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN MAP_EVERY EXISTS_TAC
   [`((p:real^N->real^P) o (h:real^M->real^N)) o (k:real^N->real^M)`;
    `((q:real^N->real^P) o (h:real^M->real^N)) o (k:real^N->real^M)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_MONO)) THEN
  ASM_SIMP_TAC[]);;

let COHOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN = prove
 (`!P Q s:real^M->bool t:real^N->bool u:real^P->bool h k.
        (h continuous_on s /\ IMAGE h s = t /\
         k continuous_on t /\ IMAGE k t SUBSET s /\
         (!y. y IN t ==> h(k y) = y) /\
         (!f. f continuous_on t /\ IMAGE f t SUBSET u /\ Q f ==> P(f o h)) /\
         (!f. f continuous_on s /\ IMAGE f s SUBSET u /\ P f ==> Q(f o k)) /\
         (!h k. (!x. x IN t ==> h x = k x) ==> (Q h <=> Q k))) /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET u /\ P f
             ==> ?c. homotopic_with P (s,u) f (\x. c))
        ==> (!f. f continuous_on t /\ IMAGE f t SUBSET u /\ Q f
                 ==> ?c. homotopic_with Q (t,u) f (\x. c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `p:real^N->real^P` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
    `(p:real^N->real^P) o (h:real^M->real^N)`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IMAGE_o] THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE) THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^P` THEN DISCH_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN MAP_EVERY EXISTS_TAC
   [`((p:real^N->real^P) o (h:real^M->real^N)) o (k:real^N->real^M)`;
    `((\x. c):real^M->real^P) o (k:real^N->real^M)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_MONO)) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Another useful lemma.                                                     *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_JOIN_SUBPATHS = prove
 (`!g:real^1->real^N s.
       path g /\ path_image g SUBSET s /\
       u IN interval[vec 0,vec 1] /\
       v IN interval[vec 0,vec 1] /\
       w IN interval[vec 0,vec 1]
       ==> homotopic_paths s (subpath u v g ++ subpath v w g) (subpath u w g)`,
  let lemma1 = prove
   (`!g:real^1->real^N s.
         drop u <= drop v /\ drop v <= drop w
         ==> path g /\ path_image g SUBSET s /\
             u IN interval[vec 0,vec 1] /\
             v IN interval[vec 0,vec 1] /\
             w IN interval[vec 0,vec 1] /\
             drop u <= drop v /\ drop v <= drop w
             ==> homotopic_paths s
                 (subpath u v g ++ subpath v w g) (subpath u w g)`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN
    EXISTS_TAC `path_image g:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `w:real^1 = u` THENL
     [MP_TAC(ISPECL
      [`path_image g:real^N->bool`;
       `subpath u v (g:real^1->real^N)`] HOMOTOPIC_PATHS_RINV) THEN
      ASM_REWRITE_TAC[REVERSEPATH_SUBPATH; SUBPATH_REFL] THEN
      REWRITE_TAC[LINEPATH_REFL; PATHSTART_SUBPATH] THEN
      ASM_SIMP_TAC[PATH_SUBPATH; PATH_IMAGE_SUBPATH_SUBSET];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_REPARAMETRIZE THEN
    ASM_SIMP_TAC[PATH_SUBPATH; PATH_IMAGE_SUBPATH_SUBSET] THEN
    EXISTS_TAC
    `\t. if drop t <= &1 / &2
         then inv(drop(w - u)) % (&2 * drop(v - u)) % t
         else inv(drop(w - u)) %
              ((v - u) + drop(w - v) % (&2 % t - vec 1))` THEN
    REWRITE_TAC[DROP_VEC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_RZERO] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CASES_1 THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP; GSYM LIFT_NUM;
                  DROP_ADD; DROP_SUB] THEN
      (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
        [CONTINUOUS_ON_MUL; o_DEF; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID;
         CONTINUOUS_ON_SUB; CONTINUOUS_ON_ADD] THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `drop u < drop w` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_LE; DROP_EQ] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC; DROP_ADD; DROP_SUB] THEN
      ONCE_REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
      (CONJ_TAC THENL
        [REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
         REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
         ASM_REAL_ARITH_TAC;
         ALL_TAC]) THEN
      REWRITE_TAC[REAL_ARITH `v - u + x * t <= w - u <=> x * t <= w - v`;
                  REAL_ARITH `(&2 * x) * t = x * &2 * t`] THEN
      MATCH_MP_TAC(REAL_ARITH `a * t <= a * &1 /\ a <= b ==> a * t <= b`) THEN
      (CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL; ALL_TAC]) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; DROP_ADD; DROP_CMUL; DROP_SUB] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_ARITH `(v - u) + (w - v) * &1 = w - u`] THEN
      ASM_SIMP_TAC[REAL_SUB_0; DROP_EQ; REAL_MUL_LINV];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      REWRITE_TAC[subpath; joinpaths] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; DROP_EQ_0; VECTOR_SUB_EQ] THEN
      AP_TERM_TAC THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; DROP_ADD; DROP_CMUL; DROP_SUB] THEN
      REAL_ARITH_TAC]) in
  let lemma2 = prove
   (`path g /\ path_image g SUBSET s /\
     u IN interval[vec 0,vec 1] /\
     v IN interval[vec 0,vec 1] /\
     w IN interval[vec 0,vec 1] /\
     homotopic_paths s (subpath u v g ++ subpath v w g) (subpath u w g)
     ==> homotopic_paths s (subpath w v g ++ subpath v u g) (subpath w u g)`,
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM HOMOTOPIC_PATHS_REVERSEPATH] THEN
    SIMP_TAC[REVERSEPATH_JOINPATHS; PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    ASM_REWRITE_TAC[REVERSEPATH_SUBPATH]) in
  let lemma3 = prove
   (`path (g:real^1->real^N) /\ path_image g SUBSET s /\
     u IN interval[vec 0,vec 1] /\
     v IN interval[vec 0,vec 1] /\
     w IN interval[vec 0,vec 1] /\
     homotopic_paths s (subpath u v g ++ subpath v w g) (subpath u w g)
     ==> homotopic_paths s (subpath v w g ++ subpath w u g) (subpath v u g)`,
    let tac =
      ASM_MESON_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH; PATH_SUBPATH;
                 HOMOTOPIC_PATHS_REFL; PATH_IMAGE_SUBPATH_SUBSET; SUBSET_TRANS;
                 PATHSTART_JOIN; PATHFINISH_JOIN] in
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM HOMOTOPIC_PATHS_REVERSEPATH] THEN
    SIMP_TAC[REVERSEPATH_JOINPATHS; PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    ASM_REWRITE_TAC[REVERSEPATH_SUBPATH] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC
     `(subpath u v g ++ subpath v w g) ++ subpath w v g:real^1->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
      ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
      ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL] THEN tac;
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC
     `subpath u v g ++ (subpath v w g ++ subpath w v g):real^1->real^N` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN tac;
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC
     `(subpath u v g :real^1->real^N) ++
      linepath(pathfinish(subpath u v g),pathfinish(subpath u v g))` THEN
    CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC HOMOTOPIC_PATHS_RID THEN tac] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    REPEAT CONJ_TAC THENL [tac; ALL_TAC; tac] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC
     `linepath(pathstart(subpath v w g):real^N,pathstart(subpath v w g))` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REVERSEPATH_SUBPATH] THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_RINV THEN tac;
      ALL_TAC] THEN
    REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH; HOMOTOPIC_PATHS_REFL;
                PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL;
                INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_MESON_TAC[path_image; IN_IMAGE; SUBSET]) in
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (REAL_ARITH `(drop u <= drop v /\ drop v <= drop w \/
                   drop w <= drop v /\ drop v <= drop u) \/
                  (drop u <= drop w /\ drop w <= drop v \/
                   drop v <= drop w /\ drop w <= drop u) \/
                  (drop v <= drop u /\ drop u <= drop w \/
                   drop w <= drop u /\ drop u <= drop v)`) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`g:real^1->real^N`; `s:real^N->bool`] o
    MATCH_MP lemma1) THEN
  ASM_MESON_TAC[lemma2; lemma3]);;

let HOMOTOPIC_LOOPS_SHIFTPATH = prove
 (`!s:real^N->bool p q u.
        homotopic_loops s p q /\ u IN interval[vec 0,vec 1]
        ==> homotopic_loops s (shiftpath u p) (shiftpath u q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_loops; homotopic_with; PCROSS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN DISCH_THEN(
   (X_CHOOSE_THEN `h:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC
   `\z. shiftpath u (\t. (h:real^(1,1)finite_sum->real^N)
                         (pastecart (fstcart z) t)) (sndcart z)` THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; ETA_AX] THEN
  ASM_SIMP_TAC[CLOSED_SHIFTPATH] THEN CONJ_TAC THENL
   [REWRITE_TAC[shiftpath; DROP_ADD; REAL_ARITH
     `u + z <= &1 <=> z <= &1 - u`] THEN
    SUBGOAL_THEN
     `{ pastecart (t:real^1) (x:real^1) |
        t IN interval[vec 0,vec 1] /\ x IN interval[vec 0,vec 1]} =
      { pastecart (t:real^1) (x:real^1) |
        t IN interval[vec 0,vec 1] /\ x IN interval[vec 0,vec 1 - u]} UNION
      { pastecart (t:real^1) (x:real^1) |
        t IN interval[vec 0,vec 1] /\ x IN interval[vec 1 - u,vec 1]}`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `s UNION s' = u
        ==> {f t x | t IN i /\ x IN u} =
            {f t x | t IN i /\ x IN s} UNION
            {f t x | t IN i /\ x IN s'}`) THEN
      UNDISCH_TAC `(u:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[EXTENSION; IN_INTERVAL_1; IN_UNION; DROP_SUB; DROP_VEC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    SIMP_TAC[REWRITE_RULE[PCROSS] CLOSED_PCROSS; CLOSED_INTERVAL] THEN
    REWRITE_TAC[FORALL_AND_THM; FORALL_IN_GSPEC; TAUT
     `p /\ q \/ r /\ s ==> t <=> (p ==> q ==> t) /\ (r ==> s ==> t)`] THEN
    SIMP_TAC[SNDCART_PASTECART; IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN
    SIMP_TAC[REAL_ARITH `&1 - u <= x ==> (x <= &1 - u <=> x = &1 - u)`] THEN
    SIMP_TAC[GSYM LIFT_EQ; LIFT_SUB; LIFT_DROP; LIFT_NUM] THEN
    REWRITE_TAC[FSTCART_PASTECART; VECTOR_ARITH `u + v - u:real^N = v`;
                VECTOR_ARITH `u + v - u - v:real^N = vec 0`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_SIMP_TAC[GSYM IN_INTERVAL_1; GSYM DROP_VEC] THEN CONJ_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST;
             LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
             VECTOR_ARITH `u + z - v:real^N = (u - v) + z`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN
    UNDISCH_TAC `(u:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1;
                IN_ELIM_PASTECART_THM; DROP_ADD; DROP_SUB; DROP_VEC] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; SET_RULE
     `(!t x. t IN i /\ x IN i ==> f t x IN s) <=>
      (!t. t IN i ==> IMAGE (f t) i SUBSET s)`] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN REWRITE_TAC[GSYM path_image] THEN
    ASM_SIMP_TAC[PATH_IMAGE_SHIFTPATH; ETA_AX] THEN
    REWRITE_TAC[path_image] THEN ASM SET_TAC[]]);;

let HOMOTOPIC_PATHS_LOOP_PARTS = prove
 (`!s p q a:real^N.
        homotopic_loops s (p ++ reversepath q) (linepath(a,a)) /\ path q
        ==> homotopic_paths s p q`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
    MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL) THEN
  REWRITE_TAC[PATHSTART_JOIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP HOMOTOPIC_PATHS_IMP_PATH) THEN
  ASM_CASES_TAC `pathfinish p:real^N = pathstart(reversepath q)` THENL
   [ASM_SIMP_TAC[PATH_JOIN; PATH_REVERSEPATH] THEN STRIP_TAC;
    ASM_MESON_TAC[PATH_JOIN_PATH_ENDS; PATH_REVERSEPATH]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PATHSTART_REVERSEPATH]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_SUBSET) THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
    PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH; UNION_SUBSET; SING_SUBSET;
    PATH_IMAGE_REVERSEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `p ++ (linepath(pathfinish p:real^N,pathfinish p))` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_RID THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `p ++ (reversepath q ++ q):real^1->real^N` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_SIMP_TAC[HOMOTOPIC_PATHS_LINV; PATHSTART_JOIN; PATHSTART_REVERSEPATH;
                 HOMOTOPIC_PATHS_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(p ++ reversepath q) ++ q:real^1->real^N` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    ASM_REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                    PATH_IMAGE_REVERSEPATH; PATH_REVERSEPATH];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `linepath(pathstart p:real^N,pathstart p) ++ q` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL] THEN
    REWRITE_TAC[PATHFINISH_JOIN; PATHFINISH_REVERSEPATH];
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH) THEN
    REWRITE_TAC[PATHFINISH_JOIN; PATHFINISH_LINEPATH;
                PATHFINISH_REVERSEPATH] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_LID THEN ASM_REWRITE_TAC[]]);;

let HOMOTOPIC_LOOPS_ADD_SYM = prove
 (`!p q:real^1->real^N.
        path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
        path q /\ path_image q SUBSET s /\ pathfinish q = pathstart q /\
        pathstart q = pathstart p
        ==> homotopic_loops s (p ++ q) (q ++ p)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  SUBGOAL_THEN `lift(&1 / &2) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  EXISTS_TAC `shiftpath (lift(&1 / &2)) (p ++ q:real^1->real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_SHIFTPATH_SELF;
    MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ] THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
               UNION_SUBSET; IN_INTERVAL_1; DROP_VEC; LIFT_DROP;
               PATH_SHIFTPATH; PATH_IMAGE_SHIFTPATH; CLOSED_SHIFTPATH] THEN
  SIMP_TAC[shiftpath; joinpaths; LIFT_DROP; DROP_ADD; DROP_SUB; DROP_VEC;
           REAL_ARITH `&0 <= t ==> (a + t <= a <=> t = &0)`;
           REAL_ARITH `t <= &1 ==> &1 / &2 + t - &1 <= &1 / &2`;
           REAL_ARITH `&1 / &2 + t <= &1 <=> t <= &1 / &2`] THEN
  X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
  ASM_CASES_TAC `drop t <= &1 / &2` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM; LIFT_DROP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_RID] THENL
     [REWRITE_TAC[GSYM LIFT_CMUL; VECTOR_MUL_RZERO] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_MESON_TAC[LIFT_NUM; pathstart; pathfinish];
      ALL_TAC];
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_SUB; DROP_ADD; DROP_VEC; DROP_CMUL;
              LIFT_DROP] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Simply connected sets defined as "all loops are homotopic (as loops)".    *)
(* ------------------------------------------------------------------------- *)

let simply_connected = new_definition
 `simply_connected(s:real^N->bool) <=>
        !p q. path p /\ pathfinish p = pathstart p /\ path_image p SUBSET s /\
              path q /\ pathfinish q = pathstart q /\ path_image q SUBSET s
              ==> homotopic_loops s p q`;;

let SIMPLY_CONNECTED_EMPTY = prove
 (`simply_connected {}`,
  REWRITE_TAC[simply_connected; SUBSET_EMPTY] THEN
  MESON_TAC[PATH_IMAGE_NONEMPTY]);;

let SIMPLY_CONNECTED_IMP_PATH_CONNECTED = prove
 (`!s:real^N->bool. simply_connected s ==> path_connected s`,
  REWRITE_TAC[simply_connected; PATH_CONNECTED_EQ_HOMOTOPIC_POINTS] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                  PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
  ASM SET_TAC[]);;

let SIMPLY_CONNECTED_IMP_CONNECTED = prove
 (`!s:real^N->bool. simply_connected s ==> connected s`,
  SIMP_TAC[SIMPLY_CONNECTED_IMP_PATH_CONNECTED;
           PATH_CONNECTED_IMP_CONNECTED]);;

let SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY = prove
 (`!s:real^N->bool.
        simply_connected s <=>
        !p a. path p /\ path_image p SUBSET s /\
              pathfinish p = pathstart p /\ a IN s
              ==> homotopic_loops s p (linepath(a,a))`,
  GEN_TAC THEN REWRITE_TAC[simply_connected] THEN EQ_TAC THEN DISCH_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET];
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `q:real^1->real^N`] THEN
    STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `linepath(pathstart p:real^N,pathstart p)` THEN
    CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]]);;

let SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_SOME = prove
 (`!s:real^N->bool.
        simply_connected s <=>
        path_connected s /\
        !p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
            ==> ?a. a IN s /\ homotopic_loops s p (linepath(a,a))`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SIMPLY_CONNECTED_IMP_PATH_CONNECTED] THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY]) THEN
    MESON_TAC[SUBSET; PATHSTART_IN_PATH_IMAGE];
    REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `a:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real^1->real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `b:real^N` THEN
    STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `linepath(b:real^N,b)` THEN
    ASM_REWRITE_TAC[HOMOTOPIC_POINTS_EQ_PATH_COMPONENT] THEN
    ASM_MESON_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT]]);;

let SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ALL = prove
 (`!s:real^N->bool.
        simply_connected s <=>
        s = {} \/
        ?a. a IN s /\
            !p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
                ==> homotopic_loops s p (linepath(a,a))`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SIMPLY_CONNECTED_EMPTY] THEN
  REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_SOME] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:real^1->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real^1->real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `b:real^N` THEN
    STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `linepath(b:real^N,b)` THEN
    ASM_REWRITE_TAC[HOMOTOPIC_POINTS_EQ_PATH_COMPONENT] THEN
    ASM_MESON_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT];
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[PATH_CONNECTED_EQ_HOMOTOPIC_POINTS] THEN
    MAP_EVERY X_GEN_TAC [`b:real^N`; `c:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `linepath(a:real^N,a)` THEN
    GEN_REWRITE_TAC RAND_CONV [HOMOTOPIC_LOOPS_SYM] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL;
                PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ASM SET_TAC[]]);;

let SIMPLY_CONNECTED_EQ_CONTRACTIBLE_PATH = prove
 (`!s:real^N->bool.
        simply_connected s <=>
        path_connected s /\
        !p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
            ==> homotopic_paths s p (linepath(pathstart p,pathstart p))`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[SIMPLY_CONNECTED_IMP_PATH_CONNECTED] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL THEN
    EXISTS_TAC `pathstart p :real^N` THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
      REWRITE_RULE[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY]) THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET];
    REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `a:real^N`] THEN
    STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `linepath(pathstart p:real^N,pathfinish p)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
      ASM_SIMP_TAC[PATHFINISH_LINEPATH];
      ASM_REWRITE_TAC[HOMOTOPIC_POINTS_EQ_PATH_COMPONENT] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[PATH_CONNECTED_IFF_PATH_COMPONENT]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]]]);;

let SIMPLY_CONNECTED_EQ_HOMOTOPIC_PATHS = prove
 (`!s:real^N->bool.
        simply_connected s <=>
        path_connected s /\
        !p q. path p /\ path_image p SUBSET s /\
              path q /\ path_image q SUBSET s /\
              pathstart q = pathstart p /\ pathfinish q = pathfinish p
              ==> homotopic_paths s p q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_PATH] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:real^1->real^N` THENL
   [X_GEN_TAC `q:real^1->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p ++ reversepath q :real^1->real^N`) THEN
    ASM_SIMP_TAC[PATH_JOIN; PATHSTART_REVERSEPATH; PATH_REVERSEPATH;
                 PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_REVERSEPATH;
                 PATH_IMAGE_JOIN; UNION_SUBSET; PATH_IMAGE_REVERSEPATH] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `p ++ linepath(pathfinish p,pathfinish p):real^1->real^N` THEN
    GEN_REWRITE_TAC LAND_CONV [HOMOTOPIC_PATHS_SYM] THEN
    ASM_SIMP_TAC[HOMOTOPIC_PATHS_RID] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `p ++ (reversepath q ++ q):real^1->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
      ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHSTART_LINEPATH] THEN
      ASM_MESON_TAC[HOMOTOPIC_PATHS_LINV; HOMOTOPIC_PATHS_SYM];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(p ++ reversepath q) ++ q:real^1->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
      ASM_SIMP_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH] THEN
      ASM_REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `linepath(pathstart q,pathstart q) ++ q:real^1->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
      ASM_SIMP_TAC[HOMOTOPIC_PATHS_RINV; HOMOTOPIC_PATHS_REFL] THEN
      ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHFINISH_REVERSEPATH];
      ASM_MESON_TAC[HOMOTOPIC_PATHS_LID]];
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_LINEPATH] THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]]);;

let SIMPLY_CONNECTED_RETRACTION_GEN = prove
 (`!s:real^M->bool t:real^N->bool h k.
        h continuous_on s /\ IMAGE h s = t /\
        k continuous_on t /\ IMAGE k t SUBSET s /\
        (!y. y IN t ==> h(k y) = y) /\
        simply_connected s
        ==> simply_connected t`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[simply_connected; path; path_image; homotopic_loops] THEN
  ONCE_REWRITE_TAC[TAUT
   `a /\ b /\ c /\ a' /\ b' /\ c' <=> a /\ c /\ b /\ a' /\ c' /\ b'`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    HOMOTOPICALLY_TRIVIAL_RETRACTION_GEN) THEN
  MAP_EVERY EXISTS_TAC [`h:real^M->real^N`; `k:real^N->real^M`] THEN
  ASM_SIMP_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
  REWRITE_TAC[pathfinish; pathstart] THEN MESON_TAC[ENDS_IN_UNIT_INTERVAL]);;

let HOMEOMORPHIC_SIMPLY_CONNECTED = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ simply_connected s
        ==> simply_connected t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
   (REWRITE_RULE[CONJ_ASSOC] SIMPLY_CONNECTED_RETRACTION_GEN)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  SIMP_TAC[homeomorphism; SUBSET_REFL]);;

let HOMEOMORPHIC_SIMPLY_CONNECTED_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t
        ==> (simply_connected s <=> simply_connected t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMEOMORPHIC_SIMPLY_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  ASM_REWRITE_TAC[]);;

let SIMPLY_CONNECTED_TRANSLATION = prove
 (`!a:real^N s. simply_connected (IMAGE (\x. a + x) s) <=> simply_connected s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_SIMPLY_CONNECTED_EQ THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION]);;

add_translation_invariants [SIMPLY_CONNECTED_TRANSLATION];;

let SIMPLY_CONNECTED_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (simply_connected (IMAGE f s) <=> simply_connected s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_SIMPLY_CONNECTED_EQ THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ;
                HOMEOMORPHIC_REFL]);;

add_linear_invariants [SIMPLY_CONNECTED_INJECTIVE_LINEAR_IMAGE];;

let SIMPLY_CONNECTED_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        simply_connected s /\ simply_connected t
        ==> simply_connected(s PCROSS t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
  REWRITE_TAC[path; path_image; pathstart; pathfinish; FORALL_PASTECART] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`p:real^1->real^(M,N)finite_sum`; `a:real^M`; `b:real^N`] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; FORALL_IN_IMAGE; SUBSET] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2
   (MP_TAC o SPECL [`fstcart o (p:real^1->real^(M,N)finite_sum)`; `a:real^M`])
   (MP_TAC o SPECL [`sndcart o (p:real^1->real^(M,N)finite_sum)`;
                    `b:real^N`])) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; LINEAR_FSTCART; LINEAR_SNDCART;
               LINEAR_CONTINUOUS_ON; homotopic_loops; homotopic_with;
               pathfinish; pathstart; IMAGE_o; o_THM] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[PCROSS; IN_ELIM_THM]) THEN
    ASM_MESON_TAC[SNDCART_PASTECART];
    DISCH_THEN(X_CHOOSE_THEN
      `k:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC)] THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[PCROSS; IN_ELIM_THM]) THEN
    ASM_MESON_TAC[FSTCART_PASTECART];
    DISCH_THEN(X_CHOOSE_THEN
      `h:real^(1,1)finite_sum->real^M` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC
   `(\z. pastecart (h z) (k z))
    :real^(1,1)finite_sum->real^(M,N)finite_sum` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_PASTECART; ETA_AX] THEN
  REWRITE_TAC[LINEPATH_REFL; PASTECART_FST_SND] THEN
  ASM_SIMP_TAC[PASTECART_IN_PCROSS]);;

let SIMPLY_CONNECTED_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        simply_connected(s PCROSS t) <=>
        s = {} \/ t = {} \/ simply_connected s /\ simply_connected t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; SIMPLY_CONNECTED_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; SIMPLY_CONNECTED_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[SIMPLY_CONNECTED_PCROSS] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
    MAP_EVERY X_GEN_TAC [`p:real^1->real^M`; `a:real^M`] THEN
    REWRITE_TAC[path; path_image; pathstart; pathfinish; SUBSET;
                FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`(\t. pastecart (p t) (b)):real^1->real^(M,N)finite_sum`;
      `pastecart (a:real^M) (b:real^N)`]) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    ASM_SIMP_TAC[path; path_image; pathstart; pathfinish; SUBSET;
                 FORALL_IN_IMAGE; PASTECART_IN_PCROSS; PASTECART_INJ;
                 CONTINUOUS_ON_PASTECART; ETA_AX; CONTINUOUS_ON_CONST] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL
     [`(\t. pastecart (p t) b):real^1->real^(M,N)finite_sum`;
      `linepath (pastecart (a:real^M) (b:real^N),pastecart a b)`;
      `fstcart:real^(M,N)finite_sum->real^M`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`; `s:real^M->bool`]
        HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE) THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    SIMP_TAC[o_DEF; LINEPATH_REFL; FSTCART_PASTECART; ETA_AX;
             SUBSET; FORALL_IN_PCROSS; FORALL_IN_IMAGE];
    REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `b:real^N`] THEN
    REWRITE_TAC[path; path_image; pathstart; pathfinish; SUBSET;
                FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN UNDISCH_TAC `~(s:real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^M` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`(\t. pastecart a (p t)):real^1->real^(M,N)finite_sum`;
      `pastecart (a:real^M) (b:real^N)`]) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    ASM_SIMP_TAC[path; path_image; pathstart; pathfinish; SUBSET;
                 FORALL_IN_IMAGE; PASTECART_IN_PCROSS; PASTECART_INJ;
                 CONTINUOUS_ON_PASTECART; ETA_AX; CONTINUOUS_ON_CONST] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL
     [`(\t. pastecart a (p t)):real^1->real^(M,N)finite_sum`;
      `linepath (pastecart (a:real^M) (b:real^N),pastecart a b)`;
      `sndcart:real^(M,N)finite_sum->real^N`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`; `t:real^N->bool`]
        HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE) THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    SIMP_TAC[o_DEF; LINEPATH_REFL; SNDCART_PASTECART; ETA_AX;
             SUBSET; FORALL_IN_PCROSS; FORALL_IN_IMAGE]]);;

(* ------------------------------------------------------------------------- *)
(* A mapping out of a sphere is nullhomotopic iff it extends to the ball.    *)
(* This even works out in the degenerate cases when the radius is <= 0, and  *)
(* we also don't need to explicitly assume continuity since it's already     *)
(* implicit in both sides of the equivalence.                                *)
(* ------------------------------------------------------------------------- *)

let NULLHOMOTOPIC_FROM_SPHERE_EXTENSION = prove
 (`!f:real^M->real^N s a r.
        (?c. homotopic_with (\x. T) (sphere(a,r),s) f (\x. c)) <=>
        (?g. g continuous_on cball(a,r) /\ IMAGE g (cball(a,r)) SUBSET s /\
             !x. x IN sphere(a,r) ==> g x = f x)`,
  let lemma = prove
   (`!f:real^M->real^N g a r.
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !x. ~(x = a) /\ norm(x - a) < d ==> norm(g x - f a) < e) /\
        g continuous_on (cball(a,r) DELETE a) /\
        (!x. x IN cball(a,r) /\ ~(x = a) ==> f x = g x)
        ==> f continuous_on cball(a,r)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_CBALL; dist] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:real^M = a` THENL
     [ASM_REWRITE_TAC[continuous_within; IN_CBALL; dist] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_CBALL; dist]) THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:real^M` THEN ASM_CASES_TAC `y:real^M = a` THEN
      ASM_MESON_TAC[VECTOR_SUB_REFL; NORM_0];
      MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
      EXISTS_TAC `g:real^M->real^N` THEN EXISTS_TAC `norm(x - a:real^M)` THEN
      ASM_SIMP_TAC[NORM_POS_LT; VECTOR_SUB_EQ; IN_CBALL; dist] THEN
      CONJ_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[IN_CBALL; dist]);
        UNDISCH_TAC
         `(g:real^M->real^N) continuous_on (cball(a,r) DELETE a)` THEN
        REWRITE_TAC[continuous_on; continuous_within] THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
        ASM_REWRITE_TAC[IN_DELETE; IN_CBALL; dist] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `min d (norm(x - a:real^M))` THEN
        ASM_REWRITE_TAC[REAL_LT_MIN; NORM_POS_LT; VECTOR_SUB_EQ]] THEN
       ASM_MESON_TAC[NORM_SUB; NORM_ARITH
        `norm(y - x:real^N) < norm(x - a) ==> ~(y = a)`]]) in
  REWRITE_TAC[sphere; ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
  REPEAT GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `r < &0 \/ r = &0 \/ &0 < r`)
  THENL
   [ASM_SIMP_TAC[NORM_ARITH `r < &0 ==> ~(norm x = r)`] THEN
    FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [GSYM CBALL_EQ_EMPTY]) THEN
    ASM_SIMP_TAC[HOMOTOPIC_WITH; IMAGE_CLAUSES; EMPTY_GSPEC; NOT_IN_EMPTY;
       PCROSS; SET_RULE `{f t x |x,t| F} = {}`; EMPTY_SUBSET] THEN
    REWRITE_TAC[CONTINUOUS_ON_EMPTY];
    ASM_SIMP_TAC[NORM_EQ_0; VECTOR_SUB_EQ; CBALL_SING] THEN
    SIMP_TAC[HOMOTOPIC_WITH; PCROSS; FORALL_IN_GSPEC; FORALL_UNWIND_THM2] THEN
    ASM_CASES_TAC `(f:real^M->real^N) a IN s` THENL
     [MATCH_MP_TAC(TAUT `p /\ q ==> (p <=> q)`) THEN CONJ_TAC THENL
       [EXISTS_TAC `(f:real^M->real^N) a` THEN
        EXISTS_TAC `\y:real^(1,M)finite_sum. (f:real^M->real^N) a` THEN
        ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; SUBSET; FORALL_IN_IMAGE];
        EXISTS_TAC `f:real^M->real^N` THEN REWRITE_TAC[CONTINUOUS_ON_SING] THEN
        ASM SET_TAC[]];
      MATCH_MP_TAC(TAUT `~q /\ ~p ==> (p <=> q)`) THEN CONJ_TAC THENL
       [ASM SET_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `~((f:real^M->real^N) a IN s)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE h t SUBSET s ==> (?y. y IN t /\ z = h y) ==> z IN s`)) THEN
      REWRITE_TAC[EXISTS_IN_GSPEC] THEN
      EXISTS_TAC `vec 0:real^1` THEN ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL] THEN
      ASM_REWRITE_TAC[EXISTS_IN_GSPEC; UNWIND_THM2]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT
   `!p. (q ==> p) /\ (r ==> p) /\ (p ==> (q <=> r)) ==> (q <=> r)`) THEN
  EXISTS_TAC
   `(f:real^M->real^N) continuous_on {x | norm(x - a) = r} /\
    IMAGE f {x | norm(x - a) = r} SUBSET s` THEN
  REPEAT CONJ_TAC THENL
   [STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `g:real^M->real^N` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `cball(a:real^M,r)`;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `IMAGE g t SUBSET s
         ==> u SUBSET t /\ (!x. x IN u ==> f x = g x)
             ==> IMAGE f u SUBSET s`)) THEN
      ASM_SIMP_TAC[]] THEN
    ASM_SIMP_TAC[SUBSET; IN_CBALL; dist; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LE_REFL; NORM_SUB];
    STRIP_TAC] THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN EQ_TAC THENL
   [REWRITE_TAC[homotopic_with; PCROSS; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:real^N`; `h:real^(1,M)finite_sum->real^N`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `\x. (h:real^(1,M)finite_sum->real^N)
                    (pastecart (lift(inv(r) * norm(x - a)))
                               (a + (if x = a then r % basis 1
                                     else r / norm(x - a) % (x - a))))` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_MUL_LINV; REAL_DIV_REFL; REAL_LT_IMP_NZ;
                 LIFT_NUM; VECTOR_ARITH `a + &1 % (x - a):real^N = x`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC lemma THEN
      EXISTS_TAC `\x. (h:real^(1,M)finite_sum->real^N)
                    (pastecart (lift(inv(r) * norm(x - a)))
                               (a + r / norm(x - a) % (x - a)))` THEN
      SIMP_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_MUL_RZERO; LIFT_NUM] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          COMPACT_UNIFORMLY_CONTINUOUS)) THEN
        SIMP_TAC[REWRITE_RULE[PCROSS] COMPACT_PCROSS;
            REWRITE_RULE[REWRITE_RULE[ONCE_REWRITE_RULE[DIST_SYM] dist] sphere]
                 COMPACT_SPHERE; COMPACT_INTERVAL] THEN
        REWRITE_TAC[uniformly_continuous_on] THEN
        DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
        DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `min r (d * r):real` THEN
        ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_MIN] THEN
        X_GEN_TAC `x:real^M` THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^1`) THEN
        REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; RIGHT_IMP_FORALL_THM] THEN
        ASM_REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
         `(!x t y. P x t y) ==> (!t x. P x t x)`)) THEN
        REWRITE_TAC[dist] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
        ASM_SIMP_TAC[REAL_MUL_LID; REAL_MUL_LZERO; NORM_POS_LE] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; CONJ_ASSOC] THEN
        REWRITE_TAC[VECTOR_ADD_SUB; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
        ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
        REWRITE_TAC[PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART] THEN
        REWRITE_TAC[NORM_0; VECTOR_SUB_RZERO] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_ADD_RID] THEN
        REWRITE_TAC[POW_2_SQRT_ABS; REAL_ABS_NORM; NORM_LIFT] THEN
        ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LT_LDIV_EQ; REAL_ABS_NORM;
                     REAL_ARITH `&0 < r ==> abs r = r`];
        GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
          SIMP_TAC[CONTINUOUS_ON_CMUL; LIFT_CMUL; CONTINUOUS_ON_SUB;
                   CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST;
                   CONTINUOUS_ON_LIFT_NORM_COMPOSE] THEN
          MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
          REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
          MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
          SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST;
                   o_DEF; real_div; LIFT_CMUL] THEN
          MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
          REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
          GEN_TAC THEN REWRITE_TAC[IN_DELETE] THEN DISCH_TAC THEN
          MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
          MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_INV) THEN
          ASM_SIMP_TAC[NETLIMIT_AT; NORM_EQ_0; VECTOR_SUB_EQ] THEN
          MATCH_MP_TAC CONTINUOUS_LIFT_NORM_COMPOSE THEN
          SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_AT_ID; CONTINUOUS_CONST];
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC; SUBSET] THEN
          REWRITE_TAC[IN_ELIM_PASTECART_THM; IN_DELETE; IN_ELIM_THM] THEN
          SIMP_TAC[IN_CBALL; NORM_ARITH `dist(a:real^M,a + x) = norm x`] THEN
          REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
          REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
          REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
          ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
          ASM_SIMP_TAC[REAL_MUL_LID; REAL_MUL_LZERO; NORM_POS_LE] THEN
          SIMP_TAC[VECTOR_ADD_SUB; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM;
                   REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
          ASM_REAL_ARITH_TAC]];
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
      REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE g s SUBSET u ==> t SUBSET s ==> IMAGE g t SUBSET u`)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IN_ELIM_PASTECART_THM; IN_CBALL; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^M` THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] dist] THEN REPEAT STRIP_TAC THENL
       [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
        ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO; NORM_POS_LE];
        REWRITE_TAC[VECTOR_ADD_SUB] THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL;
                     REAL_ABS_DIV; REAL_ABS_NORM;
                     REAL_MUL_RID; REAL_ARITH `&0 < r ==> abs r = r`] THEN
        ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ]];
      GEN_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[VECTOR_ARITH `a + &1 % (x - a):real^N = x`]];
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(g:real^M->real^N) a` THEN
    ASM_SIMP_TAC[HOMOTOPIC_WITH; PCROSS] THEN
    EXISTS_TAC `\y:real^(1,M)finite_sum.
                   (g:real^M->real^N)
                   (a + drop(fstcart y) % (sndcart y - a))` THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID] THEN
    ASM_SIMP_TAC[VECTOR_SUB_ADD2] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN SIMP_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        SIMP_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
                 LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; LINEAR_FSTCART; ETA_AX];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET))];
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
      REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE g s SUBSET u ==> t SUBSET s ==> IMAGE g t SUBSET u`))] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_CBALL; NORM_ARITH `dist(a:real^M,a + x) = norm x`] THEN
    ASM_SIMP_TAC[NORM_MUL; IN_INTERVAL_1; DROP_VEC; REAL_LE_RMUL_EQ;
                 REAL_ARITH `x * r <= r <=> x * r <= &1 * r`] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy equivalence.                                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("homotopy_equivalent",(12,"right"));;

let homotopy_equivalent = new_definition
 `(s:real^M->bool) homotopy_equivalent (t:real^N->bool) <=>
        ?f g. f continuous_on s /\ IMAGE f s SUBSET t /\
              g continuous_on t /\ IMAGE g t SUBSET s /\
              homotopic_with (\x. T) (s,s) (g o f) I /\
              homotopic_with (\x. T) (t,t) (f o g) I`;;

let HOMOTOPY_EQUIVALENT = prove
 (`!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t <=>
        ?f g h. f continuous_on s /\ IMAGE f s SUBSET t /\
                g continuous_on t /\ IMAGE g t SUBSET s /\
                h continuous_on t /\ IMAGE h t SUBSET s /\
                homotopic_with (\x. T) (s,s) (g o f) I /\
                homotopic_with (\x. T) (t,t) (f o h) I`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopy_equivalent] THEN
  MATCH_MP_TAC(MESON[] `(!x. P x <=> Q x) ==> ((?x. P x) <=> (?x. Q x))`) THEN
  X_GEN_TAC `f:real^M->real^N` THEN
  EQ_TAC THENL [MESON_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `(g:real^N->real^M) o f o (h:real^N->real^M)` THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
    REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
    ASM SET_TAC[];
    TRANS_TAC HOMOTOPIC_WITH_TRANS
      `((g:real^N->real^M) o I) o (f:real^M->real^N)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[I_O_ID]] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
    TRANS_TAC HOMOTOPIC_WITH_TRANS
      `(f:real^M->real^N) o I o (h:real^N->real^M)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[I_O_ID]] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[o_ASSOC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[]]);;

let HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> s homotopy_equivalent t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homeomorphic; homotopy_equivalent; homeomorphism] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  CONJ_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQUAL THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; IMAGE_o; o_THM; I_THM; SUBSET_REFL]);;

let HOMOTOPY_EQUIVALENT_REFL = prove
 (`!s:real^N->bool. s homotopy_equivalent s`,
  SIMP_TAC[HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT; HOMEOMORPHIC_REFL]);;

let HOMOTOPY_EQUIVALENT_SYM = prove
 (`!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t <=> t homotopy_equivalent s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopy_equivalent] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN CONV_TAC TAUT);;

let HOMOTOPY_EQUIVALENT_TRANS = prove
 (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t /\ t homotopy_equivalent u
        ==> s homotopy_equivalent u`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[homotopy_equivalent; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  SIMP_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`f1:real^M->real^N`; `g1:real^N->real^M`;
    `f2:real^N->real^P`; `g2:real^P->real^N`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(f2:real^N->real^P) o (f1:real^M->real^N)`;
    `(g1:real^N->real^M) o (g2:real^P->real^N)`] THEN
  REWRITE_TAC[IMAGE_o] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL
    [ASM_MESON_TAC[CONTINUOUS_ON_COMPOSE; CONTINUOUS_ON_SUBSET];ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  CONJ_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THENL
   [EXISTS_TAC `(g1:real^N->real^M) o I o (f1:real^M->real^N)`;
    EXISTS_TAC `(f2:real^N->real^P) o I o (g2:real^P->real^N)`] THEN
  (CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[I_O_ID]]) THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_ASSOC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_SELF = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (IMAGE f s) homotopy_equivalent s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
  MATCH_MP_TAC HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF THEN
  ASM_REWRITE_TAC[]);;

let HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_LEFT_EQ = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((IMAGE f s) homotopy_equivalent t <=> s homotopy_equivalent t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o SPEC `s:real^M->bool` o
    MATCH_MP HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_SELF) THEN
  EQ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMOTOPY_EQUIVALENT_SYM]);
    POP_ASSUM MP_TAC] THEN
  REWRITE_TAC[IMP_IMP; HOMOTOPY_EQUIVALENT_TRANS]);;

let HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (s homotopy_equivalent (IMAGE f t) <=> s homotopy_equivalent t)`,
  ONCE_REWRITE_TAC[HOMOTOPY_EQUIVALENT_SYM] THEN
  REWRITE_TAC[HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_LEFT_EQ]);;

add_linear_invariants
  [HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_LEFT_EQ;
   HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ];;

let HOMOTOPY_EQUIVALENT_TRANSLATION_SELF = prove
 (`!a:real^N s. (IMAGE (\x. a + x) s) homotopy_equivalent s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

let HOMOTOPY_EQUIVALENT_TRANSLATION_LEFT_EQ = prove
 (`!a:real^N s t.
      (IMAGE (\x. a + x) s) homotopy_equivalent t <=> s homotopy_equivalent t`,
  MESON_TAC[HOMOTOPY_EQUIVALENT_TRANSLATION_SELF;
            HOMOTOPY_EQUIVALENT_SYM; HOMOTOPY_EQUIVALENT_TRANS]);;

let HOMOTOPY_EQUIVALENT_TRANSLATION_RIGHT_EQ = prove
 (`!a:real^N s t.
      s homotopy_equivalent (IMAGE (\x. a + x) t) <=> s homotopy_equivalent t`,
  ONCE_REWRITE_TAC[HOMOTOPY_EQUIVALENT_SYM] THEN
  REWRITE_TAC[HOMOTOPY_EQUIVALENT_TRANSLATION_LEFT_EQ]);;

add_translation_invariants
  [HOMOTOPY_EQUIVALENT_TRANSLATION_LEFT_EQ;
   HOMOTOPY_EQUIVALENT_TRANSLATION_RIGHT_EQ];;

let HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY = prove
  (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t
        ==> ((!f g. f continuous_on u /\ IMAGE f u SUBSET s /\
                    g continuous_on u /\ IMAGE g u SUBSET s
                    ==> homotopic_with (\x. T) (u,s) f g) <=>
             (!f g. f continuous_on u /\ IMAGE f u SUBSET t /\
                    g continuous_on u /\ IMAGE g u SUBSET t
                    ==> homotopic_with (\x. T) (u,t) f g))`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool u:real^P->bool.
          s homotopy_equivalent t /\
          (!f g. f continuous_on u /\ IMAGE f u SUBSET s /\
                 g continuous_on u /\ IMAGE g u SUBSET s
                 ==> homotopic_with (\x. T) (u,s) f g)
          ==> (!f g. f continuous_on u /\ IMAGE f u SUBSET t /\
                     g continuous_on u /\ IMAGE g u SUBSET t
                     ==> homotopic_with (\x. T) (u,t) f g)`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopy_equivalent]) THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N`
     (X_CHOOSE_THEN `k:real^N->real^M` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `homotopic_with (\x. T) (u,t)
          ((h:real^M->real^N) o (k:real^N->real^M) o (f:real^P->real^N))
          (h o k o g)`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IMAGE_o] THEN
      REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE) THEN
      ASM_REWRITE_TAC[] THEN
      TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC(MESON[HOMOTOPIC_WITH_TRANS; HOMOTOPIC_WITH_SYM]
       `homotopic_with P (u,t) f f' /\ homotopic_with P (u,t) g g'
        ==> homotopic_with P (u,t) f g ==> homotopic_with P (u,t) f' g'`) THEN
      CONJ_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT1(SPEC_ALL I_O_ID))] THEN
      REWRITE_TAC[o_ASSOC] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] lemma) THEN
  ASM_MESON_TAC[HOMOTOPY_EQUIVALENT_SYM]);;

let HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY = prove
 (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t
        ==> ((!f g. f continuous_on s /\ IMAGE f s SUBSET u /\
                    g continuous_on s /\ IMAGE g s SUBSET u
                    ==> homotopic_with (\x. T) (s,u) f g) <=>
             (!f g. f continuous_on t /\ IMAGE f t SUBSET u /\
                    g continuous_on t /\ IMAGE g t SUBSET u
                    ==> homotopic_with (\x. T) (t,u) f g))`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool u:real^P->bool.
          s homotopy_equivalent t /\
          (!f g. f continuous_on s /\ IMAGE f s SUBSET u /\
                 g continuous_on s /\ IMAGE g s SUBSET u
                 ==> homotopic_with (\x. T) (s,u) f g)
           ==> (!f g. f continuous_on t /\ IMAGE f t SUBSET u /\
                      g continuous_on t /\ IMAGE g t SUBSET u
                      ==> homotopic_with (\x. T) (t,u) f g)`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopy_equivalent]) THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N`
     (X_CHOOSE_THEN `k:real^N->real^M` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `homotopic_with (\x. T) (t,u)
          (((f:real^N->real^P) o h) o (k:real^N->real^M)) ((g o h) o k)`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IMAGE_o] THEN
      REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE) THEN
      ASM_REWRITE_TAC[] THEN
      TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC(MESON[HOMOTOPIC_WITH_TRANS; HOMOTOPIC_WITH_SYM]
       `homotopic_with P (u,t) f f' /\ homotopic_with P (u,t) g g'
        ==> homotopic_with P (u,t) f g ==> homotopic_with P (u,t) f' g'`) THEN
      CONJ_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT2(SPEC_ALL I_O_ID))] THEN
      REWRITE_TAC[GSYM o_ASSOC] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] lemma) THEN
  ASM_MESON_TAC[HOMOTOPY_EQUIVALENT_SYM]);;

let HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY_NULL = prove
  (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t
        ==> ((!f. f continuous_on u /\ IMAGE f u SUBSET s
                  ==> ?c. homotopic_with (\x. T) (u,s) f (\x. c)) <=>
             (!f. f continuous_on u /\ IMAGE f u SUBSET t
                  ==> ?c. homotopic_with (\x. T) (u,t) f (\x. c)))`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool u:real^P->bool.
          s homotopy_equivalent t /\
          (!f. f continuous_on u /\ IMAGE f u SUBSET s
               ==> ?c. homotopic_with (\x. T) (u,s) f (\x. c))
          ==> (!f. f continuous_on u /\ IMAGE f u SUBSET t
                   ==> ?c. homotopic_with (\x. T) (u,t) f (\x. c))`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopy_equivalent]) THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N`
     (X_CHOOSE_THEN `k:real^N->real^M` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(k:real^N->real^M) o (f:real^P->real^N)`) THEN
    REWRITE_TAC[IMAGE_o] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE; ASM SET_TAC[]] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      DISCH_THEN(X_CHOOSE_TAC `c:real^M`) THEN
      EXISTS_TAC `(h:real^M->real^N) c`] THEN
    SUBGOAL_THEN
     `homotopic_with (\x. T) (u,t)
          ((h:real^M->real^N) o (k:real^N->real^M) o (f:real^P->real^N))
          (h o (\x. c))`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [o_DEF] THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_TRANS) THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT1(SPEC_ALL I_O_ID))] THEN
      REWRITE_TAC[o_ASSOC] THEN ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
      EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] lemma) THEN
  ASM_MESON_TAC[HOMOTOPY_EQUIVALENT_SYM]);;

let HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL = prove
 (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t
        ==> ((!f. f continuous_on s /\ IMAGE f s SUBSET u
                  ==> ?c. homotopic_with (\x. T) (s,u) f (\x. c)) <=>
             (!f. f continuous_on t /\ IMAGE f t SUBSET u
                  ==> ?c. homotopic_with (\x. T) (t,u) f (\x. c)))`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool u:real^P->bool.
          s homotopy_equivalent t /\
          (!f. f continuous_on s /\ IMAGE f s SUBSET u
               ==> ?c. homotopic_with (\x. T) (s,u) f (\x. c))
          ==> (!f. f continuous_on t /\ IMAGE f t SUBSET u
                   ==> ?c. homotopic_with (\x. T) (t,u) f (\x. c))`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopy_equivalent]) THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N`
     (X_CHOOSE_THEN `k:real^N->real^M` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^N->real^P) o (h:real^M->real^N)`) THEN
    REWRITE_TAC[IMAGE_o] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE; ASM SET_TAC[]] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^P` THEN DISCH_TAC] THEN
    SUBGOAL_THEN
     `homotopic_with (\x. T) (t,u)
          (((f:real^N->real^P) o h) o (k:real^N->real^M)) ((\x. c) o k)`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [o_DEF] THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_TRANS) THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT2(SPEC_ALL I_O_ID))] THEN
      REWRITE_TAC[GSYM o_ASSOC] THEN ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] lemma) THEN
  ASM_MESON_TAC[HOMOTOPY_EQUIVALENT_SYM]);;

let HOMOTOPY_INVARIANT_CONNECTEDNESS = prove
 (`!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        homotopic_with (\x. T) (t,t) (f o g) I /\
        connected s
        ==> connected t`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  REWRITE_TAC[o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^N`
        STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
  `t = IMAGE (h:real^(1,N)finite_sum->real^N) (interval[vec 0,vec 1] PCROSS t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[EXISTS_IN_PCROSS] THEN
    ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT; IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`t1:real^1`; `x1:real^N`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t2:real^1`; `x2:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[CONNECTED_COMPONENT_TRANS; CONNECTED_COMPONENT_SYM]
    `!a b. (connected_component t a a' /\ connected_component t b b') /\
           connected_component t a b
           ==> connected_component t a' b'`) THEN
  MAP_EVERY EXISTS_TAC
   [`(h:real^(1,N)finite_sum->real^N) (pastecart (vec 0) x1)`;
    `(h:real^(1,N)finite_sum->real^N) (pastecart (vec 0) x2)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[connected_component] THEN CONJ_TAC THENL
     [EXISTS_TAC
       `IMAGE ((h:real^(1,N)finite_sum->real^N) o (\s. pastecart s x1))
              (interval[vec 0,vec 1])`;
      EXISTS_TAC
       `IMAGE ((h:real^(1,N)finite_sum->real^N) o (\s. pastecart s x2))
              (interval[vec 0,vec 1])`] THEN
    (CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[CONNECTED_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS];
      REWRITE_TAC[IMAGE_o] THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS];
        CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE] THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL]]);
    ASM_REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N) s` THEN
    ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN
    REWRITE_TAC[EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
    X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`vec 1:real^1`; `(f:real^M->real^N) y`] THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN ASM SET_TAC[]]);;

let HOMOTOPY_INVARIANT_PATH_CONNECTEDNESS = prove
 (`!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        homotopic_with (\x. T) (t,t) (f o g) I /\
        path_connected s
        ==> path_connected t`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  REWRITE_TAC[o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^N`
        STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
  `t = IMAGE (h:real^(1,N)finite_sum->real^N) (interval[vec 0,vec 1] PCROSS t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[EXISTS_IN_PCROSS] THEN
    ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT; IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`t1:real^1`; `x1:real^N`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t2:real^1`; `x2:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[PATH_COMPONENT_TRANS; PATH_COMPONENT_SYM]
    `!a b. (path_component t a a' /\ path_component t b b') /\
           path_component t a b
           ==> path_component t a' b'`) THEN
  MAP_EVERY EXISTS_TAC
   [`(h:real^(1,N)finite_sum->real^N) (pastecart (vec 0) x1)`;
    `(h:real^(1,N)finite_sum->real^N) (pastecart (vec 0) x2)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PATH_COMPONENT] THEN CONJ_TAC THENL
     [EXISTS_TAC
       `IMAGE ((h:real^(1,N)finite_sum->real^N) o (\s. pastecart s x1))
              (interval[vec 0,vec 1])`;
      EXISTS_TAC
       `IMAGE ((h:real^(1,N)finite_sum->real^N) o (\s. pastecart s x2))
              (interval[vec 0,vec 1])`] THEN
    (CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[PATH_CONNECTED_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS];
      REWRITE_TAC[IMAGE_o] THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS];
        CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE] THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL]]);
    ASM_REWRITE_TAC[PATH_COMPONENT] THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N) s` THEN
    ASM_SIMP_TAC[PATH_CONNECTED_CONTINUOUS_IMAGE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN
    REWRITE_TAC[EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
    X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`vec 1:real^1`; `(f:real^M->real^N) y`] THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN ASM SET_TAC[]]);;

let HOMOTOPY_EQUIVALENT_CONNECTEDNESS = prove
 (`!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t ==> (connected s <=> connected t)`,
  REWRITE_TAC[homotopy_equivalent] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
   (REWRITE_RULE[CONJ_ASSOC] HOMOTOPY_INVARIANT_CONNECTEDNESS)) THEN
  ASM_MESON_TAC[]);;

let HOMOTOPY_EQUIVALENT_PATH_CONNECTEDNESS = prove
 (`!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t ==> (path_connected s <=> path_connected t)`,
  REWRITE_TAC[homotopy_equivalent] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
   (REWRITE_RULE[CONJ_ASSOC] HOMOTOPY_INVARIANT_PATH_CONNECTEDNESS)) THEN
  ASM_MESON_TAC[]);;
