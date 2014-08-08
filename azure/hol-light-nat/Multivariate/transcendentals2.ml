open Hol_core
open Floor
open Products
open Vectors
open Determinants
open Topology
open Convex
open Paths
open Dimension
open Derivatives
open Complexes
open Canal
include Transcendentals1

(* ------------------------------------------------------------------------- *)
(* Homotopy staying within the set of orthogonal transformations             *)
(* ------------------------------------------------------------------------- *)

let NULLHOMOTOPIC_ORTHOGONAL_TRANSFORMATION = prove
 (`!f:real^N->real^N.
       orthogonal_transformation f /\ det(matrix f) = &1
       ==> homotopic_with orthogonal_transformation ((:real^N),(:real^N)) f I`,
  let lemma0 = prove
   (`!a x:real^N.
          2 <= dimindex(:N) /\ a IN span {basis 1,basis 2}
          ==> reflect_along (vector[a$1; a$2]:real^2) (lambda i. x$i) =
              (lambda i. reflect_along a x$i)`,
    REPEAT STRIP_TAC THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; reflect_along; VECTOR_SUB_COMPONENT;
             VECTOR_MUL_COMPONENT; DIMINDEX_2; FORALL_2; VECTOR_2; ARITH] THEN
    CONJ_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN BINOP_TAC THEN REWRITE_TAC[dot] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_EQ_SUPERSET THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; FORALL_2; DIMINDEX_2; LAMBDA_BETA;
                 ARITH; VECTOR_2; SUBSET_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE
     `(1 <= i /\ i <= n) /\ ~(1 <= i /\ i <= 2) <=>
      1 <= i /\ 3 <= i /\ i <= n`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [SPAN_2]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]) THEN
    ASM_ARITH_TAC) in
  let lemma1 = prove
   (`!a b:real^2 r.
          ~(a = vec 0) /\ ~(b = vec 0)
          ==> homotopic_with orthogonal_transformation ((:real^2),(:real^2))
                             (reflect_along a o reflect_along b) I`,
    REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `reflect_along (a:real^2) o reflect_along b`
          ROTATION_ROTATE2D) THEN
    ANTS_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o
        MATCH_MP ROTOINVERSION_MATRIX_REFLECT_ALONG)) THEN
      REWRITE_TAC[rotoinversion_matrix] THEN
      SIMP_TAC[ORTHOGONAL_MATRIX_MATRIX;
               ORTHGOONAL_TRANSFORMATION_REFLECT_ALONG;
               ORTHOGONAL_TRANSFORMATION_COMPOSE; MATRIX_COMPOSE;
               LINEAR_REFLECT_ALONG; DET_MUL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
      ASM_REWRITE_TAC[homotopic_with] THEN
      EXISTS_TAC `\z. rotate2d (drop(fstcart z) * t) (sndcart z)` THEN
      SIMP_TAC[ORTHOGONAL_TRANSFORMATION_ROTATE2D; SNDCART_PASTECART;
               ETA_AX; FSTCART_PASTECART; DROP_VEC; I_THM; NORM_ROTATE2D;
               REAL_MUL_LZERO; REAL_MUL_LID; SUBSET; FORALL_IN_IMAGE; IN_UNIV;
               FORALL_IN_PCROSS; IN_SPHERE_0; ROTATE2D_ZERO] THEN
      REWRITE_TAC[ROTATE2D_COMPLEX] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[CONTINUOUS_ON_CEXP; CX_MUL] THEN
      ONCE_REWRITE_TAC[COMPLEX_RING `ii * x * t = (ii * t) * x`] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART]]) in
  let lemma2 = prove
   (`!a b:real^N r.
          2 <= dimindex(:N) /\
          ~(a = vec 0) /\ ~(b = vec 0) /\
          {a,b} SUBSET span {basis 1,basis 2}
          ==> homotopic_with orthogonal_transformation ((:real^N),(:real^N))
                             (reflect_along a o reflect_along b) I`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `homotopic_with orthogonal_transformation
        ((:real^N),(:real^N))
        ((\z. (lambda i. if i <= 2 then (fstcart z)$i
                         else (sndcart z)$i):real^N) o
         (\z. pastecart
               (((reflect_along (vector [(a:real^N)$1; a$2]) o
                 reflect_along (vector [(b:real^N)$1; b$2]))
                  :real^2->real^2)(fstcart z))
               (sndcart z)) o
         (\z:real^N. pastecart ((lambda i. z$i) :real^2) z))
        ((\z. (lambda i. if i <= 2 then (fstcart z)$i
                         else (sndcart z)$i):real^N) o
         I o
         (\z:real^N. pastecart ((lambda i. z$i) :real^2) z))`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC `(:real^2) PCROSS (:real^N)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        ONCE_REWRITE_TAC[LINEAR_COMPONENTWISE] THEN
        SIMP_TAC[LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN
        STRIP_TAC THEN ASM_CASES_TAC `i <= 2` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL;
                            SNDCART_ADD; SNDCART_CMUL] THEN
        REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        REWRITE_TAC[LIFT_ADD; LIFT_CMUL]] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
      EXISTS_TAC `(:real^2) PCROSS (:real^N)` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; PASTECART_IN_PCROSS] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        MATCH_MP_TAC LINEAR_PASTECART THEN REWRITE_TAC[LINEAR_ID] THEN
        SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT]] THEN
      SUBGOAL_THEN
       `I = \z:real^(2,N)finite_sum. pastecart (fstcart z) (sndcart z)`
      SUBST1_TAC THENL
       [REWRITE_TAC[PASTECART_FST_SND; I_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_PCROSS THEN
      EXISTS_TAC `orthogonal_transformation:(real^2->real^2)->bool` THEN
      EXISTS_TAC `\f:real^N->real^N. f = I` THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM I_DEF; ETA_AX] THEN MATCH_MP_TAC lemma1 THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INSERT_SUBSET]) THEN
        REWRITE_TAC[SING_SUBSET; SPAN_2; IN_ELIM_THM; IN_UNIV] THEN
        DISCH_THEN(REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) THEN
        POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
        REWRITE_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                    DIMINDEX_2; FORALL_2; VECTOR_2] THEN
        SIMP_TAC[BASIS_COMPONENT; ARITH; DIMINDEX_2; VEC_COMPONENT;
                 DIMINDEX_GE_1; LE_REFL] THEN
        MATCH_MP_TAC(TAUT
         `(r ==> q) /\ (s ==> p) ==> a /\ ~p /\ ~q ==> ~s /\ ~r`) THEN
        SIMP_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_MUL_RID;
                 REAL_ADD_LID; REAL_ADD_RID];
        REWRITE_TAC[HOMOTOPIC_WITH_REFL; SUBSET_UNIV; I_DEF] THEN
        REWRITE_TAC[CONTINUOUS_ON_ID];
        SIMP_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART;
                 LAMBDA_BETA; DIMINDEX_2; ARITH; I_THM] THEN
        REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; NORM_EQ] THEN
        X_GEN_TAC `f:real^2->real^2` THEN GEN_TAC THEN STRIP_TAC THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [linear]) THEN
          SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                   VECTOR_MUL_COMPONENT; DIMINDEX_2; ARITH] THEN
          MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
          DISCH_THEN(ASSUME_TAC o GSYM) THEN GEN_TAC THEN
          GEN_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
          COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
          SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                   VECTOR_MUL_COMPONENT];
          X_GEN_TAC `v:real^N` THEN REWRITE_TAC[dot; GSYM REAL_POW_2] THEN
          SUBGOAL_THEN `dimindex(:N) = 2 + (dimindex(:N) - 2)` SUBST1_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
          BINOP_TAC THENL
           [RULE_ASSUM_TAC(REWRITE_RULE[dot; DIMINDEX_2; GSYM REAL_POW_2]) THEN
            FIRST_X_ASSUM(MP_TAC o SPEC `(lambda i. (v:real^N)$i):real^2`) THEN
            MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
            MATCH_MP_TAC SUM_EQ_NUMSEG THEN
            FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
             `2 <= n ==> !i. i <= 2 ==> i <= n`)) THEN
            SIMP_TAC[LAMBDA_BETA; DIMINDEX_2];
            ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> 2 + n - 2 = n`] THEN
            MATCH_MP_TAC SUM_EQ_NUMSEG THEN
            SIMP_TAC[ARITH_RULE `2 + 1 <= i ==> 1 <= i`;
                     LAMBDA_BETA; DIMINDEX_2] THEN
            REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
            ASM_ARITH_TAC]]];
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
      REWRITE_TAC[IN_UNIV; GSYM FUN_EQ_THM] THEN
      SIMP_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART;
               LAMBDA_BETA; DIMINDEX_2; ARITH; I_THM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INSERT_SUBSET; EMPTY_SUBSET]) THEN
      ASM_SIMP_TAC[lemma0] THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_2; ARITH; COND_ID] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(a:real^N)$i = &0 /\ (b:real^N)$i = &0` ASSUME_TAC THENL
       [FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
        REWRITE_TAC[SPAN_2; IN_ELIM_THM; IN_UNIV] THEN REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                     BASIS_COMPONENT] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
        (REAL_ARITH_TAC ORELSE ASM_ARITH_TAC);
        ASM_REWRITE_TAC[reflect_along; VECTOR_SUB_COMPONENT; REAL_MUL_RZERO;
                        VECTOR_MUL_COMPONENT; REAL_SUB_RZERO]]]) in
  let lemma3 = prove
   (`!a b:real^N r.
          ~(a = vec 0) /\ ~(b = vec 0)
          ==> homotopic_with orthogonal_transformation ((:real^N),(:real^N))
                             (reflect_along a o reflect_along b) I`,
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `dimindex(:N) = 1` THENL
     [ASM_SIMP_TAC[o_DEF; I_DEF; REFLECT_ALONG_1D; VECTOR_NEG_NEG] THEN
      REWRITE_TAC[HOMOTOPIC_WITH_REFL; SUBSET_UNIV; CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_ID];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP(ARITH_RULE
       `~(n = 1) ==> 1 <= n ==> 2 <= n`)) THEN
      REWRITE_TAC[DIMINDEX_GE_1] THEN DISCH_TAC] THEN
    MP_TAC(ISPECL [`span{a:real^N,b}`; `span{basis 1:real^N,basis 2}`]
          ORTHOGONAL_TRANSFORMATION_INTO_SUBSPACE) THEN
    REWRITE_TAC[SUBSPACE_SPAN; DIM_SPAN] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[DIM_INSERT; SPAN_SING; SPAN_EMPTY;
                      IN_SING; DIM_EMPTY] THEN
      MATCH_MP_TAC(ARITH_RULE `m <= 2 /\ n = 2 ==> m <= n`) THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[BASIS_NONZERO; ARITH] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(CHOOSE_THEN (MP_TAC o AP_TERM `(\x:real^N. x$1)`)) THEN
      ASM_SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT;
                   ARITH; DIMINDEX_GE_1] THEN
      REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPEC `f:real^N->real^N` ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN
     `homotopic_with orthogonal_transformation ((:real^N),(:real^N))
       (g o (f o (reflect_along a o reflect_along b) o (g:real^N->real^N)) o f)
       (g o (f o I o (g:real^N->real^N)) o f)`
    MP_TAC THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[o_ASSOC] THEN ASM_REWRITE_TAC[GSYM o_ASSOC; I_O_ID]] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
    EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR; LINEAR_CONTINUOUS_ON] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
    EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR; LINEAR_CONTINUOUS_ON] THEN
    ASM_REWRITE_TAC[I_O_ID] THEN
    MP_TAC(ISPEC `f:real^N->real^N` REFLECT_ALONG_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[GSYM ORTHOGONAL_TRANSFORMATION] THEN
    DISCH_THEN(ASSUME_TAC o GSYM) THEN
    SUBGOAL_THEN
     `!h:real^N->real^N.
          orthogonal_transformation (g o h o (f:real^N->real^N)) <=>
          orthogonal_transformation h`
     (fun th -> REWRITE_TAC[th; ETA_AX])
    THENL
     [GEN_TAC THEN EQ_TAC THEN
      ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `h:real^N->real^N = f o (g o h o f) o (g:real^N->real^N)`
      SUBST1_TAC THENL
       [ALL_TAC; ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE]] THEN
      ASM_REWRITE_TAC[o_ASSOC] THEN ASM_REWRITE_TAC[GSYM o_ASSOC; I_O_ID];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(f:real^N->real^N) o (reflect_along a o reflect_along b) o g =
      reflect_along (f a) o reflect_along (f b)`
    SUBST1_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM]) THEN
      ASM_REWRITE_TAC[o_DEF];
      MATCH_MP_TAC lemma2 THEN RULE_ASSUM_TAC
       (REWRITE_RULE[GSYM NORM_EQ_0; ORTHOGONAL_TRANSFORMATION]) THEN
      ASM_REWRITE_TAC[GSYM NORM_EQ_0] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
         SUBSET_TRANS)) THEN
      ASM_SIMP_TAC[GSYM SPAN_LINEAR_IMAGE; IMAGE_CLAUSES] THEN
      REWRITE_TAC[SPAN_INC]]) in
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `dimindex(:N)`]
        ORTHOGONAL_TRANSFORMATION_GENERATED_BY_REFLECTIONS) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n:num <= a + n`] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(real^N)list` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `ALL (\v:real^N. ~(v = vec 0)) l` THEN
  UNDISCH_TAC `orthogonal_transformation(f:real^N->real^N)` THEN
  MATCH_MP_TAC(TAUT `r /\ (p /\ q ==> s) ==> r ==> p ==> q ==> s`) THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN
  SPEC_TAC(`l:(real^N)list`,`l:(real^N)list`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN GEN_TAC THEN
  WF_INDUCT_TAC `LENGTH(l:(real^N)list)` THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`l:(real^N)list`,`l:(real^N)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[ALL; ITLIST; HOMOTOPIC_WITH_REFL] THEN
  REWRITE_TAC[REWRITE_RULE[GSYM I_DEF] CONTINUOUS_ON_ID;
              ORTHOGONAL_TRANSFORMATION_I; SUBSET_UNIV] THEN
  X_GEN_TAC `a:real^N` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[ALL; ITLIST; I_O_ID; DET_MATRIX_REFLECT_ALONG] THEN
  REWRITE_TAC[ORTHGOONAL_TRANSFORMATION_REFLECT_ALONG] THEN
  CONJ_TAC THENL [MESON_TAC[REAL_ARITH `~(-- &1 = &1)`]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`b:real^N`; `l:(real^N)list`] THEN
  REPLICATE_TAC 2 (DISCH_THEN(K ALL_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `l:(real^N)list`) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `n < SUC(SUC n)`] THEN
  SIMP_TAC[LINEAR_COMPOSE; LINEAR_REFLECT_ALONG; MATRIX_COMPOSE;
     ORTHGOONAL_TRANSFORMATION_REFLECT_ALONG;
     ORTHOGONAL_TRANSFORMATION_COMPOSE; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
  DISCH_THEN(fun th ->
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN MP_TAC th) THEN
  ASM_SIMP_TAC[DET_MUL; DET_MATRIX_REFLECT_ALONG; REAL_ARITH
   `-- &1 * -- &1 * x = x`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_TRANS) THEN
  GEN_REWRITE_TAC RAND_CONV [MESON[I_O_ID] `f = I o f`] THEN
  REWRITE_TAC[o_ASSOC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
  ABBREV_TAC `g = ITLIST (\v:real^N h. reflect_along v o h) l I` THEN
  SUBGOAL_THEN
   `(\f:real^N->real^N.
        orthogonal_transformation (f o g)) = orthogonal_transformation`
  SUBST1_TAC THENL [ALL_TAC; MATCH_MP_TAC lemma3 THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f:real^N->real^N` THEN
  EQ_TAC THEN ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `g:real^N->real^N` ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `h:real^N->real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `f = ((f:real^N->real^N) o (g:real^N->real^N)) o h`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM o_ASSOC; I_O_ID];
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE]]);;

let HOMOTOPIC_SPECIAL_ORTHOGONAL_TRANSFORMATIONS,
    HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS = (CONJ_PAIR o prove)
 (`(!f g. homotopic_with
            (\h. orthogonal_transformation h /\ det(matrix h) = det(matrix f))
            ((:real^N),(:real^N)) f g <=>
          homotopic_with
            orthogonal_transformation ((:real^N),(:real^N)) f g) /\
   !f g. homotopic_with orthogonal_transformation ((:real^N),(:real^N)) f g <=>
         orthogonal_transformation f /\ orthogonal_transformation g /\
         det(matrix f) = det(matrix g)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(u ==> s) /\ (s ==> t) /\ (t ==> u)
    ==> (u <=> t) /\ (t <=> s)`) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN MESON_TAC[];
    STRIP_TAC THEN
    MP_TAC(ISPEC `g:real^N->real^N` ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(f:real^N->real^N) = g o (h:real^N->real^N) o f /\ g = g o I`
     (fun th -> ONCE_REWRITE_TAC[th])
    THENL [ASM_REWRITE_TAC[o_ASSOC; I_O_ID]; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
    EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR; LINEAR_CONTINUOUS_ON] THEN
    SUBGOAL_THEN
      `!k:real^N->real^N.
          orthogonal_transformation (g o k) <=> orthogonal_transformation k`
      (fun th -> REWRITE_TAC[th; ETA_AX])
    THENL
     [GEN_TAC THEN EQ_TAC THEN
      ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE] THEN DISCH_THEN
       (MP_TAC o SPEC `h:real^N->real^N` o MATCH_MP (ONCE_REWRITE_RULE
         [IMP_CONJ_ALT] ORTHOGONAL_TRANSFORMATION_COMPOSE)) THEN
      ASM_SIMP_TAC[o_ASSOC; I_O_ID];
      MATCH_MP_TAC NULLHOMOTOPIC_ORTHOGONAL_TRANSFORMATION THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM
       `\f:real^N->real^N. det(matrix f)`)) THEN
      ASM_SIMP_TAC[MATRIX_COMPOSE; ORTHOGONAL_TRANSFORMATION_LINEAR;
                   ORTHOGONAL_TRANSFORMATION_COMPOSE; DET_MUL;
                   MATRIX_I; DET_I]];
    REWRITE_TAC[homotopic_with] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `k:real^(1,N)finite_sum->real^N` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN MP_TAC(ISPECL
     [`\t. lift(
       det(matrix((k:real^(1,N)finite_sum->real^N) o pastecart t)))`;
      `interval[vec 0:real^1,vec 1]`]
     CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
    REWRITE_TAC[CONNECTED_INTERVAL] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN
        SIMP_TAC[matrix; LAMBDA_BETA; o_DEF] THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
        ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
                 CONTINUOUS_ON_ID] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_UNIV];
        X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN
        REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `u:real^1` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; LIFT_EQ] THEN
        SUBGOAL_THEN
         `orthogonal_transformation
           ((k:real^(1,N)finite_sum->real^N) o pastecart t) /\
          orthogonal_transformation (k o pastecart u)`
        MP_TAC THENL [ASM_SIMP_TAC[o_DEF]; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN
          (STRIP_ASSUME_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX o
                    MATCH_MP ORTHOGONAL_MATRIX_MATRIX)) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      REWRITE_TAC[o_DEF; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `a:real^1` THEN DISCH_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM FUN_EQ_THM])) THEN
      REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
      ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL; GSYM LIFT_EQ]]]);;

(* ------------------------------------------------------------------------- *)
(* Complex tangent function.                                                 *)
(* ------------------------------------------------------------------------- *)

let ctan = new_definition
 `ctan z = csin z / ccos z`;;

let CTAN_0 = prove
 (`ctan(Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[ctan; CSIN_0; CCOS_0; COMPLEX_DIV_1]);;

let CTAN_NEG = prove
 (`!z. ctan(--z) = --(ctan z)`,
  REWRITE_TAC[ctan; CSIN_NEG; CCOS_NEG; complex_div; COMPLEX_MUL_LNEG]);;

let CTAN_ADD = prove
 (`!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0)) /\
         ~(ccos(w + z) = Cx(&0))
         ==> ctan(w + z) = (ctan w + ctan z) / (Cx(&1) - ctan(w) * ctan(z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ctan; CSIN_ADD; CCOS_ADD] THEN
  CONV_TAC COMPLEX_FIELD);;

let CTAN_DOUBLE = prove
 (`!z. ~(ccos(z) = Cx(&0)) /\ ~(ccos(Cx(&2) * z) = Cx(&0))
       ==> ctan(Cx(&2) * z) =
           (Cx(&2) * ctan z) / (Cx(&1) - ctan(z) pow 2)`,
  SIMP_TAC[COMPLEX_MUL_2; CTAN_ADD; COMPLEX_POW_2]);;

let CTAN_SUB = prove
 (`!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0)) /\
         ~(ccos(w - z) = Cx(&0))
         ==> ctan(w - z) = (ctan w - ctan z) / (Cx(&1) + ctan(w) * ctan(z))`,
  SIMP_TAC[complex_sub; CTAN_ADD; CCOS_NEG; CTAN_NEG] THEN
  REWRITE_TAC[COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG]);;

let COMPLEX_ADD_CTAN = prove
 (`!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0))
         ==> ctan(w) + ctan(z) = csin(w + z) / (ccos(w) * ccos(z))`,
  REWRITE_TAC[ctan; CSIN_ADD] THEN CONV_TAC COMPLEX_FIELD);;

let COMPLEX_SUB_CTAN = prove
 (`!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0))
         ==> ctan(w) - ctan(z) = csin(w - z) / (ccos(w) * ccos(z))`,
  REWRITE_TAC[ctan; CSIN_SUB] THEN CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Analytic properties of tangent function.                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_CTAN = prove
 (`!z. ~(ccos z = Cx(&0))
       ==> (ctan has_complex_derivative (inv(ccos(z) pow 2))) (at z)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[ctan] THEN COMPLEX_DIFF_TAC THEN
  MP_TAC(SPEC `z:complex` CSIN_CIRCLE) THEN
  POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD);;

let COMPLEX_DIFFERENTIABLE_AT_CTAN = prove
 (`!z. ~(ccos z = Cx(&0)) ==> ctan complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CTAN]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CTAN = prove
 (`!s z. ~(ccos z = Cx(&0))
         ==> ctan complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CTAN]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CTAN)));;

let CONTINUOUS_AT_CTAN = prove
 (`!z. ~(ccos z = Cx(&0)) ==> ctan continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CTAN;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CTAN = prove
 (`!s z. ~(ccos z = Cx(&0)) ==> ctan continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CTAN]);;

let CONTINUOUS_ON_CTAN = prove
 (`!s. (!z. z IN s ==> ~(ccos z = Cx(&0))) ==> ctan continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CTAN]);;

let HOLOMORPHIC_ON_CTAN = prove
 (`!s. (!z. z IN s ==> ~(ccos z = Cx(&0))) ==> ctan holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CTAN]);;

(* ------------------------------------------------------------------------- *)
(* Real tangent function.                                                    *)
(* ------------------------------------------------------------------------- *)

let tan_def = new_definition
 `tan(x) = Re(ctan(Cx x))`;;

let CNJ_CTAN = prove
 (`!z. cnj(ctan z) = ctan(cnj z)`,
  REWRITE_TAC[ctan; CNJ_DIV; CNJ_CSIN; CNJ_CCOS]);;

let REAL_TAN = prove
 (`!z. real z ==> real(ctan z)`,
  SIMP_TAC[REAL_CNJ; CNJ_CTAN]);;

let CX_TAN = prove
 (`!x. Cx(tan x) = ctan(Cx x)`,
  REWRITE_TAC[tan_def] THEN MESON_TAC[REAL; REAL_CX; REAL_TAN]);;

let tan = prove
 (`!x. tan x = sin x / cos x`,
  REWRITE_TAC[GSYM CX_INJ; CX_DIV; CX_TAN; CX_SIN; CX_COS; ctan]);;

let TAN_0 = prove
 (`tan(&0) = &0`,
  REWRITE_TAC[GSYM CX_INJ; CX_TAN; CTAN_0]);;

let TAN_PI = prove
 (`tan(pi) = &0`,
  REWRITE_TAC[tan; SIN_PI; real_div; REAL_MUL_LZERO]);;

let TAN_NPI = prove
 (`!n. tan(&n * pi) = &0`,
  REWRITE_TAC[tan; SIN_NPI; real_div; REAL_MUL_LZERO]);;

let TAN_NEG = prove
 (`!x. tan(--x) = --(tan x)`,
  REWRITE_TAC[GSYM CX_INJ; CX_TAN; CX_NEG; CTAN_NEG]);;

let TAN_PERIODIC_PI = prove
 (`!x. tan(x + pi) = tan(x)`,
  REWRITE_TAC[tan; SIN_PERIODIC_PI; COS_PERIODIC_PI; real_div] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_INV_NEG; REAL_MUL_RNEG; REAL_NEG_NEG]);;

let TAN_PERIODIC_NPI = prove
 (`!x n. tan(x + &n * pi) = tan(x)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
  ASM_REWRITE_TAC[REAL_ADD_ASSOC; TAN_PERIODIC_PI]);;

let TAN_ADD = prove
 (`!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x + y) = &0)
         ==> tan(x + y) = (tan(x) + tan(y)) / (&1 - tan(x) * tan(y))`,
  REWRITE_TAC[GSYM CX_INJ; CX_TAN; CX_SIN; CX_COS; CTAN_ADD;
              CX_DIV; CX_ADD; CX_SUB; CX_MUL]);;

let TAN_SUB = prove
 (`!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x - y) = &0)
         ==> tan(x - y) = (tan(x) - tan(y)) / (&1 + tan(x) * tan(y))`,
  REWRITE_TAC[GSYM CX_INJ; CX_TAN; CX_SIN; CX_COS; CX_ADD; CTAN_SUB;
              CX_DIV; CX_ADD; CX_SUB; CX_MUL]);;

let TAN_DOUBLE = prove
 (`!x. ~(cos(x) = &0) /\ ~(cos(&2 * x) = &0)
       ==> tan(&2 * x) = (&2 * tan(x)) / (&1 - (tan(x) pow 2))`,
  SIMP_TAC[REAL_MUL_2; TAN_ADD; REAL_POW_2]);;

let REAL_ADD_TAN = prove
 (`!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0)
         ==> tan(x) + tan(y) = sin(x + y) / (cos(x) * cos(y))`,
  REWRITE_TAC[GSYM CX_INJ; CX_TAN; CX_SIN; CX_COS; CX_MUL; CX_ADD; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_ADD_CTAN]);;

let REAL_SUB_TAN = prove
 (`!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0)
         ==> tan(x) - tan(y) = sin(x - y) / (cos(x) * cos(y))`,
  REWRITE_TAC[GSYM CX_INJ; CX_TAN; CX_SIN; CX_COS; CX_MUL; CX_SUB; CX_DIV] THEN
  REWRITE_TAC[COMPLEX_SUB_CTAN]);;

let TAN_PI4 = prove
 (`tan(pi / &4) = &1`,
  REWRITE_TAC[tan; SIN_COS; REAL_ARITH `p / &2 - p / &4 = p / &4`] THEN
  MATCH_MP_TAC REAL_DIV_REFL THEN REWRITE_TAC[COS_EQ_0; PI_NZ; REAL_FIELD
   `p / &4 = (n + &1 / &2) * p <=> p = &0 \/ n = -- &1 / &4`] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
   REAL_ABS_INTEGER_LEMMA)) THEN
  REAL_ARITH_TAC);;

let TAN_POS_PI2 = prove
 (`!x. &0 < x /\ x < pi / &2 ==> &0 < tan x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tan] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI; MATCH_MP_TAC COS_POS_PI] THEN
  ASM_REAL_ARITH_TAC);;

let TAN_POS_PI2_LE = prove
 (`!x. &0 <= x /\ x < pi / &2 ==> &0 <= tan x`,
  REWRITE_TAC[REAL_LE_LT] THEN MESON_TAC[TAN_0; TAN_POS_PI2]);;

let COS_TAN = prove
 (`!x. abs(x) < pi / &2 ==> cos(x) = &1 / sqrt(&1 + tan(x) pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_FIELD
   `sqrt(s) pow 2 = s /\ c pow 2 * s = &1 /\ ~(&1 + c * sqrt s = &0)
    ==> c = &1 / sqrt s`) THEN
  SUBGOAL_THEN `&0 < &1 + tan x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `tan x` REAL_LE_SQUARE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [REWRITE_TAC[tan] THEN
    MATCH_MP_TAC(REAL_FIELD
     `s pow 2 + c pow 2 = &1 /\ &0 < c
      ==> c pow 2 * (&1 + (s / c) pow 2) = &1`) THEN
    ASM_SIMP_TAC[SIN_CIRCLE; COS_POS_PI; REAL_BOUNDS_LT];
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&1 + x = &0)`) THEN
    ASM_SIMP_TAC[SIN_CIRCLE; COS_POS_PI; REAL_BOUNDS_LT; SQRT_POS_LT;
                 REAL_LT_MUL]]);;

let SIN_TAN = prove
 (`!x. abs(x) < pi / &2 ==> sin(x) = tan(x) / sqrt(&1 + tan(x) pow 2)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / b = a * &1 / b`] THEN
  ASM_SIMP_TAC[GSYM COS_TAN] THEN
  ASM_SIMP_TAC[tan; REAL_DIV_RMUL; REAL_LT_IMP_NZ; COS_POS_PI;
               REAL_BOUNDS_LT]);;

(* ------------------------------------------------------------------------- *)
(* Monotonicity theorems for the basic trig functions.                       *)
(* ------------------------------------------------------------------------- *)

let SIN_MONO_LT = prove
 (`!x y. --(pi / &2) <= x /\ x < y /\ y <= pi / &2 ==> sin(x) < sin(y)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_SUB_SIN; REAL_ARITH `&0 < &2 * x <=> &0 < x`] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI; MATCH_MP_TAC COS_POS_PI] THEN
  ASM_REAL_ARITH_TAC);;

let SIN_MONO_LE = prove
 (`!x y. --(pi / &2) <= x /\ x <= y /\ y <= pi / &2 ==> sin(x) <= sin(y)`,
  MESON_TAC[SIN_MONO_LT; REAL_LE_LT]);;

let SIN_MONO_LT_EQ = prove
 (`!x y. --(pi / &2) <= x /\ x <= pi / &2 /\ --(pi / &2) <= y /\ y <= pi / &2
         ==> (sin(x) < sin(y) <=> x < y)`,
  MESON_TAC[REAL_NOT_LE; SIN_MONO_LT; SIN_MONO_LE]);;

let SIN_MONO_LE_EQ = prove
 (`!x y. --(pi / &2) <= x /\ x <= pi / &2 /\ --(pi / &2) <= y /\ y <= pi / &2
         ==> (sin(x) <= sin(y) <=> x <= y)`,
  MESON_TAC[REAL_NOT_LE; SIN_MONO_LT; SIN_MONO_LE]);;

let SIN_INJ_PI = prove
 (`!x y. --(pi / &2) <= x /\ x <= pi / &2 /\
         --(pi / &2) <= y /\ y <= pi / &2 /\
         sin(x) = sin(y)
         ==> x = y`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN MESON_TAC[SIN_MONO_LE_EQ]);;

let COS_MONO_LT = prove
 (`!x y. &0 <= x /\ x < y /\ y <= pi ==> cos(y) < cos(x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_SUB_COS; REAL_ARITH `&0 < &2 * x <=> &0 < x`] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN
  ASM_REAL_ARITH_TAC);;

let COS_MONO_LE = prove
 (`!x y. &0 <= x /\ x <= y /\ y <= pi ==> cos(y) <= cos(x)`,
  MESON_TAC[COS_MONO_LT; REAL_LE_LT]);;

let COS_MONO_LT_EQ = prove
 (`!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi
         ==> (cos(x) < cos(y) <=> y < x)`,
  MESON_TAC[REAL_NOT_LE; COS_MONO_LT; COS_MONO_LE]);;

let COS_MONO_LE_EQ = prove
 (`!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi
         ==> (cos(x) <= cos(y) <=> y <= x)`,
  MESON_TAC[REAL_NOT_LE; COS_MONO_LT; COS_MONO_LE]);;

let COS_INJ_PI = prove
 (`!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi /\ cos(x) = cos(y)
         ==> x = y`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN MESON_TAC[COS_MONO_LE_EQ]);;

let TAN_MONO_LT = prove
 (`!x y. --(pi / &2) < x /\ x < y /\ y < pi / &2 ==> tan(x) < tan(y)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [GSYM REAL_SUB_LT] THEN
  SUBGOAL_THEN `&0 < cos(x) /\ &0 < cos(y)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COS_POS_PI;
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_SUB_TAN] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
    MATCH_MP_TAC SIN_POS_PI] THEN
  ASM_REAL_ARITH_TAC);;

let TAN_MONO_LE = prove
 (`!x y. --(pi / &2) < x /\ x <= y /\ y < pi / &2 ==> tan(x) <= tan(y)`,
  REWRITE_TAC[REAL_LE_LT] THEN MESON_TAC[TAN_MONO_LT]);;

let TAN_MONO_LT_EQ = prove
 (`!x y. --(pi / &2) < x /\ x < pi / &2 /\ --(pi / &2) < y /\ y < pi / &2
         ==> (tan(x) < tan(y) <=> x < y)`,
  MESON_TAC[REAL_NOT_LE; TAN_MONO_LT; TAN_MONO_LE]);;

let TAN_MONO_LE_EQ = prove
 (`!x y. --(pi / &2) < x /\ x < pi / &2 /\ --(pi / &2) < y /\ y < pi / &2
         ==> (tan(x) <= tan(y) <=> x <= y)`,
  MESON_TAC[REAL_NOT_LE; TAN_MONO_LT; TAN_MONO_LE]);;

let TAN_BOUND_PI2 = prove
 (`!x. abs(x) < pi / &4 ==> abs(tan x) < &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM TAN_PI4] THEN
  REWRITE_TAC[GSYM TAN_NEG; REAL_ARITH `abs(x) < a <=> --a < x /\ x < a`] THEN
  CONJ_TAC THEN MATCH_MP_TAC TAN_MONO_LT THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let TAN_COT = prove
 (`!x. tan(pi / &2 - x) = inv(tan x)`,
  REWRITE_TAC[tan; SIN_SUB; COS_SUB; SIN_PI2; COS_PI2; REAL_INV_DIV] THEN
  GEN_TAC THEN BINOP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Approximation to pi.                                                      *)
(* ------------------------------------------------------------------------- *)

let SIN_PI6_STRADDLE = prove
 (`!a b. &0 <= a /\ a <= b /\ b <= &4 /\
         sin(a / &6) <= &1 / &2 /\ &1 / &2 <= sin(b / &6)
         ==> a <= pi /\ pi <= b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`pi / &6`; `b / &6`] SIN_MONO_LE_EQ) THEN
  MP_TAC(SPECL [`a / &6`; `pi / &6`] SIN_MONO_LE_EQ) THEN
  ASM_REWRITE_TAC[SIN_PI6] THEN
  SUBGOAL_THEN `!x. &0 < x /\ x < &7 / &5 ==> &0 < sin x`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`0`; `Cx(x)`] TAYLOR_CSIN) THEN
    REWRITE_TAC[VSUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[COMPLEX_DIV_1; COMPLEX_POW_1; complex_pow] THEN
    REWRITE_TAC[COMPLEX_MUL_LID; GSYM CX_SIN; GSYM CX_SUB] THEN
    REWRITE_TAC[IM_CX; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_EXP_0] THEN
    MATCH_MP_TAC(REAL_ARITH
     `e + d < a ==> abs(s - a) <= d ==> e < s`) THEN
    ASM_SIMP_TAC[real_abs; real_pow; REAL_MUL_LID; REAL_LT_IMP_LE] THEN
    SIMP_TAC[REAL_ARITH `&0 + x pow 3 / &2 < x <=> x * x pow 2 < x * &2`] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `(&7 / &5) pow 2` THEN
    ASM_SIMP_TAC[REAL_POW_LT2; ARITH_EQ; REAL_LT_IMP_LE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    DISCH_THEN(MP_TAC o SPEC `pi`) THEN
    SIMP_TAC[SIN_PI; REAL_LT_REFL; PI_POS; REAL_NOT_LT] THEN
    ASM_REAL_ARITH_TAC]);;

let PI_APPROX_32 = prove
 (`abs(pi - &13493037705 / &4294967296) <= inv(&2 pow 32)`,
  REWRITE_TAC[REAL_ARITH `abs(x - a) <= e <=> a - e <= x /\ x <= a + e`] THEN
  MATCH_MP_TAC SIN_PI6_STRADDLE THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`5`; `Cx(&1686629713 / &3221225472)`] TAYLOR_CSIN);
    MP_TAC(SPECL [`5`; `Cx(&6746518853 / &12884901888)`] TAYLOR_CSIN)] THEN
  SIMP_TAC[COMPLEX_NORM_CX; GSYM CX_POW; GSYM CX_DIV; GSYM CX_MUL;
           GSYM CX_NEG; VSUM_CX; FINITE_NUMSEG; GSYM CX_SIN; GSYM CX_SUB] THEN
  REWRITE_TAC[IM_CX; REAL_ABS_NUM; REAL_EXP_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; GSYM REAL_POW_POW] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_MUL; real_div] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  CONV_TAC(ONCE_DEPTH_CONV HORNER_SUM_CONV) THEN REAL_ARITH_TAC);;

let PI2_BOUNDS = prove
 (`&0 < pi / &2 /\ pi / &2 < &2`,
  MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Complex logarithms (the conventional principal value).                    *)
(* ------------------------------------------------------------------------- *)

let clog = new_definition
 `clog z = @w. cexp(w) = z /\ --pi < Im(w) /\ Im(w) <= pi`;;

let EXISTS_COMPLEX' = prove
 (`!P. (?z. P (Re z) (Im z)) <=> ?x y. P x y`,
  MESON_TAC[RE; IM; COMPLEX]);;

let CLOG_WORKS = prove
 (`!z. ~(z = Cx(&0))
       ==> cexp(clog z) = z /\ --pi < Im(clog z) /\ Im(clog z) <= pi`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[clog] THEN CONV_TAC SELECT_CONV THEN
  MP_TAC(SPEC `z / Cx(norm z)` COMPLEX_UNIMODULAR_POLAR) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ABS_NORM; REAL_DIV_REFL; COMPLEX_NORM_ZERO];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `x:real` SINCOS_PRINCIPAL_VALUE) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `complex(log(norm(z:complex)),y)` THEN
  ASM_REWRITE_TAC[RE; IM; CEXP_COMPLEX] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
  ASM_SIMP_TAC[EXP_LOG; COMPLEX_NORM_NZ; COMPLEX_DIV_LMUL;
               COMPLEX_NORM_ZERO; CX_INJ]);;

let CEXP_CLOG = prove
 (`!z. ~(z = Cx(&0)) ==> cexp(clog z) = z`,
  SIMP_TAC[CLOG_WORKS]);;

let CLOG_CEXP = prove
 (`!z. --pi < Im(z) /\ Im(z) <= pi ==> clog(cexp z) = z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[clog] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `w:complex` THEN
  EQ_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[CEXP_EQ] THEN
  REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(X_CHOOSE_THEN `n:real`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_MUL_RZERO; COMPLEX_ADD_RID; COMPLEX_MUL_LZERO] THEN
  SUBGOAL_THEN `abs(n * pi) < &1 * pi` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_LT_RMUL_EQ; PI_POS; REAL_ABS_PI] THEN
  ASM_MESON_TAC[REAL_ABS_INTEGER_LEMMA; REAL_NOT_LT]);;

let CLOG_EQ = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0)) ==> (clog w = clog z <=> w = z)`,
  MESON_TAC[CEXP_CLOG]);;

let CLOG_UNIQUE = prove
 (`!w z. --pi < Im(z) /\ Im(z) <= pi /\ cexp(z) = w ==> clog w = z`,
  MESON_TAC[CLOG_CEXP]);;

let RE_CLOG = prove
 (`!z. ~(z = Cx(&0)) ==> Re(clog z) = log(norm z)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC o AP_TERM `norm:complex->real` o MATCH_MP CEXP_CLOG) THEN
  REWRITE_TAC[NORM_CEXP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LOG_EXP]);;

let EXISTS_COMPLEX_ROOT = prove
 (`!a n. ~(n = 0) ==> ?z. z pow n = a`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a = Cx(&0)` THENL
   [EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_POW_ZERO];
    EXISTS_TAC `cexp(clog(a) / Cx(&n))` THEN REWRITE_TAC[GSYM CEXP_N] THEN
    ASM_SIMP_TAC[COMPLEX_DIV_LMUL; CX_INJ; REAL_OF_NUM_EQ; CEXP_CLOG]]);;

(* ------------------------------------------------------------------------- *)
(* Derivative of clog away from the branch cut.                              *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_CLOG = prove
 (`!z. (Im(z) = &0 ==> &0 < Re(z))
       ==> (clog has_complex_derivative inv(z)) (at z)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG_X THEN
  EXISTS_TAC `cexp` THEN
  EXISTS_TAC `{w | --pi < Im(w) /\ Im(w) < pi}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC `z = Cx(&0)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
     ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_LT_REFL];
     ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CEXP; CEXP_CLOG; CLOG_CEXP; REAL_LT_IMP_LE] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SET_RULE `{x | p x /\ q x} = {x | p x} INTER {x | q x}`] THEN
    MATCH_MP_TAC OPEN_INTER THEN
    REWRITE_TAC[REAL_ARITH `--x < w <=> w > --x`] THEN
    REWRITE_TAC[OPEN_HALFSPACE_IM_LT; OPEN_HALFSPACE_IM_GT];
    ASM_SIMP_TAC[CLOG_WORKS];
    ASM_SIMP_TAC[CLOG_WORKS; REAL_LT_LE] THEN
    DISCH_THEN(fun th ->
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o MATCH_MP CEXP_CLOG) THEN
      POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
    ASM_REWRITE_TAC[EULER; COS_PI; SIN_PI; COMPLEX_MUL_RZERO] THEN
    REWRITE_TAC[COMPLEX_ADD_RID; CX_NEG; COMPLEX_MUL_RNEG] THEN
    REWRITE_TAC[COMPLEX_MUL_RID; IM_NEG; IM_CX; RE_NEG; RE_CX] THEN
    MP_TAC(SPEC `Re(clog z)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
    ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_CEXP; CEXP_CLOG]]);;

let COMPLEX_DIFFERENTIABLE_AT_CLOG = prove
 (`!z. (Im(z) = &0 ==> &0 < Re(z)) ==> clog complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CLOG]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CLOG = prove
 (`!s z. (Im(z) = &0 ==> &0 < Re(z))
         ==> clog complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CLOG]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CLOG)));;

let CONTINUOUS_AT_CLOG = prove
 (`!z. (Im(z) = &0 ==> &0 < Re(z)) ==> clog continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CLOG;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CLOG = prove
 (`!s z. (Im(z) = &0 ==> &0 < Re(z)) ==> clog continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CLOG]);;

let CONTINUOUS_ON_CLOG = prove
 (`!s. (!z. z IN s /\ Im(z) = &0 ==> &0 < Re(z)) ==> clog continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CLOG]);;

let HOLOMORPHIC_ON_CLOG = prove
 (`!s. (!z. z IN s /\ Im(z) = &0 ==> &0 < Re(z)) ==> clog holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CLOG]);;

(* ------------------------------------------------------------------------- *)
(* Relation to real log.                                                     *)
(* ------------------------------------------------------------------------- *)

let CX_LOG = prove
 (`!z. &0 < z ==> Cx(log z) = clog(Cx z)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th ->
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [SYM(MATCH_MP EXP_LOG th)]) THEN
  REWRITE_TAC[CX_EXP] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CLOG_CEXP THEN REWRITE_TAC[IM_CX] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Quadrant-type results for clog.                                           *)
(* ------------------------------------------------------------------------- *)

let RE_CLOG_POS_LT = prove
 (`!z. ~(z = Cx(&0)) ==> (abs(Im(clog z)) < pi / &2 <=> &0 < Re(z))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLOG_WORKS) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th])
    MP_TAC) THEN
  SIMP_TAC[RE_CEXP; REAL_LT_MUL_EQ; REAL_EXP_POS_LT] THEN
  SPEC_TAC(`clog z`,`z:complex`) THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `--p < x /\ x <= p
    ==> --(p / &2) < x /\ x < p / &2 \/
        --(p / &2) <= p + x /\ p + x <= p / &2 \/
        --(p / &2) <= x - p /\ x - p <= p / &2`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP COS_POS_PI) ORELSE
   FIRST_ASSUM(MP_TAC o MATCH_MP COS_POS_PI_LE)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[COS_ADD; COS_SUB; COS_PI; SIN_PI] THEN
  REAL_ARITH_TAC);;

let RE_CLOG_POS_LE = prove
 (`!z. ~(z = Cx(&0)) ==> (abs(Im(clog z)) <= pi / &2 <=> &0 <= Re(z))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLOG_WORKS) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th])
    MP_TAC) THEN
  SIMP_TAC[RE_CEXP; REAL_LE_MUL_EQ; REAL_EXP_POS_LT] THEN
  SPEC_TAC(`clog z`,`z:complex`) THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `--p < x /\ x <= p
    ==> --(p / &2) <= x /\ x <= p / &2 \/
        --(p / &2) < p + x /\ p + x < p / &2 \/
        --(p / &2) < x - p /\ x - p < p / &2`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP COS_POS_PI) ORELSE
   FIRST_ASSUM(MP_TAC o MATCH_MP COS_POS_PI_LE)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[COS_ADD; COS_SUB; COS_PI; SIN_PI] THEN
  REAL_ARITH_TAC);;

let IM_CLOG_POS_LT = prove
 (`!z. ~(z = Cx(&0)) ==> (&0 < Im(clog z) /\ Im(clog z) < pi <=> &0 < Im(z))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLOG_WORKS) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th])
    MP_TAC) THEN
  SIMP_TAC[IM_CEXP; REAL_LT_MUL_EQ; REAL_EXP_POS_LT] THEN
  SPEC_TAC(`clog z`,`z:complex`) THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `--p < x /\ x <= p
    ==> &0 < x /\ x < p \/
        &0 <= x + p /\ x + p <= p \/
        &0 <= x - p /\ x - p <= p`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP SIN_POS_PI) ORELSE
   FIRST_ASSUM(MP_TAC o MATCH_MP SIN_POS_PI_LE)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[SIN_ADD; SIN_SUB; COS_PI; SIN_PI] THEN
  REAL_ARITH_TAC);;

let IM_CLOG_POS_LE = prove
 (`!z. ~(z = Cx(&0)) ==> (&0 <= Im(clog z) <=> &0 <= Im(z))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLOG_WORKS) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th])
    MP_TAC) THEN
  SIMP_TAC[IM_CEXP; REAL_LE_MUL_EQ; REAL_EXP_POS_LT] THEN
  SPEC_TAC(`clog z`,`z:complex`) THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `--p < x /\ x <= p
    ==> &0 <= x /\ x <= p \/
        &0 < x + p /\ x + p < p \/
        &0 < p - x /\ p - x < p`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP SIN_POS_PI) ORELSE
   FIRST_ASSUM(MP_TAC o MATCH_MP SIN_POS_PI_LE)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[SIN_ADD; SIN_SUB; COS_PI; SIN_PI] THEN
  REAL_ARITH_TAC);;

let RE_CLOG_POS_LT_IMP = prove
 (`!z. &0 < Re(z) ==> abs(Im(clog z)) < pi / &2`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_SIMP_TAC[RE_CLOG_POS_LT; RE_CX; REAL_LT_REFL]);;

let IM_CLOG_POS_LT_IMP = prove
 (`!z. &0 < Im(z) ==> &0 < Im(clog z) /\ Im(clog z) < pi`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_SIMP_TAC[IM_CLOG_POS_LT; IM_CX; REAL_LT_REFL]);;

let IM_CLOG_EQ_0 = prove
 (`!z. ~(z = Cx(&0)) ==> (Im(clog z) = &0 <=> &0 < Re(z) /\ Im(z) = &0)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [REAL_ARITH `z = &0 <=> &0 <= z /\ ~(&0 < z)`] THEN
  ASM_SIMP_TAC[GSYM RE_CLOG_POS_LT; GSYM IM_CLOG_POS_LE;
               GSYM IM_CLOG_POS_LT] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let IM_CLOG_EQ_PI = prove
 (`!z. ~(z = Cx(&0)) ==> (Im(clog z) = pi <=> Re(z) < &0 /\ Im(z) = &0)`,
  SIMP_TAC[PI_POS; RE_CLOG_POS_LE; IM_CLOG_POS_LE; IM_CLOG_POS_LT; CLOG_WORKS;
           REAL_ARITH `&0 < pi ==> (x = pi <=> (&0 <= x /\ x <= pi) /\
                            ~(abs x <= pi / &2) /\ ~(&0 < x /\ x < pi))`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Various properties.                                                       *)
(* ------------------------------------------------------------------------- *)

let CNJ_CLOG = prove
 (`!z. (Im z = &0 ==> &0 < Re z) ==> cnj(clog z) = clog(cnj z)`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_LT_REFL] THEN
  DISCH_TAC THEN MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
  REWRITE_TAC[GSYM CNJ_CEXP] THEN
  ASM_SIMP_TAC[CEXP_CLOG; CNJ_EQ_CX; IM_CNJ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(--p < x /\ x <= p) /\ (--p < y /\ y <= p) /\
    ~(x = p /\ y = p)
    ==> abs(--x - y) < &2 * p`) THEN
  ASM_SIMP_TAC[IM_CLOG_EQ_PI; CNJ_EQ_CX; CLOG_WORKS] THEN
  ASM_REAL_ARITH_TAC);;

let CLOG_INV = prove
 (`!z. (Im(z) = &0 ==> &0 < Re z) ==> clog(inv z) = --(clog z)`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_LT_REFL] THEN
  STRIP_TAC THEN MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
  ASM_SIMP_TAC[CEXP_CLOG; CEXP_NEG; COMPLEX_INV_EQ_0] THEN
  REWRITE_TAC[IM_NEG; REAL_SUB_RNEG] THEN
  MATCH_MP_TAC(REAL_ARITH
   `--pi < x /\ x <= pi /\ --pi < y /\ y <= pi /\
    ~(x = pi /\ y = pi) ==> abs(x + y) < &2 * pi`) THEN
  ASM_SIMP_TAC[CLOG_WORKS; COMPLEX_INV_EQ_0; IM_CLOG_EQ_PI] THEN
  UNDISCH_TAC `Im z = &0 ==> &0 < Re z` THEN
  ASM_CASES_TAC `Im z = &0` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CLOG_1 = prove
 (`clog(Cx(&1)) = Cx(&0)`,
  REWRITE_TAC[GSYM CEXP_0] THEN MATCH_MP_TAC CLOG_CEXP THEN
  REWRITE_TAC[IM_CX] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let CLOG_NEG_1 = prove
 (`clog(--Cx(&1)) = ii * Cx pi`,
  MATCH_MP_TAC COMPLEX_EQ_CEXP THEN REWRITE_TAC[GSYM CX_NEG] THEN
  SIMP_TAC[CEXP_EULER; GSYM CX_COS; GSYM CX_SIN; IM_MUL_II; IM_CX; RE_CX] THEN
  REWRITE_TAC[COS_PI; SIN_PI; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
  SIMP_TAC[CLOG_WORKS; COMPLEX_RING `~(Cx(-- &1) = Cx(&0))`;
           REAL_ARITH `--pi < x /\ x <= pi ==> abs(x - pi) < &2 * pi`]);;

let CLOG_II = prove
 (`clog ii = ii * Cx(pi / &2)`,
  MP_TAC(SPEC `ii * Cx(pi / &2)` CLOG_CEXP) THEN
  SIMP_TAC[CEXP_EULER; GSYM CX_COS; GSYM CX_SIN; IM_MUL_II; IM_CX; RE_CX] THEN
  REWRITE_TAC[COS_PI2; SIN_PI2] THEN ANTS_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC;
    REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_MUL_RID]]);;

let CLOG_NEG_II = prove
 (`clog(--ii) = --ii * Cx(pi / &2)`,
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_FIELD `--ii = inv ii`] THEN
  SIMP_TAC[CLOG_INV; RE_II; IM_II; REAL_OF_NUM_EQ; ARITH; CLOG_II] THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG]);;

(* ------------------------------------------------------------------------- *)
(* Relation between square root and exp/log, and hence its derivative.       *)
(* ------------------------------------------------------------------------- *)

let CSQRT_CEXP_CLOG = prove
 (`!z. ~(z = Cx(&0)) ==> csqrt z = cexp(clog(z) / Cx(&2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CSQRT_UNIQUE THEN
  REWRITE_TAC[GSYM CEXP_N; RE_CEXP; IM_CEXP] THEN
  ASM_SIMP_TAC[COMPLEX_DIV_LMUL; CX_INJ; REAL_OF_NUM_EQ; ARITH; CEXP_CLOG] THEN
  SIMP_TAC[REAL_LT_MUL_EQ; REAL_EXP_POS_LT; REAL_LE_MUL_EQ] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_EXP_NZ; IM_DIV_CX] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT2 o MATCH_MP CLOG_WORKS) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [DISJ1_TAC THEN MATCH_MP_TAC COS_POS_PI THEN
    ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN ASM_REWRITE_TAC[COS_PI2; SIN_PI2; REAL_POS]]);;

let CNJ_CSQRT = prove
 (`!z. (Im z = &0 ==> &0 <= Re(z)) ==> cnj(csqrt z) = csqrt(cnj z)`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[CSQRT_0; CNJ_CX] THEN DISCH_TAC THEN
  SUBGOAL_THEN `Im z = &0 ==> &0 < Re(z)` ASSUME_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[COMPLEX_EQ; IM_CX; RE_CX] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_LT_REFL] THEN
    ASM_SIMP_TAC[CSQRT_CEXP_CLOG; CNJ_CEXP; CNJ_CLOG;
                 CNJ_DIV; CNJ_EQ_CX; CNJ_CX]]);;

let HAS_COMPLEX_DERIVATIVE_CSQRT = prove
 (`!z. (Im z = &0 ==> &0 < Re(z))
       ==> (csqrt has_complex_derivative inv(Cx(&2) * csqrt z)) (at z)`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[IM_CX; RE_CX; REAL_LT_REFL] THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\z. cexp(clog(z) / Cx(&2))`; `norm(z:complex)`] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_NZ] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CSQRT_CEXP_CLOG THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC;
    COMPLEX_DIFF_TAC THEN ASM_SIMP_TAC[GSYM CSQRT_CEXP_CLOG] THEN
    UNDISCH_TAC `~(z = Cx(&0))` THEN MP_TAC(SPEC `z:complex` CSQRT) THEN
    CONV_TAC COMPLEX_FIELD]);;

let COMPLEX_DIFFERENTIABLE_AT_CSQRT = prove
 (`!z. (Im z = &0 ==> &0 < Re(z)) ==> csqrt complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CSQRT]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CSQRT = prove
 (`!s z. (Im z = &0 ==> &0 < Re(z))
         ==> csqrt complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CSQRT]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CSQRT)));;

let CONTINUOUS_AT_CSQRT = prove
 (`!z. (Im z = &0 ==> &0 < Re(z)) ==> csqrt continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CSQRT;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CSQRT = prove
 (`!s z. (Im z = &0 ==> &0 < Re(z)) ==> csqrt continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CSQRT]);;

let CONTINUOUS_ON_CSQRT = prove
 (`!s. (!z. z IN s /\ Im z = &0 ==> &0 < Re(z)) ==> csqrt continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CSQRT]);;

let HOLOMORPHIC_ON_CSQRT = prove
 (`!s. (!z. z IN s /\ Im(z) = &0 ==> &0 < Re(z)) ==> csqrt holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CSQRT]);;

let CONTINUOUS_WITHIN_CSQRT_POSREAL = prove
 (`!z. csqrt continuous (at z within {w | real w /\ &0 <= Re(w)})`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `Im z = &0 ==> &0 < Re(z)` THENL
   [ASM_SIMP_TAC[CONTINUOUS_WITHIN_CSQRT]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_IMP; REAL_NOT_LT] THEN
  REWRITE_TAC[REAL_ARITH `x <= &0 <=> x < &0 \/ x = &0`] THEN STRIP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN
    REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    SIMP_TAC[CLOSED_REAL_SET; CLOSED_INTER; IN_INTER; IN_ELIM_THM;
             REWRITE_RULE[real_ge] CLOSED_HALFSPACE_RE_GE] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `z = Cx(&0)` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX]; ALL_TAC] THEN
    REWRITE_TAC[continuous_within] THEN
    REWRITE_TAC[IN_ELIM_THM; IMP_CONJ; FORALL_REAL; RE_CX] THEN
    SIMP_TAC[GSYM CX_SQRT; REAL_LE_REFL] THEN
    SIMP_TAC[dist; GSYM CX_SUB; COMPLEX_NORM_CX; SQRT_0; REAL_SUB_RZERO] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN EXISTS_TAC `(e:real) pow 2` THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `e = sqrt(e pow 2)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[real_abs; SQRT_POS_LE]] THEN
    MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Complex powers.                                                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("cpow",(24,"left"));;

let cpow = new_definition
 `w cpow z = if w = Cx(&0) then Cx(&0)
             else cexp(z * clog w)`;;

let CPOW_0 = prove
 (`!z. Cx(&0) cpow z = Cx(&0)`,
  REWRITE_TAC[cpow]);;

let CPOW_N = prove
 (`!z. z cpow (Cx(&n)) = if z = Cx(&0) then Cx(&0) else z pow n`,
  GEN_TAC THEN REWRITE_TAC[cpow] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CEXP_N; CEXP_CLOG]);;

let CPOW_1 = prove
 (`!z. Cx(&1) cpow z = Cx(&1)`,
  REWRITE_TAC[cpow; CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ; CLOG_1] THEN
  REWRITE_TAC[CEXP_0; COMPLEX_MUL_RZERO]);;

let CPOW_ADD = prove
 (`!w z1 z2. w cpow (z1 + z2) = w cpow z1 * w cpow z2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cpow] THEN
  ASM_CASES_TAC `w = Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[COMPLEX_ADD_RDISTRIB; CEXP_ADD]);;

let CPOW_SUC = prove
 (`!w z. w cpow (z + Cx(&1)) = w * w cpow z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CPOW_ADD; CPOW_N] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[COMPLEX_POW_1; COMPLEX_MUL_SYM]);;

let CPOW_NEG = prove
 (`!w z. w cpow (--z) = inv(w cpow z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cpow] THEN ASM_CASES_TAC `w = Cx(&0)` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_INV_0] THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; CEXP_NEG]);;

let CPOW_SUB = prove
 (`!w z1 z2. w cpow (z1 - z2) = w cpow z1 / w cpow z2`,
  REWRITE_TAC[complex_sub; complex_div; CPOW_ADD; CPOW_NEG]);;

let CEXP_MUL_CPOW = prove
 (`!w z. --pi < Im w /\ Im w <= pi ==> cexp(w * z) = cexp(w) cpow z`,
  SIMP_TAC[cpow; CEXP_NZ; CLOG_CEXP] THEN
  REWRITE_TAC[COMPLEX_MUL_SYM]);;

let CPOW_EQ_0 = prove
 (`!w z. w cpow z = Cx(&0) <=> w = Cx(&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cpow] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CEXP_NZ]);;

let NORM_CPOW_REAL = prove
 (`!w z. real w /\ &0 < Re w ==> norm(w cpow z) = exp(Re z * log(Re w))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o GEN_REWRITE_RULE I [REAL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RE_CX]) THEN
  ASM_SIMP_TAC[cpow; CX_INJ; REAL_LT_IMP_NZ] THEN
  ASM_SIMP_TAC[NORM_CEXP; GSYM CX_LOG; RE_MUL_CX; RE_CX]);;

let CPOW_REAL_REAL = prove
 (`!w z. real w /\ real z /\ &0 < Re w
         ==> w cpow z = Cx(exp(Re z * log(Re w)))`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o GEN_REWRITE_RULE I [REAL])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RE_CX]) THEN
  ASM_SIMP_TAC[cpow; CX_INJ; REAL_LT_IMP_NZ] THEN
  ASM_SIMP_TAC[NORM_CEXP; GSYM CX_LOG; RE_MUL_CX; RE_CX; CX_EXP; CX_MUL]);;

let NORM_CPOW_REAL_MONO = prove
 (`!w z1 z2. real w /\ &1 < Re w
             ==> (norm(w cpow z1) <= norm(w cpow z2) <=> Re(z1) <= Re(z2))`,
  SIMP_TAC[NORM_CPOW_REAL; REAL_ARITH `&1 < x ==> &0 < x`] THEN
  SIMP_TAC[REAL_EXP_MONO_LE; REAL_LE_RMUL_EQ; LOG_POS_LT]);;

let CPOW_MUL_REAL = prove
 (`!x y z. real x /\ real y /\ &0 <= Re x /\ &0 <= Re y
           ==> (x * y) cpow z = x cpow z * y cpow z`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o GEN_REWRITE_RULE I [REAL])) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; CPOW_0] THEN
  ASM_SIMP_TAC[cpow; COMPLEX_ENTIRE; CX_INJ; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[GSYM CEXP_ADD; GSYM COMPLEX_ADD_LDISTRIB] THEN
  ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_ADD; GSYM CX_MUL; REAL_LT_MUL] THEN
  ASM_SIMP_TAC[LOG_MUL]);;

let HAS_COMPLEX_DERIVATIVE_CPOW = prove
 (`!s z. (Im z = &0 ==> &0 < Re z)
         ==> ((\z. z cpow s) has_complex_derivative
              (s * z cpow (s - Cx(&1)))) (at z)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[IM_CX; RE_CX; REAL_LT_REFL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[cpow] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\z. cexp (s * clog z)`; `norm(z:complex)`] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_NZ] THEN CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[dist] THEN
    REWRITE_TAC[COMPLEX_SUB_LZERO; NORM_NEG; REAL_LT_REFL];
    COMPLEX_DIFF_TAC THEN ASM_REWRITE_TAC[CEXP_SUB; COMPLEX_SUB_RDISTRIB] THEN
    ASM_SIMP_TAC[CEXP_CLOG; COMPLEX_MUL_LID] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (GEN `s:complex`
     (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
               (SPEC `s:complex` HAS_COMPLEX_DERIVATIVE_CPOW)))));;

let HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT = prove
 (`!w z. ~(w = Cx(&0))
         ==> ((\z. w cpow z) has_complex_derivative clog(w) * w cpow z) (at z)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[cpow] THEN
  COMPLEX_DIFF_TAC THEN REWRITE_TAC[COMPLEX_MUL_LID]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (GEN `s:complex`
     (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
               (SPEC `s:complex` HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT)))));;

let COMPLEX_DIFFERENTIABLE_CPOW_RIGHT = prove
 (`!w z. (\z. w cpow z) complex_differentiable (at z)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `w = Cx(&0)` THENL
   [ASM_REWRITE_TAC[cpow; COMPLEX_DIFFERENTIABLE_CONST];
    REWRITE_TAC[complex_differentiable] THEN
    ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT]]);;

let HOLOMORPHIC_ON_CPOW_RIGHT = prove
 (`!w f s. f holomorphic_on s
           ==> (\z. w cpow (f z)) holomorphic_on s`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[holomorphic_on; GSYM complex_differentiable] THEN
  ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_CPOW_RIGHT;
               COMPLEX_DIFFERENTIABLE_AT_WITHIN]);;

(* ------------------------------------------------------------------------- *)
(* Product rule.                                                             *)
(* ------------------------------------------------------------------------- *)

let CLOG_MUL = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
           ==> clog(w * z) =
                if Im(clog w + clog z) <= --pi then
                  (clog(w) + clog(z)) + ii * Cx(&2 * pi)
                else if Im(clog w + clog z) > pi then
                  (clog(w) + clog(z)) - ii * Cx(&2 * pi)
                else clog(w) + clog(z)`,
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC CLOG_UNIQUE THEN
  ASM_SIMP_TAC[CEXP_ADD; CEXP_SUB; CEXP_EULER; CEXP_CLOG; CONJ_ASSOC;
               GSYM CX_SIN; GSYM CX_COS; COS_NPI; SIN_NPI] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  TRY(CONJ_TAC THENL [ALL_TAC; CONV_TAC COMPLEX_FIELD]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOG_WORKS)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[IM_ADD; IM_SUB; IM_MUL_II; RE_CX] THEN
  REAL_ARITH_TAC);;

let CLOG_MUL_SIMPLE = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0)) /\
         --pi < Im(clog(w)) + Im(clog(z)) /\
         Im(clog(w)) + Im(clog(z)) <= pi
         ==> clog(w * z) = clog(w) + clog(z)`,
  SIMP_TAC[CLOG_MUL; IM_ADD] THEN REAL_ARITH_TAC);;

let CLOG_MUL_CX = prove
 (`(!x z. &0 < x /\ ~(z = Cx(&0)) ==> clog(Cx x * z) = Cx(log x) + clog z) /\
   (!x z. &0 < x /\ ~(z = Cx(&0)) ==> clog(z * Cx x) = clog z + Cx(log x))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CX_LOG] THEN
  MATCH_MP_TAC CLOG_MUL_SIMPLE THEN
  ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ; GSYM CX_LOG] THEN
  ASM_SIMP_TAC[IM_CX; REAL_ADD_LID; REAL_ADD_RID; CLOG_WORKS]);;

let CLOG_NEG = prove
 (`!z. ~(z = Cx(&0))
       ==> clog(--z) = if Im(z) <= &0 /\ ~(Re(z) < &0 /\ Im(z) = &0)
                       then clog(z) + ii * Cx(pi)
                       else clog(z) - ii * Cx(pi)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SIMPLE_COMPLEX_ARITH `--z = --Cx(&1) * z`) THEN
  ASM_SIMP_TAC[CLOG_MUL; COMPLEX_RING `~(--Cx(&1) = Cx(&0))`] THEN
  REWRITE_TAC[CLOG_NEG_1; IM_ADD; IM_MUL_II; RE_CX] THEN
  ASM_SIMP_TAC[CLOG_WORKS; REAL_ARITH
   `--p < x /\ x <= p ==> ~(p + x <= --p)`] THEN
  REWRITE_TAC[REAL_ARITH `p + x > p <=> &0 < x`] THEN
  ASM_SIMP_TAC[GSYM IM_CLOG_EQ_PI] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `Im z <= &0 <=> ~(&0 < Im z)`] THEN
  ASM_SIMP_TAC[GSYM IM_CLOG_POS_LT] THEN
  ASM_SIMP_TAC[CLOG_WORKS; REAL_ARITH `x <= p ==> (x < p <=> ~(x = p))`] THEN
  REWRITE_TAC[TAUT `~(a /\ ~b) /\ ~b <=> ~a /\ ~b`] THEN
  ASM_CASES_TAC `Im(clog z) = pi` THEN ASM_REWRITE_TAC[PI_POS] THEN
  ASM_CASES_TAC `&0 < Im(clog z)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let CLOG_MUL_II = prove
 (`!z. ~(z = Cx(&0))
       ==> clog(ii * z) = if &0 <= Re(z) \/ Im(z) < &0
                          then clog(z) + ii * Cx(pi / &2)
                          else clog(z) - ii * Cx(&3 * pi / &2)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CLOG_MUL; II_NZ; CLOG_II] THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX] THEN
  ASM_SIMP_TAC[CLOG_WORKS; REAL_ARITH
   `--p < x /\ x <= p ==> ~(p / &2 + x <= --p)`] THEN
  REWRITE_TAC[REAL_ARITH `p / &2 + x > p <=> p / &2 < x`] THEN
  REWRITE_TAC[REAL_ARITH `Im z < &0 <=> ~(&0 <= Im z)`] THEN
  ASM_SIMP_TAC[GSYM RE_CLOG_POS_LE; GSYM IM_CLOG_POS_LE] THEN
  MATCH_MP_TAC(MESON[]
   `(p <=> ~q) /\ x = a /\ y = b
    ==> ((if p then x else y) = (if q then b else a))`) THEN
  CONJ_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC;
    REWRITE_TAC[CX_MUL; CX_DIV] THEN CONV_TAC COMPLEX_RING]);;

(* ------------------------------------------------------------------------- *)
(* Unwinding number gives another version of log-product formula.            *)
(* Note that in this special case the unwinding number is -1, 0 or 1.        *)
(* ------------------------------------------------------------------------- *)

let unwinding = new_definition
 `unwinding(z) = (z - clog(cexp z)) / (Cx(&2 * pi) * ii)`;;

let UNWINDING_2PI = prove
 (`Cx(&2 * pi) * ii * unwinding(z) = z - clog(cexp z)`,
  REWRITE_TAC[unwinding; COMPLEX_MUL_ASSOC] THEN
  MATCH_MP_TAC COMPLEX_DIV_LMUL THEN
  REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; II_NZ] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let CLOG_MUL_UNWINDING = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
           ==> clog(w * z) =
               clog(w) + clog(z) -
               Cx(&2 * pi) * ii * unwinding(clog w + clog z)`,
  REWRITE_TAC[UNWINDING_2PI;
    COMPLEX_RING `w + z - ((w + z) - c) = c:complex`] THEN
  ASM_SIMP_TAC[CEXP_ADD; CEXP_CLOG]);;

(* ------------------------------------------------------------------------- *)
(* Complex arctangent (branch cut gives standard bounds in real case).       *)
(* ------------------------------------------------------------------------- *)

let catn = new_definition
 `catn z = (ii / Cx(&2)) * clog((Cx(&1) - ii * z) / (Cx(&1) + ii * z))`;;

let CATN_0 = prove
 (`catn(Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[catn; COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO; COMPLEX_ADD_RID] THEN
  REWRITE_TAC[COMPLEX_DIV_1; CLOG_1; COMPLEX_MUL_RZERO]);;

let IM_COMPLEX_DIV_LEMMA = prove
 (`!z. Im((Cx(&1) - ii * z) / (Cx(&1) + ii * z)) = &0 <=> Re z = &0`,
  REWRITE_TAC[IM_COMPLEX_DIV_EQ_0] THEN
  REWRITE_TAC[complex_mul;  IM; RE; IM_CNJ; RE_CNJ; RE_CX; IM_CX; RE_II; IM_II;
              RE_SUB; RE_ADD; IM_SUB; IM_ADD] THEN
  REAL_ARITH_TAC);;

let RE_COMPLEX_DIV_LEMMA = prove
 (`!z. &0 < Re((Cx(&1) - ii * z) / (Cx(&1) + ii * z)) <=> norm(z) < &1`,
  REWRITE_TAC[RE_COMPLEX_DIV_GT_0; NORM_LT_SQUARE; REAL_LT_01] THEN
  REWRITE_TAC[GSYM NORM_POW_2; COMPLEX_SQNORM] THEN
  REWRITE_TAC[complex_mul;  IM; RE; IM_CNJ; RE_CNJ; RE_CX; IM_CX; RE_II; IM_II;
              RE_SUB; RE_ADD; IM_SUB; IM_ADD] THEN
  REAL_ARITH_TAC);;

let CTAN_CATN = prove
 (`!z. ~(z pow 2 = --Cx(&1)) ==> ctan(catn z) = z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[catn; ctan; csin; ccos;
              COMPLEX_RING `--i * i / Cx(&2) * z = --(i * i) / Cx(&2) * z`;
              COMPLEX_RING `i * i / Cx(&2) * z =  (i * i) / Cx(&2) * z`] THEN
  REWRITE_TAC[COMPLEX_POW_II_2; GSYM COMPLEX_POW_2] THEN
  REWRITE_TAC[COMPLEX_RING `--Cx(&1) / Cx(&2) * x = --(Cx(&1) / Cx(&2) * x)`;
              CEXP_NEG] THEN
  SUBGOAL_THEN
  `~(cexp(Cx(&1) / Cx(&2) *
          (clog((Cx(&1) - ii * z) / (Cx(&1) + ii * z)))) pow 2 = --Cx(&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CEXP_N; CEXP_SUB; COMPLEX_RING
     `Cx(&2) * Cx(&1) / Cx(&2) * z = z`] THEN
    ASM_SIMP_TAC[CEXP_CLOG; COMPLEX_POW_II_2;
      COMPLEX_FIELD `~(w = Cx(&0)) /\ ~(z = Cx(&0)) ==> ~(w / z = Cx(&0))`;
      COMPLEX_FIELD `~(w = Cx(&0)) ==> (x / w = y <=> x = y * w)`;
      COMPLEX_FIELD
     `ii pow 2 = --Cx(&1) /\ ~(z pow 2 = --Cx(&1))
      ==> ~(Cx(&1) - ii * z = Cx(&0)) /\ ~(Cx(&1) + ii * z = Cx(&0))`] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_RING `-- --Cx (&1) / Cx (&2) = Cx(&1) / Cx(&2)`] THEN
  ASM_SIMP_TAC[CEXP_NZ; COMPLEX_FIELD
    `~(z = Cx(&0)) /\ ~(z pow 2 = --Cx(&1))
     ==> ((inv(z) - z) / (Cx(&2) * ii)) / ((inv(z) + z) / Cx(&2)) =
         inv ii * ((Cx(&1) - z pow 2) / (Cx(&1) + z pow 2))`] THEN
  ASM_SIMP_TAC[GSYM CEXP_N; CEXP_SUB;
               COMPLEX_RING `Cx(&2) * Cx(&1) / Cx(&2) * z = z`] THEN
  ASM_SIMP_TAC[CEXP_CLOG; COMPLEX_FIELD
     `~(z pow 2 = --Cx(&1))
      ==> ~((Cx(&1) - ii * z) / (Cx(&1) + ii * z) = Cx(&0))`] THEN
  UNDISCH_TAC `~(z pow 2 = --Cx(&1))` THEN CONV_TAC COMPLEX_FIELD);;

let CATN_CTAN = prove
 (`!z. abs(Re z) < pi / &2 ==> catn(ctan z) = z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[catn; ctan; csin; ccos] THEN
  ASM_SIMP_TAC[COMPLEX_FIELD
   `ii * (a / (Cx(&2) * ii)) / (b / Cx(&2)) = a / b`] THEN
  SIMP_TAC[COMPLEX_FIELD
   `ii / Cx(&2) * x = y <=> x = Cx(&2) * --(ii * y)`] THEN
  SUBGOAL_THEN `~(cexp(ii * z) pow 2 = --Cx(&1))` ASSUME_TAC THENL
   [SUBGOAL_THEN `--Cx(&1) = cexp(ii * Cx pi)` SUBST1_TAC THENL
     [REWRITE_TAC[CEXP_EULER; GSYM CX_SIN; GSYM CX_COS; SIN_PI; COS_PI] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CEXP_N; CEXP_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `Im`) THEN
    REWRITE_TAC[IM_MUL_CX; IM_MUL_II; IM_ADD; RE_CX; IM_II; REAL_MUL_RID] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(z) < p / &2 /\ (w = &0 \/ abs(w) >= &2 * p)
      ==> ~(&2 * z = p + w)`) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_PI; REAL_ABS_NUM] THEN
    SIMP_TAC[real_ge; REAL_MUL_ASSOC; REAL_LE_RMUL_EQ; PI_POS] THEN
    REWRITE_TAC[REAL_ENTIRE; PI_NZ] THEN
    MP_TAC(SPEC `n:real` REAL_ABS_INTEGER_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[CEXP_NEG; CEXP_NZ; COMPLEX_MUL_LNEG; COMPLEX_FIELD
     `~(w = Cx(&0)) /\ ~(w pow 2 = --Cx(&1))
      ==> (Cx(&1) - (w - inv w) / (w + inv w)) /
          (Cx(&1) + (w - inv w) / (w + inv w)) =
           inv(w) pow 2`] THEN
    REWRITE_TAC[GSYM CEXP_N; GSYM CEXP_NEG] THEN
    MATCH_MP_TAC CLOG_CEXP THEN REWRITE_TAC[IM_MUL_CX; IM_NEG; IM_MUL_II] THEN
    ASM_REAL_ARITH_TAC]);;

let RE_CATN_BOUNDS = prove
 (`!z. (Re z = &0 ==> abs(Im z) < &1) ==> abs(Re(catn z)) < pi / &2`,
  REWRITE_TAC[catn; complex_div; GSYM CX_INV; GSYM COMPLEX_MUL_ASSOC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[RE_MUL_II; IM_MUL_CX] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x < p ==> abs(--(inv(&2) * x)) < p / &2`) THEN
  MATCH_MP_TAC(REAL_ARITH `(--p < x /\ x <= p) /\ ~(x = p) ==> abs x < p`) THEN
  SUBGOAL_THEN `~(z = ii) /\ ~(z = --ii)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN SUBST1_TAC th) THEN
    REWRITE_TAC[RE_II; IM_II; RE_NEG; IM_NEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM complex_div] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `~((Cx(&1) - ii * z) / (Cx(&1) + ii * z) = Cx(&0))`
     (fun th -> MESON_TAC[th; CLOG_WORKS]) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `clog((Cx(&1) - ii * z) / (Cx(&1) + ii * z))` EULER) THEN
  ASM_REWRITE_TAC[SIN_PI; COS_PI; CX_NEG] THEN
  REWRITE_TAC[COMPLEX_RING
   `x = y * (--Cx(&1) + z * Cx(&0)) <=> x + y = Cx(&0)`] THEN
  REWRITE_TAC[CX_EXP] THEN
  ASM_SIMP_TAC[CEXP_CLOG; COMPLEX_FIELD
     `~(z = ii) /\ ~(z = --ii)
      ==> ~((Cx(&1) - ii * z) / (Cx(&1) + ii * z) = Cx(&0))`] THEN
  REWRITE_TAC[GSYM CX_EXP] THEN DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN
  REWRITE_TAC[IM_ADD; IM_CX; REAL_ADD_RID; IM_COMPLEX_DIV_LEMMA] THEN
  DISCH_TAC THEN UNDISCH_TAC `Re z = &0 ==> abs (Im z) < &1` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ii * z = --Cx(Im z)` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_EQ; RE_NEG; IM_NEG; RE_MUL_II; IM_MUL_II;
                    RE_CX; IM_CX; REAL_NEG_0];
    ALL_TAC] THEN
  UNDISCH_TAC
   `Im(clog((Cx(&1) - --Cx(Im z)) / (Cx(&1) + --Cx(Im z)))) = pi` THEN
  REWRITE_TAC[COMPLEX_SUB_RNEG; GSYM complex_sub] THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_SUB; GSYM CX_DIV] THEN
  SUBGOAL_THEN `&0 < (&1 + Im z) / (&1 - Im z)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[GSYM CX_LOG; IM_CX; PI_NZ]]);;

let HAS_COMPLEX_DERIVATIVE_CATN = prove
 (`!z. (Re z = &0 ==> abs(Im z) < &1)
       ==> (catn has_complex_derivative inv(Cx(&1) + z pow 2)) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(z = ii) /\ ~(z = --ii)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN SUBST1_TAC th) THEN
    REWRITE_TAC[RE_II; IM_II; RE_NEG; IM_NEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[catn] THEN COMPLEX_DIFF_TAC THEN
  REWRITE_TAC[RE_SUB; RE_ADD; IM_SUB; IM_ADD;
              RE_CX; RE_MUL_II; IM_CX; IM_MUL_II] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[IM_COMPLEX_DIV_LEMMA; RE_COMPLEX_DIV_LEMMA] THEN
    SIMP_TAC[complex_norm] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[REAL_ADD_LID; POW_2_SQRT_ABS];
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD]);;

let COMPLEX_DIFFERENTIABLE_AT_CATN = prove
 (`!z. (Re z = &0 ==> abs(Im z) < &1) ==> catn complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CATN]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CATN = prove
 (`!s z. (Re z = &0 ==> abs(Im z) < &1)
         ==> catn complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CATN]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CATN)));;

let CONTINUOUS_AT_CATN = prove
 (`!z. (Re z = &0 ==> abs(Im z) < &1) ==> catn continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CATN;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CATN = prove
 (`!s z. (Re z = &0 ==> abs(Im z) < &1) ==> catn continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CATN]);;

let CONTINUOUS_ON_CATN = prove
 (`!s. (!z. z IN s /\ Re z = &0 ==> abs(Im z) < &1) ==> catn continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CATN]);;

let HOLOMORPHIC_ON_CATN = prove
 (`!s. (!z. z IN s /\ Re z = &0 ==> abs(Im z) < &1) ==> catn holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CATN]);;

(* ------------------------------------------------------------------------- *)
(* Real arctangent.                                                          *)
(* ------------------------------------------------------------------------- *)

let atn = new_definition
 `atn(x) = Re(catn(Cx x))`;;

let CX_ATN = prove
 (`!x. Cx(atn x) = catn(Cx x)`,
  GEN_TAC THEN REWRITE_TAC[atn; catn; GSYM REAL; real] THEN
  REWRITE_TAC[complex_div; IM_MUL_II; GSYM CX_INV; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[RE_MUL_CX; REAL_ARITH `inv(&2) * x = &0 <=> x = &0`] THEN
  MATCH_MP_TAC NORM_CEXP_IMAGINARY THEN
  SUBGOAL_THEN `~(Cx(&1) - ii * Cx(x) = Cx(&0)) /\
                ~(Cx(&1) + ii * Cx(x) = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN
    REWRITE_TAC[RE_ADD; RE_SUB; RE_MUL_II; IM_CX; RE_CX] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CEXP_SUB; CEXP_CLOG; COMPLEX_FIELD
   `~(a = Cx(&0)) /\ ~(b = Cx(&0)) ==> ~(a * inv b = Cx(&0))`] THEN
  REWRITE_TAC[GSYM complex_div; COMPLEX_NORM_DIV] THEN
  MATCH_MP_TAC(REAL_FIELD `~(b = &0) /\ a = b ==> a / b = &1`) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_ZERO] THEN
  MATCH_MP_TAC(MESON[COMPLEX_NORM_CNJ] `cnj a = b ==> norm a = norm b`) THEN
  REWRITE_TAC[CNJ_SUB; CNJ_MUL; CNJ_MUL; CNJ_II; CNJ_CX] THEN
  CONV_TAC COMPLEX_RING);;

let ATN_TAN = prove
 (`!y. tan(atn y) = y`,
  GEN_TAC THEN REWRITE_TAC[tan_def; atn] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `Re(ctan(catn(Cx y)))` THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM CX_ATN; RE_CX]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM RE_CX] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CTAN_CATN THEN MATCH_MP_TAC(COMPLEX_RING
   `~(z = ii) /\ ~(z = --ii) ==> ~(z pow 2 = --Cx(&1))`) THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN
  REWRITE_TAC[IM_II; IM_CX; IM_NEG] THEN REAL_ARITH_TAC);;

let ATN_BOUND = prove
 (`!y. abs(atn y) < pi / &2`,
  GEN_TAC THEN REWRITE_TAC[atn] THEN MATCH_MP_TAC RE_CATN_BOUNDS THEN
  REWRITE_TAC[IM_CX] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let ATN_BOUNDS = prove
 (`!y. --(pi / &2) < atn(y) /\ atn(y) < (pi / &2)`,
  MP_TAC ATN_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let TAN_ATN = prove
 (`!x. --(pi / &2) < x /\ x < pi / &2 ==> atn(tan(x)) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tan_def; atn] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `Re(catn(ctan(Cx x)))` THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM CX_TAN; RE_CX]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM RE_CX] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CATN_CTAN THEN REWRITE_TAC[RE_CX] THEN
  ASM_REAL_ARITH_TAC);;

let ATN_0 = prove
 (`atn(&0) = &0`,
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM TAN_0] THEN
  MATCH_MP_TAC TAN_ATN THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let ATN_1 = prove
 (`atn(&1) = pi / &4`,
  MP_TAC(AP_TERM `atn` TAN_PI4) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC TAN_ATN THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let ATN_NEG = prove
 (`!x. atn(--x) = --(atn x)`,
  GEN_TAC THEN MP_TAC(SPEC `atn(x)` TAN_NEG) THEN REWRITE_TAC[ATN_TAN] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC TAN_ATN THEN
  MP_TAC(SPEC `x:real` ATN_BOUNDS) THEN REAL_ARITH_TAC);;

let ATN_MONO_LT = prove
 (`!x y. x < y ==> atn(x) < atn(y)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [GSYM ATN_TAN] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LT] THEN
  SIMP_TAC[TAN_MONO_LE; ATN_BOUNDS]);;

let ATN_MONO_LT_EQ = prove
 (`!x y. atn(x) < atn(y) <=> x < y`,
  MESON_TAC[REAL_NOT_LE; REAL_LE_LT; ATN_MONO_LT]);;

let ATN_MONO_LE_EQ = prove
 (`!x y. atn(x) <= atn(y) <=> x <= y`,
  REWRITE_TAC[GSYM REAL_NOT_LT; ATN_MONO_LT_EQ]);;

let ATN_INJ = prove
 (`!x y. (atn x = atn y) <=> (x = y)`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; ATN_MONO_LE_EQ]);;

let ATN_POS_LT = prove
 (`&0 < atn(x) <=> &0 < x`,
  MESON_TAC[ATN_0; ATN_MONO_LT_EQ]);;

let ATN_POS_LE = prove
 (`&0 <= atn(x) <=> &0 <= x`,
  MESON_TAC[ATN_0; ATN_MONO_LE_EQ]);;

let ATN_LT_PI4_POS = prove
 (`!x. x < &1 ==> atn(x) < pi / &4`,
  SIMP_TAC[GSYM ATN_1; ATN_MONO_LT]);;

let ATN_LT_PI4_NEG = prove
 (`!x. --(&1) < x ==> --(pi / &4) < atn(x)`,
  SIMP_TAC[GSYM ATN_1; GSYM ATN_NEG; ATN_MONO_LT]);;

let ATN_LT_PI4 = prove
 (`!x. abs(x) < &1 ==> abs(atn x) < pi / &4`,
  GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `(&0 < x ==> &0 < y) /\
    (x < &0 ==> y < &0) /\
    ((x = &0) ==> (y = &0)) /\
    (x < a ==> y < b) /\
    (--a < x ==> --b < y)
    ==> abs(x) < a ==> abs(y) < b`) THEN
  SIMP_TAC[ATN_LT_PI4_POS; ATN_LT_PI4_NEG; ATN_0] THEN CONJ_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM ATN_0] THEN
  SIMP_TAC[ATN_MONO_LT]);;

let ATN_LE_PI4 = prove
 (`!x. abs(x) <= &1 ==> abs(atn x) <= pi / &4`,
  REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ATN_LT_PI4] THEN DISJ2_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
    (REAL_ARITH `(abs(x) = a) ==> (x = a) \/ (x = --a)`)) THEN
  ASM_REWRITE_TAC[ATN_1; ATN_NEG] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_NEG] THEN
  SIMP_TAC[real_abs; REAL_LT_IMP_LE; PI_POS]);;

let COS_ATN_NZ = prove
 (`!x. ~(cos(atn(x)) = &0)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
  MATCH_MP_TAC COS_POS_PI THEN REWRITE_TAC[ATN_BOUNDS]);;

let TAN_SEC = prove
 (`!x. ~(cos(x) = &0) ==> (&1 + (tan(x) pow 2) = inv(cos x) pow 2)`,
  MP_TAC SIN_CIRCLE THEN MATCH_MP_TAC MONO_FORALL THEN REWRITE_TAC[tan] THEN
  CONV_TAC REAL_FIELD);;

let COS_ATN = prove
 (`!x. cos(atn x) = &1 / sqrt(&1 + x pow 2)`,
  SIMP_TAC[COS_TAN; ATN_BOUND; ATN_TAN]);;

let SIN_ATN = prove
 (`!x. sin(atn x) = x / sqrt(&1 + x pow 2)`,
  SIMP_TAC[SIN_TAN; ATN_BOUND; ATN_TAN]);;

let ATN_ABS = prove
 (`!x. atn(abs x) = abs(atn x)`,
  GEN_TAC THEN REWRITE_TAC[real_abs; ATN_POS_LE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ATN_NEG]);;

let ATN_ADD = prove
 (`!x y. abs(atn x + atn y) < pi / &2
         ==> atn(x) + atn(y) = atn((x + y) / (&1 - x * y))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `atn((tan(atn x) + tan(atn y)) /
                          (&1 - tan(atn x) * tan(atn y)))` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[ATN_TAN]] THEN
  W(MP_TAC o PART_MATCH (rand o rand) TAN_ADD o rand o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COS_ATN_NZ] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MATCH_MP_TAC COS_POS_PI THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC TAN_ATN THEN ASM_REAL_ARITH_TAC]);;

let ATN_INV = prove
 (`!x. &0 < x ==> atn(inv x) = pi / &2 - atn x`,
  REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS `atn(inv(tan(atn x)))` THEN
  CONJ_TAC THENL [REWRITE_TAC[ATN_TAN]; REWRITE_TAC[GSYM TAN_COT]] THEN
  MATCH_MP_TAC TAN_ATN THEN REWRITE_TAC[ATN_BOUNDS; REAL_ARITH
   `--(p / &2) < p / &2 - x /\ p / &2 - x < p / &2 <=> &0 < x /\ x < p`] THEN
  ASM_REWRITE_TAC[ATN_POS_LT] THEN MP_TAC(SPEC `x:real` ATN_BOUNDS) THEN
  ASM_REAL_ARITH_TAC);;

let ATN_ADD_SMALL = prove
 (`!x y. abs(x * y) < &1
         ==> (atn(x) + atn(y) = atn((x + y) / (&1 - x * y)))`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`x = &0`; `y = &0`] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_RZERO;
                  REAL_DIV_1; REAL_ADD_LID; REAL_ADD_RID; ATN_0] THEN
  MATCH_MP_TAC ATN_ADD THEN MATCH_MP_TAC(REAL_ARITH
   `abs(x) < p - abs(y) \/ abs(y) < p - abs(x) ==> abs(x + y) < p`) THEN
  REWRITE_TAC[GSYM ATN_ABS] THEN
  ASM_SIMP_TAC[GSYM ATN_INV; REAL_ARITH `~(x = &0) ==> &0 < abs x`;
        ATN_MONO_LT_EQ; REAL_ARITH `inv x = &1 / x`; REAL_LT_RDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Machin-like formulas for pi.                                              *)
(* ------------------------------------------------------------------------- *)

let [MACHIN; MACHIN_EULER; MACHIN_GAUSS] = (CONJUNCTS o prove)
 (`(&4 * atn(&1 / &5) - atn(&1 / &239) = pi / &4) /\
   (&5 * atn(&1 / &7) + &2 * atn(&3 / &79) = pi / &4) /\
   (&12 * atn(&1 / &18) + &8 * atn(&1 / &57) - &5 * atn(&1 / &239) = pi / &4)`,
  REPEAT CONJ_TAC THEN CONV_TAC(ONCE_DEPTH_CONV(fun tm ->
    if is_binop `( * ):real->real->real` tm
    then LAND_CONV(RAND_CONV(TOP_DEPTH_CONV num_CONV)) tm
    else failwith "")) THEN
  REWRITE_TAC[real_sub; GSYM REAL_MUL_RNEG; GSYM ATN_NEG] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_LID] THEN
  CONV_TAC(DEPTH_CONV (fun tm ->
    let th1 = PART_MATCH (lhand o rand) ATN_ADD_SMALL tm in
    let th2 = MP th1 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th1)))) in
    CONV_RULE(RAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) th2)) THEN
  REWRITE_TAC[ATN_1]);;

(* ------------------------------------------------------------------------- *)
(* Some bound theorems where a bit of simple calculus is handy.              *)
(* ------------------------------------------------------------------------- *)

let ATN_ABS_LE_X = prove
 (`!x. abs(atn x) <= abs x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`catn`; `\z. inv(Cx(&1) + z pow 2)`; `real`; `&1`]
      COMPLEX_MVT) THEN
  REWRITE_TAC[CONVEX_REAL; IN] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[real] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CATN THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      GEN_TAC THEN REWRITE_TAC[REAL] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM CX_POW; GSYM CX_ADD; GSYM CX_INV; COMPLEX_NORM_CX] THEN
      REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
      MP_TAC(SPEC `Re z` REAL_LE_SQUARE) THEN REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPECL [`Cx(&0)`; `Cx(x)`]) THEN
    REWRITE_TAC[GSYM CX_ATN; COMPLEX_SUB_RZERO; REAL_CX; ATN_0] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_MUL_LID]]);;

let ATN_LE_X = prove
 (`!x. &0 <= x ==> atn(x) <= x`,
  MP_TAC ATN_ABS_LE_X THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let TAN_ABS_GE_X = prove
 (`!x. abs(x) < pi / &2 ==> abs(x) <= abs(tan x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(atn(tan x))` THEN REWRITE_TAC[ATN_ABS_LE_X] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC TAN_ATN THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Probably not very useful, but for compatibility with old analysis theory. *)
(* ------------------------------------------------------------------------- *)

let TAN_TOTAL = prove
 (`!y. ?!x. --(pi / &2) < x /\ x < (pi / &2) /\ tan(x) = y`,
  MESON_TAC[TAN_ATN; ATN_TAN; ATN_BOUNDS]);;

let TAN_TOTAL_POS = prove
 (`!y. &0 <= y ==> ?x. &0 <= x /\ x < pi / &2 /\ tan(x) = y`,
  MESON_TAC[ATN_TAN; ATN_BOUNDS; ATN_POS_LE]);;

let TAN_TOTAL_LEMMA = prove
 (`!y. &0 < y ==> ?x. &0 < x /\ x < pi / &2 /\ y < tan(x)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `atn(y + &1)` THEN
  REWRITE_TAC[ATN_TAN; ATN_BOUNDS; ATN_POS_LT] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some slightly ad hoc lemmas useful here.                                  *)
(* ------------------------------------------------------------------------- *)

let RE_POW_2 = prove
 (`Re(z pow 2) = Re(z) pow 2 - Im(z) pow 2`,
  REWRITE_TAC[COMPLEX_POW_2; complex_mul; RE] THEN REAL_ARITH_TAC);;

let IM_POW_2 = prove
 (`Im(z pow 2) = &2 * Re(z) * Im(z)`,
  REWRITE_TAC[COMPLEX_POW_2; complex_mul; IM] THEN REAL_ARITH_TAC);;

let ABS_SQUARE_LT_1 = prove
 (`!x. x pow 2 < &1 <=> abs(x) < &1`,
  ONCE_REWRITE_TAC[GSYM REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_LT_SQUARE_ABS] THEN REAL_ARITH_TAC);;

let ABS_SQUARE_LE_1 = prove
 (`!x. x pow 2 <= &1 <=> abs(x) <= &1`,
  ONCE_REWRITE_TAC[GSYM REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_LT_SQUARE_ABS; GSYM REAL_NOT_LT] THEN REAL_ARITH_TAC);;

let ABS_SQUARE_EQ_1 = prove
 (`!x. x pow 2 = &1 <=> abs(x) = &1`,
  REWRITE_TAC[REAL_RING `x pow 2 = &1 <=> x = &1 \/ x = -- &1`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Inverse sine.                                                             *)
(* ------------------------------------------------------------------------- *)

let casn = new_definition
 `casn z = --ii * clog(ii * z + csqrt(Cx(&1) - z pow 2))`;;

let CASN_BODY_LEMMA = prove
 (`!z. ~(ii * z + csqrt(Cx(&1) - z pow 2) = Cx(&0))`,
  GEN_TAC THEN MP_TAC(SPEC `Cx(&1) - z pow 2` CSQRT) THEN
  CONV_TAC COMPLEX_FIELD);;

let CSIN_CASN = prove
 (`!z. csin(casn z) = z`,
  GEN_TAC THEN REWRITE_TAC[csin; casn; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC; COMPLEX_NEG_NEG] THEN
  REWRITE_TAC[COMPLEX_POW_II_2; GSYM COMPLEX_POW_2] THEN
  REWRITE_TAC[COMPLEX_NEG_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[CEXP_NEG] THEN
  ASM_SIMP_TAC[CASN_BODY_LEMMA; CEXP_CLOG; COMPLEX_FIELD
     `~(z = Cx(&0))
      ==> ((z - inv z) / (Cx(&2) * ii) = c <=>
           z pow 2 - Cx(&1) = Cx(&2) * ii * c * z)`] THEN
  MP_TAC(SPEC `Cx(&1) - z pow 2` CSQRT) THEN CONV_TAC COMPLEX_FIELD);;

let CASN_CSIN = prove
 (`!z. abs(Re z) < pi / &2 \/ (abs(Re z) = pi / &2 /\ Im z = &0)
       ==> casn(csin z) = z`,
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[csin; casn; COMPLEX_MUL_LNEG; CEXP_NEG] THEN
  SIMP_TAC[CEXP_NZ; COMPLEX_FIELD
    `~(z = Cx(&0))
     ==> Cx(&1) - ((z - inv z) / (Cx(&2) * ii)) pow 2 =
         ((z + inv z) / Cx(&2)) pow 2`] THEN
  SUBGOAL_THEN
   `csqrt(((cexp(ii * z) + inv(cexp(ii * z))) / Cx(&2)) pow 2) =
    (cexp(ii * z) + inv(cexp(ii * z))) / Cx(&2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC POW_2_CSQRT THEN REWRITE_TAC[GSYM CEXP_NEG] THEN
    REWRITE_TAC[complex_div; GSYM CX_INV; RE_MUL_CX; IM_MUL_CX] THEN
    REWRITE_TAC[REAL_ARITH
     `&0 < r * inv(&2) \/ r * inv(&2) = &0 /\ &0 <= i * inv(&2) <=>
      &0 < r \/ r = &0 /\ &0 <= i`] THEN
    REWRITE_TAC[RE_ADD; IM_ADD; RE_CEXP; IM_CEXP] THEN
    REWRITE_TAC[RE_MUL_II; RE_NEG; IM_MUL_II; IM_NEG] THEN
    REWRITE_TAC[SIN_NEG; COS_NEG; REAL_NEG_NEG] THEN
    REWRITE_TAC[REAL_MUL_RNEG; GSYM real_sub] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_ADD; REAL_EXP_POS_LT] THEN
      MATCH_MP_TAC COS_POS_PI THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
      DISJ2_TAC THEN ASM_REWRITE_TAC[SIN_PI2; COS_PI2] THEN
      REWRITE_TAC[REAL_EXP_NEG; REAL_EXP_0; REAL_INV_1; REAL_SUB_REFL] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL; REAL_ENTIRE] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (REAL_ARITH
       `abs(x) = p ==> x = p \/ x = --p`)) THEN
      REWRITE_TAC[COS_PI2; COS_NEG] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SIMP_TAC[COMPLEX_FIELD
   `ii * (a - b) / (Cx(&2) * ii) + (a + b) / Cx(&2) = a`] THEN
  SIMP_TAC[COMPLEX_FIELD `--(ii * w) = z <=> w = ii * z`] THEN
  MATCH_MP_TAC CLOG_CEXP THEN REWRITE_TAC[IM_MUL_II] THEN
  MP_TAC PI_POS THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let CASN_UNIQUE = prove
 (`!w z. csin(z) = w /\
         (abs(Re z) < pi / &2 \/ (abs(Re z) = pi / &2 /\ Im z = &0))
         ==> casn w = z`,
  MESON_TAC[CASN_CSIN]);;

let CASN_0 = prove
 (`casn(Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[casn; COMPLEX_MUL_RZERO; COMPLEX_ADD_LID; COMPLEX_POW_2;
              COMPLEX_SUB_RZERO; CSQRT_1; CLOG_1; COMPLEX_MUL_RZERO]);;

let CASN_1 = prove
 (`casn(Cx(&1)) = Cx(pi / &2)`,
  REWRITE_TAC[casn; GSYM CX_POW; GSYM CX_SUB] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[CSQRT_0; COMPLEX_MUL_RID; COMPLEX_ADD_RID] THEN
  REWRITE_TAC[CLOG_II] THEN CONV_TAC COMPLEX_RING);;

let CASN_NEG_1 = prove
 (`casn(--Cx(&1)) = --Cx(pi / &2)`,
  REWRITE_TAC[casn; GSYM CX_NEG; GSYM CX_POW; GSYM CX_SUB] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[CSQRT_0; COMPLEX_MUL_RID; COMPLEX_ADD_RID] THEN
  REWRITE_TAC[CX_NEG; COMPLEX_MUL_RID; COMPLEX_MUL_RNEG] THEN
  REWRITE_TAC[CLOG_NEG_II] THEN CONV_TAC COMPLEX_RING);;

let HAS_COMPLEX_DERIVATIVE_CASN = prove
 (`!z. (Im z = &0 ==> abs(Re z) < &1)
       ==> (casn has_complex_derivative inv(ccos(casn z))) (at z)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC THEN
  EXISTS_TAC `csin` THEN
  REWRITE_TAC[CSIN_CASN; HAS_COMPLEX_DERIVATIVE_CSIN; CONTINUOUS_AT_CSIN] THEN
  EXISTS_TAC `ball(z:complex,&1)` THEN
  REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP (COMPLEX_RING
     `ccos z = Cx(&0) ==> csin(z) pow 2 + ccos(z) pow 2 = Cx(&1)
                          ==> csin(z) pow 2 = Cx(&1)`)) THEN
    REWRITE_TAC[CSIN_CASN; CSIN_CIRCLE] THEN
    REWRITE_TAC[COMPLEX_RING
     `z pow 2 = Cx(&1) <=> z = Cx(&1) \/ z = --Cx(&1)`] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[RE_CX; IM_CX; RE_NEG; IM_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[casn] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ADD THEN
    SIMP_TAC[CONTINUOUS_COMPLEX_MUL; CONTINUOUS_CONST; CONTINUOUS_AT_ID] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_COMPLEX_POW; CONTINUOUS_SUB;
             CONTINUOUS_CONST; CONTINUOUS_AT_ID] THEN
    MATCH_MP_TAC CONTINUOUS_AT_CSQRT THEN
    REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX; RE_POW_2; IM_POW_2] THEN
    REWRITE_TAC[REAL_RING `&0 - &2 * x * y = &0 <=> x = &0 \/ y = &0`] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_SUB_RZERO;
                    REAL_ARITH `&1 - (&0 - x) = &1 + x`] THEN
    ASM_SIMP_TAC[REAL_LE_SQUARE; REAL_ARITH `&0 <= x ==> &0 < &1 + x`] THEN
    REWRITE_TAC[REAL_ARITH `&0 < &1 - x * x <=> x pow 2 < &1 pow 2`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_ABS_NUM; ARITH];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_CLOG THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_ADD; RE_MUL_II] THEN
  ASM_CASES_TAC `Im z = &0` THENL
   [DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[csqrt] THEN
    ASM_REWRITE_TAC[IM_SUB; RE_SUB; IM_CX; RE_CX; IM_POW_2; RE_POW_2;
                    REAL_MUL_RZERO; REAL_SUB_REFL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&0 <= &1 - (z pow 2 - &0) <=> z pow 2 <= &1 pow 2`;
                GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_NUM; RE; REAL_ADD_LID] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN
    REWRITE_TAC[REAL_ARITH `&0 < &1 - (z pow 2 - &0) <=> z pow 2 < &1 pow 2`;
                GSYM REAL_LT_SQUARE_ABS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[csqrt; IM_SUB; RE_SUB; IM_CX; RE_CX; IM_POW_2; RE_POW_2] THEN
  REWRITE_TAC[REAL_RING `&0 - &2 * x * y = &0 <=> x = &0 \/ y = &0`] THEN
  ASM_CASES_TAC `Re z = &0` THEN ASM_REWRITE_TAC[RE; IM] THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&1 - (&0 - x) = &1 + x`] THEN
    SIMP_TAC[REAL_POW_2; REAL_LE_ADD; REAL_LE_SQUARE; REAL_POS] THEN
    REWRITE_TAC[RE; IM; REAL_ADD_LID; REAL_ARITH `&0 < --x + y <=> x < y`] THEN
    MATCH_MP_TAC REAL_LT_RSQRT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_ARITH `&0 < --x + y <=> x < y`] THEN
  MATCH_MP_TAC REAL_LT_RSQRT THEN
  REWRITE_TAC[REAL_POW_2; REAL_ARITH
   `a < (n + &1 - (b - a)) / &2 <=> (a + b) - &1 < n`] THEN
  REWRITE_TAC[complex_norm] THEN MATCH_MP_TAC REAL_LT_RSQRT THEN
  REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX; RE_POW_2; IM_POW_2] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE I [GSYM REAL_LT_SQUARE])) THEN
  REAL_ARITH_TAC);;

let COMPLEX_DIFFERENTIABLE_AT_CASN = prove
 (`!z. (Im z = &0 ==> abs(Re z) < &1) ==> casn complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CASN]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CASN = prove
 (`!s z. (Im z = &0 ==> abs(Re z) < &1)
         ==> casn complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CASN]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CASN)));;

let CONTINUOUS_AT_CASN = prove
 (`!z. (Im z = &0 ==> abs(Re z) < &1) ==> casn continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CASN;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CASN = prove
 (`!s z. (Im z = &0 ==> abs(Re z) < &1) ==> casn continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CASN]);;

let CONTINUOUS_ON_CASN = prove
 (`!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> casn continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CASN]);;

let HOLOMORPHIC_ON_CASN = prove
 (`!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> casn holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CASN]);;

(* ------------------------------------------------------------------------- *)
(* Inverse cosine.                                                           *)
(* ------------------------------------------------------------------------- *)

let cacs = new_definition
 `cacs z = --ii * clog(z + ii * csqrt(Cx(&1) - z pow 2))`;;

let CACS_BODY_LEMMA = prove
 (`!z. ~(z + ii * csqrt(Cx(&1) - z pow 2) = Cx(&0))`,
  GEN_TAC THEN MP_TAC(SPEC `Cx(&1) - z pow 2` CSQRT) THEN
  CONV_TAC COMPLEX_FIELD);;

let CCOS_CACS = prove
 (`!z. ccos(cacs z) = z`,
  GEN_TAC THEN REWRITE_TAC[ccos; cacs; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC; COMPLEX_NEG_NEG] THEN
  REWRITE_TAC[COMPLEX_POW_II_2; GSYM COMPLEX_POW_2] THEN
  REWRITE_TAC[COMPLEX_NEG_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[CEXP_NEG] THEN
  ASM_SIMP_TAC[CACS_BODY_LEMMA; CEXP_CLOG; COMPLEX_POW_II_2; COMPLEX_FIELD
     `~(z = Cx(&0))
      ==> ((z + inv z) / Cx(&2) = c <=>
           z pow 2 + Cx(&1) = Cx(&2) * c * z)`] THEN
  MP_TAC(SPEC `Cx(&1) - z pow 2` CSQRT) THEN CONV_TAC COMPLEX_FIELD);;

let CACS_CCOS = prove
 (`!z. &0 < Re z /\ Re z < pi \/
       Re(z) = &0 /\ &0 <= Im(z) \/
       Re(z) = pi /\ Im(z) <= &0
       ==> cacs(ccos z) = z`,
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[ccos; cacs; COMPLEX_MUL_LNEG; CEXP_NEG] THEN
  SIMP_TAC[CEXP_NZ; COMPLEX_FIELD
    `~(z = Cx(&0))
     ==> Cx(&1) - ((z + inv z) / Cx(&2)) pow 2 =
         --(((z - inv z) / Cx(&2)) pow 2)`] THEN
  SUBGOAL_THEN
   `csqrt(--(((cexp(ii * z) - inv(cexp(ii * z))) / Cx(&2)) pow 2)) =
    --ii * (cexp(ii * z) - inv(cexp(ii * z))) / Cx(&2)`
  SUBST1_TAC THENL
   [SIMP_TAC[COMPLEX_FIELD `--(x pow 2) = (--ii * x) pow 2`] THEN
    MATCH_MP_TAC POW_2_CSQRT THEN REWRITE_TAC[GSYM CEXP_NEG] THEN
    REWRITE_TAC[complex_div; GSYM CX_INV; RE_MUL_CX; IM_MUL_CX; RE_NEG; IM_NEG;
                COMPLEX_MUL_LNEG; RE_MUL_II; IM_MUL_II; RE_SUB; IM_SUB] THEN
    REWRITE_TAC[REAL_NEG_NEG; REAL_NEG_EQ_0] THEN
    REWRITE_TAC[REAL_ARITH
     `&0 < r * inv(&2) \/ r * inv(&2) = &0 /\ &0 <= --(i * inv(&2)) <=>
      &0 < r \/ r = &0 /\ &0 <= --i`] THEN
    REWRITE_TAC[RE_ADD; IM_ADD; RE_CEXP; IM_CEXP] THEN
    REWRITE_TAC[RE_MUL_II; RE_NEG; IM_MUL_II; IM_NEG] THEN
    REWRITE_TAC[SIN_NEG; COS_NEG; REAL_NEG_NEG] THEN
    REWRITE_TAC[REAL_MUL_RNEG; GSYM real_sub; REAL_SUB_RNEG; REAL_NEG_SUB] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    ASM_SIMP_TAC[REAL_LT_ADD; REAL_EXP_POS_LT; REAL_LT_MUL_EQ] THEN
    POP_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[SIN_POS_PI] THEN DISJ2_TAC THEN
    REWRITE_TAC[SIN_PI; REAL_MUL_RZERO; COS_PI; SIN_0; COS_0] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RNEG] THEN
    REWRITE_TAC[REAL_NEG_SUB; REAL_SUB_LE; REAL_EXP_MONO_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[COMPLEX_FIELD
   `(e + e') / Cx(&2) + ii * --ii * (e - e') / Cx(&2) = e`] THEN
  SIMP_TAC[COMPLEX_FIELD `--(ii * w) = z <=> w = ii * z`] THEN
  MATCH_MP_TAC CLOG_CEXP THEN REWRITE_TAC[IM_MUL_II] THEN
  MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC);;

let CACS_UNIQUE = prove
 (`!w z.
       ccos z = w /\
       (&0 < Re z /\ Re z < pi \/
        Re(z) = &0 /\ &0 <= Im(z) \/
        Re(z) = pi /\ Im(z) <= &0)
       ==> cacs(w) = z`,
  MESON_TAC[CACS_CCOS]);;

let CACS_0 = prove
 (`cacs(Cx(&0)) = Cx(pi / &2)`,
  MATCH_MP_TAC CACS_UNIQUE THEN
  REWRITE_TAC[RE_CX; IM_CX; GSYM CX_COS; COS_PI2] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let CACS_1 = prove
 (`cacs(Cx(&1)) = Cx(&0)`,
  MATCH_MP_TAC CACS_UNIQUE THEN
  REWRITE_TAC[RE_CX; IM_CX; GSYM CX_COS; COS_0; REAL_LE_REFL]);;

let CACS_NEG_1 = prove
 (`cacs(--Cx(&1)) = Cx pi`,
  MATCH_MP_TAC CACS_UNIQUE THEN
  REWRITE_TAC[RE_CX; IM_CX; GSYM CX_COS; COS_PI; CX_NEG; REAL_LE_REFL]);;

let HAS_COMPLEX_DERIVATIVE_CACS = prove
 (`!z. (Im z = &0 ==> abs(Re z) < &1)
       ==> (cacs has_complex_derivative --inv(csin(cacs z))) (at z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_NEG_INV] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC THEN
  EXISTS_TAC `ccos` THEN
  REWRITE_TAC[CCOS_CACS; HAS_COMPLEX_DERIVATIVE_CCOS; CONTINUOUS_AT_CCOS] THEN
  EXISTS_TAC `ball(z:complex,&1)` THEN
  REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP (COMPLEX_RING
     `--(csin z) = Cx(&0) ==> csin(z) pow 2 + ccos(z) pow 2 = Cx(&1)
                              ==> ccos(z) pow 2 = Cx(&1)`)) THEN
    REWRITE_TAC[CCOS_CACS; CSIN_CIRCLE] THEN
    REWRITE_TAC[COMPLEX_RING
     `z pow 2 = Cx(&1) <=> z = Cx(&1) \/ z = --Cx(&1)`] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[RE_CX; IM_CX; RE_NEG; IM_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[cacs] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_COMPLEX_POW; CONTINUOUS_SUB;
             CONTINUOUS_CONST; CONTINUOUS_AT_ID] THEN
    MATCH_MP_TAC CONTINUOUS_AT_CSQRT THEN
    REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX; RE_POW_2; IM_POW_2] THEN
    REWRITE_TAC[REAL_RING `&0 - &2 * x * y = &0 <=> x = &0 \/ y = &0`] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_SUB_RZERO;
                    REAL_ARITH `&1 - (&0 - x) = &1 + x`] THEN
    ASM_SIMP_TAC[REAL_LE_SQUARE; REAL_ARITH `&0 <= x ==> &0 < &1 + x`] THEN
    REWRITE_TAC[REAL_ARITH `&0 < &1 - x * x <=> x pow 2 < &1 pow 2`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_ABS_NUM; ARITH];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_CLOG THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_ADD; RE_MUL_II] THEN
  ASM_CASES_TAC `Im z = &0` THENL
   [ASM_REWRITE_TAC[csqrt] THEN
    ASM_REWRITE_TAC[IM_SUB; RE_SUB; IM_CX; RE_CX; IM_POW_2; RE_POW_2;
                    REAL_MUL_RZERO; REAL_SUB_REFL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&0 <= &1 - (z pow 2 - &0) <=> z pow 2 <= &1 pow 2`;
                GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_NUM; RE; REAL_ADD_LID] THEN
    REWRITE_TAC[GSYM real_sub; IM; REAL_SUB_LT; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x = &0 ==> &0 < y`) THEN
    MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_SIMP_TAC[REAL_SUB_LT; ABS_SQUARE_LT_1];
    ALL_TAC] THEN
  REWRITE_TAC[csqrt; IM_SUB; RE_SUB; IM_CX; RE_CX; IM_POW_2; RE_POW_2] THEN
  REWRITE_TAC[REAL_RING `&0 - &2 * x * y = &0 <=> x = &0 \/ y = &0`] THEN
  ASM_CASES_TAC `Re z = &0` THEN ASM_REWRITE_TAC[RE; IM] THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&1 - (&0 - x) = &1 + x`] THEN
    SIMP_TAC[REAL_POW_2; REAL_LE_ADD; REAL_LE_SQUARE; REAL_POS] THEN
    REWRITE_TAC[RE; IM; REAL_ADD_LID] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `a + b = &0 ==> a = --b`)) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real. x pow 2`) THEN
    SIMP_TAC[SQRT_POW_2; REAL_POW_NEG; ARITH; REAL_LE_SQUARE; REAL_LE_ADD;
             REAL_POS] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `a + b = &0 ==> a = --b`)) THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x:real. x pow 2`) THEN
  SUBGOAL_THEN `&0 < (norm(Cx (&1) - z pow 2) +
                      &1 - (Re z pow 2 - Im z pow 2)) / &2`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&0 < (x + y - z) / &2 <=> z - y < x`] THEN
    REWRITE_TAC[complex_norm] THEN MATCH_MP_TAC REAL_LT_RSQRT THEN
    REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX; RE_POW_2; IM_POW_2] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [GSYM REAL_LT_SQUARE])) THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_POW_NEG; ARITH; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_POW_2; REAL_ARITH
   `a = (n + &1 - (b - a)) / &2 <=> (a + b) - &1 = n`] THEN
  REWRITE_TAC[complex_norm] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x:real. x pow 2`) THEN
  SIMP_TAC[SQRT_POW_2; REWRITE_RULE[GSYM REAL_POW_2] REAL_LE_SQUARE;
           REAL_LE_ADD] THEN
  REWRITE_TAC[RE_SUB; RE_CX; RE_POW_2; IM_SUB; IM_CX; IM_POW_2] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
   GEN_REWRITE_RULE I [GSYM REAL_LT_SQUARE])) THEN
  REAL_ARITH_TAC);;

let COMPLEX_DIFFERENTIABLE_AT_CACS = prove
 (`!z. (Im z = &0 ==> abs(Re z) < &1) ==> cacs complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CACS]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_CACS = prove
 (`!s z. (Im z = &0 ==> abs(Re z) < &1)
         ==> cacs complex_differentiable (at z within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_AT_WITHIN;
            COMPLEX_DIFFERENTIABLE_AT_CACS]);;

add_complex_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
             HAS_COMPLEX_DERIVATIVE_CACS)));;

let CONTINUOUS_AT_CACS = prove
 (`!z. (Im z = &0 ==> abs(Re z) < &1) ==> cacs continuous at z`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CACS;
            HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_CACS = prove
 (`!s z. (Im z = &0 ==> abs(Re z) < &1) ==> cacs continuous (at z within s)`,
  MESON_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CACS]);;

let CONTINUOUS_ON_CACS = prove
 (`!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> cacs continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CACS]);;

let HOLOMORPHIC_ON_CACS = prove
 (`!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> cacs holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CACS]);;

(* ------------------------------------------------------------------------- *)
(* Some crude range theorems (could be sharpened).                           *)
(* ------------------------------------------------------------------------- *)

let CASN_RANGE_LEMMA = prove
 (`!z. abs (Re z) < &1 ==> &0 < Re(ii * z + csqrt(Cx(&1) - z pow 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RE_ADD; RE_MUL_II] THEN
  REWRITE_TAC[REAL_ARITH `&0 < --i + r <=> i < r`] THEN
  REWRITE_TAC[csqrt; IM_SUB; RE_SUB; COMPLEX_POW_2; RE_CX; IM_CX] THEN
  REWRITE_TAC[complex_mul; RE; IM] THEN REWRITE_TAC[GSYM complex_mul] THEN
  REWRITE_TAC[REAL_ARITH `r * i + i * r = &2 * r * i`] THEN
  REWRITE_TAC[REAL_SUB_LZERO; REAL_NEG_EQ_0; REAL_ABS_NEG] THEN
  REWRITE_TAC[REAL_NEG_SUB; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH] THEN
  MAP_EVERY ASM_CASES_TAC [`Re z = &0`; `Im z = &0`] THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_SUB_RZERO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[RE; SQRT_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THENL
   [REWRITE_TAC[REAL_ARITH `&1 - (&0 - z) = &1 + z`] THEN
    SIMP_TAC[REAL_LE_ADD; REAL_POS; REAL_LE_SQUARE; RE] THEN
    MATCH_MP_TAC REAL_LT_RSQRT THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `Re(z) pow 2 < &1 pow 2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      ASM_REWRITE_TAC[REAL_ABS_POS; REAL_ABS_NUM; ARITH];
      REWRITE_TAC[REAL_POW_ONE] THEN STRIP_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[RE] THEN
    TRY(MATCH_MP_TAC SQRT_POS_LT) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_RSQRT THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH
     `a < (n + &1 - (b - a)) / &2 <=> (a + b) - &1 < n`] THEN
    REWRITE_TAC[complex_norm] THEN MATCH_MP_TAC REAL_LT_RSQRT THEN
    REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX] THEN
    REWRITE_TAC[complex_mul; RE; IM] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE I [GSYM REAL_LT_SQUARE])) THEN
    REAL_ARITH_TAC]);;

let CACS_RANGE_LEMMA = prove
 (`!z. abs(Re z) < &1 ==> &0 < Im(z + ii * csqrt(Cx(&1) - z pow 2))`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `--z:complex` CASN_RANGE_LEMMA) THEN
  ASM_SIMP_TAC[IM_NEG; RE_NEG; IM_ADD; RE_ADD; IM_MUL_II; RE_MUL_II;
               COMPLEX_POW_NEG; ARITH; REAL_ABS_NEG] THEN
  REAL_ARITH_TAC);;

let RE_CASN = prove
 (`!z. Re(casn z) = Im(clog(ii * z + csqrt(Cx(&1) - z pow 2)))`,
  REWRITE_TAC[casn; COMPLEX_MUL_LNEG; RE_NEG; RE_MUL_II; REAL_NEGNEG]);;

let RE_CACS = prove
 (`!z. Re(cacs z) = Im(clog(z + ii * csqrt(Cx(&1) - z pow 2)))`,
  REWRITE_TAC[cacs; COMPLEX_MUL_LNEG; RE_NEG; RE_MUL_II; REAL_NEGNEG]);;

let CASN_BOUNDS = prove
 (`!z. abs(Re z) < &1 ==> abs(Re(casn z)) < pi / &2`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RE_CASN] THEN
  MATCH_MP_TAC RE_CLOG_POS_LT_IMP THEN ASM_SIMP_TAC[CASN_RANGE_LEMMA]);;

let CACS_BOUNDS = prove
 (`!z. abs(Re z) < &1 ==> &0 < Re(cacs z) /\ Re(cacs z) < pi`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RE_CACS] THEN
  MATCH_MP_TAC IM_CLOG_POS_LT_IMP THEN ASM_SIMP_TAC[CACS_RANGE_LEMMA]);;

let RE_CACS_BOUNDS = prove
 (`!z. --pi < Re(cacs z) /\ Re(cacs z) <= pi`,
  REWRITE_TAC[RE_CACS] THEN SIMP_TAC[CLOG_WORKS; CACS_BODY_LEMMA]);;

let RE_CACS_BOUND = prove
 (`!z. abs(Re(cacs z)) <= pi`,
  MP_TAC RE_CACS_BOUNDS THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let RE_CASN_BOUNDS = prove
 (`!z. --pi < Re(casn z) /\ Re(casn z) <= pi`,
  REWRITE_TAC[RE_CASN] THEN SIMP_TAC[CLOG_WORKS; CASN_BODY_LEMMA]);;

let RE_CASN_BOUND = prove
 (`!z. abs(Re(casn z)) <= pi`,
  MP_TAC RE_CASN_BOUNDS THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Interrelations between the two functions.                                 *)
(* ------------------------------------------------------------------------- *)

let CCOS_CASN_NZ = prove
 (`!z. ~(z pow 2 = Cx(&1)) ==> ~(ccos(casn z) = Cx(&0))`,
  REWRITE_TAC[ccos; casn; CEXP_NEG; COMPLEX_RING `ii * --ii * z = z`;
              COMPLEX_RING `--ii * --ii * z = --z`] THEN
  SIMP_TAC[CEXP_CLOG; CASN_BODY_LEMMA;
           COMPLEX_FIELD `~(x = Cx(&0))
                          ==> ((x + inv(x)) / Cx(&2) = Cx(&0) <=>
                                x pow 2 = --Cx(&1))`] THEN
  SIMP_TAC[CSQRT; COMPLEX_FIELD
              `s pow 2 = Cx(&1) - z pow 2
               ==> ((ii * z + s) pow 2 = --Cx(&1) <=>
                    ii * s * z = Cx(&1) - z pow 2)`] THEN
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING
   `~(x pow 2 + y pow 2 = Cx(&0)) ==> ~(ii * x = y)`) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  MP_TAC(SPEC `Cx(&1) - z pow 2` CSQRT) THEN CONV_TAC COMPLEX_RING);;

let CSIN_CACS_NZ = prove
 (`!z. ~(z pow 2 = Cx(&1)) ==> ~(csin(cacs z) = Cx(&0))`,
  REWRITE_TAC[csin; cacs; CEXP_NEG; COMPLEX_RING `ii * --ii * z = z`;
              COMPLEX_RING `--ii * --ii * z = --z`] THEN
  SIMP_TAC[CEXP_CLOG; CACS_BODY_LEMMA;
           COMPLEX_FIELD `~(x = Cx(&0))
                          ==> ((x - inv(x)) / (Cx(&2) * ii) = Cx(&0) <=>
                                x pow 2 = Cx(&1))`] THEN
  SIMP_TAC[CSQRT; COMPLEX_FIELD
              `s pow 2 = Cx(&1) - z pow 2
               ==> ((z + ii * s) pow 2 = Cx(&1) <=>
                    ii * s * z = Cx(&1) - z pow 2)`] THEN
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING
   `~(x pow 2 + y pow 2 = Cx(&0)) ==> ~(ii * x = y)`) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  MP_TAC(SPEC `Cx(&1) - z pow 2` CSQRT) THEN CONV_TAC COMPLEX_RING);;

let CCOS_CSIN_CSQRT = prove
 (`!z. &0 < cos(Re z) \/ cos(Re z) = &0 /\ Im(z) * sin(Re z) <= &0
       ==> ccos(z) = csqrt(Cx(&1) - csin(z) pow 2)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CSQRT_UNIQUE THEN
  REWRITE_TAC[COMPLEX_EQ_SUB_LADD] THEN ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
  REWRITE_TAC[CSIN_CIRCLE] THEN REWRITE_TAC[RE_CCOS; IM_CCOS] THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_HALF; REAL_LT_ADD; REAL_EXP_POS_LT] THEN
  DISJ2_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(REAL_ARITH
   `x * y <= &0 ==> &0 <= --x * y`)) THEN
  REWRITE_TAC[REAL_MUL_POS_LE] THEN
  SIMP_TAC[REAL_ARITH `x / &2 = &0 <=> x = &0`; REAL_LT_RDIV_EQ; REAL_ADD_LID;
           REAL_SUB_LT; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH; REAL_MUL_LZERO;
           REAL_SUB_0; REAL_EXP_MONO_LT; REAL_LT_SUB_RADD; REAL_EXP_INJ] THEN
  REAL_ARITH_TAC);;

let CSIN_CCOS_CSQRT = prove
 (`!z. &0 < sin(Re z) \/ sin(Re z) = &0 /\ &0 <= Im(z) * cos(Re z)
       ==> csin(z) = csqrt(Cx(&1) - ccos(z) pow 2)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CSQRT_UNIQUE THEN
  REWRITE_TAC[COMPLEX_EQ_SUB_LADD] THEN ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[COMPLEX_ADD_SYM] CSIN_CIRCLE] THEN
  REWRITE_TAC[RE_CSIN; IM_CSIN] THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_HALF; REAL_LT_ADD; REAL_EXP_POS_LT] THEN
  DISJ2_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[REAL_MUL_POS_LE] THEN
  SIMP_TAC[REAL_ARITH `x / &2 = &0 <=> x = &0`; REAL_LT_RDIV_EQ; REAL_ADD_LID;
           REAL_SUB_LT; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH; REAL_MUL_LZERO;

           REAL_SUB_0; REAL_EXP_MONO_LT; REAL_LT_SUB_RADD; REAL_EXP_INJ] THEN
  REAL_ARITH_TAC);;

let CASN_CACS_SQRT_POS = prove
 (`!z. (&0 < Re z \/ Re z = &0 /\ &0 <= Im z)
       ==> casn(z) = cacs(csqrt(Cx(&1) - z pow 2))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[casn; cacs] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING `w = z ==> ii * z + s = s + ii * w`) THEN
  MATCH_MP_TAC CSQRT_UNIQUE THEN
  ASM_REWRITE_TAC[CSQRT] THEN CONV_TAC COMPLEX_RING);;

let CACS_CASN_SQRT_POS = prove
 (`!z. (&0 < Re z \/ Re z = &0 /\ &0 <= Im z)
       ==> cacs(z) = casn(csqrt(Cx(&1) - z pow 2))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[casn; cacs] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING `w = z ==> z + ii * s = ii * s + w`) THEN
  MATCH_MP_TAC CSQRT_UNIQUE THEN
  ASM_REWRITE_TAC[CSQRT] THEN CONV_TAC COMPLEX_RING);;

let CSIN_CACS = prove
 (`!z. &0 < Re z \/ Re(z) = &0 /\ &0 <= Im z
       ==> csin(cacs z) = csqrt(Cx(&1) - z pow 2)`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CSIN_CASN] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CACS_CASN_SQRT_POS THEN
  ASM_REWRITE_TAC[]);;

let CCOS_CASN = prove
 (`!z. &0 < Re z \/ Re(z) = &0 /\ &0 <= Im z
       ==> ccos(casn z) = csqrt(Cx(&1) - z pow 2)`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CCOS_CACS] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CASN_CACS_SQRT_POS THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Real arcsin.                                                              *)
(* ------------------------------------------------------------------------- *)

let asn = new_definition `asn(x) = Re(casn(Cx x))`;;

let REAL_ASN = prove
 (`!z. real z /\ abs(Re z) <= &1 ==> real(casn z)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SPEC_TAC(`Re z`,`x:real`) THEN
  REWRITE_TAC[real; casn; COMPLEX_MUL_LNEG; IM_NEG; IM_MUL_II] THEN
  GEN_TAC THEN REWRITE_TAC[RE_CX; REAL_NEG_EQ_0] THEN DISCH_TAC THEN
  MATCH_MP_TAC NORM_CEXP_IMAGINARY THEN
  SIMP_TAC[CEXP_CLOG; CASN_BODY_LEMMA; NORM_EQ_SQUARE] THEN
  REWRITE_TAC[DOT_SQUARE_NORM; COMPLEX_SQNORM] THEN
  REWRITE_TAC[RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  ASM_SIMP_TAC[GSYM CX_POW; GSYM CX_SUB; GSYM CX_SQRT; REAL_SUB_LE;
               ABS_SQUARE_LE_1; RE_CX; IM_CX; REAL_NEG_0; REAL_ADD_LID;
               SQRT_POW_2] THEN
  REAL_ARITH_TAC);;

let CX_ASN = prove
 (`!x. abs(x) <= &1 ==> Cx(asn x) = casn(Cx x)`,
  REWRITE_TAC[asn] THEN MESON_TAC[REAL; RE_CX; REAL_CX; REAL_ASN]);;

let SIN_ASN = prove
 (`!y. --(&1) <= y /\ y <= &1 ==> sin(asn(y)) = y`,
  REWRITE_TAC[REAL_ARITH `--(&1) <= y /\ y <= &1 <=> abs(y) <= &1`] THEN
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN SIMP_TAC[CX_ASN; CX_SIN; CSIN_CASN]);;

let ASN_SIN = prove
 (`!x. --(pi / &2) <= x /\ x <= pi / &2 ==> asn(sin(x)) = x`,
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN SIMP_TAC[CX_ASN; SIN_BOUND; CX_SIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CASN_CSIN THEN
  REWRITE_TAC[IM_CX; RE_CX] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REAL_ARITH_TAC);;

let ASN_BOUNDS_LT = prove
 (`!y. --(&1) < y /\ y < &1 ==> --(pi / &2) < asn(y) /\ asn(y) < pi / &2`,
  GEN_TAC THEN REWRITE_TAC[asn] THEN
  MP_TAC(SPEC `Cx y` CASN_BOUNDS) THEN
  REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC);;

let ASN_0 = prove
 (`asn(&0) = &0`,
  REWRITE_TAC[asn; CASN_0; RE_CX]);;

let ASN_1 = prove
 (`asn(&1) = pi / &2`,
  REWRITE_TAC[asn; CASN_1; RE_CX]);;

let ASN_NEG_1 = prove
 (`asn(-- &1) = --(pi / &2)`,
  REWRITE_TAC[asn; CX_NEG; CASN_NEG_1; RE_CX; RE_NEG]);;

let ASN_BOUNDS = prove
 (`!y. --(&1) <= y /\ y <= &1 ==> --(pi / &2) <= asn(y) /\ asn(y) <= pi / &2`,
  REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY MP_TAC [ASN_1; ASN_NEG_1; SPEC `y:real` ASN_BOUNDS_LT] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let ASN_BOUNDS_PI2 = prove
 (`!x. &0 <= x /\ x <= &1 ==> &0 <= asn x /\ asn x <= pi / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&0`; `asn x`] SIN_MONO_LE_EQ) THEN
  ASM_SIMP_TAC[SIN_0; SIN_ASN; REAL_ARITH `&0 <= x ==> --(&1) <= x`] THEN
  MP_TAC(SPEC `x:real` ASN_BOUNDS) THEN MP_TAC PI_POS THEN
  ASM_REAL_ARITH_TAC);;

let ASN_NEG = prove
 (`!x. -- &1 <= x /\ x <= &1 ==> asn(--x) = --asn(x)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
     [GSYM(MATCH_MP SIN_ASN th)]) THEN
  REWRITE_TAC[GSYM SIN_NEG] THEN MATCH_MP_TAC ASN_SIN THEN
  REWRITE_TAC[REAL_ARITH `--a <= --x /\ --x <= a <=> --a <= x /\ x <= a`] THEN
  ASM_SIMP_TAC[ASN_BOUNDS]);;

let COS_ASN_NZ = prove
 (`!x. --(&1) < x /\ x < &1 ==> ~(cos(asn(x)) = &0)`,
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN SIMP_TAC[CX_ASN; CX_COS;
    REAL_ARITH `--(&1) < x /\ x < &1 ==> abs(x) <= &1`] THEN
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CCOS_CASN_NZ THEN
  SIMP_TAC[COMPLEX_RING `x pow 2 = Cx(&1) <=> x = Cx(&1) \/ x = --Cx(&1)`] THEN
  REWRITE_TAC[GSYM CX_NEG; CX_INJ] THEN
  ASM_REAL_ARITH_TAC);;

let ASN_MONO_LT_EQ = prove
 (`!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (asn(x) < asn(y) <=> x < y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sin(asn(x)) < sin(asn(y))` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIN_MONO_LT_EQ THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THEN MATCH_MP_TAC ASN_BOUNDS;
    BINOP_TAC THEN MATCH_MP_TAC SIN_ASN] THEN
  ASM_REAL_ARITH_TAC);;

let ASN_MONO_LE_EQ = prove
 (`!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (asn(x) <= asn(y) <=> x <= y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ASM_SIMP_TAC[ASN_MONO_LT_EQ]);;

let ASN_MONO_LT = prove
 (`!x y. --(&1) <= x /\ x < y /\ y <= &1 ==> asn(x) < asn(y)`,
  MP_TAC ASN_MONO_LT_EQ THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REAL_ARITH_TAC);;

let ASN_MONO_LE = prove
 (`!x y. --(&1) <= x /\ x <= y /\ y <= &1 ==> asn(x) <= asn(y)`,
  MP_TAC ASN_MONO_LE_EQ THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REAL_ARITH_TAC);;

let COS_ASN = prove
 (`!x. --(&1) <= x /\ x <= &1 ==> cos(asn x) = sqrt(&1 - x pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(GSYM SQRT_UNIQUE) THEN
  ASM_SIMP_TAC[ASN_BOUNDS; COS_POS_PI_LE; REAL_EQ_SUB_RADD] THEN
  ASM_MESON_TAC[SIN_ASN; SIN_CIRCLE; REAL_ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Real arccosine.                                                           *)
(* ------------------------------------------------------------------------- *)

let acs = new_definition `acs(x) = Re(cacs(Cx x))`;;

let REAL_ACS = prove
 (`!z. real z /\ abs(Re z) <= &1 ==> real(cacs z)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SPEC_TAC(`Re z`,`x:real`) THEN
  REWRITE_TAC[real; cacs; COMPLEX_MUL_LNEG; IM_NEG; IM_MUL_II] THEN
  GEN_TAC THEN REWRITE_TAC[RE_CX; REAL_NEG_EQ_0] THEN DISCH_TAC THEN
  MATCH_MP_TAC NORM_CEXP_IMAGINARY THEN
  SIMP_TAC[CEXP_CLOG; CACS_BODY_LEMMA; NORM_EQ_SQUARE] THEN
  REWRITE_TAC[DOT_SQUARE_NORM; COMPLEX_SQNORM] THEN
  REWRITE_TAC[RE_ADD; IM_ADD; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  ASM_SIMP_TAC[GSYM CX_POW; GSYM CX_SUB; GSYM CX_SQRT; REAL_SUB_LE;
               ABS_SQUARE_LE_1; RE_CX; IM_CX; REAL_NEG_0; REAL_ADD_LID;
               SQRT_POW_2] THEN
  REAL_ARITH_TAC);;

let CX_ACS = prove
 (`!x. abs(x) <= &1 ==> Cx(acs x) = cacs(Cx x)`,
  REWRITE_TAC[acs] THEN MESON_TAC[REAL; RE_CX; REAL_CX; REAL_ACS]);;

let COS_ACS = prove
 (`!y. --(&1) <= y /\ y <= &1 ==> cos(acs(y)) = y`,
  REWRITE_TAC[REAL_ARITH `--(&1) <= y /\ y <= &1 <=> abs(y) <= &1`] THEN
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN SIMP_TAC[CX_ACS; CX_COS; CCOS_CACS]);;

let ACS_COS = prove
 (`!x. &0 <= x /\ x <= pi ==> acs(cos(x)) = x`,
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN SIMP_TAC[CX_ACS; COS_BOUND; CX_COS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CACS_CCOS THEN
  REWRITE_TAC[IM_CX; RE_CX] THEN ASM_REAL_ARITH_TAC);;

let ACS_BOUNDS_LT = prove
 (`!y. --(&1) < y /\ y < &1 ==> &0 < acs(y) /\ acs(y) < pi`,
  GEN_TAC THEN REWRITE_TAC[acs] THEN
  MP_TAC(SPEC `Cx y` CACS_BOUNDS) THEN
  REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC);;

let ACS_0 = prove
 (`acs(&0) = pi / &2`,
  REWRITE_TAC[acs; CACS_0; RE_CX]);;

let ACS_1 = prove
 (`acs(&1) = &0`,
  REWRITE_TAC[acs; CACS_1; RE_CX]);;

let ACS_NEG_1 = prove
 (`acs(-- &1) = pi`,
  REWRITE_TAC[acs; CX_NEG; CACS_NEG_1; RE_CX; RE_NEG]);;

let ACS_BOUNDS = prove
 (`!y. --(&1) <= y /\ y <= &1 ==> &0 <= acs(y) /\ acs(y) <= pi`,
  REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY MP_TAC [ACS_1; ACS_NEG_1; SPEC `y:real` ACS_BOUNDS_LT] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let ACS_NEG = prove
 (`!x. -- &1 <= x /\ x <= &1 ==> acs(--x) = pi - acs(x)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
     [GSYM(MATCH_MP COS_ACS th)]) THEN
  ONCE_REWRITE_TAC[GSYM COS_NEG] THEN REWRITE_TAC[GSYM COS_PERIODIC_PI] THEN
  REWRITE_TAC[REAL_ARITH `--x + y:real = y - x`] THEN MATCH_MP_TAC ACS_COS THEN
  SIMP_TAC[REAL_ARITH `&0 <= p - x /\ p - x <= p <=> &0 <= x /\ x <= p`] THEN
  ASM_SIMP_TAC[ACS_BOUNDS]);;

let SIN_ACS_NZ = prove
 (`!x. --(&1) < x /\ x < &1 ==> ~(sin(acs(x)) = &0)`,
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN SIMP_TAC[CX_ACS; CX_SIN;
    REAL_ARITH `--(&1) < x /\ x < &1 ==> abs(x) <= &1`] THEN
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CSIN_CACS_NZ THEN
  SIMP_TAC[COMPLEX_RING `x pow 2 = Cx(&1) <=> x = Cx(&1) \/ x = --Cx(&1)`] THEN
  REWRITE_TAC[GSYM CX_NEG; CX_INJ] THEN
  ASM_REAL_ARITH_TAC);;

let ACS_MONO_LT_EQ = prove
 (`!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (acs(x) < acs(y) <=> y < x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `cos(acs(y)) < cos(acs(x))` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COS_MONO_LT_EQ THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THEN MATCH_MP_TAC ACS_BOUNDS;
    BINOP_TAC THEN MATCH_MP_TAC COS_ACS] THEN
  ASM_REAL_ARITH_TAC);;

let ACS_MONO_LE_EQ = prove
 (`!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (acs(x) <= acs(y) <=> y <= x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ASM_SIMP_TAC[ACS_MONO_LT_EQ]);;

let ACS_MONO_LT = prove
 (`!x y. --(&1) <= x /\ x < y /\ y <= &1 ==> acs(y) < acs(x)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`y:real`; `x:real`] ACS_MONO_LT_EQ) THEN
  REAL_ARITH_TAC);;

let ACS_MONO_LE = prove
 (`!x y. --(&1) <= x /\ x <= y /\ y <= &1 ==> acs(y) <= acs(x)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`y:real`; `x:real`] ACS_MONO_LE_EQ) THEN
  REAL_ARITH_TAC);;

let SIN_ACS = prove
 (`!x. --(&1) <= x /\ x <= &1 ==> sin(acs x) = sqrt(&1 - x pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(GSYM SQRT_UNIQUE) THEN
  ASM_SIMP_TAC[ACS_BOUNDS; SIN_POS_PI_LE; REAL_EQ_SUB_RADD] THEN
  ASM_MESON_TAC[COS_ACS; SIN_CIRCLE]);;

let ACS_INJ = prove
 (`!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (acs x = acs y <=> x = y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  ASM_SIMP_TAC[ACS_MONO_LE_EQ] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some interrelationships among the real inverse trig functions.            *)
(* ------------------------------------------------------------------------- *)

let ACS_ATN = prove
 (`!x. -- &1 < x /\ x < &1 ==> acs(x) = pi / &2 - atn(x / sqrt(&1 - x pow 2))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x:real = p - y <=> y - (p - x) = &0`] THEN
  MATCH_MP_TAC SIN_EQ_0_PI THEN
  ASM_SIMP_TAC[ATN_BOUND; ACS_BOUNDS; REAL_LT_IMP_LE; REAL_ARITH
   `abs(x) < pi / &2 /\ &0 <= y /\ y <= pi
    ==> --pi < x - (pi / &2 - y) /\ x - (pi / &2 - y) < pi`] THEN
  SUBGOAL_THEN `tan(atn(x / sqrt(&1 - x pow 2))) = tan(pi / &2 - acs x)`
  MP_TAC THENL
   [REWRITE_TAC[TAN_COT; ATN_TAN] THEN REWRITE_TAC[tan] THEN
    ASM_SIMP_TAC[SIN_ACS; COS_ACS; REAL_LT_IMP_LE; REAL_INV_DIV];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_SUB_0] THEN
  ASM_SIMP_TAC[SIN_ACS_NZ; GSYM SIN_COS; COS_ATN_NZ; REAL_SUB_TAN; REAL_FIELD
   `~(y = &0) /\ ~(z = &0) ==> (x / (y * z) = &0 <=> x = &0)`]);;

let ASN_PLUS_ACS = prove
 (`!x. -- &1 <= x /\ x <= &1 ==> asn(x) + acs(x) = pi / &2`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x + y:real = p <=> x = p - y`] THEN
  MATCH_MP_TAC SIN_INJ_PI THEN
  ASM_SIMP_TAC[SIN_PI2; COS_PI2; SIN_SUB; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
  ASM_SIMP_TAC[SIN_ASN; COS_ACS; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH `--p <= p - x <=> x <= &2 * p`;
              REAL_ARITH `p - x <= p <=> &0 <= x`] THEN
  ASM_SIMP_TAC[ASN_BOUNDS; ACS_BOUNDS; REAL_ARITH `&2 * x / &2 = x`]);;

let ASN_ACS = prove
 (`!x. -- &1 <= x /\ x <= &1 ==> asn(x) = pi / &2 - acs(x)`,
  SIMP_TAC[REAL_EQ_SUB_LADD; ASN_PLUS_ACS]);;

let ACS_ASN = prove
 (`!x. -- &1 <= x /\ x <= &1 ==> acs(x) = pi / &2 - asn(x)`,
  SIMP_TAC[ASN_ACS] THEN REAL_ARITH_TAC);;

let ASN_ATN = prove
 (`!x. -- &1 < x /\ x < &1 ==> asn(x) = atn(x / sqrt(&1 - x pow 2))`,
  SIMP_TAC[ASN_ACS; REAL_LT_IMP_LE; ACS_ATN] THEN REAL_ARITH_TAC);;

let ASN_ACS_SQRT_POS = prove
 (`!x. &0 <= x /\ x <= &1 ==> asn(x) = acs(sqrt(&1 - x pow 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[asn; acs] THEN
  ASM_SIMP_TAC[CX_SQRT; REAL_SUB_LE; REAL_POW_1_LE; CX_SUB; CX_POW] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CASN_CACS_SQRT_POS THEN
  ASM_REWRITE_TAC[RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC);;

let ASN_ACS_SQRT_NEG = prove
 (`!x. -- &1 <= x /\ x <= &0 ==> asn(x) = --acs(sqrt(&1 - x pow 2))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x = --y <=> (--x:real) = y`] THEN
  ASM_SIMP_TAC[GSYM ASN_NEG; REAL_ARITH `x <= &0 ==> x <= &1`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(x:real) pow 2 = (--x) pow 2`] THEN
  MATCH_MP_TAC ASN_ACS_SQRT_POS THEN ASM_REAL_ARITH_TAC);;

let ACS_ASN_SQRT_POS = prove
 (`!x. &0 <= x /\ x <= &1 ==> acs(x) = asn(sqrt(&1 - x pow 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[asn; acs] THEN
  ASM_SIMP_TAC[CX_SQRT; REAL_SUB_LE; REAL_POW_1_LE; CX_SUB; CX_POW] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CACS_CASN_SQRT_POS THEN
  ASM_REWRITE_TAC[RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC);;

let ACS_ASN_SQRT_NEG = prove
 (`!x. -- &1 <= x /\ x <= &0 ==> acs(x) = pi - asn(sqrt(&1 - x pow 2))`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `--x:real` ACS_ASN_SQRT_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_POW_NEG; ARITH]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_NEG_NEG] THEN
  MATCH_MP_TAC ACS_NEG THEN ASM_REAL_ARITH_TAC);;
