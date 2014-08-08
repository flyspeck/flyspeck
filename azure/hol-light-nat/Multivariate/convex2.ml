open Hol_core
open Vectors
open Determinants
open Topology
include Convex1

(* ------------------------------------------------------------------------- *)
(* Existence of a rigid transform between congruent sets.                    *)
(* ------------------------------------------------------------------------- *)

let RIGID_TRANSFORMATION_BETWEEN_CONGRUENT_SETS = prove
 (`!x:A->real^N y:A->real^N s.
        (!i j. i IN s /\ j IN s ==> dist(x i,x j) = dist(y i,y j))
        ==> ?a f. orthogonal_transformation f /\
                  !i. i IN s ==> y i = a + f(x i)`,
  let lemma = prove
   (`!x:(real^N)^M y:(real^N)^M.
          (!i j. 1 <= i /\ i <= dimindex(:M) /\
                 1 <= j /\ j <= dimindex(:M)
                 ==> dist(x$i,x$j) = dist(y$i,y$j))
          ==> ?a f. orthogonal_transformation f /\
                    !i. 1 <= i /\ i <= dimindex(:M)
                        ==> y$i = a + f(x$i)`,
    REPEAT STRIP_TAC THEN
    ABBREV_TAC `(X:real^M^N) = lambda i j. (x:real^N^M)$j$i - x$1$i` THEN
    ABBREV_TAC `(Y:real^M^N) = lambda i j. (y:real^N^M)$j$i - y$1$i` THEN
    SUBGOAL_THEN `transp(X:real^M^N) ** X = transp(Y:real^M^N) ** Y`
    ASSUME_TAC THENL
     [REWRITE_TAC[MATRIX_MUL_LTRANSP_DOT_COLUMN] THEN
      MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
      SIMP_TAC[CART_EQ; column; LAMBDA_BETA; dot] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT; GSYM dot] THEN
      REWRITE_TAC[DOT_NORM_SUB; VECTOR_ARITH
       `(x - a) - (y - a):real^N = x - y`] THEN
      ASM_SIMP_TAC[GSYM dist; DIMINDEX_GE_1; LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?M:real^N^N. orthogonal_matrix M /\ (Y:real^M^N) = M ** (X:real^M^N)`
    (CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THENL
     [ALL_TAC;
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [CART_EQ] THEN
      MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
      SIMP_TAC[LAMBDA_BETA; matrix_mul] THEN
      REWRITE_TAC[REAL_ARITH `x - y:real = z <=> x = y + z`] THEN STRIP_TAC THEN
      EXISTS_TAC `(y:real^N^M)$1 - (M:real^N^N) ** (x:real^N^M)$1` THEN
      EXISTS_TAC `\x:real^N. (M:real^N^N) ** x` THEN
      ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX;
                   MATRIX_OF_MATRIX_VECTOR_MUL; MATRIX_VECTOR_MUL_LINEAR] THEN
      SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA;
               VECTOR_ADD_COMPONENT] THEN
      ASM_SIMP_TAC[REAL_SUB_LDISTRIB; SUM_SUB_NUMSEG] THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; REAL_ARITH
       `a + y - b:real = a - z + y <=> z = b`] THEN
      SIMP_TAC[LAMBDA_BETA]] THEN
    MP_TAC(ISPEC `transp(X:real^M^N) ** X`
      SYMMETRIC_MATRIX_DIAGONALIZABLE_EXPLICIT) THEN
    REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`P:real^M^M`; `d:num->real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(fun th -> MP_TAC th THEN ASM_REWRITE_TAC[] THEN MP_TAC th) THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[IMP_IMP] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [CART_EQ] THEN
    SIMP_TAC[MATRIX_MUL_LTRANSP_DOT_COLUMN; LAMBDA_BETA] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\i. column i ((X:real^M^N) ** (P:real^M^M))`;
                   `\i. column i ((Y:real^M^N) ** (P:real^M^M))`;
                   `1..dimindex(:M)`]
                  ORTHOGONAL_TRANSFORMATION_BETWEEN_ORTHOGONAL_SETS) THEN
    REWRITE_TAC[IN_NUMSEG] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[pairwise; IN_NUMSEG; NORM_EQ; orthogonal]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` (STRIP_ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC `matrix(f:real^N->real^N)` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!M:real^M^N. M = M ** (P:real^M^M) ** transp P`
     (fun th -> GEN_REWRITE_TAC BINOP_CONV [th])
    THENL
     [ASM_MESON_TAC[orthogonal_matrix; MATRIX_MUL_RID];
      REWRITE_TAC[MATRIX_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_EQUAL_COLUMNS] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [orthogonal_transformation]) THEN
    DISCH_THEN(ASSUME_TAC o GSYM o MATCH_MP MATRIX_WORKS o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CART_EQ; matrix_vector_mul; column; LAMBDA_BETA] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [matrix_mul] THEN
    ASM_SIMP_TAC[LAMBDA_BETA]) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:A->bool = {}` THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `\x:real^N. x`] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; ORTHOGONAL_TRANSFORMATION_ID];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `m:A`) THEN DISCH_TAC] THEN
  SUBGOAL_THEN
    `?r. IMAGE r (1..dimindex(:(N,1)finite_sum)) SUBSET s /\
         affine hull (IMAGE (y o r) (1..dimindex(:(N,1)finite_sum))) =
         affine hull (IMAGE (y:A->real^N) s)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    SIMP_TAC[IMAGE_o; TAUT `p /\ q <=> ~(p ==> ~q)`;
             HULL_MONO; IMAGE_SUBSET] THEN REWRITE_TAC[NOT_IMP] THEN
    MP_TAC(ISPEC `IMAGE (y:A->real^N) s` AFFINE_BASIS_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AFFINE_INDEPENDENT_IFF_CARD]) THEN
    STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:num->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `CARD(b:real^N->bool) <= dimindex(:(N,1)finite_sum)`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
       `a:int = c - &1 ==> a + &1 <= n ==> c <= n`)) THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
      REWRITE_TAC[INT_LE_RADD; AFF_DIM_LE_UNIV];
      ALL_TAC] THEN
    UNDISCH_TAC `b SUBSET IMAGE (y:A->real^N) s` THEN
    ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; IN_NUMSEG] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\i. if i <= CARD(b:real^N->bool) then r i else (m:A)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_THEN `affine hull b:real^N->bool = affine hull IMAGE y (s:A->bool)`
     (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC HULL_MONO THEN
    ONCE_ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN EXISTS_TAC `i:num` THEN
    ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[LE_TRANS];
    REWRITE_TAC[SUBSET; IN_NUMSEG; FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN MP_TAC(ISPECL
     [`(lambda i. x(r i:A)):real^N^(N,1)finite_sum`;
      `(lambda i. y(r i:A)):real^N^(N,1)finite_sum`] lemma) THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^N->real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!z. z IN
          affine hull IMAGE (y o (r:num->A)) (1..dimindex(:(N,1)finite_sum))
          ==> dist(z,y k) = dist(z,a + (f:real^N->real^N)(x k))`
    MP_TAC THENL
     [MATCH_MP_TAC SAME_DISTANCES_TO_AFFINE_HULL THEN
      REWRITE_TAC[FORALL_IN_IMAGE; o_THM; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `dist(x(r(j:num)),(x:A->real^N) k)` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
        REWRITE_TAC[dist] THEN ASM_SIMP_TAC[NORM_ARITH
         `(a + x) - (a + y):real^N = x - y`] THEN
        ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION; LINEAR_SUB]];
      ASM_SIMP_TAC[NORM_ARITH
       `a:real^N = b <=> dist(a:real^N,a) = dist(a,b)`] THEN
      DISCH_THEN MATCH_MP_TAC THEN  MATCH_MP_TAC HULL_INC THEN
      REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN ASM_MESON_TAC[]]]);;

let RIGID_TRANSFORMATION_BETWEEN_CONGRUENT_SETS_STRONG = prove
 (`!x:A->real^N y:A->real^N s t.
        t SUBSET s /\ affine hull (IMAGE y t) = affine hull (IMAGE y s) /\
        (!i j. i IN s /\ j IN t ==> dist(x i,x j) = dist(y i,y j))
        ==> ?a f. orthogonal_transformation f /\
                  !i. i IN s ==> y i = a + f(x i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:A->real^N`; `y:A->real^N`; `t:A->bool`]
        RIGID_TRANSFORMATION_BETWEEN_CONGRUENT_SETS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^N->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!z. z IN affine hull (IMAGE (y:A->real^N) t)
        ==> dist(z,y i) = dist(z,a + (f:real^N->real^N)(x i))`
  MP_TAC THENL
   [MATCH_MP_TAC SAME_DISTANCES_TO_AFFINE_HULL THEN
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM; IN_NUMSEG] THEN
    X_GEN_TAC `j:A` THEN STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `dist(a + f(x(j:A):real^N):real^N,a + f(x i))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[NORM_ARITH `dist(a + x:real^N,a + y) = dist(x,y)`] THEN
    ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_ISOMETRY; DIST_SYM];
    ASM_SIMP_TAC[NORM_ARITH
     `a:real^N = b <=> dist(a:real^N,a) = dist(a,b)`] THEN
    DISCH_THEN MATCH_MP_TAC THEN  MATCH_MP_TAC HULL_INC THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]]);;

let RIGID_TRANSFORMATION_BETWEEN_3 = prove
 (`!a b c a' b' c':real^N.
        dist(a,b) = dist(a',b') /\
        dist(b,c) = dist(b',c') /\
        dist(c,a) = dist(c',a')
        ==> ?k f. orthogonal_transformation f /\
                  a' = k + f a /\ b' = k + f b /\ c' = k + f c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`FST:real^N#real^N->real^N`; `SND:real^N#real^N->real^N`;
    `{(a:real^N,a':real^N), (b,b'), (c,c')}`]
        RIGID_TRANSFORMATION_BETWEEN_CONGRUENT_SETS) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT] THEN
  REWRITE_TAC[NOT_IN_EMPTY; IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[DIST_REFL; DIST_SYM]);;

let RIGID_TRANSFORMATION_BETWEEN_2 = prove
 (`!a b a' b':real^N.
        dist(a,b) = dist(a',b')
        ==> ?k f. orthogonal_transformation f /\
                  a' = k + f a /\ b' = k + f b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `a:real^N`;
                 `a':real^N`; `b':real^N`; `a':real^N`]
        RIGID_TRANSFORMATION_BETWEEN_3) THEN
  ASM_MESON_TAC[DIST_EQ_0; DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Caratheodory's theorem.                                                   *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_CARATHEODORY_AFF_DIM = prove
 (`!p. convex hull p =
        {y:real^N | ?s u. FINITE s /\ s SUBSET p /\
                          &(CARD s) <= aff_dim p + &1 /\
                          (!x. x IN s ==> &0 <= u x) /\
                          sum s u = &1 /\ vsum s (\v. u v % v) = y}`,
  GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_EXPLICIT] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC(TAUT `!q. (p ==> q) /\ (q ==> r) ==> (p ==> r)`) THEN
  EXISTS_TAC `?n s u. CARD s = n /\
                      FINITE s /\ s SUBSET p /\
                      (!x. x IN s ==> &0 <= u x) /\
                      sum s u = &1 /\ vsum s (\v. u v % v) = (y:real^N)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [GSYM INT_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN REWRITE_TAC[NOT_IMP] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n - 1 < n`) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim(p:real^N->bool) + &1 < &0` THEN
    REWRITE_TAC[INT_ARITH `p + &1:int < &0 <=> ~(-- &1 <= p)`] THEN
    REWRITE_TAC[AFF_DIM_GE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(aff_dim(s:real^N->bool) = &n - &1)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN

    UNDISCH_TAC `aff_dim(p:real^N->bool) + &1 < &n` THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT_FINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?t. (!v:real^N. v IN s ==> u(v) + t * w(v) >= &0) /\
        ?a. a IN s /\ u(a) + t * w(a) = &0`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC
     `i = IMAGE (\v. u(v) / --w(v)) {v:real^N | v IN s /\ w v < &0}` THEN
    EXISTS_TAC `inf i` THEN MP_TAC(SPEC `i:real->bool` INF_FINITE) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "i" THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`w:real^N->real`; `s:real^N->bool`] SUM_ZERO_EXISTS) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `t = inf i` THEN
    EXPAND_TAC "i" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^N`
      STRIP_ASSUME_TAC) MP_TAC) THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `x < &0 ==> &0 < --x`; real_ge] THEN
    REWRITE_TAC[REAL_ARITH `t * --w <= u <=> &0 <= u + t * w`] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      DISJ_CASES_TAC(REAL_ARITH `(w:real^N->real) x < &0 \/ &0 <= w x`) THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `w < &0 ==> &0 <= --w`) THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `w(a:real^N) < &0` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`s DELETE (a:real^N)`; `(\v. u(v) + t * w(v)):real^N->real`] THEN
  ASM_SIMP_TAC[SUM_DELETE; VSUM_DELETE; CARD_DELETE; FINITE_DELETE] THEN
  ASM_SIMP_TAC[SUM_ADD; VECTOR_ADD_RDISTRIB; VSUM_ADD] THEN
  ASM_SIMP_TAC[GSYM VECTOR_MUL_ASSOC; SUM_LMUL; VSUM_LMUL] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[]; ASM SET_TAC[real_ge]; REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let CARATHEODORY_AFF_DIM = prove
 (`!p. convex hull p =
        {x:real^N | ?s. FINITE s /\ s SUBSET p /\
                         &(CARD s) <= aff_dim p + &1 /\
                        x IN convex hull s}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [CONVEX_HULL_CARATHEODORY_AFF_DIM] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC[HULL_SUBSET; CONVEX_EXPLICIT; CONVEX_CONVEX_HULL];
    MESON_TAC[SUBSET; HULL_MONO]]);;

let CONVEX_HULL_CARATHEODORY = prove
 (`!p. convex hull p =
        {y:real^N | ?s u. FINITE s /\ s SUBSET p /\
                          CARD(s) <= dimindex(:N) + 1 /\
                          (!x. x IN s ==> &0 <= u x) /\
                          sum s u = &1 /\ vsum s (\v. u v % v) = y}`,

  GEN_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  EQ_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_CARATHEODORY_AFF_DIM; IN_ELIM_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_ADD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `a:int <= x + &1 ==> x <= y ==> a <= y + &1`)) THEN
    REWRITE_TAC[AFF_DIM_LE_UNIV];
    REWRITE_TAC[CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN MESON_TAC[]]);;

let CARATHEODORY = prove
 (`!p. convex hull p =
        {x:real^N | ?s. FINITE s /\ s SUBSET p /\
                        CARD(s) <= dimindex(:N) + 1 /\
                        x IN convex hull s}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [CONVEX_HULL_CARATHEODORY] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC[HULL_SUBSET; CONVEX_EXPLICIT; CONVEX_CONVEX_HULL];
    MESON_TAC[SUBSET; HULL_MONO]]);;

(* ------------------------------------------------------------------------- *)
(* Some results on decomposing convex hulls, e.g. simplicial subdivision.    *)
(* ------------------------------------------------------------------------- *)

let AFFINE_HULL_INTER,CONVEX_HULL_INTER = (CONJ_PAIR o prove)
 (`(!s t:real^N->bool.
        ~(affine_dependent(s UNION t))
        ==> affine hull s INTER affine hull t = affine hull (s INTER t)) /\
   (!s t:real^N->bool.
        ~(affine_dependent (s UNION t))
        ==> convex hull s INTER convex hull t = convex hull (s INTER t))`,
  CONJ_TAC THEN
  (REPEAT STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
   REWRITE_TAC[FINITE_UNION] THEN STRIP_TAC THEN
   MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET_INTER] THEN
   SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
   REWRITE_TAC[SUBSET; AFFINE_HULL_FINITE; CONVEX_HULL_FINITE;
               IN_ELIM_THM; IN_INTER] THEN
   X_GEN_TAC `y:real^N` THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `v:real^N->real` STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [AFFINE_DEPENDENT_EXPLICIT]) THEN
   REWRITE_TAC[NOT_EXISTS_THM] THEN
   DISCH_THEN(MP_TAC o SPEC `(s UNION t):real^N->bool`) THEN
   ASM_REWRITE_TAC[SUBSET_REFL] THEN
   DISCH_THEN(MP_TAC o SPEC
    `\x:real^N. (if x IN s then u x else &0) -
                (if x IN t then v x else &0)`) THEN
   ASM_SIMP_TAC[SUM_SUB; FINITE_UNION; VSUM_SUB; VECTOR_SUB_RDISTRIB] THEN
   REWRITE_TAC[MESON[]
    `(if p then a else b) % x = (if p then a % x else b % x)`] THEN
   ASM_SIMP_TAC[SUM_CASES; VSUM_CASES; VECTOR_MUL_LZERO; FINITE_UNION] THEN
   ASM_REWRITE_TAC[SUM_0; VSUM_0;
     SET_RULE `{x | x IN (s UNION t) /\ x IN s} = s`;
     SET_RULE `{x | x IN (s UNION t) /\ x IN t} = t`] THEN
   MATCH_MP_TAC(TAUT `a /\ c /\ (~b ==> d) ==> ~(a /\ b /\ c) ==> d`) THEN
   REPEAT CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC; ALL_TAC] THEN
   DISCH_TAC THEN EXISTS_TAC `u:real^N->real` THEN ASM_SIMP_TAC[] THEN
   CONJ_TAC THEN MATCH_MP_TAC EQ_TRANS THENL
    [EXISTS_TAC `sum s (u:real^N->real)`;
     EXISTS_TAC `vsum s (\x. (u:real^N->real) x % x)`] THEN
   (CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM ACCEPT_TAC]) THEN
   CONV_TAC SYM_CONV THENL
    [MATCH_MP_TAC SUM_EQ_SUPERSET; MATCH_MP_TAC VSUM_EQ_SUPERSET] THEN
   ASM_SIMP_TAC[FINITE_INTER; INTER_SUBSET; IN_INTER] THEN
   X_GEN_TAC `x:real^N` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
   DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
   ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN ASM SET_TAC[]));;

let AFFINE_HULL_INTERS = prove
 (`!s:(real^N->bool)->bool.
        ~(affine_dependent(UNIONS s))
        ==> affine hull (INTERS s) = INTERS {affine hull t | t IN s}`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
   MP_TAC th THEN MP_TAC(MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE th)) THEN
  SPEC_TAC(`s:(real^N->bool)->bool`,`s:(real^N->bool)->bool`) THEN
  REWRITE_TAC[FINITE_UNIONS; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; INTERS_0; UNIONS_INSERT; INTERS_INSERT;
              SET_RULE `{f x | x IN {}} = {}`; AFFINE_HULL_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `~affine_dependent((s UNION UNIONS f):real^N->bool)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_DEPENDENT_MONO) THEN
    SET_TAC[];
    DISCH_TAC] THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[INTERS_0; INTER_UNIV; IN_SING] THEN
    REWRITE_TAC[SET_RULE `{f x | x = a} = {f a}`; INTERS_1];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rhs o rand) AFFINE_HULL_INTER o lhand o snd) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~affine_dependent((s UNION UNIONS f):real^N->bool)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_DEPENDENT_MONO) THEN
    UNDISCH_TAC `~(f:(real^N->bool)->bool = {})` THEN SET_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[SET_RULE
   `{f x | x IN (a INSERT s)} = (f a) INSERT {f x | x IN s}`] THEN
  ASM_REWRITE_TAC[INTERS_INSERT]);;

let CONVEX_HULL_INTERS = prove
 (`!s:(real^N->bool)->bool.
        ~(affine_dependent(UNIONS s))
        ==> convex hull (INTERS s) = INTERS {convex hull t | t IN s}`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
   MP_TAC th THEN MP_TAC(MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE th)) THEN
  SPEC_TAC(`s:(real^N->bool)->bool`,`s:(real^N->bool)->bool`) THEN
  REWRITE_TAC[FINITE_UNIONS; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; INTERS_0; UNIONS_INSERT; INTERS_INSERT;
              SET_RULE `{f x | x IN {}} = {}`; CONVEX_HULL_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `~affine_dependent((s UNION UNIONS f):real^N->bool)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_DEPENDENT_MONO) THEN
    SET_TAC[];
    DISCH_TAC] THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[INTERS_0; INTER_UNIV; IN_SING] THEN
    REWRITE_TAC[SET_RULE `{f x | x = a} = {f a}`; INTERS_1];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rhs o rand) CONVEX_HULL_INTER o lhand o snd) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~affine_dependent((s UNION UNIONS f):real^N->bool)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_DEPENDENT_MONO) THEN
    UNDISCH_TAC `~(f:(real^N->bool)->bool = {})` THEN SET_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[SET_RULE
   `{f x | x IN (a INSERT s)} = (f a) INSERT {f x | x IN s}`] THEN
  ASM_REWRITE_TAC[INTERS_INSERT]);;

let IN_CONVEX_HULL_EXCHANGE = prove
 (`!s a x:real^N.
        a IN convex hull s /\ x IN convex hull s
        ==> ?b. b IN s /\ x IN convex hull (a INSERT (s DELETE b))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(a:real^N) IN s` THENL
   [EXISTS_TAC `a:real^N` THEN ASM_SIMP_TAC[INSERT_DELETE]; ALL_TAC] THEN
  ASM_CASES_TAC `FINITE(s:real^N->bool) /\ CARD s <= dimindex(:N) + 1` THENL
   [ALL_TAC;
    UNDISCH_TAC `(x:real^N) IN convex hull s` THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CARATHEODORY] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t:real^N->bool = s` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?b:real^N. b IN s /\ ~(b IN t)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN convex hull t` THEN
    SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]] THEN
  MP_TAC(ASSUME `(a:real^N) IN convex hull s`) THEN
  MP_TAC(ASSUME `(x:real^N) IN convex hull s`) THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `v:real^N->real` THEN STRIP_TAC THEN
  X_GEN_TAC `u:real^N->real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `?b. b IN s /\ (v:real^N->real) b = &0` THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_EXISTS) THEN
    X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `\x:real^N. if x = a then &0 else v x` THEN
    ASM_SIMP_TAC[FORALL_IN_INSERT; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_DELETE] THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN
    ASM_SIMP_TAC[SUM_DELETE; VSUM_DELETE; COND_ID] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC[SUM_CASES; VSUM_CASES; REAL_LE_REFL; COND_ID] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; SUM_0; VSUM_0] THEN
    ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> {x | x IN s /\ ~(x = a)} = s`] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
  REWRITE_TAC[TAUT `~(a /\ b) <=> a ==> ~b`] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (\b. (u:real^N->real) b / v b) s` SUP_FINITE) THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_MESON_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `b:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!b. b IN s ==> &0 < (v:real^N->real) b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (u:real^N->real) b /\ &0 < v b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LE] THEN
    UNDISCH_TAC `!x. x IN s ==> (u:real^N->real) x / v x <= u b / v b` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> (x <= &0 <=> x = &0)`] THEN
    DISCH_TAC THEN UNDISCH_TAC `sum s (u:real^N->real) = &1` THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x = &1 ==> F`) THEN
    ASM_SIMP_TAC[SUM_EQ_0];
    ALL_TAC] THEN
  EXISTS_TAC `(\x. if x = a then v b / u b else v x - (v b / u b) * u x):
              real^N->real` THEN
  ASM_SIMP_TAC[FORALL_IN_INSERT; REAL_LE_DIV; REAL_LT_IMP_LE] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_DELETE] THEN
  ASM_SIMP_TAC[SUM_DELETE; VSUM_DELETE; IN_DELETE] THEN
  ASM_SIMP_TAC[SUM_CASES; VSUM_CASES; FINITE_DELETE] THEN
  ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> {x | x IN s /\ ~(x = a)} = s`;
               SET_RULE `~(a IN s) ==> {x | x IN s /\ x = a} = {}`] THEN
  REWRITE_TAC[VSUM_CLAUSES; SUM_CLAUSES] THEN
  ASM_CASES_TAC `b:real^N = a` THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[VECTOR_SUB_RDISTRIB; VSUM_SUB; SUM_SUB] THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; VECTOR_ADD_LID; REAL_ADD_LID] THEN
  ASM_SIMP_TAC[SUM_LMUL; VSUM_LMUL] THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC; REAL_ARITH_TAC; VECTOR_ARITH_TAC] THEN
  X_GEN_TAC `c:real^N` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_CASES_TAC `(u:real^N->real) c = &0` THENL
   [ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO]; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LE] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_LE] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LE]);;

let IN_CONVEX_HULL_EXCHANGE_UNIQUE = prove
 (`!s t t' a x:real^N.
        ~(affine_dependent s) /\
        a IN convex hull s /\
        t SUBSET s /\ t' SUBSET s /\
        x IN convex hull (a INSERT t) /\
        x IN convex hull (a INSERT t')
        ==> x IN convex hull (a INSERT (t INTER t'))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(a:real^N) IN s` THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[SET_RULE
     `a INSERT (s INTER t) = (a INSERT s) INTER (a INSERT t)`] THEN
    W(MP_TAC o PART_MATCH (rand o rand)  CONVEX_HULL_INTER o rand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~(affine_dependent(s:real^N->bool))` THEN
      REWRITE_TAC[CONTRAPOS_THM] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_DEPENDENT_MONO);
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real^N->real` STRIP_ASSUME_TAC)
    MP_TAC) THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `~((a:real^N) IN t) /\ ~(a IN t')` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(t:real^N->bool) /\ FINITE(t':real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[AFFINE_HULL_FINITE_STEP_GEN; REAL_LE_ADD;
               REAL_ARITH `&0 <= a / &2 <=> &0 <= a`] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u':real`; `u:real^N->real`] THEN REPEAT DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`v':real`; `v:real^N->real`] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
    [AFFINE_DEPENDENT_EXPLICIT]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC
   `\x:real^N. (if x IN t then u x else &0) - (if x IN t' then v x else &0) +
               (u' - v') * b x`) THEN
  ASM_SIMP_TAC[SUM_ADD; VSUM_ADD; SUM_LMUL; VSUM_LMUL; VECTOR_ADD_RDISTRIB] THEN
  ASM_SIMP_TAC[SUM_SUB; VSUM_SUB; VECTOR_SUB_RDISTRIB] THEN
  REWRITE_TAC[MESON[]
   `(if p then a else b) % x = (if p then a % x else b % x)`] THEN
  ASM_SIMP_TAC[SUM_CASES; VSUM_CASES; VECTOR_MUL_LZERO; SUM_0; VSUM_0] THEN
  ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; VSUM_ADD; VSUM_LMUL; VECTOR_ADD_RDISTRIB;
               GSYM VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC(TAUT `a /\ c /\ (~b ==> d) ==> ~(a /\ b /\ c) ==> d`) THEN
  REPEAT CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(!x. x IN s ==> (if x IN t then u x else &0) <=
                    (if x IN t' then v x else &0)) \/
    (!x:real^N. x IN s ==> (if x IN t' then v x else &0) <=
                           (if x IN t then u x else &0))`
  (DISJ_CASES_THEN(LABEL_TAC "*")) THENL
   [MP_TAC(REAL_ARITH `&0 <= (u' - v') \/ &0 <= (v' - u')`) THEN
    MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
    DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> a - b + c = &0 ==> a <= b`);
      MATCH_MP_TAC(REAL_ARITH `&0 <= --c ==> a - b + c = &0 ==> b <= a`)] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; GSYM REAL_MUL_LNEG; REAL_NEG_SUB];
    EXISTS_TAC `(\x. if x = a then u' else u x):real^N->real`;
    EXISTS_TAC `(\x. if x = a then v' else v x):real^N->real`] THEN
  ASM_SIMP_TAC[FORALL_IN_INSERT] THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[IN_INTER]; ALL_TAC]) THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_INTER] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  REWRITE_TAC[REAL_ARITH `u' + u = &1 <=> u = &1 - u'`;
              VECTOR_ARITH `u' + u:real^N = y <=> u = y - u'`] THEN
  (CONJ_TAC THEN
   FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
   CONV_TAC SYM_CONV THENL
    [MATCH_MP_TAC SUM_EQ_SUPERSET; MATCH_MP_TAC VSUM_EQ_SUPERSET]) THEN
  ASM_SIMP_TAC[FINITE_INTER; INTER_SUBSET; IN_INTER] THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  X_GEN_TAC `y:real^N` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISCH_TAC THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM SET_TAC[]);;

let CONVEX_HULL_EXCHANGE_UNION = prove
 (`!s a:real^N.
        a IN convex hull s
        ==> convex hull s =
            UNIONS {convex hull (a INSERT (s DELETE b)) |b| b IN s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[UNIONS_IMAGE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[IN_CONVEX_HULL_EXCHANGE];
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; FORALL_IN_GSPEC;
                IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM SUBSET] THEN
    ASM_SIMP_TAC[SUBSET_HULL; CONVEX_CONVEX_HULL] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET] THEN
    MESON_TAC[HULL_INC; SUBSET; IN_DELETE]]);;

let CONVEX_HULL_EXCHANGE_INTER = prove
 (`!s a:real^N t t'.
         ~affine_dependent s /\
         a IN convex hull s /\
         t SUBSET s /\
         t' SUBSET s
         ==> (convex hull (a INSERT t)) INTER (convex hull (a INSERT t')) =
             convex hull (a INSERT (t INTER t'))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC IN_CONVEX_HULL_EXCHANGE_UNIQUE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Representing affine hull as hyperplane or finite intersection of them.    *)
(* ------------------------------------------------------------------------- *)

let AFF_DIM_EQ_HYPERPLANE = prove
 (`!s. aff_dim s = &(dimindex(:N)) - &1 <=>
       ?a b. ~(a = vec 0) /\ affine hull s = {x:real^N | a dot x = b}`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY; INT_ARITH `--a:int = b - a <=> b = &0`] THEN
    SIMP_TAC[INT_OF_NUM_EQ; LE_1; DIMINDEX_GE_1; AFFINE_HULL_EMPTY] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `(b / (a dot a)) % a:real^N`) THEN
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `c:real^N` THEN
    GEN_GEOM_ORIGIN_TAC `c:real^N` ["a"] THEN
    SIMP_TAC[AFF_DIM_DIM_0; HULL_INC] THEN
    SIMP_TAC[INT_OF_NUM_SUB; DIMINDEX_GE_1; INT_OF_NUM_EQ] THEN
    SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; DIM_EQ_HYPERPLANE] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `a:real^N` THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
    ASM_REWRITE_TAC[DOT_RADD; REAL_ARITH `a + b:real = c <=> b = c - a`] THEN
    EQ_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC `(a:real^N) dot c` THEN ASM_REWRITE_TAC[REAL_SUB_REFL];
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `\s. (vec 0:real^N) IN s`) THEN
      ASM_SIMP_TAC[SPAN_SUPERSET; IN_ELIM_THM; DOT_RZERO]]]);;

let AFF_DIM_HYPERPLANE = prove
 (`!a b. ~(a = vec 0)
         ==> aff_dim {x:real^N | a dot x = b} = &(dimindex(:N)) - &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFF_DIM_EQ_HYPERPLANE] THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real`] THEN
  ASM_REWRITE_TAC[AFFINE_HULL_EQ; AFFINE_HYPERPLANE]);;

let BOUNDED_HYPERPLANE_EQ_TRIVIAL = prove
 (`!a b. bounded {x:real^N | a dot x = b} <=>
         if a = vec 0 then ~(b = &0) else dimindex(:N) = 1`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO] THENL
   [ASM_CASES_TAC `b = &0` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; BOUNDED_EMPTY] THEN
    REWRITE_TAC[NOT_BOUNDED_UNIV; SET_RULE `{x | T} = UNIV`];
    ASM_SIMP_TAC[AFFINE_BOUNDED_EQ_LOWDIM; AFF_DIM_HYPERPLANE;
                 AFFINE_HYPERPLANE] THEN
    REWRITE_TAC[INT_ARITH `a - &1:int <= &0 <=> a <= &1`; INT_OF_NUM_LE] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> (n <= 1 <=> n = 1)`) THEN
    REWRITE_TAC[DIMINDEX_GE_1]]);;

let AFFINE_HULL_FINITE_INTERSECTION_HYPERPLANES = prove
 (`!s:real^N->bool.
        ?f. FINITE f /\
            &(CARD f) + aff_dim s = &(dimindex(:N)) /\
            affine hull s = INTERS f /\
            (!h. h IN f ==> ?a b. ~(a = vec 0) /\ h = {x | a dot x = b})`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  MP_TAC(ISPEC `s:real^N->bool` AFFINE_BASIS_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `(:real^N)`] EXTEND_TO_AFFINE_BASIS) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; AFFINE_HULL_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE(c:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM AFF_DIM_UNIV] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; CARD_DIFF] THEN
  REWRITE_TAC[INT_ARITH `f + b - &1:int = c - &1 <=> f = c - b`] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; CARD_SUBSET; GSYM CARD_DIFF; INT_OF_NUM_EQ] THEN
  ASM_CASES_TAC `c:real^N->bool = b` THENL
   [EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; INTERS_0;
                    DIFF_EQ_EMPTY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{affine hull (c DELETE a) |a| (a:real^N) IN (c DIFF b)}` THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DIFF] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_SIMP_TAC[FINITE_DIFF] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN REWRITE_TAC[IN_DIFF] THEN
    STRIP_TAC THEN ASM_CASES_TAC `x:real^N = y` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~affine_dependent(c:real^N->bool)` THEN
    REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN REWRITE_TAC[IMAGE_o] THEN
    ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
    W(MP_TAC o PART_MATCH (rhs o rand) AFFINE_HULL_INTERS o rand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
      EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; FORALL_IN_IMAGE;
                  IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_INTERS; FORALL_IN_IMAGE] THEN ASM SET_TAC[]];
    REWRITE_TAC[GSYM AFF_DIM_EQ_HYPERPLANE] THEN
    ASM_SIMP_TAC[IN_DIFF; AFFINE_INDEPENDENT_DELETE;
                 AFF_DIM_AFFINE_INDEPENDENT; CARD_DELETE] THEN
    REWRITE_TAC[GSYM AFF_DIM_UNIV] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; CARD_DIFF] THEN
    REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(GSYM INT_OF_NUM_SUB) THEN
    MATCH_MP_TAC(ARITH_RULE `~(c = 0) ==> 1 <= c`) THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[]]);;

let AFFINE_HYPERPLANE_SUMS_EQ_UNIV = prove
 (`!a b s.
        affine s /\
        ~(s INTER {v | a dot v = b} = {}) /\
        ~(s DIFF {v | a dot v = b} = {})
        ==> {x + y | x IN s /\ y IN {v | a dot v = b}} = (:real^N)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[DOT_LZERO] THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEMBER_NOT_EMPTY] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN X_GEN_TAC `c:real^N` THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x + y:real^N | x IN s /\ P y} =
        {z | ?x y. x IN s /\ P y /\ z = x + y}`] THEN
  GEOM_ORIGIN_TAC `c:real^N` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[DOT_RADD; REAL_ARITH `b dot c + a = d <=> a = d - b dot c`] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; DOT_RZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[AFFINE_EQ_SUBSPACE; HULL_INC] THEN STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `c + z:real^N = (c + x) + (c + y) <=>
                            z = c + x + y`] THEN
  REWRITE_TAC[SET_RULE
   `{z | ?x y. x IN s /\ P y /\ z = c + x + y} =
    IMAGE (\x. c + x) {x + y:real^N | x IN s /\ y IN {v | P v}}`] THEN
  MATCH_MP_TAC(SET_RULE
   `!f. (!x. g(f x) = x) /\ s = UNIV ==> IMAGE g s = UNIV`) THEN
  EXISTS_TAC `\x:real^N. x - c` THEN
  REWRITE_TAC[VECTOR_ARITH `c + x - c:real^N = x`] THEN
  MATCH_MP_TAC(MESON[SPAN_EQ_SELF] `subspace s /\ span s = t ==> s = t`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSPACE_SUMS; SUBSPACE_HYPERPLANE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DIM_EQ_FULL] THEN
  REWRITE_TAC[GSYM LE_ANTISYM; DIM_SUBSET_UNIV] THEN
  MATCH_MP_TAC(ARITH_RULE `m - 1 < n ==> m <= n`) THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `dim {x:real^N | a dot x = &0}` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[DIM_HYPERPLANE; LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC DIM_PSUBSET THEN
  ASM_SIMP_TAC[snd(EQ_IMP_RULE(SPEC_ALL SPAN_EQ_SELF));
               SUBSPACE_SUMS; SUBSPACE_HYPERPLANE] THEN
  REWRITE_TAC[PSUBSET; SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `x:real^N`] THEN
    ASM_SIMP_TAC[SUBSPACE_0; VECTOR_ADD_LID];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `x:real^N` THEN SIMP_TAC[IN_DIFF; IN_ELIM_THM] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^N`; `vec 0:real^N`] THEN
    ASM_REWRITE_TAC[DOT_RZERO; VECTOR_ADD_RID]]);;

let AFF_DIM_AFFINE_INTER_HYPERPLANE = prove
 (`!a b s:real^N->bool.
        affine s
        ==> aff_dim(s INTER {x | a dot x = b}) =
                if s INTER {v | a dot v = b} = {} then -- &1
                else if s SUBSET {v | a dot v = b} then aff_dim s
                else aff_dim s - &1`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[DOT_LZERO] THEN ASM_CASES_TAC `b = &0` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; INTER_EMPTY; AFF_DIM_EMPTY] THEN
    SIMP_TAC[SET_RULE `{x | T} = UNIV`; IN_UNIV; INTER_UNIV; SUBSET_UNIV] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY];
    STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
    COND_CASES_TAC THENL [AP_TERM_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `{x:real^N | a dot x = b}`]
        AFF_DIM_SUMS_INTER) THEN
    ASM_SIMP_TAC[AFFINE_HYPERPLANE; AFF_DIM_HYPERPLANE] THEN
    ASM_SIMP_TAC[AFFINE_HYPERPLANE_SUMS_EQ_UNIV; AFF_DIM_UNIV;
                 SET_RULE `~(s SUBSET t) ==> ~(s DIFF t = {})`] THEN
    SPEC_TAC(`aff_dim (s INTER {x:real^N | a dot x = b})`,`i:int`) THEN
    INT_ARITH_TAC]);;

let AFF_DIM_LT_FULL = prove
 (`!s. aff_dim s < &(dimindex(:N)) <=> ~(affine hull s = (:real^N))`,
  GEN_TAC THEN REWRITE_TAC[GSYM AFF_DIM_EQ_FULL] THEN
  MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_LE_UNIV) THEN ARITH_TAC);;

let AFF_LOWDIM_SUBSET_HYPERPLANE = prove
 (`!s:real^N->bool.
        aff_dim s < &(dimindex(:N))
        ==> ?a b. ~(a = vec 0) /\ s SUBSET {x | a dot x = b}`,
  MATCH_MP_TAC SET_PROVE_CASES THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `basis 1:real^N` THEN
    SIMP_TAC[EMPTY_SUBSET; BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1];
    MAP_EVERY X_GEN_TAC [`c:real^N`; `s:real^N->bool`] THEN
    CONV_TAC(ONCE_DEPTH_CONV(GEN_ALPHA_CONV `a:real^N`)) THEN
    GEN_GEOM_ORIGIN_TAC `c:real^N` ["a"] THEN
    SIMP_TAC[AFF_DIM_DIM_0; HULL_INC; IN_INSERT; INT_OF_NUM_LT] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP LOWDIM_SUBSET_HYPERPLANE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N` THEN
    STRIP_TAC THEN EXISTS_TAC `(u:real^N) dot c` THEN
    ASM_REWRITE_TAC[DOT_RADD; REAL_EQ_ADD_LCANCEL_0] THEN
    ASM_MESON_TAC[SPAN_INC; SUBSET_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* An additional lemma about hyperplanes.                                    *)
(* ------------------------------------------------------------------------- *)

let SUBSET_HYPERPLANES = prove
 (`!a b a' b'.
        {x | a dot x = b} SUBSET {x | a' dot x = b'} <=>
        {x | a dot x = b} = {} \/ {x | a' dot x = b'} = (:real^N) \/
        {x | a dot x = b} = {x | a' dot x = b'}`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `{x:real^N | a dot x = b} = {}` THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
  ASM_CASES_TAC `{x | a' dot x = b'} = (:real^N)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [HYPERPLANE_EQ_EMPTY; HYPERPLANE_EQ_UNIV]) THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  ASM_CASES_TAC `{x:real^N | a dot x = b} SUBSET {x | a' dot x = b'}` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`{x:real^N | a dot x = b}`; `{x:real^N | a' dot x = b'}`]
        AFF_DIM_PSUBSET) THEN
  ASM_SIMP_TAC[PSUBSET;
               REWRITE_RULE[GSYM AFFINE_HULL_EQ] AFFINE_HYPERPLANE] THEN
  ASM_CASES_TAC `{x:real^N | a dot x = b} = {x | a' dot x = b'}` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_CASES_TAC `a':real^N = vec 0` THENL
   [ASM_CASES_TAC `b' = &0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_CASES_TAC `b = &0` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_DIM_HYPERPLANE; INT_LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Openness and compactness are preserved by convex hull operation.          *)
(* ------------------------------------------------------------------------- *)

let OPEN_CONVEX_HULL = prove
 (`!s:real^N->bool. open s ==> open(convex hull s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONVEX_HULL_EXPLICIT; OPEN_CONTAINS_CBALL] THEN
  REWRITE_TAC[IN_ELIM_THM; SUBSET; LEFT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `t:real^N->bool`; `u:real^N->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?b. !x:real^N. x IN t ==> &0 < b(x) /\ cball(x,b(x)) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `i = IMAGE (b:real^N->real) t` THEN
  EXISTS_TAC `inf i` THEN MP_TAC(SPEC `i:real->bool` INF_FINITE) THEN
  EXPAND_TAC "i" THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_IMAGE] THEN
  ANTS_TAC THENL
   [EXPAND_TAC "i" THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    ASM_MESON_TAC[SUM_CLAUSES; REAL_ARITH `~(&1 = &0)`];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_CBALL; dist] THEN
  DISCH_TAC THEN EXISTS_TAC `IMAGE (\v:real^N. v + (y - a)) t` THEN
  EXISTS_TAC `\v. (u:real^N->real)(v - (y - a))` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; SUM_IMAGE; VSUM_IMAGE;
               VECTOR_ARITH `v + a:real^N = w + a <=> v = w`] THEN
  ASM_REWRITE_TAC[o_DEF; VECTOR_ARITH `(v + a) - a:real^N = v`] THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LDISTRIB; ETA_AX] THEN
  ASM_SIMP_TAC[VSUM_ADD; VSUM_RMUL] THEN
  CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `z + (y - a) IN cball(z:real^N,b z)`
   (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
  REWRITE_TAC[IN_CBALL; dist; NORM_ARITH
   `norm(z - (z + a - y)) = norm(y - a)`] THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

let COMPACT_CONVEX_COMBINATIONS = prove
 (`!s t. compact s /\ compact t
         ==> compact { (&1 - u) % x + u % y :real^N |
                      &0 <= u /\ u <= &1 /\ x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `{ (&1 - u) % x + u % y :real^N | &0 <= u /\ u <= &1 /\ x IN s /\ y IN t} =
    IMAGE (\z. (&1 - drop(fstcart z)) % fstcart(sndcart z) +
               drop(fstcart z) % sndcart(sndcart z))
          { pastecart u w | u IN interval[vec 0,vec 1] /\
                            w IN { pastecart x y | x IN s /\ y IN t} }`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV UNWIND_CONV) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[IN_INTERVAL_1; GSYM EXISTS_DROP; DROP_VEC] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[COMPACT_PCROSS; GSYM PCROSS; COMPACT_INTERVAL] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `z:real^(1,(N,N)finite_sum)finite_sum` THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[PCROSS] THEN
  MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
  CONJ_TAC THEN TRY(MATCH_MP_TAC CONTINUOUS_SUB) THEN
  REWRITE_TAC[CONTINUOUS_CONST] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART; ETA_AX] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC LINEAR_COMPOSE THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

let COMPACT_CONVEX_HULL = prove
 (`!s:real^N->bool. compact s ==> compact(convex hull s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CARATHEODORY] THEN
  SPEC_TAC(`dimindex(:N) + 1`,`n:num`) THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[SUBSET_EMPTY] THEN
    CONV_TAC(ONCE_DEPTH_CONV UNWIND_CONV) THEN
    REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
    REWRITE_TAC[SET_RULE `{x | F} = {}`; COMPACT_EMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `w:real^N`) THEN INDUCT_TAC THENL
   [SUBGOAL_THEN
     `{x:real^N | ?t. FINITE t /\ t SUBSET s /\ CARD t <= 0 /\
                      x IN convex hull t} = {}`
     (fun th -> REWRITE_TAC[th; COMPACT_EMPTY]) THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; LE; IN_ELIM_THM] THEN
    MESON_TAC[CARD_EQ_0; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `s <= SUC 0 <=> s = 0 \/ s = 1`] THEN
    UNDISCH_TAC `compact(s:real^N->bool)` THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    REWRITE_TAC[TAUT `a /\ b /\ (c \/ d) /\ e <=>
                      (a /\ c) /\ (b /\ e) \/ (a /\ d) /\ (b /\ e)`] THEN
    REWRITE_TAC[GSYM HAS_SIZE; num_CONV `1`; HAS_SIZE_CLAUSES] THEN
    REWRITE_TAC[EXISTS_OR_THM; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
    REWRITE_TAC[NOT_IN_EMPTY; CONVEX_HULL_EMPTY] THEN
    REWRITE_TAC[CONVEX_HULL_SING] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:real^N | ?t. FINITE t /\ t SUBSET s /\ CARD t <= SUC n /\
                    x IN convex hull t} =
    { (&1 - u) % x + u % y :real^N |
                      &0 <= u /\ u <= &1 /\ x IN s /\
                      y IN {x | ?t. FINITE t /\ t SUBSET s /\
                                    CARD t <= n /\ x IN convex hull t}}`
   (fun th -> ASM_SIMP_TAC[th; COMPACT_CONVEX_COMBINATIONS]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM;
                LEFT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `c:real`; `v:real^N`;
                         `t:real^N->bool`] THEN
    STRIP_TAC THEN EXISTS_TAC `(u:real^N) INSERT t` THEN
    ASM_REWRITE_TAC[FINITE_INSERT; INSERT_SUBSET] THEN
    ASM_SIMP_TAC[CARD_CLAUSES] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC IN_CONVEX_SET THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN CONJ_TAC THEN
    ASM_MESON_TAC[HULL_SUBSET; SUBSET; IN_INSERT; HULL_MONO]] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `CARD(t:real^N->bool) <= n` THENL
   [MAP_EVERY EXISTS_TAC [`w:real^N`; `&1`; `x:real^N`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->bool) HAS_SIZE (SUC n)` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `u:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  UNDISCH_TAC `(x:real^N) IN convex hull (a INSERT u)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FINITE_INSERT]) THEN
  ASM_CASES_TAC `(u:real^N->bool) = {}` THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `&1`; `a:real^N`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `{a:real^N}` THEN SIMP_TAC[FINITE_RULES] THEN
    REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `d:real`; `z:real^N`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `d:real`; `z:real^N`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
   `c + d = &1 ==> c = (&1 - d)`)) THEN
  ASM_REWRITE_TAC[REAL_ARITH `d <= &1 <=> &0 <= &1 - d`] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `CARD ((a:real^N) INSERT u) <= SUC n` THEN
  ASM_SIMP_TAC[CARD_CLAUSES; LE_SUC]);;

let FINITE_IMP_COMPACT_CONVEX_HULL = prove
 (`!s:real^N->bool. FINITE s ==> compact(convex hull s)`,
  SIMP_TAC[FINITE_IMP_COMPACT; COMPACT_CONVEX_HULL]);;

let CONVEX_HULL_INTERIOR_SUBSET = prove
 (`!s:real^N->bool. convex hull (interior s) SUBSET interior (convex hull s)`,
  GEN_TAC THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN
  SIMP_TAC[OPEN_CONVEX_HULL; OPEN_INTERIOR; HULL_MONO; INTERIOR_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Extremal points of a simplex are some vertices.                           *)
(* ------------------------------------------------------------------------- *)

let DIST_INCREASES_ONLINE = prove
 (`!a b d. ~(d = vec 0)
           ==> dist(a,b + d) > dist(a,b) \/ dist(a,b - d) > dist(a,b)`,
  REWRITE_TAC[dist; vector_norm; real_gt; GSYM NORM_POS_LT] THEN
  SIMP_TAC[SQRT_MONO_LT_EQ; DOT_POS_LE; SQRT_LT_0] THEN
  REWRITE_TAC[DOT_RSUB; DOT_RADD; DOT_LSUB; DOT_LADD] THEN REAL_ARITH_TAC);;

let NORM_INCREASES_ONLINE = prove
 (`!a:real^N d. ~(d = vec 0)
                ==> norm(a + d) > norm(a) \/ norm(a - d) > norm(a)`,
  MP_TAC(ISPEC `vec 0 :real^N` DIST_INCREASES_ONLINE) THEN
  REWRITE_TAC[dist; VECTOR_SUB_LZERO; NORM_NEG]);;

let SIMPLEX_FURTHEST_LT = prove
 (`!a:real^N s.
        FINITE s
        ==> !x. x IN (convex hull s) /\ ~(x IN s)
                ==> ?y. y IN (convex hull s) /\ norm(x - a) < norm(y - a)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `s:real^N->bool`] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT] THEN
  STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `v:real`; `b:real^N`] THEN
  ASM_CASES_TAC `y:real^N IN (convex hull s)` THENL
   [REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `c:real^N` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`; `c:real^N`] THEN
    ASM_REWRITE_TAC[REAL_ADD_LID; REAL_POS] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `u = &0` THENL
   [ASM_SIMP_TAC[REAL_ADD_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
    ASM_MESON_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_CASES_TAC `v = &0` THENL
   [ASM_SIMP_TAC[REAL_ADD_RID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_CASES_TAC `u = &1` THEN ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
    ASM_CASES_TAC `y = a:real^N` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:real`; `v:real`] REAL_DOWN2) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^N`; `y:real^N`; `w % (x - b):real^N`]
                DIST_INCREASES_ONLINE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[VECTOR_ARITH `(x - y = vec 0) <=> (x = y)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(y:real^N IN convex hull s)` THEN
    ASM_REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[dist; real_gt] THEN
  REWRITE_TAC[VECTOR_ARITH
   `((u % x + v % b) + w % (x - b) = (u + w) % x + (v - w) % b) /\
    ((u % x + v % b) - w % (x - b) = (u - w) % x + (v + w) % b)`] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`(u + w) % x + (v - w) % b:real^N`; `u + w`; `v - w`; `b:real^N`];
    MAP_EVERY EXISTS_TAC
     [`(u - w) % x + (v + w) % b:real^N`; `u - w`; `v + w`; `b:real^N`]] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
  UNDISCH_TAC `u + v = &1` THEN REAL_ARITH_TAC);;

let SIMPLEX_FURTHEST_LE = prove
 (`!a:real^N s.
        FINITE s /\ ~(s = {})
        ==> ?y. y IN s /\
                !x. x IN (convex hull s) ==> norm(x - a) <= norm(y - a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `convex hull (s:real^N->bool)` DISTANCE_ATTAINS_SUP) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMP_COMPACT_CONVEX_HULL] THEN
    ASM_MESON_TAC[SUBSET_EMPTY; HULL_SUBSET];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
  ASM_MESON_TAC[SIMPLEX_FURTHEST_LT; REAL_NOT_LE]);;

let SIMPLEX_FURTHEST_LE_EXISTS = prove
 (`!a:real^N s.
        FINITE s
        ==> !x. x IN (convex hull s)
                ==> ?y. y IN s /\ norm(x - a) <= norm(y - a)`,
  MESON_TAC[NOT_IN_EMPTY; CONVEX_HULL_EMPTY; SIMPLEX_FURTHEST_LE]);;

let SIMPLEX_EXTREMAL_LE = prove
 (`!s:real^N->bool.
        FINITE s /\ ~(s = {})
         ==> ?u v. u IN s /\ v IN s /\
                   !x y. x IN convex hull s /\ y IN convex hull s
                         ==> norm(x - y) <= norm(u - v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `convex hull (s:real^N->bool)` COMPACT_SUP_MAXDISTANCE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMP_COMPACT_CONVEX_HULL] THEN
    ASM_MESON_TAC[SUBSET_EMPTY; HULL_SUBSET];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  SIMP_TAC[] THEN ASM_MESON_TAC[SIMPLEX_FURTHEST_LT; REAL_NOT_LE; NORM_SUB]);;

let SIMPLEX_EXTREMAL_LE_EXISTS = prove
 (`!s:real^N->bool x y. FINITE s /\ x IN convex hull s /\ y IN convex hull s
                        ==> ?u v. u IN s /\ v IN s /\
                                  norm(x - y) <= norm(u - v)`,
  MESON_TAC[NOT_IN_EMPTY; CONVEX_HULL_EMPTY; SIMPLEX_EXTREMAL_LE]);;

let DIAMETER_CONVEX_HULL = prove
 (`!s:real^N->bool. diameter(convex hull s) = diameter s`,
  let lemma = prove
   (`!a b s. (!x. x IN s ==> dist(a,x) <= b)
             ==> (!x. x IN convex hull s ==> dist(a,x) <= b)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC HULL_INDUCT THEN ASM_REWRITE_TAC[GSYM cball; CONVEX_CBALL]) in
  GEN_TAC THEN REWRITE_TAC[diameter; CONVEX_HULL_EQ_EMPTY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUP_EQ THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `b:real` THEN
  EQ_TAC THENL [MESON_TAC[SUBSET; HULL_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `!b. (a ==> b) /\ (b ==> c) ==> a ==> c`) THEN
  EXISTS_TAC `!x:real^N y. x IN s /\ y IN convex hull s ==> norm(x - y) <= b`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM dist; lemma];
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:real^N` THEN
    ASM_CASES_TAC `(y:real^N) IN convex hull s` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[DIST_SYM] dist); lemma]]);;

let DIAMETER_SIMPLEX = prove
 (`!s:real^N->bool.
        ~(s = {})
        ==> diameter(convex hull s) = sup { dist(x,y) | x IN s /\ y IN s}`,
  REWRITE_TAC[DIAMETER_CONVEX_HULL] THEN SIMP_TAC[diameter; dist]);;

(* ------------------------------------------------------------------------- *)
(* Closest point of a convex set is unique, with a continuous projection.    *)
(* ------------------------------------------------------------------------- *)

let CLOSER_POINTS_LEMMA = prove
 (`!y:real^N z.
        y dot z > &0
        ==> ?u. &0 < u /\
                !v. &0 < v /\ v <= u ==> norm(v % z - y) < norm y`,
  REWRITE_TAC[NORM_LT; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL;
              REAL_SUB_LDISTRIB; real_gt] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `(a - b) - (c - d) < d <=> a < b + c`] THEN
  STRIP_TAC THEN SUBST1_TAC(VECTOR_ARITH `(z:real^N) dot y = y dot z`) THEN
  SIMP_TAC[GSYM REAL_ADD_LDISTRIB; REAL_LT_LMUL_EQ] THEN
  EXISTS_TAC `(y dot (z:real^N)) / (z dot z)` THEN
  SUBGOAL_THEN `&0 < z dot (z:real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DOT_POS_LT; DOT_RZERO; REAL_LT_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_RDIV_EQ] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < y /\ x <= y ==> x < y + y`; REAL_LT_MUL]);;

let CLOSER_POINT_LEMMA = prove
 (`!x y z. (y - x) dot (z - x) > &0
           ==> ?u. &0 < u /\ u <= &1 /\ dist(x + u % (z - x),y) < dist(x,y)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CLOSER_POINTS_LEMMA) THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist; NORM_LT] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(y - (x + z)) dot (y - (x + z)) = (z - (y - x)) dot (z - (y - x))`] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min u (&1)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LT_01; REAL_LE_REFL]);;

let ANY_CLOSEST_POINT_DOT = prove
 (`!s a x y:real^N.
        convex s /\ closed s /\ x IN s /\ y IN s /\
        (!z. z IN s ==> dist(a,x) <= dist(a,z))
        ==> (a - x) dot (y - x) <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ARITH `x <= &0 <=> ~(x > &0)`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLOSER_POINT_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[REAL_NOT_LT] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `x + u % (y - x) = (&1 - u) % x + u % y`] THEN
  MATCH_MP_TAC IN_CONVEX_SET THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let ANY_CLOSEST_POINT_UNIQUE = prove
 (`!s a x y:real^N.
        convex s /\ closed s /\ x IN s /\ y IN s /\
        (!z. z IN s ==> dist(a,x) <= dist(a,z)) /\
        (!z. z IN s ==> dist(a,y) <= dist(a,z))
        ==> x = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM NORM_LE_0; NORM_LE_SQUARE] THEN
  SUBGOAL_THEN `(a - x:real^N) dot (y - x) <= &0 /\ (a - y) dot (x - y) <= &0`
  MP_TAC THENL [ASM_MESON_TAC[ANY_CLOSEST_POINT_DOT]; ALL_TAC] THEN
  REWRITE_TAC[NORM_LT; DOT_LSUB; DOT_RSUB] THEN REAL_ARITH_TAC);;

let CLOSEST_POINT_UNIQUE = prove
 (`!s a x:real^N.
        convex s /\ closed s /\ x IN s /\
        (!z. z IN s ==> dist(a,x) <= dist(a,z))
        ==> x = closest_point s a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ANY_CLOSEST_POINT_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `a:real^N`] THEN
  ASM_MESON_TAC[CLOSEST_POINT_EXISTS; MEMBER_NOT_EMPTY]);;

let CLOSEST_POINT_DOT = prove
 (`!s a x:real^N.
        convex s /\ closed s /\ x IN s
        ==> (a - closest_point s a) dot (x - closest_point s a) <= &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ANY_CLOSEST_POINT_DOT THEN
  EXISTS_TAC `s:real^N->bool` THEN
  ASM_MESON_TAC[CLOSEST_POINT_EXISTS; MEMBER_NOT_EMPTY]);;

let CLOSEST_POINT_LT = prove
 (`!s a x. convex s /\ closed s /\ x IN s /\ ~(x = closest_point s a)
           ==> dist(a,closest_point s a) < dist(a,x)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE; CONTRAPOS_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC CLOSEST_POINT_UNIQUE THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CLOSEST_POINT_LE; REAL_LE_TRANS]);;

let CLOSEST_POINT_LIPSCHITZ = prove
 (`!s x y:real^N.
        convex s /\ closed s /\ ~(s = {})
        ==> dist(closest_point s x,closest_point s y) <= dist(x,y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dist; NORM_LE] THEN
  SUBGOAL_THEN
   `(x - closest_point s x :real^N) dot
    (closest_point s y - closest_point s x) <= &0 /\
    (y - closest_point s y) dot
    (closest_point s x - closest_point s y) <= &0`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ANY_CLOSEST_POINT_DOT THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[CLOSEST_POINT_EXISTS];
    MP_TAC(ISPEC `(x - closest_point s x :real^N) - (y - closest_point s y)`
                 DOT_POS_LE) THEN
    REWRITE_TAC[NORM_LT; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN REAL_ARITH_TAC]);;

let CONTINUOUS_AT_CLOSEST_POINT = prove
 (`!s x. convex s /\ closed s /\ ~(s = {})
         ==> (closest_point s) continuous (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_at] THEN
  ASM_MESON_TAC[CLOSEST_POINT_LIPSCHITZ; REAL_LET_TRANS]);;

let CONTINUOUS_ON_CLOSEST_POINT = prove
 (`!s t. convex s /\ closed s /\ ~(s = {})
         ==> (closest_point s) continuous_on t`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CLOSEST_POINT]);;

(* ------------------------------------------------------------------------- *)
(* Relating closest points and orthogonality.                                *)
(* ------------------------------------------------------------------------- *)

let ANY_CLOSEST_POINT_AFFINE_ORTHOGONAL = prove
 (`!s a b:real^N.
        affine s /\ b IN s /\ (!x. x IN s ==> dist(a,b) <= dist(a,x))
        ==> (!x. x IN s ==> orthogonal (x - b) (a - b))`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `b:real^N` THEN
  REWRITE_TAC[DIST_0; VECTOR_SUB_RZERO; orthogonal; dist; NORM_LE] THEN
  REWRITE_TAC[DOT_LSUB] THEN REWRITE_TAC[DOT_RSUB] THEN
  REWRITE_TAC[DOT_SYM; REAL_ARITH `a <= a - y - (y - x) <=> &2 * y <= x`] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_RZERO] THEN FIRST_X_ASSUM(fun th ->
   MP_TAC(SPEC `vec 0 + --((a dot x) / (x dot x)) % (x - vec 0:real^N)` th) THEN
   MP_TAC(SPEC `vec 0 + (a dot x) / (x dot x) % (x - vec 0:real^N)` th)) THEN
  ASM_SIMP_TAC[IN_AFFINE_ADD_MUL_DIFF] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; VECTOR_ADD_LID; DOT_RMUL] THEN
  REWRITE_TAC[DOT_LMUL; IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `&2 * x * a <= b * c * z /\ &2 * --x * a <= --b * --c * z
    ==> &2 * abs(x * a) <= b * c * z`)) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_NOT_LE; REAL_DIV_RMUL; DOT_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `~(x = &0) ==> x < &2 * abs x`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM DOT_EQ_0]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let ORTHOGONAL_ANY_CLOSEST_POINT = prove
 (`!s a b:real^N.
        b IN s /\ (!x. x IN s ==> orthogonal (x - b) (a - b))
        ==> (!x. x IN s ==> dist(a,b) <= dist(a,x))`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `b:real^N` THEN
  REWRITE_TAC[dist; NORM_LE; orthogonal; VECTOR_SUB_RZERO] THEN
  SIMP_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  REWRITE_TAC[DOT_POS_LE; REAL_ARITH `a <= a - &0 - (&0 - x) <=> &0 <= x`]);;

let CLOSEST_POINT_AFFINE_ORTHOGONAL = prove
 (`!s a:real^N x.
        affine s /\ ~(s = {}) /\ x IN s
        ==> orthogonal (x - closest_point s a) (a - closest_point s a)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC ANY_CLOSEST_POINT_AFFINE_ORTHOGONAL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSEST_POINT_EXISTS THEN
  ASM_SIMP_TAC[CLOSED_AFFINE]);;

let CLOSEST_POINT_AFFINE_ORTHOGONAL_EQ = prove
 (`!s a b:real^N.
        affine s /\ b IN s
        ==> (closest_point s a = b <=>
             !x. x IN s ==> orthogonal (x - b) (a - b))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[CLOSEST_POINT_AFFINE_ORTHOGONAL; MEMBER_NOT_EMPTY];
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CLOSEST_POINT_UNIQUE THEN
    ASM_SIMP_TAC[CLOSED_AFFINE; AFFINE_IMP_CONVEX] THEN
    MATCH_MP_TAC ORTHOGONAL_ANY_CLOSEST_POINT THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Various point-to-set separating/supporting hyperplane theorems.           *)
(* ------------------------------------------------------------------------- *)

let SUPPORTING_HYPERPLANE_COMPACT_POINT_SUP = prove
 (`!a c s:real^N->bool.
        compact s /\ ~(s = {})
        ==> ?b y. y IN s /\ a dot (y - c) = b /\
                  (!x. x IN s ==> a dot (x - c) <= b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. a dot (x - c)`; `s:real^N->bool`]
        CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  SUBGOAL_THEN `(\x:real^N. a dot (x - c)) = (\x. a dot x) o (\x. x - c)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[CONTINUOUS_ON_LIFT_DOT; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
           CONTINUOUS_ON_ID]);;

let SUPPORTING_HYPERPLANE_COMPACT_POINT_INF = prove
 (`!a c s:real^N->bool.
        compact s /\ ~(s = {})
        ==> ?b y. y IN s /\ a dot (y - c) = b /\
                  (!x. x IN s ==> a dot (x - c) >= b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`--a:real^N`; `c:real^N`; `s:real^N->bool`]
    SUPPORTING_HYPERPLANE_COMPACT_POINT_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real`
   (fun th -> EXISTS_TAC `--b:real` THEN MP_TAC th)) THEN
  REWRITE_TAC[DOT_LNEG; REAL_ARITH `x >= -- b <=> --x <= b`] THEN
  REWRITE_TAC[REAL_NEG_EQ]);;

let SUPPORTING_HYPERPLANE_CLOSED_POINT = prove
 (`!s z:real^N. convex s /\ closed s /\ ~(s = {}) /\ ~(z IN s)
                ==> ?a b y. a dot z < b /\ y IN s /\ (a dot y = b) /\
                            (!x. x IN s ==> a dot x >= b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `z:real^N`] DISTANCE_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y - z:real^N` THEN EXISTS_TAC `(y - z:real^N) dot y` THEN
  EXISTS_TAC `y:real^N` THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  ASM_REWRITE_TAC[GSYM DOT_RSUB; DOT_POS_LT; VECTOR_SUB_EQ] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_TAC THEN SUBGOAL_THEN
   `!u. &0 <= u /\ u <= &1 ==> dist(z:real^N,y) <= dist(z,(&1 - u) % y + u % x)`
  MP_TAC THENL [ASM_MESON_TAC[CONVEX_ALT]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  REWRITE_TAC[real_ge; REAL_NOT_LE; NOT_FORALL_THM; NOT_IMP] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `x < y <=> y - x > &0`] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a - b) dot x - (a - b) dot y = (b - a) dot (y - x)`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLOSER_POINT_LEMMA) THEN
  REWRITE_TAC[VECTOR_ARITH `y + u % (x - y) = (&1 - u) % y + u % x`] THEN
  MESON_TAC[REAL_LT_IMP_LE]);;

let SEPARATING_HYPERPLANE_CLOSED_POINT_INSET = prove
 (`!s z:real^N. convex s /\ closed s /\ ~(s = {}) /\ ~(z IN s)
                ==> ?a b. a IN s /\
                          (a - z) dot z < b /\
                          (!x. x IN s ==> (a - z) dot x > b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `z:real^N`] DISTANCE_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(y - z:real^N) dot z + norm(y - z) pow 2 / &2` THEN
  SUBGOAL_THEN `&0 < norm(y - z:real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_ADDR; REAL_LT_DIV; REAL_POW_LT;
               REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[NORM_POW_2; REAL_ARITH `a > b + c <=> c < a - b`] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[VECTOR_ARITH
   `((y - z) dot x - (y - z) dot z) * &2 - (y - z) dot (y - z) =
    &2 * ((y - z) dot (x - y)) + (y - z) dot (y - z)`] THEN
  MATCH_MP_TAC(REAL_ARITH `~(--x > &0) /\ &0 < y ==> &0 < &2 * x + y`) THEN
  ASM_SIMP_TAC[GSYM NORM_POW_2; REAL_POW_LT] THEN
  REWRITE_TAC[GSYM DOT_LNEG; VECTOR_NEG_SUB] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLOSER_POINT_LEMMA) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[REAL_NOT_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `y + u % (x - y) = (&1 - u) % y + u % x`] THEN
  ASM_MESON_TAC[CONVEX_ALT; REAL_LT_IMP_LE]);;

let SEPARATING_HYPERPLANE_CLOSED_0_INSET = prove
 (`!s:real^N->bool.
        convex s /\ closed s /\ ~(s = {}) /\ ~(vec 0 IN s)
        ==> ?a b. a IN s /\ ~(a = vec 0) /\ &0 < b /\
                  (!x. x IN s ==> a dot x > b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SEPARATING_HYPERPLANE_CLOSED_POINT_INSET) THEN
  REWRITE_TAC[DOT_RZERO; real_gt] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  SIMP_TAC[VECTOR_SUB_RZERO] THEN ASM_MESON_TAC[]);;

let SEPARATING_HYPERPLANE_CLOSED_POINT = prove
 (`!s z:real^N. convex s /\ closed s /\ ~(z IN s)
                ==> ?a b. a dot z < b /\ (!x. x IN s ==> a dot x > b)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`--z:real^N`; `&1`] THEN
    SIMP_TAC[DOT_LNEG; REAL_ARITH `&0 <= x ==> --x < &1`; DOT_POS_LE] THEN
    ASM_MESON_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
  ASM_MESON_TAC[SEPARATING_HYPERPLANE_CLOSED_POINT_INSET]);;

let SEPARATING_HYPERPLANE_CLOSED_0 = prove
 (`!s:real^N->bool.
        convex s /\ closed s /\ ~(vec 0 IN s)
        ==> ?a b. ~(a = vec 0) /\ &0 < b /\ (!x. x IN s ==> a dot x > b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [EXISTS_TAC `basis 1:real^N` THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01; GSYM NORM_POS_LT] THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_LT_01];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
    REWRITE_TAC[DOT_RZERO; real_gt] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY; DOT_LZERO; REAL_LT_ANTISYM]]);;

(* ------------------------------------------------------------------------- *)
(* Now set-to-set for closed/compact sets.                                   *)
(* ------------------------------------------------------------------------- *)

let SEPARATING_HYPERPLANE_CLOSED_COMPACT = prove
 (`!s t. convex s /\ closed s /\
         convex t /\ compact t /\ ~(t = {}) /\ DISJOINT s t
         ==> ?a:real^N b. (!x. x IN s ==> a dot x < b) /\
                          (!x. x IN t ==> a dot x > b)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?z:real^N. norm(z) = b + &1` CHOOSE_TAC THENL
     [ASM_SIMP_TAC[VECTOR_CHOOSE_SIZE; REAL_ARITH `&0 < b ==> &0 <= b + &1`];
      ALL_TAC] THEN
    MP_TAC(SPECL [`t:real^N->bool`; `z:real^N`]
       SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
    ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    ASM_MESON_TAC[REAL_ARITH `~(b + &1 <= b)`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x - y:real^N | x IN s /\ y IN t}`; `vec 0 :real^N`]
                SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
  ASM_SIMP_TAC[CLOSED_COMPACT_DIFFERENCES; CONVEX_DIFFERENCES] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN
    ASM_MESON_TAC[DISJOINT; NOT_IN_EMPTY; IN_INTER; EXTENSION];
    ALL_TAC] THEN
  SIMP_TAC[DOT_RZERO; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SWAP_FORALL_THM] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL; DOT_RSUB] THEN
  REWRITE_TAC[real_gt; REAL_LT_SUB_LADD] THEN DISCH_TAC THEN
  EXISTS_TAC `--a:real^N` THEN
  MP_TAC(SPEC `IMAGE (\x:real^N. a dot x) t` SUP) THEN
  ABBREV_TAC `k = sup (IMAGE (\x:real^N. a dot x) t)` THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `b + x < y ==> x <= y - b`; MEMBER_NOT_EMPTY];
    ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `--(k + b / &2)` THEN
  REWRITE_TAC[DOT_LNEG; REAL_LT_NEG2] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH;
               REAL_ARITH `&0 < b /\ x <= k ==> x < k + b`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k - b / &2`) THEN
  ASM_SIMP_TAC[REAL_ARITH `k <= k - b2 <=> ~(&0 < b2)`; REAL_LT_DIV;
     REAL_OF_NUM_LT; ARITH; NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH
   `!b. (b2 + b2 = b) /\ b + ay < ax ==> ~(ay <= k - b2) ==> k + b2 < ax`) THEN
  ASM_MESON_TAC[REAL_HALF]);;

let SEPARATING_HYPERPLANE_COMPACT_CLOSED = prove
 (`!s t. convex s /\ compact s /\ ~(s = {}) /\
         convex t /\ closed t /\ DISJOINT s t
         ==> ?a:real^N b. (!x. x IN s ==> a dot x < b) /\
                          (!x. x IN t ==> a dot x > b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `s:real^N->bool`]
      SEPARATING_HYPERPLANE_CLOSED_COMPACT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DISJOINT_SYM]; ALL_TAC] THEN
  REWRITE_TAC[real_gt] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`--a:real^N`; `--b:real`] THEN
  ASM_REWRITE_TAC[REAL_LT_NEG2; DOT_LNEG]);;

let SEPARATING_HYPERPLANE_COMPACT_CLOSED_NONZERO = prove
 (`!s t:real^N->bool.
           convex s /\ compact s /\ ~(s = {}) /\
           convex t /\ closed t /\ DISJOINT s t
           ==> ?a b. ~(a = vec 0) /\
                     (!x. x IN s ==> a dot x < b) /\
                     (!x. x IN t ==> a dot x > b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN STRIP_TAC THEN
    EXISTS_TAC `basis 1:real^N` THEN
    SUBGOAL_THEN
     `bounded(IMAGE (\x:real^N. lift(basis 1 dot x)) s)`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_DOT];
      REWRITE_TAC[BOUNDED_POS_LT; FORALL_IN_IMAGE; NORM_LIFT] THEN
      SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN
      MESON_TAC[REAL_ARITH `abs x < b ==> x < b`]];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
        SEPARATING_HYPERPLANE_COMPACT_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    ASM_CASES_TAC `a:real^N = vec 0` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DOT_LZERO; real_gt] THEN
    ASM_MESON_TAC[REAL_LT_ANTISYM; MEMBER_NOT_EMPTY]]);;

let SEPARATING_HYPERPLANE_COMPACT_COMPACT = prove
 (`!s t:real^N->bool.
           convex s /\ compact s /\ convex t /\ compact t /\ DISJOINT s t
           ==> ?a b. ~(a = vec 0) /\
                     (!x. x IN s ==> a dot x < b) /\
                     (!x. x IN t ==> a dot x > b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN STRIP_TAC THEN
    EXISTS_TAC `--basis 1:real^N` THEN
    SUBGOAL_THEN
     `bounded(IMAGE (\x:real^N. lift(basis 1 dot x)) t)`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_DOT];
      REWRITE_TAC[BOUNDED_POS_LT; FORALL_IN_IMAGE; NORM_LIFT] THEN
      SIMP_TAC[VECTOR_NEG_EQ_0; BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `--b:real` THEN REWRITE_TAC[DOT_LNEG] THEN
      REWRITE_TAC[REAL_ARITH `--x > --y <=> x < y`] THEN
      ASM_MESON_TAC[REAL_ARITH `abs x < b ==> x < b`]];
    STRIP_TAC THEN
    MATCH_MP_TAC SEPARATING_HYPERPLANE_COMPACT_CLOSED_NONZERO THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]);;

(* ------------------------------------------------------------------------- *)
(* General case without assuming closure and getting non-strict separation.  *)
(* ------------------------------------------------------------------------- *)

let SEPARATING_HYPERPLANE_SET_0_INSPAN = prove
 (`!s:real^N->bool.
        convex s /\ ~(s = {}) /\ ~(vec 0 IN s)
        ==> ?a b. a IN span s /\ ~(a = vec 0) /\
                  !x. x IN s ==> &0 <= a dot x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `k = \c:real^N. {x | &0 <= c dot x}` THEN
  SUBGOAL_THEN
   `~((span s INTER frontier(cball(vec 0:real^N,&1))) INTER
      (INTERS (IMAGE k (s:real^N->bool))) = {})`
  MP_TAC THENL
   [ALL_TAC;
    SIMP_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_INTERS; NOT_FORALL_THM;
             FORALL_IN_IMAGE; FRONTIER_CBALL; REAL_LT_01] THEN
    EXPAND_TAC "k" THEN REWRITE_TAC[IN_SPHERE_0; IN_ELIM_THM; NORM_NEG] THEN
    MESON_TAC[NORM_EQ_0; REAL_ARITH `~(&1 = &0)`; DOT_SYM]] THEN
  MATCH_MP_TAC COMPACT_IMP_FIP THEN
  SIMP_TAC[COMPACT_CBALL; COMPACT_FRONTIER; FORALL_IN_IMAGE;
           CLOSED_INTER_COMPACT; CLOSED_SPAN] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[GSYM real_ge; CLOSED_HALFSPACE_GE];
    ALL_TAC] THEN
  REWRITE_TAC[FINITE_SUBSET_IMAGE] THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` MP_TAC) THEN
  ASM_CASES_TAC `c:real^N->bool = {}` THENL
   [ASM_SIMP_TAC[INTERS_0; INTER_UNIV; IMAGE_CLAUSES] THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    SUBGOAL_THEN `~(a:real^N = vec 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `inv(norm a) % a:real^N` THEN
    ASM_SIMP_TAC[IN_INTER; FRONTIER_CBALL; SPAN_CLAUSES; IN_SPHERE_0] THEN
    REWRITE_TAC[DIST_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `convex hull (c:real^N->bool)`
      SEPARATING_HYPERPLANE_CLOSED_0_INSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN
    ASM_MESON_TAC[CONVEX_CONVEX_HULL; SUBSET; SUBSET_HULL; HULL_SUBSET;
                  FINITE_IMP_COMPACT_CONVEX_HULL; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_RZERO; real_gt] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_INTERS; FORALL_IN_IMAGE] THEN
  EXPAND_TAC "k" THEN SIMP_TAC[IN_ELIM_THM; FRONTIER_CBALL; REAL_LT_01] THEN
  REWRITE_TAC[dist; VECTOR_SUB_LZERO; NORM_NEG] THEN
  EXISTS_TAC `inv(norm(a)) % a:real^N` THEN REWRITE_TAC[DOT_RMUL] THEN
  SUBGOAL_THEN `(a:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; HULL_MINIMAL]; ASM_SIMP_TAC[SPAN_CLAUSES]] THEN
  REWRITE_TAC[IN_SPHERE_0; VECTOR_SUB_LZERO; NORM_NEG; NORM_MUL] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NORM] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_EQ_LDIV_EQ; NORM_POS_LT] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
  ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS; HULL_SUBSET; SUBSET; DOT_SYM]);;

let SEPARATING_HYPERPLANE_SET_POINT_INAFF = prove
 (`!s z:real^N.
        convex s /\ ~(s = {}) /\ ~(z IN s)
        ==> ?a b. (z + a) IN affine hull (z INSERT s) /\ ~(a = vec 0) /\
                  a dot z <= b /\ (!x. x IN s ==> a dot x >= b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. --z + x) s`
     SEPARATING_HYPERPLANE_SET_0_INSPAN) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; CONVEX_TRANSLATION; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[IN_IMAGE; VECTOR_ARITH `vec 0:real^N = --z + x <=> x = z`] THEN
  ASM_SIMP_TAC[UNWIND_THM2; AFFINE_HULL_INSERT_SPAN; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  REWRITE_TAC[GSYM SIMPLE_IMAGE; VECTOR_ARITH `--x + y:real^N = y - x`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(a:real^N) dot z` THEN REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[REAL_ARITH `x >= y <=> &0 <= x - y`; GSYM DOT_RSUB]);;

let SEPARATING_HYPERPLANE_SET_0 = prove
 (`!s:real^N->bool.
        convex s /\ ~(vec 0 IN s)
        ==> ?a b. ~(a = vec 0) /\ !x. x IN s ==> &0 <= a dot x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    MESON_TAC[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1];
    ASM_MESON_TAC[SEPARATING_HYPERPLANE_SET_0_INSPAN]]);;

let SEPARATING_HYPERPLANE_SETS = prove
 (`!s t. convex s /\ convex t /\ ~(s = {}) /\ ~(t = {}) /\ DISJOINT s t
         ==> ?a:real^N b. ~(a = vec 0) /\
                          (!x. x IN s ==> a dot x <= b) /\
                          (!x. x IN t ==> a dot x >= b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{y - x:real^N | y IN t /\ x IN s}`
                SEPARATING_HYPERPLANE_SET_0) THEN
  ASM_SIMP_TAC[CONVEX_DIFFERENCES] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN
    ASM_MESON_TAC[DISJOINT; NOT_IN_EMPTY; IN_INTER; EXTENSION];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SWAP_FORALL_THM] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL; DOT_RSUB; REAL_SUB_LE] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `IMAGE (\x:real^N. a dot x) s` SUP) THEN
  ABBREV_TAC `k = sup (IMAGE (\x:real^N. a dot x) s)` THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY; real_ge] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* More convexity generalities.                                              *)
(* ------------------------------------------------------------------------- *)

let CONVEX_CLOSURE = prove
 (`!s:real^N->bool. convex s ==> convex(closure s)`,
  REWRITE_TAC[convex; CLOSURE_SEQUENTIAL] THEN
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:num->real^N`) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `b:num->real^N`) MP_TAC) THEN
  STRIP_TAC THEN EXISTS_TAC `\n:num. u % a(n) + v % b(n) :real^N` THEN
  ASM_SIMP_TAC[LIM_ADD; LIM_CMUL]);;

let CONVEX_INTERIOR = prove
 (`!s:real^N->bool. convex s ==> convex(interior s)`,
  REWRITE_TAC[CONVEX_ALT; IN_INTERIOR; SUBSET; IN_BALL; dist] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `d:real`) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e:real`) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d e` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  SUBST1_TAC(VECTOR_ARITH `z:real^N =
   (&1 - u) % (z - u % (y - x)) + u % (z + (&1 - u) % (y - x))`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[VECTOR_ARITH `x - (z - u % (y - x)) =
                                ((&1 - u) % x + u % y) - z:real^N`;
                VECTOR_ARITH `y - (z + (&1 - u) % (y - x)) =
                                ((&1 - u) % x + u % y) - z:real^N`]);;

let CONVEX_ON_SETDIST = prove
 (`!s t:real^N->bool. convex t ==> (\x. setdist ({x},t)) convex_on s`,
  SUBGOAL_THEN
   `!s t:real^N->bool. convex t /\ closed t
                       ==> (\x. setdist ({x},t)) convex_on s`
  MP_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
      SPECL [`s:real^N->bool`; `closure t:real^N->bool`]) THEN
    ASM_SIMP_TAC[CLOSED_CLOSURE; SETDIST_CLOSURE; CONVEX_CLOSURE]] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[convex_on] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[SETDIST_EMPTY; REAL_MUL_RZERO; REAL_ADD_RID; REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`{x:real^N}`; `t:real^N->bool`] SETDIST_COMPACT_CLOSED) THEN
  MP_TAC(ISPECL [`{y:real^N}`; `t:real^N->bool`] SETDIST_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY; COMPACT_SING; UNWIND_THM2; SETDIST_CLOSURE;
                  CLOSURE_EQ_EMPTY; RIGHT_EXISTS_AND_THM; IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^N` (STRIP_ASSUME_TAC o GSYM)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^N` (STRIP_ASSUME_TAC o GSYM)) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `dist(u % x + v % y:real^N,u % x' + v % y')` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SETDIST_LE_DIST THEN REWRITE_TAC[IN_SING] THEN
    ASM_MESON_TAC[convex];
    REWRITE_TAC[dist] THEN MATCH_MP_TAC(NORM_ARITH
     `norm(a - a':real^N) + norm(b - b') <= r
      ==> norm((a + b) - (a' + b')) <= r`) THEN
    ASM_REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL; dist] THEN
    ASM_REWRITE_TAC[real_abs; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Moving and scaling convex hulls.                                          *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_TRANSLATION = prove
 (`!a:real^N s.
       convex hull (IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (convex hull s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HULL_IMAGE THEN
  REWRITE_TAC[CONVEX_TRANSLATION_EQ; CONVEX_CONVEX_HULL] THEN
  REWRITE_TAC[VECTOR_ARITH `a + x:real^N = y <=> x = y - a`; EXISTS_REFL] THEN
  VECTOR_ARITH_TAC);;

add_translation_invariants [CONVEX_HULL_TRANSLATION];;

let CONVEX_HULL_SCALING = prove
 (`!s:real^N->bool c.
       convex hull (IMAGE (\x. c % x) s) = IMAGE (\x. c % x) (convex hull s)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = &0` THENL
   [ASM_SIMP_TAC[IMAGE_CONST; VECTOR_MUL_LZERO; CONVEX_HULL_EQ_EMPTY] THEN
    COND_CASES_TAC THEN REWRITE_TAC[CONVEX_HULL_EMPTY; CONVEX_HULL_SING];
    ALL_TAC] THEN
  MATCH_MP_TAC HULL_IMAGE THEN
  ASM_SIMP_TAC[CONVEX_SCALING_EQ; CONVEX_CONVEX_HULL] THEN
  REWRITE_TAC[VECTOR_ARITH `c % x = c % y <=> c % (x - y) = vec 0`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
  X_GEN_TAC `x:real^N` THEN EXISTS_TAC `inv c % x:real^N` THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID]);;

let CONVEX_HULL_AFFINITY = prove
 (`!s a:real^N c.
        convex hull (IMAGE (\x. a + c % x) s) =
        IMAGE (\x. a + c % x) (convex hull s)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; CONVEX_HULL_TRANSLATION; CONVEX_HULL_SCALING]);;

(* ------------------------------------------------------------------------- *)
(* Convex set as intersection of halfspaces.                                 *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HALFSPACE_INTERSECTION = prove
 (`!s. closed(s:real^N->bool) /\ convex s
       ==> s = INTERS {h | s SUBSET h /\ ?a b. h = {x | a dot x <= b}}`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTERS] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[MESON[] `(!t. (P t /\ ?a b. t = x a b) ==> Q t) <=>
                       (!a b. P(x a b) ==> Q(x a b))`] THEN
  EQ_TAC THENL [SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
    SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`--a:real^N`; `--b:real`]) THEN
  ASM_SIMP_TAC[SUBSET; IN_ELIM_THM; DOT_LNEG; NOT_IMP] THEN
  ASM_SIMP_TAC[REAL_LE_NEG2; REAL_LT_NEG2; REAL_NOT_LE;
               REAL_ARITH `a > b ==> b <= a`]);;

(* ------------------------------------------------------------------------- *)
(* Radon's theorem (from Lars Schewe).                                       *)
(* ------------------------------------------------------------------------- *)

let RADON_EX_LEMMA = prove
 (`!(c:real^N->bool).
        FINITE c /\ affine_dependent c
        ==> (?u. sum c u = &0 /\ (?v. v IN c /\ ~(u v = &0)) /\
                                      vsum c (\v. u v % v) = (vec 0):real^N)`,
  REWRITE_TAC[AFFINE_DEPENDENT_EXPLICIT] THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\v:real^N. if v IN s then u v else &0` THEN
  ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[COND_RAND;COND_RATOR;
               VECTOR_MUL_LZERO;GSYM VSUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SET_RULE `s SUBSET c ==> {x | x IN c /\ x IN s} = s`] THEN
  EXISTS_TAC `v:real^N` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let RADON_S_LEMMA = prove
 (`!(s:A->bool) f.
        FINITE s /\ sum s f = &0
        ==> sum {x | x IN s /\ &0 < f x} f =
            -- sum {x | x IN s /\ f x < &0} f`,
  REWRITE_TAC[REAL_ARITH `a = --b <=> a + b = &0`] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FINITE_RESTRICT;GSYM SUM_UNION;
    REWRITE_RULE [REAL_ARITH `&0 < f x ==> ~(f x < &0)`]
     (SET_RULE `(!x:A. &0 < f x ==> ~(f x < &0))
                ==>  DISJOINT {x | x IN s /\ &0 < f x}
                              {x | x IN s /\ f x < &0}`)] THEN
  MATCH_MP_TAC (REAL_ARITH `!a b.a = &0 /\ a + b = &0 ==> b = &0`) THEN
  EXISTS_TAC `sum {x:A | x IN s /\ f x = &0} f` THEN
  CONJ_TAC THENL
  [ASM_SIMP_TAC[SUM_RESTRICT_SET] THEN REWRITE_TAC[COND_ID;SUM_0];
   ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT {x:A | x IN s /\ f x = &0}
                         ({x | x IN s /\ &0 < f x} UNION
                          {x | x IN s /\ f x < &0})` ASSUME_TAC THENL
  [REWRITE_TAC[DISJOINT;UNION;INTER;IN_ELIM_THM;EXTENSION;NOT_IN_EMPTY] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
   ASM_SIMP_TAC[FINITE_UNION;FINITE_RESTRICT;GSYM SUM_UNION] THEN
  FIRST_X_ASSUM (SUBST1_TAC o GSYM) THEN
  MATCH_MP_TAC (MESON[] `a = b ==> sum a f = sum b f`) THEN
  REWRITE_TAC[EXTENSION;IN_ELIM_THM;UNION] THEN
  MESON_TAC[REAL_LT_TOTAL]);;

let RADON_V_LEMMA = prove
 (`!(s:A->bool) f g.
        FINITE s /\ vsum s f = vec 0 /\ (!x. g x = &0 ==> f x = vec 0)
        ==> (vsum {x | x IN s /\ &0 < g x} f) :real^N =
             -- vsum {x | x IN s /\ g x < &0} f`,
  REWRITE_TAC[VECTOR_ARITH `a:real^N = --b <=> a + b = vec 0`] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FINITE_RESTRICT;GSYM VSUM_UNION;
               REWRITE_RULE [REAL_ARITH `&0 < f x ==> ~(f x < &0)`]
                 (SET_RULE `(!x:A. &0 < f x ==> ~(f x < &0))
                            ==>  DISJOINT {x | x IN s /\ &0 < f x}
                                          {x | x IN s /\ f x < &0}`)] THEN
  MATCH_MP_TAC (VECTOR_ARITH
    `!a b. (a:real^N) = vec 0 /\ a + b = vec 0 ==> b = vec 0`) THEN
  EXISTS_TAC `(vsum {x:A | x IN s /\ g x = &0} f):real^N` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[VSUM_RESTRICT_SET;COND_ID;VSUM_0];ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT {x:A | x IN s /\ g x = &0}
                           ({x | x IN s /\ &0 < g x} UNION
                            {x | x IN s /\ g x < &0})` ASSUME_TAC THENL
     [REWRITE_TAC[DISJOINT;UNION;INTER;IN_ELIM_THM;EXTENSION;NOT_IN_EMPTY] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_UNION;FINITE_RESTRICT;GSYM VSUM_UNION] THEN
  FIRST_X_ASSUM (SUBST1_TAC o GSYM) THEN
  MATCH_MP_TAC (MESON[] `a = b ==> vsum a f = vsum b f`) THEN
  REWRITE_TAC[EXTENSION;IN_ELIM_THM;UNION] THEN
  MESON_TAC[REAL_LT_TOTAL]);;

let RADON_PARTITION = prove
 (`!(c:real^N->bool).
        FINITE c /\ affine_dependent c
        ==> ?(m:real^N->bool) (p:real^N->bool).
                (DISJOINT m p) /\
                (m UNION p = c) /\
                ~(DISJOINT (convex hull m) (convex hull p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPEC `c:real^N->bool` RADON_EX_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`{v:real^N | v IN c /\ u v <= &0}`;
                        `{v:real^N | v IN c /\ u v > &0}`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DISJOINT;INTER;
               IN_ELIM_THM;REAL_ARITH `x <= &0 <=> ~(x > &0)`] THEN
    SET_TAC[];
    REWRITE_TAC[UNION;IN_ELIM_THM;REAL_ARITH `x <= &0 <=> ~(x > &0)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(sum {x:real^N | x IN c /\ u x > &0} u = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC (REAL_ARITH `a > &0 ==> ~(a = &0)`) THEN
    REWRITE_TAC[REAL_ARITH `a > &0 <=> &0 < a`]        THEN
    MATCH_MP_TAC (REWRITE_RULE[SUM_0] (ISPEC `\x. &0` SUM_LT_ALL)) THEN
    ASM_SIMP_TAC[FINITE_RESTRICT;IN_ELIM_THM;EXTENSION;NOT_IN_EMPTY] THEN
    REWRITE_TAC[MESON[]`~(!x. ~(P x /\ Q x)) = ?x. P x /\ Q x`] THEN
       ASM_CASES_TAC `&0 < u (v:real^N)` THENL
    [ASM SET_TAC[];ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[IMP_IMP;REAL_ARITH `~(a = &0) /\ ~(&0 < a) <=> a < &0`] THEN
    DISCH_TAC THEN
    REWRITE_TAC[MESON[REAL_NOT_LT]
     `(?x:real^N. P x /\ &0 < u x) <=> (!x. P x ==> u x <= &0) ==> F`]  THEN
    DISCH_TAC THEN
       MP_TAC (ISPECL [`u:real^N->real`;`\x:real^N. &0`;`c:real^N->bool`]
                      SUM_LT) THEN
    ASM_REWRITE_TAC[SUM_0;REAL_ARITH `~(&0 < &0)`] THEN
    ASM_MESON_TAC[];ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `~DISJOINT a b <=> ?y. y IN a /\ y IN b`] THEN
  EXISTS_TAC `&1 / (sum {x:real^N | x IN c /\ u x > &0} u) %
              vsum {x:real^N | x IN c /\ u x > &0} (\x. u x % x)` THEN
  REWRITE_TAC[CONVEX_HULL_EXPLICIT;IN_ELIM_THM] THEN
  CONJ_TAC THENL
  [MAP_EVERY EXISTS_TAC [`{v:real^N | v IN c /\ u v < &0}`;
                         `\y:real^N.
                         &1 / (sum {x:real^N | x IN c /\ u x > &0} u) *
                           (--(u y))`] THEN
   ASM_SIMP_TAC[FINITE_RESTRICT;SUBSET;IN_ELIM_THM] THEN
   REPEAT CONJ_TAC THENL
    [REAL_ARITH_TAC;
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC REAL_LE_MUL THEN
     CONJ_TAC THENL [ALL_TAC;
                     ASM_REWRITE_TAC[REAL_NEG_GE0;REAL_LE_LT]] THEN
     MATCH_MP_TAC REAL_LE_DIV THEN
     REWRITE_TAC[REAL_LE_01] THEN
     MATCH_MP_TAC SUM_POS_LE THEN
     ASM_SIMP_TAC[FINITE_RESTRICT;IN_ELIM_THM] THEN
     REAL_ARITH_TAC;
     ASM_SIMP_TAC[FINITE_RESTRICT;SUM_LMUL] THEN
     MATCH_MP_TAC (REAL_FIELD `!a. ~(a = &0) /\ a * b = a * c ==> b = c`) THEN
     EXISTS_TAC `sum {x:real^N | x IN c /\ u x > &0} u` THEN
     REWRITE_TAC[SUM_LMUL] THEN
     ASM_SIMP_TAC[REAL_FIELD `~(a = &0) ==> a * &1 / a * b = b`]  THEN
     REWRITE_TAC[SUM_NEG;REAL_MUL_RID] THEN
     REWRITE_TAC[REAL_ARITH `a > &0 <=> &0 < a`] THEN
     MATCH_MP_TAC (GSYM RADON_S_LEMMA) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC;VSUM_LMUL;VECTOR_MUL_LCANCEL] THEN
    REWRITE_TAC[VECTOR_MUL_LNEG;VSUM_NEG] THEN
    DISJ2_TAC THEN
    MATCH_MP_TAC (REWRITE_RULE[REAL_ARITH `&0 < a <=>  a > &0`]
     (GSYM RADON_V_LEMMA)) THEN
    ASM_REWRITE_TAC[] THEN
    MESON_TAC[VECTOR_MUL_LZERO];ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`{v:real^N | v IN c /\ u v > &0}`;
                        `\y:real^N.
                           &1 / (sum {x:real^N | x IN c /\ u x > &0} u) *
                           (u y)`] THEN
  ASM_SIMP_TAC[FINITE_RESTRICT;SUBSET;IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ALL_TAC;
                    ASM_SIMP_TAC[REAL_ARITH `a > &0 ==> &0 <= a`]] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_LE_01] THEN
    MATCH_MP_TAC SUM_POS_LE THEN
    ASM_SIMP_TAC[FINITE_RESTRICT;IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[FINITE_RESTRICT;SUM_LMUL] THEN
    MATCH_MP_TAC (REAL_FIELD `!a. ~(a = &0) /\ a * b = a * c ==> b = c`) THEN
    EXISTS_TAC `sum {x:real^N | x IN c /\ u x > &0} u` THEN
    REWRITE_TAC[SUM_LMUL] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(a = &0) ==> a * &1 / a * b = b`]  THEN
    REWRITE_TAC[SUM_NEG;REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH `a > &0 <=> &0 < a`] THEN
    MATCH_MP_TAC (GSYM RADON_S_LEMMA) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC;VSUM_LMUL;VECTOR_MUL_LCANCEL] THEN
  REWRITE_TAC[VECTOR_MUL_LNEG;VSUM_NEG] THEN
  DISJ2_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[REAL_ARITH `&0 < a <=>  a > &0`]
    (GSYM RADON_V_LEMMA)) THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[VECTOR_MUL_LZERO]);;

let RADON = prove
 (`!(c:real^N->bool).
        affine_dependent c
        ==> ?(m:real^N->bool) (p:real^N->bool).
                m SUBSET c /\
                p SUBSET c /\
                DISJOINT m p /\
                ~(DISJOINT (convex hull m) (convex hull p))`,
  REPEAT STRIP_TAC THEN MP_TAC
    (ISPEC `c:real^N->bool` AFFINE_DEPENDENT_EXPLICIT) THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN MP_TAC
  (ISPEC `s:real^N->bool` RADON_PARTITION) THEN
  ANTS_TAC THENL
  [ASM_SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT] THEN
     MAP_EVERY EXISTS_TAC [`s:real^N->bool`;`u:real^N->real`] THEN
     ASM SET_TAC[];ALL_TAC] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  MAP_EVERY EXISTS_TAC [`m:real^N->bool`;`p:real^N->bool`] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Helly's theorem.                                                          *)
(* ------------------------------------------------------------------------- *)

let HELLY_INDUCT = prove
 (`!n f. f HAS_SIZE n /\ n >= dimindex(:N) + 1 /\
         (!s:real^N->bool. s IN f ==> convex s) /\
         (!t. t SUBSET f /\ CARD(t) = dimindex(:N) + 1
              ==> ~(INTERS t = {}))
         ==> ~(INTERS f = {})`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH_RULE `~(0 >= n + 1)`] THEN GEN_TAC THEN
  POP_ASSUM(LABEL_TAC "*") THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_SIZE_SUC]) THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
    `SUC n >= m + 1 ==> m = n \/ n >= m + 1`))
  THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_SIMP_TAC[CARD_CLAUSES; SUBSET_REFL] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?X. !s:real^N->bool. s IN f ==> X(s) IN INTERS (f DELETE s)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; MEMBER_NOT_EMPTY; RIGHT_EXISTS_IMP_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN REMOVE_THEN "*" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?s t:real^N->bool. s IN f /\ t IN f /\ ~(s = t) /\ X s:real^N = X t`
  THENL
   [FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `(X:(real^N->bool)->real^N) t` THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC ONCE_DEPTH_CONV
     [MATCH_MP
       (SET_RULE`~(s = t)
               ==> INTERS f = INTERS(f DELETE s) INTER INTERS(f DELETE t)`)
       th]) THEN
    REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (X:(real^N->bool)->real^N) f` RADON_PARTITION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE] THEN
    MATCH_MP_TAC AFFINE_DEPENDENT_BIGGERSET THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN
    MATCH_MP_TAC(ARITH_RULE
     `!f n. n >= d + 1 /\ f = SUC n /\ c = f ==> c >= d + 2`) THEN
    MAP_EVERY EXISTS_TAC [`CARD(f:(real^N->bool)->bool)`; `n:num`] THEN
    REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `P /\ m UNION p = s /\ Q <=>
    m SUBSET s /\ p SUBSET s /\ m UNION p = s /\ P /\ Q`] THEN
  REWRITE_TAC[SUBSET_IMAGE; DISJOINT] THEN
  REWRITE_TAC[MESON[]
   `(?m p. (?u. P u /\ m = t u) /\ (?u. P u /\ p = t u) /\ Q m p) ==> r <=>
    (!u v. P u /\ P v /\ Q (t u) (t v) ==> r)`] THEN
  MAP_EVERY X_GEN_TAC [`g:(real^N->bool)->bool`; `h:(real^N->bool)->bool`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(f:(real^N->bool)->bool) = h UNION g` SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[UNION_SUBSET] THEN
    REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o ISPEC `X:(real^N->bool)->real^N` o
      MATCH_MP FUN_IN_IMAGE) THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
    ONCE_REWRITE_TAC[DISJ_SYM] THEN REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
    MATCH_MP_TAC MONO_OR THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `g SUBSET INTERS g' /\ h SUBSET INTERS h'
    ==> ~(g INTER h = {}) ==> ~(INTERS(g' UNION h') = {})`) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SET_RULE
   `IMAGE X s INTER IMAGE X t = {} ==> s INTER t = {}`)) THEN
  CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  (CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET; CONVEX_INTERS]]) THEN
  REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_IMAGE] THEN ASM SET_TAC[]);;

let HELLY = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\ CARD(f) >= dimindex(:N) + 1 /\
        (!s. s IN f ==> convex s) /\
        (!t. t SUBSET f /\ CARD(t) = dimindex(:N) + 1 ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HELLY_INDUCT THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN ASM_MESON_TAC[]);;

let HELLY_ALT = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> convex s) /\
        (!t. t SUBSET f /\ CARD(t) <= dimindex(:N) + 1 ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `CARD(f:(real^N->bool)->bool) < dimindex(:N) + 1` THEN
  ASM_SIMP_TAC[SUBSET_REFL; LT_IMP_LE] THEN MATCH_MP_TAC HELLY THEN
  ASM_SIMP_TAC[GE; GSYM NOT_LT] THEN ASM_MESON_TAC[LE_REFL]);;

let HELLY_CLOSED_ALT = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> convex s /\ closed s) /\ (?s. s IN f /\ bounded s) /\
        (!t. t SUBSET f /\ FINITE t /\ CARD(t) <= dimindex(:N) + 1
             ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC CLOSED_FIP THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC HELLY_ALT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[SUBSET_TRANS; FINITE_SUBSET]]);;

let HELLY_COMPACT_ALT = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> convex s /\ compact s) /\
        (!t. t SUBSET f /\ FINITE t /\ CARD(t) <= dimindex(:N) + 1
             ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[INTERS_0; UNIV_NOT_EMPTY] THEN
  MATCH_MP_TAC HELLY_CLOSED_ALT THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY; COMPACT_IMP_BOUNDED]);;

let HELLY_CLOSED = prove
 (`!f:(real^N->bool)->bool.
        (FINITE f ==> CARD f >= dimindex (:N) + 1) /\
        (!s. s IN f ==> convex s /\ closed s) /\ (?s. s IN f /\ bounded s) /\
        (!t. t SUBSET f /\ FINITE t /\ CARD(t) = dimindex(:N) + 1
             ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN REWRITE_TAC[GE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC HELLY_CLOSED_ALT THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`dimindex(:N) + 1`; `g:(real^N->bool)->bool`;
                 `f:(real^N->bool)->bool`] CHOOSE_SUBSET_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ ~(s = {}) ==> ~(t = {})`) THEN
  EXISTS_TAC `INTERS h: real^N->bool` THEN
  CONJ_TAC THENL [ASM SET_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC] THEN
  ASM_MESON_TAC[HAS_SIZE]);;

let HELLY_COMPACT = prove
 (`!f:(real^N->bool)->bool.
        (FINITE f ==> CARD f >= dimindex (:N) + 1) /\
        (!s. s IN f ==> convex s /\ compact s) /\
        (!t. t SUBSET f /\ FINITE t /\ CARD(t) = dimindex(:N) + 1
             ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[INTERS_0; UNIV_NOT_EMPTY] THEN
  MATCH_MP_TAC HELLY_CLOSED THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY; COMPACT_IMP_BOUNDED]);;

(* ------------------------------------------------------------------------- *)
(* Kirchberger's theorem                                                     *)
(* ------------------------------------------------------------------------- *)

let KIRCHBERGER = prove
 (`!s t:real^N->bool.
        compact s /\ compact t /\
        (!s' t'. s' SUBSET s /\ t' SUBSET t /\ FINITE s' /\ FINITE t' /\
                 CARD(s') + CARD(t') <= dimindex(:N) + 2
                 ==> ?a b. (!x. x IN s' ==> a dot x < b) /\
                           (!x. x IN t' ==> a dot x > b))
        ==> ?a b. ~(a = vec 0) /\
                  (!x. x IN s ==> a dot x < b) /\
                  (!x. x IN t ==> a dot x > b)`,
  let lemma = prove
   (`(!x. x IN convex hull s ==> a dot x < b) /\
     (!x. x IN convex hull t ==> a dot x > b) <=>
     (!x. x IN s ==> a dot x < b) /\ (!x. x IN t ==> a dot x > b)`,
    REWRITE_TAC[SET_RULE `(!x. x IN s ==> P x) <=> s SUBSET {x | P x}`] THEN
    SIMP_TAC[SUBSET_HULL; CONVEX_HALFSPACE_LT; CONVEX_HALFSPACE_GT])
  and KIRCH_LEMMA = prove
   (`!s t:real^N->bool.
          FINITE s /\ FINITE t /\
          (!s' t'. s' SUBSET s /\ t' SUBSET t /\
                   CARD(s') + CARD(t') <= dimindex(:N) + 2
                   ==> ?a b. (!x. x IN s' ==> a dot x < b) /\
                             (!x. x IN t' ==> a dot x > b))
          ==> ?a b. (!x. x IN s ==> a dot x < b) /\
                    (!x. x IN t ==> a dot x > b)`,
    REPEAT STRIP_TAC THEN MP_TAC(ISPECL
     [`IMAGE (\r. {z:real^(N,1)finite_sum |
                          fstcart z dot r < drop(sndcart z)}) s UNION
       IMAGE (\r. {z:real^(N,1)finite_sum |
                          fstcart z dot r > drop(sndcart z)}) t`]
     HELLY_ALT) THEN
    REWRITE_TAC[FORALL_SUBSET_UNION; IN_UNION; IMP_CONJ] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_SUBSET_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; INTERS_UNION] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; INTERS_IMAGE; IN_INTER;
                EXISTS_PASTECART; IN_ELIM_PASTECART_THM;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    REWRITE_TAC[FORALL_AND_THM; FORALL_IN_IMAGE; RIGHT_IMP_FORALL_THM] THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; GSYM EXISTS_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `a > b <=> --a < --b`; GSYM DOT_RNEG] THEN
      REWRITE_TAC[convex; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      SIMP_TAC[PASTECART_ADD; GSYM PASTECART_CMUL; IN_ELIM_PASTECART_THM] THEN
      SIMP_TAC[DOT_LADD; DOT_LMUL; DROP_ADD; DROP_CMUL; GSYM FORALL_DROP] THEN
      REWRITE_TAC[REAL_ARITH `--(a * x + b * y):real = a * --x + b * --y`] THEN
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
       `u + v = &1
        ==> &0 <= u /\ &0 <= v
           ==> u = &0 /\ v = &1 \/ u = &1 /\ v = &0 \/ &0 < u /\ &0 < v`)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID;
                      REAL_ADD_LID; REAL_ADD_RID] THEN
      MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_SIMP_TAC[REAL_LT_LMUL_EQ];
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1;
                  ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
      MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      SUBGOAL_THEN `FINITE(u:real^N->bool) /\ FINITE(v:real^N->bool)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) CARD_UNION o lhand o lhand o snd) THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN ANTS_TAC THENL
       [REWRITE_TAC[SET_RULE `IMAGE f s INTER IMAGE g t = {} <=>
                              !x y. x IN s /\ y IN t ==> ~(f x = g y)`] THEN
        MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
        REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN
        REWRITE_TAC[GSYM FORALL_DROP; DOT_LZERO] THEN
        DISCH_THEN(MP_TAC o SPEC `&1`) THEN REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(ARITH_RULE
       `a = a' /\ b = b' ==> a + b <= n + 2 ==> a' + b' <= n + 2`) THEN
      CONJ_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
      ASM_REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
      SIMP_TAC[GSYM FORALL_DROP; real_gt; VECTOR_EQ_LDOT;
        MESON[REAL_LT_TOTAL; REAL_LT_REFL]
         `((!y:real. a < y <=> b < y) <=> a = b) /\
          ((!y:real. y < a <=> y < b) <=> a = b)`]]) in
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM lemma] THEN
  MATCH_MP_TAC SEPARATING_HYPERPLANE_COMPACT_COMPACT THEN
  ASM_SIMP_TAC[CONVEX_CONVEX_HULL; COMPACT_CONVEX_HULL;
               CONVEX_HULL_EQ_EMPTY] THEN
  SUBGOAL_THEN
   `!s' t'. (s':real^N->bool) SUBSET s /\ t' SUBSET t /\
            FINITE s' /\ CARD(s') <= dimindex(:N) + 1 /\
            FINITE t' /\ CARD(t') <= dimindex(:N) + 1
            ==> DISJOINT (convex hull s') (convex hull t')`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s':real^N->bool`; `t':real^N->bool`] KIRCH_LEMMA) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET; FINITE_SUBSET];
      ONCE_REWRITE_TAC[GSYM lemma] THEN SET_TAC[REAL_LT_ANTISYM; real_gt]];
    POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
    REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. x IN s /\ x IN t ==> F`] THEN
    X_GEN_TAC `x:real^N` THEN ONCE_REWRITE_TAC[CARATHEODORY] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s':real^N->bool`; `t':real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Convex hull is "preserved" by a linear function.                          *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_LINEAR_IMAGE = prove
 (`!f s. linear f ==> convex hull (IMAGE f s) = IMAGE f (convex hull s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  CONJ_TAC THEN MATCH_MP_TAC HULL_INDUCT THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN SIMP_TAC[FUN_IN_IMAGE; HULL_INC] THEN
  REWRITE_TAC[convex; IN_ELIM_THM] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_ADD th)]) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    MESON_TAC[REWRITE_RULE[convex] CONVEX_CONVEX_HULL];
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
    MESON_TAC[REWRITE_RULE[convex] CONVEX_CONVEX_HULL]]);;

add_linear_invariants [CONVEX_HULL_LINEAR_IMAGE];;

let IN_CONVEX_HULL_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s x.
        linear f /\ x IN convex hull s ==> (f x) IN convex hull (IMAGE f s)`,
  SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Convexity of general and special intervals.                               *)
(* ------------------------------------------------------------------------- *)

let IS_INTERVAL_CONVEX = prove
 (`!s:real^N->bool. is_interval s ==> convex s`,
  REWRITE_TAC[is_interval; convex] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`(x:real^N)$i`; `(y:real^N)$i`] REAL_LE_TOTAL) THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&1 * a <= b /\ b <= &1 * c ==> a <= b /\ b <= c`) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[GSYM VECTOR_MUL_COMPONENT;
               VECTOR_ADD_RDISTRIB; VECTOR_ADD_COMPONENT] THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_LE_LMUL;
               REAL_LE_LADD; REAL_LE_RADD]);;

let IS_INTERVAL_CONNECTED = prove
 (`!s:real^N->bool. is_interval s ==> connected s`,
  MESON_TAC[IS_INTERVAL_CONVEX; CONVEX_CONNECTED]);;

let IS_INTERVAL_CONNECTED_1 = prove
 (`!s:real^1->bool. is_interval s <=> connected s`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[IS_INTERVAL_CONNECTED] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[IS_INTERVAL_1; connected; NOT_FORALL_THM; LEFT_IMP_EXISTS_THM;
              NOT_IMP; FORALL_LIFT; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `x:real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`{z:real^1 | basis 1 dot z < x}`; `{z:real^1 | basis 1 dot z > x}`] THEN
  REWRITE_TAC[OPEN_HALFSPACE_LT; OPEN_HALFSPACE_GT] THEN
  SIMP_TAC[SUBSET; EXTENSION; IN_UNION; IN_INTER; GSYM drop; NOT_FORALL_THM;
   real_gt; NOT_IN_EMPTY; IN_ELIM_THM; DOT_BASIS; DIMINDEX_1; ARITH] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LT_TOTAL; LIFT_DROP];
    REAL_ARITH_TAC;
    EXISTS_TAC `lift a`;
    EXISTS_TAC `lift b`] THEN
  ASM_REWRITE_TAC[REAL_LT_LE; LIFT_DROP] THEN ASM_MESON_TAC[]);;

let CONVEX_INTERVAL = prove
 (`!a b:real^N. convex(interval [a,b]) /\ convex(interval (a,b))`,
  SIMP_TAC[IS_INTERVAL_CONVEX; IS_INTERVAL_INTERVAL]);;

let CONNECTED_INTERVAL = prove
 (`(!a b:real^N. connected(interval[a,b])) /\
   (!a b:real^N. connected(interval(a,b)))`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERVAL]);;

let CONVEX_CONNECTED_COLLINEAR = prove
 (`!s:real^N->bool. collinear s ==> (convex s <=> connected s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[CONVEX_CONNECTED] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COLLINEAR_AFFINE_HULL]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  GEOM_ORIGIN_TAC `u:real^N` THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT; SPAN_INSERT_0] THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `v:real^N` THEN
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[SPAN_SPECIAL_SCALE] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[SPAN_EMPTY; SET_RULE `s SUBSET {a} <=> s = {} \/ s = {a}`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[CONVEX_EMPTY; CONVEX_SING];
    DISCH_TAC THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT; connected; NOT_EXISTS_THM] THEN
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `a:real^N = b` THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; SING_SUBSET] THEN
    REWRITE_TAC[SUBSET; IN_SEGMENT; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `u:real`] THEN
    MAP_EVERY ASM_CASES_TAC [`u = &0`; `u = &1`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; REAL_SUB_REFL;
                    REAL_SUB_RZERO; VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`{y:real^N | basis 1 dot y < basis 1 dot (x:real^N)}`;
      `{y:real^N | basis 1 dot y > basis 1 dot (x:real^N)}`]) THEN
    REWRITE_TAC[OPEN_HALFSPACE_LT; OPEN_HALFSPACE_GT] THEN
    MATCH_MP_TAC(TAUT `q /\ r /\ (~p ==> s) ==> ~(p /\ q /\ r) ==> s`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      REWRITE_TAC[CONJ_ASSOC; REAL_ARITH `~(x:real < a /\ x > a)`];
      ALL_TAC] THEN
    REWRITE_TAC[real_gt] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
    REWRITE_TAC[GSYM DOT_RSUB; SET_RULE
     `~(s SUBSET {x | P x} UNION {x | Q x}) <=>
      ?x. x IN s /\ ~(P x \/ Q x)`] THEN
    SUBGOAL_THEN
     `!p q:real^N. p IN span {basis 1} /\ q IN span {basis 1} /\
                   basis 1 dot p = basis 1 dot q
                   ==> p = q`
    ASSUME_TAC THENL
     [SIMP_TAC[SPAN_SING; IMP_CONJ; LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
      SIMP_TAC[DOT_RMUL; BASIS_NONZERO; DOT_BASIS_BASIS; DIMINDEX_GE_1;
               LE_REFL; REAL_MUL_RID];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN span {basis 1}` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC SPAN_MUL THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
       `(a:real^N) IN s \/ b IN s ==> ~(s = {})`) THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; DOT_RADD; DOT_RMUL;
        VECTOR_ARITH `((&1 - u) % a + u % b) - b:real^N = (u - &1) % (b - a)`;
        VECTOR_ARITH `((&1 - u) % a + u % b) - a:real^N = u % (b - a)`;
        VECTOR_ARITH `b - ((&1 - u) % a + u % b):real^N = (u - &1) % (a - b)`;
        VECTOR_ARITH `a - ((&1 - u) % a + u % b):real^N = u % (a - b)`] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&0 < x ==> &0 < u * x) /\ (&0 < --x ==> &0 < (&1 - u) * --x) /\
        ~(x = &0)
        ==>  &0 < u * x \/ &0 < (u - &1) * x`) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_SUB_LT] THEN
      REWRITE_TAC[DOT_RSUB; REAL_SUB_0];
      REWRITE_TAC[DOT_RSUB; REAL_ARITH
       `~(&0 < x - y \/ &0 < y - x) <=> y = x`]] THEN
    ASM SET_TAC[]]);;

let CONVEX_EQ_CONVEX_LINE_INTERSECTION = prove
 (`!s:real^N->bool. convex s <=> !a b. convex(s INTER affine hull {a,b})`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[CONVEX_INTER; AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL] THEN
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`a:real^N`; `b:real^N`; `a:real^N`; `b:real^N`]) THEN
  ASM_SIMP_TAC[IN_INTER; HULL_INC; IN_INSERT] THEN SET_TAC[]);;

let CONVEX_EQ_CONNECTED_LINE_INTERSECTION = prove
 (`!s:real^N->bool. convex s <=> !a b. connected(s INTER affine hull {a,b})`,
  GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [CONVEX_EQ_CONVEX_LINE_INTERSECTION] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  MATCH_MP_TAC CONVEX_CONNECTED_COLLINEAR THEN
  MATCH_MP_TAC COLLINEAR_SUBSET THEN
  EXISTS_TAC `affine hull {a:real^N,b}` THEN
  REWRITE_TAC[COLLINEAR_AFFINE_HULL_COLLINEAR; COLLINEAR_2] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* On real^1, is_interval, convex and connected are all equivalent.          *)
(* ------------------------------------------------------------------------- *)

let IS_INTERVAL_CONVEX_1 = prove
 (`!s:real^1->bool. is_interval s <=> convex s`,
  MESON_TAC[IS_INTERVAL_CONVEX; CONVEX_CONNECTED; IS_INTERVAL_CONNECTED_1]);;

let CONVEX_CONNECTED_1 = prove
 (`!s:real^1->bool. convex s <=> connected s`,
  REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1; GSYM IS_INTERVAL_CONNECTED_1]);;

let CONNECTED_CONVEX_1 = prove
 (`!s:real^1->bool. connected s <=> convex s`,
  REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1; GSYM IS_INTERVAL_CONNECTED_1]);;

let CONNECTED_COMPACT_INTERVAL_1 = prove
 (`!s:real^1->bool. connected s /\ compact s <=> ?a b. s = interval[a,b]`,
  REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_COMPACT]);;

let CONVEX_CONNECTED_1_GEN = prove
 (`!s:real^N->bool.
        dimindex(:N) = 1 ==> (convex s <=> connected s)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[GSYM DIMINDEX_1] THEN
  DISCH_THEN(ACCEPT_TAC o C GEOM_EQUAL_DIMENSION_RULE CONVEX_CONNECTED_1));;

let CONNECTED_CONVEX_1_GEN = prove
 (`!s:real^N->bool.
        dimindex(:N) = 1 ==> (convex s <=> connected s)`,
  SIMP_TAC[CONVEX_CONNECTED_1_GEN]);;

(* ------------------------------------------------------------------------- *)
(* Jung's theorem.                                                           *)
(* Proof taken from http://cstheory.wordpress.com/2010/08/07/jungs-theorem/  *)
(* ------------------------------------------------------------------------- *)

let JUNG = prove
 (`!s:real^N->bool r.
        bounded s /\
        sqrt(&(dimindex(:N)) / &(2 * dimindex(:N) + 2)) * diameter s <= r
        ==> ?a. s SUBSET cball(a,r)`,
  let lemma = prove
   (`&0 < x /\ x <= y ==> (x - &1) / x <= (y - &1) / y`,
    SIMP_TAC[REAL_LE_LDIV_EQ] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x / y * z:real = (x * z) / y`] THEN
    SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ]] THEN
    ASM_REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= r` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_LE_TRANS)) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[DIAMETER_POS_LE] THEN
    SIMP_TAC[SQRT_POS_LE; REAL_LE_DIV; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. cball(x,r)) s` HELLY_COMPACT_ALT) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; COMPACT_CBALL; CONVEX_CBALL] THEN
  REWRITE_TAC[TAUT `p /\ q /\ r ==> s <=> q /\ p ==> r ==> s`] THEN
  REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[INTERS_IMAGE; GSYM MEMBER_NOT_EMPTY] THEN
  REWRITE_TAC[SUBSET; IN_CBALL; IN_ELIM_THM] THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[DIST_SYM]] THEN
  X_GEN_TAC `t:real^N->bool` THEN REWRITE_TAC[GSYM SUBSET] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_IMAGE_INJ; EQ_BALLS; GSYM REAL_NOT_LE] THEN
  UNDISCH_TAC `FINITE(t:real^N->bool)` THEN
  SUBGOAL_THEN `bounded(t:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= r` THEN
  SUBGOAL_THEN
   `sqrt(&(dimindex(:N)) / &(2 * dimindex(:N) + 2)) *
    diameter(t:real^N->bool) <= r`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_LE_TRANS)) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[DIAMETER_SUBSET; SQRT_POS_LE; REAL_POS; REAL_LE_DIV];
    POP_ASSUM_LIST(K ALL_TAC) THEN
    SPEC_TAC(`t:real^N->bool`,`s:real^N->bool`) THEN
    REPEAT STRIP_TAC] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  MP_TAC(ISPEC `{d | &0 <= d /\ ?a:real^N. s SUBSET cball(a,d)}` INF) THEN
  ABBREV_TAC `d = inf {d | &0 <= d /\ ?a:real^N. s SUBSET cball(a,d)}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    ASM_MESON_TAC[BOUNDED_SUBSET_CBALL; REAL_LT_IMP_LE];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P") (LABEL_TAC "M"))] THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. s SUBSET cball(a,d)` MP_TAC THENL
   [SUBGOAL_THEN
     `!n. ?a:real^N. s SUBSET cball(a,d + inv(&n + &1))`
    MP_TAC THENL
     [X_GEN_TAC `n:num` THEN
      REMOVE_THEN "M" (MP_TAC o SPEC `d + inv(&n + &1)`) THEN
      REWRITE_TAC[REAL_ARITH `d + i <= d <=> ~(&0 < i)`] THEN
      REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
      MESON_TAC[SUBSET_CBALL; REAL_LT_IMP_LE; SUBSET_TRANS];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    X_GEN_TAC `aa:num->real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?t. compact t /\ !n. (aa:num->real^N) n IN t` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^N` o
        MATCH_MP BOUNDED_SUBSET_CBALL) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET; IN_CBALL_0] THEN
      X_GEN_TAC `B:real` THEN STRIP_TAC THEN
      EXISTS_TAC `cball(vec 0:real^N,B + d + &1)` THEN
      REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0] THEN X_GEN_TAC `n:num` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_CBALL]) THEN
      MATCH_MP_TAC(NORM_ARITH
       `(?x:real^N. norm(x) <= B /\ dist(a,x) <= d) ==> norm(a) <= B + d`) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d + inv(&n + &1)` THEN
      ASM_SIMP_TAC[REAL_LE_LADD] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[compact; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `aa:num->real^N`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPEC `(dist(a:real^N,x) - d) / &2` REAL_ARCH_INV) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `(dist(a:real^N,x) - d) / &2`) THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_HALF; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPECL [`(r:num->num)(N1 + N2)`; `x:real^N`]) THEN
    ASM_REWRITE_TAC[IN_CBALL; REAL_NOT_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num`) THEN
    ASM_REWRITE_TAC[LE_ADD] THEN
    SUBGOAL_THEN `inv(&(r (N1 + N2:num)) + &1) < (dist(a:real^N,x) - d) / &2`
    MP_TAC THENL [ALL_TAC; NORM_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC(ARITH_RULE
      `N1 + N2 <= r(N1 + N2) ==> N2 <= r(N1 + N2) + 1`) THEN
    ASM_MESON_TAC[MONOTONE_BIGGER];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN
  REWRITE_TAC[GSYM IN_CBALL; GSYM SUBSET] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
  MATCH_MP_TAC SUBSET_CBALL THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `a * s <= r ==> d <= a * s ==> d <= r`)) THEN
  UNDISCH_THEN `&0 <= r` (K ALL_TAC) THEN REMOVE_THEN "M" (K ALL_TAC) THEN
  FIRST_X_ASSUM(K ALL_TAC o SYM) THEN REMOVE_THEN "P" MP_TAC THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  ABBREV_TAC `n = CARD(s:real^N->bool)` THEN
  SUBGOAL_THEN `(s:real^N->bool) HAS_SIZE n` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
  UNDISCH_THEN `CARD(s:real^N->bool) = n` (K ALL_TAC) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`d:real`,`r:real`) THEN GEN_TAC THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN SIMP_TAC[HAS_SIZE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ABBREV_TAC `t = {x:real^N | x IN s /\ norm(x) = r}` THEN
  SUBGOAL_THEN `FINITE(t:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^N) IN convex hull t` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPEC `convex hull t:real^N->bool`
      SEPARATING_HYPERPLANE_CLOSED_0) THEN
    ASM_SIMP_TAC[CONVEX_CONVEX_HULL; NOT_IMP; COMPACT_CONVEX_HULL;
                 FINITE_IMP_COMPACT; COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    X_GEN_TAC `v:real^N` THEN
    ABBREV_TAC `k = CARD(s:real^N->bool)` THEN
    SUBGOAL_THEN `(s:real^N->bool) HAS_SIZE k` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    UNDISCH_THEN `CARD(s:real^N->bool) = k` (K ALL_TAC) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    GEOM_BASIS_MULTIPLE_TAC 1 `v:real^N` THEN X_GEN_TAC `m:real` THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL; REAL_LT_IMP_NZ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[HAS_SIZE] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN X_GEN_TAC `b:real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[DOT_LMUL; DOT_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[real_gt; GSYM REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 < b / m` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV];
      UNDISCH_THEN `&0 < b` (K ALL_TAC) THEN
      SPEC_TAC(`b / m:real`,`b:real`)] THEN
    X_GEN_TAC `b:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!x:real^N e. &0 < e /\ e < b /\ x IN t ==> norm(x - e % basis 1) < r`
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^N`; `e:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `r = norm(x:real^N)` SUBST1_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[NORM_LT; dot]] THEN
      SIMP_TAC[SUM_CLAUSES_LEFT; DIMINDEX_GE_1] THEN
      SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
               BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL;
               ARITH_RULE `2 <= n ==> 1 <= n /\ ~(n = 1)`; ARITH] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_LT_RADD] THEN
      REWRITE_TAC[GSYM REAL_POW_2; GSYM REAL_LT_SQUARE_ABS] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!b. &0 < e /\ e < b /\ b < x ==> abs(x - e * &1) < abs x`) THEN
      EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[HULL_INC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?d. &0 < d /\
          !x:real^N a. x IN (s DIFF t) /\ norm(a) < d ==> norm(x - a) < r`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `s DIFF t:real^N->bool = {}` THENL
       [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
      EXISTS_TAC `inf (IMAGE (\x:real^N. r - norm x) (s DIFF t))` THEN
      SUBGOAL_THEN `FINITE(s DIFF t:real^N->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[FINITE_DIFF]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN SIMP_TAC
       [NORM_ARITH `norm a < r - norm x ==> norm(x - a:real^N) < r`] THEN
      EXPAND_TAC "t" THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM; REAL_SUB_LT] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_CBALL_0]) THEN
      ASM_MESON_TAC[REAL_LT_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?a. !x. x IN s ==> norm(x - a:real^N) < r`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `min (b / &2) (d / &2) % basis 1:real^N` THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^N) IN t` THENL
       [MATCH_MP_TAC(ASSUME
         `!x:real^N e. &0 < e /\ e < b /\ x IN t
                       ==> norm (x - e % basis 1) < r`) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(ASSUME
         `!x:real^N a. x IN s DIFF t /\ norm a < d ==> norm (x - a) < r`) THEN
        ASM_SIMP_TAC[IN_DIFF; NORM_MUL; LE_REFL; NORM_BASIS;
                     DIMINDEX_GE_1] THEN
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
       [ASM_MESON_TAC[MEMBER_NOT_EMPTY; NORM_ARITH
         `norm(x:real^N) < r ==> &0 < r`];
        ALL_TAC] THEN
      UNDISCH_THEN
        `!x a:real^N. &0 <= x /\ s SUBSET cball (a,x) ==> r <= x` (MP_TAC o
        SPECL [`max (&0) (r - inf (IMAGE (\x:real^N. r - norm(x - a)) s))`;
               `a:real^N`]) THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> (r <= max (&0) a <=> r <= a)`] THEN
      REWRITE_TAC[SUBSET; IN_CBALL; REAL_ARITH `a <= max a b`] THEN
      REWRITE_TAC[NOT_IMP; REAL_ARITH `~(r <= r - x) <=> &0 < x`] THEN
      ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE; REAL_SUB_LT] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `d <= b ==> d <= max a b`) THEN
      ONCE_REWRITE_TAC[REAL_ARITH `a <= b - c <=> c <= b - a`] THEN
      ASM_SIMP_TAC[REAL_INF_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; ONCE_REWRITE_RULE[NORM_SUB] dist] THEN
      ASM_MESON_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt((&(dimindex (:N)) / &(2 * dimindex (:N) + 2)) *
                   diameter(s:real^N->bool) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT;
    ASM_SIMP_TAC[SQRT_MUL; DIAMETER_POS_LE; REAL_POW_LE; REAL_LE_DIV;
                 REAL_POS; POW_2_SQRT; REAL_LE_REFL]] THEN

  SUBGOAL_THEN
   `sum t (\y:real^N. &2 * r pow 2) <=
    sum t (\y. (&1 - l y) * diameter(s:real^N->bool) pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (t DELETE x) (\x:real^N. l(x)) *
                diameter(s:real^N->bool) pow 2` THEN CONJ_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[SUM_DELETE; ETA_AX; REAL_LE_REFL]] THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (t DELETE x) (\y:real^N. l y * norm(y - x) pow 2)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN ASM SET_TAC[]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum t (\y:real^N. l y * norm (y - x) pow 2)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_SUPERSET THEN
      ASM_REWRITE_TAC[FINITE_DELETE] THEN
      CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[IN_DELETE]] THEN
      SIMP_TAC[TAUT `p /\ ~(p /\ ~q) <=> p /\ q`] THEN
      REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN REAL_ARITH_TAC] THEN
    REWRITE_TAC[NORM_POW_2; VECTOR_ARITH
     `(y - x:real^N) dot (y - x) = (x dot x + y dot y) - &2 * x dot y`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum t (\y:real^N. l y * (&2 * r pow 2 - &2 * (x dot y)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      UNDISCH_TAC `(x:real^N) IN t` THEN EXPAND_TAC "t" THEN
      REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
      SIMP_TAC[NORM_EQ_SQUARE; NORM_POW_2] THEN REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_ARITH `x * (&2 * y - &2 * z) = &2 * (x * y - x * z)`] THEN
    REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN
    ASM_SIMP_TAC[SUM_SUB; FINITE_DELETE; SUM_RMUL] THEN
    REWRITE_TAC[GSYM DOT_RMUL] THEN
    ASM_SIMP_TAC[GSYM DOT_RSUM; DOT_RZERO] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[SUM_CONST; SUM_RMUL; SUM_SUB] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; MULT_CLAUSES] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
    SUBGOAL_THEN `&0 < &(CARD(t:real^N->bool) * 2)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < n * 2 <=> ~(n = 0)`] THEN
      ASM_SIMP_TAC[CARD_EQ_0];
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      REWRITE_TAC[REAL_ARITH `(a * b) / c:real = a / c * b`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REWRITE_TAC[ARITH_RULE `2 * n + 2 = (n + 1) * 2`; GSYM REAL_OF_NUM_MUL;
                  real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[GSYM real_div] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SUBGOAL_THEN `&(dimindex(:N)) = &(dimindex(:N) + 1) - &1`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC lemma THEN
        ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; CARD_EQ_0;
                     ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(s:real^N->bool)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_SUBSET THEN
        ASM SET_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The Dugundji extension theorem, and Tietze variants as corollaries.       *)
(* ------------------------------------------------------------------------- *)

let DUGUNDJI = prove
 (`!f:real^M->real^N c u s.
        convex c /\ ~(c = {}) /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\ IMAGE f s SUBSET c
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\
                !x. x IN s ==> g x = f x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    EXISTS_TAC `(\x. y):real^M->real^N` THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u DIFF s:real^M->bool`;
                 `{ ball(x:real^M,setdist({x},s) / &2) |x| x IN u DIFF s}`]
        PARACOMPACT) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC; OPEN_BALL] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; UNIONS_GSPEC] THEN
    X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN EXISTS_TAC `x:real^M` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x / &2`) THEN
    ASM_MESON_TAC[SETDIST_POS_LE; SETDIST_EQ_0_CLOSED_IN];
    DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `!t. t IN c
        ==> ?v a:real^M. v IN u /\ ~(v IN s) /\ a IN s /\
                         t SUBSET ball(v,setdist({v},s) / &2) /\
                         dist(v,a) <= &2 * setdist({v},s)`
  MP_TAC THENL
   [X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^M->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^M` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL[`{v:real^M}`; `s:real^M->bool`; `&2 * setdist({v:real^M},s)`]
        REAL_SETDIST_LT_EXISTS) THEN
    ASM_SIMP_TAC[NOT_INSERT_EMPTY; SETDIST_POS_LE; REAL_ARITH
      `&0 <= x ==> (x < &2 * x <=> ~(x = &0))`] THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; IN_SING; SETDIST_EQ_0_CLOSED_IN];
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`vv:(real^M->bool)->real^M`; `aa:(real^M->bool)->real^M`] THEN
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!t v:real^M. t IN c /\ v IN t ==> setdist({vv t},s) <= &2 * setdist({v},s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^M->bool`) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^M`) THEN ASM_REWRITE_TAC[IN_BALL] THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `(vv:(real^M->bool)->real^M) t`;
                   `v:real^M`] SETDIST_SING_TRIANGLE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t v a:real^M. t IN c /\ v IN t /\ a IN s
                   ==> dist(a,aa t) <= &6 * dist(a,v)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real^M->bool`; `v:real^M`]) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `t:real^M->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o funpow 3 CONJUNCT2) THEN
    REWRITE_TAC[IMP_CONJ; SUBSET; IN_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^M`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`{v:real^M}`; `s:real^M->bool`; `v:real^M`; `a:real^M`]
        SETDIST_LE_DIST) THEN
    ASM_REWRITE_TAC[IN_SING] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `u DIFF s:real^M->bool`]
        SUBORDINATE_PARTITION_OF_UNITY) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:(real^M->bool)->real^M->real` THEN STRIP_TAC THEN
  EXISTS_TAC
   `\x. if x IN s then (f:real^M->real^N) x
        else vsum c (\t:real^M->bool. h t x % f(aa t))` THEN
  SIMP_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONVEX_VSUM_STRONG THEN ASM SET_TAC[]] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `a:real^M` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(a:real^M) IN s` THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN_OPEN_IN THEN
    MAP_EVERY EXISTS_TAC
     [`\x:real^M.
        vsum c (\t:real^M->bool. h t x % (f:real^M->real^N) (aa t))`;
      `u DIFF s:real^M->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL; IN_DIFF] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^M`) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:real^M->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN_OPEN_IN THEN MAP_EVERY EXISTS_TAC
     [`\x. vsum {u | u IN c /\ ~(!x:real^M. x IN n ==> h u x = &0)}
                (\t:real^M->bool. h t x % (f:real^M->real^N) (aa t))`;
      `(u DIFF s) INTER n:real^M->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL; OPEN_IN_INTER_OPEN;
                 IN_INTER; IN_DIFF] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC VSUM_SUPERSET THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_VSUM THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_VMUL THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^M->bool`) THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      DISCH_THEN(MP_TAC o SPEC `a:real^M` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[IN_DIFF; ETA_AX] THEN
      REWRITE_TAC[CONTINUOUS_WITHIN] THEN MATCH_MP_TAC EQ_IMP THEN
      MATCH_MP_TAC LIM_TRANSFORM_WITHIN_SET THEN
      SUBGOAL_THEN `open_in (subtopology euclidean u) (u DIFF s:real^M->bool)`
      MP_TAC THENL [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL]; ALL_TAC] THEN
      REWRITE_TAC[EVENTUALLY_AT; OPEN_IN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `a:real^M` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN MATCH_MP_TAC MONO_EXISTS THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_INTER; IN_DIFF] THEN
      MESON_TAC[DIST_SYM]]] THEN
  ASM_REWRITE_TAC[CONTINUOUS_WITHIN_OPEN] THEN
  X_GEN_TAC `w:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) a`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
   [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^M`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[continuous_within] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(a:real^M,d / &6)` THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; OPEN_BALL] THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &6 <=> &0 < e`] THEN
  X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONVEX_VSUM_STRONG THEN
  ASM_SIMP_TAC[CONVEX_BALL; IN_DIFF] THEN
  X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^M) IN t` THENL [DISJ2_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[IN_BALL] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
   `dist(a:real^M,v) < d / &6
    ==> dist(a,a') <= &6 * dist(a,v) ==> dist(a',a) < d`)) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let TIETZE = prove
 (`!f:real^M->real^N u s B.
        &0 <= B /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> norm(f x) <= B)
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> norm(g x) <= B)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `cball(vec 0:real^N,B)`; `u:real^M->bool`;
                 `s:real^M->bool`] DUGUNDJI) THEN
  ASM_REWRITE_TAC[CONVEX_CBALL; CBALL_EQ_EMPTY; REAL_NOT_LT] THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0] THEN
  MESON_TAC[]);;

let TIETZE_CLOSED_INTERVAL = prove
 (`!f:real^M->real^N u s a b.
        ~(interval[a,b] = {}) /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval[a,b])
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> g(x) IN interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `interval[a:real^N,b]`; `u:real^M->bool`;
                 `s:real^M->bool`] DUGUNDJI) THEN
  ASM_REWRITE_TAC[CONVEX_INTERVAL; SUBSET; FORALL_IN_IMAGE] THEN
  MESON_TAC[]);;

let TIETZE_CLOSED_INTERVAL_1 = prove
 (`!f:real^N->real^1 u s a b.
        drop a <= drop b /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval[a,b])
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> g(x) IN interval[a,b])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TIETZE_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[INTERVAL_NE_EMPTY_1]);;

let TIETZE_OPEN_INTERVAL = prove
 (`!f:real^M->real^N u s a b.
        ~(interval(a,b) = {}) /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval(a,b))
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> g(x) IN interval(a,b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `interval(a:real^N,b)`; `u:real^M->bool`;
                 `s:real^M->bool`] DUGUNDJI) THEN
  ASM_REWRITE_TAC[CONVEX_INTERVAL; SUBSET; FORALL_IN_IMAGE] THEN
  MESON_TAC[]);;

let TIETZE_OPEN_INTERVAL_1 = prove
 (`!f:real^N->real^1 u s a b.
        drop a < drop b /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval(a,b))
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> g(x) IN interval(a,b))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TIETZE_OPEN_INTERVAL THEN
  ASM_REWRITE_TAC[INTERVAL_NE_EMPTY_1]);;

let TIETZE_UNBOUNDED = prove
 (`!f:real^M->real^N u s.
        closed_in (subtopology euclidean u) s /\ f continuous_on s
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(:real^N)`; `u:real^M->bool`;
                 `s:real^M->bool`] DUGUNDJI) THEN
  ASM_REWRITE_TAC[CONVEX_UNIV; UNIV_NOT_EMPTY; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Convex cones and corresponding hulls.                                     *)
(* ------------------------------------------------------------------------- *)

let convex_cone = new_definition
 `convex_cone s <=> ~(s = {}) /\ convex s /\ conic s`;;

let CONVEX_CONE = prove
 (`!s:real^N->bool.
     convex_cone s <=>
        vec 0 IN s /\
        (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\
        (!x c. x IN s /\ &0 <= c ==> (c % x) IN s)`,
  GEN_TAC THEN REWRITE_TAC[convex_cone; GSYM conic] THEN
  ASM_CASES_TAC `conic(s:real^N->bool)` THEN
  ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN AP_TERM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[conic]) THEN
  REWRITE_TAC[convex] THEN EQ_TAC THEN
  ASM_SIMP_TAC[REAL_SUB_LE] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`&2 % (x:real^N)`; `&2 % (y:real^N)`; `&1 / &2`; `&1 / &2`]) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[VECTOR_MUL_LID; REAL_POS]);;

let CONVEX_CONE_ADD = prove
 (`!s x y. convex_cone s /\ x IN s /\ y IN s ==> (x + y) IN s`,
  MESON_TAC[CONVEX_CONE]);;

let CONVEX_CONE_MUL = prove
 (`!s c x. convex_cone s /\ &0 <= c /\ x IN s ==> (c % x) IN s`,
  MESON_TAC[CONVEX_CONE]);;

let CONVEX_CONE_NONEMPTY = prove
 (`!s. convex_cone s ==> ~(s = {})`,
  MESON_TAC[CONVEX_CONE; MEMBER_NOT_EMPTY]);;

let CONVEX_CONE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        convex_cone s /\ linear f ==> convex_cone(IMAGE f s)`,
  SIMP_TAC[convex_cone; CONVEX_LINEAR_IMAGE; IMAGE_EQ_EMPTY;
           CONIC_LINEAR_IMAGE]);;

let CONVEX_CONE_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (convex_cone(IMAGE f s) <=> convex_cone s)`,
  REWRITE_TAC[convex_cone] THEN
  MESON_TAC[IMAGE_EQ_EMPTY; CONVEX_LINEAR_IMAGE_EQ; CONIC_LINEAR_IMAGE_EQ]);;

add_linear_invariants [CONVEX_CONE_LINEAR_IMAGE_EQ];;

let CONVEX_CONE_HALFSPACE_GE = prove
 (`!a. convex_cone {x | a dot x >= &0}`,
  SIMP_TAC[CONVEX_CONE; real_ge; IN_ELIM_THM; DOT_RZERO; DOT_RADD; DOT_RMUL;
           REAL_LE_ADD; REAL_LE_MUL; REAL_LE_REFL]);;

let CONVEX_CONE_HALFSPACE_LE = prove
 (`!a. convex_cone {x | a dot x <= &0}`,
  REWRITE_TAC[REAL_ARITH `x <= &0 <=> &0 <= --x`; GSYM DOT_LNEG] THEN
  REWRITE_TAC[GSYM real_ge; CONVEX_CONE_HALFSPACE_GE]);;

let CONVEX_CONE_CONTAINS_0 = prove
 (`!s:real^N->bool. convex_cone s ==> vec 0 IN s`,
  SIMP_TAC[CONVEX_CONE]);;

let CONVEX_CONE_INTERS = prove
 (`!f. (!s:real^N->bool. s IN f ==> convex_cone s) ==> convex_cone(INTERS f)`,
  SIMP_TAC[convex_cone; CONIC_INTERS; CONVEX_INTERS] THEN
  REWRITE_TAC[GSYM convex_cone] THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^N` THEN
  ASM_SIMP_TAC[IN_INTERS; CONVEX_CONE_CONTAINS_0]);;

let CONVEX_CONE_CONVEX_CONE_HULL = prove
 (`!s. convex_cone(convex_cone hull s)`,
  SIMP_TAC[P_HULL; CONVEX_CONE_INTERS]);;

let CONVEX_CONVEX_CONE_HULL = prove
 (`!s. convex(convex_cone hull s)`,
  MESON_TAC[CONVEX_CONE_CONVEX_CONE_HULL; convex_cone]);;

let CONIC_CONVEX_CONE_HULL = prove
 (`!s. conic(convex_cone hull s)`,
  MESON_TAC[CONVEX_CONE_CONVEX_CONE_HULL; convex_cone]);;

let CONVEX_CONE_HULL_NONEMPTY = prove
 (`!s. ~(convex_cone hull s = {})`,
  MESON_TAC[CONVEX_CONE_CONVEX_CONE_HULL; convex_cone]);;

let CONVEX_CONE_HULL_CONTAINS_0 = prove
 (`!s. vec 0 IN convex_cone hull s`,
  MESON_TAC[CONVEX_CONE_CONVEX_CONE_HULL; CONVEX_CONE]);;

let CONVEX_CONE_HULL_ADD = prove
 (`!s x y:real^N.
        x IN convex_cone hull s /\ y IN convex_cone hull s
        ==> x + y IN convex_cone hull s`,
  MESON_TAC[CONVEX_CONE; CONVEX_CONE_CONVEX_CONE_HULL]);;

let CONVEX_CONE_HULL_MUL = prove
 (`!s c x:real^N.
        &0 <= c /\ x IN convex_cone hull s
        ==> (c % x) IN convex_cone hull s`,
  MESON_TAC[CONVEX_CONE; CONVEX_CONE_CONVEX_CONE_HULL]);;

let CONVEX_CONE_SUMS = prove
 (`!s t. convex_cone s /\ convex_cone t
         ==> convex_cone {x + y:real^N | x IN s /\ y IN t}`,
  SIMP_TAC[convex_cone; CONIC_SUMS; CONVEX_SUMS] THEN SET_TAC[]);;

let CONVEX_CONE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        convex_cone s /\ convex_cone t ==> convex_cone(s PCROSS t)`,
  SIMP_TAC[convex_cone; CONVEX_PCROSS; CONIC_PCROSS; PCROSS_EQ_EMPTY]);;

let CONVEX_CONE_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        convex_cone(s PCROSS t) <=> convex_cone s /\ convex_cone t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [ASM_REWRITE_TAC[PCROSS_EMPTY; convex_cone]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[PCROSS_EMPTY; convex_cone]; ALL_TAC] THEN
  EQ_TAC THEN REWRITE_TAC[CONVEX_CONE_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
     `(s:real^M->bool) PCROSS (t:real^N->bool)`] CONVEX_CONE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
     `(s:real^M->bool) PCROSS (t:real^N->bool)`] CONVEX_CONE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let CONVEX_CONE_HULL_UNION = prove
 (`!s t. convex_cone hull(s UNION t) =
         {x + y:real^N | x IN convex_cone hull s /\ y IN convex_cone hull t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    SIMP_TAC[CONVEX_CONE_SUMS; CONVEX_CONE_CONVEX_CONE_HULL] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`x:real^N`; `vec 0:real^N`] THEN
      ASM_SIMP_TAC[HULL_INC; CONVEX_CONE_HULL_CONTAINS_0; VECTOR_ADD_RID];
      MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `x:real^N`] THEN
      ASM_SIMP_TAC[HULL_INC; CONVEX_CONE_HULL_CONTAINS_0; VECTOR_ADD_LID]];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_CONE_HULL_ADD THEN
    ASM_MESON_TAC[HULL_MONO; SUBSET_UNION; SUBSET]]);;

let CONVEX_CONE_SING = prove
 (`convex_cone {vec 0}`,
  SIMP_TAC[CONVEX_CONE; IN_SING; VECTOR_ADD_LID; VECTOR_MUL_RZERO]);;

let CONVEX_HULL_SUBSET_CONVEX_CONE_HULL = prove
 (`!s. convex hull s SUBSET convex_cone hull s`,
  GEN_TAC THEN MATCH_MP_TAC HULL_ANTIMONO THEN
  SIMP_TAC[convex_cone; SUBSET; IN]);;

let CONIC_HULL_SUBSET_CONVEX_CONE_HULL = prove
 (`!s. conic hull s SUBSET convex_cone hull s`,
  GEN_TAC THEN MATCH_MP_TAC HULL_ANTIMONO THEN
  SIMP_TAC[convex_cone; SUBSET; IN]);;

let CONVEX_CONE_HULL_SEPARATE_NONEMPTY = prove
 (`!s:real^N->bool.
    ~(s = {})
    ==> convex_cone hull s = conic hull (convex hull s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC HULL_MINIMAL THEN
  REWRITE_TAC[CONIC_CONVEX_CONE_HULL; CONVEX_HULL_SUBSET_CONVEX_CONE_HULL] THEN
  ASM_SIMP_TAC[CONVEX_CONIC_HULL; CONVEX_CONVEX_HULL; CONIC_CONIC_HULL;
               convex_cone; CONIC_HULL_EQ_EMPTY; CONVEX_HULL_EQ_EMPTY] THEN
  ASM_MESON_TAC[HULL_SUBSET; SUBSET_REFL; SUBSET_TRANS]);;

let CONVEX_CONE_HULL_EMPTY = prove
 (`convex_cone hull {} = {vec 0}`,
  MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[CONVEX_CONE_CONTAINS_0; EMPTY_SUBSET; CONVEX_CONE_SING;
              SET_RULE `{a} SUBSET s <=> a IN s`; CONVEX_CONE_CONTAINS_0]);;

let CONVEX_CONE_HULL_SEPARATE = prove
 (`!s:real^N->bool.
    convex_cone hull s = vec 0 INSERT conic hull (convex hull s)`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[CONVEX_CONE_HULL_EMPTY; CONVEX_HULL_EMPTY; CONIC_HULL_EMPTY] THEN
  ASM_SIMP_TAC[CONVEX_CONE_HULL_SEPARATE_NONEMPTY] THEN
  MATCH_MP_TAC(SET_RULE `a IN s ==> s = a INSERT s`) THEN
  ASM_SIMP_TAC[CONIC_CONTAINS_0; CONIC_CONIC_HULL] THEN
  ASM_REWRITE_TAC[CONIC_HULL_EQ_EMPTY; CONVEX_HULL_EQ_EMPTY]);;

let CONVEX_CONE_HULL_CONVEX_HULL_NONEMPTY = prove
 (`!s:real^N->bool.
        ~(s = {})
        ==> convex_cone hull s = {c % x | &0 <= c /\ x IN convex hull s}`,
  SIMP_TAC[CONVEX_CONE_HULL_SEPARATE_NONEMPTY; CONIC_HULL_EXPLICIT]);;

let CONVEX_CONE_HULL_CONVEX_HULL = prove
 (`!s:real^N->bool.
        convex_cone hull s =
        vec 0 INSERT {c % x | &0 <= c /\ x IN convex hull s}`,
  REWRITE_TAC[CONVEX_CONE_HULL_SEPARATE; CONIC_HULL_EXPLICIT]);;

let CONVEX_CONE_HULL_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f
        ==> convex_cone hull (IMAGE f s) = IMAGE f (convex_cone hull s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^M-> bool = {}` THEN
  ASM_SIMP_TAC[CONVEX_CONE_HULL_SEPARATE_NONEMPTY; IMAGE_EQ_EMPTY;
               CONVEX_HULL_LINEAR_IMAGE; CONIC_HULL_LINEAR_IMAGE] THEN
  REWRITE_TAC[IMAGE_CLAUSES; CONVEX_CONE_HULL_EMPTY] THEN
  MATCH_MP_TAC(SET_RULE `f x = y ==> {y} = {f x}`) THEN
  ASM_MESON_TAC[LINEAR_0]);;

add_linear_invariants [CONVEX_CONE_HULL_LINEAR_IMAGE];;

let SUBSPACE_IMP_CONVEX_CONE = prove
 (`!s. subspace s ==> convex_cone s`,
  SIMP_TAC[subspace; CONVEX_CONE]);;

let CONVEX_CONE_SPAN = prove
 (`!s. convex_cone(span s)`,
  SIMP_TAC[convex_cone; CONVEX_SPAN; CONIC_SPAN; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[SPAN_0]);;

let CONVEX_CONE_NEGATIONS = prove
 (`!s. convex_cone s ==> convex_cone (IMAGE (--) s)`,
  SIMP_TAC[convex_cone; IMAGE_EQ_EMPTY; CONIC_NEGATIONS; CONVEX_NEGATIONS]);;

let SUBSPACE_CONVEX_CONE_SYMMETRIC = prove
 (`!s:real^N->bool.
        subspace s <=> convex_cone s /\ (!x. x IN s ==> --x IN s)`,
  GEN_TAC THEN REWRITE_TAC[subspace; CONVEX_CONE] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THENL
   [ASM_MESON_TAC[VECTOR_ARITH `--x:real^N = -- &1 % x`];
    MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN DISCH_TAC THEN
    DISJ_CASES_TAC(SPEC `c:real` REAL_LE_NEGTOTAL) THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[VECTOR_ARITH `c % x:real^N = --(--c % x)`]]);;

let SPAN_CONVEX_CONE_ALLSIGNS = prove
 (`!s:real^N->bool. span s = convex_cone hull (s UNION IMAGE (--) s)`,
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN CONJ_TAC THENL
     [MESON_TAC[HULL_SUBSET; SUBSET_UNION; SUBSET_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[SUBSPACE_CONVEX_CONE_SYMMETRIC;
                CONVEX_CONE_CONVEX_CONE_HULL] THEN
    MATCH_MP_TAC HULL_INDUCT THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
      DISCH_TAC THEN MATCH_MP_TAC HULL_INC THEN
      REWRITE_TAC[IN_UNION; IN_IMAGE] THEN ASM_MESON_TAC[VECTOR_NEG_NEG];
      SUBGOAL_THEN `!s. {x:real^N | (--x) IN s} = IMAGE (--) s`
       (fun th -> SIMP_TAC[th; CONVEX_CONE_NEGATIONS;
                           CONVEX_CONE_CONVEX_CONE_HULL]) THEN
      GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[VECTOR_NEG_NEG]];
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONE_SPAN] THEN
    REWRITE_TAC[UNION_SUBSET; SPAN_INC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    MESON_TAC[SPAN_SUPERSET; SPAN_NEG]]);;

(* ------------------------------------------------------------------------- *)
(* Epigraphs of convex functions.                                            *)
(* ------------------------------------------------------------------------- *)

let epigraph = new_definition
  `epigraph s (f:real^N->real) =
       {xy:real^((N,1)finite_sum) |
             fstcart xy IN s /\ f(fstcart xy) <= drop(sndcart xy)}`;;

let IN_EPIGRAPH = prove
 (`!x y. (pastecart x (lift y)) IN epigraph s f <=> x IN s /\ f(x) <= y`,
  REWRITE_TAC[epigraph; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
              LIFT_DROP]);;

let CONVEX_EPIGRAPH = prove
 (`!f s. f convex_on s /\ convex s <=> convex(epigraph s f)`,
  REWRITE_TAC[convex; convex_on; IN_ELIM_THM; SNDCART_ADD; SNDCART_CMUL;
   epigraph; FSTCART_ADD; FSTCART_CMUL; FORALL_PASTECART; FSTCART_PASTECART;
   SNDCART_PASTECART] THEN
  REWRITE_TAC[GSYM FORALL_DROP; DROP_ADD; DROP_CMUL] THEN
  MESON_TAC[REAL_LE_REFL; REAL_LE_ADD2; REAL_LE_LMUL; REAL_LE_TRANS]);;

let CONVEX_EPIGRAPH_CONVEX = prove
 (`!f s. convex s ==> (f convex_on s <=> convex(epigraph s f))`,
  REWRITE_TAC[GSYM CONVEX_EPIGRAPH] THEN CONV_TAC TAUT);;

let CONVEX_ON_EPIGRAPH_SLICE_LE = prove
 (`!f:real^N->real s a.
        f convex_on s /\ convex s ==> convex {x | x IN s /\ f(x) <= a}`,
  SIMP_TAC[convex_on; convex; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  MATCH_MP_TAC REAL_CONVEX_BOUND_LE THEN ASM_REWRITE_TAC[]);;

let CONVEX_ON_EPIGRAPH_SLICE_LT = prove
 (`!f:real^N->real s a.
        f convex_on s /\ convex s ==> convex {x | x IN s /\ f(x) < a}`,
  SIMP_TAC[convex_on; convex; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LET_TRANS) THEN
  MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Use this to derive general bound property of convex function.             *)
(* ------------------------------------------------------------------------- *)

let FORALL_OF_PASTECART = prove
 (`(!p. P (fstcart o p) (sndcart o p)) <=> (!x:A->B^M y:A->B^N. P x y)`,
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\a:A. pastecart (x a :B^M) (y a :B^N)`) THEN
  REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART; ETA_AX]);;

let FORALL_OF_DROP = prove
 (`(!v. P (drop o v)) <=> (!x:A->real. P x)`,
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\a:A. lift(x a)`) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]);;

let CONVEX_ON_JENSEN = prove
 (`!f:real^N->real s.
        convex s
        ==> (f convex_on s <=>
                !k u x.
                   (!i:num. 1 <= i /\ i <= k ==> &0 <= u(i) /\ x(i) IN s) /\
                   (sum (1..k) u = &1)
                   ==> f(vsum (1..k) (\i. u(i) % x(i)))
                           <= sum (1..k) (\i. u(i) * f(x(i))))`,
  let lemma = prove
   (`(!x. P x ==> (Q x = R x)) ==> (!x. P x) ==> ((!x. Q x) <=> (!x. R x))`,
    MESON_TAC[]) in
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (fun th -> REWRITE_TAC[MATCH_MP CONVEX_EPIGRAPH_CONVEX th]) THEN
  REWRITE_TAC[CONVEX_INDEXED; epigraph] THEN
  SIMP_TAC[IN_ELIM_THM; SNDCART_ADD; SNDCART_CMUL; FINITE_NUMSEG;
           FSTCART_ADD; FSTCART_CMUL; FORALL_PASTECART; DROP_CMUL;
           FSTCART_PASTECART; SNDCART_PASTECART;
           FSTCART_VSUM; SNDCART_VSUM; DROP_VSUM; o_DEF] THEN
  REWRITE_TAC[GSYM(ISPEC `fstcart` o_THM); GSYM(ISPEC `sndcart` o_THM)] THEN
  REWRITE_TAC[GSYM(ISPEC `drop` o_THM)] THEN
  REWRITE_TAC[FORALL_OF_PASTECART; FORALL_OF_DROP] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONVEX_INDEXED]) THEN
  REPEAT(MATCH_MP_TAC lemma THEN GEN_TAC) THEN SIMP_TAC[] THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  EQ_TAC THEN SIMP_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  ASM_SIMP_TAC[SUM_LE_NUMSEG; REAL_LE_LMUL]);;

let CONVEX_ON_IMP_JENSEN = prove
 (`!f:real^N->real s k:A->bool u x.
        f convex_on s /\ convex s /\ FINITE k /\
        (!i. i IN k ==> &0 <= u i /\ x i IN s) /\ sum k u = &1
        ==> f(vsum k (\i. u i % x i)) <= sum k (\i. u i * f(x i))`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `n = CARD(k:A->bool)` THEN
  REWRITE_TAC[INJECTIVE_ON_ALT] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->A`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  ASM_SIMP_TAC[VSUM_IMAGE; SUM_IMAGE; FINITE_NUMSEG; IMP_CONJ; o_DEF] THEN
  DISCH_TAC THEN MP_TAC(ISPECL [`f:real^N->real`; `s:real^N->bool`]
        CONVEX_ON_JENSEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM IN_NUMSEG] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Another intermediate value theorem formulation.                           *)
(* ------------------------------------------------------------------------- *)

let IVT_INCREASING_COMPONENT_ON_1 = prove
 (`!f:real^1->real^N a b y k.
        drop a <= drop b /\ 1 <= k /\ k <= dimindex(:N) /\
        f continuous_on interval[a,b] /\
        f(a)$k <= y /\ y <= f(b)$k
        ==> ?x. x IN interval[a,b] /\ f(x)$k = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (f:real^1->real^N) (interval[a,b])`]
        CONNECTED_IVT_COMPONENT) THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE] THEN
  ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE; CONVEX_CONNECTED;
               CONVEX_INTERVAL] THEN
  EXISTS_TAC `a:real^1` THEN ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL] THEN
  EXISTS_TAC `b:real^1` THEN ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL]);;

let IVT_INCREASING_COMPONENT_1 = prove
 (`!f:real^1->real^N a b y k.
        drop a <= drop b /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> f continuous at x) /\
        f(a)$k <= y /\ y <= f(b)$k
        ==> ?x. x IN interval[a,b] /\ f(x)$k = y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVT_INCREASING_COMPONENT_ON_1 THEN
  ASM_SIMP_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON]);;

let IVT_DECREASING_COMPONENT_ON_1 = prove
 (`!f:real^1->real^N a b y k.
        drop a <= drop b /\ 1 <= k /\ k <= dimindex(:N) /\
        f continuous_on interval[a,b] /\
        f(b)$k <= y /\ y <= f(a)$k
        ==> ?x. x IN interval[a,b] /\ f(x)$k = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EQ_NEG2] THEN
  ASM_SIMP_TAC[GSYM VECTOR_NEG_COMPONENT] THEN
  MATCH_MP_TAC IVT_INCREASING_COMPONENT_ON_1 THEN
  ASM_SIMP_TAC[VECTOR_NEG_COMPONENT; CONTINUOUS_ON_NEG; REAL_LE_NEG2]);;

let IVT_DECREASING_COMPONENT_1 = prove
 (`!f:real^1->real^N a b y k.
        drop a <= drop b /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> f continuous at x) /\
        f(b)$k <= y /\ y <= f(a)$k
        ==> ?x. x IN interval[a,b] /\ f(x)$k = y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVT_DECREASING_COMPONENT_ON_1 THEN
  ASM_SIMP_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON]);;

(* ------------------------------------------------------------------------- *)
(* A bound within a convex hull, and so an interval.                         *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_CONVEX_HULL_BOUND = prove
 (`!f s b. f convex_on (convex hull s) /\
           (!x:real^N. x IN s ==> f(x) <= b)
           ==> !x. x IN convex hull s ==> f(x) <= b`,
  REPEAT GEN_TAC THEN SIMP_TAC[CONVEX_ON_JENSEN; CONVEX_CONVEX_HULL] THEN
  STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_INDEXED] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `u:num->real`; `v:num->real^N`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..k) (\i. u i * f(v i :real^N))` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET; HULL_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..k) (\i. u i * b)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[REAL_LE_LMUL];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[SUM_LMUL] THEN
  ASM_MESON_TAC[REAL_LE_REFL; REAL_MUL_RID]);;

let UNIT_INTERVAL_CONVEX_HULL = prove
 (`interval [vec 0,vec 1:real^N] =
     convex hull
       {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                           ==> ((x$i = &0) \/ (x$i = &1))}`,
  let lemma = prove
   (`FINITE {i | 1 <= i /\ i <= n /\ P(i)} /\
     CARD {i | 1 <= i /\ i <= n /\ P(i)} <= n`,
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..n`;
      GEN_REWRITE_TAC RAND_CONV [ARITH_RULE `x = (x + 1) - 1`] THEN
      REWRITE_TAC[GSYM CARD_NUMSEG] THEN MATCH_MP_TAC CARD_SUBSET] THEN
    SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; SUBSET; IN_ELIM_THM]) in
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_INTERVAL; SUBSET; IN_INTERVAL; IN_ELIM_THM] THEN
    SIMP_TAC[VEC_COMPONENT] THEN MESON_TAC[REAL_LE_REFL; REAL_POS]] THEN
  SUBGOAL_THEN
   `!n x:real^N.
        x IN interval[vec 0,vec 1] /\
        n <= dimindex(:N) /\
        CARD {i | 1 <= i /\ i <= dimindex(:N) /\ ~(x$i = &0)} <= n
        ==> x IN convex hull
                  {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                  ==> ((x$i = &0) \/ (x$i = &1))}`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `dimindex(:N)` THEN
    ASM_REWRITE_TAC[LE_REFL; lemma]] THEN
  INDUCT_TAC THEN X_GEN_TAC `x:real^N` THENL
   [SIMP_TAC[LE; lemma; CARD_EQ_0] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; BETA_THM] THEN
    REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `x = vec 0:real^N` SUBST1_TAC THENL
     [ASM_SIMP_TAC[CART_EQ; VEC_COMPONENT]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
    SIMP_TAC[IN_ELIM_THM; VEC_COMPONENT];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `{i | 1 <= i /\ i <= dimindex(:N) /\ ~((x:real^N)$i = &0)} = {}`
  THENL
   [DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; BETA_THM] THEN
    REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `x = vec 0:real^N` SUBST1_TAC THENL
     [ASM_SIMP_TAC[CART_EQ; VEC_COMPONENT]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
    SIMP_TAC[IN_ELIM_THM; VEC_COMPONENT];
    ALL_TAC] THEN
  MP_TAC(ISPEC
   `IMAGE (\i. x$i)
      {i | 1 <= i /\ i <= dimindex(:N) /\ ~((x:real^N)$i = &0)}`
   INF_FINITE) THEN
  ABBREV_TAC `xi = inf
   (IMAGE (\i. x$i)
     {i | 1 <= i /\ i <= dimindex(:N) /\ ~((x:real^N)$i = &0)})` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; lemma] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (x:real^N)$i /\ x$i <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `x:real^N IN interval [vec 0,vec 1]` THEN
    ASM_SIMP_TAC[IN_INTERVAL; VEC_COMPONENT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `x <= &1 ==> (x = &1) \/ x < &1`))
  THENL
   [SUBGOAL_THEN
     `x = lambda i. if (x:real^N)$i = &0 then &0 else &1`
    SUBST1_TAC THENL
     [UNDISCH_TAC `x:real^N IN interval [vec 0,vec 1]` THEN
      ASM_SIMP_TAC[CART_EQ; IN_INTERVAL; VEC_COMPONENT; LAMBDA_BETA] THEN
      ASM_MESON_TAC[REAL_LE_ANTISYM];
      ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
    SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x:real^N =
        x$i % (lambda j. if x$j = &0 then &0 else &1) +
        (&1 - x$i) %
        (lambda j. if x$j = &0 then &0 else (x$j - x$i) / (&1 - x$i))`
  SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             LAMBDA_BETA; VEC_COMPONENT] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; ARITH_RULE `x < &1 ==> ~(&1 - x = &0)`] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[convex] CONVEX_CONVEX_HULL) THEN
  ASM_SIMP_TAC[REAL_ARITH `x < &1 ==> &0 <= &1 - x`;
               REAL_ARITH `x + &1 - x = &1`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
    SIMP_TAC[LAMBDA_BETA; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC k <= n ==> k <= n`] THEN CONJ_TAC THENL
   [SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; VEC_COMPONENT] THEN
    GEN_TAC THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ;
                 REAL_ARITH `x < &1 ==> &0 < &1 - x`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_LE; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_ARITH `a - b <= &1 - b <=> a <= &1`] THEN
    UNDISCH_TAC `x:real^N IN interval [vec 0,vec 1]` THEN
    ASM_SIMP_TAC[CART_EQ; IN_INTERVAL; VEC_COMPONENT; LAMBDA_BETA];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
   `CARD({i | 1 <= i /\ i <= dimindex(:N) /\ ~((x:real^N)$i = &0)}
         DELETE i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[lemma; FINITE_DELETE] THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_ELIM_THM] THEN
    GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
    SIMP_TAC[real_div; REAL_SUB_REFL; REAL_MUL_LZERO];
    SIMP_TAC[lemma; CARD_DELETE] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `x <= SUC n ==> x - 1 <= n`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Some convexity-related properties of Hausdorff distance                   *)
(* ------------------------------------------------------------------------- *)

let HAUSDIST_CONVEX_HULLS = prove
 (`!s t:real^N->bool.
        bounded s /\ bounded t
        ==> hausdist(convex hull s,convex hull t) <= hausdist(s,t)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_MESON_TAC[HAUSDIST_EMPTY; CONVEX_HULL_EMPTY; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_MESON_TAC[HAUSDIST_EMPTY; CONVEX_HULL_EMPTY; REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_HAUSDIST_LE THEN ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONVEX_ON_CONVEX_HULL_BOUND THEN
  CONJ_TAC THEN SIMP_TAC[CONVEX_ON_SETDIST; CONVEX_CONVEX_HULL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_HAUSDIST THEN
  ASM_REWRITE_TAC[LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM; CONJ_ASSOC] THEN
  (CONJ_TAC THENL
    [CONJ_TAC; ASM_MESON_TAC[SETDIST_SUBSET_RIGHT; HULL_SUBSET]]) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] BOUNDED_DIFFS) THEN
  ASM_REWRITE_TAC[bounded; FORALL_IN_GSPEC; GSYM dist] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[SETDIST_LE_DIST; dist; DIST_SYM; REAL_LE_TRANS;
                MEMBER_NOT_EMPTY; IN_SING]);;

let HAUSDIST_SUMS = prove
 (`!s t:real^N->bool u.
        bounded s /\ bounded t /\ convex s /\ convex t /\ bounded u /\
        ~(s = {}) /\ ~(t = {}) /\ ~(u = {})
        ==> hausdist({x + e | x IN s /\ e IN u},
                     {y + e | y IN t /\ e IN u}) =
            hausdist(s,t)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[HAUSDIST_CLOSURE]
   `hausdist(s:real^N->bool,t) = hausdist(closure s,closure t)`] THEN
  SIMP_TAC[CLOSURE_SUMS] THEN
  SIMP_TAC[CLOSURE_CLOSED; CLOSED_CBALL; GSYM COMPACT_CLOSURE] THEN
  ONCE_REWRITE_TAC[GSYM CLOSURE_EQ_EMPTY] THEN
  ASM_CASES_TAC
   `convex(closure s:real^N->bool) /\ convex(closure t:real^N->bool)`
  THENL [POP_ASSUM MP_TAC; ASM_MESON_TAC[CONVEX_CLOSURE]] THEN
  ASM_CASES_TAC `convex(s:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `convex(t:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`closure u:real^N->bool`,`u:real^N->bool`) THEN
  SPEC_TAC(`closure t:real^N->bool`,`t:real^N->bool`) THEN
  SPEC_TAC(`closure s:real^N->bool`,`s:real^N->bool`) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_HAUSDIST_LE_SUMS THEN
  MAP_EVERY ABBREV_TAC
   [`a = hausdist(s:real^N->bool,t)`;
    `b = hausdist({x + e:real^N | x IN s /\ e IN u},
                  {y + e | y IN t /\ e IN u})`] THEN
   ASM_REWRITE_TAC[CBALL_EQ_EMPTY; REAL_NOT_LT; SET_RULE
    `{f x y | x IN s /\ y IN t} = {} <=> s = {} \/ t = {}`]
  THENL
   [REWRITE_TAC[SUMS_ASSOC] THEN
    GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
      [SUMS_SYM] THEN
    REWRITE_TAC[GSYM SUMS_ASSOC] THEN CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET s'
      ==> {f x y | x IN s /\ y IN t} SUBSET {f x y | x IN s' /\ y IN t}`) THEN
    EXPAND_TAC "a" THENL
     [ALL_TAC; ONCE_REWRITE_TAC[HAUSDIST_SYM]] THEN
    MATCH_MP_TAC HAUSDIST_COMPACT_SUMS THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    CONJ_TAC THEN MATCH_MP_TAC SUBSET_SUMS_RCANCEL THEN
    EXISTS_TAC `u:real^N->bool` THEN
    ASM_SIMP_TAC[CLOSED_COMPACT_SUMS; COMPACT_CBALL; COMPACT_IMP_CLOSED;
      CONVEX_CBALL; COMPACT_IMP_BOUNDED; CONVEX_SUMS; REAL_NOT_LT] THEN
    REWRITE_TAC[SUMS_ASSOC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [SUMS_SYM] THEN
    REWRITE_TAC[GSYM SUMS_ASSOC] THEN
    EXPAND_TAC "b" THENL
     [ALL_TAC; ONCE_REWRITE_TAC[HAUSDIST_SYM]] THEN
    MATCH_MP_TAC HAUSDIST_COMPACT_SUMS THEN
    ASM_SIMP_TAC[BOUNDED_SUMS; COMPACT_SUMS; COMPACT_CBALL;
     COMPACT_IMP_BOUNDED; CBALL_EQ_EMPTY; REAL_NOT_LT; SET_RULE
     `{f x y | x IN s /\ y IN t} = {} <=> s = {} \/ t = {}`]]);;

(* ------------------------------------------------------------------------- *)
(* Representation of any interval as a finite convex hull.                   *)
(* ------------------------------------------------------------------------- *)

let CLOSED_INTERVAL_AS_CONVEX_HULL = prove
 (`!a b:real^N. ?s. FINITE s /\ interval[a,b] = convex hull s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
   [ASM_MESON_TAC[CONVEX_HULL_EMPTY; FINITE_EMPTY]; ALL_TAC] THEN
  ASM_SIMP_TAC[CLOSED_INTERVAL_IMAGE_UNIT_INTERVAL] THEN
  SUBGOAL_THEN
   `?s:real^N->bool. FINITE s /\ interval[vec 0,vec 1] = convex hull s`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `{x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                      ==> ((x$i = &0) \/ (x$i = &1))}` THEN
    REWRITE_TAC[UNIT_INTERVAL_CONVEX_HULL] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     `IMAGE (\s. (lambda i. if i IN s then &1 else &0):real^N)
            {t | t SUBSET (1..dimindex(:N))}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET; FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC
     `{i | 1 <= i /\ i <= dimindex(:N) /\ ((x:real^N)$i = &1)}` THEN
    SIMP_TAC[CART_EQ; IN_ELIM_THM; IN_NUMSEG; LAMBDA_BETA] THEN
    ASM_MESON_TAC[];
    EXISTS_TAC `IMAGE (\x:real^N. a + x)
                      (IMAGE (\x. (lambda i. ((b:real^N)$i - a$i) * x$i))
                             (s:real^N->bool))` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; CONVEX_HULL_TRANSLATION] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC(GSYM CONVEX_HULL_LINEAR_IMAGE) THEN
    SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Bounded convex function on open set is continuous.                        *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_BOUNDED_CONTINUOUS = prove
 (`!f:real^N->real s b.
        open s /\ f convex_on s /\ (!x. x IN s ==> abs(f x) <= b)
        ==> (lift o f) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[CONTINUOUS_AT_LIFT_RANGE] THEN
  ABBREV_TAC `B = abs(b) + &1` THEN
  SUBGOAL_THEN `&0 < B /\ !x:real^N. x IN s ==> abs(f x) <= B`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[REAL_ARITH `x <= b ==> x <= abs b + &1`];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `abs(x - y) < e <=> x - y < e /\ y - x < e`] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN REWRITE_TAC[SUBSET; IN_CBALL] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (k / &2) (e / (&2 * B) * k)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_LT_MUL;
               REAL_OF_NUM_LT; ARITH] THEN
  X_GEN_TAC `y:real^N` THEN
  ASM_CASES_TAC `y:real^N = x` THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
  STRIP_TAC THEN
  ABBREV_TAC `t = k / norm(y - x:real^N)` THEN
  SUBGOAL_THEN `&2 < t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (REAL_ARITH
   `&2 < t ==> &0 < t /\ ~(t = &0) /\ &0 < t - &1 /\
               &0 < &1 + t /\ ~(&1 + t = &0)`)) THEN
  SUBGOAL_THEN `y:real^N IN s` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[dist] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < k / &2 ==> k / &2 <= k ==> x <= k`)) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `&0 < k` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ABBREV_TAC `w:real^N = x + t % (y - x)` THEN
    SUBGOAL_THEN `w:real^N IN s` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "w" THEN
      REWRITE_TAC[dist; VECTOR_ARITH `x - (x + t) = --t:real^N`] THEN
      EXPAND_TAC "t" THEN REWRITE_TAC[NORM_NEG; NORM_MUL; REAL_ABS_DIV] THEN
      REWRITE_TAC[REAL_ABS_NORM; real_div; GSYM REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; NORM_POS_LT; VECTOR_SUB_EQ;
        REAL_MUL_RID; REAL_ARITH `&0 < x ==> abs(x) <= x`];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 / t) % w + (t - &1) / t % x = y:real^N` ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN
      REWRITE_TAC[VECTOR_ARITH
       `b % (x + c % (y - x)) + a % x =
        (a + b - b * c) % x + (b * c) % y`] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; VECTOR_MUL_LID] THEN
      ASM_SIMP_TAC[real_div; REAL_MUL_RINV; REAL_SUB_REFL;
                   VECTOR_MUL_LZERO; VECTOR_ADD_LID;
                   REAL_ARITH `(a - &1) * b + &1 * b - &1 = a * b - &1`];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [convex_on]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`w:real^N`; `x:real^N`; `&1 / t`; `(t - &1) / t`]) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_LT_01] THEN
    REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN
    ASM_SIMP_TAC[REAL_SUB_ADD2; REAL_MUL_RINV] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a * fw + (b - &1) * fx < e
      ==> fy <= a * fw + b * fx ==> fy - fx < e`) THEN
    ASM_SIMP_TAC[real_div; REAL_SUB_RDISTRIB; REAL_MUL_RINV; REAL_MUL_LID;
                 REAL_ARITH `a * x + y - a * y - y = a * (x - y)`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!b. abs(x) <= b /\ abs(y) <= b /\ &2 * b < z ==> x - y < z`) THEN
    EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[real_div; REAL_ARITH `(a * b) * inv c = (b * inv c) * a`] THEN
    ASM_REWRITE_TAC[GSYM real_div];

    ABBREV_TAC `w:real^N = x - t % (y - x)` THEN
    SUBGOAL_THEN `w:real^N IN s` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "w" THEN
      REWRITE_TAC[dist; VECTOR_ARITH `x - (x - t) = t:real^N`] THEN
      EXPAND_TAC "t" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_DIV] THEN
      REWRITE_TAC[REAL_ABS_NORM; real_div; GSYM REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; NORM_POS_LT; VECTOR_SUB_EQ;
        REAL_MUL_RID; REAL_ARITH `&0 < x ==> abs(x) <= x`];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 / (&1 + t)) % w + t / (&1 + t) % y = x:real^N`
    ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN
      REWRITE_TAC[VECTOR_ARITH
       `b % (x - c % (y - x)) + a % y =
        (b * (&1 + c)) % x + (a - b * c) % y`] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; VECTOR_MUL_LID] THEN
      REWRITE_TAC[real_div; REAL_MUL_AC; REAL_MUL_LID; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [convex_on]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`w:real^N`; `y:real^N`; `&1 / (&1 + t)`; `t / (&1 + t)`]) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_LT_01] THEN
    REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN
    ASM_SIMP_TAC[REAL_SUB_ADD2; REAL_MUL_RINV] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a * fw + (b - &1) * fx < e
      ==> fy <= a * fw + b * fx ==> fy - fx < e`) THEN
    SUBGOAL_THEN `t * inv(&1 + t) - &1 = --(inv(&1 + t))` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ARITH `(a * b - &1 = --b) <=> ((&1 + a) * b = &1)`] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(&1 * a) * x + --a * y = a * (x - y)`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!b. abs(x) <= b /\ abs(y) <= b /\ &2 * b < z ==> x - y < z`) THEN
    EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x < e * k ==> x < e * (&1 + k)`) THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[real_div; REAL_ARITH `(a * b) * inv c = (b * inv c) * a`] THEN
    ASM_REWRITE_TAC[GSYM real_div]]);;
