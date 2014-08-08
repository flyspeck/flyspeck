open Hol_core
include Vector3

(* ------------------------------------------------------------------------- *)
(* Some bounds on components etc. relative to operator norm.                 *)
(* ------------------------------------------------------------------------- *)

let NORM_COLUMN_LE_ONORM = prove
 (`!A:real^N^M i. norm(column i A) <= onorm(\x. A ** x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[column] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$i = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPEC `\x:real^N. (A:real^N^M) ** x` ONORM) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
  DISCH_THEN(MP_TAC o SPEC `basis l:real^N` o CONJUNCT1) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; NORM_BASIS; column; REAL_MUL_RID]);;

let MATRIX_COMPONENT_LE_ONORM = prove
 (`!A:real^N^M i j. abs(A$i$j) <= onorm(\x. A ** x)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(column l (A:real^N^M))` THEN
  REWRITE_TAC[NORM_COLUMN_LE_ONORM] THEN
  MP_TAC(ISPECL [`column l (A:real^N^M)`; `k:num`]
        COMPONENT_LE_NORM) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  ASM_SIMP_TAC[column; LAMBDA_BETA; REAL_LE_REFL]);;

let COMPONENT_LE_ONORM = prove
 (`!f:real^M->real^N i j. linear f ==> abs(matrix f$i$j) <= onorm f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
        [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
  REWRITE_TAC[MATRIX_COMPONENT_LE_ONORM]);;

(* ------------------------------------------------------------------------- *)
(* Basic lemmas about hyperplanes and halfspaces.                            *)
(* ------------------------------------------------------------------------- *)

let HYPERPLANE_EQ_EMPTY = prove
 (`!a:real^N b. {x | a dot x = b} = {} <=> a = vec 0 /\ ~(b = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `a:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO] THENL
   [MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `b / (a dot a) % a:real^N`) THEN
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0]]);;

let HYPERPLANE_EQ_UNIV = prove
 (`!a b. {x | a dot x = b} = (:real^N) <=> a = vec 0 /\ b = &0`,
  REPEAT GEN_TAC THEN  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
  ASM_CASES_TAC `a:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO] THENL
   [MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `(b + &1) / (a dot a) % a:real^N`) THEN
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0] THEN REAL_ARITH_TAC]);;

let HALFSPACE_EQ_EMPTY_LT = prove
 (`!a:real^N b. {x | a dot x < b} = {} <=> a = vec 0 /\ b <= &0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_SIMP_TAC[DOT_LZERO; SET_RULE `{x | p} = if p then UNIV else {}`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[UNIV_NOT_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `(b - &1) / (a dot a) % a:real^N` THEN
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0] THEN
    REAL_ARITH_TAC]);;

let HALFSPACE_EQ_EMPTY_GT = prove
 (`!a:real^N b. {x | a dot x > b} = {} <=> a = vec 0 /\ b >= &0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`--a:real^N`; `--b:real`] HALFSPACE_EQ_EMPTY_LT) THEN
  SIMP_TAC[real_gt; DOT_LNEG; REAL_LT_NEG2; VECTOR_NEG_EQ_0] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let HALFSPACE_EQ_EMPTY_LE = prove
 (`!a:real^N b. {x | a dot x <= b} = {} <=> a = vec 0 /\ b < &0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_SIMP_TAC[DOT_LZERO; SET_RULE `{x | p} = if p then UNIV else {}`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[UNIV_NOT_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `(b - &1) / (a dot a) % a:real^N` THEN
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0] THEN
    REAL_ARITH_TAC]);;

let HALFSPACE_EQ_EMPTY_GE = prove
 (`!a:real^N b. {x | a dot x >= b} = {} <=> a = vec 0 /\ b > &0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`--a:real^N`; `--b:real`] HALFSPACE_EQ_EMPTY_LE) THEN
  SIMP_TAC[real_ge; DOT_LNEG; REAL_LE_NEG2; VECTOR_NEG_EQ_0] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A non-injective linear function maps into a hyperplane.                   *)
(* ------------------------------------------------------------------------- *)

let ADJOINT_INJECTIVE = prove
 (`!f:real^M->real^N.
        linear f
        ==> ((!x y. adjoint f x = adjoint f y ==> x = y) <=>
             (!y. ?x. f x = y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM o MATCH_MP MATRIX_WORKS o MATCH_MP
   ADJOINT_LINEAR) THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM o MATCH_MP MATRIX_WORKS) THEN
  ASM_REWRITE_TAC[GSYM FULL_RANK_INJECTIVE; GSYM FULL_RANK_SURJECTIVE] THEN
  ASM_SIMP_TAC[MATRIX_ADJOINT; RANK_TRANSP]);;

let ADJOINT_SURJECTIVE = prove
 (`!f:real^M->real^N.
        linear f
        ==> ((!y. ?x. adjoint f x = y) <=> (!x y. f x = f y ==> x = y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [GSYM(MATCH_MP ADJOINT_ADJOINT th)]) THEN
  ASM_SIMP_TAC[ADJOINT_INJECTIVE; ADJOINT_LINEAR]);;

let ADJOINT_INJECTIVE_INJECTIVE = prove
 (`!f:real^N->real^N.
        linear f
        ==> ((!x y. adjoint f x = adjoint f y ==> x = y) <=>
             (!x y. f x = f y ==> x = y))`,
  SIMP_TAC[ADJOINT_INJECTIVE] THEN
  MESON_TAC[LINEAR_INJECTIVE_IMP_SURJECTIVE;
            LINEAR_SURJECTIVE_IMP_INJECTIVE]);;

let ADJOINT_INJECTIVE_INJECTIVE_0 = prove
 (`!f:real^N->real^N.
        linear f
        ==> ((!x. adjoint f x = vec 0 ==> x = vec 0) <=>
             (!x. f x = vec 0 ==> x = vec 0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ADJOINT_INJECTIVE_INJECTIVE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ADJOINT_LINEAR) THEN
  ASM_MESON_TAC[LINEAR_INJECTIVE_0]);;

let LINEAR_SINGULAR_INTO_HYPERPLANE = prove
 (`!f:real^N->real^N.
        linear f
        ==> (~(!x y. f(x) = f(y) ==> x = y) <=>
             ?a. ~(a = vec 0) /\ !x. a dot f(x) = &0)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
  ASM_SIMP_TAC[ADJOINT_WORKS; FORALL_DOT_EQ_0] THEN
  REWRITE_TAC[MESON[] `(?a. ~p a /\ q a) <=> ~(!a. q a ==> p a)`] THEN
  ASM_SIMP_TAC[ADJOINT_INJECTIVE_INJECTIVE_0; LINEAR_INJECTIVE_0]);;

let LINEAR_SINGULAR_IMAGE_HYPERPLANE = prove
 (`!f:real^N->real^N.
        linear f /\ ~(!x y. f(x) = f(y) ==> x = y)
        ==> ?a. ~(a = vec 0) /\ !s. IMAGE f s SUBSET {x | a dot x = &0}`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[LINEAR_SINGULAR_INTO_HYPERPLANE] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let LOWDIM_EXPAND_DIMENSION = prove
 (`!s:real^N->bool n.
        dim s <= n /\ n <= dimindex(:N)
        ==> ?t. dim(t) = n /\ span s SUBSET span t`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV) [LE_EXISTS] THEN
  SIMP_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  INDUCT_TAC THENL [MESON_TAC[ADD_CLAUSES; SUBSET_REFL]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `s + SUC d <= n <=> s + d < n`] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[LT_IMP_LE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[ADD_CLAUSES] THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `~(span t = (:real^N))` MP_TAC THENL
   [REWRITE_TAC[GSYM DIM_EQ_FULL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; NOT_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `(a:real^N) INSERT t` THEN ASM_REWRITE_TAC[DIM_INSERT; ADD1] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `span(t:real^N->bool)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_MONO THEN SET_TAC[]);;

let LOWDIM_EXPAND_BASIS = prove
 (`!s:real^N->bool n.
        dim s <= n /\ n <= dimindex(:N)
        ==> ?b. b HAS_SIZE n /\ independent b /\ span s SUBSET span b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC o
    MATCH_MP LOWDIM_EXPAND_DIMENSION) THEN
  MP_TAC(ISPEC `t:real^N->bool` BASIS_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SPAN_SPAN; SUBSET_TRANS; SPAN_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Orthogonal bases, Gram-Schmidt process, and related theorems.             *)
(* ------------------------------------------------------------------------- *)

let SPAN_DELETE_0 = prove
 (`!s:real^N->bool. span(s DELETE vec 0) = span s`,
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[DELETE_SUBSET; SPAN_MONO] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `span((vec 0:real^N) INSERT (s DELETE vec 0))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_MONO THEN SET_TAC[];
    SIMP_TAC[SUBSET; SPAN_BREAKDOWN_EQ; VECTOR_MUL_RZERO; VECTOR_SUB_RZERO]]);;

let SPAN_IMAGE_SCALE = prove
 (`!c s. FINITE s /\ (!x. x IN s ==> ~(c x = &0))
         ==> span (IMAGE (\x:real^N. c(x) % x) s) = span s`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IMAGE_CLAUSES; SPAN_BREAKDOWN_EQ; EXTENSION; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real^N->bool`] THEN
  STRIP_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
  EXISTS_TAC `k / (c:real^N->real) x` THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL]);;

let PAIRWISE_ORTHOGONAL_INDEPENDENT = prove
 (`!s:real^N->bool.
        pairwise orthogonal s /\ ~(vec 0 IN s) ==> independent s`,
  REWRITE_TAC[pairwise; orthogonal] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[independent; dependent] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[SPAN_EXPLICIT; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->real`] THEN
  REWRITE_TAC[SUBSET; IN_DELETE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x:real^N. a dot x`) THEN
  ASM_SIMP_TAC[DOT_RSUM; DOT_RMUL; REAL_MUL_RZERO; SUM_0] THEN
  ASM_MESON_TAC[DOT_EQ_0]);;

let PAIRWISE_ORTHOGONAL_IMP_FINITE = prove
 (`!s:real^N->bool. pairwise orthogonal s ==> FINITE s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `independent (s DELETE (vec 0:real^N))` MP_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
    REWRITE_TAC[IN_DELETE] THEN MATCH_MP_TAC PAIRWISE_MONO THEN
    EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[SUBSET; IN_DELETE];
    DISCH_THEN(MP_TAC o MATCH_MP INDEPENDENT_IMP_FINITE) THEN
    REWRITE_TAC[FINITE_DELETE]]);;

let GRAM_SCHMIDT_STEP = prove
 (`!s a x.
        pairwise orthogonal s /\ x IN span s
        ==> orthogonal x (a - vsum s (\b:real^N. (b dot a) / (b dot b) % b))`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ORTHOGONAL_SYM] ORTHOGONAL_TO_SPAN_EQ] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `x:real^N`] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PAIRWISE_ORTHOGONAL_IMP_FINITE) THEN
  REWRITE_TAC[orthogonal; DOT_RSUB] THEN ASM_SIMP_TAC[DOT_RSUM] THEN
  REWRITE_TAC[REAL_SUB_0; DOT_RMUL] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum s (\y:real^N. if y = x then y dot a else &0)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[SUM_DELTA; DOT_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pairwise; orthogonal]) THEN
  ASM_CASES_TAC `x:real^N = y` THEN ASM_SIMP_TAC[DOT_LMUL; REAL_MUL_RZERO] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; DOT_EQ_0; DOT_LZERO; REAL_MUL_RZERO]);;

let ORTHOGONAL_EXTENSION = prove
 (`!s t:real^N->bool.
        pairwise orthogonal s
        ==> ?u. pairwise orthogonal (s UNION u) /\
                span (s UNION u) = span (s UNION t)`,
  let lemma = prove
   (`!t s:real^N->bool.
        FINITE t /\ FINITE s /\ pairwise orthogonal s
        ==> ?u. pairwise orthogonal (s UNION u) /\
                span (s UNION u) = span (s UNION t)`,
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN EXISTS_TAC `{}:real^N->bool` THEN
      ASM_REWRITE_TAC[UNION_EMPTY];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `t:real^N->bool`] THEN
    REWRITE_TAC[pairwise; orthogonal] THEN REPEAT STRIP_TAC THEN
    ABBREV_TAC `a' = a - vsum s (\b:real^N. (b dot a) / (b dot b) % b)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(a':real^N) INSERT s`) THEN
    ASM_REWRITE_TAC[FINITE_INSERT] THEN ANTS_TAC THENL
     [SUBGOAL_THEN `!x:real^N. x IN s ==> a' dot x = &0`
       (fun th -> REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[DOT_SYM; th]) THEN
      REPEAT STRIP_TAC THEN EXPAND_TAC "a'" THEN
      REWRITE_TAC[GSYM orthogonal] THEN ONCE_REWRITE_TAC[ORTHOGONAL_SYM] THEN
      MATCH_MP_TAC GRAM_SCHMIDT_STEP THEN
      ASM_SIMP_TAC[pairwise; orthogonal; SPAN_CLAUSES];
      DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(a':real^N) INSERT u` THEN
      ASM_REWRITE_TAC[SET_RULE `s UNION a INSERT u = a INSERT s UNION u`] THEN
      REWRITE_TAC[SET_RULE `(x INSERT s) UNION t = x INSERT (s UNION t)`] THEN
      MATCH_MP_TAC EQ_SPAN_INSERT_EQ THEN EXPAND_TAC "a'" THEN
      REWRITE_TAC[VECTOR_ARITH `a - x - a:real^N = --x`] THEN
      MATCH_MP_TAC SPAN_NEG THEN MATCH_MP_TAC SPAN_VSUM THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SPAN_MUL THEN ASM_SIMP_TAC[SPAN_SUPERSET; IN_UNION]]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `span t:real^N->bool` BASIS_SUBSPACE_EXISTS) THEN
  REWRITE_TAC[SUBSPACE_SPAN; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `b:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `s:real^N->bool`] lemma) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[HAS_SIZE; PAIRWISE_ORTHOGONAL_IMP_FINITE];
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[SPAN_UNION]]);;

let ORTHOGONAL_EXTENSION_STRONG = prove
 (`!s t:real^N->bool.
        pairwise orthogonal s
        ==> ?u. DISJOINT u (vec 0 INSERT s) /\
                pairwise orthogonal (s UNION u) /\
                span (s UNION u) = span (s UNION t)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
    SPEC `t:real^N->bool` o MATCH_MP ORTHOGONAL_EXTENSION) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u DIFF ((vec 0:real^N) INSERT s)` THEN REPEAT CONJ_TAC THENL
   [SET_TAC[];
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        PAIRWISE_MONO)) THEN SET_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC BINOP_CONV [GSYM SPAN_DELETE_0] THEN
    AP_TERM_TAC THEN SET_TAC[]]);;

let ORTHONORMAL_EXTENSION = prove
 (`!s t:real^N->bool.
        pairwise orthogonal s /\ (!x. x IN s ==> norm x = &1)
        ==> ?u. DISJOINT u s /\
                pairwise orthogonal (s UNION u) /\
                (!x. x IN u ==> norm x = &1) /\
                span(s UNION u) = span(s UNION t)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
    SPEC `t:real^N->bool` o MATCH_MP ORTHOGONAL_EXTENSION_STRONG) THEN
  REWRITE_TAC[SET_RULE `DISJOINT u s <=> !x. x IN u ==> ~(x IN s)`] THEN
  REWRITE_TAC[IN_INSERT; DE_MORGAN_THM; pairwise] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\x:real^N. inv(norm x) % x) u` THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `norm(x:real^N) = &1` THEN
    ASM_SIMP_TAC[REAL_INV_1; VECTOR_MUL_LID] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `inv(norm x) % x:real^N`]) THEN
    ASM_REWRITE_TAC[IN_UNION; VECTOR_MUL_EQ_0; REAL_SUB_0; REAL_INV_EQ_1;
      VECTOR_ARITH `x:real^N = a % x <=> (a - &1) % x = vec 0`] THEN
    ASM_CASES_TAC `x:real^N = vec 0` THENL
     [ASM_MESON_TAC[VECTOR_MUL_RZERO];
      ASM_REWRITE_TAC[orthogonal; DOT_RMUL; REAL_ENTIRE; DOT_EQ_0] THEN
      ASM_REWRITE_TAC[REAL_INV_EQ_0; NORM_EQ_0]];
    REWRITE_TAC[IN_UNION; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[orthogonal; DOT_LMUL; DOT_RMUL; REAL_ENTIRE; DOT_EQ_0;
                 REAL_INV_EQ_0; NORM_EQ_0] THEN
    REWRITE_TAC[GSYM orthogonal] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_UNION] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[NORM_MUL; REAL_MUL_LINV; NORM_EQ_0; REAL_ABS_INV;
                 REAL_ABS_NORM];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SPAN_EQ; UNION_SUBSET] THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; SPAN_SUPERSET; SPAN_MUL; IN_UNION] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `x:real^N = norm(x) % inv(norm x) % x`
     (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
    THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID];
      MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
      REWRITE_TAC[IN_UNION; IN_IMAGE] THEN ASM_MESON_TAC[]]]);;

let VECTOR_IN_ORTHOGONAL_SPANNINGSET = prove
 (`!a. ?s. a IN s /\ pairwise orthogonal s /\ span s = (:real^N)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`{a:real^N}`; `(IMAGE basis (1..dimindex(:N))):real^N->bool`]
                 ORTHOGONAL_EXTENSION) THEN
  REWRITE_TAC[PAIRWISE_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{a:real^N} UNION u` THEN ASM_REWRITE_TAC[IN_UNION; IN_SING] THEN
  MATCH_MP_TAC(SET_RULE `!s. s = UNIV /\ s SUBSET t ==> t = UNIV`) THEN
  EXISTS_TAC `span {basis i:real^N | 1 <= i /\ i <= dimindex (:N)}` THEN
  CONJ_TAC THENL [REWRITE_TAC[SPAN_STDBASIS]; MATCH_MP_TAC SPAN_MONO] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; GSYM IN_NUMSEG] THEN SET_TAC[]);;

let VECTOR_IN_ORTHOGONAL_BASIS = prove
 (`!a. ~(a = vec 0)
       ==> ?s. a IN s /\ ~(vec 0 IN s) /\
               pairwise orthogonal s /\
               independent s /\
               s HAS_SIZE (dimindex(:N)) /\
               span s = (:real^N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `a:real^N` VECTOR_IN_ORTHOGONAL_SPANNINGSET) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s DELETE (vec 0:real^N)` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_SIMP_TAC[pairwise; IN_DELETE];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN ASM_SIMP_TAC[IN_DELETE];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SPAN_DELETE_0];
    DISCH_TAC THEN ASM_SIMP_TAC[BASIS_HAS_SIZE_UNIV]]);;

let VECTOR_IN_ORTHONORMAL_BASIS = prove
 (`!a. norm a = &1
       ==> ?s. a IN s /\
               pairwise orthogonal s /\
               (!x. x IN s ==> norm x = &1) /\
               independent s /\
               s HAS_SIZE (dimindex(:N)) /\
               span s = (:real^N)`,
  GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
  ASM_REWRITE_TAC[NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP VECTOR_IN_ORTHOGONAL_BASIS) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\x:real^N. inv(norm x) % x) s` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_MESON_TAC[ORTHOGONAL_CLAUSES];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_MESON_TAC[REAL_MUL_LINV; NORM_EQ_0];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0] THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[BASIS_HAS_SIZE_UNIV]] THEN
  UNDISCH_THEN `span s = (:real^N)` (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SPAN_IMAGE_SCALE THEN
  REWRITE_TAC[REAL_INV_EQ_0; NORM_EQ_0] THEN
  ASM_MESON_TAC[HAS_SIZE]);;

let BESSEL_INEQUALITY = prove
 (`!s x:real^N.
        pairwise orthogonal s /\ (!x. x IN s ==> norm x = &1)
        ==> sum s (\e. (e dot x) pow 2) <= norm(x) pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PAIRWISE_ORTHOGONAL_IMP_FINITE) THEN
  MP_TAC(ISPEC `x - vsum s (\e. (e dot x) % e):real^N` DOT_POS_LE) THEN
  REWRITE_TAC[NORM_POW_2; VECTOR_ARITH
   `(a - b:real^N) dot (a - b) = a dot a + b dot b - &2 * b dot a`] THEN
  ASM_SIMP_TAC[DOT_LSUM; REAL_POW_2; DOT_LMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `t = s ==> &0 <= x + t - &2 * s ==> s <= x`) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `e:real^N` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[DOT_RSUM] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum s (\k:real^N. if k = e then e dot x else &0)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[SUM_DELTA]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[DOT_RMUL] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[REAL_RING `a * x = a <=> a = &0 \/ x = &1`] THEN
    DISJ2_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N`) THEN
    ASM_REWRITE_TAC[NORM_EQ_SQUARE] THEN REAL_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise; orthogonal]) THEN
    ASM_SIMP_TAC[REAL_ENTIRE]]);;

(* ------------------------------------------------------------------------- *)
(* Analogous theorems for existence of orthonormal basis for a subspace.     *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_SPANNINGSET_SUBSPACE = prove
 (`!s:real^N->bool.
        subspace s
        ==> ?b. b SUBSET s /\ pairwise orthogonal b /\ span b = s`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s:real^N->bool` BASIS_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL[`{}:real^N->bool`; `b:real^N->bool`] ORTHOGONAL_EXTENSION) THEN
  REWRITE_TAC[PAIRWISE_EMPTY; UNION_EMPTY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_SUBSPACE THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[SPAN_INC]]);;

let ORTHOGONAL_BASIS_SUBSPACE = prove
 (`!s:real^N->bool.
        subspace s
        ==> ?b. ~(vec 0 IN b) /\
                b SUBSET s /\
                pairwise orthogonal b /\
                independent b /\
                b HAS_SIZE (dim s) /\
                span b = s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_SPANNINGSET_SUBSPACE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `b DELETE (vec 0:real^N)` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_SIMP_TAC[pairwise; IN_DELETE];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN ASM_SIMP_TAC[IN_DELETE];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SPAN_DELETE_0];
    DISCH_TAC THEN ASM_SIMP_TAC[BASIS_HAS_SIZE_DIM]]);;

let ORTHONORMAL_BASIS_SUBSPACE = prove
 (`!s:real^N->bool.
        subspace s
        ==> ?b. b SUBSET s /\
                pairwise orthogonal b /\
                (!x. x IN b ==> norm x = &1) /\
                independent b /\
                b HAS_SIZE (dim s) /\
                span b = s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_BASIS_SUBSPACE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\x:real^N. inv(norm x) % x) b` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[SPAN_MUL; SPAN_INC; SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_MESON_TAC[ORTHOGONAL_CLAUSES];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_MESON_TAC[REAL_MUL_LINV; NORM_EQ_0];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0] THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[BASIS_HAS_SIZE_DIM]] THEN
  UNDISCH_THEN `span b = (s:real^N->bool)` (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SPAN_IMAGE_SCALE THEN
  REWRITE_TAC[REAL_INV_EQ_0; NORM_EQ_0] THEN
  ASM_MESON_TAC[HAS_SIZE]);;

let ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN = prove
 (`!s t:real^N->bool.
        span s PSUBSET span t
        ==> ?x. ~(x = vec 0) /\ x IN span t /\
                (!y. y IN span s ==> orthogonal x y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `span s:real^N->bool` ORTHOGONAL_BASIS_SUBSPACE) THEN
  REWRITE_TAC[SUBSPACE_SPAN] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `{u:real^N}`] ORTHOGONAL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ns:real^N->bool` MP_TAC) THEN
  ASM_CASES_TAC `ns SUBSET (vec 0:real^N) INSERT b` THENL
   [DISCH_THEN(MP_TAC o AP_TERM `(IN) (u:real^N)` o CONJUNCT2) THEN
    SIMP_TAC[SPAN_SUPERSET; IN_UNION; IN_SING] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    SUBGOAL_THEN `~(u IN span (b UNION {vec 0:real^N}))` MP_TAC THENL
     [ASM_REWRITE_TAC[SET_RULE `s UNION {a} = a INSERT s`; SPAN_INSERT_0];
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> ~(x IN t) ==> ~(x IN s)`) THEN
      MATCH_MP_TAC SPAN_MONO THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `~(s SUBSET t) ==> ?z. z IN s /\ ~(z IN t)`)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_INSERT; DE_MORGAN_THM] THEN
  X_GEN_TAC `n:real^N` THEN STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `n:real^N`) THEN ASM_REWRITE_TAC[IN_UNION] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_TAC THEN EXISTS_TAC `n:real^N` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(n:real^N) IN span (b UNION ns)` MP_TAC THENL
     [MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[] THEN SPEC_TAC(`n:real^N`,`n:real^N`) THEN
      REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN REWRITE_TAC[SUBSPACE_SPAN] THEN
      ASM_REWRITE_TAC[SET_RULE
       `s UNION {a} SUBSET t <=> s SUBSET t /\ a IN t`] THEN
      ASM_MESON_TAC[SPAN_INC; SUBSET_TRANS]];
    MATCH_MP_TAC SPAN_INDUCT THEN
    REWRITE_TAC[SET_RULE `(\y. orthogonal n y) = {y | orthogonal n y}`] THEN
    REWRITE_TAC[SUBSPACE_ORTHOGONAL_TO_VECTOR] THEN ASM SET_TAC[]]);;

let ORTHOGONAL_TO_SUBSPACE_EXISTS = prove
 (`!s:real^N->bool. dim s < dimindex(:N)
                    ==> ?x. ~(x = vec 0) /\ !y. y IN s ==> orthogonal x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `(:real^N)`]
        ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN) THEN
  ANTS_TAC THENL [REWRITE_TAC[PSUBSET]; MESON_TAC[SPAN_SUPERSET]] THEN
  REWRITE_TAC[SPAN_UNIV; SUBSET_UNIV] THEN
  ASM_MESON_TAC[DIM_SPAN; DIM_UNIV; LT_REFL]);;

let ORTHOGONAL_TO_VECTOR_EXISTS = prove
 (`!x:real^N. 2 <= dimindex(:N) ==> ?y. ~(y = vec 0) /\ orthogonal x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{x:real^N}` ORTHOGONAL_TO_SUBSPACE_EXISTS) THEN
  SIMP_TAC[DIM_SING; IN_SING; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; MESON_TAC[ORTHOGONAL_SYM]]);;

let SPAN_NOT_UNIV_ORTHOGONAL = prove
 (`!s. ~(span s = (:real^N))
         ==> ?a. ~(a = vec 0) /\ !x. x IN span s ==> a dot x = &0`,
  REWRITE_TAC[GSYM DIM_EQ_FULL; GSYM LE_ANTISYM; DIM_SUBSET_UNIV;
              NOT_LE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM orthogonal] THEN
  MATCH_MP_TAC ORTHOGONAL_TO_SUBSPACE_EXISTS THEN ASM_REWRITE_TAC[DIM_SPAN]);;

let SPAN_NOT_UNIV_SUBSET_HYPERPLANE = prove
 (`!s. ~(span s = (:real^N))
       ==> ?a. ~(a = vec 0) /\ span s SUBSET {x | a dot x = &0}`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM; SPAN_NOT_UNIV_ORTHOGONAL]);;

let LOWDIM_SUBSET_HYPERPLANE = prove
 (`!s. dim s < dimindex(:N)
       ==> ?a:real^N. ~(a = vec 0) /\ span s SUBSET {x | a dot x = &0}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_NOT_UNIV_SUBSET_HYPERPLANE THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIM_SUBSET) THEN
  ASM_REWRITE_TAC[NOT_LE; DIM_SPAN; DIM_UNIV]);;

let VECTOR_EQ_DOT_SPAN = prove
 (`!b x y:real^N.
        (!v. v IN b ==> v dot x = v dot y) /\ x IN span b /\ y IN span b
        ==> x = y`,
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0; GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM DOT_RSUB; GSYM ORTHOGONAL_REFL; GSYM orthogonal] THEN
  MESON_TAC[ORTHOGONAL_TO_SPAN; SPAN_SUB; ORTHOGONAL_SYM]);;

let ORTHONORMAL_BASIS_EXPAND = prove
 (`!b x:real^N.
        pairwise orthogonal b /\ (!v. v IN b ==> norm v = &1) /\ x IN span b
   ==> vsum b (\v. (v dot x) % v) = x`,
  REWRITE_TAC[NORM_EQ_1] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VECTOR_EQ_DOT_SPAN THEN EXISTS_TAC `b:real^N->bool` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PAIRWISE_ORTHOGONAL_IMP_FINITE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pairwise; orthogonal]) THEN
  ASM_SIMP_TAC[SPAN_VSUM; SPAN_MUL; DOT_RSUM; DOT_RMUL; SPAN_SUPERSET] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  TRANS_TAC EQ_TRANS `sum b (\w:real^N. if w = v then v dot x else &0)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[SUM_DELTA]] THEN
  MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_MUL_RID; REAL_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Decomposing a vector into parts in orthogonal subspaces.                  *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE = prove
 (`!s t x y x' y':real^N.
        (!a b. a IN s /\ b IN t ==> orthogonal a b) /\
        x IN span s /\ x' IN span s /\ y IN span t /\ y' IN span t /\
        x + y = x' + y'
        ==> x = x' /\ y = y'`,
  REWRITE_TAC[VECTOR_ARITH `x + y:real^N = x' + y' <=> x - x' = y' - y`] THEN
  ONCE_REWRITE_TAC[GSYM ORTHOGONAL_TO_SPANS_EQ] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[VECTOR_ARITH
   `x:real^N = x' /\ y:real^N = y' <=> x - x' = vec 0 /\ y' - y = vec 0`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GSYM ORTHOGONAL_REFL] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  ASM_MESON_TAC[ORTHOGONAL_CLAUSES; ORTHOGONAL_SYM]);;

let ORTHOGONAL_SUBSPACE_DECOMP_EXISTS = prove
 (`!s x:real^N. ?y z. y IN span s /\ (!w. w IN span s ==> orthogonal z w) /\
                      x = y + z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `span s:real^N->bool` ORTHOGONAL_BASIS_SUBSPACE) THEN
  REWRITE_TAC[SUBSPACE_SPAN; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `vsum t (\b:real^N. (b dot x) / (b dot b) % b)` THEN
  EXISTS_TAC `x - vsum t (\b:real^N. (b dot x) / (b dot b) % b)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_VSUM THEN
    ASM_SIMP_TAC[INDEPENDENT_IMP_FINITE; SPAN_CLAUSES];
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ORTHOGONAL_SYM] THEN
    MATCH_MP_TAC GRAM_SCHMIDT_STEP THEN ASM_SIMP_TAC[];
    VECTOR_ARITH_TAC]);;

let ORTHOGONAL_SUBSPACE_DECOMP = prove
 (`!s x. ?!(y,z). y IN span s /\
                  z IN {z:real^N | !x. x IN span s ==> orthogonal z x} /\
                  x = y + z`,
  REWRITE_TAC[EXISTS_UNIQUE_DEF; IN_ELIM_THM] THEN
  REWRITE_TAC[EXISTS_PAIRED_THM; FORALL_PAIRED_THM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; ORTHOGONAL_SUBSPACE_DECOMP_EXISTS] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  MATCH_MP_TAC ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`s:real^N->bool`; `{z:real^N | !x. x IN span s ==> orthogonal z x}`] THEN
  ASM_SIMP_TAC[SPAN_CLAUSES; IN_ELIM_THM] THEN
  ASM_MESON_TAC[SPAN_CLAUSES; ORTHOGONAL_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Existence of isometry between subspaces of same dimension.                *)
(* ------------------------------------------------------------------------- *)

let ISOMETRY_SUBSET_SUBSPACE = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s <= dim t
        ==> ?f. linear f /\ IMAGE f s SUBSET t /\
                (!x. x IN s ==> norm(f x) = norm(x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:real^N->bool` ORTHONORMAL_BASIS_SUBSPACE) THEN
  MP_TAC(ISPEC `s:real^M->bool` ORTHONORMAL_BASIS_SUBSPACE) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^M->bool`; `c:real^N->bool`] CARD_LE_INJ) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; INJECTIVE_ON_ALT] THEN
  X_GEN_TAC `fb:real^M->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`fb:real^M->real^N`; `b:real^M->bool`]
    LINEAR_INDEPENDENT_EXTEND) THEN
  ASM_REWRITE_TAC[IMP_IMP; LEFT_AND_EXISTS_THM; INJECTIVE_ON_ALT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `span b:real^M->bool = s`)] THEN
    ASM_SIMP_TAC[GSYM SPAN_LINEAR_IMAGE] THEN
    REWRITE_TAC[SYM(ASSUME `span c:real^N->bool = t`)] THEN
    MATCH_MP_TAC SPAN_MONO THEN ASM SET_TAC[];
    UNDISCH_THEN `span b:real^M->bool = s` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[SPAN_FINITE] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:real^M`; `u:real^M->real`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[LINEAR_VSUM] THEN
    REWRITE_TAC[o_DEF; NORM_EQ_SQUARE; NORM_POS_LE; GSYM NORM_POW_2] THEN
    ASM_SIMP_TAC[LINEAR_CMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o rand o snd) THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o lhand o rand o snd) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_SIMP_TAC[pairwise; ORTHOGONAL_CLAUSES] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[ORTHOGONAL_MUL] THEN ASM SET_TAC[];
      REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_SIMP_TAC[NORM_MUL] THEN
      MATCH_MP_TAC SUM_EQ THEN ASM SET_TAC[]]]);;

let ISOMETRIES_SUBSPACES = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t
        ==> ?f g. linear f /\ linear g /\
                  IMAGE f s = t /\ IMAGE g t = s /\
                  (!x. x IN s ==> norm(f x) = norm x) /\
                  (!y. y IN t ==> norm(g y) = norm y) /\
                  (!x. x IN s ==> g(f x) = x) /\
                  (!y. y IN t ==> f(g y) = y)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `n = dim(t:real^N->bool)` THEN
  MP_TAC(ISPEC `t:real^N->bool` ORTHONORMAL_BASIS_SUBSPACE) THEN
  MP_TAC(ISPEC `s:real^M->bool` ORTHONORMAL_BASIS_SUBSPACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^M->bool`; `c:real^N->bool`] CARD_EQ_BIJECTIONS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`fb:real^M->real^N`; `gb:real^N->real^M`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`gb:real^N->real^M`; `c:real^N->bool`]
    LINEAR_INDEPENDENT_EXTEND) THEN
  MP_TAC(ISPECL [`fb:real^M->real^N`; `b:real^M->bool`]
    LINEAR_INDEPENDENT_EXTEND) THEN
  ASM_REWRITE_TAC[IMP_IMP; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `span b:real^M->bool = s`)] THEN
    ASM_SIMP_TAC[GSYM SPAN_LINEAR_IMAGE] THEN
    REWRITE_TAC[SYM(ASSUME `span c:real^N->bool = t`)] THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[SYM(ASSUME `span c:real^N->bool = t`)] THEN
    ASM_SIMP_TAC[GSYM SPAN_LINEAR_IMAGE] THEN
    REWRITE_TAC[SYM(ASSUME `span b:real^M->bool = s`)] THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    UNDISCH_THEN `span b:real^M->bool = s` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[SPAN_FINITE] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:real^M`; `u:real^M->real`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[LINEAR_VSUM] THEN
    REWRITE_TAC[o_DEF; NORM_EQ_SQUARE; NORM_POS_LE; GSYM NORM_POW_2] THEN
    ASM_SIMP_TAC[LINEAR_CMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o rand o snd) THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o lhand o rand o snd) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_SIMP_TAC[pairwise; ORTHOGONAL_CLAUSES] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[ORTHOGONAL_MUL] THEN ASM SET_TAC[];
      REPEAT(DISCH_THEN SUBST1_TAC) THEN
      ASM_SIMP_TAC[NORM_MUL]];
    UNDISCH_THEN `span c:real^N->bool = t` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[SPAN_FINITE] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `u:real^N->real`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[LINEAR_VSUM] THEN
    REWRITE_TAC[o_DEF; NORM_EQ_SQUARE; NORM_POS_LE; GSYM NORM_POW_2] THEN
    ASM_SIMP_TAC[LINEAR_CMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o rand o snd) THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o lhand o rand o snd) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_SIMP_TAC[pairwise; ORTHOGONAL_CLAUSES] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[ORTHOGONAL_MUL] THEN ASM SET_TAC[];
      REPEAT(DISCH_THEN SUBST1_TAC) THEN
      ASM_SIMP_TAC[NORM_MUL]];
    REWRITE_TAC[SYM(ASSUME `span b:real^M->bool = s`)] THEN
    MATCH_MP_TAC SPAN_INDUCT THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; IN]; ALL_TAC] THEN
    REWRITE_TAC[subspace; IN] THEN ASM_MESON_TAC[linear; LINEAR_0];
    REWRITE_TAC[SYM(ASSUME `span c:real^N->bool = t`)] THEN
    MATCH_MP_TAC SPAN_INDUCT THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; IN]; ALL_TAC] THEN
    REWRITE_TAC[subspace; IN] THEN ASM_MESON_TAC[linear; LINEAR_0]]);;

let ISOMETRY_SUBSPACES = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t
        ==> ?f:real^M->real^N. linear f /\ IMAGE f s = t /\
                               (!x. x IN s ==> norm(f x) = norm(x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP ISOMETRIES_SUBSPACES) THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]);;

let ISOMETRY_UNIV_SUBSPACE = prove
 (`!s. subspace s /\ dimindex(:M) = dim s
       ==> ?f:real^M->real^N.
                linear f /\ IMAGE f (:real^M) = s /\
                (!x. norm(f x) = norm(x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `s:real^N->bool`] ISOMETRY_SUBSPACES) THEN
  ASM_REWRITE_TAC[SUBSPACE_UNIV; IN_UNIV; DIM_UNIV]);;

let ISOMETRY_UNIV_SUPERSET_SUBSPACE = prove
 (`!s. subspace s /\ dim s <= dimindex(:M) /\ dimindex(:M) <= dimindex(:N)
       ==> ?f:real^M->real^N.
                linear f /\ s SUBSET (IMAGE f (:real^M)) /\
                (!x. norm(f x) = norm(x))`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LOWDIM_EXPAND_DIMENSION) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(:real^M)`; `span t:real^N->bool`] ISOMETRY_SUBSPACES) THEN
  ASM_REWRITE_TAC[SUBSPACE_SPAN; SUBSPACE_UNIV; DIM_UNIV; DIM_SPAN] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[IN_UNIV] THEN
  ASM_MESON_TAC[SUBSET; SPAN_INC]);;

let ISOMETRY_UNIV_UNIV = prove
 (`dimindex(:M) <= dimindex(:N)
   ==> ?f:real^M->real^N. linear f /\ (!x. norm(f x) = norm(x))`,
  DISCH_TAC THEN
  MP_TAC(ISPEC `{vec 0:real^N}`ISOMETRY_UNIV_SUPERSET_SUBSPACE) THEN
  ASM_REWRITE_TAC[SUBSPACE_TRIVIAL] THEN
  ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC(ARITH_RULE `x = 0 /\ 1 <= y ==> x <= y`) THEN
  ASM_REWRITE_TAC[DIM_EQ_0; DIMINDEX_GE_1] THEN SET_TAC[]);;

let SUBSPACE_ISOMORPHISM = prove
 (`!s t. subspace s /\ subspace t /\ dim(s) = dim(t)
         ==> ?f:real^M->real^N.
                linear f /\ (IMAGE f s = t) /\
                (!x y. x IN s /\ y IN s /\ f x = f y ==> (x = y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ISOMETRY_SUBSPACES) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[LINEAR_INJECTIVE_0_SUBSPACE] THEN MESON_TAC[NORM_EQ_0]);;

let ISOMORPHISMS_UNIV_UNIV = prove
 (`dimindex(:M) = dimindex(:N)
   ==> ?f:real^M->real^N g.
            linear f /\ linear g /\
            (!x. norm(f x) = norm x) /\ (!y. norm(g y) = norm y) /\
            (!x. g(f x) = x) /\ (!y. f(g y) = y)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(\x. lambda i. x$i):real^M->real^N` THEN
  EXISTS_TAC `(\x. lambda i. x$i):real^N->real^M` THEN
  SIMP_TAC[vector_norm; dot; LAMBDA_BETA] THEN
  SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           LAMBDA_BETA] THEN
  FIRST_ASSUM SUBST1_TAC THEN SIMP_TAC[LAMBDA_BETA] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN SIMP_TAC[LAMBDA_BETA]);;

(* ------------------------------------------------------------------------- *)
(* Properties of special hyperplanes.                                        *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_HYPERPLANE = prove
 (`!a. subspace {x:real^N | a dot x = &0}`,
  SIMP_TAC[subspace; DOT_RADD; DOT_RMUL; IN_ELIM_THM; REAL_ADD_LID;
           REAL_MUL_RZERO; DOT_RZERO]);;

let SUBSPACE_SPECIAL_HYPERPLANE = prove
 (`!k. subspace {x:real^N | x$k = &0}`,
  SIMP_TAC[subspace; IN_ELIM_THM; VEC_COMPONENT;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC);;

let SPECIAL_HYPERPLANE_SPAN = prove
 (`!k. 1 <= k /\ k <= dimindex(:N)
       ==> {x:real^N | x$k = &0} =
           span(IMAGE basis ((1..dimindex(:N)) DELETE k))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SPAN_SUBSPACE THEN
  ASM_SIMP_TAC[SUBSPACE_SPECIAL_HYPERPLANE] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; IN_DELETE];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    SIMP_TAC[SPAN_FINITE; FINITE_IMAGE; FINITE_DELETE; FINITE_NUMSEG] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `\v:real^N. x dot v` THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG; IN_NUMSEG; IN_DELETE] THEN
      MESON_TAC[BASIS_INJ];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
      ASM_SIMP_TAC[VSUM_DELETE; FINITE_NUMSEG; IN_NUMSEG; DOT_BASIS] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO]]]);;

let DIM_SPECIAL_HYPERPLANE = prove
 (`!k. 1 <= k /\ k <= dimindex(:N)
       ==> dim {x:real^N | x$k = &0} = dimindex(:N) - 1`,
  SIMP_TAC[SPECIAL_HYPERPLANE_SPAN] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DIM_UNIQUE THEN
  EXISTS_TAC `IMAGE (basis:num->real^N) ((1..dimindex(:N)) DELETE k)` THEN
  REWRITE_TAC[SUBSET_REFL; SPAN_INC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INDEPENDENT_MONO THEN
    EXISTS_TAC `{basis i:real^N | 1 <= i /\ i <= dimindex(:N)}` THEN
    REWRITE_TAC[INDEPENDENT_STDBASIS; SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_DELETE; IN_NUMSEG; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG; IN_NUMSEG; IN_DELETE] THEN
      MESON_TAC[BASIS_INJ];
      ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; FINITE_NUMSEG; CARD_DELETE;
                   FINITE_IMAGE; IN_NUMSEG; CARD_NUMSEG_1]]]);;

(* ------------------------------------------------------------------------- *)
(* More theorems about dimensions of different subspaces.                    *)
(* ------------------------------------------------------------------------- *)

let DIM_IMAGE_KERNEL_GEN = prove
 (`!f:real^M->real^N s.
        linear f /\ subspace s
        ==> dim(IMAGE f s) + dim {x | x IN s /\  f x = vec 0} = dim(s)`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPEC `{x | x IN s /\ (f:real^M->real^N) x = vec 0}` BASIS_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v:real^M->bool`; `s:real^M->bool`]
    MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `span(w:real^M->bool) = s`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th] THEN
              ASSUME_TAC th)
  THENL [ASM_SIMP_TAC[SPAN_SUBSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `subspace {x | x IN s /\ (f:real^M->real^N) x = vec 0}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER {x | P x}`] THEN
    ASM_SIMP_TAC[SUBSPACE_INTER; SUBSPACE_KERNEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x | x IN s /\ (f:real^M->real^N) x = vec 0} = span v`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_ANTISYM; SPAN_SUBSET_SUBSPACE; SUBSPACE_KERNEL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[DIM_SPAN; DIM_EQ_CARD] THEN
  SUBGOAL_THEN
   `!x. x IN span(w DIFF v) /\ (f:real^M->real^N) x = vec 0 ==> x = vec 0`
  (LABEL_TAC "*") THENL
   [MATCH_MP_TAC(SET_RULE
     `!t. s SUBSET t /\ (!x. x IN s /\ x IN t /\ P x ==> Q x)
          ==> (!x. x IN s /\ P x ==> Q x)`) THEN
    EXISTS_TAC `s:real^M->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SPAN_MONO; SUBSET_DIFF]; ALL_TAC] THEN
    ASM_SIMP_TAC[SPAN_FINITE; IN_ELIM_THM; IMP_CONJ; FINITE_DIFF;
                 INDEPENDENT_IMP_FINITE; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN X_GEN_TAC `u:real^M->real` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IMP_IMP] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `y IN s /\ f y = a <=> y IN {x | x IN s /\ f x = a}`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SPAN_FINITE; INDEPENDENT_IMP_FINITE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `t:real^M->real`) THEN
    MP_TAC(ISPEC `w:real^M->bool` INDEPENDENT_EXPLICIT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC
     `(\x. if x IN w DIFF v then --u x else t x):real^M->real`) THEN
    ASM_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC[VSUM_CASES; INDEPENDENT_IMP_FINITE] THEN
    REWRITE_TAC[SET_RULE `{x | x IN w /\ x IN (w DIFF v)} = w DIFF v`] THEN
    SIMP_TAC[ASSUME `(v:real^M->bool) SUBSET w`; SET_RULE
     `v SUBSET w ==> {x | x IN w /\ ~(x IN (w DIFF v))} = v`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LNEG; VSUM_NEG; VECTOR_ADD_LINV] THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC VSUM_EQ_0 THEN MP_TAC th) THEN
    REWRITE_TAC[REAL_NEG_EQ_0; VECTOR_MUL_EQ_0; IN_DIFF] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN (w DIFF v) /\ y IN (w DIFF v) /\
                      (f:real^M->real^N) x = f y ==> x = y`
  ASSUME_TAC THENL
   [REMOVE_THEN "*" MP_TAC THEN
    ASM_SIMP_TAC[GSYM LINEAR_INJECTIVE_0_SUBSPACE; SUBSPACE_SPAN] THEN
    MP_TAC(ISPEC `w DIFF v:real^M->bool` SPAN_INC) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) s = span(IMAGE f (w DIFF v))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC;
      ASM_MESON_TAC[SUBSPACE_LINEAR_IMAGE; SPAN_MONO; IMAGE_SUBSET;
                    SUBSET_TRANS; SUBSET_DIFF; SPAN_EQ_SELF]] THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^M` THEN
    DISCH_TAC THEN UNDISCH_TAC `span w:real^M->bool = s` THEN
    REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `x:real^M`) THEN
    (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
     [IN_UNIV; SPAN_FINITE; INDEPENDENT_IMP_FINITE; IN_ELIM_THM;
      FINITE_IMAGE; FINITE_DIFF; ASSUME `independent(w:real^M->bool)`] THEN
    REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
    X_GEN_TAC `u:real^M->real` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
    DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^M`) THEN
    EXISTS_TAC `(u:real^M->real) o (g:real^N->real^M)` THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FINITE_DIFF; INDEPENDENT_IMP_FINITE; LINEAR_VSUM] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[o_DEF] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_EQ_SUPERSET THEN
    SIMP_TAC[SUBSET_DIFF; FINITE_DIFF; INDEPENDENT_IMP_FINITE;
             LINEAR_CMUL; IN_DIFF; TAUT `a /\ ~(a /\ ~b) <=> a /\ b`;
             ASSUME `independent(w:real^M->bool)`;
             ASSUME `linear(f:real^M->real^N)`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM SET_TAC[];
    SUBGOAL_THEN `independent(IMAGE (f:real^M->real^N) (w DIFF v))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE_GEN THEN
      ASM_SIMP_TAC[LINEAR_INJECTIVE_0_SUBSPACE; SUBSPACE_SPAN] THEN
      ASM_MESON_TAC[INDEPENDENT_MONO; SUBSET_DIFF];
      ASM_SIMP_TAC[DIM_SPAN; DIM_EQ_CARD] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o
        lhand o lhand o snd) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[FINITE_DIFF; CARD_DIFF; INDEPENDENT_IMP_FINITE] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUB_ADD THEN
      ASM_MESON_TAC[CARD_SUBSET; INDEPENDENT_IMP_FINITE]]]);;

let DIM_IMAGE_KERNEL = prove
 (`!f:real^M->real^N.
        linear f
        ==> dim(IMAGE f (:real^M)) + dim {x | f x = vec 0} = dimindex(:M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(:real^M)`] DIM_IMAGE_KERNEL_GEN) THEN
  ASM_REWRITE_TAC[SUBSPACE_UNIV; IN_UNIV; DIM_UNIV]);;

let DIM_SUMS_INTER = prove
 (`!s t:real^N->bool.
    subspace s /\ subspace t
    ==> dim {x + y | x IN s /\ y IN t} + dim(s INTER t) = dim(s) + dim(t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s INTER t:real^N->bool` BASIS_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `s:real^N->bool`]
    MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `t:real^N->bool`]
    MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:real^N->bool) INTER d = b` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[SUBSET_INTER] THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN MP_TAC(ISPEC `c:real^N->bool` independent) THEN
    ASM_REWRITE_TAC[dependent; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^N) IN span b` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_INTER; SPAN_INC];
      MP_TAC(ISPECL [`b:real^N->bool`; `c DELETE (x:real^N)`] SPAN_MONO) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `dim (s INTER t:real^N->bool) = CARD(b:real^N->bool) /\
    dim s = CARD c /\ dim t = CARD d /\
    dim {x + y:real^N | x IN s /\ y IN t} = CARD(c UNION d:real^N->bool)`
  (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CARD_UNION_GEN; INDEPENDENT_IMP_FINITE] THEN
    MATCH_MP_TAC(ARITH_RULE `b:num <= c ==> (c + d) - b + b = c + d`) THEN
    ASM_SIMP_TAC[CARD_SUBSET; INDEPENDENT_IMP_FINITE]] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC DIM_UNIQUE THENL
   [EXISTS_TAC `b:real^N->bool`;
    EXISTS_TAC `c:real^N->bool`;
    EXISTS_TAC `d:real^N->bool`;
    EXISTS_TAC `c UNION d:real^N->bool`] THEN
  ASM_SIMP_TAC[HAS_SIZE; INDEPENDENT_IMP_FINITE; FINITE_UNION] THEN
  REWRITE_TAC[UNION_SUBSET; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; FORALL_IN_GSPEC] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real^N`; `vec 0:real^N`] THEN
    ASM_SIMP_TAC[SUBSPACE_0; VECTOR_ADD_RID] THEN ASM SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `x:real^N`] THEN
    ASM_SIMP_TAC[SUBSPACE_0; VECTOR_ADD_LID] THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL[`c:real^N->bool`; `c UNION d:real^N->bool`] SPAN_MONO);
      MP_TAC(ISPECL[`d:real^N->bool`; `c UNION d:real^N->bool`] SPAN_MONO)] THEN
    REWRITE_TAC[SUBSET_UNION] THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INDEPENDENT_EXPLICIT; FINITE_UNION; INDEPENDENT_IMP_FINITE] THEN
  X_GEN_TAC `a:real^N->real` THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [SET_RULE `s UNION t = s UNION (t DIFF s)`] THEN
  ASM_SIMP_TAC[VSUM_UNION; SET_RULE `DISJOINT c (d DIFF c)`;
               INDEPENDENT_IMP_FINITE; FINITE_DIFF; FINITE_UNION] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(vsum (d DIFF c) (\v:real^N. a v % v)) IN span b`
  MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (VECTOR_ARITH
       `a + b = vec 0 ==> b = --a`)) THEN
      MATCH_MP_TAC SUBSPACE_NEG THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSPACE_VSUM THEN
    ASM_SIMP_TAC[FINITE_DIFF; INDEPENDENT_IMP_FINITE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSPACE_MUL THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SPAN_FINITE; INDEPENDENT_IMP_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `e:real^N->real`) THEN
  MP_TAC(ISPEC `c:real^N->bool` INDEPENDENT_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (MP_TAC o SPEC `(\x. if x IN b then a x + e x else a x):real^N->real`)) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  ONCE_REWRITE_TAC[COND_RATOR] THEN ASM_SIMP_TAC[VSUM_CASES] THEN
  REWRITE_TAC[VECTOR_ADD_RDISTRIB; GSYM DIFF] THEN
  ASM_SIMP_TAC[SET_RULE `b SUBSET c ==> {x | x IN c /\ x IN b} = b`] THEN
  ASM_SIMP_TAC[VSUM_ADD; INDEPENDENT_IMP_FINITE] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `(a + b) + c:real^N = (a + c) + b`] THEN
  ASM_SIMP_TAC[GSYM VSUM_UNION; FINITE_DIFF; INDEPENDENT_IMP_FINITE;
               SET_RULE `DISJOINT b (c DIFF b)`] THEN
  ASM_SIMP_TAC[SET_RULE `b SUBSET c ==> b UNION (c DIFF b) = c`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!v:real^N. v IN (c DIFF b) ==> a v = &0` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `d:real^N->bool` INDEPENDENT_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (MP_TAC o SPEC `a:real^N->real`)) THEN
  SUBGOAL_THEN `d:real^N->bool = b UNION (d DIFF c)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ASM_SIMP_TAC[VSUM_UNION; FINITE_DIFF; INDEPENDENT_IMP_FINITE;
               SET_RULE `c INTER d = b ==> DISJOINT b (d DIFF c)`] THEN
  SUBGOAL_THEN `vsum b (\x:real^N. a x % x) = vsum c (\x. a x % x)`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0] THEN ASM_MESON_TAC[]);;

let DIM_KERNEL_COMPOSE = prove
 (`!f:real^M->real^N g:real^N->real^P.
        linear f /\ linear g
        ==> dim {x | (g o f) x = vec 0} <=
                dim {x | f(x) = vec 0} +
                dim {y | g(y) = vec 0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{x | (f:real^M->real^N) x = vec 0}` BASIS_EXISTS_FINITE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?c. FINITE c /\
        IMAGE f c SUBSET {y | g(y):real^P = vec 0} /\
        independent (IMAGE (f:real^M->real^N) c) /\
        IMAGE f (:real^M) INTER {y | g(y) = vec 0} SUBSET span(IMAGE f c) /\
        (!x y. x IN c /\ y IN c ==> (f x = f y <=> x = y)) /\
        (IMAGE f c) HAS_SIZE dim (IMAGE f (:real^M) INTER {y | g(y) = vec 0})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (f:real^M->real^N) (:real^M) INTER
                 {x | (g:real^N->real^P) x = vec 0}` BASIS_EXISTS_FINITE) THEN
    REWRITE_TAC[SUBSET_INTER; GSYM CONJ_ASSOC; EXISTS_FINITE_SUBSET_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `c:real^M->bool`]
        IMAGE_INJECTIVE_IMAGE_OF_SUBSET) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FINITE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `dim(span(b UNION c:real^M->bool))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIM_SUBSET THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; o_THM] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^M->real^N) x IN span(IMAGE f c)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SPAN_LINEAR_IMAGE; IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
    SUBST1_TAC(VECTOR_ARITH `x:real^M = y + (x - y)`) THEN
    MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET_UNION; SPAN_MONO; SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!t. x IN t /\ t SUBSET s ==> x IN s`) THEN
    EXISTS_TAC `{x | (f:real^M->real^N) x = vec 0}` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[LINEAR_SUB; VECTOR_SUB_EQ];
      ASM_MESON_TAC[SUBSET_TRANS; SUBSET_UNION; SPAN_MONO]];
    REWRITE_TAC[DIM_SPAN] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(b UNION c:real^M->bool)` THEN
    ASM_SIMP_TAC[DIM_LE_CARD; FINITE_UNION; INDEPENDENT_IMP_FINITE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(b:real^M->bool) + CARD(c:real^M->bool)` THEN
    ASM_SIMP_TAC[CARD_UNION_LE] THEN MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM DIM_EQ_CARD; DIM_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `dim(IMAGE (f:real^M->real^N) c)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[DIM_EQ_CARD] THEN
      ASM_MESON_TAC[CARD_IMAGE_INJ; LE_REFL];
      ASM_SIMP_TAC[GSYM DIM_EQ_CARD; DIM_SUBSET]]]);;

let DIM_ORTHOGONAL_SUM = prove
 (`!s t:real^N->bool.
        (!x y. x IN s /\ y IN t ==> x dot y = &0)
        ==> dim(s UNION t) = dim(s) + dim(t)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  REWRITE_TAC[SPAN_UNION] THEN
  SIMP_TAC[GSYM DIM_SUMS_INTER; SUBSPACE_SPAN] THEN
  REWRITE_TAC[ARITH_RULE `x = x + y <=> y = 0`] THEN
  REWRITE_TAC[DIM_EQ_0; SUBSET; IN_INTER] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN span s ==> !y:real^N. y IN span t ==> x dot y = &0`
  MP_TAC THENL
   [MATCH_MP_TAC SPAN_INDUCT THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC SPAN_INDUCT THEN ASM_SIMP_TAC[IN_ELIM_THM] THEN
      SIMP_TAC[subspace; IN_ELIM_THM; DOT_RMUL; DOT_RADD; DOT_RZERO] THEN
      REAL_ARITH_TAC;
      SIMP_TAC[subspace; IN_ELIM_THM; DOT_LMUL; DOT_LADD; DOT_LZERO] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[IN_SING] THEN MESON_TAC[DOT_EQ_0]]);;

let DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS = prove
 (`!s t:real^N->bool.
        subspace s /\ subspace t /\ s SUBSET t
        ==> dim {y | y IN t /\ !x. x IN s ==> orthogonal x y} + dim s = dim t`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) DIM_ORTHOGONAL_SUM o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[IN_ELIM_THM; orthogonal] THEN MESON_TAC[DOT_SYM];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_MONO THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN REWRITE_TAC[SUBSPACE_SPAN] THEN
  REWRITE_TAC[SPAN_UNION; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
        ORTHOGONAL_SUBSPACE_DECOMP_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_SYM] THEN
  MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP (VECTOR_ARITH
     `x:real^N = y + z ==> z = x - y`)) THEN
    MATCH_MP_TAC SUBSPACE_SUB THEN
    ASM_MESON_TAC[SUBSET; SPAN_EQ_SELF];
    ASM_MESON_TAC[SPAN_SUPERSET; ORTHOGONAL_SYM]]);;

let DIM_SPECIAL_SUBSPACE = prove
 (`!k. dim {x:real^N |
            !i. 1 <= i /\ i <= dimindex(:N) /\ i IN k ==> x$i = &0} =
       CARD((1..dimindex(:N)) DIFF k)`,
  GEN_TAC THEN MATCH_MP_TAC DIM_UNIQUE THEN
  EXISTS_TAC `IMAGE (basis:num->real^N) ((1..dimindex(:N)) DIFF k)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    SIMP_TAC[BASIS_COMPONENT; IN_DIFF; IN_NUMSEG] THEN MESON_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    MATCH_MP_TAC SPAN_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:real^N)$j = &0` THEN
    ASM_REWRITE_TAC[SPAN_0; VECTOR_MUL_LZERO] THEN
    MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `j:num` THEN
    REWRITE_TAC[IN_NUMSEG; IN_DIFF] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
    REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM;
      SET_RULE `~(a IN IMAGE f s) <=> (!x. x IN s ==> ~(f x = a))`] THEN
    SIMP_TAC[FORALL_IN_IMAGE; ORTHOGONAL_BASIS_BASIS; BASIS_INJ_EQ;
             IN_DIFF; IN_NUMSEG; BASIS_NONZERO];
    SIMP_TAC[HAS_SIZE; FINITE_IMAGE; FINITE_DIFF; FINITE_NUMSEG] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    SIMP_TAC[FINITE_DIFF; FINITE_NUMSEG; IMP_CONJ; RIGHT_FORALL_IMP_THM;
      SET_RULE `~(a IN IMAGE f s) <=> (!x. x IN s ==> ~(f x = a))`] THEN
    SIMP_TAC[FORALL_IN_IMAGE; ORTHOGONAL_BASIS_BASIS; BASIS_INJ_EQ;
             IN_DIFF; IN_NUMSEG; BASIS_NONZERO]]);;

(* ------------------------------------------------------------------------- *)
(* More injective/surjective versus dimension variants.                      *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INJECTIVE_IFF_DIM = prove
 (`!f:real^M->real^N.
        linear f
        ==> ((!x y. f x = f y ==> x = y) <=>
             dim(IMAGE f (:real^M)) = dimindex(:M))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` DIM_IMAGE_KERNEL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP (ARITH_RULE
    `x + y:num = m ==> (x = m <=> y = 0)`)) THEN
  REWRITE_TAC[DIM_EQ_0; SUBSET; IN_ELIM_THM; IN_SING] THEN
  ASM_MESON_TAC[LINEAR_INJECTIVE_0]);;

let LINEAR_SURJECTIVE_IFF_DIM = prove
 (`!f:real^M->real^N.
        linear f
        ==> ((!y. ?x. f x = y) <=>
             dim(IMAGE f (:real^M)) = dimindex(:N))`,
  SIMP_TAC[DIM_EQ_FULL; SPAN_LINEAR_IMAGE; SPAN_UNIV] THEN SET_TAC[]);;

let LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN = prove
 (`!f:real^M->real^N.
      dimindex(:M) = dimindex(:N) /\ linear f
      ==> ((!y. ?x. f x = y) <=> (!x y. f x = f y ==> x = y))`,
  SIMP_TAC[LINEAR_INJECTIVE_IFF_DIM; LINEAR_SURJECTIVE_IFF_DIM] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More about product spaces.                                                *)
(* ------------------------------------------------------------------------- *)

let PASTECART_AS_ORTHOGONAL_SUM = prove
 (`!x:real^M y:real^N.
        pastecart x y = pastecart x (vec 0) + pastecart (vec 0) y`,
  REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID]);;

let PCROSS_AS_ORTHOGONAL_SUM = prove
 (`!s:real^M->bool t:real^N->bool.
        s PCROSS t =
        {u + v | u IN IMAGE (\x. pastecart x (vec 0)) s /\
                 v IN IMAGE (\y. pastecart (vec 0) y) t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [PASTECART_AS_ORTHOGONAL_SUM] THEN
  SET_TAC[]);;

let DIM_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t ==> dim(s PCROSS t) = dim s + dim t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PCROSS_AS_ORTHOGONAL_SUM] THEN
  W(MP_TAC o PART_MATCH (lhand o lhand o rand) DIM_SUMS_INTER o
        lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSPACE_LINEAR_IMAGE;
    MATCH_MP_TAC(ARITH_RULE `c = d /\ b = 0 ==> a + b = c ==> a = d`) THEN
    CONJ_TAC THENL
     [BINOP_TAC THEN MATCH_MP_TAC DIM_INJECTIVE_LINEAR_IMAGE THEN
      SIMP_TAC[PASTECART_INJ];
      REWRITE_TAC[DIM_EQ_0; SUBSET; IN_INTER; IN_IMAGE; IN_SING] THEN
      REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MESON_TAC[FSTCART_VEC; SNDCART_VEC]]] THEN
  ASM_REWRITE_TAC[linear; GSYM PASTECART_VEC] THEN
  REWRITE_TAC[PASTECART_ADD; GSYM PASTECART_CMUL; PASTECART_INJ] THEN
  VECTOR_ARITH_TAC);;

let SPAN_PCROSS_SUBSET = prove
 (`!s:real^M->bool t:real^N->bool.
        span(s PCROSS t) SUBSET (span s) PCROSS (span t)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
  SIMP_TAC[SUBSPACE_PCROSS; SUBSPACE_SPAN; PCROSS_MONO; SPAN_INC]);;

let SPAN_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ (vec 0 IN s \/ vec 0 IN t)
        ==> span(s PCROSS t) = (span s) PCROSS (span t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SPAN_PCROSS_SUBSET] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_PCROSS] THEN
  ONCE_REWRITE_TAC[PASTECART_AS_ORTHOGONAL_SUM] THEN
  SUBGOAL_THEN
   `(!x:real^M. x IN span s ==> pastecart x (vec 0) IN span(s PCROSS t)) /\
    (!y:real^N. y IN span t ==> pastecart (vec 0) y IN span(s PCROSS t))`
   (fun th -> ASM_MESON_TAC[th; SPAN_ADD]) THEN
  CONJ_TAC THEN MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC[IN_ELIM_THM] THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM] THEN
     ASM_SIMP_TAC[SPAN_SUPERSET; PASTECART_IN_PCROSS];
     REWRITE_TAC[subspace; IN_ELIM_THM; PASTECART_VEC; SPAN_0] THEN
     CONJ_TAC THEN REPEAT GEN_TAC THENL
      [DISCH_THEN(MP_TAC o MATCH_MP SPAN_ADD) THEN
       REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID];
       DISCH_THEN(MP_TAC o MATCH_MP SPAN_MUL) THEN
       SIMP_TAC[GSYM PASTECART_CMUL; VECTOR_MUL_RZERO]]])
  THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    SUBGOAL_THEN
     `pastecart x (vec 0) =
      pastecart (x:real^M) (y:real^N) - pastecart (vec 0) y`
    SUBST1_TAC THENL
     [REWRITE_TAC[PASTECART_SUB; PASTECART_INJ] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC SPAN_SUB THEN
      ASM_SIMP_TAC[SPAN_SUPERSET; PASTECART_IN_PCROSS]];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `~(s:real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^M`) THEN
    SUBGOAL_THEN
     `pastecart (vec 0) y =
      pastecart (x:real^M) (y:real^N) - pastecart x (vec 0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[PASTECART_SUB; PASTECART_INJ] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC SPAN_SUB THEN
      ASM_SIMP_TAC[SPAN_SUPERSET; PASTECART_IN_PCROSS]]]);;

let DIM_PCROSS_STRONG = prove
 (`!s:real^M->bool t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ (vec 0 IN s \/ vec 0 IN t)
        ==> dim(s PCROSS t) = dim s + dim t`,
  ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  SIMP_TAC[SPAN_PCROSS; DIM_PCROSS; SUBSPACE_SPAN]);;

let SPAN_SUMS = prove
 (`!s t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ vec 0 IN (s UNION t)
        ==> span {x + y | x IN s /\ y IN t} =
            {x + y | x IN span s /\ y IN span t}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SPAN_UNION] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THEN MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
  REWRITE_TAC[SUBSPACE_SPAN; SUBSET; FORALL_IN_GSPEC] THEN
  SIMP_TAC[SPAN_ADD; IN_UNION; SPAN_SUPERSET] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o GEN_REWRITE_RULE I [IN_UNION]) THENL
   [UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    SUBST1_TAC(VECTOR_ARITH `x:real^N = (x + y) - (vec 0 + y)`) THEN
    MATCH_MP_TAC SPAN_SUB THEN CONJ_TAC THEN MATCH_MP_TAC SPAN_SUPERSET THEN
    ASM SET_TAC[];
    MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[VECTOR_ADD_RID];
    MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[VECTOR_ADD_LID];
    UNDISCH_TAC `~(s:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    SUBST1_TAC(VECTOR_ARITH `x:real^N = (y + x) - (y + vec 0)`) THEN
    MATCH_MP_TAC SPAN_SUB THEN CONJ_TAC THEN MATCH_MP_TAC SPAN_SUPERSET THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* More about rank from the rank/nullspace formula.                          *)
(* ------------------------------------------------------------------------- *)

let RANK_NULLSPACE = prove
 (`!A:real^M^N. rank A + dim {x | A ** x = vec 0} = dimindex(:M)`,
  GEN_TAC THEN REWRITE_TAC[RANK_DIM_IM] THEN
  MATCH_MP_TAC DIM_IMAGE_KERNEL THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let RANK_SYLVESTER = prove
 (`!A:real^N^M B:real^P^N.
        rank(A) + rank(B) <= rank(A ** B) + dimindex(:N)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(ARITH_RULE
    `!ia ib iab p:num.
        ra + ia = n /\
        rb + ib = p /\
        rab + iab = p /\
        iab <= ia + ib
        ==> ra + rb <= rab + n`) THEN
  MAP_EVERY EXISTS_TAC
   [`dim {x | (A:real^N^M) ** x = vec 0}`;
    `dim {x | (B:real^P^N) ** x = vec 0}`;
    `dim {x | ((A:real^N^M) ** (B:real^P^N)) ** x = vec 0}`;
    `dimindex(:P)`] THEN
  REWRITE_TAC[RANK_NULLSPACE] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] DIM_KERNEL_COMPOSE) THEN
  CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let RANK_GRAM = prove
 (`!A:real^M^N. rank(transp A ** A) = rank A`,
  GEN_TAC THEN MATCH_MP_TAC(ARITH_RULE
   `!n n' k. r + n:num = k /\ r' + n' = k /\ n = n' ==> r = r'`) THEN
  MAP_EVERY EXISTS_TAC
   [`dim {x | (transp A ** (A:real^M^N)) ** x = vec 0}`;
    `dim {x | (A:real^M^N) ** x = vec 0}`;
    `dimindex(:M)`] THEN
  REWRITE_TAC[RANK_NULLSPACE] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; GSYM MATRIX_VECTOR_MUL_ASSOC;
           MATRIX_VECTOR_MUL_RZERO] THEN
  X_GEN_TAC `x:real^M` THEN
  DISCH_THEN(MP_TAC o AP_TERM `(dot) (x:real^M)`) THEN
  ONCE_REWRITE_TAC[GSYM DOT_LMUL_MATRIX] THEN
  REWRITE_TAC[VECTOR_MATRIX_MUL_TRANSP; TRANSP_TRANSP; DOT_RZERO] THEN
  REWRITE_TAC[DOT_EQ_0]);;

let RANK_TRIANGLE = prove
 (`!A B:real^M^N. rank(A + B) <= rank(A) + rank(B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RANK_DIM_IM] THEN
  MP_TAC(ISPECL [`IMAGE (\x. (A:real^M^N) ** x) (:real^M)`;
                 `IMAGE (\x. (B:real^M^N) ** x) (:real^M)`]
                DIM_SUMS_INTER) THEN
  ASM_SIMP_TAC[SUBSPACE_LINEAR_IMAGE; SUBSPACE_UNIV;
               MATRIX_VECTOR_MUL_LINEAR] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(ARITH_RULE `x:num <= y ==> x <= y + z`) THEN
  MATCH_MP_TAC DIM_SUBSET THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV;
              MATRIX_VECTOR_MUL_ADD_RDISTRIB] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Infinity norm.                                                            *)
(* ------------------------------------------------------------------------- *)

let infnorm = define
 `infnorm (x:real^N) = sup { abs(x$i) | 1 <= i /\ i <= dimindex(:N) }`;;

let NUMSEG_DIMINDEX_NONEMPTY = prove
 (`?i. i IN 1..dimindex(:N)`,
  REWRITE_TAC[MEMBER_NOT_EMPTY; NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1]);;

let INFNORM_SET_IMAGE = prove
 (`{abs(x$i) | 1 <= i /\ i <= dimindex(:N)} =
   IMAGE (\i. abs(x$i)) (1..dimindex(:N))`,
  REWRITE_TAC[numseg] THEN SET_TAC[]);;

let INFNORM_SET_LEMMA = prove
 (`FINITE {abs((x:real^N)$i) | 1 <= i /\ i <= dimindex(:N)} /\
   ~({abs(x$i) | 1 <= i /\ i <= dimindex(:N)} = {})`,
  SIMP_TAC[INFNORM_SET_IMAGE; FINITE_NUMSEG; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1]);;

let INFNORM_POS_LE = prove
 (`!x. &0 <= infnorm x`,
  REWRITE_TAC[infnorm] THEN
  SIMP_TAC[REAL_LE_SUP_FINITE; INFNORM_SET_LEMMA] THEN
  REWRITE_TAC[INFNORM_SET_IMAGE; NUMSEG_DIMINDEX_NONEMPTY;
              EXISTS_IN_IMAGE; REAL_ABS_POS]);;

let INFNORM_TRIANGLE = prove
 (`!x y. infnorm(x + y) <= infnorm x + infnorm y`,
  REWRITE_TAC[infnorm] THEN
  SIMP_TAC[REAL_SUP_LE_FINITE; INFNORM_SET_LEMMA] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_SUB_RADD] THEN
  SIMP_TAC[REAL_LE_SUP_FINITE; INFNORM_SET_LEMMA] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x - y <= z <=> x - z <= y`] THEN
  SIMP_TAC[REAL_LE_SUP_FINITE; INFNORM_SET_LEMMA] THEN
  REWRITE_TAC[INFNORM_SET_IMAGE; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; GSYM IN_NUMSEG] THEN
  MESON_TAC[NUMSEG_DIMINDEX_NONEMPTY;
            REAL_ARITH `abs(x + y) - abs(x) <= abs(y)`]);;

let INFNORM_EQ_0 = prove
 (`!x. infnorm x = &0 <=> x = vec 0`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; INFNORM_POS_LE] THEN
  SIMP_TAC[infnorm; REAL_SUP_LE_FINITE; INFNORM_SET_LEMMA] THEN
  SIMP_TAC[FORALL_IN_IMAGE; INFNORM_SET_IMAGE; CART_EQ; VEC_COMPONENT] THEN
  REWRITE_TAC[IN_NUMSEG; REAL_ARITH `abs(x) <= &0 <=> x = &0`]);;

let INFNORM_0 = prove
 (`infnorm(vec 0) = &0`,
  REWRITE_TAC[INFNORM_EQ_0]);;

let INFNORM_NEG = prove
 (`!x. infnorm(--x) = infnorm x`,
  GEN_TAC THEN REWRITE_TAC[infnorm] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[REAL_ABS_NEG; VECTOR_NEG_COMPONENT]);;

let INFNORM_SUB = prove
 (`!x y. infnorm(x - y) = infnorm(y - x)`,
  MESON_TAC[INFNORM_NEG; VECTOR_NEG_SUB]);;

let REAL_ABS_SUB_INFNORM = prove
 (`abs(infnorm x - infnorm y) <= infnorm(x - y)`,
  MATCH_MP_TAC(REAL_ARITH
    `nx <= n + ny /\ ny <= n + nx ==> abs(nx - ny) <= n`) THEN
  MESON_TAC[INFNORM_SUB; VECTOR_SUB_ADD2; INFNORM_TRIANGLE; VECTOR_ADD_SYM]);;

let REAL_ABS_INFNORM = prove
 (`!x. abs(infnorm x) = infnorm x`,
  REWRITE_TAC[real_abs; INFNORM_POS_LE]);;

let COMPONENT_LE_INFNORM = prove
 (`!x:real^N i. 1 <= i /\ i <= dimindex (:N) ==> abs(x$i) <= infnorm x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[infnorm] THEN
  MP_TAC(SPEC `{ abs((x:real^N)$i) | 1 <= i /\ i <= dimindex(:N) }`
              SUP_FINITE) THEN
  REWRITE_TAC[INFNORM_SET_LEMMA] THEN
  SIMP_TAC[INFNORM_SET_IMAGE; FORALL_IN_IMAGE; IN_NUMSEG]);;

let INFNORM_MUL_LEMMA = prove
 (`!a x. infnorm(a % x) <= abs a * infnorm x`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [infnorm] THEN
  SIMP_TAC[REAL_SUP_LE_FINITE; INFNORM_SET_LEMMA] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; INFNORM_SET_IMAGE] THEN
  SIMP_TAC[REAL_ABS_MUL; VECTOR_MUL_COMPONENT; IN_NUMSEG] THEN
  SIMP_TAC[COMPONENT_LE_INFNORM; REAL_LE_LMUL; REAL_ABS_POS]);;

let INFNORM_MUL = prove
 (`!a x:real^N. infnorm(a % x) = abs a * infnorm x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = &0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INFNORM_0; REAL_ABS_0; REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; INFNORM_MUL_LEMMA] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) [GSYM VECTOR_MUL_LID] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP REAL_MUL_LINV) THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(a) * abs(inv a) * infnorm(a % x:real^N)` THEN
  ASM_SIMP_TAC[INFNORM_MUL_LEMMA; REAL_LE_LMUL; REAL_ABS_POS] THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; GSYM REAL_ABS_MUL; REAL_MUL_RINV] THEN
  REAL_ARITH_TAC);;

let INFNORM_POS_LT = prove
 (`!x. &0 < infnorm x <=> ~(x = vec 0)`,
  MESON_TAC[REAL_LT_LE; INFNORM_POS_LE; INFNORM_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Prove that it differs only up to a bound from Euclidean norm.             *)
(* ------------------------------------------------------------------------- *)

let INFNORM_LE_NORM = prove
 (`!x. infnorm(x) <= norm(x)`,
  SIMP_TAC[infnorm; REAL_SUP_LE_FINITE; INFNORM_SET_LEMMA] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[COMPONENT_LE_NORM]);;

let NORM_LE_INFNORM = prove
 (`!x:real^N. norm(x) <= sqrt(&(dimindex(:N))) * infnorm(x)`,
  GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o funpow 2 RAND_CONV)
   [GSYM CARD_NUMSEG_1] THEN
  REWRITE_TAC[vector_norm] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
  SIMP_TAC[DOT_POS_LE; SQRT_POS_LE; REAL_POS; REAL_LE_MUL; INFNORM_POS_LE;
           SQRT_POW_2; REAL_POW_MUL] THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_BOUND THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs(y)`) THEN
  SIMP_TAC[infnorm; REAL_LE_SUP_FINITE; INFNORM_SET_LEMMA] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Equality in Cauchy-Schwarz and triangle inequalities.                     *)
(* ------------------------------------------------------------------------- *)

let NORM_CAUCHY_SCHWARZ_EQ = prove
 (`!x:real^N y. x dot y = norm(x) * norm(y) <=> norm(x) % y = norm(y) % x`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`x:real^N = vec 0`; `y:real^N = vec 0`] THEN
  ASM_REWRITE_TAC[NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO;
    DOT_LZERO; DOT_RZERO; VECTOR_MUL_LZERO; VECTOR_MUL_RZERO] THEN
  MP_TAC(ISPEC `norm(y:real^N) % x - norm(x:real^N) % y` DOT_EQ_0) THEN
  REWRITE_TAC[DOT_RSUB; DOT_LSUB; DOT_LMUL; DOT_RMUL; GSYM NORM_POW_2;
              REAL_POW_2; VECTOR_SUB_EQ] THEN
  REWRITE_TAC[DOT_SYM; REAL_ARITH
   `y * (y * x * x - x * d) - x * (y * d - x * y * y) =
    &2 * x * y * (x * y - d)`] THEN
  ASM_SIMP_TAC[REAL_ENTIRE; NORM_EQ_0; REAL_SUB_0; REAL_OF_NUM_EQ; ARITH] THEN
  REWRITE_TAC[EQ_SYM_EQ]);;

let NORM_CAUCHY_SCHWARZ_ABS_EQ = prove
 (`!x:real^N y. abs(x dot y) = norm(x) * norm(y) <=>
                norm(x) % y = norm(y) % x \/ norm(x) % y = --norm(y) % x`,
  SIMP_TAC[REAL_ARITH `&0 <= a ==> (abs x = a <=> x = a \/ --x = a)`;
           REAL_LE_MUL; NORM_POS_LE; GSYM DOT_RNEG] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 3 RAND_CONV) [GSYM NORM_NEG] THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_EQ] THEN REWRITE_TAC[NORM_NEG] THEN
  BINOP_TAC THEN VECTOR_ARITH_TAC);;

let NORM_TRIANGLE_EQ = prove
 (`!x y:real^N. norm(x + y) = norm(x) + norm(y) <=> norm(x) % y = norm(y) % x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NORM_CAUCHY_SCHWARZ_EQ] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `norm(x + y:real^N) pow 2 = (norm(x) + norm(y)) pow 2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_RING `x pow 2 = y pow 2 <=> x = y \/ x + y = &0`] THEN
    MAP_EVERY (MP_TAC o C ISPEC NORM_POS_LE)
     [`x + y:real^N`; `x:real^N`; `y:real^N`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; REAL_ARITH
     `(x + y) pow 2 = x pow 2 + y pow 2 + &2 * x * y`] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC]);;

let DIST_TRIANGLE_EQ = prove
 (`!x y z. dist(x,z) = dist(x,y) + dist(y,z) <=>
                norm (x - y) % (y - z) = norm (y - z) % (x - y)`,
  REWRITE_TAC[GSYM NORM_TRIANGLE_EQ] THEN NORM_ARITH_TAC);;

let NORM_CROSS_MULTIPLY = prove
 (`!a b x y:real^N.
        a % x = b % y /\ &0 < a /\ &0 < b
        ==> norm y % x = norm x % y`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; VECTOR_MUL_RZERO] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. inv(a) % x`) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
               NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Collinearity.                                                             *)
(* ------------------------------------------------------------------------- *)

let collinear = new_definition
 `collinear s <=> ?u. !x y. x IN s /\ y IN s ==> ?c. x - y = c % u`;;

let COLLINEAR_SUBSET = prove
 (`!s t. collinear t /\ s SUBSET t ==> collinear s`,
  REWRITE_TAC[collinear] THEN SET_TAC[]);;

let COLLINEAR_EMPTY = prove
 (`collinear {}`,
  REWRITE_TAC[collinear; NOT_IN_EMPTY]);;

let COLLINEAR_SING = prove
 (`!x. collinear {x}`,
  SIMP_TAC[collinear; IN_SING; VECTOR_SUB_REFL] THEN
  MESON_TAC[VECTOR_MUL_LZERO]);;

let COLLINEAR_2 = prove
 (`!x y:real^N. collinear {x,y}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[collinear; IN_INSERT; NOT_IN_EMPTY] THEN
  EXISTS_TAC `x - y:real^N` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `&0`; EXISTS_TAC `&1`; EXISTS_TAC `-- &1`; EXISTS_TAC `&0`] THEN
  VECTOR_ARITH_TAC);;

let COLLINEAR_SMALL = prove
 (`!s. FINITE s /\ CARD s <= 2 ==> collinear s`,
  REWRITE_TAC[ARITH_RULE `s <= 2 <=> s = 0 \/ s = 1 \/ s = 2`] THEN
  REWRITE_TAC[LEFT_OR_DISTRIB; GSYM HAS_SIZE] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[COLLINEAR_EMPTY; COLLINEAR_SING; COLLINEAR_2]);;

let COLLINEAR_3 = prove
 (`!x y z. collinear {x,y,z} <=> collinear {vec 0,x - y,z - y}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[collinear; FORALL_IN_INSERT; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              NOT_IN_EMPTY] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MESON_TAC[VECTOR_ARITH `x - y = (x - y) - vec 0`;
            VECTOR_ARITH `y - x = vec 0 - (x - y)`;
            VECTOR_ARITH `x - z:real^N = (x - y) - (z - y)`]);;

let COLLINEAR_LEMMA = prove
 (`!x y:real^N. collinear {vec 0,x,y} <=>
                   x = vec 0 \/ y = vec 0 \/ ?c. y = c % x`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`x:real^N = vec 0`; `y:real^N = vec 0`] THEN
  TRY(ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_SING; COLLINEAR_2] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[collinear] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N`
     (fun th -> MP_TAC(SPECL [`x:real^N`; `vec 0:real^N`] th) THEN
                MP_TAC(SPECL [`y:real^N`; `vec 0:real^N`] th))) THEN
    REWRITE_TAC[IN_INSERT; VECTOR_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` SUBST_ALL_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` SUBST_ALL_TAC) THEN
    EXISTS_TAC `e / d` THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_MUL_EQ_0; DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL];
    STRIP_TAC THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `&0`; EXISTS_TAC `-- &1`; EXISTS_TAC `--c`;
      EXISTS_TAC `&1`; EXISTS_TAC `&0`; EXISTS_TAC `&1 - c`;
      EXISTS_TAC `c:real`; EXISTS_TAC `c - &1`; EXISTS_TAC `&0`] THEN
    VECTOR_ARITH_TAC]);;

let COLLINEAR_LEMMA_ALT = prove
 (`!x y. collinear {vec 0,x,y} <=> x = vec 0 \/ ?c. y = c % x`,
  REWRITE_TAC[COLLINEAR_LEMMA] THEN MESON_TAC[VECTOR_MUL_LZERO]);;

let NORM_CAUCHY_SCHWARZ_EQUAL = prove
 (`!x y:real^N. abs(x dot y) = norm(x) * norm(y) <=> collinear {vec 0,x,y}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS_EQ] THEN
  MAP_EVERY ASM_CASES_TAC [`x:real^N = vec 0`; `y:real^N = vec 0`] THEN
  TRY(ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_SING; COLLINEAR_2; NORM_0;
                      VECTOR_MUL_LZERO; VECTOR_MUL_RZERO] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[COLLINEAR_LEMMA] THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM
       `(%) (inv(norm(x:real^N))):real^N->real^N`);
      FIRST_X_ASSUM(MP_TAC o AP_TERM
       `(%) (--inv(norm(x:real^N))):real^N->real^N`)] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LNEG] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; VECTOR_MUL_LNEG; VECTOR_MUL_LID;
                 VECTOR_ARITH `--x = --y <=> x:real^N = y`] THEN
    MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC(MESON[]
      `t = a \/ t = b ==> t % x = a % x \/ t % x = b % x`) THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG;
                REAL_ARITH `x * c = d * x <=> x * (c - d) = &0`] THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; NORM_EQ_0] THEN REAL_ARITH_TAC]);;

let DOT_CAUCHY_SCHWARZ_EQUAL = prove
 (`!x y:real^N.
        (x dot y) pow 2 = (x dot x) * (y dot y) <=>
        collinear {vec 0,x,y}`,
  REWRITE_TAC[GSYM NORM_CAUCHY_SCHWARZ_EQUAL] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `&0 <= y /\ (u:real = v <=> x = abs y) ==> (u = v <=> x = y)`) THEN
  SIMP_TAC[NORM_POS_LE; REAL_LE_MUL] THEN
  REWRITE_TAC[REAL_EQ_SQUARE_ABS] THEN REWRITE_TAC[REAL_POW_MUL; NORM_POW_2]);;

let COLLINEAR_3_EXPAND = prove
 (`!a b c:real^N. collinear{a,b,c} <=> a = c \/ ?u. b = u % a + (&1 - u) % c`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {a,c,b}`] THEN
  ONCE_REWRITE_TAC[COLLINEAR_3] THEN
  REWRITE_TAC[COLLINEAR_LEMMA; VECTOR_SUB_EQ] THEN
  ASM_CASES_TAC `a:real^N = c` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `b:real^N = c` THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `u % c + (&1 - u) % c = c`] THENL
   [EXISTS_TAC `&0` THEN VECTOR_ARITH_TAC;
    AP_TERM_TAC THEN ABS_TAC THEN VECTOR_ARITH_TAC]);;

let COLLINEAR_TRIPLES = prove
 (`!s a b:real^N.
        ~(a = b)
        ==> (collinear(a INSERT b INSERT s) <=>
             !x. x IN s ==> collinear{a,b,x})`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] COLLINEAR_SUBSET)) THEN
    ASM SET_TAC[];
    ONCE_REWRITE_TAC[SET_RULE `{a,b,x} = {a,x,b}`] THEN
    ASM_REWRITE_TAC[COLLINEAR_3_EXPAND] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!x:real^N. x IN (a INSERT b INSERT s) ==> ?u. x = u % a + (&1 - u) % b`
    MP_TAC THENL
     [ASM_REWRITE_TAC[FORALL_IN_INSERT] THEN CONJ_TAC THENL
       [EXISTS_TAC `&1` THEN VECTOR_ARITH_TAC;
        EXISTS_TAC `&0` THEN VECTOR_ARITH_TAC];
      POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
      REWRITE_TAC[collinear] THEN EXISTS_TAC `b - a:real^N` THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x:real^N` th) THEN MP_TAC(SPEC
        `y:real^N` th)) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ARITH
       `(u % a + (&1 - u) % b) - (v % a + (&1 - v) % b):real^N =
        (v - u) % (b - a)`] THEN
      MESON_TAC[]]]);;

let COLLINEAR_4_3 = prove
 (`!a b c d:real^N.
        ~(a = b)
        ==> (collinear {a,b,c,d} <=> collinear{a,b,c} /\ collinear{a,b,d})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{c:real^N,d}`; `a:real^N`; `b:real^N`]
    COLLINEAR_TRIPLES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let COLLINEAR_3_TRANS = prove
 (`!a b c d:real^N.
        collinear{a,b,c} /\ collinear{b,c,d} /\ ~(b = c) ==> collinear{a,b,d}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COLLINEAR_SUBSET THEN
  EXISTS_TAC `{b:real^N,c,a,d}` THEN ASM_SIMP_TAC[COLLINEAR_4_3] THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN SIMP_TAC[INSERT_AC]);;

let ORTHOGONAL_TO_ORTHOGONAL_2D = prove
 (`!x y z:real^2.
     ~(x = vec 0) /\ orthogonal x y /\ orthogonal x z
     ==> collinear {vec 0,y,z}`,
  REWRITE_TAC[orthogonal; GSYM DOT_CAUCHY_SCHWARZ_EQUAL; GSYM DOT_EQ_0] THEN
  REWRITE_TAC[DOT_2] THEN CONV_TAC REAL_RING);;

let COLLINEAR_3_2D = prove
 (`!x y z:real^2. collinear{x,y,z} <=>
                  (z$1 - x$1) * (y$2 - x$2) = (y$1 - x$1) * (z$2 - x$2)`,
  ONCE_REWRITE_TAC[COLLINEAR_3] THEN
  REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL] THEN
  REWRITE_TAC[DOT_2; VECTOR_SUB_COMPONENT] THEN CONV_TAC REAL_RING);;

let COLLINEAR_3_DOT_MULTIPLES = prove
 (`!a b c:real^N.
        collinear {a,b,c} <=>
        ((b - a) dot (b - a)) % (c - a) = ((c - a) dot (b - a)) % (b - a)`,
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC; DOT_RZERO; VECTOR_MUL_LZERO;
                    VECTOR_SUB_REFL];
    ONCE_REWRITE_TAC[COLLINEAR_3] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL; GSYM DOT_EQ_0] THEN
    REWRITE_TAC[GSYM DOT_EQ_0; DOT_RSUB; DOT_LSUB; DOT_RMUL; DOT_LMUL] THEN
    REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_RING]);;

(* ------------------------------------------------------------------------- *)
(* Between-ness.                                                             *)
(* ------------------------------------------------------------------------- *)

let between = new_definition
 `between x (a,b) <=> dist(a,b) = dist(a,x) + dist(x,b)`;;

let BETWEEN_REFL = prove
 (`!a b. between a (a,b) /\ between b (a,b) /\ between a (a,a)`,
  REWRITE_TAC[between] THEN NORM_ARITH_TAC);;

let BETWEEN_REFL_EQ = prove
 (`!a x. between x (a,a) <=> x = a`,
  REWRITE_TAC[between] THEN NORM_ARITH_TAC);;

let BETWEEN_SYM = prove
 (`!a b x. between x (a,b) <=> between x (b,a)`,
  REWRITE_TAC[between] THEN NORM_ARITH_TAC);;

let BETWEEN_ANTISYM = prove
 (`!a b c. between a (b,c) /\ between b (a,c) ==> a = b`,
  REWRITE_TAC[between; DIST_SYM] THEN NORM_ARITH_TAC);;

let BETWEEN_TRANS = prove
 (`!a b c d. between a (b,c) /\ between d (a,c) ==> between d (b,c)`,
  REWRITE_TAC[between; DIST_SYM] THEN NORM_ARITH_TAC);;

let BETWEEN_TRANS_2 = prove
 (`!a b c d. between a (b,c) /\ between d (a,b) ==> between a (c,d)`,
  REWRITE_TAC[between; DIST_SYM] THEN NORM_ARITH_TAC);;

let BETWEEN_NORM = prove
 (`!a b x:real^N.
     between x (a,b) <=> norm(x - a) % (b - x) = norm(b - x) % (x - a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[between; DIST_TRIANGLE_EQ] THEN
  REWRITE_TAC[NORM_SUB] THEN VECTOR_ARITH_TAC);;

let BETWEEN_DOT = prove
 (`!a b x:real^N.
     between x (a,b) <=> (x - a) dot (b - x) = norm(x - a) * norm(b - x)`,
  REWRITE_TAC[BETWEEN_NORM; NORM_CAUCHY_SCHWARZ_EQ]);;

let BETWEEN_EXISTS_EXTENSION = prove
 (`!a b x:real^N.
        between b (a,x) /\ ~(b = a) ==> ?d. &0 <= d /\ x = b + d % (b - a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BETWEEN_NORM] THEN STRIP_TAC THEN
  EXISTS_TAC `norm(x - b:real^N) / norm(b - a)` THEN
  SIMP_TAC[REAL_LE_DIV; NORM_POS_LE] THEN FIRST_X_ASSUM
   (MP_TAC o AP_TERM `(%) (inv(norm(b - a:real^N))):real^N->real^N`) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; NORM_EQ_0; VECTOR_SUB_EQ] THEN
  VECTOR_ARITH_TAC);;

let BETWEEN_IMP_COLLINEAR = prove
 (`!a b x:real^N. between x (a,b) ==> collinear {a,x,b}`,
  REPEAT GEN_TAC THEN MAP_EVERY
   (fun t -> ASM_CASES_TAC t THEN
             TRY(ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2] THEN NO_TAC))
   [`x:real^N = a`; `x:real^N = b`; `a:real^N = b`] THEN
  ONCE_REWRITE_TAC[COLLINEAR_3; BETWEEN_NORM] THEN
  DISCH_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA] THEN
  REPEAT DISJ2_TAC THEN EXISTS_TAC `--(norm(b - x:real^N) / norm(x - a))` THEN
  MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC `norm(x - a:real^N)` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RNEG] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
  VECTOR_ARITH_TAC);;

let COLLINEAR_BETWEEN_CASES = prove
 (`!a b c:real^N.
        collinear {a,b,c} <=>
        between a (b,c) \/ between b (c,a) \/ between c (a,b)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[COLLINEAR_3_EXPAND] THEN
    ASM_CASES_TAC `c:real^N = a` THEN ASM_REWRITE_TAC[BETWEEN_REFL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[between; dist] THEN
    REWRITE_TAC[VECTOR_ARITH `(u % a + (&1 - u) % c) - c = --u % (c - a)`;
      VECTOR_ARITH `(u % a + (&1 - u) % c) - a = (&1 - u) % (c - a)`;
      VECTOR_ARITH `c - (u % a + (&1 - u) % c) = u % (c - a)`;
      VECTOR_ARITH `a - (u % a + (&1 - u) % c) = (u - &1) % (c - a)`] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBST1_TAC(NORM_ARITH `norm(a - c:real^N) = norm(c - a)`) THEN
    REWRITE_TAC[REAL_ARITH `a * c + c = (a + &1) * c`; GSYM REAL_ADD_RDISTRIB;
                REAL_ARITH `c + a * c = (a + &1) * c`] THEN
    ASM_REWRITE_TAC[REAL_EQ_MUL_RCANCEL;
                    REAL_RING `n = x * n <=> n = &0 \/ x = &1`] THEN
    ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN REAL_ARITH_TAC;
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (MP_TAC o MATCH_MP
      BETWEEN_IMP_COLLINEAR)) THEN
    REWRITE_TAC[INSERT_AC]]);;

let COLLINEAR_DIST_BETWEEN = prove
 (`!a b x. collinear {x,a,b} /\
           dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b)
           ==> between x (a,b)`,
  SIMP_TAC[COLLINEAR_BETWEEN_CASES; between; DIST_SYM] THEN NORM_ARITH_TAC);;

let BETWEEN_COLLINEAR_DIST_EQ = prove
 (`!a b x:real^N.
        between x (a,b) <=>
        collinear {a, x, b} /\
        dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[BETWEEN_IMP_COLLINEAR] THEN REWRITE_TAC[between] THEN
    NORM_ARITH_TAC;
    MESON_TAC[COLLINEAR_DIST_BETWEEN; INSERT_AC]]);;

let COLLINEAR_1 = prove
 (`!s:real^1->bool. collinear s`,
  GEN_TAC THEN MATCH_MP_TAC COLLINEAR_SUBSET THEN
  EXISTS_TAC `(vec 0:real^1) INSERT (vec 1) INSERT s` THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) COLLINEAR_TRIPLES o snd) THEN
  REWRITE_TAC[VEC_EQ; ARITH_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COLLINEAR_BETWEEN_CASES] THEN
  REWRITE_TAC[between; DIST_REAL; GSYM drop; DROP_VEC; REAL_ABS_NUM] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Midpoint between two points.                                              *)
(* ------------------------------------------------------------------------- *)

let midpoint = new_definition
 `midpoint(a,b) = inv(&2) % (a + b)`;;

let MIDPOINT_REFL = prove
 (`!x. midpoint(x,x) = x`,
  REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC);;

let MIDPOINT_SYM = prove
 (`!a b. midpoint(a,b) = midpoint(b,a)`,
  REWRITE_TAC[midpoint; VECTOR_ADD_SYM]);;

let DIST_MIDPOINT = prove
 (`!a b. dist(a,midpoint(a,b)) = dist(a,b) / &2 /\
         dist(b,midpoint(a,b)) = dist(a,b) / &2 /\
         dist(midpoint(a,b),a) = dist(a,b) / &2 /\
         dist(midpoint(a,b),b) = dist(a,b) / &2`,
  REWRITE_TAC[midpoint] THEN NORM_ARITH_TAC);;

let MIDPOINT_EQ_ENDPOINT = prove
 (`!a b. (midpoint(a,b) = a <=> a = b) /\
         (midpoint(a,b) = b <=> a = b) /\
         (a = midpoint(a,b) <=> a = b) /\
         (b = midpoint(a,b) <=> a = b)`,
  REWRITE_TAC[midpoint] THEN NORM_ARITH_TAC);;

let BETWEEN_MIDPOINT = prove
 (`!a b. between (midpoint(a,b)) (a,b) /\ between (midpoint(a,b)) (b,a)`,
  REWRITE_TAC[between; midpoint] THEN NORM_ARITH_TAC);;

let MIDPOINT_LINEAR_IMAGE = prove
 (`!f a b. linear f ==> midpoint(f a,f b) = f(midpoint(a,b))`,
  SIMP_TAC[midpoint; LINEAR_ADD; LINEAR_CMUL]);;

let COLLINEAR_MIDPOINT = prove
 (`!a b. collinear{a,midpoint(a,b),b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_3_EXPAND; midpoint] THEN
  DISJ2_TAC THEN EXISTS_TAC `&1 / &2` THEN VECTOR_ARITH_TAC);;

let MIDPOINT_COLLINEAR = prove
 (`!a b c:real^N.
        ~(a = c)
        ==> (b = midpoint(a,c) <=> collinear{a,b,c} /\ dist(a,b) = dist(b,c))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (b ==> (a <=> c)) ==> (a <=> b /\ c)`) THEN
  SIMP_TAC[COLLINEAR_MIDPOINT] THEN ASM_REWRITE_TAC[COLLINEAR_3_EXPAND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[midpoint; dist] THEN
  REWRITE_TAC
   [VECTOR_ARITH `a - (u % a + (&1 - u) % c) = (&1 - u) % (a - c)`;
    VECTOR_ARITH `(u % a + (&1 - u) % c) - c = u % (a - c)`;
    VECTOR_ARITH `u % a + (&1 - u) % c = inv (&2) % (a + c) <=>
                  (u - &1 / &2) % (a - c) = vec 0`] THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_EQ_MUL_RCANCEL; NORM_EQ_0; VECTOR_SUB_EQ;
               VECTOR_MUL_EQ_0] THEN
  REAL_ARITH_TAC);;

let MIDPOINT_BETWEEN = prove
 (`!a b c:real^N.
        b = midpoint (a,c) <=> between b (a,c) /\ dist (a,b) = dist (b,c)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = c` THENL
   [ASM_SIMP_TAC[BETWEEN_REFL_EQ; MIDPOINT_REFL; DIST_SYM]; ALL_TAC] THEN
  EQ_TAC THEN SIMP_TAC[BETWEEN_MIDPOINT; DIST_MIDPOINT] THEN
  ASM_MESON_TAC[MIDPOINT_COLLINEAR; BETWEEN_IMP_COLLINEAR]);;

(* ------------------------------------------------------------------------- *)
(* General "one way" lemma for properties preserved by injective map.        *)
(* ------------------------------------------------------------------------- *)

let WLOG_LINEAR_INJECTIVE_IMAGE_2 = prove
 (`!P Q. (!f s. P s /\ linear f ==> Q(IMAGE f s)) /\
         (!g t. Q t /\ linear g ==> P(IMAGE g t))
         ==> !f:real^M->real^N.
                linear f /\ (!x y. f x = f y ==> x = y)
                ==> !s. Q(IMAGE f s) <=> P s`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`g:real^N->real^M`; `IMAGE (f:real^M->real^N) s`]) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID]);;

let WLOG_LINEAR_INJECTIVE_IMAGE_2_ALT = prove
 (`!P Q f s. (!h u. P u /\ linear h ==> Q(IMAGE h u)) /\
             (!g t. Q t /\ linear g ==> P(IMAGE g t)) /\
             linear f /\ (!x y. f x = f y ==> x = y)
             ==> (Q(IMAGE f s) <=> P s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
     WLOG_LINEAR_INJECTIVE_IMAGE_2) THEN
  ASM_REWRITE_TAC[]);;

let WLOG_LINEAR_INJECTIVE_IMAGE = prove
 (`!P. (!f s. P s /\ linear f ==> P(IMAGE f s))
       ==> !f:real^N->real^N. linear f /\ (!x y. f x = f y ==> x = y)
                              ==> !s. P(IMAGE f s) <=> P s`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC WLOG_LINEAR_INJECTIVE_IMAGE_2 THEN
  ASM_REWRITE_TAC[]);;

let WLOG_LINEAR_INJECTIVE_IMAGE_ALT = prove
 (`!P f s. (!g t. P t /\ linear g ==> P(IMAGE g t)) /\
           linear f /\ (!x y. f x = f y ==> x = y)
           ==> (P(IMAGE f s) <=> P s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
     WLOG_LINEAR_INJECTIVE_IMAGE) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Inference rule to apply it conveniently.                                  *)
(*                                                                           *)
(*   |- !f s. P s /\ linear f ==> P(IMAGE f s)  [or /\ commuted]             *)
(* ---------------------------------------------------------------           *)
(*   |- !f s. linear f /\ (!x y. f x = f y ==> x = y)                        *)
(*            ==> (Q(IMAGE f s) <=> P s)                                     *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INVARIANT_RULE th =
  let [f;s] = fst(strip_forall(concl th)) in
  let (rm,rn) = dest_fun_ty (type_of f) in
  let m = last(snd(dest_type rm)) and n = last(snd(dest_type rn)) in
  let th' = INST_TYPE [m,n; n,m] th in
  let th0 = CONJ th th' in
  let th1 = try MATCH_MP WLOG_LINEAR_INJECTIVE_IMAGE_2 th0
            with Failure _ ->
                MATCH_MP WLOG_LINEAR_INJECTIVE_IMAGE_2
            (GEN_REWRITE_RULE (BINOP_CONV o ONCE_DEPTH_CONV) [CONJ_SYM] th0) in
  GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_FORALL_THM] th1;;

(* ------------------------------------------------------------------------- *)
(* Immediate application.                                                    *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (subspace (IMAGE f s) <=> subspace s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE SUBSPACE_LINEAR_IMAGE));;

(* ------------------------------------------------------------------------- *)
(* Storage of useful "invariance under linear map / translation" theorems.   *)
(* ------------------------------------------------------------------------- *)

let invariant_under_linear = ref([]:thm list);;

let invariant_under_translation = ref([]:thm list);;

let scaling_theorems = ref([]:thm list);;

(* ------------------------------------------------------------------------- *)
(* Scaling theorems and derivation from linear invariance.                   *)
(* ------------------------------------------------------------------------- *)

let LINEAR_SCALING = prove
 (`!c. linear(\x:real^N. c % x)`,
  REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC);;

let INJECTIVE_SCALING = prove
 (`!c. (!x y:real^N. c % x = c % y ==> x = y) <=> ~(c = &0)`,
  GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
  ASM_CASES_TAC `c:real = &0` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^N`; `vec 1:real^N`]) THEN
  REWRITE_TAC[VEC_EQ; ARITH]);;

let SURJECTIVE_SCALING = prove
 (`!c. (!y:real^N. ?x. c % x = y) <=> ~(c = &0)`,
  ASM_SIMP_TAC[LINEAR_SURJECTIVE_IFF_INJECTIVE; LINEAR_SCALING] THEN
  REWRITE_TAC[INJECTIVE_SCALING]);;

let SCALING_INVARIANT =
  let pths = (CONJUNCTS o UNDISCH o prove)
   (`&0 < c
     ==> linear(\x:real^N. c % x) /\
         (!x y:real^N. c % x = c % y ==> x = y) /\
         (!y:real^N. ?x. c % x = y)`,
    SIMP_TAC[REAL_LT_IMP_NZ; LINEAR_SCALING;
             INJECTIVE_SCALING; SURJECTIVE_SCALING])
  and sc_tm = `\x:real^N. c % x`
  and sa_tm = `&0:real < c`
  and c_tm = `c:real` in
  fun th ->
    let ith = BETA_RULE(ISPEC sc_tm th) in
    let avs,bod = strip_forall(concl ith) in
    let cjs = conjuncts(lhand bod) in
    let cths = map (fun t -> find(fun th -> aconv (concl th) t) pths) cjs in
    let oth = MP (SPECL avs ith) (end_itlist CONJ cths) in
    GEN c_tm (DISCH sa_tm (GENL avs oth));;

let scaling_theorems = ref([]:thm list);;

(* ------------------------------------------------------------------------- *)
(* Augmentation of the lists. The "add_linear_invariants" also updates       *)
(* the scaling theorems automatically, so only a few of those will need      *)
(* to be added explicitly.                                                   *)
(* ------------------------------------------------------------------------- *)

let add_scaling_theorems thl =
  (scaling_theorems := (!scaling_theorems) @ thl);;

let add_linear_invariants thl =
  ignore(mapfilter (fun th -> add_scaling_theorems[SCALING_INVARIANT th]) thl);
  (invariant_under_linear := (!invariant_under_linear) @ thl);;

let add_translation_invariants thl =
 (invariant_under_translation := (!invariant_under_translation) @ thl);;

(* ------------------------------------------------------------------------- *)
(* Start with some basic set equivalences.                                   *)
(* We give them all an injectivity hypothesis even if it's not necessary.    *)
(* For just the intersection theorem we add surjectivity (more manageable    *)
(* than assuming that the set isn't empty).                                  *)
(* ------------------------------------------------------------------------- *)

let th_sets = prove
 (`!f. (!x y. f x = f y ==> x = y)
       ==> (if p then f x else f y) = f(if p then x else y) /\
           (if p then IMAGE f s else IMAGE f t) =
           IMAGE f (if p then s else t) /\
           (f x) INSERT (IMAGE f s) = IMAGE f (x INSERT s) /\
           (IMAGE f s) DELETE (f x) = IMAGE f (s DELETE x) /\
           (IMAGE f s) INTER (IMAGE f t) = IMAGE f (s INTER t) /\
           (IMAGE f s) UNION (IMAGE f t) = IMAGE f (s UNION t) /\
           UNIONS(IMAGE (IMAGE f) u) = IMAGE f (UNIONS u) /\
           (IMAGE f s) DIFF (IMAGE f t) = IMAGE f (s DIFF t) /\
           (IMAGE f s (f x) <=> s x) /\
           ((f x) IN (IMAGE f s) <=> x IN s) /\
           ((f o xs) (n:num) = f(xs n)) /\
           ((f o pt) (tt:real^1) = f(pt tt)) /\
           (DISJOINT (IMAGE f s) (IMAGE f t) <=> DISJOINT s t) /\
           ((IMAGE f s) SUBSET (IMAGE f t) <=> s SUBSET t) /\
           ((IMAGE f s) PSUBSET (IMAGE f t) <=> s PSUBSET t) /\
           (IMAGE f s = IMAGE f t <=> s = t) /\
           ((IMAGE f s) HAS_SIZE n <=> s HAS_SIZE n) /\
           (FINITE(IMAGE f s) <=> FINITE s) /\
           (INFINITE(IMAGE f s) <=> INFINITE s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[IMAGE_UNIONS] THEN
  REWRITE_TAC[o_THM; MESON[IN] `IMAGE f s y <=> y IN IMAGE f s`] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [MESON_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[INFINITE; TAUT `(~p <=> ~q) <=> (p <=> q)`] THEN
  REPLICATE_TAC 11 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[HAS_SIZE] THEN
  ASM_MESON_TAC[FINITE_IMAGE_INJ_EQ; CARD_IMAGE_INJ]) in
let f = `f:real^M->real^N`
and imf = `IMAGE (f:real^M->real^N)`
and a = `a:real^N`
and ima = `IMAGE (\x:real^N. a + x)`
and vth = VECTOR_ARITH `!x y. a + x:real^N = a + y ==> x = y` in
let th1 = UNDISCH(ISPEC f th_sets)
and th1' = UNDISCH
 (GEN_REWRITE_RULE LAND_CONV [INJECTIVE_IMAGE] (ISPEC imf th_sets))
and th2 = MATCH_MP th_sets vth
and th2' = MATCH_MP
  (BETA_RULE(GEN_REWRITE_RULE LAND_CONV [INJECTIVE_IMAGE] (ISPEC ima th_sets)))
  vth in
let fn a th = GENL (a::subtract (frees(concl th)) [a]) th in
add_linear_invariants(map (fn f o DISCH_ALL) (CONJUNCTS th1 @ CONJUNCTS th1')),
add_translation_invariants(map (fn a) (CONJUNCTS th2 @ CONJUNCTS th2'));;

let th_set = prove
 (`!f:A->B s. (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
              ==> INTERS (IMAGE (IMAGE f) s) = IMAGE f (INTERS s)`,
  REWRITE_TAC[INTERS_IMAGE] THEN SET_TAC[]) in
let th_vec = prove
 (`!a:real^N s.
    INTERS (IMAGE (IMAGE (\x. a + x)) s) = IMAGE (\x. a + x) (INTERS s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC th_set THEN
  REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  REWRITE_TAC[VECTOR_ARITH `a + x:real^N = y <=> x = y - a`; EXISTS_REFL]) in
add_linear_invariants [th_set],add_translation_invariants[th_vec];;

(* ------------------------------------------------------------------------- *)
(* Now add arithmetical equivalences.                                        *)
(* ------------------------------------------------------------------------- *)

let PRESERVES_NORM_PRESERVES_DOT = prove
 (`!f:real^M->real^N x y.
     linear f /\ (!x. norm(f x) = norm x)
     ==> (f x) dot (f y) = x dot y`,
  REWRITE_TAC[NORM_EQ] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x + y:real^M`) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th]) THEN
  ASM_REWRITE_TAC[DOT_LADD; DOT_RADD] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

let PRESERVES_NORM_INJECTIVE = prove
 (`!f:real^M->real^N.
     linear f /\ (!x. norm(f x) = norm x)
     ==> !x y. f x = f y ==> x = y`,
  SIMP_TAC[LINEAR_INJECTIVE_0; GSYM NORM_EQ_0]);;

let ORTHOGONAL_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N x y.
     linear f /\ (!x. norm(f x) = norm x)
     ==> (orthogonal (f x) (f y) <=> orthogonal x y)`,
  SIMP_TAC[orthogonal; PRESERVES_NORM_PRESERVES_DOT]);;

add_linear_invariants
 [GSYM LINEAR_ADD;
  GSYM LINEAR_CMUL;
  GSYM LINEAR_SUB;
  GSYM LINEAR_NEG;
  MIDPOINT_LINEAR_IMAGE;
  MESON[] `!f:real^M->real^N x.
                (!x. norm(f x) = norm x) ==> norm(f x) = norm x`;
  PRESERVES_NORM_PRESERVES_DOT;
  MESON[dist; LINEAR_SUB]
    `!f:real^M->real^N x y.
        linear f /\ (!x. norm(f x) = norm x)
        ==> dist(f x,f y) = dist(x,y)`;
  MESON[] `!f:real^M->real^N x y.
                (!x y. f x = f y ==> x = y) ==> (f x = f y <=> x = y)`;
  SUBSPACE_LINEAR_IMAGE_EQ;
  ORTHOGONAL_LINEAR_IMAGE_EQ;
  SPAN_LINEAR_IMAGE;
  DEPENDENT_LINEAR_IMAGE_EQ;
  INDEPENDENT_LINEAR_IMAGE_EQ;
  DIM_INJECTIVE_LINEAR_IMAGE];;

add_translation_invariants
 [VECTOR_ARITH `!a x y. a + x:real^N = a + y <=> x = y`;
  NORM_ARITH `!a x y. dist(a + x,a + y) = dist(x,y)`;
  VECTOR_ARITH `!a x y. &1 / &2 % ((a + x) + (a + y)) = a + &1 / &2 % (x + y)`;
  VECTOR_ARITH `!a x y. inv(&2) % ((a + x) + (a + y)) = a + inv(&2) % (x + y)`;
  VECTOR_ARITH `!a x y. (a + x) - (a + y):real^N = x - y`;
  (EQT_ELIM o (REWRITE_CONV[midpoint] THENC(EQT_INTRO o NORM_ARITH)))
               `!a x y. midpoint(a + x,a + y) = a + midpoint(x,y)`;
  (EQT_ELIM o (REWRITE_CONV[between] THENC(EQT_INTRO o NORM_ARITH)))
               `!a x y z. between (a + x) (a + y,a + z) <=> between x (y,z)`];;

let th = prove
 (`!a s b c:real^N. (a + b) + c IN IMAGE (\x. a + x) s <=> (b + c) IN s`,
  REWRITE_TAC[IN_IMAGE; VECTOR_ARITH
    `(a + b) + c:real^N = a + x <=> x = b + c`] THEN
  MESON_TAC[]) in
add_translation_invariants [th];;

(* ------------------------------------------------------------------------- *)
(* A few for lists.                                                          *)
(* ------------------------------------------------------------------------- *)

let MEM_TRANSLATION = prove
 (`!a:real^N x l. MEM (a + x) (MAP (\x. a + x) l) <=> MEM x l`,
  REWRITE_TAC[MEM_MAP; VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  MESON_TAC[]);;

add_translation_invariants [MEM_TRANSLATION];;

let MEM_LINEAR_IMAGE = prove
 (`!f:real^M->real^N x l.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (MEM (f x) (MAP f l) <=> MEM x l)`,
  REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]);;

add_linear_invariants [MEM_LINEAR_IMAGE];;

let LENGTH_TRANSLATION = prove
 (`!a:real^N l. LENGTH(MAP (\x. a + x) l) = LENGTH l`,
  REWRITE_TAC[LENGTH_MAP]) in
add_translation_invariants [LENGTH_TRANSLATION];;

let LENGTH_LINEAR_IMAGE = prove
 (`!f:real^M->real^N l. linear f ==> LENGTH(MAP f l) = LENGTH l`,
  REWRITE_TAC[LENGTH_MAP]) in
add_linear_invariants [LENGTH_LINEAR_IMAGE];;

let CONS_TRANSLATION = prove
 (`!a:real^N h t.
     CONS ((\x. a + x) h) (MAP (\x. a + x) t) = MAP (\x. a + x) (CONS h t)`,
  REWRITE_TAC[MAP]) in
add_translation_invariants [CONS_TRANSLATION];;

let CONS_LINEAR_IMAGE = prove
 (`!f:real^M->real^N h t.
     linear f ==> CONS (f h) (MAP f t) = MAP f (CONS h t)`,
  REWRITE_TAC[MAP]) in
add_linear_invariants [CONS_LINEAR_IMAGE];;

let APPEND_TRANSLATION = prove
 (`!a:real^N l1 l2.
     APPEND (MAP (\x. a + x) l1) (MAP (\x. a + x) l2) =
     MAP (\x. a + x) (APPEND l1 l2)`,
  REWRITE_TAC[MAP_APPEND]) in
add_translation_invariants [APPEND_TRANSLATION];;

let APPEND_LINEAR_IMAGE = prove
 (`!f:real^M->real^N l1 l2.
     linear f ==> APPEND (MAP f l1) (MAP f l2) = MAP f (APPEND l1 l2)`,
  REWRITE_TAC[MAP_APPEND]) in
add_linear_invariants [APPEND_LINEAR_IMAGE];;

let REVERSE_TRANSLATION = prove
 (`!a:real^N l. REVERSE(MAP (\x. a + x) l) = MAP (\x. a + x) (REVERSE l)`,
  REWRITE_TAC[MAP_REVERSE]) in
add_translation_invariants [REVERSE_TRANSLATION];;

let REVERSE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N l. linear f ==> REVERSE(MAP f l) = MAP f (REVERSE l)`,
  REWRITE_TAC[MAP_REVERSE]) in
add_linear_invariants [REVERSE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* A few scaling theorems that don't come from invariance theorems. Most are *)
(* artificially weak with 0 < c hypotheses, so we don't bind them to names.  *)
(* ------------------------------------------------------------------------- *)

let DOT_SCALING = prove
 (`!c. &0 < c ==> !x y. (c % x) dot (c % y) = c pow 2 * (x dot y)`,
  REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN REAL_ARITH_TAC) in
add_scaling_theorems [DOT_SCALING];;

let DIST_SCALING = prove
 (`!c. &0 < c ==> !x y. dist(c % x,c % y) = c * dist(x,y)`,
  SIMP_TAC[DIST_MUL; REAL_ARITH `&0 < c ==> abs c = c`]) in
add_scaling_theorems [DIST_SCALING];;

let ORTHOGONAL_SCALING = prove
 (`!c. &0 < c ==> !x y. orthogonal (c % x) (c % y) <=> orthogonal x y`,
  REWRITE_TAC[orthogonal; DOT_LMUL; DOT_RMUL] THEN CONV_TAC REAL_FIELD) in
add_scaling_theorems [ORTHOGONAL_SCALING];;

let NORM_SCALING = prove
 (`!c. &0 < c ==> !x. norm(c % x) = c * norm x`,
  SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < c ==> abs c = c`]) in
add_scaling_theorems [NORM_SCALING];;

add_scaling_theorems
  [REAL_ARITH `!c. &0 < c ==> !a b. a * c * b = c * a * b`;
   REAL_ARITH `!c. &0 < c ==> !a b. c * a + c * b = c * (a + b)`;
   REAL_ARITH `!c. &0 < c ==> !a b. c * a - c * b = c * (a - b)`;
   REAL_FIELD `!c. &0 < c ==> !a b. c * a = c * b <=> a = b`;
   MESON[REAL_LT_LMUL_EQ] `!c. &0 < c ==> !a b. c * a < c * b <=> a < b`;
   MESON[REAL_LE_LMUL_EQ] `!c. &0 < c ==> !a b. c * a <= c * b <=> a <= b`;
   MESON[REAL_LT_LMUL_EQ; real_gt]
     `!c. &0 < c ==> !a b. c * a > c * b <=> a > b`;
   MESON[REAL_LE_LMUL_EQ; real_ge]
     `!c. &0 < c ==> !a b. c * a >= c * b <=> a >= b`;
   MESON[REAL_POW_MUL]
    `!c. &0 < c ==> !a n. (c * a) pow n = c pow n * a pow n`;
   REAL_ARITH `!c. &0 < c ==> !a b n. a * c pow n * b = c pow n * a * b`;
   REAL_ARITH
    `!c. &0 < c ==> !a b n. c pow n * a + c pow n * b = c pow n * (a + b)`;
   REAL_ARITH
    `!c. &0 < c ==> !a b n. c pow n * a - c pow n * b = c pow n * (a - b)`;
   MESON[REAL_POW_LT; REAL_EQ_LCANCEL_IMP; REAL_LT_IMP_NZ]
    `!c. &0 < c ==> !a b n. c pow n * a = c pow n * b <=> a = b`;
   MESON[REAL_LT_LMUL_EQ; REAL_POW_LT]
     `!c. &0 < c ==> !a b n. c pow n * a < c pow n * b <=> a < b`;
   MESON[REAL_LE_LMUL_EQ; REAL_POW_LT]
     `!c. &0 < c ==> !a b n. c pow n * a <= c pow n * b <=> a <= b`;
   MESON[REAL_LT_LMUL_EQ; real_gt; REAL_POW_LT]
     `!c. &0 < c ==> !a b n. c pow n * a > c pow n * b <=> a > b`;
   MESON[REAL_LE_LMUL_EQ; real_ge; REAL_POW_LT]
     `!c. &0 < c ==> !a b n. c pow n * a >= c pow n * b <=> a >= b`];;

(* ------------------------------------------------------------------------- *)
(* Theorem deducing quantifier mappings from surjectivity.                   *)
(* ------------------------------------------------------------------------- *)

let QUANTIFY_SURJECTION_THM = prove
 (`!f:A->B.
        (!y. ?x. f x = y)
        ==> ((!P. (!x. P x) <=> (!x. P (f x))) /\
             (!P. (?x. P x) <=> (?x. P (f x))) /\
             (!Q. (!s. Q s) <=> (!s. Q(IMAGE f s))) /\
             (!Q. (?s. Q s) <=> (?s. Q(IMAGE f s)))) /\
            (!P. {x | P x} = IMAGE f {x | P(f x)})`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [SURJECTIVE_RIGHT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN
  SUBGOAL_THEN `!s. IMAGE (f:A->B) (IMAGE g s) = s` ASSUME_TAC THENL
   [ASM SET_TAC[]; CONJ_TAC THENL [ASM MESON_TAC[]; ASM SET_TAC[]]]);;

let QUANTIFY_SURJECTION_HIGHER_THM = prove
 (`!f:A->B.
        (!y. ?x. f x = y)
        ==> ((!P. (!x. P x) <=> (!x. P (f x))) /\
             (!P. (?x. P x) <=> (?x. P (f x))) /\
             (!Q. (!s. Q s) <=> (!s. Q(IMAGE f s))) /\
             (!Q. (?s. Q s) <=> (?s. Q(IMAGE f s))) /\
             (!Q. (!s. Q s) <=> (!s. Q(IMAGE (IMAGE f) s))) /\
             (!Q. (?s. Q s) <=> (?s. Q(IMAGE (IMAGE f) s))) /\
             (!P. (!g:real^1->B. P g) <=> (!g. P(f o g))) /\
             (!P. (?g:real^1->B. P g) <=> (?g. P(f o g))) /\
             (!P. (!g:num->B. P g) <=> (!g. P(f o g))) /\
             (!P. (?g:num->B. P g) <=> (?g. P(f o g))) /\
             (!Q. (!l. Q l) <=> (!l. Q(MAP f l))) /\
             (!Q. (?l. Q l) <=> (?l. Q(MAP f l)))) /\
            ((!P. {x | P x} = IMAGE f {x | P(f x)}) /\
             (!Q. {s | Q s} = IMAGE (IMAGE f) {s | Q(IMAGE f s)}) /\
             (!R. {l | R l} = IMAGE (MAP f) {l | R(MAP f l)}))`,
  GEN_TAC THEN DISCH_TAC THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  ASM_REWRITE_TAC[GSYM SURJECTIVE_FORALL_THM; GSYM SURJECTIVE_EXISTS_THM;
            GSYM SURJECTIVE_IMAGE_THM; SURJECTIVE_IMAGE; SURJECTIVE_MAP] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM SKOLEM_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Apply such quantifier and set expansions once per level at depth.         *)
(* In the PARTIAL version, avoid expanding named variables in list.          *)
(* ------------------------------------------------------------------------- *)

let PARTIAL_EXPAND_QUANTS_CONV avoid th =
  let ath,sth = CONJ_PAIR th in
  let conv1 = GEN_REWRITE_CONV I [ath]
  and conv2 = GEN_REWRITE_CONV I [sth] in
  let conv1' tm =
    let th = conv1 tm in
    if mem (fst(dest_var(fst(dest_abs(rand tm))))) avoid
    then failwith "Not going to expand this variable" else th in
  let rec conv tm =
   ((conv1' THENC BINDER_CONV conv) ORELSEC
    (conv2 THENC
     RAND_CONV(RAND_CONV(ABS_CONV(BINDER_CONV(LAND_CONV conv))))) ORELSEC
    SUB_CONV conv) tm in
  conv;;

let EXPAND_QUANTS_CONV = PARTIAL_EXPAND_QUANTS_CONV [];;
