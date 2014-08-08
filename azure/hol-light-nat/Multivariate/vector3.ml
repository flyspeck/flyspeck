open Hol_core
include Vector2

(* ------------------------------------------------------------------------- *)
(* Individual closure properties.                                            *)
(* ------------------------------------------------------------------------- *)

let SPAN_SUPERSET = prove
 (`!x. x IN s ==> x IN span s`,
  MESON_TAC[SPAN_CLAUSES]);;

let SPAN_INC = prove
 (`!s. s SUBSET span s`,
  REWRITE_TAC[SUBSET; SPAN_SUPERSET]);;

let SPAN_UNION_SUBSET = prove
 (`!s t. span s UNION span t SUBSET span(s UNION t)`,
  REWRITE_TAC[span; HULL_UNION_SUBSET]);;

let SPAN_UNIV = prove
 (`span(:real^N) = (:real^N)`,
  SIMP_TAC[SPAN_INC; SET_RULE `UNIV SUBSET s ==> s = UNIV`]);;

let SPAN_0 = prove
 (`vec(0) IN span s`,
  MESON_TAC[SUBSPACE_SPAN; SUBSPACE_0]);;

let SPAN_ADD = prove
 (`!x y s. x IN span s /\ y IN span s ==> (x + y) IN span s`,
  MESON_TAC[SUBSPACE_SPAN; SUBSPACE_ADD]);;

let SPAN_MUL = prove
 (`!x c s. x IN span s ==> (c % x) IN span s`,
  MESON_TAC[SUBSPACE_SPAN; SUBSPACE_MUL]);;

let SPAN_MUL_EQ = prove
 (`!x:real^N c s. ~(c = &0) ==> ((c % x) IN span s <=> x IN span s)`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN ASM_SIMP_TAC[SPAN_MUL] THEN
  SUBGOAL_THEN `(inv(c) % c % x:real^N) IN span s` MP_TAC THENL
   [ASM_SIMP_TAC[SPAN_MUL];
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID]]);;

let SPAN_NEG = prove
 (`!x s. x IN span s ==> (--x) IN span s`,
  MESON_TAC[SUBSPACE_SPAN; SUBSPACE_NEG]);;

let SPAN_NEG_EQ = prove
 (`!x s. --x IN span s <=> x IN span s`,
  MESON_TAC[SPAN_NEG; VECTOR_NEG_NEG]);;

let SPAN_SUB = prove
 (`!x y s. x IN span s /\ y IN span s ==> (x - y) IN span s`,
  MESON_TAC[SUBSPACE_SPAN; SUBSPACE_SUB]);;

let SPAN_VSUM = prove
 (`!s f t. FINITE t /\ (!x. x IN t ==> f(x) IN span(s))
           ==> (vsum t f) IN span(s)`,
  MESON_TAC[SUBSPACE_SPAN; SUBSPACE_VSUM]);;

let SPAN_ADD_EQ = prove
 (`!s x y. x IN span s ==> ((x + y) IN span s <=> y IN span s)`,
  MESON_TAC[SPAN_ADD; SPAN_SUB; VECTOR_ARITH `(x + y) - x:real^N = y`]);;

let SPAN_EQ_SELF = prove
 (`!s. span s = s <=> subspace s`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[SUBSPACE_SPAN]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SPAN_SUBSPACE THEN
  ASM_REWRITE_TAC[SUBSET_REFL; SPAN_INC]);;

let SPAN_OF_SUBSPACE = prove
 (`!s:real^N->bool. subspace s ==> span s = s`,
  REWRITE_TAC[SPAN_EQ_SELF]);;

let SPAN_SUBSET_SUBSPACE = prove
 (`!s t:real^N->bool. s SUBSET t /\ subspace t ==> span s SUBSET t`,
  MESON_TAC[SPAN_MONO; SPAN_EQ_SELF]);;

let SUBSPACE_TRANSLATION_SELF = prove
 (`!s a. subspace s /\ a IN s ==> IMAGE (\x. a + x) s = s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o GEN_REWRITE_RULE I [GSYM SPAN_EQ_SELF]) THEN
  ASM_SIMP_TAC[SPAN_ADD_EQ; SPAN_CLAUSES] THEN
  REWRITE_TAC[VECTOR_ARITH `a + x:real^N = y <=> x = y - a`; EXISTS_REFL]);;

let SUBSPACE_TRANSLATION_SELF_EQ = prove
 (`!s a:real^N. subspace s ==> (IMAGE (\x. a + x) s = s <=> a IN s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[SUBSPACE_TRANSLATION_SELF] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\s. (a:real^N) IN s`) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^N` THEN
  ASM_MESON_TAC[subspace; VECTOR_ADD_RID]);;

let SUBSPACE_SUMS = prove
 (`!s t. subspace s /\ subspace t
         ==> subspace {x + y | x IN s /\ y IN t}`,
  REWRITE_TAC[subspace; FORALL_IN_GSPEC; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[VECTOR_ADD_LID];
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `(x + y) + (x' + y'):real^N = (x + x') + (y + y')`] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[VECTOR_ADD_LDISTRIB] THEN ASM_MESON_TAC[]]);;

let SPAN_UNION = prove
 (`!s t. span(s UNION t) = {x + y:real^N | x IN span s /\ y IN span t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
    SIMP_TAC[SUBSPACE_SUMS; SUBSPACE_SPAN] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`x:real^N`; `vec 0:real^N`] THEN
      ASM_SIMP_TAC[SPAN_SUPERSET; SPAN_0; VECTOR_ADD_RID];
      MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `x:real^N`] THEN
      ASM_SIMP_TAC[SPAN_SUPERSET; SPAN_0; VECTOR_ADD_LID]];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_ADD THEN
    ASM_MESON_TAC[SPAN_MONO; SUBSET_UNION; SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Mapping under linear image.                                               *)
(* ------------------------------------------------------------------------- *)

let SPAN_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s. linear f ==> (span(IMAGE f s) = IMAGE f (span s))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [SPEC_TAC(`x:real^N`,`x:real^N`) THEN MATCH_MP_TAC SPAN_INDUCT THEN
    REWRITE_TAC[SET_RULE `(\x. x IN s) = s`] THEN
    ASM_SIMP_TAC[SUBSPACE_SPAN; SUBSPACE_LINEAR_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN
    MESON_TAC[SPAN_SUPERSET; SUBSET];
    SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC SPAN_INDUCT THEN
    REWRITE_TAC[SET_RULE `(\x. f x IN span(s)) = {x | f(x) IN span s}`] THEN
    ASM_SIMP_TAC[SUBSPACE_LINEAR_PREIMAGE; SUBSPACE_SPAN] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[SPAN_SUPERSET; SUBSET; IN_IMAGE]]);;

let DEPENDENT_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (dependent(IMAGE f s) <=> dependent s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dependent; EXISTS_IN_IMAGE] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:real^M` THEN
  ASM_CASES_TAC `(a:real^M) IN s` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(f:real^M->real^N) a IN span(IMAGE f (s DELETE a))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    ASM_SIMP_TAC[SPAN_LINEAR_IMAGE] THEN ASM SET_TAC[]]);;

let DEPENDENT_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        dependent(s)
        ==> dependent(IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[dependent; EXISTS_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^M` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) s DELETE f a = IMAGE f (s DELETE a)`
   (fun th -> ASM_SIMP_TAC[FUN_IN_IMAGE; SPAN_LINEAR_IMAGE; th]) THEN
  ASM SET_TAC[]);;

let INDEPENDENT_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (independent(IMAGE f s) <=> independent s)`,
  REWRITE_TAC[independent; TAUT `(~p <=> ~q) <=> (p <=> q)`] THEN
  REWRITE_TAC[DEPENDENT_LINEAR_IMAGE_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The key breakdown property.                                               *)
(* ------------------------------------------------------------------------- *)

let SPAN_BREAKDOWN = prove
 (`!b s a:real^N.
      b IN s /\ a IN span s ==> ?k. (a - k % b) IN span(s DELETE b)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPAN_INDUCT THEN
  REWRITE_TAC[subspace; IN_ELIM_THM] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `a:real^N = b`; ALL_TAC] THEN
  ASM_MESON_TAC[SPAN_CLAUSES; IN_DELETE; VECTOR_ARITH
   `(a - &1 % a = vec 0) /\ (a - &0 % b = a) /\
    ((x + y) - (k1 + k2) % b = (x - k1 % b) + (y - k2 % b)) /\
    (c % x - (c * k) % y = c % (x - k % y))`]);;

let SPAN_BREAKDOWN_EQ = prove
 (`!a:real^N s. (x IN span(a INSERT s) <=> (?k. (x - k % a) IN span s))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o CONJ(SET_RULE `(a:real^N) IN (a INSERT s)`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SPAN_BREAKDOWN) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN
    SPEC_TAC(`x - k % a:real^N`,`y:real^N`) THEN
    REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC SPAN_MONO THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
    SUBST1_TAC(VECTOR_ARITH `x = (x - k % a) + k % a:real^N`) THEN
    MATCH_MP_TAC SPAN_ADD THEN
    ASM_MESON_TAC[SPAN_MONO; SUBSET; IN_INSERT; SPAN_CLAUSES]]);;

let SPAN_INSERT_0 = prove
 (`!s. span(vec 0 INSERT s) = span s`,
  SIMP_TAC[EXTENSION; SPAN_BREAKDOWN_EQ; VECTOR_MUL_RZERO; VECTOR_SUB_RZERO]);;

let SPAN_SING = prove
 (`!a. span {a} = {u % a | u IN (:real)}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; SPAN_BREAKDOWN_EQ; SPAN_EMPTY] THEN
  REWRITE_TAC[IN_UNIV; IN_SING; VECTOR_SUB_EQ]);;

let SPAN_2 = prove
 (`!a b. span {a,b} = {u % a + v % b | u IN (:real) /\ v IN (:real)}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; SPAN_BREAKDOWN_EQ; SPAN_EMPTY] THEN
  REWRITE_TAC[IN_UNIV; IN_SING; VECTOR_SUB_EQ] THEN
  REWRITE_TAC[VECTOR_ARITH `x - y:real^N = z <=> x = y + z`]);;

let SPAN_3 = prove
 (`!a b c. span {a,b,c} =
      {u % a + v % b + w % c | u IN (:real) /\ v IN (:real) /\ w IN (:real)}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; SPAN_BREAKDOWN_EQ; SPAN_EMPTY] THEN
  REWRITE_TAC[IN_UNIV; IN_SING; VECTOR_SUB_EQ] THEN
  REWRITE_TAC[VECTOR_ARITH `x - y:real^N = z <=> x = y + z`]);;

(* ------------------------------------------------------------------------- *)
(* Hence some "reversal" results.                                            *)
(* ------------------------------------------------------------------------- *)

let IN_SPAN_INSERT = prove
 (`!a b:real^N s.
        a IN span(b INSERT s) /\ ~(a IN span s) ==> b IN span(a INSERT s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^N`; `(b:real^N) INSERT s`; `a:real^N`]
    SPAN_BREAKDOWN) THEN ASM_REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` MP_TAC) THEN ASM_CASES_TAC `k = &0` THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `a - &0 % b = a`; DELETE_INSERT] THENL
   [ASM_MESON_TAC[SPAN_MONO; SUBSET; DELETE_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(k)` o MATCH_MP SPAN_MUL) THEN
  ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC; REAL_MUL_LINV] THEN
  DISCH_TAC THEN SUBST1_TAC(VECTOR_ARITH
   `b:real^N = inv(k) % a - (inv(k) % a - &1 % b)`) THEN
  MATCH_MP_TAC SPAN_SUB THEN
  ASM_MESON_TAC[SPAN_CLAUSES; IN_INSERT; SUBSET; IN_DELETE; SPAN_MONO]);;

let IN_SPAN_DELETE = prove
 (`!a b s.
         a IN span s /\ ~(a IN span (s DELETE b))
         ==> b IN span (a INSERT (s DELETE b))`,
  ASM_MESON_TAC[IN_SPAN_INSERT; SPAN_MONO; SUBSET; IN_INSERT; IN_DELETE]);;

let EQ_SPAN_INSERT_EQ = prove
 (`!s x y:real^N. (x - y) IN span s ==> span(x INSERT s) = span(y INSERT s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SPAN_BREAKDOWN_EQ; EXTENSION] THEN
  ASM_MESON_TAC[SPAN_ADD; SPAN_SUB; SPAN_MUL;
                VECTOR_ARITH `(z - k % y) - k % (x - y) = z - k % x`;
                VECTOR_ARITH `(z - k % x) + k % (x - y) = z - k % y`]);;

(* ------------------------------------------------------------------------- *)
(* Transitivity property.                                                    *)
(* ------------------------------------------------------------------------- *)

let SPAN_TRANS = prove
 (`!x y:real^N s. x IN span(s) /\ y IN span(x INSERT s) ==> y IN span(s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real^N`; `(x:real^N) INSERT s`; `y:real^N`]
         SPAN_BREAKDOWN) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  SUBST1_TAC(VECTOR_ARITH `y:real^N = (y - k % x) + k % x`) THEN
  MATCH_MP_TAC SPAN_ADD THEN ASM_SIMP_TAC[SPAN_MUL] THEN
  ASM_MESON_TAC[SPAN_MONO; SUBSET; IN_INSERT; IN_DELETE]);;

(* ------------------------------------------------------------------------- *)
(* An explicit expansion is sometimes needed.                                *)
(* ------------------------------------------------------------------------- *)

let SPAN_EXPLICIT = prove
 (`!(p:real^N -> bool).
        span p =
         {y | ?s u. FINITE s /\ s SUBSET p /\
                    vsum s (\v. u v % v) = y}`,
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SPAN_VSUM THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SPAN_SUPERSET; SPAN_MUL]] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  MATCH_MP_TAC SPAN_INDUCT_ALT THEN CONJ_TAC THENL
   [EXISTS_TAC `{}:real^N->bool` THEN
    REWRITE_TAC[FINITE_RULES; VSUM_CLAUSES; EMPTY_SUBSET; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`; `y:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `u:real^N->real`] THEN
  STRIP_TAC THEN EXISTS_TAC `(x:real^N) INSERT s` THEN
  EXISTS_TAC `\y. if y = x then (if x IN s then (u:real^N->real) y + c else c)
                  else u y` THEN
  ASM_SIMP_TAC[FINITE_INSERT; IN_INSERT; VSUM_CLAUSES] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
    ASM_SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_DELETE; IN_DELETE] THEN
    MATCH_MP_TAC(VECTOR_ARITH
      `y = z ==> (c + d) % x + y = d % x + c % x + z`);
    AP_TERM_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN ASM_MESON_TAC[IN_DELETE]);;

let DEPENDENT_EXPLICIT = prove
 (`!p. dependent (p:real^N -> bool) <=>
                ?s u. FINITE s /\ s SUBSET p /\
                      (?v. v IN s /\ ~(u v = &0)) /\
                      vsum s (\v. u v % v) = vec 0`,
  GEN_TAC THEN REWRITE_TAC[dependent; SPAN_EXPLICIT; IN_ELIM_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`a:real^N`; `s:real^N->bool`; `u:real^N->real`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`(a:real^N) INSERT s`;
      `\y. if y = a then -- &1 else (u:real^N->real) y`;
      `a:real^N`] THEN
    ASM_REWRITE_TAC[IN_INSERT; INSERT_SUBSET; FINITE_INSERT] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    ASM_SIMP_TAC[VSUM_CLAUSES] THEN
    COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `-- &1 % a + s = vec 0 <=> a = s`] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    MATCH_MP_TAC VSUM_EQ THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `u:real^N->real`; `a:real^N`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`a:real^N`; `s DELETE (a:real^N)`;
      `\i. --((u:real^N->real) i) / (u a)`] THEN
    ASM_SIMP_TAC[VSUM_DELETE; FINITE_DELETE] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LNEG; GSYM VECTOR_MUL_ASSOC; VSUM_LMUL;
                    VSUM_NEG; VECTOR_MUL_RNEG; VECTOR_MUL_RZERO] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV] THEN VECTOR_ARITH_TAC]);;

let DEPENDENT_FINITE = prove
 (`!s:real^N->bool.
        FINITE s
        ==> (dependent s <=> ?u. (?v. v IN s /\ ~(u v = &0)) /\
                                 vsum s (\v. u(v) % v) = vec 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DEPENDENT_EXPLICIT] THEN EQ_TAC THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->real`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    EXISTS_TAC `\v:real^N. if v IN t then u(v) else &0` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO; GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`];
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `u:real^N->real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

let SPAN_FINITE = prove
 (`!s:real^N->bool.
        FINITE s ==> span s = {y | ?u. vsum s (\v. u v % v) = y}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SPAN_EXPLICIT; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->real`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `\x:real^N. if x IN t then u(x) else &0` THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC[GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`];
    X_GEN_TAC `u:real^N->real` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `u:real^N->real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Standard bases are a spanning set, and obviously finite.                  *)
(* ------------------------------------------------------------------------- *)

let SPAN_STDBASIS = prove
 (`span {basis i :real^N | 1 <= i /\ i <= dimindex(:N)} = UNIV`,
  REWRITE_TAC[EXTENSION; IN_UNIV] THEN X_GEN_TAC `x:real^N` THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
  MATCH_MP_TAC SPAN_VSUM THEN SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
  MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let HAS_SIZE_STDBASIS = prove
 (`{basis i :real^N | 1 <= i /\ i <= dimindex(:N)} HAS_SIZE
        dimindex(:N)`,
  ONCE_REWRITE_TAC[SET_RULE `{f x | P x} = IMAGE f {x | P x}`] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  REWRITE_TAC[GSYM numseg; HAS_SIZE_NUMSEG_1; IN_NUMSEG] THEN
  MESON_TAC[BASIS_INJ]);;

let FINITE_STDBASIS = prove
 (`FINITE {basis i :real^N | 1 <= i /\ i <= dimindex(:N)}`,
  MESON_TAC[HAS_SIZE_STDBASIS; HAS_SIZE]);;

let CARD_STDBASIS = prove
 (`CARD {basis i :real^N | 1 <= i /\ i <= dimindex(:N)} =
        dimindex(:N)`,
   MESON_TAC[HAS_SIZE_STDBASIS; HAS_SIZE]);;

let IN_SPAN_IMAGE_BASIS = prove
 (`!x:real^N s.
        x IN span(IMAGE basis s) <=>
          !i. 1 <= i /\ i <= dimindex(:N) /\ ~(i IN s) ==> x$i = &0`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`x:real^N`,`x:real^N`) THEN MATCH_MP_TAC SPAN_INDUCT THEN
    SIMP_TAC[subspace; IN_ELIM_THM; VEC_COMPONENT; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    SIMP_TAC[FORALL_IN_IMAGE; BASIS_COMPONENT] THEN MESON_TAC[];
    DISCH_TAC THEN REWRITE_TAC[SPAN_EXPLICIT; IN_ELIM_THM] THEN
    EXISTS_TAC `(IMAGE basis ((1..dimindex(:N)) INTER s)):real^N->bool` THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_INTER; FINITE_NUMSEG] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `\v:real^N. x dot v` THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL
     [SIMP_TAC[FINITE_IMAGE; FINITE_INTER; FINITE_NUMSEG] THEN
      REWRITE_TAC[IN_INTER; IN_NUMSEG] THEN MESON_TAC[BASIS_INJ];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]] THEN
    REWRITE_TAC[o_DEF] THEN
    SIMP_TAC[CART_EQ; VSUM_COMPONENT; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    ONCE_REWRITE_TAC[MESON[]
     `(if x = y then p else q) = (if y = x then p else q)`] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_RZERO; IN_INTER; IN_NUMSEG; DOT_BASIS] THEN
    ASM_MESON_TAC[REAL_MUL_RID]]);;

let INDEPENDENT_STDBASIS = prove
 (`independent {basis i :real^N | 1 <= i /\ i <= dimindex(:N)}`,
  REWRITE_TAC[independent; dependent] THEN
  ONCE_REWRITE_TAC[SET_RULE `{f x | P x} = IMAGE f {x | P x}`] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN
   `IMAGE basis {i | 1 <= i /\ i <= dimindex(:N)} DELETE
           (basis k:real^N) =
    IMAGE basis ({i | 1 <= i /\ i <= dimindex(:N)} DELETE k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_ELIM_THM] THEN
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[BASIS_INJ];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SPAN_IMAGE_BASIS] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
  ASM_SIMP_TAC[IN_DELETE; BASIS_COMPONENT; REAL_OF_NUM_EQ; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* This is useful for building a basis step-by-step.                         *)
(* ------------------------------------------------------------------------- *)

let INDEPENDENT_INSERT = prove
 (`!a:real^N s. independent(a INSERT s) <=>
                  if a IN s then independent s
                  else independent s /\ ~(a IN span s)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(a:real^N) IN s` THEN
  ASM_SIMP_TAC[SET_RULE `x IN s ==> (x INSERT s = s)`] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[INDEPENDENT_MONO; SUBSET; IN_INSERT];
      POP_ASSUM MP_TAC THEN REWRITE_TAC[independent; dependent] THEN
      ASM_MESON_TAC[IN_INSERT; SET_RULE
        `~(a IN s) ==> ((a INSERT s) DELETE a = s)`]];
    ALL_TAC] THEN
  REWRITE_TAC[independent; dependent; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN X_GEN_TAC `b:real^N` THEN
  REWRITE_TAC[IN_INSERT] THEN ASM_CASES_TAC `b:real^N = a` THEN
  ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> ((a INSERT s) DELETE a = s)`] THEN
  ASM_SIMP_TAC[SET_RULE
    `~(a IN s) /\ ~(b = a)
     ==> ((a INSERT s) DELETE b = a INSERT (s DELETE b))`] THEN
  ASM_MESON_TAC[IN_SPAN_INSERT; SET_RULE
    `b IN s ==> (b INSERT (s DELETE b) = s)`]);;

(* ------------------------------------------------------------------------- *)
(* The degenerate case of the Exchange Lemma.                                *)
(* ------------------------------------------------------------------------- *)

let SPANNING_SUBSET_INDEPENDENT = prove
 (`!s t:real^N->bool.
        t SUBSET s /\ independent s /\ s SUBSET span(t) ==> (s = t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [independent]) THEN
  REWRITE_TAC[dependent; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SPAN_MONO; SUBSET; IN_DELETE]);;

(* ------------------------------------------------------------------------- *)
(* The general case of the Exchange Lemma, the key to what follows.          *)
(* ------------------------------------------------------------------------- *)

let EXCHANGE_LEMMA = prove
 (`!s t:real^N->bool.
        FINITE t /\ independent s /\ s SUBSET span t
        ==> ?t'. t' HAS_SIZE (CARD t) /\
                 s SUBSET t' /\ t' SUBSET (s UNION t) /\ s SUBSET (span t')`,
  REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `CARD(t DIFF s :real^N->bool)` THEN
  ASM_CASES_TAC `(s:real^N->bool) SUBSET t` THENL
   [ASM_MESON_TAC[HAS_SIZE; SUBSET_UNION]; ALL_TAC] THEN
  ASM_CASES_TAC `t SUBSET (s:real^N->bool)` THENL
   [ASM_MESON_TAC[SPANNING_SUBSET_INDEPENDENT; HAS_SIZE]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SUBSET] o check(is_neg o concl)) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `s SUBSET span(t DELETE (b:real^N))` THENL
   [FIRST_X_ASSUM(MP_TAC o
     SPECL [`t DELETE (b:real^N)`; `s:real^N->bool`]) THEN
    ASM_REWRITE_TAC[SET_RULE `s DELETE a DIFF t = (s DIFF t) DELETE a`] THEN
    ASM_SIMP_TAC[CARD_DELETE; FINITE_DIFF; IN_DIFF; FINITE_DELETE;
                 CARD_EQ_0; ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~((s:real^N->bool) SUBSET t)` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(b:real^N) INSERT u` THEN
    ASM_SIMP_TAC[SUBSET_INSERT; INSERT_SUBSET; IN_UNION] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(u:real^N->bool) HAS_SIZE CARD(t:real^N->bool) - 1` THEN
      SIMP_TAC[HAS_SIZE; FINITE_RULES; CARD_CLAUSES] THEN STRIP_TAC THEN
      COND_CASES_TAC THENL
       [ASM_MESON_TAC[SUBSET; IN_UNION; IN_DELETE]; ALL_TAC] THEN
      ASM_MESON_TAC[ARITH_RULE `~(n = 0) ==> (SUC(n - 1) = n)`;
                    CARD_EQ_0; MEMBER_NOT_EMPTY];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `u SUBSET s UNION t DELETE (b:real^N)` THEN SET_TAC[];
      ASM_MESON_TAC[SUBSET; SPAN_MONO; IN_INSERT]];
    ALL_TAC] THEN
  UNDISCH_TAC `~(s SUBSET span (t DELETE (b:real^N)))` THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SUBSET] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(a:real^N = b)` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((a:real^N) IN t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_DELETE; SPAN_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(a:real^N) INSERT (t DELETE b)`; `s:real^N->bool`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SET_RULE
     `a IN s ==> ((a INSERT (t DELETE b) DIFF s) = (t DIFF s) DELETE b)`] THEN
    ASM_SIMP_TAC[CARD_DELETE; FINITE_DELETE; FINITE_DIFF; IN_DIFF] THEN
    ASM_SIMP_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`; CARD_EQ_0;
                 FINITE_DIFF] THEN
    UNDISCH_TAC `~((s:real^N->bool) SUBSET t)` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RULES; FINITE_DELETE] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN MATCH_MP_TAC SPAN_TRANS THEN EXISTS_TAC `b:real^N` THEN
    ASM_MESON_TAC[IN_SPAN_DELETE; SUBSET; SPAN_MONO;
                  SET_RULE `t SUBSET (b INSERT (a INSERT (t DELETE b)))`];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
  ASM_SIMP_TAC[HAS_SIZE; CARD_CLAUSES; CARD_DELETE; FINITE_DELETE; IN_DELETE;
               ARITH_RULE `(SUC(n - 1) = n) <=> ~(n = 0)`;
               CARD_EQ_0] THEN
  UNDISCH_TAC `(b:real^N) IN t` THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* This implies corresponding size bounds.                                   *)
(* ------------------------------------------------------------------------- *)

let INDEPENDENT_SPAN_BOUND = prove
 (`!s t. FINITE t /\ independent s /\ s SUBSET span(t)
         ==> FINITE s /\ CARD(s) <= CARD(t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EXCHANGE_LEMMA) THEN
  ASM_MESON_TAC[HAS_SIZE; CARD_SUBSET; FINITE_SUBSET]);;

let INDEPENDENT_BOUND = prove
 (`!s:real^N->bool.
        independent s ==> FINITE s /\ CARD(s) <= dimindex(:N)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM CARD_STDBASIS] THEN
  MATCH_MP_TAC INDEPENDENT_SPAN_BOUND THEN
  ASM_REWRITE_TAC[FINITE_STDBASIS; SPAN_STDBASIS; SUBSET_UNIV]);;

let DEPENDENT_BIGGERSET = prove
 (`!s:real^N->bool. (FINITE s ==> CARD(s) > dimindex(:N)) ==> dependent s`,
  MP_TAC INDEPENDENT_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN
  REWRITE_TAC[GT; GSYM NOT_LE; independent] THEN MESON_TAC[]);;

let INDEPENDENT_IMP_FINITE = prove
 (`!s:real^N->bool. independent s ==> FINITE s`,
  SIMP_TAC[INDEPENDENT_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Explicit formulation of independence.                                     *)
(* ------------------------------------------------------------------------- *)

let INDEPENDENT_EXPLICIT = prove
 (`!b:real^N->bool.
        independent b <=>
            FINITE b /\
            !c. vsum b (\v. c(v) % v) = vec 0 ==> !v. v IN b ==> c(v) = &0`,
  GEN_TAC THEN
  ASM_CASES_TAC `FINITE(b:real^N->bool)` THENL
   [ALL_TAC; ASM_MESON_TAC[INDEPENDENT_BOUND]] THEN
  ASM_SIMP_TAC[independent; DEPENDENT_FINITE] THEN MESON_TAC[]);;

let INDEPENDENT_SING = prove
 (`!x. independent {x} <=> ~(x = vec 0)`,
  REWRITE_TAC[INDEPENDENT_INSERT; NOT_IN_EMPTY; SPAN_EMPTY] THEN
  REWRITE_TAC[INDEPENDENT_EMPTY] THEN SET_TAC[]);;

let DEPENDENT_SING = prove
 (`!x. dependent {x} <=> x = vec 0`,
  MESON_TAC[independent; INDEPENDENT_SING]);;

let DEPENDENT_2 = prove
 (`!a b:real^N.
        dependent {a,b} <=>
                if a = b then a = vec 0
                else ?x y. x % a + y % b = vec 0 /\ ~(x = &0 /\ y = &0)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[DEPENDENT_SING; SET_RULE `{x,x} = {x}`] THEN
  SIMP_TAC[DEPENDENT_FINITE; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; VECTOR_ADD_RID; EXISTS_IN_INSERT] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [X_GEN_TAC `u:real^N->real` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(u:real^N->real) a`; `(u:real^N->real) b`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN DISCH_TAC THEN EXISTS_TAC
     `\v:real^N. if v = a then x else if v = b then y else z:real` THEN
    ASM_MESON_TAC[]]);;

let DEPENDENT_3 = prove
 (`!a b c:real^N.
        ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> (dependent {a,b,c} <=>
             ?x y z. x % a + y % b + z % c = vec 0 /\
                     ~(x = &0 /\ y = &0 /\ z = &0))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[DEPENDENT_FINITE; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; VECTOR_ADD_RID; IN_INSERT] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [X_GEN_TAC `u:real^N->real` THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`(u:real^N->real) a`; `(u:real^N->real) b`; `(u:real^N->real) c`];
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `z:real`] THEN DISCH_TAC THEN
    EXISTS_TAC
     `\v:real^N. if v = a then x else if v = b then y else z:real`] THEN
  ASM_MESON_TAC[]);;

let INDEPENDENT_2 = prove
 (`!a b:real^N x y.
        independent{a,b} /\ ~(a = b)
        ==> (x % a + y % b = vec 0 <=> x = &0 /\ y = &0)`,
  SIMP_TAC[IMP_CONJ_ALT; independent; DEPENDENT_2] THEN
  MESON_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID]);;

let INDEPENDENT_3 = prove
 (`!a b c:real^N x y z.
        independent{a,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> (x % a + y % b + z % c = vec 0 <=> x = &0 /\ y = &0 /\ z = &0)`,
  SIMP_TAC[IMP_CONJ_ALT; independent; DEPENDENT_3] THEN
  MESON_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID]);;

(* ------------------------------------------------------------------------- *)
(* Hence we can create a maximal independent subset.                         *)
(* ------------------------------------------------------------------------- *)

let MAXIMAL_INDEPENDENT_SUBSET_EXTEND = prove
 (`!s v:real^N->bool.
        s SUBSET v /\ independent s
        ==> ?b. s SUBSET b /\ b SUBSET v /\ independent b /\
                v SUBSET (span b)`,
  REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `dimindex(:N) - CARD(s:real^N->bool)` THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `v SUBSET (span(s:real^N->bool))` THENL
   [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [SUBSET]) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a:real^N) INSERT s`) THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [ALL_TAC; MESON_TAC[INSERT_SUBSET]] THEN
  SUBGOAL_THEN `independent ((a:real^N) INSERT s)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INDEPENDENT_INSERT; COND_ID]; ALL_TAC] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET] THEN
  MATCH_MP_TAC(ARITH_RULE `(b = a + 1) /\ b <= n ==> n - b < n - a`) THEN
  ASM_SIMP_TAC[CARD_CLAUSES; INDEPENDENT_BOUND] THEN
  ASM_MESON_TAC[SPAN_SUPERSET; ADD1]);;

let MAXIMAL_INDEPENDENT_SUBSET = prove
 (`!v:real^N->bool. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b)`,
  MP_TAC(SPEC `EMPTY:real^N->bool` MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  REWRITE_TAC[EMPTY_SUBSET; INDEPENDENT_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* A kind of closed graph property for linearity.                            *)
(* ------------------------------------------------------------------------- *)

let LINEAR_SUBSPACE_GRAPH = prove
 (`!f:real^M->real^N.
        linear f <=> subspace {pastecart x (f x) | x IN (:real^M)}`,
  REWRITE_TAC[linear; subspace; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; GSYM(SPEC `0` PASTECART_VEC); IN_UNIV] THEN
  REWRITE_TAC[IN_ELIM_THM; PASTECART_INJ; UNWIND_THM1; PASTECART_ADD;
              GSYM PASTECART_CMUL] THEN
  MESON_TAC[VECTOR_MUL_LZERO]);;

(* ------------------------------------------------------------------------- *)
(* Notion of dimension.                                                      *)
(* ------------------------------------------------------------------------- *)

let dim = new_definition
  `dim v = @n. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b) /\
                   b HAS_SIZE n`;;

let BASIS_EXISTS = prove
 (`!v. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b) /\
           b HAS_SIZE (dim v)`,
  GEN_TAC THEN REWRITE_TAC[dim] THEN CONV_TAC SELECT_CONV THEN
  MESON_TAC[MAXIMAL_INDEPENDENT_SUBSET; HAS_SIZE; INDEPENDENT_BOUND]);;

let BASIS_EXISTS_FINITE = prove
 (`!v. ?b. FINITE b /\
           b SUBSET v /\
           independent b /\
           v SUBSET (span b) /\
           b HAS_SIZE (dim v)`,
  MESON_TAC[BASIS_EXISTS; INDEPENDENT_IMP_FINITE]);;

let BASIS_SUBSPACE_EXISTS = prove
 (`!s:real^N->bool.
        subspace s
        ==> ?b. FINITE b /\
                b SUBSET s /\
                independent b /\
                span b = s /\
                b HAS_SIZE dim s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` BASIS_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  ASM_MESON_TAC[SPAN_EQ_SELF; SPAN_MONO; INDEPENDENT_IMP_FINITE]);;

(* ------------------------------------------------------------------------- *)
(* Consequences of independence or spanning for cardinality.                 *)
(* ------------------------------------------------------------------------- *)

let INDEPENDENT_CARD_LE_DIM = prove
 (`!v b:real^N->bool.
        b SUBSET v /\ independent b ==> FINITE b /\ CARD(b) <= dim v`,
  MESON_TAC[BASIS_EXISTS; INDEPENDENT_SPAN_BOUND; HAS_SIZE;SUBSET_TRANS]);;

let SPAN_CARD_GE_DIM = prove
 (`!v b:real^N->bool.
        v SUBSET (span b) /\ FINITE b ==> dim(v) <= CARD(b)`,
  MESON_TAC[BASIS_EXISTS; INDEPENDENT_SPAN_BOUND; HAS_SIZE;SUBSET_TRANS]);;

let BASIS_CARD_EQ_DIM = prove
 (`!v b. b SUBSET v /\ v SUBSET (span b) /\ independent b
         ==> FINITE b /\ (CARD b = dim v)`,
  MESON_TAC[LE_ANTISYM; INDEPENDENT_CARD_LE_DIM; SPAN_CARD_GE_DIM]);;

let BASIS_HAS_SIZE_DIM = prove
 (`!v b. independent b /\ span b = v ==> b HAS_SIZE (dim v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  MATCH_MP_TAC BASIS_CARD_EQ_DIM THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SPAN_INC]);;

let DIM_UNIQUE = prove
 (`!v b. b SUBSET v /\ v SUBSET (span b) /\ independent b /\ b HAS_SIZE n
         ==> (dim v = n)`,
  MESON_TAC[BASIS_CARD_EQ_DIM; HAS_SIZE]);;

let DIM_LE_CARD = prove
 (`!s. FINITE s ==> dim s <= CARD s`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
  ASM_REWRITE_TAC[SPAN_INC; SUBSET_REFL]);;

(* ------------------------------------------------------------------------- *)
(* More lemmas about dimension.                                              *)
(* ------------------------------------------------------------------------- *)

let DIM_UNIV = prove
 (`dim(:real^N) = dimindex(:N)`,
  MATCH_MP_TAC DIM_UNIQUE THEN
  EXISTS_TAC `{basis i :real^N | 1 <= i /\ i <= dimindex(:N)}` THEN
  REWRITE_TAC[SUBSET_UNIV; SPAN_STDBASIS; HAS_SIZE_STDBASIS;
              INDEPENDENT_STDBASIS]);;

let DIM_SUBSET = prove
 (`!s t:real^N->bool. s SUBSET t ==> dim(s) <= dim(t)`,
  MESON_TAC[BASIS_EXISTS; INDEPENDENT_SPAN_BOUND; SUBSET; HAS_SIZE]);;

let DIM_SUBSET_UNIV = prove
 (`!s:real^N->bool. dim(s) <= dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[GSYM DIM_UNIV] THEN
  MATCH_MP_TAC DIM_SUBSET THEN REWRITE_TAC[SUBSET_UNIV]);;

let BASIS_HAS_SIZE_UNIV = prove
 (`!b. independent b /\ span b = (:real^N) ==> b HAS_SIZE (dimindex(:N))`,
  REWRITE_TAC[GSYM DIM_UNIV; BASIS_HAS_SIZE_DIM]);;

(* ------------------------------------------------------------------------- *)
(* Converses to those.                                                       *)
(* ------------------------------------------------------------------------- *)

let CARD_GE_DIM_INDEPENDENT = prove
 (`!v b:real^N->bool.
        b SUBSET v /\ independent b /\ dim v <= CARD(b)
        ==> v SUBSET (span b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a:real^N. ~(a IN v /\ ~(a IN span b))` MP_TAC THENL
   [ALL_TAC; SET_TAC[]] THEN
  X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `independent((a:real^N) INSERT b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INDEPENDENT_INSERT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N->bool`; `(a:real^N) INSERT b`]
                INDEPENDENT_CARD_LE_DIM) THEN
  ASM_SIMP_TAC[INSERT_SUBSET; CARD_CLAUSES; INDEPENDENT_BOUND] THEN
  ASM_MESON_TAC[SPAN_SUPERSET; SUBSET; ARITH_RULE
    `x <= y ==> ~(SUC y <= x)`]);;

let CARD_LE_DIM_SPANNING = prove
 (`!v b:real^N->bool.
        v SUBSET (span b) /\ FINITE b /\ CARD(b) <= dim v
        ==> independent b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[independent; dependent] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `dim(v:real^N->bool) <= CARD(b DELETE (a:real^N))` MP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CARD_DELETE] THEN MATCH_MP_TAC
     (ARITH_RULE `b <= n /\ ~(b = 0) ==> ~(n <= b - 1)`) THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN ASM_MESON_TAC[MEMBER_NOT_EMPTY]] THEN
  MATCH_MP_TAC SPAN_CARD_GE_DIM THEN ASM_SIMP_TAC[FINITE_DELETE] THEN
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SPAN_TRANS THEN EXISTS_TAC `a:real^N` THEN
  ASM_SIMP_TAC[SET_RULE `a IN b ==> (a INSERT (b DELETE a) = b)`] THEN
  ASM_MESON_TAC[SUBSET]);;

let CARD_EQ_DIM = prove
 (`!v b. b SUBSET v /\ b HAS_SIZE (dim v)
         ==> (independent b <=> v SUBSET (span b))`,
  REWRITE_TAC[HAS_SIZE; GSYM LE_ANTISYM] THEN
  MESON_TAC[CARD_LE_DIM_SPANNING; CARD_GE_DIM_INDEPENDENT]);;

(* ------------------------------------------------------------------------- *)
(* More general size bound lemmas.                                           *)
(* ------------------------------------------------------------------------- *)

let INDEPENDENT_BOUND_GENERAL = prove
 (`!s:real^N->bool. independent s ==> FINITE s /\ CARD(s) <= dim(s)`,
  MESON_TAC[INDEPENDENT_CARD_LE_DIM; INDEPENDENT_BOUND; SUBSET_REFL]);;

let DEPENDENT_BIGGERSET_GENERAL = prove
 (`!s:real^N->bool. (FINITE s ==> CARD(s) > dim(s)) ==> dependent s`,
  MP_TAC INDEPENDENT_BOUND_GENERAL THEN MATCH_MP_TAC MONO_FORALL THEN
  REWRITE_TAC[GT; GSYM NOT_LE; independent] THEN MESON_TAC[]);;

let DIM_SPAN = prove
 (`!s:real^N->bool. dim(span s) = dim s`,
  GEN_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC DIM_SUBSET THEN MESON_TAC[SUBSET; SPAN_SUPERSET]] THEN
  MP_TAC(ISPEC `s:real^N->bool` BASIS_EXISTS) THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SPAN_CARD_GE_DIM THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SPAN_SPAN] THEN
  MATCH_MP_TAC SPAN_MONO THEN ASM_REWRITE_TAC[]);;

let DIM_INSERT_0 = prove
 (`!s:real^N->bool. dim(vec 0 INSERT s) = dim s`,
  ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  REWRITE_TAC[SPAN_INSERT_0]);;

let DIM_EQ_CARD = prove
 (`!s:real^N->bool. independent s ==> dim s = CARD s`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPECL [`span s:real^N->bool`; `s:real^N->bool`] BASIS_CARD_EQ_DIM) THEN
  ASM_SIMP_TAC[SUBSET_REFL; SPAN_INC; DIM_SPAN]);;

let SUBSET_LE_DIM = prove
 (`!s t:real^N->bool. s SUBSET (span t) ==> dim s <= dim t`,
  MESON_TAC[DIM_SPAN; DIM_SUBSET]);;

let SPAN_EQ_DIM = prove
 (`!s t. span s = span t ==> dim s = dim t`,
  MESON_TAC[DIM_SPAN]);;

let SPANS_IMAGE = prove
 (`!f b v. linear f /\ v SUBSET (span b)
           ==> (IMAGE f v) SUBSET span(IMAGE f b)`,
  SIMP_TAC[SPAN_LINEAR_IMAGE; IMAGE_SUBSET]);;

let DIM_LINEAR_IMAGE_LE = prove
 (`!f:real^M->real^N s. linear f ==> dim(IMAGE f s) <= dim s`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s:real^M->bool` BASIS_EXISTS) THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(IMAGE (f:real^M->real^N) b)` THEN
  ASM_SIMP_TAC[CARD_IMAGE_LE] THEN MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
  ASM_MESON_TAC[SPAN_LINEAR_IMAGE; SPANS_IMAGE; SUBSET_IMAGE; FINITE_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Some stepping theorems.                                                   *)
(* ------------------------------------------------------------------------- *)

let DIM_EMPTY = prove
 (`dim({}:real^N->bool) = 0`,
  MATCH_MP_TAC DIM_UNIQUE THEN EXISTS_TAC `{}:real^N->bool` THEN
  REWRITE_TAC[SUBSET_REFL; SPAN_EMPTY; INDEPENDENT_EMPTY; HAS_SIZE_0;
              EMPTY_SUBSET]);;

let DIM_INSERT = prove
 (`!x:real^N s. dim(x INSERT s) = if x IN span s then dim s else dim s + 1`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC SPAN_EQ_DIM THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_MESON_TAC[SPAN_TRANS; SUBSET; SPAN_MONO; IN_INSERT];
    ALL_TAC] THEN
  X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC
   (ISPEC `span s:real^N->bool` BASIS_EXISTS) THEN
  ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  MATCH_MP_TAC DIM_UNIQUE THEN
  EXISTS_TAC `(x:real^N) INSERT b` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INSERT_SUBSET] THEN
    ASM_MESON_TAC[SUBSET; SPAN_MONO; IN_INSERT; SPAN_SUPERSET];
    REWRITE_TAC[SUBSET; SPAN_BREAKDOWN_EQ] THEN
    ASM_MESON_TAC[SUBSET];
    REWRITE_TAC[INDEPENDENT_INSERT] THEN
    ASM_MESON_TAC[SUBSET; SPAN_SUPERSET; SPAN_MONO; SPAN_SPAN];
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_INSERT; ADD1] THEN
    ASM_MESON_TAC[SUBSET; SPAN_SUPERSET; SPAN_MONO; SPAN_SPAN]]);;

let DIM_SING = prove
 (`!x. dim{x} = if x = vec 0 then 0 else 1`,
  REWRITE_TAC[DIM_INSERT; DIM_EMPTY; SPAN_EMPTY; IN_SING; ARITH]);;

let DIM_EQ_0 = prove
 (`!s:real^N->bool. dim s = 0 <=> s SUBSET {vec 0}`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `~(?b. ~(b = a) /\ {b} SUBSET s) ==> s SUBSET {a}`) THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP DIM_SUBSET);
    MATCH_MP_TAC(ARITH_RULE `!m. m = 0 /\ n <= m ==> n = 0`) THEN
    EXISTS_TAC `dim{vec 0:real^N}` THEN ASM_SIMP_TAC[DIM_SUBSET]] THEN
  ASM_REWRITE_TAC[DIM_SING; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Choosing a subspace of a given dimension.                                 *)
(* ------------------------------------------------------------------------- *)

let CHOOSE_SUBSPACE_OF_SUBSPACE = prove
 (`!s:real^N->bool n.
        n <= dim s ==> ?t. subspace t /\ t SUBSET span s /\ dim t = n`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `{vec 0:real^N}` THEN
    REWRITE_TAC[SUBSPACE_TRIVIAL; DIM_SING; SING_SUBSET; SPAN_0];
    DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `span (s:real^N->bool) SUBSET span t` THENL
     [SUBGOAL_THEN `dim(s:real^N->bool) = dim(t:real^N->bool)` MP_TAC THENL
       [ALL_TAC; ASM_ARITH_TAC] THEN MATCH_MP_TAC SPAN_EQ_DIM THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN ASM_REWRITE_TAC[SUBSPACE_SPAN];
      FIRST_ASSUM(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC o MATCH_MP(SET_RULE
       `~(s SUBSET t) ==> ?a. a IN s /\ ~(a IN t)`)) THEN
      EXISTS_TAC `span((y:real^N) INSERT t)` THEN
      REWRITE_TAC[SUBSPACE_SPAN] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
        ASM_REWRITE_TAC[SUBSPACE_SPAN] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[DIM_SPAN; DIM_INSERT; ADD1]]]]);;

(* ------------------------------------------------------------------------- *)
(* Relation between bases and injectivity/surjectivity of map.               *)
(* ------------------------------------------------------------------------- *)

let SPANNING_SURJECTIVE_IMAGE = prove
 (`!f:real^M->real^N s.
        UNIV SUBSET (span s) /\ linear f /\ (!y. ?x. f(x) = y)
        ==> UNIV SUBSET span(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) UNIV` THEN
  ASM_SIMP_TAC[SPANS_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_UNIV; IN_IMAGE] THEN ASM_MESON_TAC[]);;

let INDEPENDENT_INJECTIVE_IMAGE_GEN = prove
 (`!f:real^M->real^N s.
        independent s /\ linear f /\
        (!x y. x IN span s /\ y IN span s /\ f(x) = f(y) ==> x = y)
        ==> independent (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[independent; DEPENDENT_EXPLICIT] THEN
  REWRITE_TAC[CONJ_ASSOC; FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[MESON[]
     `(?s u. ((?t. p t /\ s = f t) /\ q s u) /\ r s u) <=>
      (?t u. p t /\ q (f t) u /\ r (f t) u)`] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^M->bool`; `u:real^N->real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`t:real^M->bool`; `(u:real^N->real) o (f:real^M->real^N)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_VSUM THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC[];
    REWRITE_TAC[SPAN_0];
    ASM_SIMP_TAC[LINEAR_VSUM] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP LINEAR_0) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
    ASM_SIMP_TAC[o_DEF; LINEAR_CMUL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[SPAN_SUPERSET; SUBSET]]);;

let INDEPENDENT_INJECTIVE_IMAGE = prove
 (`!f:real^M->real^N s.
        independent s /\ linear f /\ (!x y. (f(x) = f(y)) ==> (x = y))
        ==> independent (IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE_GEN THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Picking an orthogonal replacement for a spanning set.                     *)
(* ------------------------------------------------------------------------- *)

let VECTOR_SUB_PROJECT_ORTHOGONAL = prove
 (`!b:real^N x. b dot (x - ((b dot x) / (b dot b)) % b) = &0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b = vec 0 :real^N` THENL
   [ASM_REWRITE_TAC[DOT_LZERO]; ALL_TAC] THEN
  ASM_SIMP_TAC[DOT_RSUB; DOT_RMUL] THEN
  ASM_SIMP_TAC[REAL_SUB_REFL; REAL_DIV_RMUL; DOT_EQ_0]);;

let BASIS_ORTHOGONAL = prove
 (`!b:real^N->bool.
        FINITE b
        ==> ?c. FINITE c /\ CARD c <= CARD b /\
                span c = span b /\ pairwise orthogonal c`,
  REWRITE_TAC[pairwise; orthogonal] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [EXISTS_TAC `{}:real^N->bool` THEN
    REWRITE_TAC[FINITE_RULES; NOT_IN_EMPTY; LE_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC)
        STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(a - vsum c (\x. ((x dot a) / (x dot x)) % x):real^N)
              INSERT c` THEN
  ASM_SIMP_TAC[FINITE_RULES; CARD_CLAUSES] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[EXTENSION; SPAN_BREAKDOWN_EQ] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN GEN_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN
    REWRITE_TAC[VECTOR_ARITH `a - (x - y):real^N = y + (a - x)`] THEN
    MATCH_MP_TAC SPAN_ADD_EQ THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC SPAN_VSUM THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    ASM_SIMP_TAC[SPAN_SUPERSET];
    REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM SUBST_ALL_TAC;
      FIRST_X_ASSUM SUBST_ALL_TAC;
      ASM_MESON_TAC[]] THEN
    REWRITE_TAC[DOT_LSUB; DOT_RSUB; REAL_SUB_0] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
    ASM_SIMP_TAC[VSUM_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
    REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
    MATCH_MP_TAC(REAL_ARITH `s = &0 /\ a = b ==> b = a + s`) THEN
    ASM_SIMP_TAC[DOT_LSUM; DOT_RSUM; FINITE_DELETE] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC SUM_EQ_0 THEN
       ASM_SIMP_TAC[DOT_LMUL; DOT_RMUL; IN_DELETE;
                    REAL_MUL_RZERO; REAL_MUL_LZERO];
       W(MP_TAC o PART_MATCH (lhand o rand) REAL_DIV_RMUL o lhand o snd) THEN
       REWRITE_TAC[DOT_SYM] THEN
       MATCH_MP_TAC(TAUT `(p ==> q) ==> (~p ==> q) ==> q`) THEN
       SIMP_TAC[] THEN SIMP_TAC[DOT_EQ_0; DOT_RZERO; DOT_LZERO] THEN
       REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]])]);;

let ORTHOGONAL_BASIS_EXISTS = prove
 (`!v:real^N->bool.
        ?b. independent b /\
            b SUBSET span v /\
            v SUBSET span b /\
            b HAS_SIZE dim v /\
            pairwise orthogonal b`,
  GEN_TAC THEN MP_TAC(ISPEC `v:real^N->bool` BASIS_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `b:real^N->bool` BASIS_ORTHOGONAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CARD_LE_DIM_SPANNING THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `span(v):real^N->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SPAN_SPAN; SPAN_MONO];
      ASM_MESON_TAC[LE_TRANS; HAS_SIZE; DIM_SPAN]];
    ASM_MESON_TAC[SUBSET_TRANS; SPAN_INC; SPAN_SPAN; SPAN_MONO];
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_REWRITE_TAC[HAS_SIZE; GSYM LE_ANTISYM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[LE_TRANS]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SPAN_SPAN; SPAN_MONO; SUBSET_TRANS; SPAN_INC]]);;

let SPAN_EQ = prove
 (`!s t. span s = span t <=> s SUBSET span t /\ t SUBSET span s`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  MESON_TAC[SUBSET_TRANS; SPAN_SPAN; SPAN_MONO; SPAN_INC]);;

let SPAN_EQ_INSERT = prove
 (`!s x. span(x INSERT s) = span s <=> x IN span s`,
  REWRITE_TAC[SPAN_EQ; INSERT_SUBSET] THEN
  MESON_TAC[SPAN_INC; SUBSET; SET_RULE `s SUBSET (x INSERT s)`]);;

let SPAN_SPECIAL_SCALE = prove
 (`!s a x:real^N.
     span((a % x) INSERT s) = if a = &0 then span s else span(x INSERT s)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; SPAN_INSERT_0] THEN
  REWRITE_TAC[SPAN_EQ; SUBSET; FORALL_IN_INSERT] THEN
  SIMP_TAC[SPAN_MUL; SPAN_SUPERSET; IN_INSERT] THEN
  REWRITE_TAC[SPAN_BREAKDOWN_EQ] THEN EXISTS_TAC `inv a:real` THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
  REWRITE_TAC[SPAN_0; VECTOR_SUB_REFL]);;

(* ------------------------------------------------------------------------- *)
(* We can extend a linear basis-basis injection to the whole set.            *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INDEP_IMAGE_LEMMA = prove
 (`!f b. linear(f:real^M->real^N) /\
         FINITE b /\
         independent (IMAGE f b) /\
         (!x y. x IN b /\ y IN b /\ (f x = f y) ==> (x = y))
         ==> !x. x IN span b ==> (f(x) = vec 0) ==> (x = vec 0)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [IMP_IMP] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL [SIMP_TAC[IN_SING; SPAN_EMPTY]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M->bool`] THEN STRIP_TAC THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[INDEPENDENT_MONO; IMAGE_CLAUSES; SUBSET; IN_INSERT];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^M`; `(a:real^M) INSERT b`; `x:real^M`]
    SPAN_BREAKDOWN) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN
  SIMP_TAC[ASSUME `~((a:real^M) IN b)`; SET_RULE
    `~(a IN b) ==> ((a INSERT b) DELETE a = b)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N)(x - k % a) IN span(IMAGE f b)` MP_TAC THENL
   [ASM_MESON_TAC[SPAN_LINEAR_IMAGE; IN_IMAGE]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB th]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `vec 0 - k % x = (--k) % x`] THEN
  ASM_CASES_TAC `k = &0` THENL
   [ASM_MESON_TAC[VECTOR_ARITH `x - &0 % y = x`]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `--inv(k)` o MATCH_MP SPAN_MUL) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
  SIMP_TAC[REAL_NEGNEG; REAL_MUL_LINV; ASSUME `~(k = &0)`] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [independent]) THEN
  REWRITE_TAC[dependent; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) a`) THEN
  SUBGOAL_THEN
   `IMAGE (f:real^M->real^N) (a INSERT b) DELETE f a =
    IMAGE f ((a INSERT b) DELETE a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_INSERT] THEN
    ASM_MESON_TAC[IN_INSERT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DELETE_INSERT] THEN
  SIMP_TAC[SET_RULE `~(a IN b) ==> (b DELETE a = b)`;
           ASSUME `~(a:real^M IN b)`] THEN
  SIMP_TAC[IMAGE_CLAUSES; IN_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* We can extend a linear mapping from basis.                                *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INDEPENDENT_EXTEND_LEMMA = prove
 (`!f b. FINITE b
         ==> independent b
             ==> ?g:real^M->real^N.
                        (!x y. x IN span b /\ y IN span b
                                ==> (g(x + y) = g(x) + g(y))) /\
                        (!x c. x IN span b ==> (g(c % x) = c % g(x))) /\
                        (!x. x IN b ==> (g x = f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; INDEPENDENT_INSERT] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `(\x. vec 0):real^M->real^N` THEN
    SIMP_TAC[SPAN_EMPTY] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `h = \z:real^M. @k. (z - k % a) IN span b` THEN
  SUBGOAL_THEN `!z:real^M. z IN span(a INSERT b)
                    ==> (z - h(z) % a) IN span(b) /\
                        !k. (z - k % a) IN span(b) ==> (k = h(z))`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [EXPAND_TAC "h" THEN CONV_TAC SELECT_CONV THEN
      ASM_MESON_TAC[SPAN_BREAKDOWN_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP SPAN_SUB) THEN
    REWRITE_TAC[VECTOR_ARITH `(z - a % v) - (z - b % v) = (b - a) % v`] THEN
    ASM_CASES_TAC `k = (h:real^M->real) z` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(k - (h:real^M->real) z)` o
               MATCH_MP SPAN_MUL) THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_ASSOC; REAL_SUB_0] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  GEN_REWRITE_TAC LAND_CONV [FORALL_AND_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `\z:real^M. h(z) % (f:real^M->real^N)(a) + g(z - h(z) % a)` THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^M->real)(x + y) = h(x) + h(y)` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[VECTOR_ARITH
       `(x + y) - (k + l) % a = (x - k % a) + (y - l % a)`] THEN
      CONJ_TAC THEN MATCH_MP_TAC SPAN_ADD THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
       `(x + y) - (k + l) % a = (x - k % a) + (y - l % a)`] THEN
    ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^M`; `c:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^M->real)(c % x) = c * h(x)` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[VECTOR_ARITH
       `c % x - (c * k) % a = c % (x - k % a)`] THEN
      CONJ_TAC THEN MATCH_MP_TAC SPAN_MUL THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
       `c % x - (c * k) % a = c % (x - k % a)`] THEN
    ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
   [SUBGOAL_THEN `&1 = h(a:real^M)` (SUBST1_TAC o SYM) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `a - &1 % a = vec 0`; SPAN_0] THENL
     [ASM_MESON_TAC[SPAN_SUPERSET; SUBSET; IN_INSERT]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^M`; `vec 0:real^M`]) THEN
    REWRITE_TAC[SPAN_0; VECTOR_ADD_LID] THEN
    REWRITE_TAC[VECTOR_ARITH `(a = a + a) <=> (a = vec 0)`] THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 = h(x:real^M)` (SUBST1_TAC o SYM) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LID; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
  ASM_MESON_TAC[SUBSET; IN_INSERT; SPAN_SUPERSET]);;

let LINEAR_INDEPENDENT_EXTEND = prove
 (`!f b. independent b
         ==> ?g:real^M->real^N. linear g /\ (!x. x IN b ==> (g x = f x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^M->bool`; `(:real^M)`]
           MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; UNIV_SUBSET] THEN
  REWRITE_TAC[EXTENSION; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `c:real^M->bool`]
    LINEAR_INDEPENDENT_EXTEND_LEMMA) THEN
  ASM_SIMP_TAC[INDEPENDENT_BOUND; linear] THEN
  ASM_MESON_TAC[SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Linear functions are equal on a subspace if they are on a spanning set.   *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_KERNEL = prove
 (`!f. linear f ==> subspace {x | f(x) = vec 0}`,
  REWRITE_TAC[subspace; IN_ELIM_THM] THEN
  SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; VECTOR_ADD_LID; VECTOR_MUL_RZERO] THEN
  MESON_TAC[LINEAR_0]);;

let LINEAR_EQ_0_SPAN = prove
 (`!f:real^M->real^N b.
        linear f /\ (!x. x IN b ==> f(x) = vec 0)
        ==> !x. x IN span(b) ==> f(x) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
  MATCH_MP_TAC SPAN_INDUCT THEN ASM_REWRITE_TAC[IN] THEN
  MP_TAC(ISPEC `f:real^M->real^N` SUBSPACE_KERNEL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM]);;

let LINEAR_EQ_0 = prove
 (`!f b s. linear f /\ s SUBSET (span b) /\ (!x. x IN b ==> f(x) = vec 0)
           ==> !x. x IN s ==> f(x) = vec 0`,
  MESON_TAC[LINEAR_EQ_0_SPAN; SUBSET]);;

let LINEAR_EQ = prove
 (`!f g b s. linear f /\ linear g /\ s SUBSET (span b) /\
             (!x. x IN b ==> f(x) = g(x))
              ==> !x. x IN s ==> f(x) = g(x)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  STRIP_TAC THEN MATCH_MP_TAC LINEAR_EQ_0 THEN
  ASM_MESON_TAC[LINEAR_COMPOSE_SUB]);;

let LINEAR_EQ_STDBASIS = prove
 (`!f:real^M->real^N g.
        linear f /\ linear g /\
        (!i. 1 <= i /\ i <= dimindex(:M)
             ==> f(basis i) = g(basis i))
        ==> f = g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN UNIV ==> (f:real^M->real^N) x = g x`
   (fun th -> MP_TAC th THEN REWRITE_TAC[FUN_EQ_THM; IN_UNIV]) THEN
  MATCH_MP_TAC LINEAR_EQ THEN
  EXISTS_TAC `{basis i :real^M | 1 <= i /\ i <= dimindex(:M)}` THEN
  ASM_REWRITE_TAC[SPAN_STDBASIS; SUBSET_REFL; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let SUBSPACE_LINEAR_FIXED_POINTS = prove
 (`!f:real^N->real^N. linear f ==> subspace {x | f(x) = x}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC SUBSPACE_KERNEL THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE_SUB; LINEAR_ID]);;

(* ------------------------------------------------------------------------- *)
(* Similar results for bilinear functions.                                   *)
(* ------------------------------------------------------------------------- *)

let BILINEAR_EQ = prove
 (`!f:real^M->real^N->real^P g b c s.
        bilinear f /\ bilinear g /\
        s SUBSET (span b) /\ t SUBSET (span c) /\
        (!x y. x IN b /\ y IN c ==> f x y = g x y)
         ==> !x y. x IN s /\ y IN t ==> f x y = g x y`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
    `!x:real^M. x IN span b
                ==> !y:real^N. y IN span c ==> (f x y :real^P = g x y)`
    (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
  MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC[subspace; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC;
    ASM_SIMP_TAC[BILINEAR_LADD; BILINEAR_LMUL] THEN
    ASM_MESON_TAC[BILINEAR_LZERO]] THEN
  MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC[subspace; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[BILINEAR_RADD; BILINEAR_RMUL] THEN
  ASM_MESON_TAC[BILINEAR_RZERO]);;

let BILINEAR_EQ_STDBASIS = prove
 (`!f:real^M->real^N->real^P g.
        bilinear f /\ bilinear g /\
        (!i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N)
             ==> f (basis i) (basis j) = g (basis i) (basis j))
        ==> f = g`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `!x y. x IN UNIV /\ y IN UNIV ==> (f:real^M->real^N->real^P) x y = g x y`
   (fun th -> MP_TAC th THEN REWRITE_TAC[FUN_EQ_THM; IN_UNIV]) THEN
  MATCH_MP_TAC BILINEAR_EQ THEN
  EXISTS_TAC `{basis i :real^M | 1 <= i /\ i <= dimindex(:M)}` THEN
  EXISTS_TAC `{basis i :real^N | 1 <= i /\ i <= dimindex(:N)}` THEN
  ASM_REWRITE_TAC[SPAN_STDBASIS; SUBSET_REFL; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Detailed theorems about left and right invertibility in general case.     *)
(* ------------------------------------------------------------------------- *)

let LEFT_INVERTIBLE_TRANSP = prove
 (`!A:real^N^M.
    (?B:real^N^M. B ** transp A = mat 1) <=> (?B:real^M^N. A ** B = mat 1)`,
  MESON_TAC[MATRIX_TRANSP_MUL; TRANSP_MAT; TRANSP_TRANSP]);;

let RIGHT_INVERTIBLE_TRANSP = prove
 (`!A:real^N^M.
    (?B:real^N^M. transp A ** B = mat 1) <=> (?B:real^M^N. B ** A = mat 1)`,
  MESON_TAC[MATRIX_TRANSP_MUL; TRANSP_MAT; TRANSP_TRANSP]);;

let INVERTIBLE_TRANSP = prove
 (`!A:real^N^M. invertible(transp A) <=> invertible A`,
  GEN_TAC THEN REWRITE_TAC[invertible] THEN
  GEN_REWRITE_TAC LAND_CONV [MESON[TRANSP_TRANSP]
    `(?A:real^M^N. P A) <=> (?A:real^N^M. P(transp A))`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM TRANSP_MAT] THEN
  REWRITE_TAC[GSYM MATRIX_TRANSP_MUL; TRANSP_EQ] THEN MESON_TAC[]);;

let LINEAR_INJECTIVE_LEFT_INVERSE = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ?g. linear g /\ g o f = I`,
  REWRITE_TAC[INJECTIVE_LEFT_INVERSE] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `?h. linear(h:real^N->real^M) /\
        !x. x IN IMAGE (f:real^M->real^N)
               {basis i | 1 <= i /\ i <= dimindex(:M)} ==> h x = g x`
  MP_TAC THENL
   [MATCH_MP_TAC LINEAR_INDEPENDENT_EXTEND THEN
    MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE THEN
    ASM_MESON_TAC[INJECTIVE_LEFT_INVERSE; INDEPENDENT_STDBASIS];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^N->real^M` THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN
    ASM_SIMP_TAC[I_DEF; LINEAR_COMPOSE; LINEAR_ID; o_THM] THEN
    ASM_MESON_TAC[]]);;

let LINEAR_SURJECTIVE_RIGHT_INVERSE = prove
 (`!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y) ==> ?g. linear g /\ f o g = I`,
  REWRITE_TAC[SURJECTIVE_RIGHT_INVERSE] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `?h. linear(h:real^N->real^M) /\
        !x. x IN {basis i | 1 <= i /\ i <= dimindex(:N)} ==> h x = g x`
  MP_TAC THENL
   [MATCH_MP_TAC LINEAR_INDEPENDENT_EXTEND THEN
    REWRITE_TAC[INDEPENDENT_STDBASIS];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^N->real^M` THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN
    ASM_SIMP_TAC[I_DEF; LINEAR_COMPOSE; LINEAR_ID; o_THM] THEN
    ASM_MESON_TAC[]]);;

let MATRIX_LEFT_INVERTIBLE_INJECTIVE = prove
 (`!A:real^N^M.
        (?B:real^M^N. B ** A = mat 1) <=>
        !x y:real^N. A ** x = A ** y ==> x = y`,
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^M. (B:real^M^N) ** x`) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    DISCH_TAC THEN MP_TAC(ISPEC
     `\x:real^N. (A:real^N^M) ** x` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; FUN_EQ_THM; I_THM; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `matrix(g):real^M^N` THEN
    REWRITE_TAC[MATRIX_EQ; MATRIX_VECTOR_MUL_LID] THEN
    ASM_MESON_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_WORKS]]);;

let MATRIX_LEFT_INVERTIBLE_KER = prove
 (`!A:real^N^M.
        (?B:real^M^N. B ** A = mat 1) <=> !x. A ** x = vec 0 ==> x = vec 0`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
  MATCH_MP_TAC LINEAR_INJECTIVE_0 THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let MATRIX_RIGHT_INVERTIBLE_SURJECTIVE = prove
 (`!A:real^N^M.
        (?B:real^M^N. A ** B = mat 1) <=> !y. ?x. A ** x = y`,
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN X_GEN_TAC `y:real^M` THEN
    EXISTS_TAC `(B:real^M^N) ** (y:real^M)` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    DISCH_TAC THEN MP_TAC(ISPEC
     `\x:real^N. (A:real^N^M) ** x` LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; FUN_EQ_THM; I_THM; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `matrix(g):real^M^N` THEN
    REWRITE_TAC[MATRIX_EQ; MATRIX_VECTOR_MUL_LID] THEN
    ASM_MESON_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_WORKS]]);;

let MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS = prove
 (`!A:real^N^M. (?B:real^M^N. B ** A = mat 1) <=>
                !c. vsum(1..dimindex(:N)) (\i. c(i) % column i A) = vec 0 ==>
                    !i. 1 <= i /\ i <= dimindex(:N) ==> c(i) = &0`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_KER; MATRIX_MUL_VSUM] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `c:num->real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(lambda i. c(i)):real^N`);
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\i. (x:real^N)$i`)] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; CART_EQ; VEC_COMPONENT]);;

let MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS = prove
 (`!A:real^N^M. (?B:real^M^N. A ** B = mat 1) <=>
                !c. vsum(1..dimindex(:M)) (\i. c(i) % row i A) = vec 0 ==>
                    !i. 1 <= i /\ i <= dimindex(:M) ==> c(i) = &0`,
  ONCE_REWRITE_TAC[GSYM LEFT_INVERTIBLE_TRANSP] THEN
  REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS] THEN
  SIMP_TAC[COLUMN_TRANSP]);;

let MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS = prove
 (`!A:real^N^M. (?B:real^M^N. A ** B = mat 1) <=> span(columns A) = (:real^M)`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_RIGHT_INVERTIBLE_SURJECTIVE] THEN
  REWRITE_TAC[MATRIX_MUL_VSUM; EXTENSION; IN_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^M` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC SPAN_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC(CONJUNCT1 SPAN_CLAUSES) THEN
    REWRITE_TAC[columns; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SPEC_TAC(`y:real^M`,`y:real^M`) THEN MATCH_MP_TAC SPAN_INDUCT_ALT THEN
  CONJ_TAC THENL
   [EXISTS_TAC `vec 0 :real^N` THEN
    SIMP_TAC[VEC_COMPONENT; VECTOR_MUL_LZERO; VSUM_0];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `y1:real^M`; `y2:real^M`] THEN
  REWRITE_TAC[columns; IN_ELIM_THM] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `x:real^N` (SUBST1_TAC o SYM))) THEN
  EXISTS_TAC `(lambda j. if j = i then c + (x:real^N)$i else x$j):real^N` THEN
  SUBGOAL_THEN `1..dimindex(:N) = i INSERT ((1..dimindex(:N)) DELETE i)`
  SUBST1_TAC THENL [ASM_MESON_TAC[INSERT_DELETE; IN_NUMSEG]; ALL_TAC] THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_DELETE; FINITE_NUMSEG; IN_DELETE] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_RDISTRIB; VECTOR_ADD_ASSOC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  SIMP_TAC[FINITE_DELETE; IN_DELETE; FINITE_NUMSEG; LAMBDA_BETA; IN_NUMSEG]);;

let MATRIX_LEFT_INVERTIBLE_SPAN_ROWS = prove
 (`!A:real^N^M. (?B:real^M^N. B ** A = mat 1) <=> span(rows A) = (:real^N)`,
  MESON_TAC[RIGHT_INVERTIBLE_TRANSP; COLUMNS_TRANSP;
            MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS]);;

(* ------------------------------------------------------------------------- *)
(* An injective map real^N->real^N is also surjective.                       *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INJECTIVE_IMP_SURJECTIVE = prove
 (`!f:real^N->real^N.
        linear f /\ (!x y. (f(x) = f(y)) ==> (x = y))
        ==> !y. ?x. f(x) = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:real^N)` BASIS_EXISTS) THEN
  REWRITE_TAC[SUBSET_UNIV; HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIV SUBSET span(IMAGE (f:real^N->real^N) b)` MP_TAC THENL
   [MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
    ASM_MESON_TAC[INDEPENDENT_INJECTIVE_IMAGE; LE_REFL;
                  SUBSET_UNIV; CARD_IMAGE_INJ];
    ASM_SIMP_TAC[SPAN_LINEAR_IMAGE] THEN
    ASM_MESON_TAC[SUBSET; IN_IMAGE; IN_UNIV]]);;

(* ------------------------------------------------------------------------- *)
(* And vice versa.                                                           *)
(* ------------------------------------------------------------------------- *)

let LINEAR_SURJECTIVE_IMP_INJECTIVE = prove
 (`!f:real^N->real^N.
        linear f /\ (!y. ?x. f(x) = y)
        ==> !x y. (f(x) = f(y)) ==> (x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(:real^N)` BASIS_EXISTS) THEN
  REWRITE_TAC[SUBSET_UNIV; HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x. x IN span b ==> (f:real^N->real^N) x = vec 0 ==> x = vec 0`
   (fun th -> ASM_MESON_TAC[th; LINEAR_INJECTIVE_0; SUBSET; IN_UNIV]) THEN
  MATCH_MP_TAC LINEAR_INDEP_IMAGE_LEMMA THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_LE_DIM_SPANNING THEN
    EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; FINITE_IMAGE; SPAN_LINEAR_IMAGE] THEN
    REWRITE_TAC[SUBSET; IN_UNIV; IN_IMAGE] THEN
    ASM_MESON_TAC[CARD_IMAGE_LE; SUBSET; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `dim(:real^N) <= CARD(IMAGE (f:real^N->real^N) b)`
  MP_TAC THENL
   [MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
    ASM_SIMP_TAC[SUBSET_UNIV; FINITE_IMAGE] THEN
    ASM_SIMP_TAC[SPAN_LINEAR_IMAGE] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^N->real^N) UNIV` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET] THEN
    ASM_REWRITE_TAC[SUBSET; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ISPEC `f:real^N->real^N` o
                MATCH_MP CARD_IMAGE_LE) THEN
  ASM_REWRITE_TAC[IMP_IMP; LE_ANTISYM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`b:real^N->bool`; `IMAGE (f:real^N->real^N) b`; `f:real^N->real^N`]
   SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; INDEPENDENT_BOUND; SUBSET_REFL] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN MESON_TAC[]);;

let LINEAR_SURJECTIVE_IFF_INJECTIVE = prove
 (`!f:real^N->real^N.
      linear f ==> ((!y. ?x. f x = y) <=> (!x y. f x = f y ==> x = y))`,
  MESON_TAC[LINEAR_INJECTIVE_IMP_SURJECTIVE;
            LINEAR_SURJECTIVE_IMP_INJECTIVE]);;

(* ------------------------------------------------------------------------- *)
(* Hence either is enough for isomorphism.                                   *)
(* ------------------------------------------------------------------------- *)

let LEFT_RIGHT_INVERSE_EQ = prove
 (`!f:A->A g h. f o g = I /\ g o h = I ==> f = h`,
  MESON_TAC[o_ASSOC; I_O_ID]);;

let ISOMORPHISM_EXPAND = prove
 (`!f g. f o g = I /\ g o f = I <=> (!x. f(g x) = x) /\ (!x. g(f x) = x)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM]);;

let LINEAR_INJECTIVE_ISOMORPHISM = prove
 (`!f:real^N->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ?f'. linear f' /\ (!x. f'(f x) = x) /\ (!x. f(f' x) = x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM ISOMORPHISM_EXPAND] THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN MESON_TAC[LEFT_RIGHT_INVERSE_EQ]);;

let LINEAR_SURJECTIVE_ISOMORPHISM = prove
 (`!f:real^N->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> ?f'. linear f' /\ (!x. f'(f x) = x) /\ (!x. f(f' x) = x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM ISOMORPHISM_EXPAND] THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_SURJECTIVE_IMP_INJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN MESON_TAC[LEFT_RIGHT_INVERSE_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Left and right inverses are the same for R^N->R^N.                        *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INVERSE_LEFT = prove
 (`!f:real^N->real^N f'.
        linear f /\ linear f' ==> ((f o f' = I) <=> (f' o f = I))`,
  SUBGOAL_THEN
   `!f:real^N->real^N f'.
        linear f /\ linear f' /\ (f o f' = I) ==> (f' o f = I)`
   (fun th -> MESON_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_SURJECTIVE_ISOMORPHISM) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Moreover, a one-sided inverse is automatically linear.                    *)
(* ------------------------------------------------------------------------- *)

let LEFT_INVERSE_LINEAR = prove
 (`!f g:real^N->real^N. linear f /\ (g o f = I) ==> linear g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  STRIP_TAC THEN SUBGOAL_THEN
   `?h:real^N->real^N. linear h /\ (!x. h(f x) = x) /\ (!x. f(h x) = x)`
  CHOOSE_TAC THENL
   [MATCH_MP_TAC LINEAR_INJECTIVE_ISOMORPHISM THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `g:real^N->real^N = h` (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]]);;

let RIGHT_INVERSE_LINEAR = prove
 (`!f g:real^N->real^N. linear f /\ (f o g = I) ==> linear g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  STRIP_TAC THEN SUBGOAL_THEN
   `?h:real^N->real^N. linear h /\ (!x. h(f x) = x) /\ (!x. f(h x) = x)`
  CHOOSE_TAC THENL [ASM_MESON_TAC[LINEAR_SURJECTIVE_ISOMORPHISM]; ALL_TAC] THEN
  SUBGOAL_THEN `g:real^N->real^N = h` (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Without (ostensible) constraints on types, though dimensions must match.  *)
(* ------------------------------------------------------------------------- *)

let LEFT_RIGHT_INVERSE_LINEAR = prove
 (`!f g:real^M->real^N.
        linear f /\ g o f = I /\ f o g = I ==> linear g`,
  REWRITE_TAC[linear; FUN_EQ_THM; o_THM; I_THM] THEN MESON_TAC[]);;

let LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> ?g. linear g /\ (!x. g(f x) = x) /\ (!y. f(g y) = y)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BIJECTIVE_LEFT_RIGHT_INVERSE]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LEFT_RIGHT_INVERSE_LINEAR THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM]);;

(* ------------------------------------------------------------------------- *)
(* The same result in terms of square matrices.                              *)
(* ------------------------------------------------------------------------- *)

let MATRIX_LEFT_RIGHT_INVERSE = prove
 (`!A:real^N^N A':real^N^N. (A ** A' = mat 1) <=> (A' ** A = mat 1)`,
  SUBGOAL_THEN
    `!A:real^N^N A':real^N^N. (A ** A' = mat 1) ==> (A' ** A = mat 1)`
    (fun th -> MESON_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x:real^N. A:(real^N^N) ** x`
    LINEAR_SURJECTIVE_ISOMORPHISM) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:real^N` THEN EXISTS_TAC `(A':real^N^N) ** (x:real^N)` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^N->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `matrix (f':real^N->real^N) ** (A:real^N^N) = mat 1`
  MP_TAC THENL
   [ASM_SIMP_TAC[MATRIX_EQ; MATRIX_WORKS; GSYM MATRIX_VECTOR_MUL_ASSOC;
                 MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o AP_TERM `(\m:real^N^N. m ** (A':real^N^N))`) THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[MATRIX_MUL_RID; MATRIX_MUL_LID] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Invertibility of matrices and corresponding linear functions.             *)
(* ------------------------------------------------------------------------- *)

let MATRIX_LEFT_INVERTIBLE = prove
 (`!f:real^M->real^N.
    linear f ==> ((?B:real^N^M. B ** matrix f = mat 1) <=>
                  (?g. linear g /\ g o f = I))`,
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `\y:real^N. (B:real^N^M) ** y` THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
                [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; MATRIX_VECTOR_MUL_ASSOC;
                    MATRIX_VECTOR_MUL_LID];
    EXISTS_TAC `matrix(g:real^N->real^M)` THEN
    ASM_SIMP_TAC[GSYM MATRIX_COMPOSE; MATRIX_I]]);;

let MATRIX_RIGHT_INVERTIBLE = prove
 (`!f:real^M->real^N.
    linear f ==> ((?B:real^N^M. matrix f ** B = mat 1) <=>
                  (?g. linear g /\ f o g = I))`,
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `\y:real^N. (B:real^N^M) ** y` THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
                [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; MATRIX_VECTOR_MUL_ASSOC;
                    MATRIX_VECTOR_MUL_LID];
    EXISTS_TAC `matrix(g:real^N->real^M)` THEN
    ASM_SIMP_TAC[GSYM MATRIX_COMPOSE; MATRIX_I]]);;

let INVERTIBLE_LEFT_INVERSE = prove
 (`!A:real^N^N. invertible(A) <=> ?B:real^N^N. B ** A = mat 1`,
  MESON_TAC[invertible; MATRIX_LEFT_RIGHT_INVERSE]);;

let INVERTIBLE_RIGHT_INVERSE = prove
 (`!A:real^N^N. invertible(A) <=> ?B:real^N^N. A ** B = mat 1`,
  MESON_TAC[invertible; MATRIX_LEFT_RIGHT_INVERSE]);;

let MATRIX_INVERTIBLE = prove
 (`!f:real^N->real^N.
        linear f
        ==> (invertible(matrix f) <=>
             ?g. linear g /\ f o g = I /\ g o f = I)`,
  SIMP_TAC[INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE] THEN
  MESON_TAC[LINEAR_INVERSE_LEFT]);;

let MATRIX_INV_UNIQUE_LEFT = prove
 (`!A:real^N^N B. A ** B = mat 1 ==> matrix_inv B = A`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
  ASM_MESON_TAC[MATRIX_LEFT_RIGHT_INVERSE]);;

let MATRIX_INV_UNIQUE_RIGHT = prove
 (`!A:real^N^N B. A ** B = mat 1 ==> matrix_inv A = B`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
  ASM_MESON_TAC[MATRIX_LEFT_RIGHT_INVERSE]);;

(* ------------------------------------------------------------------------- *)
(* Left-invertible linear transformation has a lower bound.                  *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INVERTIBLE_BOUNDED_BELOW_POS = prove
 (`!f:real^M->real^N g.
        linear f /\ linear g /\ (g o f = I)
        ==> ?B. &0 < B /\ !x. B * norm(x) <= norm(f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `g:real^N->real^M` LINEAR_BOUNDED_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inv B:real` THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  X_GEN_TAC `x:real^M` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(B) * norm(((g:real^N->real^M) o (f:real^M->real^N)) x)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[I_THM; REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `inv B * x = x / B`] THEN
  ASM_SIMP_TAC[o_THM; REAL_LE_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]);;

let LINEAR_INVERTIBLE_BOUNDED_BELOW = prove
 (`!f:real^M->real^N g.
        linear f /\ linear g /\ (g o f = I)
        ==> ?B. !x. B * norm(x) <= norm(f x)`,
  MESON_TAC[LINEAR_INVERTIBLE_BOUNDED_BELOW_POS]);;

let LINEAR_INJECTIVE_BOUNDED_BELOW_POS = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ?B. &0 < B /\ !x. norm(x) * B <= norm(f x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC LINEAR_INVERTIBLE_BOUNDED_BELOW_POS THEN
  ASM_MESON_TAC[LINEAR_INJECTIVE_LEFT_INVERSE]);;

(* ------------------------------------------------------------------------- *)
(* Preservation of dimension by injective map.                               *)
(* ------------------------------------------------------------------------- *)

let DIM_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) ==> dim(IMAGE f s) = dim s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIM_LINEAR_IMAGE_LE]; ALL_TAC] THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `dim(IMAGE (g:real^N->real^M) (IMAGE (f:real^M->real^N) s))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID; LE_REFL];
    MATCH_MP_TAC DIM_LINEAR_IMAGE_LE THEN ASM_REWRITE_TAC[]]);;

let LINEAR_INJECTIVE_DIMINDEX_LE = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> dimindex(:M) <= dimindex(:N)`,
  REWRITE_TAC[GSYM DIM_UNIV] THEN REPEAT GEN_TAC THEN DISCH_THEN
   (SUBST1_TAC o SYM o SPEC `(:real^M)` o
    MATCH_MP DIM_INJECTIVE_LINEAR_IMAGE) THEN
  MATCH_MP_TAC DIM_SUBSET THEN REWRITE_TAC[SUBSET_UNIV]);;

let LINEAR_SURJECTIVE_DIMINDEX_LE = prove
 (`!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> dimindex(:N) <= dimindex(:M)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM
   (MP_TAC o MATCH_MP LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real^N->real^M` THEN STRIP_TAC THEN
  MATCH_MP_TAC LINEAR_INJECTIVE_DIMINDEX_LE THEN
  EXISTS_TAC `g:real^N->real^M` THEN ASM_MESON_TAC[]);;

let LINEAR_BIJECTIVE_DIMINDEX_EQ = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> dimindex(:M) = dimindex(:N)`,
  REWRITE_TAC[GSYM LE_ANTISYM] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC LINEAR_INJECTIVE_DIMINDEX_LE;
    MATCH_MP_TAC LINEAR_SURJECTIVE_DIMINDEX_LE] THEN
  EXISTS_TAC `f:real^M->real^N` THEN ASM_REWRITE_TAC[]);;

let INVERTIBLE_IMP_SQUARE_MATRIX = prove
 (`!A:real^N^M. invertible A ==> dimindex(:M) = dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[invertible; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `B:real^M^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC LINEAR_BIJECTIVE_DIMINDEX_EQ THEN
  EXISTS_TAC `\x:real^M. (B:real^M^N) ** x` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR;
                  GSYM MATRIX_LEFT_INVERTIBLE_INJECTIVE;
                  GSYM MATRIX_RIGHT_INVERTIBLE_SURJECTIVE] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Considering an n-element vector as an n-by-1 or 1-by-n matrix.            *)
(* ------------------------------------------------------------------------- *)

let rowvector = new_definition
 `(rowvector:real^N->real^N^1) v = lambda i j. v$j`;;

let columnvector = new_definition
 `(columnvector:real^N->real^1^N) v = lambda i j. v$i`;;

let TRANSP_COLUMNVECTOR = prove
 (`!v. transp(columnvector v) = rowvector v`,
  SIMP_TAC[transp; columnvector; rowvector; CART_EQ; LAMBDA_BETA]);;

let TRANSP_ROWVECTOR = prove
 (`!v. transp(rowvector v) = columnvector v`,
  SIMP_TAC[transp; columnvector; rowvector; CART_EQ; LAMBDA_BETA]);;

let DOT_ROWVECTOR_COLUMNVECTOR = prove
 (`!A:real^N^M v:real^N. columnvector(A ** v) = A ** columnvector v`,
  REWRITE_TAC[rowvector; columnvector; matrix_mul; matrix_vector_mul] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA]);;

let DOT_MATRIX_PRODUCT = prove
 (`!x y:real^N. x dot y = (rowvector x ** columnvector y)$1$1`,
  REWRITE_TAC[matrix_mul; columnvector; rowvector; dot] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_1; LE_REFL]);;

let DOT_MATRIX_VECTOR_MUL = prove
 (`!A:real^N^N B:real^N^N x:real^N y:real^N.
      (A ** x) dot (B ** y) =
      ((rowvector x) ** (transp(A) ** B) ** (columnvector y))$1$1`,
  REWRITE_TAC[DOT_MATRIX_PRODUCT] THEN
  ONCE_REWRITE_TAC[GSYM TRANSP_COLUMNVECTOR] THEN
  REWRITE_TAC[DOT_ROWVECTOR_COLUMNVECTOR; MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Rank of a matrix. Equivalence of row and column rank is taken from        *)
(* George Mackiw's paper, Mathematics Magazine 1995, p. 285.                 *)
(* ------------------------------------------------------------------------- *)

let MATRIX_VECTOR_MUL_IN_COLUMNSPACE = prove
 (`!A:real^M^N x:real^M. (A ** x) IN span(columns A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MATRIX_VECTOR_COLUMN; columns] THEN
  MATCH_MP_TAC SPAN_VSUM THEN
  SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; transp; LAMBDA_BETA] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
  MATCH_MP_TAC SPAN_SUPERSET THEN
  REWRITE_TAC[IN_ELIM_THM; column] THEN EXISTS_TAC `k:num` THEN
  ASM_REWRITE_TAC[]);;

let SUBSPACE_ORTHOGONAL_TO_VECTOR = prove
 (`!x. subspace {y | orthogonal x y}`,
  SIMP_TAC[subspace; IN_ELIM_THM; ORTHOGONAL_CLAUSES]);;

let SUBSPACE_ORTHOGONAL_TO_VECTORS = prove
 (`!s. subspace {y | (!x. x IN s ==> orthogonal x y)}`,
  SIMP_TAC[subspace; IN_ELIM_THM; ORTHOGONAL_CLAUSES]);;

let ORTHOGONAL_TO_SPAN = prove
 (`!s x. (!y. y IN s ==> orthogonal x y)
         ==> !y. y IN span(s) ==> orthogonal x y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPAN_INDUCT THEN
  REWRITE_TAC[SET_RULE `(\y. orthogonal x y) = {y | orthogonal x y}`] THEN
  ASM_SIMP_TAC[SUBSPACE_ORTHOGONAL_TO_VECTOR; IN_ELIM_THM]);;

let ORTHOGONAL_TO_SPAN_EQ = prove
 (`!s x. (!y. y IN span(s) ==> orthogonal x y) <=>
         (!y. y IN s ==> orthogonal x y)`,
  MESON_TAC[SPAN_SUPERSET; ORTHOGONAL_TO_SPAN]);;

let ORTHOGONAL_TO_SPANS_EQ = prove
 (`!s t. (!x y. x IN span(s) /\ y IN span(t) ==> orthogonal x y) <=>
         (!x y. x IN s /\ y IN t ==> orthogonal x y)`,
  MESON_TAC[ORTHOGONAL_TO_SPAN_EQ; ORTHOGONAL_SYM]);;

let ORTHOGONAL_NULLSPACE_ROWSPACE = prove
 (`!A:real^M^N x y:real^M.
        A ** x = vec 0 /\ y IN span(rows A) ==> orthogonal x y`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPAN_INDUCT THEN
  REWRITE_TAC[SET_RULE `(\y. orthogonal x y) = {y | orthogonal x y}`] THEN
  REWRITE_TAC[SUBSPACE_ORTHOGONAL_TO_VECTOR; rows; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\y:real^N. y$k`) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; VEC_COMPONENT; row; dot;
               orthogonal; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let NULLSPACE_INTER_ROWSPACE = prove
 (`!A:real^M^N x:real^M. A ** x = vec 0 /\ x IN span(rows A) <=> x = vec 0`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[ORTHOGONAL_NULLSPACE_ROWSPACE; ORTHOGONAL_REFL];
    SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; SPAN_0]]);;

let MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE = prove
 (`!A:real^M^N x y:real^M.
        x IN span(rows A) /\ y IN span(rows A) /\ A ** x = A ** y ==> x = y`,
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM NULLSPACE_INTER_ROWSPACE] THEN
  ASM_SIMP_TAC[SPAN_SUB]);;

let DIM_ROWS_LE_DIM_COLUMNS = prove
 (`!A:real^M^N. dim(rows A) <= dim(columns A)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  X_CHOOSE_THEN `b:real^M->bool` STRIP_ASSUME_TAC
   (ISPEC `span(rows(A:real^M^N))` BASIS_EXISTS) THEN
  SUBGOAL_THEN `FINITE(IMAGE (\x:real^M. (A:real^M^N) ** x) b) /\
                CARD (IMAGE (\x:real^M. (A:real^M^N) ** x) b) <=
                dim(span(columns A))`
  MP_TAC THENL
   [MATCH_MP_TAC INDEPENDENT_CARD_LE_DIM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MATRIX_VECTOR_MUL_IN_COLUMNSPACE] THEN
    MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE_GEN THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    SUBGOAL_THEN `span(b) = span(rows(A:real^M^N))` SUBST1_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE]] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM SPAN_SPAN] THEN
    ASM_SIMP_TAC[SPAN_MONO];
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM) o
      GEN_REWRITE_RULE I [HAS_SIZE]) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC
     (ISPEC `A:real^M^N` MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE) THEN
    ASM SET_TAC[]]);;

let rank = new_definition
 `rank(A:real^M^N) = dim(columns A)`;;

let RANK_ROW = prove
 (`!A:real^M^N. rank(A) = dim(rows A)`,
  GEN_TAC THEN REWRITE_TAC[rank] THEN
  MP_TAC(ISPEC `A:real^M^N` DIM_ROWS_LE_DIM_COLUMNS) THEN
  MP_TAC(ISPEC `transp(A:real^M^N)` DIM_ROWS_LE_DIM_COLUMNS) THEN
  REWRITE_TAC[ROWS_TRANSP; COLUMNS_TRANSP] THEN ARITH_TAC);;

let RANK_TRANSP = prove
 (`!A:real^M^N. rank(transp A) = rank A`,
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [RANK_ROW] THEN
  REWRITE_TAC[rank; COLUMNS_TRANSP]);;

let MATRIX_VECTOR_MUL_BASIS = prove
 (`!A:real^M^N k. 1 <= k /\ k <= dimindex(:M)
                 ==> A ** (basis k) = column k A`,
  SIMP_TAC[CART_EQ; column; MATRIX_VECTOR_MUL_COMPONENT; DOT_BASIS;
           LAMBDA_BETA]);;

let COLUMNS_IMAGE_BASIS = prove
 (`!A:real^M^N.
     columns A = IMAGE (\x. A ** x) {basis i | 1 <= i /\ i <= dimindex(:M)}`,
  GEN_TAC THEN REWRITE_TAC[columns] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC(SET_RULE
    `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  SIMP_TAC[IN_ELIM_THM; MATRIX_VECTOR_MUL_BASIS]);;

let RANK_DIM_IM = prove
 (`!A:real^M^N. rank A = dim(IMAGE (\x. A ** x) (:real^M))`,
  GEN_TAC THEN REWRITE_TAC[rank] THEN
  MATCH_MP_TAC SPAN_EQ_DIM THEN REWRITE_TAC[COLUMNS_IMAGE_BASIS] THEN
  SIMP_TAC[SPAN_LINEAR_IMAGE; MATRIX_VECTOR_MUL_LINEAR] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM SPAN_SPAN] THEN
  REWRITE_TAC[SPAN_STDBASIS]);;

let DIM_EQ_SPAN = prove
 (`!s t:real^N->bool. s SUBSET t /\ dim t <= dim s ==> span s = span t`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC
   (ISPEC `span s:real^N->bool` BASIS_EXISTS) THEN
  MP_TAC(ISPECL [`span t:real^N->bool`; `b:real^N->bool`]
    CARD_GE_DIM_INDEPENDENT) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_REWRITE_TAC[DIM_SPAN] THEN
  ASM_MESON_TAC[SPAN_MONO; SPAN_SPAN; SUBSET_TRANS; SUBSET_ANTISYM]);;

let DIM_EQ_FULL = prove
 (`!s:real^N->bool. dim s = dimindex(:N) <=> span s = (:real^N)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN EQ_TAC THEN
  SIMP_TAC[DIM_UNIV] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SPAN_UNIV] THEN MATCH_MP_TAC DIM_EQ_SPAN THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; DIM_UNIV] THEN
  ASM_MESON_TAC[LE_REFL; DIM_SPAN]);;

let DIM_PSUBSET = prove
 (`!s t. (span s) PSUBSET (span t) ==> dim s < dim t`,
  ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  SIMP_TAC[PSUBSET; DIM_SUBSET; LT_LE] THEN
  MESON_TAC[EQ_IMP_LE; DIM_EQ_SPAN; SPAN_SPAN]);;

let RANK_BOUND = prove
 (`!A:real^M^N. rank(A) <= MIN (dimindex(:M)) (dimindex(:N))`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `x <= MIN a b <=> x <= a /\ x <= b`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[DIM_SUBSET_UNIV; RANK_ROW];
    REWRITE_TAC[DIM_SUBSET_UNIV; rank]]);;

let FULL_RANK_INJECTIVE = prove
 (`!A:real^M^N.
        rank A = dimindex(:M) <=>
        (!x y:real^M. A ** x = A ** y ==> x = y)`,
  REWRITE_TAC[GSYM MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
  REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_SPAN_ROWS] THEN
  REWRITE_TAC[RANK_ROW; DIM_EQ_FULL]);;

let FULL_RANK_SURJECTIVE = prove
 (`!A:real^M^N.
        rank A = dimindex(:N) <=> (!y:real^N. ?x:real^M. A ** x = y)`,
  REWRITE_TAC[GSYM MATRIX_RIGHT_INVERTIBLE_SURJECTIVE] THEN
  REWRITE_TAC[GSYM LEFT_INVERTIBLE_TRANSP] THEN
  REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
  REWRITE_TAC[GSYM FULL_RANK_INJECTIVE; RANK_TRANSP]);;

let RANK_I = prove
 (`rank(mat 1:real^N^N) = dimindex(:N)`,
  REWRITE_TAC[FULL_RANK_INJECTIVE; MATRIX_VECTOR_MUL_LID]);;

let MATRIX_FULL_LINEAR_EQUATIONS = prove
 (`!A:real^M^N b:real^N.
        rank A = dimindex(:N) ==> ?x. A ** x = b`,
  SIMP_TAC[FULL_RANK_SURJECTIVE]);;

let MATRIX_NONFULL_LINEAR_EQUATIONS_EQ = prove
 (`!A:real^M^N.
        (?x. ~(x = vec 0) /\ A ** x = vec 0) <=> ~(rank A = dimindex(:M))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FULL_RANK_INJECTIVE] THEN
  SIMP_TAC[LINEAR_INJECTIVE_0; MATRIX_VECTOR_MUL_LINEAR] THEN
  MESON_TAC[]);;

let MATRIX_NONFULL_LINEAR_EQUATIONS = prove
 (`!A:real^M^N.
        ~(rank A = dimindex(:M)) ==> ?x. ~(x = vec 0) /\ A ** x = vec 0`,
  REWRITE_TAC[MATRIX_NONFULL_LINEAR_EQUATIONS_EQ]);;

let MATRIX_TRIVIAL_LINEAR_EQUATIONS = prove
 (`!A:real^M^N.
        dimindex(:N) < dimindex(:M)
        ==> ?x. ~(x = vec 0) /\ A ** x = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_NONFULL_LINEAR_EQUATIONS THEN
  MATCH_MP_TAC(ARITH_RULE
   `!a. x <= MIN b a /\ a < b ==> ~(x = b)`) THEN
  EXISTS_TAC `dimindex(:N)` THEN ASM_REWRITE_TAC[RANK_BOUND]);;

let RANK_EQ_0 = prove
 (`!A:real^M^N. rank A = 0 <=> A = mat 0`,
  REWRITE_TAC[RANK_DIM_IM; DIM_EQ_0; SUBSET; FORALL_IN_IMAGE; IN_SING;
              IN_UNIV] THEN
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CART_EQ] THEN
  SIMP_TAC[CART_EQ; MATRIX_MUL_DOT; VEC_COMPONENT; LAMBDA_BETA; mat] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_DOT_EQ_0; COND_ID] THEN
  REWRITE_TAC[CART_EQ; VEC_COMPONENT]);;

let RANK_0 = prove
 (`rank(mat 0) = 0`,
  REWRITE_TAC[RANK_EQ_0]);;

let RANK_MUL_LE_RIGHT = prove
 (`!A:real^N^M B:real^P^N. rank(A ** B) <= rank(B)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `dim(IMAGE (\y. (A:real^N^M) ** y)
                        (IMAGE (\x. (B:real^P^N) ** x) (:real^P)))` THEN
  REWRITE_TAC[RANK_DIM_IM] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF; MATRIX_VECTOR_MUL_ASSOC; LE_REFL];
    MATCH_MP_TAC DIM_LINEAR_IMAGE_LE THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]]);;

let RANK_MUL_LE_LEFT = prove
 (`!A:real^N^M B:real^P^N. rank(A ** B) <= rank(A)`,
  ONCE_REWRITE_TAC[GSYM RANK_TRANSP] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[RANK_MUL_LE_RIGHT]);;

