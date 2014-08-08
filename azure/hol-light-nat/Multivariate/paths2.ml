open Hol_core
open Card
open Floor
open Vectors
open Determinants
open Topology
open Convex
include Paths1


(* ------------------------------------------------------------------------- *)
(* Every path between distinct points contains an arc, and hence             *)
(* that path connection is equivalent to arcwise connection, for distinct    *)
(* points. The proof is based on Whyburn's "Topological Analysis".           *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_MONOTONE_IMAGE_INTERVAL = prove
 (`!f:real^1->real^N.
       f continuous_on interval[vec 0,vec 1] /\
       (!y. connected {x | x IN interval[vec 0,vec 1] /\ f x = y}) /\
       ~(f(vec 1) = f(vec 0))
       ==> (IMAGE f (interval[vec 0,vec 1])) homeomorphic
           (interval[vec 0:real^1,vec 1])`,
  let closure_dyadic_rationals_in_convex_set_pos_1 = prove
   (`!s. convex s /\ ~(interior s = {}) /\ (!x. x IN s ==> &0 <= drop x)
         ==> closure(s INTER { lift(&m / &2 pow n) |
                               m IN (:num) /\ n IN (:num)}) =
             closure s`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `s:real^1->bool` CLOSURE_DYADIC_RATIONALS_IN_CONVEX_SET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN t ==> x IN u) /\ (!x. x IN u ==> x IN s ==> x IN t)
      ==> s INTER t = s INTER u`) THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; DIMINDEX_1; FORALL_1] THEN
    REWRITE_TAC[IN_ELIM_THM; EXISTS_LIFT; GSYM drop; LIFT_DROP] THEN
    REWRITE_TAC[REAL_ARITH `x / y:real = inv y * x`; LIFT_CMUL] THEN
    CONJ_TAC THENL [MESON_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^1`] THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(&2 pow n) % x:real^1`) THEN
    ASM_SIMP_TAC[DROP_CMUL; REAL_LE_MUL_EQ; REAL_LT_POW2; REAL_LT_INV_EQ] THEN
    ASM_MESON_TAC[INTEGER_POS; LIFT_DROP]) in
  let function_on_dyadic_rationals = prove
   (`!f:num->num->A.
          (!m n. f (2 * m) (n + 1) = f m n)
          ==> ?g. !m n. g(&m / &2 pow n) = f m n`,
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MP_TAC(ISPECL
     [`\(m,n). (f:num->num->A) m n`; `\(m,n). &m / &2 pow n`]
     FUNCTION_FACTORS_LEFT) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FUN_EQ_THM; o_THM] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    ONCE_REWRITE_TAC[MESON[]
      `(!a b c d. P a b c d) <=> (!b d a c. P a b c d)`] THEN
    MATCH_MP_TAC WLOG_LE THEN REPEAT CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    SIMP_TAC[REAL_FIELD `~(y = &0) /\ ~(y' = &0)
                         ==> (x / y = x' / y' <=> y' / y * x = x')`;
       REAL_POW_EQ_0; REAL_OF_NUM_EQ; REAL_DIV_POW2; ARITH_EQ] THEN
    SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    SIMP_TAC[ADD_SUB2; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ; REAL_OF_NUM_POW] THEN
    REWRITE_TAC[MESON[]
     `(!n n' d. n' = f d n ==> !m m'. g d m = m' ==> P m m' n d) <=>
      (!d m n. P m (g d m) n d)`] THEN
    INDUCT_TAC THEN SIMP_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; ADD1] THEN ASM_MESON_TAC[]) in
  let recursion_on_dyadic_rationals = prove
   (`!b:num->A l r.
          ?f. (!m. f(&m) = b m) /\
              (!m n. f(&(4 * m + 1) / &2 pow (n + 1)) =
                     l(f(&(2 * m + 1) / &2 pow n))) /\
              (!m n. f(&(4 * m + 3) / &2 pow (n + 1)) =
                     r(f(&(2 * m + 1) / &2 pow n)))`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `?f:num->num->A.
          (!m n. f (2 * m) (n + 1) = f m n) /\
          (!m. f m 0 = b m) /\
          (!m n. f (4 * m + 1) (n + 1) = l(f (2 * m + 1) n)) /\
          (!m n. f (4 * m + 3) (n + 1) = r(f (2 * m + 1) n))`
    MP_TAC THENL
     [MP_TAC(prove_recursive_functions_exist num_RECURSION
       `(!m. f m 0 = (b:num->A) m) /\
        (!m n. f m (SUC n) =
                  if EVEN m then f (m DIV 2) n
                  else if EVEN(m DIV 2)
                       then l(f ((m + 1) DIV 2) n)
                       else r(f (m DIV 2) n))`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `f:num->num->A` THEN STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD1]) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[EVEN_MULT; ARITH_EVEN; ARITH_RULE `(2 * m) DIV 2 = m`] THEN
      REWRITE_TAC[ARITH_RULE `(4 * m + 1) DIV 2 = 2 * m`;
                  ARITH_RULE `(4 * m + 3) DIV 2 = 2 * m + 1`;
                  ARITH_RULE `((4 * m + 1) + 1) DIV 2 = 2 * m + 1`;
                  ARITH_RULE `((4 * m + 3) + 1) DIV 2 = 2 * m + 2`] THEN
      REWRITE_TAC[EVEN_ADD; EVEN_MULT; EVEN; ARITH_EVEN; SND];
      DISCH_THEN(X_CHOOSE_THEN `f:num->num->A`
       (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP function_on_dyadic_rationals) THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_ARITH `x / &2 pow 0 = x`]) THEN
      ASM_REWRITE_TAC[]]) in
  let recursion_on_dyadic_rationals_1 = prove
   (`!b:A l r.
          ?f. (!m. f(&m / &2) = b) /\
              (!m n. 0 < n ==> f(&(4 * m + 1) / &2 pow (n + 1)) =
                               l(f(&(2 * m + 1) / &2 pow n))) /\
              (!m n. 0 < n ==> f(&(4 * m + 3) / &2 pow (n + 1)) =
                               r(f(&(2 * m + 1) / &2 pow n)))`,
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(\n. b):num->A`; `l:A->A`; `r:A->A`]
          recursion_on_dyadic_rationals) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\x. (f:real->A)(&2 * x)` THEN
    ASM_REWRITE_TAC[REAL_ARITH `&2 * x / &2 = x`] THEN
    CONJ_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT_REFL] THEN
    ASM_SIMP_TAC[ADD_CLAUSES; real_pow; REAL_POW_EQ_0; REAL_OF_NUM_EQ;
      ARITH_EQ; REAL_FIELD `~(y = &0) ==> &2 * x / (&2 * y) = x / y`]) in
  let exists_function_unpair = prove
   (`(?f:A->B#C. P f) <=> (?f1 f2. P(\x. (f1 x,f2 x)))`,
    EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN STRIP_TAC THEN
    EXISTS_TAC `\x. FST((f:A->B#C) x)` THEN
    EXISTS_TAC `\x. SND((f:A->B#C) x)` THEN
    ASM_REWRITE_TAC[PAIR; ETA_AX]) in
  let dyadics_in_open_unit_interval = prove
   (`interval(vec 0,vec 1) INTER
      {lift(&m / &2 pow n) | m IN (:num) /\ n IN (:num)} =
      {lift(&m / &2 pow n) | 0 < m /\ m < 2 EXP n}`,
    MATCH_MP_TAC(SET_RULE
     `(!m n. (f m n) IN s <=> P m n)
      ==> s INTER {f m n | m IN UNIV /\ n IN UNIV} =
          {f m n | P m n}`) THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN
    SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_POW; REAL_OF_NUM_LT]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b m. m IN interval[a,b] /\ interval[a,b] SUBSET interval[vec 0,vec 1]
            ==> ?c d. drop a <= drop c /\ drop c <= drop m /\
                      drop m <= drop d /\ drop d <= drop b /\
                      (!x. x IN interval[c,d] ==> f x = f m) /\
                      (!x. x IN interval[a,c] DELETE c ==> ~(f x = f m)) /\
                      (!x. x IN interval[d,b] DELETE d ==> ~(f x = f m)) /\
                      (!x y. x IN interval[a,c] DELETE c /\
                             y IN interval[d,b] DELETE d
                             ==> ~((f:real^1->real^N) x = f y))`
  MP_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; SUBSET_INTERVAL_1] THEN
    REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `?c d. {x | x IN interval[a,b] /\ (f:real^1->real^N) x = f m} =
            interval[c,d]`
    MP_TAC THENL
     [SUBGOAL_THEN
       `{x | x IN interval[a,b] /\ (f:real^1->real^N) x = f m} =
        interval[a,b] INTER
        {x | x IN interval[vec 0,vec 1] /\ (f:real^1->real^N) x = f m}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERVAL_1; IN_ELIM_THM;
                    DROP_VEC] THEN
        GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `?c d. {x | x IN interval[vec 0,vec 1] /\ (f:real^1->real^N) x = f m} =
              interval[c,d]`
      MP_TAC THENL
       [ASM_REWRITE_TAC[GSYM CONNECTED_COMPACT_INTERVAL_1] THEN
        ONCE_REWRITE_TAC[SET_RULE
         `{x | x IN s /\ P x} = s INTER {x | x IN s /\ P x}`] THEN
        MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
        REWRITE_TAC[COMPACT_INTERVAL] THEN
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_CONSTANT THEN
        ASM_REWRITE_TAC[CLOSED_INTERVAL];
        STRIP_TAC THEN ASM_REWRITE_TAC[INTER_INTERVAL_1] THEN MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^1` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `m IN interval[c:real^1,d]` MP_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
                  ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_INTERVAL_1; IN_DELETE] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `{c:real^1,d} SUBSET interval[c,d]` MP_TAC THENL
     [ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTERVAL_1] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
       [GSYM th]) THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM; IN_INTERVAL_1] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[GSYM IN_INTERVAL_1] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC  (LAND_CONV o RAND_CONV)
       [GSYM th]) THEN SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
      `{x | x IN s /\ f x = a} = t
       ==> (!x. P x ==> x IN s) /\ (!x. P x /\ Q x ==> ~(x IN t))
           ==> !x. P x /\ Q x ==> ~(f x = a)`)) THEN
      REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[GSYM DROP_EQ] THEN STRIP_TAC THEN
    SUBGOAL_THEN `{x:real^1,y} INTER interval[c,d] = {}` MP_TAC THENL
     [REWRITE_TAC[SET_RULE `{a,b} INTER s = {} <=> ~(a IN s) /\ ~(b IN s)`;
                  IN_INTERVAL_1] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
       (LAND_CONV o LAND_CONV o RAND_CONV) [GSYM th])] THEN
    REWRITE_TAC[SET_RULE `{a,b} INTER s = {} <=> ~(a IN s) /\ ~(b IN s)`] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1] THEN
    ASM_CASES_TAC `(f:real^1->real^N) x = f m` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `(f:real^1->real^N) y = f m` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM IS_INTERVAL_CONNECTED_1] o
                  SPEC `(f:real^1->real^N) y`) THEN
    ASM_REWRITE_TAC[IS_INTERVAL_1] THEN DISCH_THEN(MP_TAC o SPECL
     [`x:real^1`; `y:real^1`; `m:real^1`]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`leftcut:real^1->real^1->real^1->real^1`;
      `rightcut:real^1->real^1->real^1->real^1`] THEN
    STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`vec 0:real^1`; `vec 1:real^1`; `vec 0:real^1`]) THEN
  REWRITE_TAC[SUBSET_REFL; ENDS_IN_UNIT_INTERVAL] THEN ABBREV_TAC
   `u = (rightcut:real^1->real^1->real^1->real^1) (vec 0) (vec 1) (vec 0)` THEN
  REWRITE_TAC[CONJ_ASSOC; REAL_LE_ANTISYM; DROP_EQ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[INTERVAL_SING; SET_RULE `~(x IN ({a} DELETE a))`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`u:real^1`; `vec 1:real^1`; `vec 1:real^1`]) THEN
  REWRITE_TAC[ENDS_IN_INTERVAL; SUBSET_INTERVAL_1; INTERVAL_NE_EMPTY_1] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ABBREV_TAC
   `v = (leftcut:real^1->real^1->real^1->real^1) u (vec 1) (vec 1)` THEN
  ONCE_REWRITE_TAC[TAUT
    `a /\ b /\ c /\ d /\ e <=> (c /\ d) /\ a /\ b /\ e`] THEN
  REWRITE_TAC[REAL_LE_ANTISYM; DROP_EQ] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[INTERVAL_SING; SET_RULE `~(x IN ({a} DELETE a))`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN interval[vec 0,v] DELETE v
        ==> ~((f:real^1->real^N) x = f(vec 1))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN
    REWRITE_TAC[IN_DELETE; IN_INTERVAL_1; GSYM DROP_EQ] THEN STRIP_TAC THEN
    ASM_CASES_TAC `drop t < drop u` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
       `~(f1 = f0) ==> ft = f0 ==> ~(ft = f1)`));
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; IN_DELETE; GSYM DROP_EQ] THEN
    ASM_REAL_ARITH_TAC;
    UNDISCH_THEN
      `!x. x IN interval[u,v] DELETE v ==> ~((f:real^1->real^N) x = f (vec 1))`
      (K ALL_TAC)] THEN
  MP_TAC(ISPECL
   [`(u:real^1,v:real^1)`;
    `\(a,b). (a:real^1,leftcut a b (midpoint(a,b)):real^1)`;
    `\(a,b). (rightcut a b (midpoint(a,b)):real^1,b:real^1)`]
        recursion_on_dyadic_rationals_1) THEN
  REWRITE_TAC[exists_function_unpair; PAIR_EQ] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real->real^1`; `b:real->real^1`] THEN
  ABBREV_TAC `(c:real->real^1) x = midpoint(a x,b x)` THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m n. drop u <= drop(a(&m / &2 pow n)) /\
          drop(a(&m / &2 pow n)) <= drop(b(&m / &2 pow n)) /\
          drop(b(&m / &2 pow n)) <= drop v`
  MP_TAC THENL
   [GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN MATCH_MP_TAC num_INDUCTION THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x / &2 pow 0 = (&2 * x) / &2`] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_LE_REFL];
      X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "*")] THEN
    X_GEN_TAC `p:num` THEN DISJ_CASES_TAC(SPEC `p:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; real_pow] THEN
      ASM_SIMP_TAC[REAL_LT_POW2; REAL_FIELD
       `&0 < y ==> (&2 * x) / (&2 * y) = x / y`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 0 < n`) THENL
     [ASM_REWRITE_TAC[real_pow; REAL_MUL_RID; REAL_LE_REFL];
      REWRITE_TAC[ADD1]] THEN
    DISJ_CASES_TAC(SPEC `m:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
      ASM_SIMP_TAC[ARITH_RULE `2 * 2 * r = 4 * r`];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
      ASM_SIMP_TAC[ARITH_RULE `2 * SUC(2 * r) + 1 = 4 * r + 3`]] THEN
    (FIRST_X_ASSUM(MP_TAC o SPECL
      [`a(&(2 * r + 1) / &2 pow n):real^1`;
       `b(&(2 * r + 1) / &2 pow n):real^1`;
       `c(&(2 * r + 1) / &2 pow n):real^1`]) THEN
     ANTS_TAC THENL
      [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
        [GSYM th]) THEN
       REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
       REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN
       UNDISCH_TAC `drop(vec 0) <= drop u` THEN
       UNDISCH_TAC `drop v <= drop (vec 1)`;
       ALL_TAC] THEN
     REMOVE_THEN "*" (MP_TAC o SPEC `2 * r + 1`) THEN REAL_ARITH_TAC);
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `!m n. drop(vec 0) <= drop(a(&m / &2 pow n))` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. drop(b(&m / &2 pow n)) <= drop(vec 1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m n. drop(a(&m / &2 pow n)) <= drop(c(&m / &2 pow n)) /\
          drop(c(&m / &2 pow n)) <= drop(b(&m / &2 pow n))`
  MP_TAC THENL
   [UNDISCH_THEN `!x:real. midpoint(a x:real^1,b x) = c x`
      (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
    ASM_REWRITE_TAC[DROP_CMUL; DROP_ADD; REAL_ARITH
     `a <= inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a <= b`];
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `!i m n j. ODD j /\
              abs(&i / &2 pow m - &j / &2 pow n) < inv(&2 pow n)
              ==> drop(a(&j / &2 pow n)) <= drop(c(&i / &2 pow m)) /\
                  drop(c(&i / &2 pow m)) <= drop(b(&j / &2 pow n))`
  ASSUME_TAC THENL
   [REPLICATE_TAC 3 GEN_TAC THEN WF_INDUCT_TAC `m - n:num` THEN
    DISJ_CASES_TAC(ARITH_RULE `m <= n \/ n:num < m`) THENL
     [GEN_TAC THEN STRIP_TAC THEN
      MP_TAC(SPEC `abs(&2 pow n) * abs(&i / &2 pow m - &j / &2 pow n)`
                REAL_ABS_INTEGER_LEMMA) THEN
      MATCH_MP_TAC(TAUT
       `i /\ ~b /\ (n ==> p) ==> (i /\ ~n ==> b) ==> p`) THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_ABS_MUL; INTEGER_ABS] THEN
        REWRITE_TAC[REAL_ARITH
         `n * (x / m - y / n):real = x * (n / m) - y * (n / n)`] THEN
        ASM_SIMP_TAC[GSYM REAL_POW_SUB; LE_REFL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
        MESON_TAC[INTEGER_CLOSED];
        SIMP_TAC[REAL_ABS_MUL; REAL_ABS_ABS; REAL_ABS_POW; REAL_ABS_NUM] THEN
        REWRITE_TAC[REAL_ARITH `~(&1 <= x * y) <=> y * x < &1`] THEN
        SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
        ASM_REWRITE_TAC[REAL_ARITH `&1 / x = inv x`];
        ASM_SIMP_TAC[REAL_ABS_POW; REAL_ABS_NUM; REAL_ENTIRE; REAL_LT_IMP_NZ;
          REAL_LT_POW2; REAL_ARITH `abs(x - y) = &0 <=> x = y`]];
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[IMP_CONJ; ODD_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 0 < n`) THENL
     [ASM_REWRITE_TAC[REAL_ARITH `x / &2 pow 0 = (&2 * x) / &2`] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_MUL] THEN ASM_MESON_TAC[REAL_LE_TRANS];
      ALL_TAC] THEN
    UNDISCH_THEN `n:num < m`
      (fun th -> let th' = MATCH_MP
                   (ARITH_RULE `n < m ==> m - SUC n < m - n`) th in
                 FIRST_X_ASSUM(MP_TAC o C MATCH_MP th')) THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH
     `&i / &2 pow m = &(2 * j + 1) / &2 pow n \/
      &i / &2 pow m < &(2 * j + 1) / &2 pow n \/
      &(2 * j + 1) / &2 pow n < &i / &2 pow m`)
    THENL
     [ASM_REWRITE_TAC[ADD1];
      DISCH_THEN(MP_TAC o SPEC `4 * j + 1`) THEN
      REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN ASM_SIMP_TAC[ADD1] THEN
      MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH
         `x < i /\ &2 * n1 = n /\ j + n1 = i
          ==> abs(x - i) < n ==> abs(x - j) < n1`) THEN
        ASM_REWRITE_TAC[REAL_ARITH `a / b + inv b = (a + &1) / b`] THEN
        REWRITE_TAC[real_div; REAL_POW_ADD; REAL_INV_MUL] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH
         `b' <= b ==> a <= c /\ c <= b' ==> a <= c /\ c <= b`) THEN
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`a(&(2 * j + 1) / &2 pow n):real^1`;
          `b(&(2 * j + 1) / &2 pow n):real^1`;
          `c(&(2 * j + 1) / &2 pow n):real^1`]) THEN
        ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
          [GSYM th]) THEN
        REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
        REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN
        ASM_REWRITE_TAC[DROP_CMUL; DROP_ADD; REAL_ARITH
         `a <= inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a <= b`]];
      DISCH_THEN(MP_TAC o SPEC `4 * j + 3`) THEN
      REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN ASM_SIMP_TAC[ADD1] THEN
      MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH
         `i < x /\ &2 * n1 = n /\ j - n1 = i
          ==> abs(x - i) < n ==> abs(x - j) < n1`) THEN
        ASM_REWRITE_TAC[REAL_ARITH `a / b - inv b = (a - &1) / b`] THEN
        REWRITE_TAC[real_div; REAL_POW_ADD; REAL_INV_MUL] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH
         `a <= a' ==> a' <= c /\ c <= b ==> a <= c /\ c <= b`) THEN
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`a(&(2 * j + 1) / &2 pow n):real^1`;
          `b(&(2 * j + 1) / &2 pow n):real^1`;
          `c(&(2 * j + 1) / &2 pow n):real^1`]) THEN
        ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
          [GSYM th]) THEN
        REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
        REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN
        ASM_REWRITE_TAC[DROP_CMUL; DROP_ADD; REAL_ARITH
         `a <= inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a <= b`]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m n. ODD m ==> abs(drop(a(&m / &2 pow n)) - drop(b(&m / &2 pow n)))
                    <= &2 / &2 pow n`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THENL
     [ASM_REWRITE_TAC[REAL_ARITH `x / &2 pow 0 = (&2 * x) / &2`] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_MUL] THEN CONV_TAC NUM_REDUCE_CONV THEN
      RULE_ASSUM_TAC(REWRITE_RULE[DROP_VEC]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[ODD_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 0 < n`) THENL
     [ASM_REWRITE_TAC[ARITH; REAL_POW_1] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[DROP_VEC]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISJ_CASES_TAC(SPEC `k:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
      REWRITE_TAC[ARITH_RULE `SUC(2 * 2 * j) = 4 * j + 1`] THEN
      ASM_SIMP_TAC[ADD1] THEN
      MATCH_MP_TAC(REAL_ARITH
       `drop c = (drop a + drop b) / &2 /\
        abs(drop a - drop b) <= &2 * k /\
        drop a <= drop(leftcut a b c) /\
        drop(leftcut a b c) <= drop c
        ==> abs(drop a - drop(leftcut a b c)) <= k`);
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
      REWRITE_TAC[ARITH_RULE `SUC(2 * SUC(2 * j)) = 4 * j + 3`] THEN
      ASM_SIMP_TAC[ADD1] THEN
      MATCH_MP_TAC(REAL_ARITH
       `drop c = (drop a + drop b) / &2 /\
        abs(drop a - drop b) <= &2 * k /\
        drop c <= drop(rightcut a b c) /\
        drop(rightcut a b c) <= drop b
        ==> abs(drop(rightcut a b c) - drop b) <= k`)] THEN
    (CONJ_TAC THENL
      [UNDISCH_THEN `!x:real. midpoint(a x:real^1,b x) = c x`
        (fun th -> REWRITE_TAC[GSYM th]) THEN
       REWRITE_TAC[midpoint; DROP_CMUL; DROP_ADD] THEN REAL_ARITH_TAC;
       ALL_TAC] THEN
     CONJ_TAC THENL
      [REWRITE_TAC[real_div; REAL_POW_ADD; REAL_INV_MUL] THEN
       REWRITE_TAC[REAL_ARITH `&2 * x * inv y * inv(&2 pow 1) = x / y`] THEN
       ASM_SIMP_TAC[GSYM real_div; ODD_ADD; ODD_MULT; ARITH];
       ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPECL
      [`a(&(2 * j + 1) / &2 pow n):real^1`;
       `b(&(2 * j + 1) / &2 pow n):real^1`;
       `c(&(2 * j + 1) / &2 pow n):real^1`]) THEN
     ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
     FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
       [GSYM th]) THEN
     REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
     REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN
     ASM_REWRITE_TAC[DROP_CMUL; DROP_ADD; REAL_ARITH
      `a <= inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a <= b`]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n j. 0 < 2 * j /\ 2 * j < 2 EXP n
          ==> (f:real^1->real^N)(b(&(2 * j - 1) / &2 pow n)) =
              f(a(&(2 * j + 1) / &2 pow n))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `0 < 2 * j <=> 0 < j`;
                  ARITH_RULE `2 * j < 2 <=> j < 1`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "+") THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 0 < n`) THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ARITH_RULE `0 < 2 * j <=> 0 < j`;
                   ARITH_RULE `2 * j < 2  <=> j < 1`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISJ_CASES_TAC(SPEC `k:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
      REWRITE_TAC[EXP; ARITH_RULE `0 < 2 * j <=> 0 < j`; LT_MULT_LCANCEL] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[ARITH_RULE `0 < j ==> 2 * 2 * j - 1 = 4 * (j - 1) + 3`;
        ADD1; ARITH_RULE `2 * 2 * j + 1 = 4 * j + 1`] THEN
      SIMP_TAC[ARITH_RULE `0 < j ==> 2 * (j - 1) + 1 = 2 * j - 1`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
      STRIP_TAC THEN
      ASM_SIMP_TAC[ADD1; ARITH_RULE `2 * SUC(2 * j) - 1 = 4 * j + 1`;
                   ARITH_RULE `2 * SUC(2 * j) + 1 = 4 * j + 3`] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`a(&(2 * j + 1) / &2 pow n):real^1`;
        `b(&(2 * j + 1) / &2 pow n):real^1`;
        `c(&(2 * j + 1) / &2 pow n):real^1`]) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
         [GSYM th]) THEN
        REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
        REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN
        ASM_REWRITE_TAC[DROP_CMUL; DROP_ADD; REAL_ARITH
         `a <= inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a <= b`];
        REPLICATE_TAC 4 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
        MATCH_MP_TAC(MESON[]
         `a IN s /\ b IN s ==> (!x. x IN s ==> f x = c) ==> f a = f b`) THEN
        REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
        ASM_MESON_TAC[REAL_LE_TRANS]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n j. 0 < j /\ j < 2 EXP n
          ==> (f:real^1->real^N)(b(&(2 * j - 1) / &2 pow (n + 1))) =
              f(c(&j / &2 pow n)) /\
              f(a(&(2 * j + 1) / &2 pow (n + 1))) = f(c(&j / &2 pow n))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC[ARITH_RULE `~(0 < j /\ j < 2 EXP 0)`] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "*") THEN
    X_GEN_TAC `j:num` THEN
    DISJ_CASES_TAC(SPEC `j:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
      REWRITE_TAC[ADD_CLAUSES; EXP; ARITH_RULE `0 < 2 * k <=> 0 < k`;
                  ARITH_RULE `2 * x < 2 * y <=> x < y`] THEN STRIP_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `k:num`) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(MESON[]
       `c' = c /\ a' = a /\ b' = b
        ==> b = c /\ a = c ==> b' = c' /\ a' = c'`) THEN
      REPEAT CONJ_TAC THEN AP_TERM_TAC THENL
       [AP_TERM_TAC THEN
        REWRITE_TAC[real_pow; real_div; REAL_INV_MUL;
                    GSYM REAL_OF_NUM_MUL] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[ADD1; ARITH_RULE `2 * 2 * n = 4 * n`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
        SUBGOAL_THEN `k = PRE k + 1` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `2 * (k + 1) - 1 = 2 * k + 1`;
                    ARITH_RULE `2 * 2 * (k + 1) - 1 = 4 * k + 3`] THEN
        REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
      REWRITE_TAC[EXP; ARITH_RULE `SUC(2 * k) < 2 * n <=> k < n`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
       [`a(&(2 * k + 1) / &2 pow (SUC n)):real^1`;
        `b(&(2 * k + 1) / &2 pow (SUC n)):real^1`;
        `c(&(2 * k + 1) / &2 pow (SUC n)):real^1`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1];
        REPLICATE_TAC 4 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)] THEN
      REWRITE_TAC[ARITH_RULE `SUC(2 * k) = 2 * k + 1`] THEN
      DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN
      ASM_SIMP_TAC[ARITH_RULE `2 * (2 * k + 1) - 1 = 4 * k + 1`; ADD1;
                   ARITH_RULE `2 * (2 * k + 1) + 1 = 4 * k + 3`;
                   ARITH_RULE `0 < n + 1`] THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; GSYM ADD1] THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC(2 * k) = 2 * k + 1`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
  REWRITE_TAC[COMPACT_INTERVAL] THEN
  MP_TAC(ISPECL [`\x. (f:real^1->real^N)(c(drop x))`;
                 `interval(vec 0,vec 1) INTER
                  {lift(&m / &2 pow n) | m IN (:num) /\ n IN (:num)}`]
        UNIFORMLY_CONTINUOUS_EXTENDS_TO_CLOSURE) THEN
  SIMP_TAC[closure_dyadic_rationals_in_convex_set_pos_1;
           CONVEX_INTERVAL; INTERIOR_OPEN; OPEN_INTERVAL;
           UNIT_INTERVAL_NONEMPTY; IN_INTERVAL_1; REAL_LT_IMP_LE; DROP_VEC;
           CLOSURE_OPEN_INTERVAL] THEN
  REWRITE_TAC[dyadics_in_open_unit_interval] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[uniformly_continuous_on; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN SUBGOAL_THEN
     `(f:real^1->real^N) uniformly_continuous_on interval[vec 0,vec 1]`
    MP_TAC THENL
     [ASM_SIMP_TAC[COMPACT_UNIFORMLY_CONTINUOUS; COMPACT_INTERVAL];
      REWRITE_TAC[uniformly_continuous_on]] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`inv(&2)`; `min (d:real) (&1 / &4)`] REAL_ARCH_POW_INV) THEN
    ASM_REWRITE_TAC[REAL_HALF; REAL_POW_INV; REAL_LT_MIN] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
    EXISTS_TAC `inv(&2 pow n)` THEN
    REWRITE_TAC[REAL_LT_POW2; REAL_LT_INV_EQ] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    SUBGOAL_THEN
     `!i j m. 0 < i /\ i < 2 EXP m /\ 0 < j /\ j < 2 EXP n /\
              abs(&i / &2 pow m - &j / &2 pow n) < inv(&2 pow n)
              ==> norm((f:real^1->real^N)(c(&i / &2 pow m)) -
                       f(c(&j / &2 pow n))) < e / &2`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC o MATCH_MP (REAL_ARITH
       `abs(x - a) < e
        ==> x = a \/
            abs(x - (a - e / &2)) < e / &2 \/
            abs(x - (a + e / &2)) < e / &2`))
      THENL
       [DISCH_THEN SUBST1_TAC THEN
        ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_HALF];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `&j / &2 pow n = &(2 * j) / &2 pow (n + 1)`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
      THENL
       [REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL;
                    GSYM REAL_OF_NUM_MUL] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[real_div; GSYM REAL_INV_MUL] THEN
      REWRITE_TAC[GSYM real_div;
           GSYM(ONCE_REWRITE_RULE[REAL_MUL_SYM] (CONJUNCT2 real_pow))] THEN
      REWRITE_TAC[ADD1; REAL_ARITH `x / n + inv n = (x + &1) / n`;
                  REAL_ARITH `x / n - inv n = (x - &1) / n`] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `0 < j ==> 1 <= 2 * j`] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD] THEN STRIP_TAC THENL
       [SUBGOAL_THEN `(f:real^1->real^N)(c(&j / &2 pow n)) =
                      f(b (&(2 * j - 1) / &2 pow (n + 1)))`
        SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC];
        SUBGOAL_THEN `(f:real^1->real^N)(c(&j / &2 pow n)) =
                      f(a (&(2 * j + 1) / &2 pow (n + 1)))`
        SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC]] THEN
      REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_INTERVAL_1] THEN
      REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC]) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `m:num`; `n + 1`]) THENL
       [DISCH_THEN(MP_TAC o SPEC `2 * j - 1`) THEN REWRITE_TAC[ODD_SUB];
        DISCH_THEN(MP_TAC o SPEC `2 * j + 1`) THEN REWRITE_TAC[ODD_ADD]] THEN
      ASM_REWRITE_TAC[ODD_MULT; ARITH; ARITH_RULE `1 < 2 * j <=> 0 < j`] THEN
      REWRITE_TAC[DIST_REAL; GSYM drop] THENL
       [MATCH_MP_TAC(NORM_ARITH
         `!t. abs(a - b) <= t /\ t < d
              ==> a <= c /\ c <= b ==> abs(c - b) < d`);
        MATCH_MP_TAC(NORM_ARITH
         `!t. abs(a - b) <= t /\ t < d
              ==> a <= c /\ c <= b ==> abs(c - a) < d`)] THEN
      EXISTS_TAC `&2 / &2 pow (n + 1)` THEN
      (CONJ_TAC THENL
        [FIRST_X_ASSUM MATCH_MP_TAC THEN
         REWRITE_TAC[ODD_SUB; ODD_ADD; ODD_MULT; ARITH_ODD] THEN
         ASM_REWRITE_TAC[ARITH_RULE `1 < 2 * j <=> 0 < j`];
         REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL] THEN
         ASM_REAL_ARITH_TAC]);
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `m:num`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `p:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[DIST_LIFT; LIFT_DROP] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?j. 0 < j /\ j < 2 EXP n /\
          abs(&i / &2 pow m - &j / &2 pow n) < inv(&2 pow n) /\
          abs(&k / &2 pow p - &j / &2 pow n) < inv(&2 pow n)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `max (&2 pow n * &i / &2 pow m)
                       (&2 pow n * &k / &2 pow p)`
        FLOOR_POS) THEN
      SIMP_TAC[REAL_LE_MUL; REAL_LE_MAX; REAL_LE_DIV;
               REAL_POS; REAL_POW_LE] THEN
      DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
      MP_TAC(SPEC `max (&2 pow n * &i / &2 pow m)
                       (&2 pow n * &k / &2 pow p)` FLOOR) THEN
      ASM_REWRITE_TAC[REAL_LE_MAX; REAL_MAX_LT] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_ARITH `(j + &1) / n = j / n + inv n`] THEN
      ASM_CASES_TAC `j = 0` THENL
       [ASM_REWRITE_TAC[REAL_ARITH `&0 / x = &0`; REAL_ADD_LID] THEN
        DISCH_TAC THEN EXISTS_TAC `1` THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[ARITH_RULE `1 < n <=> 2 EXP 1 <= n`] THEN
        ASM_SIMP_TAC[LE_EXP; LE_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 < x /\ x < inv n /\ &0 < y /\ y < inv n
          ==> abs(x - &1 / n) < inv n /\ abs(y - &1 / n) < inv n`) THEN
        ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; REAL_LT_POW2];
        DISCH_TAC THEN EXISTS_TAC `j:num` THEN ASM_SIMP_TAC[LE_1] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_POW] THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
        SIMP_TAC[GSYM REAL_NOT_LE; REAL_LE_FLOOR; INTEGER_CLOSED] THEN
        REWRITE_TAC[REAL_NOT_LE; REAL_MAX_LT] THEN
        REWRITE_TAC[REAL_ARITH `n * x < n <=> n * x < n * &1`] THEN
        SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_POW2; REAL_LT_LDIV_EQ] THEN
        ASM_REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_POW; REAL_OF_NUM_LT]];
      MATCH_MP_TAC(NORM_ARITH
       `!u. dist(w:real^N,u) < e / &2 /\ dist(z,u) < e / &2
            ==> dist(w,z) < e`) THEN
      EXISTS_TAC `(f:real^1->real^N)(c(&j / &2 pow n))` THEN
      REWRITE_TAC[dist] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^1->real^N` THEN
  REWRITE_TAC[FORALL_IN_GSPEC; LIFT_DROP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT1)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS) THEN
  ONCE_REWRITE_TAC[MESON[] `h x = f(c(drop x)) <=> f(c(drop x)) = h x`] THEN
  REWRITE_TAC[IN_INTER; IMP_CONJ_ALT; FORALL_IN_GSPEC] THEN
  ASM_REWRITE_TAC[IN_UNIV; LIFT_DROP; IMP_IMP; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `interval(vec 0:real^1,vec 1)`
        closure_dyadic_rationals_in_convex_set_pos_1) THEN
      SIMP_TAC[CONVEX_INTERVAL; IN_INTERVAL_1; REAL_LT_IMP_LE; DROP_VEC;
        INTERIOR_OPEN; OPEN_INTERVAL; INTERVAL_NE_EMPTY_1; REAL_LT_01;
        CLOSURE_OPEN_INTERVAL] THEN
      DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
      MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_INTERVAL] THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
        REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED];
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        ASM_REWRITE_TAC[COMPACT_INTERVAL];
        SIMP_TAC[dyadics_in_open_unit_interval; SUBSET; FORALL_IN_IMAGE] THEN
        ASM_SIMP_TAC[FORALL_IN_GSPEC] THEN
        MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1] THEN
        ASM_MESON_TAC[REAL_LE_TRANS]];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure(IMAGE (h:real^1->real^N)
                                 (interval (vec 0,vec 1) INTER
        {lift (&m / &2 pow n) | m IN (:num) /\ n IN (:num)}))` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC CLOSURE_MINIMAL THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_INTERVAL;
                     COMPACT_CONTINUOUS_IMAGE] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
        REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED]] THEN
      REWRITE_TAC[SUBSET; CLOSURE_APPROACHABLE; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[dyadics_in_open_unit_interval;
                  EXISTS_IN_IMAGE; EXISTS_IN_GSPEC] THEN
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN UNDISCH_TAC
       `(f:real^1->real^N) continuous_on interval [vec 0,vec 1]` THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        COMPACT_UNIFORMLY_CONTINUOUS)) THEN
      REWRITE_TAC[COMPACT_INTERVAL; uniformly_continuous_on] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `!n. ~(n = 0)
            ==> ?m y. ODD m /\ 0 < m /\ m < 2 EXP n /\
                      y IN interval[a(&m / &2 pow n),b(&m / &2 pow n)] /\
                     (f:real^1->real^N) y = f x`
      MP_TAC THENL
       [ALL_TAC;
        MP_TAC(SPECL [`inv(&2)`; `min (d / &2) (&1 / &4)`]
         REAL_ARCH_POW_INV) THEN
        ASM_REWRITE_TAC[REAL_HALF; REAL_POW_INV; REAL_LT_MIN] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
        ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
        DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^1` MP_TAC) THEN
        REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN EXISTS_TAC `n:num` THEN
        ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
        REWRITE_TAC[DIST_REAL; GSYM drop; IN_INTERVAL_1] THEN
        REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC]) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `a <= y /\ y <= b
          ==> a <= c /\ c <= b /\ abs(a - b) < d
              ==> abs(c - y) < d`)) THEN
        REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC]) THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 / &2 pow n` THEN
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[NOT_SUC] THEN
      X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
       [EXISTS_TAC `1` THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[REAL_POW_1] THEN
        SUBGOAL_THEN
         `x IN interval[vec 0:real^1,u] \/
          x IN interval[u,v] \/
          x IN interval[v,vec 1]`
        STRIP_ASSUME_TAC THENL
         [REWRITE_TAC[IN_INTERVAL_1] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
          ASM_REAL_ARITH_TAC;
          EXISTS_TAC `u:real^1` THEN
          ASM_MESON_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1];
          EXISTS_TAC `x:real^1` THEN ASM_MESON_TAC[];
          EXISTS_TAC `v:real^1` THEN
          ASM_MESON_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1]];
        DISCH_THEN(X_CHOOSE_THEN `m:num`
         (X_CHOOSE_THEN `y:real^1` MP_TAC)) THEN
        REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
        DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THEN
        REWRITE_TAC[ADD1] THEN DISCH_TAC THEN
        SUBGOAL_THEN
        `y IN interval[a(&(2 * j + 1) / &2 pow n):real^1,
                       b(&(4 * j + 1) / &2 pow (n + 1))] \/
         y IN interval[b(&(4 * j + 1) / &2 pow (n + 1)),
                       a(&(4 * j + 3) / &2 pow (n + 1))] \/
         y IN interval[a(&(4 * j + 3) / &2 pow (n + 1)),
                       b(&(2 * j + 1) / &2 pow n)]`
        STRIP_ASSUME_TAC THENL
         [REWRITE_TAC[IN_INTERVAL_1] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
          ASM_REAL_ARITH_TAC;
          EXISTS_TAC `4 * j + 1` THEN
          EXISTS_TAC `y:real^1` THEN
          REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH; EXP_ADD] THEN
          REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
           `y IN interval[a,b]
            ==> a = a' /\ b = b' ==> y IN interval[a',b']`)) THEN
          ASM_MESON_TAC[LE_1];
          EXISTS_TAC `4 * j + 1` THEN
          EXISTS_TAC `b(&(4 * j + 1) / &2 pow (n + 1)):real^1` THEN
          REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH; EXP_ADD] THEN
          REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
          REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
          CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o SPECL
           [`a(&(2 * j + 1) / &2 pow n):real^1`;
            `b(&(2 * j + 1) / &2 pow n):real^1`;
            `c(&(2 * j + 1) / &2 pow n):real^1`]) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1];
            REPLICATE_TAC 4
             (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
            DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)] THEN
          MATCH_MP_TAC(MESON[]
           `a IN s /\ b IN s ==> (!x. x IN s ==> f x = k) ==> f a = f b`) THEN
          SUBGOAL_THEN
           `leftcut (a (&(2 * j + 1) / &2 pow n))
                    (b (&(2 * j + 1) / &2 pow n))
                    (c (&(2 * j + 1) / &2 pow n):real^1):real^1 =
            b(&(4 * j + 1) / &2 pow (n + 1)) /\
            rightcut (a (&(2 * j + 1) / &2 pow n))
                     (b (&(2 * j + 1) / &2 pow n))
                     (c (&(2 * j + 1) / &2 pow n)):real^1 =
            a(&(4 * j + 3) / &2 pow (n + 1))`
          (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
            [ASM_MESON_TAC[LE_1]; ALL_TAC] THEN
          REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
           `y IN interval[a,b]
            ==> a = a' /\ b = b' ==> y IN interval[a',b']`)) THEN
          ASM_MESON_TAC[LE_1];
          EXISTS_TAC `4 * j + 3` THEN
          EXISTS_TAC `y:real^1` THEN
          REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH; EXP_ADD] THEN
          REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
           `y IN interval[a,b]
            ==> a = a' /\ b = b' ==> y IN interval[a',b']`)) THEN
          ASM_MESON_TAC[LE_1]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n m. drop(a(&m / &2 pow n)) < drop(b(&m / &2 pow n)) /\
          (!x. drop(a(&m / &2 pow n)) < drop x /\
               drop x <= drop(b(&m / &2 pow n))
               ==> ~(f x = f(a(&m / &2 pow n)))) /\
          (!x. drop(a(&m / &2 pow n)) <= drop x /\
               drop x < drop(b(&m / &2 pow n))
               ==> ~(f x :real^N = f(b(&m / &2 pow n))))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `drop u < drop v` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_LE; DROP_EQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [IN_DELETE; IN_INTERVAL_1; GSYM DROP_EQ; DROP_VEC]) THEN
      ASM_MESON_TAC[DROP_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(!x. drop u < drop x /\ drop x <= drop v
          ==> ~((f:real^1->real^N) x = f u)) /\
      (!x. drop u <= drop x /\ drop x < drop v
           ==> ~(f x = f v))`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(f:real^1->real^N) u = f(vec 0) /\
        (f:real^1->real^N) v = f(vec 1)`
       (CONJUNCTS_THEN SUBST1_TAC)
      THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL];
        ALL_TAC] THEN
      CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_DELETE; IN_INTERVAL_1; GSYM DROP_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC num_INDUCTION THEN
    ASM_REWRITE_TAC[REAL_ARITH `&m / &2 pow 0 = (&2 * &m) / &2`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_MUL] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "*") THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 0 < n`) THEN
    ASM_REWRITE_TAC[ARITH; REAL_POW_1] THEN
    X_GEN_TAC `j:num` THEN
    DISJ_CASES_TAC(ISPEC `j:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
      SIMP_TAC[GSYM REAL_OF_NUM_MUL; real_div; REAL_INV_MUL; real_pow] THEN
      ASM_REWRITE_TAC[REAL_ARITH `(&2 * p) * inv(&2) * inv q = p / q`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
    DISJ_CASES_TAC(ISPEC `k:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
      ASM_SIMP_TAC[ARITH_RULE `2 * 2 * m = 4 * m`; ADD1] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`a(&(2 * m + 1) / &2 pow n):real^1`;
        `b(&(2 * m + 1) / &2 pow n):real^1`;
        `c(&(2 * m + 1) / &2 pow n):real^1`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
        ASM_MESON_TAC[REAL_LE_TRANS];
        REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(K ALL_TAC)] THEN
      SUBGOAL_THEN
       `(f:real^1->real^N)
        (leftcut (a (&(2 * m + 1) / &2 pow n):real^1)
                 (b (&(2 * m + 1) / &2 pow n):real^1)
                 (c (&(2 * m + 1) / &2 pow n):real^1)) =
        (f:real^1->real^N) (c(&(2 * m + 1) / &2 pow n))`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_LT_LE] THEN ASM_REWRITE_TAC[DROP_EQ] THEN
      REPEAT CONJ_TAC THENL
       [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        UNDISCH_THEN
         `(f:real^1->real^N) (a (&(2 * m + 1) / &2 pow n)) =
          f(c (&(2 * m + 1) / &2 pow n))` (MP_TAC o SYM) THEN
        REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o SPEC_ALL) THEN
        REWRITE_TAC[GSYM(ASSUME `!x. midpoint ((a:real->real^1) x,b x) = c x`);
                    midpoint; DROP_CMUL; DROP_ADD] THEN
        ASM_REWRITE_TAC[REAL_ARITH
         `a < inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a < b`];
        GEN_TAC THEN STRIP_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o SPEC_ALL) THEN
        ASM_MESON_TAC[REAL_LE_TRANS];
        GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM
         (fun th -> MATCH_MP_TAC th THEN
                    REWRITE_TAC[IN_INTERVAL_1; IN_DELETE; GSYM DROP_EQ] THEN
             GEN_REWRITE_TAC I [REAL_ARITH
              `(a <= x /\ x <= b) /\ ~(x = b) <=> a <= x /\ x < b`]) THEN
        ASM_REWRITE_TAC[]];
       FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
       DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
       ASM_SIMP_TAC[ARITH_RULE `2 * (2 * m + 1) + 1  = 4 * m + 3`; ADD1] THEN
       FIRST_X_ASSUM(MP_TAC o SPECL
        [`a(&(2 * m + 1) / &2 pow n):real^1`;
         `b(&(2 * m + 1) / &2 pow n):real^1`;
         `c(&(2 * m + 1) / &2 pow n):real^1`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
        ASM_MESON_TAC[REAL_LE_TRANS];
        REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(K ALL_TAC)] THEN
      SUBGOAL_THEN
       `(f:real^1->real^N)
        (rightcut (a (&(2 * m + 1) / &2 pow n):real^1)
                  (b (&(2 * m + 1) / &2 pow n):real^1)
                  (c (&(2 * m + 1) / &2 pow n):real^1)) =
        (f:real^1->real^N) (c(&(2 * m + 1) / &2 pow n))`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_LT_LE] THEN ASM_REWRITE_TAC[DROP_EQ] THEN
      REPEAT CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_THEN
         `(f:real^1->real^N) (b (&(2 * m + 1) / &2 pow n)) =
          f(c (&(2 * m + 1) / &2 pow n))` (MP_TAC o SYM) THEN
        REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC_ALL) THEN
        REWRITE_TAC[GSYM(ASSUME `!x. midpoint ((a:real->real^1) x,b x) = c x`);
                    midpoint; DROP_CMUL; DROP_ADD] THEN
        ASM_REWRITE_TAC[REAL_ARITH
         `a <= inv(&2) * (a + b) /\ inv(&2) * (a + b) < b <=> a < b`];
        GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM
         (fun th -> MATCH_MP_TAC th THEN
                    REWRITE_TAC[IN_INTERVAL_1; IN_DELETE; GSYM DROP_EQ] THEN
             GEN_REWRITE_TAC I [REAL_ARITH
              `(a <= x /\ x <= b) /\ ~(x = a) <=> a < x /\ x <= b`]) THEN
        ASM_REWRITE_TAC[];
        GEN_TAC THEN STRIP_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC_ALL) THEN
        ASM_MESON_TAC[REAL_LE_TRANS]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m i n j. 0 < i /\ i < 2 EXP m /\ 0 < j /\ j < 2 EXP n /\
              &i / &2 pow m < &j / &2 pow n
              ==> drop(c(&i / &2 pow m)) <= drop(c(&j / &2 pow n))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!N m p i k.
         0 < i /\ i < 2 EXP m /\ 0 < k /\ k < 2 EXP p /\
         &i / &2 pow m < &k / &2 pow p /\ m + p = N
         ==> ?j n. ODD(j) /\ ~(n = 0) /\
                   &i / &2 pow m <= &j / &2 pow n /\
                   &j / &2 pow n <= &k / &2 pow p /\
                   abs(&i / &2 pow m - &j / &2 pow n) < inv(&2 pow n) /\
                   abs(&k / &2 pow p - &j / &2 pow n) < inv(&2 pow n)`
    MP_TAC THENL
     [MATCH_MP_TAC num_WF THEN X_GEN_TAC `N:num` THEN
      DISCH_THEN(LABEL_TAC "I") THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `p:num`; `i:num`; `k:num`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       `&i / &2 pow m <= &1 / &2 pow 1 /\
        &1 / &2 pow 1 <= &k / &2 pow p \/
        &k / &2 pow p < &1 / &2 \/
        &1 / &2 < &i / &2 pow m`
       (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC)
      THENL
       [ASM_REAL_ARITH_TAC;
        MAP_EVERY EXISTS_TAC [`1`; `1`] THEN ASM_REWRITE_TAC[ARITH] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 < i /\ i <= &1 / &2 pow 1 /\ &1 / &2 pow 1 <= k /\ k < &1
          ==> abs(i -  &1 / &2 pow 1) < inv(&2 pow 1) /\
              abs(k -  &1 / &2 pow 1) < inv(&2 pow 1)`) THEN
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN
        REWRITE_TAC[MULT_CLAUSES; REAL_OF_NUM_POW; REAL_OF_NUM_MUL] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LT];
        REMOVE_THEN "I" MP_TAC THEN
        POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
        SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
        REWRITE_TAC[ARITH_RULE `i < 2 EXP 0 <=> ~(0 < i)`] THEN
        REWRITE_TAC[TAUT `p /\ ~p /\ q <=> F`] THEN POP_ASSUM(K ALL_TAC) THEN
        SPEC_TAC(`p:num`,`p:num`) THEN INDUCT_TAC THEN
        REWRITE_TAC[ARITH_RULE `i < 2 EXP 0 <=> ~(0 < i)`] THEN
        REWRITE_TAC[TAUT `p /\ ~p /\ q <=> F`] THEN POP_ASSUM(K ALL_TAC) THEN
        STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC `m + p:num`) THEN
        ANTS_TAC THENL [EXPAND_TAC "N" THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`m:num`; `p:num`; `i:num`; `k:num`]) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`&k / &2 pow SUC p < &1 / &2`;
            `&i / &2 pow SUC m < &k / &2 pow SUC p`] THEN
          REWRITE_TAC[real_div; real_pow; REAL_INV_MUL;
                      REAL_ARITH `x * inv(&2) * y = (x * y) * inv(&2)`] THEN
          SIMP_TAC[GSYM real_div; REAL_LT_DIV2_EQ; REAL_OF_NUM_LT; ARITH] THEN
          REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
           `x < y /\ y < &1 ==> x < &1 /\ y < &1`)) THEN
          SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_POW2; REAL_MUL_LID] THEN
          REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT];
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:num` THEN
          DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[NOT_SUC] THEN
          REWRITE_TAC[real_div; real_pow; REAL_INV_MUL;
                      REAL_ARITH `inv(&2) * y = y * inv(&2)`] THEN
          REWRITE_TAC[GSYM REAL_SUB_RDISTRIB; REAL_MUL_ASSOC;
                      REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
          REWRITE_TAC[GSYM real_div; REAL_ABS_NUM] THEN
          ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ;
                       REAL_OF_NUM_LT; ARITH]];
        REMOVE_THEN "I" MP_TAC THEN
        POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
        SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
        REWRITE_TAC[ARITH_RULE `i < 2 EXP 0 <=> ~(0 < i)`] THEN
        REWRITE_TAC[TAUT `p /\ ~p /\ q <=> F`] THEN POP_ASSUM(K ALL_TAC) THEN
        SPEC_TAC(`p:num`,`p:num`) THEN INDUCT_TAC THEN
        REWRITE_TAC[ARITH_RULE `i < 2 EXP 0 <=> ~(0 < i)`] THEN
        REWRITE_TAC[TAUT `p /\ ~p /\ q <=> F`] THEN POP_ASSUM(K ALL_TAC) THEN
        STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC `m + p:num`) THEN
        ANTS_TAC THENL [EXPAND_TAC "N" THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL
         [`m:num`; `p:num`; `i - 2 EXP m`; `k - 2 EXP p`]) THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`&1 / &2 < &i / &2 pow SUC m`;
          `&i / &2 pow SUC m < &k / &2 pow SUC p`] THEN
        REWRITE_TAC[real_div; real_pow; REAL_INV_MUL;
                    REAL_ARITH `x * inv(&2) * y = (x * y) * inv(&2)`] THEN
        SIMP_TAC[GSYM real_div; REAL_LT_DIV2_EQ; REAL_OF_NUM_LT; ARITH] THEN
        GEN_REWRITE_TAC I [IMP_IMP] THEN DISCH_THEN(fun th ->
          STRIP_ASSUME_TAC th THEN MP_TAC(MATCH_MP
           (REAL_ARITH `i < k /\ &1 < i ==> &1 < i /\ &1 < k`) th)) THEN
        SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_POW2; REAL_MUL_LID] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_OF_NUM_POW] THEN
        SIMP_TAC[REAL_OF_NUM_LT; GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
        STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN ANTS_TAC THENL
         [ASM_SIMP_TAC[ARITH_RULE `a < b ==> 0 < b - a`] THEN
          ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
          REWRITE_TAC[real_div; REAL_SUB_RDISTRIB] THEN
          ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LT_POW2] THEN
          ASM_REWRITE_TAC[REAL_ARITH `u * inv v - &1 < w * inv z - &1 <=>
                                      u / v < w / z`] THEN
          CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
           `i < 2 * m ==> i - m < m`) THEN
          ASM_REWRITE_TAC[GSYM(CONJUNCT2 EXP)];
          REWRITE_TAC[real_div; REAL_SUB_RDISTRIB] THEN
          ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LT_POW2] THEN
          REWRITE_TAC[GSYM real_div] THEN
          DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `n:num`
           STRIP_ASSUME_TAC)) THEN
          EXISTS_TAC `2 EXP n + j` THEN EXISTS_TAC `SUC n` THEN
          ASM_REWRITE_TAC[NOT_SUC; ODD_ADD; ODD_EXP; ARITH] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
          REWRITE_TAC[real_div; real_pow; REAL_INV_MUL;
                      REAL_ARITH `inv(&2) * y = y * inv(&2)`] THEN
          REWRITE_TAC[GSYM REAL_SUB_RDISTRIB; REAL_MUL_ASSOC;
                      REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
          REWRITE_TAC[GSYM real_div; REAL_ABS_NUM] THEN
          ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ;
                       REAL_OF_NUM_LT; ARITH] THEN
          REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
          ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LT_POW2] THEN
          REWRITE_TAC[GSYM real_div] THEN ASM_REAL_ARITH_TAC]];
      DISCH_THEN(fun th ->
       MAP_EVERY X_GEN_TAC [`m:num`; `i:num`; `p:num`; `k:num`] THEN
       STRIP_TAC THEN MP_TAC(ISPECL
        [`m + p:num`; `m:num`; `p:num`; `i:num`; `k:num`] th)) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
      REWRITE_TAC[ADD1; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `q:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `drop(c(&(2 * q + 1) / &2 pow n))` THEN CONJ_TAC THENL
       [ASM_CASES_TAC `&i / &2 pow m = &(2 * q + 1) / &2 pow n` THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        SUBGOAL_THEN
         `drop(a(&(4 * q + 1) / &2 pow (n + 1))) <= drop(c(&i / &2 pow m)) /\
          drop(c(&i / &2 pow m)) <= drop(b(&(4 * q + 1) / &2 pow (n + 1)))`
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN
          SIMP_TAC[real_div; REAL_POW_ADD; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
          REWRITE_TAC[GSYM real_div; REAL_POW_1] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `abs(i - q) < n
            ==> i <= q /\ ~(i = q) /\ q = q' + n / &2
                ==> abs(i - q') < n / &2`)) THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
          REAL_ARITH_TAC;
          ASM_SIMP_TAC[LE_1] THEN MATCH_MP_TAC(REAL_ARITH
           `l <= d ==> u <= v /\ c <= l ==> c <= d`) THEN
          FIRST_X_ASSUM(MP_TAC o SPECL
           [`a(&(2 * q + 1) / &2 pow n):real^1`;
            `b(&(2 * q + 1) / &2 pow n):real^1`;
            `c(&(2 * q + 1) / &2 pow n):real^1`]) THEN
          ANTS_TAC THENL
           [REWRITE_TAC[IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
            ASM_MESON_TAC[REAL_LE_TRANS];
            DISCH_THEN(fun th -> REWRITE_TAC[th])]];
        ASM_CASES_TAC `&k / &2 pow p = &(2 * q + 1) / &2 pow n` THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        SUBGOAL_THEN
         `drop(a(&(4 * q + 3) / &2 pow (n + 1))) <= drop(c(&k / &2 pow p)) /\
          drop(c(&k / &2 pow p)) <= drop(b(&(4 * q + 3) / &2 pow (n + 1)))`
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN
          SIMP_TAC[real_div; REAL_POW_ADD; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
          REWRITE_TAC[GSYM real_div; REAL_POW_1] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `abs(i - q) < n
            ==> q <= i /\ ~(i = q) /\ q' = q +  n / &2
                ==> abs(i - q') < n / &2`)) THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
          REAL_ARITH_TAC;
          ASM_SIMP_TAC[LE_1] THEN MATCH_MP_TAC(REAL_ARITH
           `d <= l ==> l <= c /\ u <= v ==> d <= c`) THEN
          FIRST_X_ASSUM(MP_TAC o SPECL
           [`a(&(2 * q + 1) / &2 pow n):real^1`;
            `b(&(2 * q + 1) / &2 pow n):real^1`;
            `c(&(2 * q + 1) / &2 pow n):real^1`]) THEN
          ANTS_TAC THENL
           [REWRITE_TAC[IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
            ASM_MESON_TAC[REAL_LE_TRANS];
            DISCH_THEN(fun th -> REWRITE_TAC[th])]]]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_LIFT] THEN MATCH_MP_TAC REAL_WLOG_LT THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_DROP; LIFT_DROP; IN_INTERVAL_1; DROP_VEC] THEN
  MAP_EVERY X_GEN_TAC [`x1:real^1`; `x2:real^1`] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?m n. 0 < m /\ m < 2 EXP n /\
          drop x1 < &m / &2 pow n /\ &m / &2 pow n < drop x2 /\
          ~(h(x1):real^N = h(lift(&m / &2 pow n)))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `interval(vec 0:real^1,vec 1)`
        closure_dyadic_rationals_in_convex_set_pos_1) THEN
    SIMP_TAC[CONVEX_INTERVAL; IN_INTERVAL_1; REAL_LT_IMP_LE; DROP_VEC;
            INTERIOR_OPEN; OPEN_INTERVAL; INTERVAL_NE_EMPTY_1; REAL_LT_01;
            CLOSURE_OPEN_INTERVAL] THEN
    REWRITE_TAC[EXTENSION] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(&2) % (x1 + x2):real^1`) THEN
    REWRITE_TAC[dyadics_in_open_unit_interval; IN_INTERVAL_1; DROP_VEC] THEN
    REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (q <=> p) ==> r`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[CLOSURE_APPROACHABLE]] THEN
    DISCH_THEN(MP_TAC o SPEC `(drop x2 - drop x1) / &64`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[EXISTS_IN_GSPEC]] THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP; DROP_CMUL; DROP_ADD] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `?m n. (0 < m /\ m < 2 EXP n) /\
            abs(&m / &2 pow n - inv (&2) * (drop x1 + drop x2)) <
            (drop x2 - drop x1) / &64 /\
            inv(&2 pow n) < (drop x2 - drop x1) / &128`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`inv(&2)`; `min (&1 / &4) ((drop x2 - drop x1) / &128)`]
      REAL_ARCH_POW_INV) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
      ASM_CASES_TAC `N = 0` THENL
       [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_INV_POW; REAL_LT_MIN; EXISTS_IN_GSPEC] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `n:num`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `2 EXP N * m` THEN EXISTS_TAC `N + n:num` THEN
      ASM_SIMP_TAC[EXP_ADD; LT_MULT; EXP_LT_0; LT_MULT_LCANCEL; LE_1;
                   ARITH_EQ] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; REAL_ARITH
         `(N * n) * inv N * inv m:real = (N / N) * (n / m)`] THEN
        ASM_SIMP_TAC[REAL_DIV_REFL; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ;
                     REAL_MUL_LID; GSYM real_div];
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&2) pow N` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LE_ADD]];
      REWRITE_TAC[CONJ_ASSOC] THEN MATCH_MP_TAC(MESON[]
       `!m n m' n'. (P m n /\ P m' n') /\
                    (P m n /\ P m' n' ==> ~(g m n = g m' n'))
        ==> (?m n. P m n /\ ~(a = g m n))`) THEN
      MAP_EVERY EXISTS_TAC
       [`2 * m + 1`; `n + 1`; `4 * m + 3`; `n + 2`] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THEN
        (REWRITE_TAC[GSYM CONJ_ASSOC] THEN
         REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC])) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `abs(x - inv(&2) * (x1 + x2)) < (x2 - x1) / &64
          ==> abs(x - y) < (x2 - x1) / &4
              ==> x1 < y /\ y < x2`)) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `n < x / &128 ==> &0 < x /\ y < &4 * n ==> y < x / &4`)) THEN
        ASM_REWRITE_TAC[REAL_SUB_LT] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        MATCH_MP_TAC(REAL_ARITH
         `a / y = x /\ abs(b / y) < z
          ==> abs(x - (a + b) / y) < z`) THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[REAL_POW_ADD] THEN
        SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_MUL; REAL_ABS_POW] THEN
        REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
        SIMP_TAC[REAL_LT_RMUL_EQ; REAL_EQ_MUL_RCANCEL; REAL_LT_INV_EQ;
           REAL_LT_POW2; REAL_INV_EQ_0; REAL_POW_EQ_0; ARITH_EQ;
           REAL_OF_NUM_EQ] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o SPECL [`n + 2`; `4 * m + 3`]) THEN
        UNDISCH_THEN `!x. midpoint ((a:real->real^1) x,b x) = c x`
         (fun th -> REWRITE_TAC[GSYM th] THEN
              ASM_SIMP_TAC[ARITH_RULE `n + 2 = (n + 1) + 1 /\ 0 < n + 1`] THEN
              REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
        DISCH_TAC THEN
        CONV_TAC(RAND_CONV SYM_CONV) THEN
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`a(&(2 * m + 1) / &2 pow (n + 1)):real^1`;
          `b(&(2 * m + 1) / &2 pow (n + 1)):real^1`;
          `c(&(2 * m + 1) / &2 pow (n + 1)):real^1`]) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
          ASM_MESON_TAC[REAL_LE_TRANS];
          REPLICATE_TAC 6 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
          DISCH_THEN(MATCH_MP_TAC o CONJUNCT1)] THEN
        REWRITE_TAC[IN_INTERVAL_1; IN_DELETE; GSYM DROP_EQ] THEN
        REWRITE_TAC[REAL_ARITH
         `(a <= b /\ b <= c) /\ ~(b = a) <=> a < b /\ b <= c`] THEN
        REWRITE_TAC[midpoint; DROP_CMUL; DROP_ADD] THEN
        ASM_REWRITE_TAC[REAL_ARITH
           `a < inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a < b`] THEN
        ASM_REWRITE_TAC[REAL_LT_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE h (interval[vec 0,lift(&m / &2 pow n)]) SUBSET
    IMAGE (f:real^1->real^N) (interval[vec 0,c(&m / &2 pow n)]) /\
    IMAGE h (interval[lift(&m / &2 pow n),vec 1]) SUBSET
    IMAGE (f:real^1->real^N) (interval[c(&m / &2 pow n),vec 1])`
  MP_TAC THENL
   [MP_TAC(ISPEC `interval(lift(&m / &2 pow n),vec 1)`
      closure_dyadic_rationals_in_convex_set_pos_1) THEN
    MP_TAC(ISPEC `interval(vec 0,lift(&m / &2 pow n))`
      closure_dyadic_rationals_in_convex_set_pos_1) THEN
    SUBGOAL_THEN `&0 < &m / &2 pow n /\ &m / &2 pow n < &1`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_POW2; REAL_OF_NUM_LT; REAL_LT_LDIV_EQ;
        REAL_OF_NUM_MUL; REAL_OF_NUM_LT; REAL_OF_NUM_POW; MULT_CLAUSES];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT
     `(p1 /\ p2) /\ (q1 ==> r1) /\ (q2 ==> r2)
      ==> (p1 ==> q1) ==> (p2 ==> q2) ==> r1 /\ r2`) THEN
    ASM_SIMP_TAC[CONVEX_INTERVAL; IN_INTERVAL_1; REAL_LT_IMP_LE; DROP_VEC;
     INTERIOR_OPEN; OPEN_INTERVAL; INTERVAL_NE_EMPTY_1; REAL_LT_01;
     CLOSURE_OPEN_INTERVAL; LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    (MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REPEAT CONJ_TAC THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         CONTINUOUS_ON_SUBSET)) THEN
       MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_INTERVAL] THEN
       MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
       ASM_SIMP_TAC[SUBSET_INTERVAL_1; LIFT_DROP; REAL_LT_IMP_LE; DROP_VEC;
                    REAL_LE_REFL];
       MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
       MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
       ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         CONTINUOUS_ON_SUBSET)) THEN
       REWRITE_TAC[SUBSET_INTERVAL_1; REAL_LE_REFL] THEN
       ASM_MESON_TAC[REAL_LE_TRANS];
       REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
       MATCH_MP_TAC(SET_RULE
        `i SUBSET interval(vec 0,vec 1) /\
         (!x. x IN interval(vec 0,vec 1) INTER l ==> x IN i ==> P x)
         ==> !x. x IN i INTER l ==> P x`) THEN
       ASM_SIMP_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC;
                    REAL_LT_IMP_LE; REAL_LE_REFL] THEN
       REWRITE_TAC[dyadics_in_open_unit_interval; FORALL_IN_GSPEC] THEN
       MAP_EVERY X_GEN_TAC [`k:num`; `p:num`] THEN STRIP_TAC THEN
       REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
       STRIP_TAC THEN ASM_SIMP_TAC[] THEN
       MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1] THEN
       ASM_SIMP_TAC[] THEN ASM_MESON_TAC[REAL_LE_TRANS]]);
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `IMAGE h s SUBSET t /\ IMAGE h s' SUBSET t'
      ==> !x y. x IN s /\ y IN s' ==> h(x) IN t /\ h(y) IN t'`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`x1:real^1`; `x2:real^1`]) THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; REAL_LT_IMP_LE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `a IN IMAGE f s /\ a IN IMAGE f t
      ==> ?x y. x IN s /\ y IN t /\ f x = a /\ f y = a`)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t1:real^1`; `t2:real^1`] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(h:real^1->real^N) x2` o
     GEN_REWRITE_RULE BINDER_CONV [GSYM IS_INTERVAL_CONNECTED_1]) THEN
    REWRITE_TAC[IS_INTERVAL_1; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`t1:real^1`; `t2:real^1`; `c(&m / &2 pow n):real^1`]) THEN
    UNDISCH_TAC `~(h x1:real^N = h(lift (&m / &2 pow n)))` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC(TAUT `q ==> p ==> ~q ==> r`) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    ASM_MESON_TAC[REAL_LE_TRANS]]);;

let PATH_CONTAINS_ARC = prove
 (`!p:real^1->real^N a b.
        path p /\ pathstart p = a /\ pathfinish p = b /\ ~(a = b)
        ==> ?q. arc q /\ path_image q SUBSET path_image p /\
                pathstart q = a /\ pathfinish q = b`,
  REWRITE_TAC[pathstart; pathfinish; path] THEN
  MAP_EVERY X_GEN_TAC [`f:real^1->real^N`; `a:real^N`; `b:real^N`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`\s. s SUBSET interval[vec 0,vec 1] /\
         vec 0 IN s /\ vec 1 IN s /\
         (!x y. x IN s /\ y IN s /\ segment(x,y) INTER s = {}
                ==> (f:real^1->real^N)(x) = f(y))`;
    `interval[vec 0:real^1,vec 1]`]
  BROUWER_REDUCTION_THEOREM_GEN) THEN
  ASM_REWRITE_TAC[GSYM path_image; CLOSED_INTERVAL; SUBSET_REFL] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
       `s INTER i = {} ==> s SUBSET i ==> s = {}`)) THEN
      REWRITE_TAC[SEGMENT_EQ_EMPTY] THEN
      ANTS_TAC THENL [ONCE_REWRITE_TAC[segment]; MESON_TAC[]] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF i SUBSET t`) THEN
      ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT; CONVEX_INTERVAL]] THEN
    X_GEN_TAC `s:num->real^1->bool` THEN
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[INTERS_GSPEC; SUBSET; IN_ELIM_THM; IN_UNIV] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[FORALL_LIFT] THEN MATCH_MP_TAC REAL_WLOG_LT THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SEGMENT_SYM] THEN MESON_TAC[];
      REWRITE_TAC[FORALL_DROP; LIFT_DROP]] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[INTERS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
    SIMP_TAC[SEGMENT_1; REAL_LT_IMP_LE] THEN DISCH_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        COMPACT_UNIFORMLY_CONTINUOUS)) THEN
    REWRITE_TAC[COMPACT_INTERVAL; uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `norm((f:real^1->real^N) x - f y) / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?u v. u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
            norm(u - x) < e /\ norm(v - y) < e /\ (f:real^1->real^N) u = f v`
    STRIP_ASSUME_TAC THENL
     [ALL_TAC;
      FIRST_X_ASSUM(fun th ->
        MP_TAC(ISPECL [`x:real^1`; `u:real^1`] th) THEN
        MP_TAC(ISPECL [`y:real^1`; `v:real^1`] th)) THEN
      ASM_REWRITE_TAC[dist] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `q /\ (p ==> ~r) ==> p ==> ~(q ==> r)`) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; CONV_TAC NORM_ARITH]] THEN
    SUBGOAL_THEN
     `?w z. w IN interval(x,y) /\ z IN interval(x,y) /\ drop w < drop z /\
            norm(w - x) < e /\ norm(z - y) < e`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `x + lift(min e (drop y - drop x) / &3)` THEN
      EXISTS_TAC `y - lift(min e (drop y - drop x) / &3)` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_SUB; LIFT_DROP;
                  NORM_REAL; GSYM drop] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`interval[w:real^1,z]`;
                   `{s n :real^1->bool | n IN (:num)}`] COMPACT_IMP_FIP) THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL; FORALL_IN_GSPEC] THEN
    MATCH_MP_TAC(TAUT `q /\ (~p ==> r) ==> (p ==> ~q) ==> r`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INTERS_GSPEC; IN_UNIV] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
       MATCH_MP (SET_RULE
        `s INTER u = {} ==> t SUBSET s ==> t INTER u = {}`)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MESON[] `~(!x. P x /\ Q x ==> R x) <=>
                         (?x. P x /\ Q x /\ ~R x)`] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\n:num. n` o MATCH_MP
      UPPER_BOUND_FINITE_SET) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `interval[w,z] INTER (s:num->real^1->bool) n = {}`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `a INTER t = {} ==> s SUBSET t ==> a INTER s = {}`)) THEN
      REWRITE_TAC[SUBSET; INTERS_IMAGE; IN_ELIM_THM] THEN
      REWRITE_TAC[SET_RULE
       `(!x. x IN s n ==> !i. i IN k ==> x IN s i) <=>
        (!i. i IN k ==> s n SUBSET s i)`] THEN
      SUBGOAL_THEN
       `!i n. i <= n ==> (s:num->real^1->bool) n SUBSET s i`
       (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?u. u IN (s:num->real^1->bool) n /\ u IN interval[x,w] /\
          (interval[u,w] DELETE u) INTER (s n) = {}`
    MP_TAC THENL
     [ASM_CASES_TAC `w IN (s:num->real^1->bool) n` THENL
       [EXISTS_TAC `w:real^1` THEN ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
        REWRITE_TAC[INTERVAL_SING; SET_RULE `{a} DELETE a = {}`] THEN
        REWRITE_TAC[INTER_EMPTY; INTERVAL_NE_EMPTY_1] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`(s:num->real^1->bool) n INTER interval[x,w]`;
                   `w:real^1`] SEGMENT_TO_POINT_EXISTS) THEN
      ASM_SIMP_TAC[CLOSED_INTER; CLOSED_INTERVAL] THEN ANTS_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^1` THEN
        ASM_REWRITE_TAC[IN_INTER; IN_INTERVAL_1] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^1` THEN
        REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
         `s INTER t INTER u = {} ==> s SUBSET u ==> s INTER t = {}`)) THEN
        REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
          ASM_MESON_TAC[DROP_EQ; REAL_LE_ANTISYM];
          ANTS_TAC THENL
           [REWRITE_TAC[SUBSET_INTERVAL_1] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
            ASM_REAL_ARITH_TAC;
            REWRITE_TAC[OPEN_CLOSED_INTERVAL_1] THEN ASM SET_TAC[]]]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?v. v IN (s:num->real^1->bool) n /\ v IN interval[z,y] /\
          (interval[z,v] DELETE v) INTER (s n) = {}`
    MP_TAC THENL
     [ASM_CASES_TAC `z IN (s:num->real^1->bool) n` THENL
       [EXISTS_TAC `z:real^1` THEN ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
        REWRITE_TAC[INTERVAL_SING; SET_RULE `{a} DELETE a = {}`] THEN
        REWRITE_TAC[INTER_EMPTY; INTERVAL_NE_EMPTY_1] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`(s:num->real^1->bool) n INTER interval[z,y]`;
                   `z:real^1`] SEGMENT_TO_POINT_EXISTS) THEN
      ASM_SIMP_TAC[CLOSED_INTER; CLOSED_INTERVAL] THEN ANTS_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^1` THEN
        ASM_REWRITE_TAC[IN_INTER; IN_INTERVAL_1] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^1` THEN
        REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
         `s INTER t INTER u = {} ==> s SUBSET u ==> s INTER t = {}`)) THEN
        REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THENL
         [ANTS_TAC THENL
           [REWRITE_TAC[SUBSET_INTERVAL_1] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
            ASM_REAL_ARITH_TAC;
            REWRITE_TAC[OPEN_CLOSED_INTERVAL_1] THEN ASM SET_TAC[]];
          RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
          ASM_MESON_TAC[DROP_EQ; REAL_LE_ANTISYM]]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[NORM_REAL; GSYM drop; DROP_SUB]) THEN
      REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[NORM_REAL; GSYM drop; DROP_SUB]) THEN
      REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`interval[w,z] INTER (s:num->real^1->bool) n = {}`;
          `interval[u,w] DELETE u INTER (s:num->real^1->bool) n = {}`;
          `interval[z,v] DELETE v INTER (s:num->real^1->bool) n = {}`] THEN
        REWRITE_TAC[IMP_IMP; SET_RULE
          `s1 INTER t = {} /\ s2 INTER t = {} <=>
           (s1 UNION s2) INTER t = {}`] THEN
        MATCH_MP_TAC(SET_RULE
         `t SUBSET s ==> s INTER u = {} ==> t INTER u = {}`) THEN
        REWRITE_TAC[SUBSET; IN_UNION; IN_DELETE;
                    GSYM DROP_EQ; IN_INTERVAL_1] THEN
        ASM_REAL_ARITH_TAC;
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `t:real^1->bool = {}` THENL
   [ASM_MESON_TAC[IN_IMAGE; NOT_IN_EMPTY]; ALL_TAC] THEN
  ABBREV_TAC
   `h = \x. (f:real^1->real^N)(@y. y IN t /\ segment(x,y) INTER t = {})` THEN
  SUBGOAL_THEN
   `!x y. y IN t /\ segment(x,y) INTER t = {} ==> h(x) = (f:real^1->real^N)(y)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!x y z. y IN t /\ segment(x,y) INTER t = {} /\
              z IN t /\ segment(x,z) INTER t = {}
              ==> (f:real^1->real^N)(y) = f(z)`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN ASM_CASES_TAC `(x:real^1) IN t` THENL
       [ASM_MESON_TAC[]; UNDISCH_TAC `~((x:real^1) IN t)`] THEN
      ONCE_REWRITE_TAC[TAUT `p ==> a /\ b /\ c /\ d ==> q <=>
                             (a /\ c) ==> p /\ b /\ d ==> q`] THEN
      STRIP_TAC THEN
      REWRITE_TAC[SET_RULE `~(x IN t) /\ s INTER t = {} /\ s' INTER t = {} <=>
                            (x INSERT (s UNION s')) INTER t = {}`] THEN
      DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE
       `s SUBSET s' ==> s' INTER t = {} ==> s INTER t = {}`) THEN
      REWRITE_TAC[SEGMENT_1; SUBSET; IN_UNION; IN_INSERT; IN_INTERVAL_1] THEN
      GEN_TAC THEN REWRITE_TAC[GSYM DROP_EQ] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1]) THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN t ==> h(x) = (f:real^1->real^N)(x)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; INTER_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^1. ?y. y IN t /\ segment(x,y) INTER t = {}`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN
    EXISTS_TAC `closest_point t (x:real^1)` THEN
    ASM_SIMP_TAC[SEGMENT_TO_CLOSEST_POINT; CLOSEST_POINT_EXISTS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. segment(x,y) INTER t = {} ==> (h:real^1->real^N) x = h y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^1`; `x':real^1`] THEN
    ASM_CASES_TAC `(x:real^1) IN t` THENL
     [ASM_MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
    ASM_CASES_TAC `(x':real^1) IN t` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?y y'. y IN t /\ segment(x,y) INTER t = {} /\ h x = f y /\
             y' IN t /\ segment(x',y') INTER t = {} /\
             (h:real^1->real^N) x' = f y'`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC
     [`~((x:real^1) IN t)`; `~((x':real^1) IN t)`;
      `segment(x:real^1,y) INTER t = {}`;
      `segment(x':real^1,y') INTER t = {}`;
      `segment(x:real^1,x') INTER t = {}`] THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET (x1 INSERT x2 INSERT (s0 UNION s1 UNION s2))
      ==> s0 INTER t = {} ==> s1 INTER t = {} ==> s2 INTER t = {}
          ==> ~(x1 IN t) ==> ~(x2 IN t) ==> s INTER t = {}`) THEN
    REWRITE_TAC[SEGMENT_1; SUBSET; IN_UNION; IN_INSERT; IN_INTERVAL_1] THEN
      GEN_TAC THEN REWRITE_TAC[GSYM DROP_EQ] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:real^1->real^N` HOMEOMORPHIC_MONOTONE_IMAGE_INTERVAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[continuous_on] THEN X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_on]) THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^1`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
      ASM_CASES_TAC `segment(u:real^1,v) INTER t = {}` THENL
       [ASM_MESON_TAC[DIST_REFL]; ALL_TAC] THEN
      SUBGOAL_THEN
       `(?w:real^1. w IN t /\ w IN segment[u,v] /\ segment(u,w) INTER t = {}) /\
        (?z:real^1. z IN t /\ z IN segment[u,v] /\ segment(v,z) INTER t = {})`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC(ISPECL [`segment[u:real^1,v] INTER t`; `u:real^1`]
            SEGMENT_TO_POINT_EXISTS);
          MP_TAC(ISPECL [`segment[u:real^1,v] INTER t`; `v:real^1`]
          SEGMENT_TO_POINT_EXISTS)] THEN
       (ASM_SIMP_TAC[CLOSED_INTER; CLOSED_SEGMENT] THEN ANTS_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
            `~(segment(u,v) INTER t = {})
             ==> segment(u,v) SUBSET segment[u,v]
                 ==> ~(segment[u,v] INTER t = {})`)) THEN
          REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED];
          ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^1` THEN
        SIMP_TAC[IN_INTER] THEN
        MATCH_MP_TAC(SET_RULE
         `(w IN uv ==> uw SUBSET uv)
          ==> (w IN uv /\ w IN t) /\ (uw INTER uv INTER t = {})
          ==> uw INTER t = {}`) THEN
        DISCH_TAC THEN REWRITE_TAC[open_segment] THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF u SUBSET t`) THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
        REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; CONVEX_SEGMENT] THEN
        ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_SEGMENT]);
        SUBGOAL_THEN `(h:real^1->real^N) u = (f:real^1->real^N) w /\
                      (h:real^1->real^N) v = (f:real^1->real^N) z`
          (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(NORM_ARITH
         `!u. dist(w:real^N,u) < e / &2 /\ dist(z,u) < e / &2
              ==> dist(w,z) < e`) THEN
        EXISTS_TAC `(f:real^1->real^N) u` THEN CONJ_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        (CONJ_TAC THENL
          [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
            `x IN s ==> s SUBSET t ==> x IN t`)) THEN
           REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
           ASM_REWRITE_TAC[CONVEX_INTERVAL; INSERT_SUBSET; EMPTY_SUBSET];
           ASM_MESON_TAC[DIST_IN_CLOSED_SEGMENT; REAL_LET_TRANS; DIST_SYM]])];
      X_GEN_TAC `z:real^N` THEN
      REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
      MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `segment[u:real^1,v]` THEN
      REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN
      ASM_CASES_TAC `segment(u:real^1,v) INTER t = {}` THENL
       [REWRITE_TAC[SET_RULE `s SUBSET {x | x IN t /\ P x} <=>
                              s SUBSET t /\ !x. x IN s ==> P x`] THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT; CONVEX_INTERVAL];
          X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
          SUBGOAL_THEN `segment(u:real^1,x) INTER t = {}`
            (fun th -> ASM_MESON_TAC[th]) THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `uv INTER t = {} ==> ux SUBSET uv ==> ux INTER t = {}`)) THEN
          UNDISCH_TAC `(x:real^1) IN segment[u,v]` THEN
          REWRITE_TAC[SEGMENT_1] THEN
          REPEAT(COND_CASES_TAC THEN
                 ASM_REWRITE_TAC[IN_INTERVAL_1; SUBSET_INTERVAL_1]) THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t DIFF segment(u:real^1,v)`) THEN
      ASM_REWRITE_TAC[SET_RULE `t DIFF s PSUBSET t <=> ~(s INTER t = {})`] THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC CLOSED_DIFF THEN ASM_REWRITE_TAC[OPEN_SEGMENT_1];
        ASM SET_TAC[];
        ASM_REWRITE_TAC[IN_DIFF] THEN MAP_EVERY UNDISCH_TAC
         [`(u:real^1) IN interval[vec 0,vec 1]`;
          `(v:real^1) IN interval[vec 0,vec 1]`] THEN
        REWRITE_TAC[SEGMENT_1] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1]) THEN
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[IN_DIFF] THEN MAP_EVERY UNDISCH_TAC
         [`(u:real^1) IN interval[vec 0,vec 1]`;
          `(v:real^1) IN interval[vec 0,vec 1]`] THEN
        REWRITE_TAC[SEGMENT_1] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1]) THEN
        ASM_REAL_ARITH_TAC;
        MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
        REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
        ASM_CASES_TAC `segment(x:real^1,y) INTER segment(u,v) = {}` THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN
         `(segment(x:real^1,u) SUBSET segment(x,y) DIFF segment(u,v) /\
           segment(y:real^1,v) SUBSET segment(x,y) DIFF segment(u,v)) \/
          (segment(y:real^1,u) SUBSET segment(x,y) DIFF segment(u,v) /\
           segment(x:real^1,v) SUBSET segment(x,y) DIFF segment(u,v))`
        MP_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`~(x IN segment(u:real^1,v))`; `~(y IN segment(u:real^1,v))`;
            `~(segment(x:real^1,y) INTER segment (u,v) = {})`] THEN
          POP_ASSUM_LIST(K ALL_TAC) THEN
          MAP_EVERY (fun t -> SPEC_TAC(t,t))
           [`v:real^1`; `u:real^1`; `y:real^1`; `x:real^1`] THEN
          REWRITE_TAC[FORALL_LIFT] THEN
          MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
           [REWRITE_TAC[SEGMENT_SYM] THEN MESON_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[FORALL_DROP; LIFT_DROP] THEN
          MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN DISCH_TAC THEN
          REWRITE_TAC[FORALL_LIFT] THEN
          MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
           [REWRITE_TAC[SEGMENT_SYM] THEN MESON_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[FORALL_DROP; LIFT_DROP] THEN
          MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
          ASM_REWRITE_TAC[SEGMENT_1] THEN
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
          REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
          REWRITE_TAC[IN_INTERVAL_1; SUBSET; IN_DIFF; AND_FORALL_THM] THEN
          ASM_REAL_ARITH_TAC;
          DISCH_THEN(DISJ_CASES_THEN(CONJUNCTS_THEN
           (let sl = SET_RULE
             `i SUBSET xy DIFF uv
              ==> xy INTER (t DIFF uv) = {} ==> i INTER t = {}` in
            fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP (MATCH_MP sl th))))) THEN
          ASM_MESON_TAC[]]];
      ASM_MESON_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `?q:real^1->real^N.
        arc q /\ path_image q SUBSET path_image f /\
        a IN path_image q /\ b IN path_image q`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
    REWRITE_TAC[homeomorphism] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^1->real^N` THEN
    REWRITE_TAC[arc; path; path_image] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM MESON_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; path_image] THEN ASM SET_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^1` THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 1:real^1` THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN ASM_MESON_TAC[]];
    SUBGOAL_THEN
     `?u v. u IN interval[vec 0,vec 1] /\ a = (q:real^1->real^N) u /\
            v IN interval[vec 0,vec 1] /\ b = (q:real^1->real^N) v`
    STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[path_image]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `subpath u v (q:real^1->real^N)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
      ASM_MESON_TAC[ARC_IMP_SIMPLE_PATH];
      ASM_MESON_TAC[SUBSET_TRANS; PATH_IMAGE_SUBPATH_SUBSET; ARC_IMP_PATH];
      ASM_MESON_TAC[pathstart; PATHSTART_SUBPATH];
      ASM_MESON_TAC[pathfinish; PATHFINISH_SUBPATH]]]);;

let PATH_CONNECTED_ARCWISE = prove
 (`!s:real^N->bool.
        path_connected s <=>
        !x y. x IN s /\ y IN s /\ ~(x = y)
              ==> ?g. arc g /\
                      path_image g SUBSET s /\
                      pathstart g = x /\
                      pathfinish g = y`,
  GEN_TAC THEN REWRITE_TAC[path_connected] THEN EQ_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`g:real^1->real^N`; `x:real^N`; `y:real^N`]
        PATH_CONTAINS_ARC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ASM_CASES_TAC `y:real^N = x` THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `linepath(y:real^N,y)` THEN
      ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                      PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET];
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[ARC_IMP_PATH]]]);;

let ARC_CONNECTED_TRANS = prove
 (`!g h:real^1->real^N.
        arc g /\ arc h /\
        pathfinish g = pathstart h /\ ~(pathstart g = pathfinish h)
        ==> ?i. arc i /\
                path_image i SUBSET (path_image g UNION path_image h) /\
                pathstart i = pathstart g /\
                pathfinish i = pathfinish h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g ++ h:real^1->real^N`; `pathstart(g):real^N`;
                 `pathfinish(h):real^N`] PATH_CONTAINS_ARC) THEN
  ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATH_JOIN_EQ; ARC_IMP_PATH;
               PATH_IMAGE_JOIN]);;

(* ------------------------------------------------------------------------- *)
(* Local versions of topological properties in general.                      *)
(* ------------------------------------------------------------------------- *)

let locally = new_definition
 `locally P (s:real^N->bool) <=>
        !w x. open_in (subtopology euclidean s) w /\ x IN w
              ==> ?u v. open_in (subtopology euclidean s) u /\ P v /\
                        x IN u /\ u SUBSET v /\ v SUBSET w`;;

let LOCALLY_MONO = prove
 (`!P Q s. (!t. P t ==> Q t) /\ locally P s ==> locally Q s`,
  REWRITE_TAC[locally] THEN MESON_TAC[]);;

let LOCALLY_OPEN_SUBSET = prove
 (`!P s t:real^N->bool.
        locally P s /\ open_in (subtopology euclidean s) t
        ==> locally P t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`w:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N->bool`; `x:real^N`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_TRANS]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[open_in; SUBSET]);;

let LOCALLY_DIFF_CLOSED = prove
 (`!P s t:real^N->bool.
        locally P s /\ closed_in (subtopology euclidean s) t
        ==> locally P (s DIFF t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_DIFF THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; SUBSET_UNIV; TOPSPACE_EUCLIDEAN]);;

let LOCALLY_EMPTY = prove
 (`!P. locally P {}`,
  REWRITE_TAC[locally] THEN MESON_TAC[open_in; SUBSET; NOT_IN_EMPTY]);;

let LOCALLY_SING = prove
 (`!P a. locally P {a} <=> P {a}`,
  REWRITE_TAC[locally; open_in] THEN
  REWRITE_TAC[SET_RULE
   `(w SUBSET {a} /\ P) /\ x IN w <=> w = {a} /\ x = a /\ P`] THEN
  SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2; IN_SING] THEN
  REWRITE_TAC[SET_RULE
   `(u SUBSET {a} /\ P) /\ Q /\ a IN u /\ u SUBSET v /\ v SUBSET {a} <=>
    u = {a} /\ v = {a} /\ P /\ Q`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2; IN_SING] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; MESON[REAL_LT_01] `?x. &0 < x`]);;

let LOCALLY_INTER = prove
 (`!P:(real^N->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> !s t. locally P s /\ locally P t ==> locally P (s INTER t)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[locally; OPEN_IN_OPEN] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC; MESON[]
   `(!w x. (?t. P t /\ w = f t) /\ Q w x ==> R w x) <=>
    (!t x. P t /\ Q (f t) x ==> R (f t) x)`] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(?a b c. P a b c /\ Q a b c /\ R a b c) <=>
    (?b c a. Q a b c /\ P a b c /\ R a b c)`] THEN
  REWRITE_TAC[AND_FORALL_THM; UNWIND_THM2; IN_INTER] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `w:real^N->bool` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u1:real^N->bool` (X_CHOOSE_THEN `v1:real^N->bool`
        STRIP_ASSUME_TAC))
   (X_CHOOSE_THEN `u2:real^N->bool` (X_CHOOSE_THEN `v2:real^N->bool`
        STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `u1 INTER u2:real^N->bool` THEN
  EXISTS_TAC `v1 INTER v2:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER] THEN ASM SET_TAC[]);;

let HOMEOMORPHISM_LOCALLY = prove
 (`!P Q f:real^N->real^M g.
        (!s t. homeomorphism (s,t) (f,g) ==> (P s <=> Q t))
        ==> (!s t. homeomorphism (s,t) (f,g)
                   ==> (locally P s <=> locally Q t))`,

  let lemma = prove
   (`!P Q f g.
        (!s t. P s /\ homeomorphism (s,t) (f,g) ==> Q t)
        ==> (!s:real^N->bool t:real^M->bool.
                locally P s /\ homeomorphism (s,t) (f,g) ==> locally Q t)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[locally] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    MAP_EVERY X_GEN_TAC [`w:real^M->bool`; `y:real^M`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`IMAGE (g:real^M->real^N) w`; `(g:real^M->real^N) y`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      SUBGOAL_THEN `IMAGE (g:real^M->real^N) w =
                     {x | x IN s /\ f(x) IN w}`
      SUBST1_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[open_in]) THEN ASM SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_IMP_OPEN_IN THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`IMAGE (f:real^N->real^M) u`; `IMAGE (f:real^N->real^M) v`] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (f:real^N->real^M) u =
                     {x | x IN t /\ g(x) IN u}`
      SUBST1_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[open_in]) THEN ASM SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_IMP_OPEN_IN THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `v:real^N->bool` THEN
      ASM_REWRITE_TAC[homeomorphism] THEN
      REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THEN
      TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)));
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[open_in]) THEN ASM SET_TAC[]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM;
        TAUT `p ==> q /\ r ==> s <=> p /\ r ==> q ==> s`] lemma) THEN
  ASM_MESON_TAC[HOMEOMORPHISM_SYM]);;

let HOMEOMORPHIC_LOCALLY = prove
 (`!P Q. (!s:real^N->bool t:real^M->bool. s homeomorphic t ==> (P s <=> Q t))
         ==> (!s t. s homeomorphic t ==> (locally P s <=> locally Q t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[homeomorphic; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(!a b c d. P a b c d) <=> (!c d a b. P a b c d)`] THEN
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_LOCALLY THEN
  ASM_MESON_TAC[homeomorphic]);;

let LOCALLY_TRANSLATION = prove
 (`!P:(real^N->bool)->bool.
        (!a s. P (IMAGE (\x. a + x) s) <=> P s)
        ==> (!a s. locally P (IMAGE (\x. a + x) s) <=> locally P s)`,
  GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MP_TAC(ISPECL
   [`P:(real^N->bool)->bool`; `P:(real^N->bool)->bool`;
    `\x:real^N. a + x`; `\x:real^N. --a + x`]
     HOMEOMORPHISM_LOCALLY) THEN
  REWRITE_TAC[homeomorphism] THEN
  SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
  REWRITE_TAC[FORALL_UNWIND_THM1; IMP_CONJ; GSYM IMAGE_o; o_DEF; IMAGE_ID;
              VECTOR_ARITH `--a + a + x:real^N = x /\ a + --a + x = x`] THEN
  MESON_TAC[]);;

let LOCALLY_INJECTIVE_LINEAR_IMAGE = prove
 (`!P:(real^N->bool)->bool Q:(real^M->bool)->bool.
        (!f s. linear f /\ (!x y. f x = f y ==> x = y)
               ==> (P (IMAGE f s) <=> Q s))
        ==>  (!f s. linear f /\ (!x y. f x = f y ==> x = y)
                    ==> (locally P (IMAGE f s) <=> locally Q s))`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  ASM_CASES_TAC `linear(f:real^M->real^N) /\ (!x y. f x = f y ==> x = y)` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`Q:(real^M->bool)->bool`; `P:(real^N->bool)->bool`;
    `f:real^M->real^N`; `g:real^N->real^M`]
     HOMEOMORPHISM_LOCALLY) THEN
  ASM_SIMP_TAC[homeomorphism; LINEAR_CONTINUOUS_ON] THEN
  ASM_REWRITE_TAC[FORALL_UNWIND_THM1; IMP_CONJ; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID] THEN MESON_TAC[]);;

let LOCALLY_OPEN_MAP_IMAGE = prove
 (`!P Q f:real^M->real^N s.
        f continuous_on s /\
        (!t. open_in (subtopology euclidean s) t
              ==> open_in (subtopology euclidean (IMAGE f s)) (IMAGE f t)) /\
        (!t. t SUBSET s /\ P t ==> Q(IMAGE f t)) /\
        locally P s
        ==> locally Q (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[locally] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`w:real^N->bool`; `y:real^N`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
  FIRST_ASSUM(MP_TAC o  SPEC `w:real^N->bool` o
    GEN_REWRITE_RULE I [CONTINUOUS_ON_OPEN]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x. x IN s /\ (f:real^M->real^N) x = y` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`{x | x IN s /\ (f:real^M->real^N) x IN w}`; `x:real^M`]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `v:real^M->bool`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`IMAGE (f:real^M->real^N) u`; `IMAGE (f:real^M->real^N) v`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Important special cases of local connectedness & path connectedness.      *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_CONNECTED,LOCALLY_CONNECTED_OPEN_CONNECTED_COMPONENT =
 (CONJ_PAIR o prove)
 (`(!s:real^N->bool.
        locally connected s <=>
        !v x. open_in (subtopology euclidean s) v /\ x IN v
              ==> ?u. open_in (subtopology euclidean s) u /\
                      connected u /\
                      x IN u /\ u SUBSET v) /\
   (!s:real^N->bool.
        locally connected s <=>
        !t x. open_in (subtopology euclidean s) t /\ x IN t
              ==> open_in (subtopology euclidean s)
                          (connected_component t x))`,
  REWRITE_TAC[AND_FORALL_THM; locally] THEN X_GEN_TAC `s:real^N->bool` THEN
  MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (p ==> r) /\ (r ==> q) ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[SUBSET_REFL];
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `y:real^N`] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CONNECTED_COMPONENT_EQ) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `x:real^N`]) THEN ANTS_TAC
    THENL [ASM_MESON_TAC[CONNECTED_COMPONENT_SUBSET; SUBSET]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` (X_CHOOSE_THEN `a:real^N->bool`
          STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `v:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `a:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
    EXISTS_TAC `connected_component u (x:real^N)` THEN
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET; CONNECTED_CONNECTED_COMPONENT] THEN
    ASM_SIMP_TAC[IN; CONNECTED_COMPONENT_REFL]]);;

let LOCALLY_PATH_CONNECTED,LOCALLY_PATH_CONNECTED_OPEN_PATH_COMPONENT =
 (CONJ_PAIR o prove)
 (`(!s:real^N->bool.
        locally path_connected s <=>
        !v x. open_in (subtopology euclidean s) v /\ x IN v
              ==> ?u. open_in (subtopology euclidean s) u /\
                      path_connected u /\
                      x IN u /\ u SUBSET v) /\
   (!s:real^N->bool.
        locally path_connected s <=>
        !t x. open_in (subtopology euclidean s) t /\ x IN t
              ==> open_in (subtopology euclidean s)
                          (path_component t x))`,
  REWRITE_TAC[AND_FORALL_THM; locally] THEN X_GEN_TAC `s:real^N->bool` THEN
  MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (p ==> r) /\ (r ==> q) ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[SUBSET_REFL];
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `y:real^N`] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP PATH_COMPONENT_EQ) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `x:real^N`]) THEN ANTS_TAC
    THENL [ASM_MESON_TAC[PATH_COMPONENT_SUBSET; SUBSET]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` (X_CHOOSE_THEN `a:real^N->bool`
          STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `v:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `a:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
    EXISTS_TAC `path_component u (x:real^N)` THEN
    REWRITE_TAC[PATH_COMPONENT_SUBSET; PATH_CONNECTED_PATH_COMPONENT] THEN
    ASM_SIMP_TAC[IN; PATH_COMPONENT_REFL]]);;

let LOCALLY_CONNECTED_OPEN_COMPONENT = prove
 (`!s:real^N->bool.
        locally connected s <=>
        !t c. open_in (subtopology euclidean s) t /\ c IN components t
              ==> open_in (subtopology euclidean s) c`,
  REWRITE_TAC[LOCALLY_CONNECTED_OPEN_CONNECTED_COMPONENT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; components; FORALL_IN_GSPEC]);;

let LOCALLY_CONNECTED_IM_KLEINEN = prove
 (`!s:real^N->bool.
      locally connected s <=>
      !v x. open_in (subtopology euclidean s) v /\ x IN v
            ==> ?u. open_in (subtopology euclidean s) u /\
                    x IN u /\ u SUBSET v /\
                    !y. y IN u
                        ==> ?c. connected c /\ c SUBSET v /\ x IN c /\ y IN c`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[LOCALLY_CONNECTED] THEN MESON_TAC[SUBSET_REFL]; DISCH_TAC] THEN
  REWRITE_TAC[LOCALLY_CONNECTED_OPEN_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `c:real^N->bool`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `x:real^N`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET c` MP_TAC THENL
   [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM SET_TAC[]);;

let LOCALLY_PATH_CONNECTED_IM_KLEINEN = prove
 (`!s:real^N->bool.
      locally path_connected s <=>
      !v x. open_in (subtopology euclidean s) v /\ x IN v
            ==> ?u. open_in (subtopology euclidean s) u /\
                    x IN u /\ u SUBSET v /\
                    !y. y IN u
                        ==> ?p. path p /\ path_image p SUBSET v /\
                                pathstart p = x /\ pathfinish p = y`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[LOCALLY_PATH_CONNECTED] THEN
    REWRITE_TAC[path_connected] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[LOCALLY_PATH_CONNECTED_OPEN_PATH_COMPONENT] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `z:real^N`] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `x:real^N`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[PATH_COMPONENT_SUBSET; SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(path_image p) SUBSET path_component u (z:real^N)` MP_TAC
    THENL [ALL_TAC; ASM_MESON_TAC[PATHFINISH_IN_PATH_IMAGE; SUBSET]] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP PATH_COMPONENT_EQ) THEN
    MATCH_MP_TAC PATH_COMPONENT_MAXIMAL THEN
    ASM_SIMP_TAC[PATH_CONNECTED_PATH_IMAGE] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE]]);;

let LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED = prove
 (`!s:real^N->bool. locally path_connected s ==> locally connected s`,
  MESON_TAC[LOCALLY_MONO; PATH_CONNECTED_IMP_CONNECTED]);;

let LOCALLY_CONNECTED_COMPONENTS = prove
 (`!s c:real^N->bool.
        locally connected s /\ c IN components s ==> locally connected c`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] LOCALLY_OPEN_SUBSET)) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o
   GEN_REWRITE_RULE I [LOCALLY_CONNECTED_OPEN_COMPONENT]) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[OPEN_IN_REFL]);;

let LOCALLY_CONNECTED_CONNECTED_COMPONENT = prove
 (`!s x:real^N.
        locally connected s
        ==> locally connected (connected_component s x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `connected_component s (x:real^N) = {}` THEN
  ASM_REWRITE_TAC[LOCALLY_EMPTY] THEN
  MATCH_MP_TAC LOCALLY_CONNECTED_COMPONENTS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[IN_COMPONENTS] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_EQ_EMPTY]);;

let LOCALLY_PATH_CONNECTED_COMPONENTS = prove
 (`!s c:real^N->bool.
        locally path_connected s /\ c IN components s
        ==> locally path_connected c`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] LOCALLY_OPEN_SUBSET)) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o
   GEN_REWRITE_RULE I [LOCALLY_CONNECTED_OPEN_COMPONENT] o
   MATCH_MP LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[OPEN_IN_REFL]);;

let LOCALLY_PATH_CONNECTED_CONNECTED_COMPONENT = prove
 (`!s x:real^N.
        locally path_connected s
        ==> locally path_connected (connected_component s x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `connected_component s (x:real^N) = {}` THEN
  ASM_REWRITE_TAC[LOCALLY_EMPTY] THEN
  MATCH_MP_TAC LOCALLY_PATH_CONNECTED_COMPONENTS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[IN_COMPONENTS] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_EQ_EMPTY]);;

let OPEN_IMP_LOCALLY_PATH_CONNECTED = prove
 (`!s:real^N->bool. open s ==> locally path_connected s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_MONO THEN
  EXISTS_TAC `convex:(real^N->bool)->bool` THEN
  REWRITE_TAC[CONVEX_IMP_PATH_CONNECTED] THEN
  ASM_SIMP_TAC[locally; OPEN_IN_OPEN_EQ] THEN
  ASM_MESON_TAC[OPEN_CONTAINS_BALL; CENTRE_IN_BALL; OPEN_BALL; CONVEX_BALL;
                SUBSET]);;

let OPEN_IMP_LOCALLY_CONNECTED = prove
 (`!s:real^N->bool. open s ==> locally connected s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_MONO THEN
  EXISTS_TAC `path_connected:(real^N->bool)->bool` THEN
  ASM_SIMP_TAC[OPEN_IMP_LOCALLY_PATH_CONNECTED;
               PATH_CONNECTED_IMP_CONNECTED]);;

let LOCALLY_PATH_CONNECTED_UNIV = prove
 (`locally path_connected (:real^N)`,
  SIMP_TAC[OPEN_IMP_LOCALLY_PATH_CONNECTED; OPEN_UNIV]);;

let LOCALLY_CONNECTED_UNIV = prove
 (`locally connected (:real^N)`,
  SIMP_TAC[OPEN_IMP_LOCALLY_CONNECTED; OPEN_UNIV]);;

let OPEN_IN_CONNECTED_COMPONENT_LOCALLY_CONNECTED = prove
 (`!s x:real^N.
        locally connected s
        ==> open_in (subtopology euclidean s) (connected_component s x)`,
  REWRITE_TAC[LOCALLY_CONNECTED_OPEN_CONNECTED_COMPONENT] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:real^N) IN s` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; SUBSET_UNIV; TOPSPACE_EUCLIDEAN];
    ASM_MESON_TAC[OPEN_IN_EMPTY; CONNECTED_COMPONENT_EQ_EMPTY]]);;

let OPEN_IN_COMPONENTS_LOCALLY_CONNECTED = prove
 (`!s c:real^N->bool.
        locally connected s /\ c IN components s
        ==> open_in (subtopology euclidean s) c`,
  MESON_TAC[LOCALLY_CONNECTED_OPEN_COMPONENT; OPEN_IN_REFL]);;

let OPEN_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED = prove
 (`!s x:real^N.
        locally path_connected s
        ==> open_in (subtopology euclidean s) (path_component s x)`,
  REWRITE_TAC[LOCALLY_PATH_CONNECTED_OPEN_PATH_COMPONENT] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:real^N) IN s` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; SUBSET_UNIV; TOPSPACE_EUCLIDEAN];
    ASM_MESON_TAC[OPEN_IN_EMPTY; PATH_COMPONENT_EQ_EMPTY]]);;

let CLOSED_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED = prove
 (`!s x:real^N.
        locally path_connected s
        ==> closed_in (subtopology euclidean s) (path_component s x)`,
  REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              PATH_COMPONENT_SUBSET] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEMENT_PATH_COMPONENT_UNIONS] THEN
  MATCH_MP_TAC OPEN_IN_UNIONS THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC; IN_DELETE] THEN
  ASM_SIMP_TAC[OPEN_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED]);;

let CONVEX_IMP_LOCALLY_PATH_CONNECTED = prove
 (`!s:real^N->bool. convex s ==> locally path_connected s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LOCALLY_PATH_CONNECTED] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s INTER ball(x:real^N,e)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN MESON_TAC[OPEN_BALL];
    MATCH_MP_TAC CONVEX_IMP_PATH_CONNECTED THEN
    ASM_SIMP_TAC[CONVEX_INTER; CONVEX_BALL];
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    ASM SET_TAC[]]);;

let OPEN_IN_CONNECTED_COMPONENTS = prove
 (`!s c:real^N->bool.
        FINITE(components s) /\ c IN components s
        ==> open_in (subtopology euclidean s) c`,
  REWRITE_TAC[components; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  SIMP_TAC[OPEN_IN_CONNECTED_COMPONENT]);;

let FINITE_LOCALLY_CONNECTED_CONNECTED_COMPONENTS = prove
 (`!s:real^N->bool.
        compact s /\ locally connected s
        ==> FINITE {connected_component s x |x|  x IN s}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{connected_component s (x:real^N) |x| x IN s}` o
    GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY]) THEN
  ASM_SIMP_TAC[OPEN_IN_CONNECTED_COMPONENT_LOCALLY_CONNECTED; FORALL_IN_GSPEC;
               UNIONS_CONNECTED_COMPONENT; SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `cs:(real^N->bool)->bool` MP_TAC) THEN
  ASM_CASES_TAC `{connected_component s (x:real^N) |x| x IN s} = cs` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(TAUT `(p ==> ~r) ==> p /\ q /\ r ==> s`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?x:real^N. x IN s /\ ~(connected_component s x IN cs)`
  MP_TAC THENL [ASM SET_TAC[]; SIMP_TAC[SUBSET; NOT_FORALL_THM]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?y:real^N. y IN s /\ x IN connected_component s y /\
                           connected_component s y IN cs`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENT_EQ) THEN
  ASM_MESON_TAC[]);;

let FINITE_LOCALLY_PATH_CONNECTED_PATH_COMPONENTS = prove
 (`!s:real^N->bool.
        compact s /\ locally path_connected s
        ==> FINITE {path_component s x |x|  x IN s}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{path_component s (x:real^N) |x| x IN s}` o
    GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY]) THEN
  ASM_SIMP_TAC[OPEN_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED; FORALL_IN_GSPEC;
               UNIONS_PATH_COMPONENT; SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `cs:(real^N->bool)->bool` MP_TAC) THEN
  ASM_CASES_TAC `{path_component s (x:real^N) |x| x IN s} = cs` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(TAUT `(p ==> ~r) ==> p /\ q /\ r ==> s`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?x:real^N. x IN s /\ ~(path_component s x IN cs)`
  MP_TAC THENL [ASM SET_TAC[]; SIMP_TAC[SUBSET; NOT_FORALL_THM]] THEN

  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?y:real^N. y IN s /\ x IN path_component s y /\
                           path_component s y IN cs`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PATH_COMPONENT_EQ) THEN
  ASM_MESON_TAC[]);;

let FINITE_COMPONENTS = prove
 (`!s:real^N->bool. compact s /\ locally connected s ==> FINITE(components s)`,
  REWRITE_TAC[components; FINITE_LOCALLY_CONNECTED_CONNECTED_COMPONENTS]);;

let CONVEX_IMP_LOCALLY_CONNECTED = prove
 (`!s:real^N->bool. convex s ==> locally connected s`,
  MESON_TAC[CONVEX_IMP_LOCALLY_PATH_CONNECTED;
            LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED]);;

let HOMEOMORPHIC_LOCAL_CONNECTEDNESS = prove
 (`!s t. s homeomorphic t ==> (locally connected s <=> locally connected t)`,
  MATCH_MP_TAC HOMEOMORPHIC_LOCALLY THEN
  REWRITE_TAC[HOMEOMORPHIC_CONNECTEDNESS]);;

let HOMEOMORPHIC_LOCAL_PATH_CONNECTEDNESS = prove
 (`!s t. s homeomorphic t
         ==> (locally path_connected s <=> locally path_connected t)`,
  MATCH_MP_TAC HOMEOMORPHIC_LOCALLY THEN
  REWRITE_TAC[HOMEOMORPHIC_PATH_CONNECTEDNESS]);;

let LOCALLY_PATH_CONNECTED_TRANSLATION_EQ = prove
 (`!a:real^N s. locally path_connected (IMAGE (\x. a + x) s) <=>
                locally path_connected s`,
  MATCH_MP_TAC LOCALLY_TRANSLATION THEN
  REWRITE_TAC[PATH_CONNECTED_TRANSLATION_EQ]);;

add_translation_invariants [LOCALLY_PATH_CONNECTED_TRANSLATION_EQ];;

let LOCALLY_CONNECTED_TRANSLATION_EQ = prove
 (`!a:real^N s. locally connected (IMAGE (\x. a + x) s) <=>
                locally connected s`,
  MATCH_MP_TAC LOCALLY_TRANSLATION THEN
  REWRITE_TAC[CONNECTED_TRANSLATION_EQ]);;

add_translation_invariants [LOCALLY_CONNECTED_TRANSLATION_EQ];;

let LOCALLY_PATH_CONNECTED_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (locally path_connected (IMAGE f s) <=> locally path_connected s)`,
  MATCH_MP_TAC LOCALLY_INJECTIVE_LINEAR_IMAGE THEN
  REWRITE_TAC[PATH_CONNECTED_LINEAR_IMAGE_EQ]);;

add_linear_invariants [LOCALLY_PATH_CONNECTED_LINEAR_IMAGE_EQ];;

let LOCALLY_CONNECTED_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (locally connected (IMAGE f s) <=> locally connected s)`,
  MATCH_MP_TAC LOCALLY_INJECTIVE_LINEAR_IMAGE THEN
  REWRITE_TAC[CONNECTED_LINEAR_IMAGE_EQ]);;

add_linear_invariants [LOCALLY_CONNECTED_LINEAR_IMAGE_EQ];;

let LOCALLY_CONNECTED_QUOTIENT_IMAGE = prove
 (`!f:real^M->real^N s.
      (!t. t SUBSET IMAGE f s
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN t} <=>
                open_in (subtopology euclidean (IMAGE f s)) t)) /\
      locally connected s
      ==> locally connected (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LOCALLY_CONNECTED_OPEN_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `c:real^N->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN EXISTS_TAC
   `connected_component {w | w IN s /\ (f:real^M->real^N)(w) IN u} x` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [LOCALLY_CONNECTED_OPEN_COMPONENT]) THEN
    REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_COMPONENTS; IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC;
    ASSUME_TAC(ISPECL [`{w | w IN s /\ (f:real^M->real^N) w IN u}`; `x:real^M`]
        CONNECTED_COMPONENT_SUBSET) THEN
    SUBGOAL_THEN
     `IMAGE (f:real^M->real^N) (connected_component {w | w IN s /\ f w IN u} x)
      SUBSET c`
    MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_ON_OPEN] THEN ASM_MESON_TAC[open_in];
        ASM SET_TAC[]];
      ASM SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(f:real^M->real^N) x` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE]] THEN
  GEN_REWRITE_TAC I [IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
  ASM SET_TAC[]);;

let LOCALLY_PATH_CONNECTED_QUOTIENT_IMAGE = prove
 (`!f:real^M->real^N s.
      (!t. t SUBSET IMAGE f s
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN t} <=>
                open_in (subtopology euclidean (IMAGE f s)) t)) /\
      locally path_connected s
      ==> locally path_connected (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LOCALLY_PATH_CONNECTED_OPEN_PATH_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `y:real^N`] THEN
  STRIP_TAC THEN
  ASSUME_TAC(ISPECL [`u:real^N->bool`; `y:real^N`] PATH_COMPONENT_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `path_component u (y:real^N)`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN EXISTS_TAC
   `path_component {w | w IN s /\ (f:real^M->real^N)(w) IN u} x` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [LOCALLY_PATH_CONNECTED_OPEN_PATH_COMPONENT]) THEN
    REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC;
    ASSUME_TAC(ISPECL [`{w | w IN s /\ (f:real^M->real^N) w IN u}`; `x:real^M`]
        PATH_COMPONENT_SUBSET) THEN
    SUBGOAL_THEN
     `IMAGE (f:real^M->real^N) (path_component {w | w IN s /\ f w IN u} x)
      SUBSET path_component u y`
    MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP PATH_COMPONENT_EQ) THEN
    MATCH_MP_TAC PATH_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE;
      MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[PATH_CONNECTED_PATH_COMPONENT] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_ON_OPEN] THEN ASM_MESON_TAC[open_in];
        ASM SET_TAC[]];
      ASM SET_TAC[]]] THEN
  GEN_REWRITE_TAC I [IN] THEN REWRITE_TAC[PATH_COMPONENT_REFL_EQ] THEN
  ASM SET_TAC[]);;

let LOCALLY_CONNECTED_CONTINUOUS_IMAGE_COMPACT = prove
 (`!f:real^M->real^N s.
        locally connected s /\ compact s /\ f continuous_on s
        ==> locally connected (IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_CONNECTED_QUOTIENT_IMAGE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_MAP_IMP_QUOTIENT_MAP THEN
  ASM_SIMP_TAC[CLOSED_IN_CLOSED_EQ; COMPACT_IMP_CLOSED;
               COMPACT_CONTINUOUS_IMAGE; IMAGE_SUBSET] THEN
  ASM_MESON_TAC[COMPACT_IMP_CLOSED; COMPACT_CONTINUOUS_IMAGE;
    CONTINUOUS_ON_SUBSET; BOUNDED_SUBSET; COMPACT_EQ_BOUNDED_CLOSED]);;

let LOCALLY_PATH_CONNECTED_CONTINUOUS_IMAGE_COMPACT = prove
 (`!f:real^M->real^N s.
        locally path_connected s /\ compact s /\ f continuous_on s
        ==> locally path_connected (IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_PATH_CONNECTED_QUOTIENT_IMAGE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_MAP_IMP_QUOTIENT_MAP THEN
  ASM_SIMP_TAC[CLOSED_IN_CLOSED_EQ; COMPACT_IMP_CLOSED;
               COMPACT_CONTINUOUS_IMAGE; IMAGE_SUBSET] THEN
  ASM_MESON_TAC[COMPACT_IMP_CLOSED; COMPACT_CONTINUOUS_IMAGE;
    CONTINUOUS_ON_SUBSET; BOUNDED_SUBSET; COMPACT_EQ_BOUNDED_CLOSED]);;

let LOCALLY_PATH_CONNECTED_PATH_IMAGE = prove
 (`!p:real^1->real^N. path p ==> locally path_connected (path_image p)`,
  REWRITE_TAC[path; path_image] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LOCALLY_PATH_CONNECTED_CONTINUOUS_IMAGE_COMPACT THEN
  ASM_SIMP_TAC[COMPACT_INTERVAL; CONVEX_INTERVAL;
               CONVEX_IMP_LOCALLY_PATH_CONNECTED]);;

let LOCALLY_CONNECTED_PATH_IMAGE = prove
 (`!p:real^1->real^N. path p ==> locally connected (path_image p)`,
  SIMP_TAC[LOCALLY_PATH_CONNECTED_PATH_IMAGE;
           LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED]);;

let LOCALLY_CONNECTED_LEFT_INVERTIBLE_IMAGE = prove
 (`!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        (!x. x IN s ==> g(f x) = x) /\
        locally connected s
        ==> locally connected (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LOCALLY_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC CONTINUOUS_LEFT_INVERSE_IMP_QUOTIENT_MAP THEN ASM_MESON_TAC[]);;

let LOCALLY_CONNECTED_RIGHT_INVERTIBLE_IMAGE = prove
 (`!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        IMAGE g (IMAGE f s) SUBSET s /\ (!x. x IN IMAGE f s ==> f(g x) = x) /\
        locally connected s
        ==> locally connected (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LOCALLY_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC CONTINUOUS_RIGHT_INVERSE_IMP_QUOTIENT_MAP THEN
  EXISTS_TAC `g:real^N->real^M` THEN ASM SET_TAC[]);;

let LOCALLY_PATH_CONNECTED_LEFT_INVERTIBLE_IMAGE = prove
 (`!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        (!x. x IN s ==> g(f x) = x) /\
        locally path_connected s
        ==> locally path_connected (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
    LOCALLY_PATH_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC CONTINUOUS_LEFT_INVERSE_IMP_QUOTIENT_MAP THEN ASM_MESON_TAC[]);;

let LOCALLY_PATH_CONNECTED_RIGHT_INVERTIBLE_IMAGE = prove
 (`!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        IMAGE g (IMAGE f s) SUBSET s /\ (!x. x IN IMAGE f s ==> f(g x) = x) /\
        locally path_connected s
        ==> locally path_connected (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
    LOCALLY_PATH_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC CONTINUOUS_RIGHT_INVERSE_IMP_QUOTIENT_MAP THEN
  EXISTS_TAC `g:real^N->real^M` THEN ASM SET_TAC[]);;

let LOCALLY_PCROSS = prove
 (`!P Q R.
        (!s:real^M->bool t:real^N->bool. P s /\ Q t ==> R(s PCROSS t))
        ==> (!s t. locally P s /\ locally Q t ==> locally R (s PCROSS t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[locally; FORALL_PASTECART] THEN
  MAP_EVERY X_GEN_TAC
   [`w:real^(M,N)finite_sum->bool`; `x:real^M`; `y:real^N`] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
   MP_TAC(MATCH_MP PASTECART_IN_INTERIOR_SUBTOPOLOGY
        (ONCE_REWRITE_RULE[CONJ_SYM] th))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `v:real^N->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^M->bool`; `x:real^M`] o
    GEN_REWRITE_RULE I [locally]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^N->bool`; `y:real^N`] o
    GEN_REWRITE_RULE I [locally]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v':real^N->bool`; `v'':real^N->bool`] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`u':real^M->bool`; `u'':real^M->bool`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `(u':real^M->bool) PCROSS (v':real^N->bool)` THEN
  EXISTS_TAC `(u'':real^M->bool) PCROSS (v'':real^N->bool)` THEN
  ASM_SIMP_TAC[PASTECART_IN_PCROSS; PCROSS_MONO; OPEN_IN_PCROSS] THEN
  ASM_MESON_TAC[PCROSS_MONO; SUBSET_TRANS]);;

let LOCALLY_CONNECTED_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        locally connected s /\ locally connected t
        ==> locally connected (s PCROSS t)`,
  MATCH_MP_TAC LOCALLY_PCROSS THEN REWRITE_TAC[CONNECTED_PCROSS]);;

let LOCALLY_PATH_CONNECTED_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        locally path_connected s /\ locally path_connected t
        ==> locally path_connected (s PCROSS t)`,
  MATCH_MP_TAC LOCALLY_PCROSS THEN REWRITE_TAC[PATH_CONNECTED_PCROSS]);;

let LOCALLY_CONNECTED_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        locally connected (s PCROSS t) <=>
        s = {} \/ t = {} \/ locally connected s /\ locally connected t`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; LOCALLY_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; LOCALLY_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[LOCALLY_CONNECTED_PCROSS] THEN
  GEN_REWRITE_TAC LAND_CONV [LOCALLY_CONNECTED] THEN DISCH_TAC THEN
  REWRITE_TAC[LOCALLY_CONNECTED_IM_KLEINEN] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `x:real^M`] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(u:real^M->bool) PCROSS (t:real^N->bool)`;
      `pastecart (x:real^M) (y:real^N)`]);
    MAP_EVERY X_GEN_TAC [`v:real^N->bool`; `y:real^N`] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(s:real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^M`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(s:real^M->bool) PCROSS (v:real^N->bool)`;
      `pastecart (x:real^M) (y:real^N)`])] THEN
  ASM_SIMP_TAC[OPEN_IN_PCROSS_EQ; PASTECART_IN_PCROSS; SUBSET_UNIV;
    OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `w:real^(M,N)finite_sum->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:real^M->bool`; `t:real^N->bool`; `w:real^(M,N)finite_sum->bool`;
    `x:real^M`; `y:real^N`] PASTECART_IN_INTERIOR_SUBTOPOLOGY) THEN
  ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u':real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
      EXISTS_TAC `IMAGE fstcart (w:real^(M,N)finite_sum->bool)` THEN
      ASM_SIMP_TAC[CONNECTED_LINEAR_IMAGE; LINEAR_FSTCART] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART]];
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` MP_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `v':real^N->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `IMAGE sndcart (w:real^(M,N)finite_sum->bool)` THEN
      ASM_SIMP_TAC[CONNECTED_LINEAR_IMAGE; LINEAR_SNDCART] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PASTECART; SNDCART_PASTECART]]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SUBSET; FORALL_IN_PCROSS; PASTECART_IN_PCROSS; FORALL_PASTECART]) THEN
  ASM SET_TAC[]);;

let LOCALLY_PATH_CONNECTED_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        locally path_connected (s PCROSS t) <=>
        s = {} \/ t = {} \/
        locally path_connected s /\ locally path_connected t`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; LOCALLY_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; LOCALLY_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[LOCALLY_PATH_CONNECTED_PCROSS] THEN
  GEN_REWRITE_TAC LAND_CONV [LOCALLY_PATH_CONNECTED] THEN DISCH_TAC THEN
  REWRITE_TAC[LOCALLY_PATH_CONNECTED_IM_KLEINEN] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `x:real^M`] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(u:real^M->bool) PCROSS (t:real^N->bool)`;
      `pastecart (x:real^M) (y:real^N)`]);
    MAP_EVERY X_GEN_TAC [`v:real^N->bool`; `y:real^N`] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(s:real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^M`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(s:real^M->bool) PCROSS (v:real^N->bool)`;
      `pastecart (x:real^M) (y:real^N)`])] THEN
  ASM_SIMP_TAC[OPEN_IN_PCROSS_EQ; PASTECART_IN_PCROSS; SUBSET_UNIV;
    OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `w:real^(M,N)finite_sum->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:real^M->bool`; `t:real^N->bool`; `w:real^(M,N)finite_sum->bool`;
    `x:real^M`; `y:real^N`] PASTECART_IN_INTERIOR_SUBTOPOLOGY) THEN
  ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u':real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
                     `w:real^(M,N)finite_sum->bool`]
        PATH_CONNECTED_LINEAR_IMAGE) THEN ASM_REWRITE_TAC[LINEAR_FSTCART] THEN
      REWRITE_TAC[path_connected] THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `z:real^M`]) THEN ANTS_TAC THENL
       [REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART];
        MATCH_MP_TAC MONO_EXISTS THEN
        REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` MP_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `v':real^N->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
                     `w:real^(M,N)finite_sum->bool`]
        PATH_CONNECTED_LINEAR_IMAGE) THEN ASM_REWRITE_TAC[LINEAR_SNDCART] THEN
      REWRITE_TAC[path_connected] THEN
      DISCH_THEN(MP_TAC o SPECL [`y:real^N`; `z:real^N`]) THEN ANTS_TAC THENL
       [REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; SNDCART_PASTECART];
        MATCH_MP_TAC MONO_EXISTS THEN
        REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PASTECART; SNDCART_PASTECART] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SUBSET; FORALL_IN_PCROSS; PASTECART_IN_PCROSS; FORALL_PASTECART]) THEN
  ASM SET_TAC[]);;

let CARD_EQ_OPEN_IN = prove
 (`!u s:real^N->bool.
      locally connected u /\
      open_in (subtopology euclidean u) s /\
      (?x. x IN s /\ x limit_point_of u)
      ==> s =_c (:real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
    SIMP_TAC[CARD_EQ_IMP_LE; CARD_EQ_EUCLIDEAN] THEN
    MATCH_MP_TAC CARD_LE_SUBSET THEN REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LOCALLY_CONNECTED]) THEN
  DISCH_THEN(MP_TAC o SPECL [`u INTER t:real^N->bool`; `x:real^N`]) THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER] THEN
  REWRITE_TAC[OPEN_IN_OPEN; GSYM CONJ_ASSOC; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REWRITE_TAC[UNWIND_THM2; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [limit_point_of]) THEN
  DISCH_THEN(MP_TAC o SPEC `t INTER v:real^N->bool`) THEN
  ASM_SIMP_TAC[IN_INTER; OPEN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  TRANS_TAC CARD_LE_TRANS `u INTER v:real^N->bool` THEN
  ASM_SIMP_TAC[CARD_LE_SUBSET] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN MATCH_MP_TAC CARD_EQ_CONNECTED THEN
  ASM SET_TAC[]);;

let CARD_EQ_OPEN_IN_AFFINE = prove
 (`!u s:real^N->bool.
        affine u /\ ~(aff_dim u = &0) /\
        open_in (subtopology euclidean u) s /\ ~(s = {})
        ==> s =_c (:real)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_EQ_OPEN_IN THEN
  EXISTS_TAC `u:real^N->bool` THEN
  ASM_SIMP_TAC[CONVEX_IMP_LOCALLY_CONNECTED; AFFINE_IMP_CONVEX] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_IMP_PERFECT_AFF_DIM THEN
  ASM_SIMP_TAC[AFFINE_IMP_CONVEX; CONVEX_CONNECTED] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Locally convex sets.                                                      *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_CONVEX = prove
 (`!s:real^N->bool.
        locally convex s <=>
        !x. x IN s ==> ?u v. x IN u /\ u SUBSET v /\ v SUBSET s /\
                             open_in (subtopology euclidean s) u /\
                             convex v`,
  GEN_TAC THEN REWRITE_TAC[locally] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM
     (MP_TAC o SPECL [`s INTER ball(x:real^N,&1)`; `x:real^N`]) THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; REAL_LT_01] THEN
    MESON_TAC[SUBSET_INTER];
    MAP_EVERY X_GEN_TAC [`w:real^N->bool`; `x:real^N`] THEN
    REWRITE_TAC[IMP_CONJ] THEN GEN_REWRITE_TAC LAND_CONV [OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(s INTER ball(x:real^N,e)) INTER u` THEN
    EXISTS_TAC `cball(x:real^N,e) INTER v` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; OPEN_IN_OPEN_INTER; OPEN_BALL; CENTRE_IN_BALL;
                 CONVEX_INTER; CONVEX_CBALL; IN_INTER] THEN
    MP_TAC(ISPECL [`x:real^N`; `e:real`] BALL_SUBSET_CBALL) THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Basic properties of local compactness.                                    *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_COMPACT = prove
 (`!s:real^N->bool.
        locally compact s <=>
        !x. x IN s ==> ?u v. x IN u /\ u SUBSET v /\ v SUBSET s /\
                             open_in (subtopology euclidean s) u /\
                             compact v`,
  GEN_TAC THEN REWRITE_TAC[locally] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM
     (MP_TAC o SPECL [`s INTER ball(x:real^N,&1)`; `x:real^N`]) THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; REAL_LT_01] THEN
    MESON_TAC[SUBSET_INTER];
    MAP_EVERY X_GEN_TAC [`w:real^N->bool`; `x:real^N`] THEN
    REWRITE_TAC[IMP_CONJ] THEN GEN_REWRITE_TAC LAND_CONV [OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(s INTER ball(x:real^N,e)) INTER u` THEN
    EXISTS_TAC `cball(x:real^N,e) INTER v` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; OPEN_IN_OPEN_INTER; OPEN_BALL; CENTRE_IN_BALL;
                 COMPACT_INTER; COMPACT_CBALL; IN_INTER] THEN
    MP_TAC(ISPECL [`x:real^N`; `e:real`] BALL_SUBSET_CBALL) THEN
    ASM SET_TAC[]]);;

let LOCALLY_COMPACT_ALT = prove
 (`!s:real^N->bool.
        locally compact s <=>
        !x. x IN s
            ==> ?u. x IN u /\
                    open_in (subtopology euclidean s) u /\
                    compact(closure u) /\ closure u SUBSET s`,
  GEN_TAC THEN REWRITE_TAC[LOCALLY_COMPACT] THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
  MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS; CLOSURE_MINIMAL;
            COMPACT_CLOSURE; BOUNDED_SUBSET; COMPACT_EQ_BOUNDED_CLOSED]);;

let LOCALLY_COMPACT_INTER_CBALL = prove
 (`!s:real^N->bool.
        locally compact s <=>
        !x. x IN s ==> ?e. &0 < e /\ closed(cball(x,e) INTER s)`,
  GEN_TAC THEN REWRITE_TAC[LOCALLY_COMPACT; OPEN_IN_CONTAINS_CBALL] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cball(x:real^N,e) INTER s = cball (x,e) INTER v`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_CBALL; COMPACT_INTER; COMPACT_IMP_CLOSED];
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    EXISTS_TAC `ball(x:real^N,e) INTER s` THEN
    EXISTS_TAC `cball(x:real^N,e) INTER s` THEN
    REWRITE_TAC[GSYM OPEN_IN_CONTAINS_CBALL] THEN
    ASM_SIMP_TAC[IN_INTER; CENTRE_IN_BALL; INTER_SUBSET] THEN
    ASM_SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_INTER; BOUNDED_CBALL] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
    MESON_TAC[SUBSET; IN_INTER; BALL_SUBSET_CBALL]]);;

let LOCALLY_COMPACT_INTER_CBALLS = prove
 (`!s:real^N->bool.
      locally compact s <=>
      !x. x IN s ==> ?e. &0 < e /\ !d. d <= e ==> closed(cball(x,d) INTER s)`,
  GEN_TAC THEN REWRITE_TAC[LOCALLY_COMPACT_INTER_CBALL] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[REAL_LE_REFL]] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `cball(x:real^N,d) INTER s = cball(x,d) INTER cball(x,e) INTER s`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INTER_ASSOC; GSYM CBALL_MIN_INTER] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    BINOP_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[CLOSED_INTER; CLOSED_CBALL]]);;

let LOCALLY_COMPACT_COMPACT = prove
 (`!s:real^N->bool.
        locally compact s <=>
        !k. k SUBSET s /\ compact k
            ==> ?u v. k SUBSET u /\
                      u SUBSET v /\
                      v SUBSET s /\
                      open_in (subtopology euclidean s) u /\

                      compact v`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LOCALLY_COMPACT] THEN EQ_TAC THEN
  REPEAT STRIP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SING_SUBSET; COMPACT_SING]] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM] o
        check (is_forall o concl)) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->real^N->bool`; `v:real^N->real^N->bool`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
   [COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\x:real^N. k INTER u x) k`) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; UNIONS_IMAGE] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    ASM SET_TAC[];
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
    REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE; UNIONS_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `UNIONS(IMAGE (u:real^N->real^N->bool) t)` THEN
    EXISTS_TAC `UNIONS(IMAGE (v:real^N->real^N->bool) t)` THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC; ALL_TAC; ALL_TAC; MATCH_MP_TAC OPEN_IN_UNIONS;
      MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE]] THEN
    ASM SET_TAC[]]);;

let LOCALLY_COMPACT_COMPACT_ALT = prove
 (`!s:real^N->bool.
        locally compact s <=>
        !k. k SUBSET s /\ compact k
            ==> ?u. k SUBSET u /\
                    open_in (subtopology euclidean s) u /\
                    compact(closure u) /\ closure u SUBSET s`,
  GEN_TAC THEN REWRITE_TAC[LOCALLY_COMPACT_COMPACT] THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
  MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS; CLOSURE_MINIMAL;
            COMPACT_CLOSURE; BOUNDED_SUBSET; COMPACT_EQ_BOUNDED_CLOSED]);;

let LOCALLY_COMPACT_COMPACT_SUBOPEN = prove
 (`!s:real^N->bool.
        locally compact s <=>
        !k t. k SUBSET s /\ compact k /\ open t /\ k SUBSET t
              ==> ?u v. k SUBSET u /\ u SUBSET v /\ u SUBSET t /\ v SUBSET s /\
                        open_in (subtopology euclidean s) u /\
                        compact v`,
  GEN_TAC THEN REWRITE_TAC[LOCALLY_COMPACT_COMPACT] THEN
  EQ_TAC THEN DISCH_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`u INTER t:real^N->bool`; `closure(u INTER t:real^N->bool)`] THEN
    REWRITE_TAC[CLOSURE_SUBSET; INTER_SUBSET] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      TRANS_TAC SUBSET_TRANS `closure(u:real^N->bool)` THEN
      SIMP_TAC[SUBSET_CLOSURE; INTER_SUBSET] THEN
      TRANS_TAC SUBSET_TRANS `v:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      ASM_SIMP_TAC[OPEN_IN_INTER_OPEN];
      REWRITE_TAC[COMPACT_CLOSURE] THEN
      ASM_MESON_TAC[BOUNDED_SUBSET; INTER_SUBSET; SUBSET_TRANS;
                    COMPACT_IMP_BOUNDED]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:real^N->bool`; `(:real^N)`]) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV]]);;

let OPEN_IMP_LOCALLY_COMPACT = prove
 (`!s:real^N->bool. open s ==> locally compact s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LOCALLY_COMPACT] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`ball(x:real^N,e)`; `cball(x:real^N,e)`] THEN
  ASM_REWRITE_TAC[BALL_SUBSET_CBALL; CENTRE_IN_BALL; COMPACT_CBALL] THEN
  MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
  ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS]);;

let CLOSED_IMP_LOCALLY_COMPACT = prove
 (`!s:real^N->bool. closed s ==> locally compact s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LOCALLY_COMPACT] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MAP_EVERY EXISTS_TAC
   [`s INTER ball(x:real^N,&1)`; `s INTER cball(x:real^N,&1)`] THEN
  ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; INTER_SUBSET; REAL_LT_01] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
  ASM_SIMP_TAC[CLOSED_INTER_COMPACT; COMPACT_CBALL] THEN
  MP_TAC(ISPECL [`x:real^N`; `&1`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[]);;

let IS_INTERVAL_IMP_LOCALLY_COMPACT = prove
 (`!s:real^N->bool. is_interval s ==> locally compact s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LOCALLY_COMPACT] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
   INTERVAL_CONTAINS_COMPACT_NEIGHBOURHOOD) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`s INTER ball(x:real^N,d)`; `interval[a:real^N,b]`] THEN
  ASM_SIMP_TAC[COMPACT_INTERVAL; OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; IN_INTER] THEN ASM SET_TAC[]);;

let LOCALLY_COMPACT_UNIV = prove
 (`locally compact (:real^N)`,
  SIMP_TAC[OPEN_IMP_LOCALLY_COMPACT; OPEN_UNIV]);;

let LOCALLY_COMPACT_INTER = prove
 (`!s t:real^N->bool.
        locally compact s /\ locally compact t
        ==> locally compact (s INTER t)`,
  MATCH_MP_TAC LOCALLY_INTER THEN REWRITE_TAC[COMPACT_INTER]);;

let LOCALLY_COMPACT_OPEN_IN = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean s) t /\ locally compact s
        ==> locally compact t`,
  REWRITE_TAC[OPEN_IN_OPEN] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LOCALLY_COMPACT_INTER; OPEN_IMP_LOCALLY_COMPACT]);;

let LOCALLY_COMPACT_CLOSED_IN = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean s) t /\ locally compact s
        ==> locally compact t`,
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LOCALLY_COMPACT_INTER; CLOSED_IMP_LOCALLY_COMPACT]);;

let LOCALLY_COMPACT_DELETE = prove
 (`!s a:real^N. locally compact s ==> locally compact (s DELETE a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_COMPACT_OPEN_IN THEN
  EXISTS_TAC `s:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_IN_DELETE; OPEN_IN_REFL]);;

let SIGMA_COMPACT = prove
 (`!s:real^N->bool.
        locally compact s
        ==> ?f. COUNTABLE f /\ (!t. t IN f ==> compact t) /\ UNIONS f = s`,
  GEN_TAC THEN REWRITE_TAC[LOCALLY_COMPACT] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->real^N->bool`; `c:real^N->real^N->bool`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (u:real^N->real^N->bool) s`; `s:real^N->bool`]
   LINDELOF_OPEN_IN) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REWRITE_TAC[EXISTS_COUNTABLE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (c:real^N->real^N->bool) t` THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; FORALL_IN_IMAGE; FORALL_IN_UNIONS] THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE] THEN ASM SET_TAC[]);;

let HOMEOMORPHIC_LOCAL_COMPACTNESS = prove
 (`!s t:real^N->bool.
        s homeomorphic t ==> (locally compact s <=> locally compact t)`,
  MATCH_MP_TAC HOMEOMORPHIC_LOCALLY THEN
  REWRITE_TAC[HOMEOMORPHIC_COMPACTNESS]);;

let LOCALLY_COMPACT_TRANSLATION_EQ = prove
 (`!a:real^N s. locally compact (IMAGE (\x. a + x) s) <=>
                locally compact s`,
  MATCH_MP_TAC LOCALLY_TRANSLATION THEN
  REWRITE_TAC[COMPACT_TRANSLATION_EQ]);;

add_translation_invariants [LOCALLY_COMPACT_TRANSLATION_EQ];;

let LOCALLY_COMPACT_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (locally compact (IMAGE f s) <=> locally compact s)`,
  MATCH_MP_TAC LOCALLY_INJECTIVE_LINEAR_IMAGE THEN
  REWRITE_TAC[COMPACT_LINEAR_IMAGE_EQ]);;

add_linear_invariants [LOCALLY_COMPACT_LINEAR_IMAGE_EQ];;

let LOCALLY_CLOSED = prove
 (`!s:real^N->bool. locally closed s <=> locally compact s`,
  GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[LOCALLY_MONO; COMPACT_IMP_CLOSED]] THEN
  REWRITE_TAC[locally] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`w:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N->bool`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `u INTER ball(x:real^N,&1)` THEN
  EXISTS_TAC `v INTER cball(x:real^N,&1)` THEN
  ASM_SIMP_TAC[OPEN_IN_INTER_OPEN; OPEN_BALL] THEN
  ASM_SIMP_TAC[CLOSED_INTER_COMPACT; COMPACT_CBALL] THEN
  ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; REAL_LT_01] THEN
  MP_TAC(ISPEC `x:real^N` BALL_SUBSET_CBALL) THEN ASM SET_TAC[]);;

let LOCALLY_COMPACT_OPEN_UNION = prove
 (`!s t:real^N->bool.
        locally compact s /\ locally compact t /\
        open_in (subtopology euclidean (s UNION t)) s /\
        open_in (subtopology euclidean (s UNION t)) t
        ==> locally compact (s UNION t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LOCALLY_COMPACT_INTER_CBALL; IN_UNION] THEN
  INTRO_TAC "lcs lct os ot" THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
   [REMOVE_THEN "lcs" (MP_TAC o SPEC `x:real^N`) THEN
    REMOVE_THEN "os"
     (MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_CBALL]);
    REMOVE_THEN "lct" (MP_TAC o SPEC `x:real^N`) THEN
    REMOVE_THEN "ot"
     (MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_CBALL])] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d e:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REWRITE_TAC[CBALL_MIN_INTER; INTER_ASSOC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `u INTER st SUBSET s ==> s SUBSET st ==> u INTER st = u INTER s`)) THEN
  REWRITE_TAC[SUBSET_UNION] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_MESON_TAC[CLOSED_INTER; CLOSED_CBALL; INTER_ACI]);;

let LOCALLY_COMPACT_CLOSED_UNION = prove
 (`!s t:real^N->bool.
        locally compact s /\ locally compact t /\
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t
        ==> locally compact (s UNION t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LOCALLY_COMPACT_INTER_CBALL; IN_UNION] THEN
  INTRO_TAC "lcs lct cs ct" THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP (TAUT
   `p \/ q ==> p /\ q \/ p /\ ~q \/ q /\ ~p`))
  THENL
   [REMOVE_THEN "lct" (MP_TAC o SPEC `x:real^N`) THEN
    REMOVE_THEN "lcs" (MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    EXISTS_TAC `min d e:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    SIMP_TAC[SET_RULE `u INTER (s UNION t) = u INTER s UNION u INTER t`] THEN
    MATCH_MP_TAC CLOSED_UNION THEN REWRITE_TAC[CBALL_MIN_INTER] THEN
    ASM_MESON_TAC[CLOSED_CBALL; CLOSED_INTER; INTER_ACI];
    REMOVE_THEN "lcs" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "ct" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [closed_in]);
    REMOVE_THEN "lct" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "cs" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [closed_in])] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_CBALL]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_DIFF; IN_UNION] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT2) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d e:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THENL
   [SUBGOAL_THEN `cball (x:real^N,min d e) INTER (s UNION t) =
                  cball(x,d) INTER cball (x,e) INTER s` SUBST1_TAC
    THENL [REWRITE_TAC[CBALL_MIN_INTER] THEN ASM SET_TAC[]; ALL_TAC];
    SUBGOAL_THEN `cball (x:real^N,min d e) INTER (s UNION t) =
                  cball(x,d) INTER cball (x,e) INTER t` SUBST1_TAC
    THENL [REWRITE_TAC[CBALL_MIN_INTER] THEN ASM SET_TAC[]; ALL_TAC]] THEN
  ASM_MESON_TAC[CLOSED_INTER; CLOSED_CBALL]);;

let LOCALLY_COMPACT_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        locally compact s /\ locally compact t
        ==> locally compact (s PCROSS t)`,
  MATCH_MP_TAC LOCALLY_PCROSS THEN REWRITE_TAC[COMPACT_PCROSS]);;

let LOCALLY_COMPACT_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        locally compact (s PCROSS t) <=>
        s = {} \/ t = {} \/ locally compact s /\ locally compact t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LOCALLY_COMPACT_PCROSS; PCROSS_EMPTY; LOCALLY_EMPTY] THEN
  MATCH_MP_TAC(TAUT `(~p ==> s) /\ (~q ==> r) ==> p \/ q \/ r /\ s`) THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THENL
   [X_GEN_TAC `a:real^M`; X_GEN_TAC `b:real^N`] THEN
  DISCH_TAC THEN FIRST_ASSUM
   (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] LOCALLY_COMPACT_INTER))
  THENL
   [DISCH_THEN(MP_TAC o SPEC `{a:real^M} PCROSS (:real^N)`);
    DISCH_THEN(MP_TAC o SPEC `(:real^M) PCROSS {b:real^N}`)] THEN
  ASM_SIMP_TAC[LOCALLY_COMPACT_PCROSS; CLOSED_IMP_LOCALLY_COMPACT;
               CLOSED_UNIV; CLOSED_SING; INTER_PCROSS; INTER_UNIV;
               SET_RULE `a IN s ==> s INTER {a} = {a}`] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_PCROSS_SING; HOMEOMORPHIC_LOCAL_COMPACTNESS]);;

let OPEN_IN_LOCALLY_COMPACT = prove
 (`!s t:real^N->bool.
        locally compact s
        ==> (open_in (subtopology euclidean s) t <=>
             t SUBSET s /\
             !k. compact k /\ k SUBSET s
                 ==> open_in (subtopology euclidean k) (k INTER t))`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LOCALLY_COMPACT]) THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    STRIP_TAC THEN EXISTS_TAC `t INTER u:real^N->bool` THEN
    ASM_REWRITE_TAC[IN_INTER; INTER_SUBSET] THEN
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `closure u:real^N->bool`) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `(closure u:real^N->bool) SUBSET v` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
        REWRITE_TAC[COMPACT_CLOSURE] THEN
        ASM_MESON_TAC[SUBSET_TRANS; BOUNDED_SUBSET; COMPACT_IMP_BOUNDED]];
      REWRITE_TAC[OPEN_IN_OPEN] THEN MATCH_MP_TAC MONO_EXISTS THEN
      MP_TAC(ISPEC `u:real^N->bool` CLOSURE_SUBSET) THEN SET_TAC[]]]);;

let LOCALLY_COMPACT_PROPER_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\
        (!k. k SUBSET (IMAGE f s) /\ compact k
             ==> compact {x | x IN s /\ f x IN k})
        ==> (locally compact s <=> locally compact (IMAGE f s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`;
                 `IMAGE (f:real^M->real^N) s`] PROPER_MAP) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[LOCALLY_COMPACT_ALT] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LOCALLY_COMPACT_COMPACT_ALT]) THEN
    DISCH_THEN(MP_TAC o SPEC `{x | x IN s /\ (f:real^M->real^N) x = y}`) THEN
    ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?v. open_in (subtopology euclidean (IMAGE f s)) v /\
          y IN v /\
          {x | x IN s /\ (f:real^M->real^N) x IN v} SUBSET u`
    MP_TAC THENL
     [GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o LAND_CONV)
       [GSYM SING_SUBSET] THEN
      MATCH_MP_TAC CLOSED_MAP_OPEN_SUPERSET_PREIMAGE THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_SING];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `closure v SUBSET IMAGE (f:real^M->real^N) (closure u)`
      ASSUME_TAC THENL
       [TRANS_TAC SUBSET_TRANS `closure(IMAGE (f:real^M->real^N) u)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SUBSET_CLOSURE THEN
          REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
          ASM SET_TAC[];
          MATCH_MP_TAC CLOSURE_MINIMAL THEN
          SIMP_TAC[CLOSURE_SUBSET; IMAGE_SUBSET] THEN
          MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
          MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]];
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_CLOSURE] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          BOUNDED_SUBSET)) THEN
        MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]]];
    REWRITE_TAC[LOCALLY_COMPACT_ALT] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LOCALLY_COMPACT_ALT]) THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `closure v:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `{x | x IN s /\ (f:real^M->real^N) x IN v}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
      ASM_MESON_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `closure {x | x IN s /\ f x IN v} SUBSET
      {x | x IN s /\ (f:real^M->real^N) x IN closure v}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      MP_TAC(ISPEC `v:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_CLOSURE] THEN
      ASM_MESON_TAC[COMPACT_IMP_BOUNDED; BOUNDED_SUBSET]]]);;

let LOCALLY_COMPACT_PROPER_IMAGE = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\
        (!k. k SUBSET (IMAGE f s) /\ compact k
             ==> compact {x | x IN s /\ f x IN k}) /\
        locally compact s
        ==> locally compact (IMAGE f s)`,
  MESON_TAC[LOCALLY_COMPACT_PROPER_IMAGE_EQ]);;

let MUMFORD_LEMMA = prove
 (`!f:real^M->real^N s t y.
        f continuous_on s /\ IMAGE f s SUBSET t /\ locally compact s /\
        y IN t /\ compact {x | x IN s /\ f x = y}
        ==> ?u v. open_in (subtopology euclidean s) u /\
                  open_in (subtopology euclidean t) v /\
                  {x | x IN s /\ f x = y} SUBSET u /\ y IN v /\
                  IMAGE f u SUBSET v /\
                  (!k. k SUBSET v /\ compact k
                       ==> compact {x | x IN u /\ f x IN k})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `{x | x IN s /\ (f:real^M->real^N) x = y}` o
   GEN_REWRITE_RULE I [LOCALLY_COMPACT_COMPACT]) THEN
  ASM_REWRITE_TAC[SUBSET_RESTRICT; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `v:real^M->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(closure u:real^M->bool) SUBSET v` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(closure u:real^M->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CLOSURE] THEN
    ASM_MESON_TAC[BOUNDED_SUBSET; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!b. open_in (subtopology euclidean t) b /\ y IN b
        ==> u INTER {x | x IN s /\ (f:real^M->real^N) x IN b} PSUBSET
            closure u INTER {x | x IN s /\ (f:real^M->real^N) x IN b}`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PSUBSET] THEN
    SIMP_TAC[CLOSURE_SUBSET;
             SET_RULE `s SUBSET t ==> s INTER u SUBSET t INTER u`] THEN
    MATCH_MP_TAC(MESON[] `!P. ~P s /\ P t ==> ~(s = t)`) THEN
    EXISTS_TAC
     `\a. !k. k SUBSET b /\ compact k
              ==> compact {x | x IN a /\ (f:real^M->real^N) x IN k}` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPECL
       [`u INTER {x | x IN s /\ (f:real^M->real^N) x IN b}`;
        `b:real^N->bool`]) THEN
      ASM_REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN ANTS_TAC THENL
       [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN ASM SET_TAC[];
        ASM SET_TAC[]];
      X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `{x | x IN closure u INTER {x | x IN s /\ f x IN b} /\ f x IN k} =
        v INTER {x | x IN closure u /\ (f:real^M->real^N) x IN k}`
      SUBST1_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC COMPACT_INTER_CLOSED] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_CLOSURE] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_TRANS]];
    DISCH_THEN(MP_TAC o GEN `n:num` o SPEC
     `t INTER ball(y:real^N,inv(&n + &1))`) THEN
    SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL; IN_INTER; CENTRE_IN_BALL] THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    SIMP_TAC[CLOSURE_SUBSET; SET_RULE
     `u SUBSET u'
      ==> (u INTER t PSUBSET u' INTER t <=>
           ?x. x IN u' /\ ~(x IN u) /\ x IN t)`] THEN
    REWRITE_TAC[SKOLEM_THM; IN_ELIM_THM; IN_BALL; FORALL_AND_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num->real^M` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `closure u:real^M->bool` compact) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:num->real^M`) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`l:real^M`; `r:num->num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:real^M->real^N) l = y` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `(f:real^M->real^N) o x o (r:num->num)` THEN
      ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(f:real^M->real^N) continuous_on closure u` MP_TAC THENL
         [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
        REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[o_THM];
        REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC LIM_SUBSEQUENCE THEN
        ASM_REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC `N:num` THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
        DISCH_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        TRANS_TAC REAL_LT_TRANS `inv(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
        TRANS_TAC REAL_LT_TRANS `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_INV2 THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_in]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `l:real^M`)) THEN
      REWRITE_TAC[NOT_IMP; NOT_EXISTS_THM] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `e:real` THEN STRIP_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
      ASM_REWRITE_TAC[LE_REFL; o_THM] THEN ASM SET_TAC[]]]);;

