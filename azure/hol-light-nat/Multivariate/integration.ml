open Hol_core
open Products
open Floor
open Card
open Permutations
open Determinants
open Vectors
open Topology
open Convex
open Paths
open Polytope
open Dimension
open Derivatives
include Integration4

(* ------------------------------------------------------------------------- *)
(* Second mean value theorem and corollaries.                                *)
(* ------------------------------------------------------------------------- *)

let SECOND_MEAN_VALUE_THEOREM_FULL = prove
 (`!f:real^1->real^1 g a b.
        ~(interval[a,b] = {}) /\
        f integrable_on interval [a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                ((\x. g x % f x) has_integral
                 (g(a) % integral (interval[a,c]) f +
                  g(b) % integral (interval[c,b]) f)) (interval[a,b])`,
  let lemma1 = prove
   (`!f:real->real s.
      (!x. x IN s ==> &0 <= f x /\ f x <= &1)
      ==> (!n x. x IN s /\ ~(n = 0)
                 ==> abs(f x -
                         sum(1..n) (\k. if &k / &n <= f(x)
                                        then inv(&n) else &0)) < inv(&n))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?m. floor(&n * (f:real->real) x) = &m` CHOOSE_TAC THENL
     [MATCH_MP_TAC FLOOR_POS THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `!k. &k / &n <= (f:real->real) x <=> k <= m` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
      SIMP_TAC[REAL_LE_FLOOR; INTEGER_CLOSED; REAL_MUL_SYM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; real_div; REAL_ADD_RDISTRIB] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[REAL_ARITH `y <= &1 /\ &0 < i ==> ~(&1 + i <= y)`;
                 REAL_LT_INV_EQ; REAL_OF_NUM_LT; LE_1; NOT_LE] THEN
    SIMP_TAC[IN_NUMSEG; ARITH_RULE
     `m < n + 1 ==> ((1 <= k /\ k <= n) /\ k <= m <=> 1 <= k /\ k <= m)`] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM numseg; SUM_CONST_NUMSEG; ADD_SUB] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `abs(&n)` THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_NUM; REAL_MUL_RINV; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1; REAL_SUB_LDISTRIB; GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `f <= x /\ x < f + &1 ==> abs(x - f) < &1`) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[FLOOR]) in
  let lemma2 = prove
   (`!f:real^1->real^N g a b.
          f integrable_on interval[a,b] /\
          (!x y. drop x <= drop y ==> g(x) <= g(y))
          ==> {(\x. if c <= g(x) then f x else vec 0) | c IN (:real)}
              equiintegrable_on interval[a,b]`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM EQUIINTEGRABLE_ON_SING]) THEN
    DISCH_THEN(fun th ->
     MP_TAC(SPEC `f:real^1->real^N` (MATCH_MP (REWRITE_RULE[IMP_CONJ]
       EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GE) th)) THEN
     MP_TAC(SPEC `f:real^1->real^N` (MATCH_MP (REWRITE_RULE[IMP_CONJ]
       EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GT) th)) THEN
      MP_TAC th) THEN
    SIMP_TAC[IN_SING; REAL_LE_REFL] THEN
    SUBGOAL_THEN `{(\x. vec 0):real^1->real^N} equiintegrable_on interval[a,b]`
    MP_TAC THENL
     [REWRITE_TAC[EQUIINTEGRABLE_ON_SING; INTEGRABLE_CONST]; ALL_TAC] THEN
    REPEAT(ONCE_REWRITE_TAC[IMP_IMP] THEN
           DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_UNION)) THEN
    REWRITE_TAC[NUMSEG_SING; DIMINDEX_1; IN_SING] THEN
    REWRITE_TAC[SET_RULE `{m i c h | i = 1 /\ c IN (:real) /\ h = f} =
                          {m 1 c f | c IN (:real)}`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
    X_GEN_TAC `y:real` THEN
    ASM_CASES_TAC `!x. y <= (g:real^1->real) x` THENL
     [ASM_REWRITE_TAC[ETA_AX; IN_UNION; IN_SING]; ALL_TAC] THEN
    ASM_CASES_TAC `!x. ~(y <= (g:real^1->real) x)` THENL
     [ASM_REWRITE_TAC[ETA_AX; IN_UNION; IN_SING]; ALL_TAC] THEN
    MP_TAC(ISPEC `IMAGE drop {x | y <= (g:real^1->real) x}` INF) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IMAGE_EQ_EMPTY] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_TOTAL];
      STRIP_TAC THEN REWRITE_TAC[real_gt; real_ge]] THEN
    REWRITE_TAC[IN_UNION; GSYM DISJ_ASSOC] THEN
    ASM_CASES_TAC `y <= g(lift(inf(IMAGE drop {x | y <= g x})))` THENL
     [REPEAT DISJ2_TAC; REPLICATE_TAC 2 DISJ2_TAC THEN DISJ1_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `inf(IMAGE drop {x | y <= g x})` THEN
    REWRITE_TAC[FUN_EQ_THM] THEN
    MATCH_MP_TAC(MESON[]
     `(!x. P x <=> Q x)
      ==> !x. (if P x then f x else b) = (if Q x then f x else b)`) THEN
    X_GEN_TAC `x:real^1` THEN REWRITE_TAC[GSYM REAL_NOT_LE; GSYM drop] THEN
    ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LT_ANTISYM; REAL_LE_TRANS; LIFT_DROP]) in
  let lemma3 = prove
   (`!f:real^1->real^N g a b.
          f integrable_on interval[a,b] /\
          (!x y. drop x <= drop y ==> g(x) <= g(y))
          ==> {(\x. vsum (1..n)
                     (\k. if &k / &n <= g x then inv(&n) % f(x) else vec 0)) |
               ~(n = 0)}
              equiintegrable_on interval[a,b]`,
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o
     MATCH_MP lemma2) THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (INST_TYPE [`:num`,`:A`] EQUIINTEGRABLE_SUM)) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN X_GEN_TAC `n:num` THEN
    DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`1..n`; `\k:num. inv(&n)`;
     `\k x. if &k / &n <= g x then (f:real^1->real^N) x else vec 0`] THEN
    ASM_SIMP_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RINV; REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[FINITE_NUMSEG; COND_RAND; COND_RATOR; VECTOR_MUL_RZERO] THEN
    X_GEN_TAC `k:num` THEN
    REWRITE_TAC[IN_NUMSEG; REAL_LE_INV_EQ; REAL_POS] THEN STRIP_TAC THEN
    EXISTS_TAC `&k / &n` THEN REWRITE_TAC[]) in
  let lemma4 = prove
   (`!f:real^1->real^1 g a b.
          ~(interval[a,b] = {}) /\
          f integrable_on interval[a,b] /\
          (!x y. drop x <= drop y ==> g(x) <= g(y)) /\
          (!x. x IN interval[a,b] ==> &0 <= g x /\ g x <= &1)
          ==> (\x. g(x) % f(x)) integrable_on interval[a,b] /\
              ?c. c IN interval[a,b] /\
                  integral (interval[a,b]) (\x. g(x) % f(x)) =
                  integral (interval[c,b]) f`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?m M. IMAGE (\x. integral (interval[x,b]) (f:real^1->real^1))
                  (interval[a,b]) = interval[m,M]`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM CONNECTED_COMPACT_INTERVAL_1] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE;
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE] THEN
      ASM_SIMP_TAC[INDEFINITE_INTEGRAL_CONTINUOUS_LEFT; CONVEX_CONNECTED;
                   CONVEX_INTERVAL; COMPACT_INTERVAL];
      ALL_TAC] THEN
    MP_TAC(ISPECL[`f:real^1->real^1`; `g:real^1->real`; `a:real^1`; `b:real^1`]
          lemma3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!n. ?c. c IN interval[a,b] /\
              integral (interval[c,b]) (f:real^1->real^1) =
              integral (interval[a,b])
                (\x. vsum (1..n)
                    (\k. if &k / &n <= g x then inv(&n) % f x else vec 0))`
    MP_TAC THENL
     [X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THENL
       [ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_EQ; INTEGRAL_0] THEN
        EXISTS_TAC `b:real^1` THEN ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
        SIMP_TAC[INTEGRAL_NULL; CONTENT_EQ_0_1; REAL_LE_REFL];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`f:real^1->real^1`; `g:real^1->real`;
                     `a:real^1`; `b:real^1`] lemma2) THEN
      ASM_REWRITE_TAC[equiintegrable_on; FORALL_IN_GSPEC; IN_UNIV] THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
      REWRITE_TAC[MESON[VECTOR_MUL_RZERO]
       `(if p then a % x else vec 0:real^1) =
        a % (if p then x else vec 0)`] THEN
      ASM_SIMP_TAC[VSUM_LMUL; INTEGRAL_CMUL; INTEGRABLE_VSUM; ETA_AX;
                   FINITE_NUMSEG; INTEGRAL_VSUM] THEN
      SUBGOAL_THEN
       `!y:real. ?d:real^1.
          d IN interval[a,b] /\
          integral (interval[a,b]) (\x. if y <= g x then f x else vec 0) =
          integral (interval[d,b]) (f:real^1->real^1)`
      MP_TAC THENL
       [X_GEN_TAC `y:real` THEN
        SUBGOAL_THEN
         `{x | y <= g x} = {} \/
          {x | y <= g x} = (:real^1) \/
          (?a. {x | y <= g x} = {x | a <= drop x}) \/
          (?a. {x | y <= g x} = {x | a < drop x})`
        MP_TAC THENL
         [MATCH_MP_TAC(TAUT `(~a /\ ~b ==> c \/ d) ==> a \/ b \/ c \/ d`) THEN
          DISCH_TAC THEN
          MP_TAC(ISPEC `IMAGE drop {x | y <= (g:real^1->real) x}` INF) THEN
          ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IMAGE_EQ_EMPTY] THEN
          ANTS_TAC THENL
           [FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
            REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
            ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_TOTAL];
            STRIP_TAC] THEN
          ASM_CASES_TAC `y <= g(lift(inf(IMAGE drop {x | y <= g x})))` THENL
           [DISJ1_TAC; DISJ2_TAC] THEN
          REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
          EXISTS_TAC `inf(IMAGE drop {x | y <= g x})` THEN
          REWRITE_TAC[FUN_EQ_THM] THEN
          X_GEN_TAC `x:real^1` THEN
          REWRITE_TAC[GSYM REAL_NOT_LE; GSYM drop] THEN
          ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LT_ANTISYM;
                        REAL_LE_TRANS; LIFT_DROP];
          REWRITE_TAC[EXTENSION; IN_UNIV; NOT_IN_EMPTY; IN_ELIM_THM] THEN
          DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
           [EXISTS_TAC `b:real^1` THEN ASM_REWRITE_TAC[] THEN
            SIMP_TAC[INTEGRAL_NULL; CONTENT_EQ_0_1; REAL_LE_REFL] THEN
            ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTEGRAL_0];
            ALL_TAC] THEN
          DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
           [EXISTS_TAC `a:real^1` THEN
            ASM_REWRITE_TAC[ETA_AX; ENDS_IN_INTERVAL];
            ALL_TAC] THEN
          GEN_REWRITE_TAC LAND_CONV [OR_EXISTS_THM] THEN
          REWRITE_TAC[EXISTS_DROP] THEN
          DISCH_THEN(X_CHOOSE_THEN `d:real^1` ASSUME_TAC) THEN
          ASM_CASES_TAC `drop d < drop a` THENL
           [EXISTS_TAC `a:real^1` THEN
            ASM_REWRITE_TAC[ETA_AX; ENDS_IN_INTERVAL] THEN
            MATCH_MP_TAC INTEGRAL_EQ THEN
            REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; NOT_IN_EMPTY] THEN
            GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `~(y <= (g:real^1->real) x)` THEN
            FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
            ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          ASM_CASES_TAC `drop b < drop d` THENL
           [EXISTS_TAC `b:real^1` THEN
            SIMP_TAC[INTEGRAL_NULL; CONTENT_EQ_0_1; REAL_LE_REFL] THEN
            ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTEGRAL_0] THEN
            MATCH_MP_TAC INTEGRAL_EQ_0 THEN REWRITE_TAC[IN_INTERVAL_1] THEN
            REPEAT STRIP_TAC THEN
            COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `y <= (g:real^1->real) x` THEN
            FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
            ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          EXISTS_TAC `d:real^1` THEN
          ASM_REWRITE_TAC[IN_INTERVAL_1; GSYM REAL_NOT_LT] THEN
          ONCE_REWRITE_TAC[SET_RULE
            `~((g:real^1->real) x < y) <=> x IN {x | ~(g x < y)}`] THEN
          REWRITE_TAC[INTEGRAL_RESTRICT_INTER] THEN
          MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
          MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{d:real^1}` THEN
          REWRITE_TAC[NEGLIGIBLE_SING; REAL_NOT_LT; SUBSET] THEN GEN_TAC THEN
          REWRITE_TAC[SUBSET; IN_UNION; IN_INTER; IN_DIFF; IN_INTERVAL_1;
                      IN_ELIM_THM; IN_SING; GSYM DROP_EQ] THEN
          FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC];
        DISCH_THEN(MP_TAC o GEN `k:num` o SPEC `&k / &n`) THEN
        REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC `d:num->real^1` THEN STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
         `IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y`)) THEN
        REWRITE_TAC[GSYM VSUM_LMUL] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC(REWRITE_RULE[CONVEX_INDEXED]
         (CONJUNCT1(SPEC_ALL CONVEX_INTERVAL))) THEN
        REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_INV_EQ; REAL_POS] THEN
        ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ] THEN ASM SET_TAC[]];
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
      X_GEN_TAC `c:num->real^1` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM)] THEN
    SUBGOAL_THEN `compact(interval[a:real^1,b])` MP_TAC THENL
     [REWRITE_TAC[COMPACT_INTERVAL]; REWRITE_TAC[compact]] THEN
    DISCH_THEN(MP_TAC o SPEC `c:num->real^1`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`d:real^1`; `s:num->num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\n:num x. vsum (1..(s n))
                      (\k. if &k / &(s n) <= g x
                           then inv(&(s n)) % (f:real^1->real^1) x
                           else vec 0)`;
      `\x. g x % (f:real^1->real^1) x`; `a:real^1`; `b:real^1`]
     EQUIINTEGRABLE_LIMIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC EQUIINTEGRABLE_SUBSET THEN
        EXISTS_TAC
         `{\x. vsum(1..0) (\k. if &k / &0 <= g x
                               then inv(&0) % (f:real^1->real^1) x else vec 0)}
          UNION
          {\x. vsum (1..n)
                    (\k. if &k / &n <= g x then inv (&n) % f x else vec 0)
           | ~(n = 0)}` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC EQUIINTEGRABLE_UNION THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[EQUIINTEGRABLE_ON_SING; VSUM_CLAUSES_NUMSEG;
                      ARITH_EQ] THEN
          REWRITE_TAC[INTEGRABLE_0];
          REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV; IN_UNION] THEN
          REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
          X_GEN_TAC `n:num` THEN ASM_CASES_TAC `(s:num->num) n = 0` THEN
          ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
          EXISTS_TAC `(s:num->num) n` THEN ASM_REWRITE_TAC[]];
        X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[MESON[VECTOR_MUL_LZERO]
         `(if p then a % x else vec 0) = (if p then a else &0) % x`] THEN
        REWRITE_TAC[VSUM_RMUL] THEN MATCH_MP_TAC LIM_VMUL THEN
        REWRITE_TAC[LIM_SEQUENTIALLY; o_DEF; DIST_LIFT] THEN
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        MP_TAC(ISPEC `e:real` REAL_ARCH_INV) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC `N:num` THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
        DISCH_TAC THEN
        ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
        MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&n)` THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL
           [`(g:real^1->real) o lift`; `IMAGE drop (interval[a,b])`]
            lemma1) THEN
          ASM_REWRITE_TAC[FORALL_IN_IMAGE; o_DEF; LIFT_DROP; IMP_CONJ;
                          RIGHT_FORALL_IMP_THM] THEN
          REWRITE_TAC[IMP_IMP] THEN DISCH_TAC THEN
          MATCH_MP_TAC REAL_LTE_TRANS THEN
          EXISTS_TAC `inv(&((s:num->num) n))` THEN CONJ_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_LE_INV2 THEN
            REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT]] THEN
          FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP MONOTONE_BIGGER) THEN
          ASM_ARITH_TAC;
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
          REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC]];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `d:real^1` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `\n. integral (interval [c((s:num->num) n),b])
                               (f:real^1->real^1)` THEN
      ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
      MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`]
          INDEFINITE_INTEGRAL_CONTINUOUS_LEFT) THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      DISCH_THEN(MP_TAC o SPEC `d:real^1`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONTINUOUS_WITHIN_SEQUENTIALLY] THEN
      DISCH_THEN(MP_TAC o SPEC `(c:num->real^1) o (s:num->num)`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[o_DEF]]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^1->real) a <= g b` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
    ASM_MESON_TAC[INTERVAL_EQ_EMPTY_1; REAL_LET_TOTAL];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `!x. x IN interval[a,b] ==> g(x) % (f:real^1->real^1)(x) = g(a) % f x`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^1` THEN
      REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [IN_INTERVAL_1; INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
      ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_TRANS; REAL_LE_TOTAL];
      ALL_TAC] THEN
    EXISTS_TAC `a:real^1` THEN ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
    MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
    EXISTS_TAC `\x. g(a:real^1) % (f:real^1->real^1) x` THEN
    ASM_SIMP_TAC[INTEGRAL_NULL; CONTENT_EQ_0_1; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
    ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]] THEN
  MP_TAC(ISPECL
   [`f:real^1->real^1`;
    `\x. if drop x < drop a then &0
         else if drop b < drop x then &1
         else (g(x) - g(a)) / (g(b) - g(a))`;
    `a:real^1`; `b:real^1`]
   lemma4) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN
    REPEAT GEN_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL]) THEN
    TRY ASM_REAL_ARITH_TAC THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; REAL_LE_DIV2_EQ; REAL_SUB_LT] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_SUB_LE;
                    REAL_ARITH `x - a <= y - a <=> x <= y`] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^1` THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^1->real) b - g a` o
        MATCH_MP HAS_INTEGRAL_CMUL) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^1->real)(a)` o
      MATCH_MP HAS_INTEGRAL_CMUL) THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_ADD) THEN
  MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `c:real^1`]
        INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_INTERVAL_1]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_ARITH
   `ga % (i1 + i2) + (gb - ga) % i2:real^N = ga % i1 + gb % i2`] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
  X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM REAL_NOT_LE; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_SUB_LT] THEN
  VECTOR_ARITH_TAC);;

let SECOND_MEAN_VALUE_THEOREM = prove
 (`!f:real^1->real^1 g a b.
        ~(interval[a,b] = {}) /\
        f integrable_on interval [a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                integral (interval[a,b]) (\x. g x % f x) =
                 g(a) % integral (interval[a,c]) f +
                 g(b) % integral (interval[c,b]) f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SECOND_MEAN_VALUE_THEOREM_FULL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^1` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REWRITE_TAC[]);;

let SECOND_MEAN_VALUE_THEOREM_GEN_FULL = prove
 (`!f:real^1->real^1 g a b u v.
        ~(interval[a,b] = {}) /\ f integrable_on interval [a,b] /\
        (!x. x IN interval(a,b) ==> u <= g x /\ g x <= v) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                ((\x. g x % f x) has_integral
                 (u % integral (interval[a,c]) f +
                  v % integral (interval[c,b]) f)) (interval[a,b])`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `b:real^1 = a` THENL
   [EXISTS_TAC `a:real^1` THEN ASM_REWRITE_TAC[INTERVAL_SING; IN_SING] THEN
    ASM_SIMP_TAC[GSYM INTERVAL_SING; INTEGRAL_NULL; CONTENT_EQ_0_1;
      VECTOR_ADD_LID; REAL_LE_REFL; VECTOR_MUL_RZERO; HAS_INTEGRAL_NULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop a < drop b` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LE; DROP_EQ; REAL_LT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `u <= v` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERVAL_EQ_EMPTY_1; MEMBER_NOT_EMPTY; REAL_NOT_LT;
                  REAL_LE_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:real^1->real^1`;
    `\x:real^1. if x = a then u else if x = b then v else g x:real`;
    `a:real^1`; `b:real^1`] SECOND_MEAN_VALUE_THEOREM_FULL) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    ASM_CASES_TAC `x:real^1 = a` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[REAL_LE_REFL; INTERVAL_CASES_1]; ALL_TAC] THEN
    ASM_CASES_TAC `y:real^1 = b` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[REAL_LE_REFL; INTERVAL_CASES_1]; ALL_TAC] THEN
    REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM DROP_EQ]) THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^1` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC
     (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
        HAS_INTEGRAL_SPIKE) THEN
    EXISTS_TAC `{a:real^1,b}` THEN
    SIMP_TAC[NEGLIGIBLE_EMPTY; NEGLIGIBLE_INSERT; IN_DIFF; IN_INSERT;
             NOT_IN_EMPTY; DE_MORGAN_THM]]);;

let SECOND_MEAN_VALUE_THEOREM_GEN = prove
 (`!f:real^1->real^1 g a b u v.
        ~(interval[a,b] = {}) /\ f integrable_on interval [a,b] /\
        (!x. x IN interval(a,b) ==> u <= g x /\ g x <= v) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                integral (interval[a,b]) (\x. g x % f x) =
                u % integral (interval[a,c]) f +
                v % integral (interval[c,b]) f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SECOND_MEAN_VALUE_THEOREM_GEN_FULL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^1` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REWRITE_TAC[]);;

let SECOND_MEAN_VALUE_THEOREM_BONNET_FULL = prove
 (`!f:real^1->real^1 g a b.
        ~(interval[a,b] = {}) /\ f integrable_on interval [a,b] /\
        (!x. x IN interval[a,b] ==> &0 <= g x) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                ((\x. g x % f x) has_integral
                 (g(b) % integral (interval[c,b]) f)) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`f:real^1->real^1`; `g:real^1->real`; `a:real^1`; `b:real^1`;
    `&0`; `(g:real^1->real) b`] SECOND_MEAN_VALUE_THEOREM_GEN_FULL) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

let SECOND_MEAN_VALUE_THEOREM_BONNET = prove
 (`!f:real^1->real^1 g a b.
        ~(interval[a,b] = {}) /\ f integrable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> &0 <= g x) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                integral (interval[a,b]) (\x. g x % f x) =
                g(b) % integral (interval[c,b]) f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SECOND_MEAN_VALUE_THEOREM_BONNET_FULL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^1` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REWRITE_TAC[]);;

let INTEGRABLE_INCREASING_PRODUCT = prove
 (`!f:real^1->real^N g a b.
        f integrable_on interval[a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g(x) <= g(y))
        ==> (\x. g(x) % f(x)) integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `interval[a:real^1,b] = {}` THEN
  ASM_REWRITE_TAC[INTEGRABLE_ON_EMPTY] THEN
  ONCE_REWRITE_TAC[INTEGRABLE_COMPONENTWISE] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift((f:real^1->real^N) x$i)`;
                 `g:real^1->real`; `a:real^1`; `b:real^1`]
    SECOND_MEAN_VALUE_THEOREM_FULL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[INTEGRABLE_COMPONENTWISE]) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[VECTOR_MUL_COMPONENT; LIFT_CMUL; integrable_on] THEN
    MESON_TAC[]]);;

let INTEGRABLE_INCREASING_PRODUCT_UNIV = prove
 (`!f:real^1->real^N g B.
        f integrable_on (:real^1) /\
        (!x y. drop x <= drop y ==> g x <= g y) /\
        (!x. abs(g x) <= B)
         ==> (\x. g x % f x) integrable_on (:real^1)`,
  let lemma = prove
   (`!f:real^1->real^1 g B.
          f integrable_on (:real^1) /\
          (!x y. drop x <= drop y ==> g x <= g y) /\
          (!x. abs(g x) <= B)
           ==> (\x. g x % f x) integrable_on (:real^1)`,
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INTEGRABLE_ALT_SUBSET] THEN
    REWRITE_TAC[IN_UNIV; ETA_AX] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_INCREASING_PRODUCT THEN
      ASM_SIMP_TAC[];
      DISCH_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / (&8 * abs B + &8)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &8 * abs B + &8`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(ball(vec 0:real^1,C) = {})` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[BALL_EQ_EMPTY; REAL_NOT_LE]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`; `c:real^1`; `d:real^1`] THEN
    STRIP_TAC THEN SUBGOAL_THEN
     `~(interval[a:real^1,b] = {}) /\ ~(interval[c:real^1,d] = {})`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_INTERVAL_1]) THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\x. g x % (f:real^1->real^1) x`;
                   `c:real^1`; `b:real^1`; `a:real^1`] INTEGRAL_COMBINE) THEN
    MP_TAC(ISPECL [`\x. g x % (f:real^1->real^1) x`;
                   `c:real^1`; `d:real^1`; `b:real^1`] INTEGRAL_COMBINE) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_NOT_LE; NORM_ARITH
     `norm(ab - ((ca + ab) + bd):real^1) = norm(ca + bd)`] THEN
    MP_TAC(ISPECL[`f:real^1->real^1`; `g:real^1->real`; `c:real^1`; `a:real^1`]
          SECOND_MEAN_VALUE_THEOREM) THEN
    ASM_SIMP_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL[`f:real^1->real^1`; `g:real^1->real`; `b:real^1`; `d:real^1`]
          SECOND_MEAN_VALUE_THEOREM) THEN
    ASM_SIMP_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^1` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!x y. drop y <= drop a
            ==> norm(integral (interval[x,y]) (f:real^1->real^1))
                < e / (&4 * abs B + &4)`
     (LABEL_TAC "L")
    THENL
     [REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `drop x <= drop y` THENL
       [FIRST_X_ASSUM(fun th ->
         MP_TAC(SPECL[`a:real^1`; `b:real^1`; `y:real^1`; `b:real^1`] th) THEN
         MP_TAC(SPECL[`a:real^1`; `b:real^1`; `x:real^1`; `b:real^1`] th)) THEN
        ASM_REWRITE_TAC[SUBSET_INTERVAL_1; REAL_LE_REFL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`f:real^1->real^1`; `x:real^1`; `b:real^1`; `y:real^1`]
          INTEGRAL_COMBINE) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
        MATCH_MP_TAC(NORM_ARITH
         `&2 * d = e
          ==> norm(ab - (xy + yb)) < d
              ==> norm(ab - yb) < d
                  ==> norm(xy:real^1) < e`) THEN
        CONV_TAC REAL_FIELD;
        SUBGOAL_THEN `interval[x:real^1,y] = {}` SUBST1_TAC THENL
         [REWRITE_TAC[INTERVAL_EQ_EMPTY_1] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[INTEGRAL_EMPTY; NORM_0] THEN
          MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x y. drop b <= drop x
            ==> norm(integral (interval[x,y]) (f:real^1->real^1))
                < e / (&4 * abs B + &4)`
     (LABEL_TAC "R")
    THENL
     [REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `drop x <= drop y` THENL
       [FIRST_X_ASSUM(fun th ->
         MP_TAC(SPECL[`a:real^1`; `b:real^1`; `a:real^1`; `x:real^1`] th) THEN
         MP_TAC(SPECL[`a:real^1`; `b:real^1`; `a:real^1`; `y:real^1`] th)) THEN
        ASM_REWRITE_TAC[SUBSET_INTERVAL_1; REAL_LE_REFL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `y:real^1`; `x:real^1`]
          INTEGRAL_COMBINE) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
        MATCH_MP_TAC(NORM_ARITH
         `&2 * d = e
          ==> norm(ab - (ax + xy)) < d
              ==> norm(ab - ax) < d
                  ==> norm(xy:real^1) < e`) THEN
        CONV_TAC REAL_FIELD;
        SUBGOAL_THEN `interval[x:real^1,y] = {}` SUBST1_TAC THENL
         [REWRITE_TAC[INTERVAL_EQ_EMPTY_1] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[INTEGRAL_EMPTY; NORM_0] THEN
          MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&4 * B * e / (&4 * abs B + &4)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `(norm a <= e /\ norm b <= e) /\ (norm c <= e /\ norm d <= e)
        ==> norm((a + b) + (c + d):real^1) <= &4 * e`) THEN
      REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        REMOVE_THEN "L" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        REMOVE_THEN "R" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ARITH
       `&4 * B * e / y < e <=> e * (&4 * B) / y < e * &1`] THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_LDIV_EQ;
                   REAL_ARITH `&0 < &4 * abs B + &4`] THEN
      REAL_ARITH_TAC]) in
  GEN_TAC THEN ONCE_REWRITE_TAC[INTEGRABLE_COMPONENTWISE] THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_MUL_COMPONENT; LIFT_CMUL] THEN
  MATCH_MP_TAC lemma THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[]);;

let INTEGRABLE_INCREASING = prove
 (`!f:real^1->real^N a b.
        (!x y i. x IN interval[a,b] /\ y IN interval[a,b] /\
                 drop x <= drop y /\ 1 <= i /\ i <= dimindex(:N)
                 ==> f(x)$i <= f(y)$i)
        ==> f integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[INTEGRABLE_COMPONENTWISE] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_RID] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_NUM] THEN
  MATCH_MP_TAC INTEGRABLE_INCREASING_PRODUCT THEN
  ASM_SIMP_TAC[INTEGRABLE_CONST]);;

let INTEGRABLE_INCREASING_1 = prove
 (`!f:real^1->real^1 a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> f integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_INCREASING THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[IMP_IMP; FORALL_1; DIMINDEX_1; GSYM drop]);;

let INTEGRABLE_DECREASING_PRODUCT = prove
 (`!f:real^1->real^N g a b.
        f integrable_on interval[a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g(y) <= g(x))
        ==> (\x. g(x) % f(x)) integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `x % y:real^N = --(--x % y)`] THEN
  MATCH_MP_TAC INTEGRABLE_NEG THEN
  MATCH_MP_TAC INTEGRABLE_INCREASING_PRODUCT THEN
  ASM_REWRITE_TAC[REAL_LE_NEG2]);;

let INTEGRABLE_DECREASING_PRODUCT_UNIV = prove
 (`!f:real^1->real^N g B.
        f integrable_on (:real^1) /\
        (!x y. drop x <= drop y ==> g y <= g x) /\
        (!x. abs(g x) <= B)
         ==> (\x. g x % f x) integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `x % y:real^N = --(--x % y)`] THEN
  MATCH_MP_TAC INTEGRABLE_NEG THEN
  MATCH_MP_TAC INTEGRABLE_INCREASING_PRODUCT_UNIV THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[REAL_LE_NEG2; REAL_ABS_NEG]);;

let INTEGRABLE_DECREASING = prove
 (`!f:real^1->real^N a b.
        (!x y i. x IN interval[a,b] /\ y IN interval[a,b] /\
                 drop x <= drop y /\ 1 <= i /\ i <= dimindex(:N)
                 ==> f(y)$i <= f(x)$i)
        ==> f integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [GSYM VECTOR_NEG_NEG] THEN
  MATCH_MP_TAC INTEGRABLE_NEG THEN MATCH_MP_TAC INTEGRABLE_INCREASING THEN
  ASM_SIMP_TAC[VECTOR_NEG_COMPONENT; REAL_LE_NEG2]);;

let INTEGRABLE_DECREASING_1 = prove
 (`!f:real^1->real^1 a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x))
        ==> f integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_DECREASING THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[IMP_IMP; FORALL_1; DIMINDEX_1; GSYM drop]);;

(* ------------------------------------------------------------------------- *)
(* Bounded variation and variation function, for real^1->real^N functions.   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_bounded_variation_on",(12,"right"));;

let has_bounded_variation_on = new_definition
 `(f:real^1->real^N) has_bounded_variation_on s <=>
        (\k. f(interval_upperbound k) - f(interval_lowerbound k))
        has_bounded_setvariation_on s`;;

let vector_variation = new_definition
 `vector_variation s (f:real^1->real^N) =
  set_variation s (\k. f(interval_upperbound k) - f(interval_lowerbound k))`;;

let HAS_BOUNDED_VARIATION_ON_EQ = prove
 (`!f g:real^1->real^N s.
        (!x. x IN s ==> f x = g x) /\ f has_bounded_variation_on s
        ==> g has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[has_bounded_variation_on] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_BOUNDED_SETVARIATION_ON_EQ) THEN
  SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND;
           GSYM INTERVAL_NE_EMPTY] THEN
  ASM_MESON_TAC[ENDS_IN_INTERVAL; SUBSET]);;

let VECTOR_VARIATION_EQ = prove
 (`!f g:real^1->real^N s.
        (!x. x IN s ==> f x = g x)
        ==> vector_variation s f = vector_variation s g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_variation] THEN
  MATCH_MP_TAC SET_VARIATION_EQ THEN
  SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND;
           GSYM INTERVAL_NE_EMPTY] THEN
  ASM_MESON_TAC[ENDS_IN_INTERVAL; SUBSET]);;

let HAS_BOUNDED_VARIATION_ON_COMPONENTWISE = prove
 (`!f:real^1->real^N s.
        f has_bounded_variation_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift(f x$i)) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_BOUNDED_SETVARIATION_ON_COMPONENTWISE] THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT; LIFT_SUB]);;

let VARIATION_EQUAL_LEMMA = prove
 (`!ms ms'.
        (!s. ms'(ms s) = s /\ ms(ms' s) = s) /\
        (!d t. d division_of t
               ==> (IMAGE (IMAGE ms) d) division_of IMAGE ms t /\
                   (IMAGE (IMAGE ms') d) division_of IMAGE ms' t) /\
        (!a b. ~(interval[a,b] = {})
               ==> IMAGE ms' (interval [a,b]) = interval[ms' a,ms' b] \/
                   IMAGE ms' (interval [a,b]) = interval[ms' b,ms' a])
   ==> (!f:real^1->real^N s.
            (\x. f(ms' x)) has_bounded_variation_on (IMAGE ms s) <=>
            f has_bounded_variation_on s) /\
       (!f:real^1->real^N s.
            vector_variation (IMAGE ms s) (\x. f(ms' x)) =
            vector_variation s f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[has_bounded_variation_on; vector_variation] THEN
  GEN_REWRITE_TAC I [AND_FORALL_THM] THEN X_GEN_TAC `f:real^1->real^N` THEN
  MP_TAC(ISPECL
   [`\f k. (f:(real^1->bool)->real^N) (IMAGE (ms':real^1->real^1) k)`;
    `IMAGE (ms:real^1->real^1)`;
    `IMAGE (ms':real^1->real^1)`]
  SETVARIATION_EQUAL_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID; IMAGE_SUBSET] THEN
    MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [AND_FORALL_THM] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `\k. (f:real^1->real^N) (interval_upperbound k) -
                     f (interval_lowerbound k)` th)) THEN
  REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  GEN_REWRITE_TAC I [AND_FORALL_THM] THEN X_GEN_TAC `s:real^1->bool` THEN
  REWRITE_TAC[has_bounded_setvariation_on; set_variation] THEN
  CONJ_TAC THENL
   [REPLICATE_TAC 3 (AP_TERM_TAC THEN ABS_TAC) THEN
    REWRITE_TAC[TAUT `((p ==> q) <=> (p ==> r)) <=> p ==> (q <=> r)`] THEN
    STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC;
    AP_TERM_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
    GEN_TAC THEN STRIP_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN FIRST_ASSUM(fun th ->
   GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
  MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `IMAGE f s = s' ==> ~(s = {}) ==> IMAGE f s = s' /\ ~(s' = {})`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1]) THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1] THEN
  NORM_ARITH_TAC);;

let HAS_BOUNDED_VARIATION_ON_SUBSET = prove
 (`!f:real^1->real^N s t.
        f has_bounded_variation_on s /\ t SUBSET s
        ==> f has_bounded_variation_on t`,
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_SUBSET; has_bounded_variation_on]);;

let HAS_BOUNDED_VARIATION_ON_CONST = prove
 (`!s c:real^N. (\x. c) has_bounded_variation_on s`,
  REWRITE_TAC[has_bounded_variation_on; VECTOR_SUB_REFL;
              HAS_BOUNDED_SETVARIATION_ON_0]);;

let VECTOR_VARIATION_CONST = prove
 (`!s c:real^N. vector_variation s (\x. c) = &0`,
  REWRITE_TAC[vector_variation; VECTOR_SUB_REFL; SET_VARIATION_0]);;

let HAS_BOUNDED_VARIATION_ON_CMUL = prove
 (`!f:real^1->real^N c s.
        f has_bounded_variation_on s
        ==> (\x. c % f x) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; HAS_BOUNDED_SETVARIATION_ON_CMUL]);;

let HAS_BOUNDED_VARIATION_ON_NEG = prove
 (`!f:real^1->real^N s.
        f has_bounded_variation_on s
        ==> (\x. --f x) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  REWRITE_TAC[VECTOR_ARITH `--a - --b:real^N = --(a - b)`;
              HAS_BOUNDED_SETVARIATION_ON_NEG]);;

let HAS_BOUNDED_VARIATION_ON_ADD = prove
 (`!f g:real^1->real^N s.
        f has_bounded_variation_on s /\ g has_bounded_variation_on s
        ==> (\x. f x + g x) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  REWRITE_TAC[VECTOR_ARITH `(f + g) - (f' + g'):real^N = (f - f') + (g - g')`;
              HAS_BOUNDED_SETVARIATION_ON_ADD]);;

let HAS_BOUNDED_VARIATION_ON_SUB = prove
 (`!f g:real^1->real^N s.
        f has_bounded_variation_on s /\ g has_bounded_variation_on s
        ==> (\x. f x - g x) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  REWRITE_TAC[VECTOR_ARITH `(f - g) - (f' - g'):real^N = (f - f') - (g - g')`;
              HAS_BOUNDED_SETVARIATION_ON_SUB]);;

let HAS_BOUNDED_VARIATION_ON_COMPOSE_LINEAR = prove
 (`!f:real^1->real^M g:real^M->real^N s.
        f has_bounded_variation_on s /\ linear g
        ==> (g o f) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  SIMP_TAC[o_THM; GSYM LINEAR_SUB] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_BOUNDED_SETVARIATION_ON_COMPOSE_LINEAR) THEN
  REWRITE_TAC[o_DEF]);;

let HAS_BOUNDED_VARIATION_ON_NULL = prove
 (`!f:real^1->real^N s.
        content s = &0 /\ bounded s ==> f has_bounded_variation_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  MATCH_MP_TAC HAS_BOUNDED_SETVARIATION_ON_NULL THEN
  ASM_SIMP_TAC[INTERVAL_BOUNDS_NULL_1; VECTOR_SUB_REFL]);;

let HAS_BOUNDED_VARIATION_ON_EMPTY = prove
 (`!f:real^1->real^N. f has_bounded_variation_on {}`,
  MESON_TAC[CONTENT_EMPTY; BOUNDED_EMPTY; HAS_BOUNDED_VARIATION_ON_NULL]);;

let VECTOR_VARIATION_ON_NULL = prove
 (`!f s. content s = &0 /\ bounded s ==> vector_variation s f = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_variation] THEN
  MATCH_MP_TAC SET_VARIATION_ON_NULL THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INTERVAL_BOUNDS_NULL_1; VECTOR_SUB_REFL]);;

let HAS_BOUNDED_VARIATION_ON_NORM = prove
 (`!f:real^1->real^N s.
        f has_bounded_variation_on s
        ==> (\x. lift(norm(f x))) has_bounded_variation_on s`,
  REWRITE_TAC[has_bounded_variation_on; has_bounded_setvariation_on] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; LIFT_DROP; DROP_SUB] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_FINITE]; NORM_ARITH_TAC]);;

let HAS_BOUNDED_VARIATION_ON_MAX = prove
 (`!f g s. f has_bounded_variation_on s /\ g has_bounded_variation_on s
           ==> (\x. lift(max (drop(f x)) (drop(g x))))
               has_bounded_variation_on s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `max a b = inv(&2) * (a + b + abs(a - b))`] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_ADD; LIFT_DROP; GSYM DROP_SUB] THEN
  REWRITE_TAC[drop; GSYM NORM_REAL] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_CMUL THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_NORM THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB THEN ASM_REWRITE_TAC[]);;

let HAS_BOUNDED_VARIATION_ON_MIN = prove
 (`!f g s. f has_bounded_variation_on s /\ g has_bounded_variation_on s
           ==> (\x. lift(min (drop(f x)) (drop(g x))))
               has_bounded_variation_on s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `min a b = inv(&2) * ((a + b) - abs(a - b))`] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_ADD; LIFT_DROP; LIFT_SUB; GSYM DROP_SUB] THEN
  REWRITE_TAC[drop; GSYM NORM_REAL] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_CMUL THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB THEN
  ASM_SIMP_TAC[HAS_BOUNDED_VARIATION_ON_ADD] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_NORM THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB THEN ASM_REWRITE_TAC[]);;

let HAS_BOUNDED_VARIATION_ON_IMP_BOUNDED_ON_SUBINTERVALS = prove
 (`!f:real^1->real^N s.
        f has_bounded_variation_on s
        ==> bounded { f(d) - f(c) | interval[c,d] SUBSET s /\
                                    ~(interval[c,d] = {})}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   HAS_BOUNDED_SETVARIATION_ON_IMP_BOUNDED_ON_SUBINTERVALS) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`d:real^1`; `c:real^1`] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`c:real^1`; `d:real^1`] THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1]);;

let HAS_BOUNDED_VARIATION_ON_IMP_BOUNDED_ON_INTERVAL = prove
 (`!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b]
        ==> bounded(IMAGE f (interval[a,b]))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
   HAS_BOUNDED_VARIATION_ON_IMP_BOUNDED_ON_SUBINTERVALS) THEN
  REWRITE_TAC[BOUNDED_POS_LT; FORALL_IN_GSPEC; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B + norm((f:real^1->real^N) a)` THEN
  ASM_SIMP_TAC[NORM_ARITH `&0 < B ==> &0 < B + norm(x:real^N)`] THEN
  X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^1`; `a:real^1`]) THEN
  REWRITE_TAC[SUBSET_INTERVAL_1; INTERVAL_EQ_EMPTY_1] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; NORM_ARITH_TAC]);;

let HAS_BOUNDED_VARIATION_ON_MUL = prove
 (`!f g:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b] /\
        g has_bounded_variation_on interval[a,b]
        ==> (\x. drop(f x) % g x) has_bounded_variation_on interval[a,b]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `bounded(IMAGE (f:real^1->real^1) (interval[a,b])) /\
     bounded(IMAGE (g:real^1->real^N) (interval[a,b]))`
  MP_TAC THENL
   [ASM_SIMP_TAC[HAS_BOUNDED_VARIATION_ON_IMP_BOUNDED_ON_INTERVAL];
    REWRITE_TAC[BOUNDED_POS_LT; FORALL_IN_IMAGE]] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_INTERVAL;
              has_bounded_variation_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real` (LABEL_TAC "G")) THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (LABEL_TAC "F")) THEN
  EXISTS_TAC `B1 * C2 + B2 * C1:real` THEN
  X_GEN_TAC `d:(real^1->bool)->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `B1 * sum d (\k. norm((g:real^1->real^N)(interval_upperbound k) -
                         g(interval_lowerbound k))) +
    B2 * sum d (\k. norm((f:real^1->real^1)(interval_upperbound k) -
                         f(interval_lowerbound k)))` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[REAL_LE_LMUL_EQ]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_ADD] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH
   `f' % g' - f % g:real^N = f' % (g' - g) + (f' - f) % g`] THEN
  MATCH_MP_TAC(NORM_ARITH
    `norm x <= a /\ norm y <= b ==> norm(x + y) <= a + b`) THEN
  REWRITE_TAC[NORM_MUL; NORM_REAL] THEN
  REWRITE_TAC[drop; GSYM NORM_REAL; GSYM VECTOR_SUB_COMPONENT] THEN
  SUBGOAL_THEN `~(interval[u:real^1,v] = {})` MP_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  SUBGOAL_THEN `interval[u:real^1,v] SUBSET interval[a,b]` MP_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET_INTERVAL_1; GSYM REAL_NOT_LE] THEN
  STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

let VECTOR_VARIATION_POS_LE = prove
 (`!f:real^1->real^N s.
        f has_bounded_variation_on s ==> &0 <= vector_variation s f`,
  REWRITE_TAC[has_bounded_variation_on; vector_variation] THEN
  REWRITE_TAC[SET_VARIATION_POS_LE]);;

let VECTOR_VARIATION_GE_NORM_FUNCTION = prove
 (`!f:real^1->real^N s a b.
        f has_bounded_variation_on s /\ segment[a,b] SUBSET s
        ==> norm(f b - f a) <= vector_variation s f`,
  REWRITE_TAC[FORALL_LIFT] THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
   [MESON_TAC[SEGMENT_SYM; NORM_SUB]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_DROP; LIFT_DROP; has_bounded_variation_on] THEN
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
  [`\k. (f:real^1->real^N)(interval_upperbound k) - f(interval_lowerbound k)`;
   `s:real^1->bool`; `a:real^1`; `b:real^1`] SET_VARIATION_GE_FUNCTION) THEN
  ASM_REWRITE_TAC[vector_variation; INTERVAL_NE_EMPTY_1] THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1] THEN
  ASM_MESON_TAC[SEGMENT_1]);;

let VECTOR_VARIATION_GE_DROP_FUNCTION = prove
 (`!f s a b.
        f has_bounded_variation_on s /\ segment[a,b] SUBSET s
        ==> drop(f b) - drop(f a) <= vector_variation s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((f:real^1->real^1) b - f a)` THEN
  ASM_SIMP_TAC[VECTOR_VARIATION_GE_NORM_FUNCTION] THEN
  REWRITE_TAC[NORM_REAL; DROP_SUB; GSYM drop] THEN REAL_ARITH_TAC);;

let VECTOR_VARIATION_CONST_EQ = prove
 (`!f:real^1->real^N s.
        is_interval s /\ f has_bounded_variation_on s
        ==> (vector_variation s f = &0 <=> ?c. !x. x IN s ==> f x = c)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[MESON[]
     `(?c. !x. P x ==> f x = c) <=> !a b. P a /\ P b ==> f a = f b`] THEN
    MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^1->real^N`; `s:real^1->bool`;
        `a:real^1`; `b:real^1`] VECTOR_VARIATION_GE_NORM_FUNCTION) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[IS_INTERVAL_CONVEX_1; CONVEX_CONTAINS_SEGMENT];
      ASM_REWRITE_TAC[] THEN CONV_TAC NORM_ARITH];
    DISCH_THEN(X_CHOOSE_TAC `c:real^N`) THEN
    MP_TAC(ISPECL [`f:real^1->real^N`; `(\x. c):real^1->real^N`;
                   `s:real^1->bool`] VECTOR_VARIATION_EQ) THEN
    ASM_SIMP_TAC[VECTOR_VARIATION_CONST]]);;

let VECTOR_VARIATION_MONOTONE = prove
 (`!f s t. f has_bounded_variation_on s /\ t SUBSET s
           ==> vector_variation t f <= vector_variation s f`,
  REWRITE_TAC[has_bounded_variation_on; vector_variation] THEN
  REWRITE_TAC[SET_VARIATION_MONOTONE]);;

let VECTOR_VARIATION_NEG = prove
 (`!f:real^1->real^N s.
        vector_variation s (\x. --(f x)) = vector_variation s f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vector_variation; set_variation] THEN
  REWRITE_TAC[NORM_ARITH `norm(--x - --y:real^N) = norm(x - y)`]);;

let VECTOR_VARIATION_TRIANGLE = prove
 (`!f g:real^1->real^N s.
        f has_bounded_variation_on s /\ g has_bounded_variation_on s
        ==> vector_variation s (\x. f x + g x)
              <= vector_variation s f + vector_variation s g`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_bounded_variation_on; vector_variation] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SET_VARIATION_TRIANGLE) THEN
  REWRITE_TAC[VECTOR_ARITH `(a + b) - (c + d):real^N = (a - c) + (b - d)`]);;

let OPERATIVE_FUNCTION_ENDPOINT_DIFF = prove
 (`!f:real^1->real^N.
    operative (+) (\k. f (interval_upperbound k) - f (interval_lowerbound k))`,
  GEN_TAC THEN
  SIMP_TAC[operative; INTERVAL_BOUNDS_NULL_1; VECTOR_SUB_REFL] THEN
  REWRITE_TAC[NEUTRAL_VECTOR_ADD; DIMINDEX_1; FORALL_1; GSYM drop] THEN
  REWRITE_TAC[FORALL_DROP] THEN
  MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`; `c:real^1`] THEN
  ASM_CASES_TAC `interval[a:real^1,b] = {}` THENL
   [ASM_REWRITE_TAC[INTER_EMPTY; INTERVAL_BOUNDS_EMPTY_1] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `interval[a,b] INTER {x | drop x <= drop c} = {}` THENL
   [ASM_REWRITE_TAC[INTERVAL_BOUNDS_EMPTY_1; VECTOR_SUB_REFL] THEN
    SUBGOAL_THEN `interval[a,b] INTER {x | drop x >= drop c} = interval[a,b]`
     (fun th -> REWRITE_TAC[th; VECTOR_ADD_LID]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `i INTER s = {} ==> s UNION t = UNIV ==> i INTER t = i`)) THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_UNION; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `interval[a,b] INTER {x | drop x >= drop c} = {}` THENL
   [ASM_REWRITE_TAC[INTERVAL_BOUNDS_EMPTY_1; VECTOR_SUB_REFL] THEN
    SUBGOAL_THEN `interval[a,b] INTER {x | drop x <= drop c} = interval[a,b]`
     (fun th -> REWRITE_TAC[th; VECTOR_ADD_RID]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `i INTER s = {} ==> s UNION t = UNIV ==> i INTER t = i`)) THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_UNION; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SIMP_TAC[INTERVAL_SPLIT; drop; DIMINDEX_1; LE_REFL] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN
  SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1] THEN
  SIMP_TAC[drop; LAMBDA_BETA; DIMINDEX_1; LE_REFL] THEN STRIP_TAC THEN
  MATCH_MP_TAC(VECTOR_ARITH
   `fx:real^N = fy ==> fb - fa = fx - fa + fb - fy`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM DROP_EQ; drop] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_1; LE_REFL] THEN ASM_REAL_ARITH_TAC);;

let OPERATIVE_REAL_FUNCTION_ENDPOINT_DIFF = prove
 (`!f:real^1->real.
    operative (+) (\k. f (interval_upperbound k) - f (interval_lowerbound k))`,
  GEN_TAC THEN
  MP_TAC(ISPEC `lift o (f:real^1->real)` OPERATIVE_FUNCTION_ENDPOINT_DIFF) THEN
  REWRITE_TAC[operative; NEUTRAL_REAL_ADD; NEUTRAL_VECTOR_ADD] THEN
  REWRITE_TAC[o_THM; GSYM LIFT_SUB; GSYM LIFT_ADD; GSYM LIFT_NUM] THEN
  REWRITE_TAC[LIFT_EQ]);;

let OPERATIVE_LIFTED_VECTOR_VARIATION = prove
 (`!f:real^1->real^N.
        operative (lifted(+))
                  (\i. if f has_bounded_variation_on i
                       then SOME(vector_variation i f) else NONE)`,
  GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on; vector_variation] THEN
  MATCH_MP_TAC OPERATIVE_LIFTED_SETVARIATION THEN
  REWRITE_TAC[OPERATIVE_FUNCTION_ENDPOINT_DIFF]);;

let HAS_BOUNDED_VARIATION_ON_DIVISION = prove
 (`!f:real^1->real^N a b d.
        d division_of interval[a,b]
        ==> ((!k. k IN d ==> f has_bounded_variation_on k) <=>
             f has_bounded_variation_on interval[a,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  MATCH_MP_TAC HAS_BOUNDED_SETVARIATION_ON_DIVISION THEN
  ASM_REWRITE_TAC[OPERATIVE_FUNCTION_ENDPOINT_DIFF]);;

let VECTOR_VARIATION_ON_DIVISION = prove
 (`!f:real^1->real^N a b d.
        d division_of interval[a,b] /\
        f has_bounded_variation_on interval[a,b]
        ==> sum d (\k. vector_variation k f) =
            vector_variation (interval[a,b]) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_variation] THEN
  MATCH_MP_TAC SET_VARIATION_ON_DIVISION THEN
  ASM_REWRITE_TAC[OPERATIVE_FUNCTION_ENDPOINT_DIFF; GSYM
                  has_bounded_variation_on]);;

let HAS_BOUNDED_VARIATION_ON_COMBINE = prove
 (`!f:real^1->real^N a b c.
        drop a <= drop c /\ drop c <= drop b
        ==> (f has_bounded_variation_on interval[a,b] <=>
             f has_bounded_variation_on interval[a,c] /\
             f has_bounded_variation_on interval[c,b])`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPEC `f:real^1->real^N` OPERATIVE_LIFTED_VECTOR_VARIATION) THEN
  REWRITE_TAC[operative; FORALL_1; FORALL_DROP; DIMINDEX_1] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`; `c:real^1`] o
   CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `interval[a,b] INTER {x:real^1 | x$1 <= drop c} = interval[a,c] /\
    interval[a,b] INTER {x:real^1 | x$1 >= drop c} = interval[c,b]`
   (fun th -> REWRITE_TAC[th])
  THENL
   [SIMP_TAC[EXTENSION; IN_INTER; GSYM drop; IN_INTERVAL_1; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[distinctness "option"; lifted])]);;

let VECTOR_VARIATION_COMBINE = prove
 (`!f:real^1->real^N a b c.
        drop a <= drop c /\
        drop c <= drop b /\
        f has_bounded_variation_on interval[a,b]
        ==> vector_variation (interval[a,c]) f +
            vector_variation (interval[c,b]) f =
            vector_variation (interval[a,b]) f`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPEC `f:real^1->real^N` OPERATIVE_LIFTED_VECTOR_VARIATION) THEN
  REWRITE_TAC[operative; FORALL_1; FORALL_DROP; DIMINDEX_1] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`; `c:real^1`] o
   CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN REPEAT(COND_CASES_TAC THENL
    [ALL_TAC;
     ASM_MESON_TAC[HAS_BOUNDED_VARIATION_ON_SUBSET; INTER_SUBSET]]) THEN
  REWRITE_TAC[lifted; injectivity "option"] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[INTERVAL_SPLIT; DIMINDEX_1; LE_REFL] THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[EXTENSION; IN_INTERVAL_1; drop; LAMBDA_BETA;
           DIMINDEX_1; LE_REFL] THEN
  REWRITE_TAC[GSYM drop] THEN ASM_REAL_ARITH_TAC);;

let VECTOR_VARIATION_MINUS_FUNCTION_MONOTONE = prove
 (`!f a b c d.
        f has_bounded_variation_on interval[a,b] /\
        interval[c,d] SUBSET interval[a,b] /\ ~(interval[c,d] = {})
        ==> vector_variation (interval[c,d]) f - drop(f d - f c) <=
            vector_variation (interval[a,b]) f - drop(f b - f a)`,
  REWRITE_TAC[SUBSET_INTERVAL_1; INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN
  REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(f c) - drop(f a) <= vector_variation(interval[a,c]) f /\
    drop(f b) - drop(f d) <= vector_variation(interval[d,b]) f`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VECTOR_VARIATION_GE_DROP_FUNCTION THEN
    ASM_REWRITE_TAC[SEGMENT_1; SUBSET_INTERVAL_1; INTERVAL_EQ_EMPTY_1] THEN
    (CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DROP_SUB] THEN
  MP_TAC(ISPEC `f:real^1->real^1` VECTOR_VARIATION_COMBINE) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`a:real^1`; `b:real^1`; `d:real^1`] th) THEN
    MP_TAC(SPECL [`a:real^1`; `d:real^1`; `c:real^1`] th)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let INCREASING_BOUNDED_VARIATION = prove
 (`!f a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> f has_bounded_variation_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval[a:real^1,b] = {}` THEN
  ASM_REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_EMPTY] THEN
  REWRITE_TAC[has_bounded_variation_on;
              HAS_BOUNDED_SETVARIATION_ON_INTERVAL] THEN
  EXISTS_TAC `drop(f b) - drop(f(a:real^1))` THEN
  MP_TAC(MATCH_MP (REWRITE_RULE
   [TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`]
   OPERATIVE_DIVISION) (SPEC `drop o (f:real^1->real^1)`
      OPERATIVE_REAL_FUNCTION_ENDPOINT_DIFF)) THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[GSYM sum; MONOIDAL_REAL_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[o_THM; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[NORM_REAL; GSYM drop] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interval[u:real^1,v] = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[DROP_SUB; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> abs(y - x) = y - x`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
  SUBGOAL_THEN `interval[u:real^1,v] SUBSET interval[a,b]` MP_TAC THENL
   [ASM_MESON_TAC[division_of]; REWRITE_TAC[SUBSET_INTERVAL_1]] THEN
  ASM_REAL_ARITH_TAC);;

let DECREASING_BOUNDED_VARIATION = prove
 (`!f a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x))
         ==> f has_bounded_variation_on interval[a,b]`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV o RAND_CONV)
   [GSYM REAL_LE_NEG2] THEN
  REWRITE_TAC[GSYM DROP_NEG] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INCREASING_BOUNDED_VARIATION) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_BOUNDED_VARIATION_ON_NEG) THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX]);;

let INCREASING_VECTOR_VARIATION = prove
 (`!f a b.
        ~(interval[a,b] = {}) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> vector_variation (interval[a,b]) f = drop(f b) - drop(f a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_variation] THEN
  REWRITE_TAC[SET_VARIATION_ON_INTERVAL] THEN
  SUBGOAL_THEN
   `{sum d (\k. norm (f (interval_upperbound k) - f (interval_lowerbound k))) |
     d division_of interval[a:real^1,b]} =
    {drop (f b) - drop(f a)}`
   (fun th -> SIMP_TAC[SUP_INSERT_FINITE; FINITE_EMPTY; th]) THEN
  MATCH_MP_TAC(SET_RULE
   `(?x. P x) /\ (!x. P x ==> f x = a) ==> {f x | P x} = {a}`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_SELF]; ALL_TAC] THEN
  MP_TAC(MATCH_MP (REWRITE_RULE
   [TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`]
   OPERATIVE_DIVISION) (SPEC `drop o (f:real^1->real^1)`
      OPERATIVE_REAL_FUNCTION_ENDPOINT_DIFF)) THEN
   MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[GSYM sum; MONOIDAL_REAL_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[o_THM; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[NORM_REAL; GSYM drop] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interval[u:real^1,v] = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[DROP_SUB; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> abs(y - x) = y - x`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
  SUBGOAL_THEN `interval[u:real^1,v] SUBSET interval[a,b]` MP_TAC THENL
   [ASM_MESON_TAC[division_of]; REWRITE_TAC[SUBSET_INTERVAL_1]] THEN
  ASM_REAL_ARITH_TAC);;

let DECREASING_VECTOR_VARIATION = prove
 (`!f a b.
        ~(interval[a,b] = {}) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x))
        ==> vector_variation (interval[a,b]) f = drop(f a) - drop(f b)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC
   (LAND_CONV o RAND_CONV o BINDER_CONV o BINDER_CONV o RAND_CONV)
   [GSYM REAL_LE_NEG2] THEN
  REWRITE_TAC[GSYM DROP_NEG] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INCREASING_VECTOR_VARIATION) THEN
  SIMP_TAC[VECTOR_VARIATION_NEG; DROP_NEG] THEN
  DISCH_TAC THEN REAL_ARITH_TAC);;

let HAS_BOUNDED_VARIATION_TRANSLATION2_EQ,VECTOR_VARIATION_TRANSLATION2 =
 (CONJ_PAIR o prove)
 (`(!a f:real^1->real^N s.
        (\x. f(a + x)) has_bounded_variation_on (IMAGE (\x. --a + x) s) <=>
        f has_bounded_variation_on s) /\
   (!a f:real^1->real^N s.
        vector_variation (IMAGE (\x. --a + x) s) (\x. f(a + x)) =
        vector_variation s f)`,
  GEN_REWRITE_TAC I [AND_FORALL_THM] THEN X_GEN_TAC `a:real^1` THEN
  MATCH_MP_TAC VARIATION_EQUAL_LEMMA THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIVISION_OF_TRANSLATION; GSYM INTERVAL_TRANSLATION]);;

let HAS_BOUNDED_VARIATION_AFFINITY2_EQ,VECTOR_VARIATION_AFFINITY2 =
 (CONJ_PAIR o prove)
 (`(!m c f:real^1->real^N s.
        (\x. f (m % x + c)) has_bounded_variation_on
        IMAGE (\x. inv m % x + --(inv m % c)) s <=>
        m = &0 \/ f has_bounded_variation_on s) /\
   (!m c f:real^1->real^N s.
        vector_variation (IMAGE (\x. inv m % x + --(inv m % c)) s)
                         (\x. f (m % x + c)) =
        if m = &0 then &0 else vector_variation s f)`,
  GEN_REWRITE_TAC I [AND_FORALL_THM] THEN X_GEN_TAC `m:real` THEN
  GEN_REWRITE_TAC I [AND_FORALL_THM] THEN X_GEN_TAC `c:real^1` THEN
  ASM_CASES_TAC `m = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; HAS_BOUNDED_VARIATION_ON_CONST] THEN
    REWRITE_TAC[VECTOR_VARIATION_CONST];
    MATCH_MP_TAC VARIATION_EQUAL_LEMMA THEN
    ASM_SIMP_TAC[REWRITE_RULE[FUN_EQ_THM; o_DEF] AFFINITY_INVERSES; I_THM] THEN
    ASM_SIMP_TAC[IMAGE_AFFINITY_INTERVAL] THEN
    ASM_REWRITE_TAC[DIVISION_OF_AFFINITY; REAL_INV_EQ_0] THEN
    MESON_TAC[]]);;

let HAS_BOUNDED_VARIATION_AFFINITY_EQ,VECTOR_VARIATION_AFFINITY =
 (CONJ_PAIR o prove)
 (`(!m c f:real^1->real^N s.
        (\x. f(m % x + c)) has_bounded_variation_on s <=>
        m = &0 \/ f has_bounded_variation_on (IMAGE (\x. m % x + c) s)) /\
   (!m c f:real^1->real^N s.
        vector_variation s (\x. f(m % x + c)) =
        if m = &0 then &0 else vector_variation (IMAGE (\x. m % x + c) s) f)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `m = &0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; HAS_BOUNDED_VARIATION_ON_CONST;
                  VECTOR_VARIATION_CONST] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL[`m:real`; `c:real^1`; `f:real^1->real^N`;
                  `IMAGE (\x:real^1. m % x + c) s`]
          HAS_BOUNDED_VARIATION_AFFINITY2_EQ);
    MP_TAC(ISPECL[`m:real`; `c:real^1`; `f:real^1->real^N`;
                  `IMAGE (\x:real^1. m % x + c) s`]
          VECTOR_VARIATION_AFFINITY2)] THEN
  ASM_SIMP_TAC[AFFINITY_INVERSES; GSYM IMAGE_o; IMAGE_I]);;

let HAS_BOUNDED_VARIATION_TRANSLATION_EQ,VECTOR_VARIATION_TRANSLATION =
 (CONJ_PAIR o prove)
 (`(!a f:real^1->real^N s.
        (\x. f(a + x)) has_bounded_variation_on s <=>
        f has_bounded_variation_on (IMAGE (\x. a + x) s)) /\
   (!a f:real^1->real^N s.
        vector_variation s (\x. f(a + x)) =
        vector_variation (IMAGE (\x. a + x) s) f)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL[`a:real^1`; `f:real^1->real^N`; `IMAGE (\x:real^1. a + x) s`]
          HAS_BOUNDED_VARIATION_TRANSLATION2_EQ);
    MP_TAC(ISPECL[`a:real^1`; `f:real^1->real^N`; `IMAGE (\x:real^1. a + x) s`]
          VECTOR_VARIATION_TRANSLATION2)] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[IMAGE_ID; VECTOR_ARITH `--a + a + x:real^N = x`;
              VECTOR_ARITH `a + --a + x:real^N = x`]);;

let HAS_BOUNDED_VARIATION_TRANSLATION_EQ_INTERVAL,
    VECTOR_VARIATION_TRANSLATION_INTERVAL =
 (CONJ_PAIR o prove)
 (`(!a f:real^1->real^N u v.
        (\x. f(a + x)) has_bounded_variation_on interval[u,v] <=>
        f has_bounded_variation_on interval[a+u,a+v]) /\
   (!a f:real^1->real^N u v.
        vector_variation (interval[u,v]) (\x. f(a + x)) =
        vector_variation (interval[a+u,a+v]) f)`,
  REWRITE_TAC[INTERVAL_TRANSLATION; HAS_BOUNDED_VARIATION_TRANSLATION_EQ;
              VECTOR_VARIATION_TRANSLATION]);;

let HAS_BOUNDED_VARIATION_TRANSLATION = prove
 (`!f:real^1->real^N s a.
        f has_bounded_variation_on s
        ==> (\x. f(a + x)) has_bounded_variation_on (IMAGE (\x. --a + x) s)`,
  REWRITE_TAC[HAS_BOUNDED_VARIATION_TRANSLATION2_EQ]);;

let HAS_BOUNDED_VARIATION_REFLECT2_EQ,VECTOR_VARIATION_REFLECT2 =
 (CONJ_PAIR o prove)
 (`(!f:real^1->real^N s.
        (\x. f(--x)) has_bounded_variation_on (IMAGE (--) s) <=>
        f has_bounded_variation_on s) /\
   (!f:real^1->real^N s.
        vector_variation (IMAGE (--) s) (\x. f(--x)) =
        vector_variation s f)`,
  MATCH_MP_TAC VARIATION_EQUAL_LEMMA THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIVISION_OF_REFLECT; REFLECT_INTERVAL]);;

let HAS_BOUNDED_VARIATION_REFLECT_EQ,VECTOR_VARIATION_REFLECT =
 (CONJ_PAIR o prove)
 (`(!f:real^1->real^N s.
        (\x. f(--x)) has_bounded_variation_on s <=>
        f has_bounded_variation_on (IMAGE (--) s)) /\
   (!f:real^1->real^N s.
        vector_variation s (\x. f(--x)) =
        vector_variation (IMAGE (--) s) f)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL[`f:real^1->real^N`; `IMAGE (--) (s:real^1->bool)`]
          HAS_BOUNDED_VARIATION_REFLECT2_EQ);
    MP_TAC(ISPECL[`f:real^1->real^N`; `IMAGE (--) (s:real^1->bool)`]
          VECTOR_VARIATION_REFLECT2)] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[IMAGE_ID; VECTOR_NEG_NEG]);;

let HAS_BOUNDED_VARIATION_REFLECT_EQ_INTERVAL,
    VECTOR_VARIATION_REFLECT_INTERVAL =
 (CONJ_PAIR o prove)
 (`(!f:real^1->real^N u v.
        (\x. f(--x)) has_bounded_variation_on interval[u,v] <=>
        f has_bounded_variation_on interval[--v,--u]) /\
   (!f:real^1->real^N u v.
        vector_variation (interval[u,v]) (\x. f(--x)) =
        vector_variation (interval[--v,--u]) f)`,
  REWRITE_TAC[GSYM REFLECT_INTERVAL; HAS_BOUNDED_VARIATION_REFLECT_EQ;
              VECTOR_VARIATION_REFLECT]);;

let HAS_BOUNDED_VARIATION_DARBOUX = prove
 (`!f a b.
     f has_bounded_variation_on interval[a,b] <=>
     ?g h. (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
                  ==> drop(g x) <= drop(g y)) /\
           (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
                  ==> drop(h x) <= drop(h y)) /\
           (!x. f x = g x - h x)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`\x:real^1. lift(vector_variation (interval[a,x]) (f:real^1->real^1))`;
      `\x:real^1. lift(vector_variation (interval[a,x]) f) - f x`] THEN
    REWRITE_TAC[VECTOR_ARITH `a - (a - x):real^1 = x`] THEN
    REWRITE_TAC[LIFT_DROP; DROP_SUB] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC VECTOR_VARIATION_MONOTONE;
      MATCH_MP_TAC(REAL_ARITH
       `!x. a - (b - x) <= c - (d - x) ==> a - b <= c - d`) THEN
      EXISTS_TAC `drop(f(a:real^1))` THEN
      REWRITE_TAC[GSYM DROP_SUB] THEN
      MATCH_MP_TAC VECTOR_VARIATION_MINUS_FUNCTION_MONOTONE] THEN
    (CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         HAS_BOUNDED_VARIATION_ON_SUBSET));
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; INTERVAL_EQ_EMPTY_1] THEN
      ASM_REAL_ARITH_TAC);
    GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC INCREASING_BOUNDED_VARIATION THEN
    ASM_REWRITE_TAC[]]);;

let HAS_BOUNDED_VARIATION_DARBOUX_STRICT = prove
 (`!f a b.
     f has_bounded_variation_on interval[a,b] <=>
     ?g h. (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x < drop y
                  ==> drop(g x) < drop(g y)) /\
           (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x < drop y
                  ==> drop(h x) < drop(h y)) /\
           (!x. f x = g x - h x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_BOUNDED_VARIATION_DARBOUX] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`\x:real^1. g x + x`; `\x:real^1. h x + x`] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(a + x) - (b + x):real^1 = a - b`] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_ADD] THEN
    MATCH_MP_TAC REAL_LET_ADD2 THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MAP_EVERY EXISTS_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
    ASM_REWRITE_TAC[REAL_LE_LT; DROP_EQ] THEN ASM_MESON_TAC[]]);;

let HAS_BOUNDED_VARIATION_COMPOSE_INCREASING = prove
 (`!f g:real^1->real^N a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        g has_bounded_variation_on interval[f a,f b]
        ==> (g o f) has_bounded_variation_on interval[a,b]`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_COMPONENTWISE] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[HAS_BOUNDED_VARIATION_DARBOUX; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^1->real^1`; `k:real^1->real^1`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(h:real^1->real^1) o (f:real^1->real^1)`;
                        `(k:real^1->real^1) o (f:real^1->real^1)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_INTERVAL_1] THEN CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

let HAS_BOUNDED_VARIATION_ON_REFLECT = prove
 (`!f:real^1->real^N s.
        f has_bounded_variation_on IMAGE (--) s
        ==> (\x. f(--x)) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_bounded_variation_on] THEN
  REWRITE_TAC[has_bounded_setvariation_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`d:(real^1->bool)->bool`; `t:real^1->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`IMAGE (IMAGE (--)) (d:(real^1->bool)->bool)`;
    `IMAGE (--) (t:real^1->bool)`]) THEN
  ASM_SIMP_TAC[DIVISION_OF_REFLECT] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM SUBSET] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [MESON_TAC[VECTOR_ARITH `--x:real^N = --y <=> x = y`; INJECTIVE_IMAGE];
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= d ==> y <= d`) THEN
    MATCH_MP_TAC SUM_EQ THEN FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION th]) THEN
    MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `drop u <= drop v` ASSUME_TAC THENL
     [ASM_MESON_TAC[INTERVAL_NE_EMPTY_1; division_of]; ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM; REFLECT_INTERVAL] THEN
    ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1;
                 DROP_NEG; REAL_LE_NEG2] THEN
    NORM_ARITH_TAC]);;

let HAS_BOUNDED_VARIATION_ON_REFLECT_INTERVAL = prove
 (`!f:real^1->real^N a b.
        f has_bounded_variation_on interval[--b,--a]
        ==> (\x. f(--x)) has_bounded_variation_on interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_REFLECT THEN
  ASM_REWRITE_TAC[REFLECT_INTERVAL]);;

let VECTOR_VARIATION_REFLECT = prove
 (`!f:real^1->real^N s.
        vector_variation s (\x. f(--x)) =
        vector_variation (IMAGE (--) s) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vector_variation; set_variation] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real` THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^1->bool)->bool`
   (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (IMAGE (--)) (d:(real^1->bool)->bool)` THEN
  (CONJ_TAC THENL
    [EXISTS_TAC `IMAGE (--) (t:real^1->bool)` THEN
     ASM_SIMP_TAC[DIVISION_OF_REFLECT] THEN
     ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_IMAGE]) THEN
     ASM_MESON_TAC[VECTOR_NEG_NEG; IN_IMAGE];
     ALL_TAC]) THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o rand o snd) THEN
  (ANTS_TAC THENL
   [MESON_TAC[VECTOR_ARITH `--x:real^N = --y <=> x = y`; INJECTIVE_IMAGE];
    DISCH_THEN SUBST1_TAC]) THEN
  MATCH_MP_TAC SUM_EQ THEN FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION th]) THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
  (SUBGOAL_THEN `drop u <= drop v` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERVAL_NE_EMPTY_1; division_of]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[o_THM; REFLECT_INTERVAL] THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1;
               DROP_NEG; REAL_LE_NEG2; VECTOR_NEG_NEG] THEN
  NORM_ARITH_TAC);;

let VECTOR_VARIATION_REFLECT_INTERVAL = prove
 (`!f:real^1->real^N a b.
        vector_variation (interval[a,b]) (\x. f(--x)) =
        vector_variation (interval[--b,--a]) f`,
  REWRITE_TAC[VECTOR_VARIATION_REFLECT; REFLECT_INTERVAL]);;

let HAS_BOUNDED_VARIATION_COMPOSE_DECREASING = prove
 (`!f g:real^1->real^N a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x)) /\
        g has_bounded_variation_on interval[f b,f a]
        ==> (g o f) has_bounded_variation_on interval[a,b]`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[VECTOR_NEG_NEG]
    (ISPECL [`f:real^1->real^N`; `--b:real^1`; `--a:real^1`]
        HAS_BOUNDED_VARIATION_ON_REFLECT_INTERVAL))) THEN
  POP_ASSUM MP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV o RAND_CONV)
   [GSYM REAL_LE_NEG2] THEN
  REWRITE_TAC[GSYM DROP_NEG; IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_BOUNDED_VARIATION_COMPOSE_INCREASING) THEN
  REWRITE_TAC[o_DEF; VECTOR_NEG_NEG]);;

let HAS_BOUNDED_VARIATION_ON_ID = prove
 (`!a b. (\x. x) has_bounded_variation_on interval[a,b]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INCREASING_BOUNDED_VARIATION THEN
  SIMP_TAC[]);;

let HAS_BOUNDED_VARIATION_ON_LINEAR_IMAGE = prove
 (`!f:real^1->real^1 g:real^1->real^N a b.
        linear f /\ g has_bounded_variation_on IMAGE f (interval[a,b])
        ==> (g o f) has_bounded_variation_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LINEAR_1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` SUBST_ALL_TAC) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH
   `c = &0 \/ &0 <= c /\ &0 < c \/ ~(&0 <= c) /\ &0 < --c`)
  THENL
   [ASM_REWRITE_TAC[o_DEF; VECTOR_MUL_LZERO; HAS_BOUNDED_VARIATION_ON_CONST];
    MATCH_MP_TAC HAS_BOUNDED_VARIATION_COMPOSE_INCREASING THEN
    REWRITE_TAC[DROP_CMUL];
    MATCH_MP_TAC HAS_BOUNDED_VARIATION_COMPOSE_DECREASING THEN
    REWRITE_TAC[DROP_CMUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `c * y <= c * x <=> --c * x <= --c * y`]] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(MESON[]
   `g has_bounded_variation_on s
    ==> s = t ==> g has_bounded_variation_on t`)) THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `c % x:real^N = c % x + vec 0`] THEN
  ASM_REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_RID] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_CMUL] THENL
   [ALL_TAC;
   ONCE_REWRITE_TAC[REAL_ARITH `c * y < c * x <=> --c * x < --c * y`]] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN
  ASM_REWRITE_TAC[GSYM INTERVAL_EQ_EMPTY_1]);;

let INCREASING_LEFT_LIMIT_1 = prove
 (`!f a b c.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        c IN interval[a,b]
       ==> ?l. (f --> l) (at c within interval[a,c])`,
  REPEAT STRIP_TAC THEN EXISTS_TAC
   `lift(sup {drop(f x) | x IN interval[a,b] /\ drop x < drop c})` THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[LIM_WITHIN] THEN
  REWRITE_TAC[DIST_REAL; GSYM drop] THEN
  ASM_CASES_TAC `{x | x IN interval[a,b] /\ drop x < drop c} = {}` THENL
   [GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC(TAUT
     `(a ==> ~b) ==> a ==> b ==> c`) THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_ELIM_THM; IN_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `{drop(f x) | x IN interval[a,b] /\ drop x < drop c}` SUP) THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN ASM_SIMP_TAC[IMAGE_EQ_EMPTY];
      EXISTS_TAC `drop(f(b:real^1))` THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC];
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[IMAGE_ID] THEN
    ABBREV_TAC `s = sup (IMAGE (\x. drop(f x))
                        {x | x IN interval[a,b] /\ drop x < drop c})` THEN
    REWRITE_TAC[LIFT_DROP] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `s - e:real`)) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> ~(s <= s - e)`; NOT_FORALL_THM] THEN
    REWRITE_TAC[NOT_IMP; REAL_NOT_LE; IN_INTERVAL_1] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `drop c - drop d` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`d:real^1`; `x:real^1`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN ASM_REAL_ARITH_TAC]);;

let DECREASING_LEFT_LIMIT_1 = prove
 (`!f a b c.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x)) /\
        c IN interval[a,b]
        ==> ?l. (f --> l) (at c within interval[a,c])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. --((f:real^1->real^1) x)`; `a:real^1`; `b:real^1`; `c:real^1`]
        INCREASING_LEFT_LIMIT_1) THEN
  ASM_REWRITE_TAC[REAL_LE_NEG2; DROP_NEG] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM LIM_NEG_EQ] THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX] THEN MESON_TAC[]);;

let INCREASING_RIGHT_LIMIT_1 = prove
 (`!f a b c.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        c IN interval[a,b]
       ==> ?l. (f --> l) (at c within interval[c,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (f:real^1->real^1) (--x)`;
                 `--b:real^1`; `--a:real^1`; `--c:real^1`]
        DECREASING_LEFT_LIMIT_1) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_REFLECT] THEN
  ONCE_REWRITE_TAC[MESON[VECTOR_NEG_NEG]
   `(!x:real^1 y:real^1. P x y) <=> (!x y. P (--x) (--y))`] THEN
  REWRITE_TAC[DROP_NEG; IN_INTERVAL_REFLECT; VECTOR_NEG_NEG] THEN
  ASM_SIMP_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `l:real^1` THEN REWRITE_TAC[LIM_WITHIN] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [MESON[VECTOR_NEG_NEG] `(!x:real^1. P x) <=> (!x. P (--x))`] THEN
  REWRITE_TAC[IN_INTERVAL_REFLECT; VECTOR_NEG_NEG;
              NORM_ARITH `dist(--x:real^1,--y) = dist(x,y)`]);;

let DECREASING_RIGHT_LIMIT_1 = prove
 (`!f a b c.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x)) /\
        c IN interval[a,b]
       ==> ?l. (f --> l) (at c within interval[c,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. --((f:real^1->real^1) x)`; `a:real^1`; `b:real^1`; `c:real^1`]
        INCREASING_RIGHT_LIMIT_1) THEN
  ASM_REWRITE_TAC[REAL_LE_NEG2; DROP_NEG] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM LIM_NEG_EQ] THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX] THEN MESON_TAC[]);;

let HAS_BOUNDED_VECTOR_VARIATION_LEFT_LIMIT = prove
 (`!f:real^1->real^N a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ?l. (f --> l) (at c within interval[a,c])`,
  ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT;
                   HAS_BOUNDED_VARIATION_ON_COMPONENTWISE] THEN
  REWRITE_TAC[GSYM LAMBDA_SKOLEM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`\x. lift((f:real^1->real^N)x$i)`,`f:real^1->real^1`) THEN
  UNDISCH_TAC `(c:real^1) IN interval[a,b]` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM EXISTS_LIFT] THEN
  FIRST_X_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [HAS_BOUNDED_VARIATION_DARBOUX]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; CONJ_ASSOC] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN DISCH_THEN(CONJUNCTS_THEN
   (MP_TAC o SPEC `c:real^1` o MATCH_MP
     (ONCE_REWRITE_RULE[IMP_CONJ] INCREASING_LEFT_LIMIT_1))) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `l2:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `l1:real^1` THEN DISCH_TAC THEN
  EXISTS_TAC `l1 - l2:real^1` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  ASM_SIMP_TAC[LIM_SUB]);;

let HAS_BOUNDED_VECTOR_VARIATION_RIGHT_LIMIT = prove
 (`!f:real^1->real^N a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ?l. (f --> l) (at c within interval[c,b])`,
  ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT;
                   HAS_BOUNDED_VARIATION_ON_COMPONENTWISE] THEN
  REWRITE_TAC[GSYM LAMBDA_SKOLEM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`\x. lift((f:real^1->real^N)x$i)`,`f:real^1->real^1`) THEN
  UNDISCH_TAC `(c:real^1) IN interval[a,b]` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM EXISTS_LIFT] THEN
  FIRST_X_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [HAS_BOUNDED_VARIATION_DARBOUX]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; CONJ_ASSOC] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN DISCH_THEN(CONJUNCTS_THEN
   (MP_TAC o SPEC `c:real^1` o MATCH_MP
     (ONCE_REWRITE_RULE[IMP_CONJ] INCREASING_RIGHT_LIMIT_1))) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `l2:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `l1:real^1` THEN DISCH_TAC THEN
  EXISTS_TAC `l1 - l2:real^1` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  ASM_SIMP_TAC[LIM_SUB]);;

let VECTOR_VARIATION_CONTINUOUS_LEFT = prove
 (`!f:real^1->real^1 a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ((\x. lift(vector_variation(interval[a,x]) f))
             continuous (at c within interval[a,c]) <=>
            f continuous (at c within interval[a,c]))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[continuous_within] THEN
    REWRITE_TAC[DIST_LIFT; IN_ELIM_THM; DIST_REAL; GSYM drop] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS) THEN
    REWRITE_TAC[GSYM DROP_SUB] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `c:real^1`; `x:real^1`]
        VECTOR_VARIATION_COMBINE) THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH `abs(a - (a + b)) = abs b`] THEN
    REWRITE_TAC[drop; GSYM NORM_REAL] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs a`) THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    MATCH_MP_TAC VECTOR_VARIATION_GE_NORM_FUNCTION THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HAS_BOUNDED_VARIATION_ON_SUBSET));
      REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `c limit_point_of interval[a:real^1,c]` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[CONTINUOUS_WITHIN; LIM; TRIVIAL_LIMIT_WITHIN]] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_BOUNDED_VARIATION_DARBOUX]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^1->real^1`; `a:real^1`; `b:real^1`; `c:real^1`]
   INCREASING_LEFT_LIMIT_1) THEN
  MP_TAC(ISPECL [`g:real^1->real^1`; `a:real^1`; `b:real^1`; `c:real^1`]
   INCREASING_LEFT_LIMIT_1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `gc:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `hc:real^1` THEN DISCH_TAC THEN
  ABBREV_TAC `k = gc - (g:real^1->real^1) c` THEN
  SUBGOAL_THEN `hc - (h:real^1->real^1) c = k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `hc' - hc:real^1 = gc' - gc <=> gc' - hc' = gc - hc`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_WITHIN]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
      LIM_UNIQUE) THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_WITHIN] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
    ASM_SIMP_TAC[LIM_SUB];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`g':real^1->real^1 = \x. if drop c <= drop x then g(x) + k else g(x)`;
    `h':real^1->real^1 = \x. if drop c <= drop x then h(x) + k else h(x)`] THEN
  SUBGOAL_THEN
   `(!x y. x IN interval[a,c] /\ y IN interval[a,c] /\ drop x <= drop y
           ==> drop(g' x) <= drop(g' y)) /\
    (!x y. x IN interval[a,c] /\ y IN interval[a,c] /\ drop x <= drop y
           ==> drop(h' x) <= drop(h' y))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN REWRITE_TAC[] THEN CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
    (ASM_CASES_TAC `drop c <= drop x` THENL
      [SUBGOAL_THEN `drop c <= drop y` ASSUME_TAC THENL
        [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
       REWRITE_TAC[DROP_ADD; REAL_LE_RADD] THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
      [ALL_TAC;
       FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC] THEN
     SUBGOAL_THEN `y:real^1 = c` SUBST_ALL_TAC THENL
      [REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
      `gc - g c = k
       ==> b <= drop(g c + (gc - g c)) ==> b <= drop(g c + k)`)) THEN
     REWRITE_TAC[VECTOR_ARITH `a + b - a:real^1 = b`] THEN
     MATCH_MP_TAC(ISPEC `at c within interval[a:real^1,c]`
        LIM_DROP_LBOUND))
    THENL [EXISTS_TAC `g:real^1->real^1`; EXISTS_TAC `h:real^1->real^1`] THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_WITHIN; EVENTUALLY_WITHIN] THEN
    EXISTS_TAC `drop c - drop x` THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; IN_INTERVAL_1] THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(g':real^1->real^1) continuous (at c within interval[a,c]) /\
    (h':real^1->real^1) continuous (at c within interval[a,c])`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN
    REWRITE_TAC[CONTINUOUS_WITHIN; REAL_LE_REFL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_ARITH
     `g - g':real^1 = k <=> g' + k = g`]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] LIM_TRANSFORM)) THEN
    MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN
    REWRITE_TAC[LIM_WITHIN; DIST_REAL; GSYM drop; IN_INTERVAL_1] THEN
    SIMP_TAC[REAL_ARITH `x <= c /\ &0 < abs(x - c) ==> ~(c <= x)`] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; DROP_VEC; REAL_SUB_REFL; REAL_ABS_NUM] THEN
    MESON_TAC[REAL_LT_01];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_within] THEN
  REWRITE_TAC[DIST_LIFT; IN_ELIM_THM; DIST_REAL; GSYM drop] THEN
  DISCH_THEN(fun th ->
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    CONJUNCTS_THEN (MP_TAC o SPEC `e / &2`) th) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `d:real^1` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `c:real^1`; `d:real^1`]
        VECTOR_VARIATION_COMBINE) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[REAL_ARITH `abs(a - (a + b)) = abs b`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < a ==> abs x < a`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VECTOR_VARIATION_POS_LE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `f:real^1->real^1 = \x. g' x - h' x` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`g':real^1->real^1`; `\x. --((h':real^1->real^1) x)`;
    `interval[d:real^1,c]`] VECTOR_VARIATION_TRIANGLE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_NEG] THEN
    MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUBSET THEN
    EXISTS_TAC `interval[a:real^1,c]` THEN
    ASM_SIMP_TAC[INCREASING_BOUNDED_VARIATION; SUBSET_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN  ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_SUB] THEN MATCH_MP_TAC(REAL_ARITH
   `y < a / &2 /\ z < a / &2 ==> x <= y + z ==> x < a`) THEN
  REWRITE_TAC[VECTOR_VARIATION_NEG] THEN CONJ_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand)
    INCREASING_VECTOR_VARIATION o lhand o snd) THEN
  (ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
     ASM_REWRITE_TAC[INTERVAL_EQ_EMPTY_1; IN_INTERVAL_1; REAL_NOT_LT] THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
     DISCH_THEN SUBST1_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x - y) < e ==> y - x < e`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let VECTOR_VARIATION_CONTINUOUS_RIGHT = prove
 (`!f:real^1->real^1 a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ((\x. lift(vector_variation(interval[a,x]) f))
             continuous (at c within interval[c,b]) <=>
            f continuous (at c within interval[c,b]))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[continuous_within] THEN
    REWRITE_TAC[DIST_LIFT; IN_ELIM_THM; DIST_REAL; GSYM drop] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS) THEN
    REWRITE_TAC[GSYM DROP_SUB] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `x:real^1`; `c:real^1`]
        VECTOR_VARIATION_COMBINE) THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH `abs((a + b) - a) = abs b`] THEN
    REWRITE_TAC[drop; GSYM NORM_REAL] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs a`) THEN
    MATCH_MP_TAC VECTOR_VARIATION_GE_NORM_FUNCTION THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HAS_BOUNDED_VARIATION_ON_SUBSET));
      REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `c limit_point_of interval[c:real^1,b]` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[CONTINUOUS_WITHIN; LIM; TRIVIAL_LIMIT_WITHIN]] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_BOUNDED_VARIATION_DARBOUX]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^1->real^1`; `a:real^1`; `b:real^1`; `c:real^1`]
   INCREASING_RIGHT_LIMIT_1) THEN
  MP_TAC(ISPECL [`g:real^1->real^1`; `a:real^1`; `b:real^1`; `c:real^1`]
   INCREASING_RIGHT_LIMIT_1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `gc:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `hc:real^1` THEN DISCH_TAC THEN
  ABBREV_TAC `k = gc - (g:real^1->real^1) c` THEN
  SUBGOAL_THEN `hc - (h:real^1->real^1) c = k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `hc' - hc:real^1 = gc' - gc <=> gc' - hc' = gc - hc`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_WITHIN]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
      LIM_UNIQUE) THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_WITHIN] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
    ASM_SIMP_TAC[LIM_SUB];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`g':real^1->real^1 = \x. if drop x <= drop c then g(x) + k else g(x)`;
    `h':real^1->real^1 = \x. if drop x <= drop c then h(x) + k else h(x)`] THEN
  SUBGOAL_THEN
   `(!x y. x IN interval[c,b] /\ y IN interval[c,b] /\ drop x <= drop y
           ==> drop(g' x) <= drop(g' y)) /\
    (!x y. x IN interval[c,b] /\ y IN interval[c,b] /\ drop x <= drop y
           ==> drop(h' x) <= drop(h' y))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN REWRITE_TAC[] THEN CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
    (ASM_CASES_TAC `drop y <= drop c` THENL
      [SUBGOAL_THEN `drop x <= drop c` ASSUME_TAC THENL
        [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
       REWRITE_TAC[DROP_ADD; REAL_LE_RADD] THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
      [ALL_TAC;
       FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC] THEN
     SUBGOAL_THEN `x:real^1 = c` SUBST_ALL_TAC THENL
      [REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
      `gc - g c = k
       ==> drop(g c + (gc - g c)) <= b ==> drop(g c + k) <= b`)) THEN
     REWRITE_TAC[VECTOR_ARITH `a + b - a:real^1 = b`] THEN
     MATCH_MP_TAC(ISPEC `at c within interval[c:real^1,b]`
        LIM_DROP_UBOUND))
    THENL [EXISTS_TAC `g:real^1->real^1`; EXISTS_TAC `h:real^1->real^1`] THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_WITHIN; EVENTUALLY_WITHIN] THEN
    EXISTS_TAC `drop y - drop c` THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; IN_INTERVAL_1] THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(g':real^1->real^1) continuous (at c within interval[c,b]) /\
    (h':real^1->real^1) continuous (at c within interval[c,b])`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN
    REWRITE_TAC[CONTINUOUS_WITHIN; REAL_LE_REFL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_ARITH
     `g - g':real^1 = k <=> g' + k = g`]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] LIM_TRANSFORM)) THEN
    MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN
    REWRITE_TAC[LIM_WITHIN; DIST_REAL; GSYM drop; IN_INTERVAL_1] THEN
    SIMP_TAC[REAL_ARITH `c <= x /\ &0 < abs(x - c) ==> ~(x <= c)`] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; DROP_VEC; REAL_SUB_REFL; REAL_ABS_NUM] THEN
    MESON_TAC[REAL_LT_01];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_within] THEN
  REWRITE_TAC[DIST_LIFT; IN_ELIM_THM; DIST_REAL; GSYM drop] THEN
  DISCH_THEN(fun th ->
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    CONJUNCTS_THEN (MP_TAC o SPEC `e / &2`) th) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `d:real^1` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `d:real^1`; `c:real^1`]
        VECTOR_VARIATION_COMBINE) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) - a:real = b`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < a ==> abs x < a`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VECTOR_VARIATION_POS_LE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `f:real^1->real^1 = \x. g' x - h' x` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`g':real^1->real^1`; `\x. --((h':real^1->real^1) x)`;
    `interval[c:real^1,d]`] VECTOR_VARIATION_TRIANGLE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_NEG] THEN
    MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUBSET THEN
    EXISTS_TAC `interval[c:real^1,b]` THEN
    ASM_SIMP_TAC[INCREASING_BOUNDED_VARIATION; SUBSET_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN  ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_SUB] THEN MATCH_MP_TAC(REAL_ARITH
   `y < a / &2 /\ z < a / &2 ==> x <= y + z ==> x < a`) THEN
  REWRITE_TAC[VECTOR_VARIATION_NEG] THEN CONJ_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand)
    INCREASING_VECTOR_VARIATION o lhand o snd) THEN
  (ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
     ASM_REWRITE_TAC[INTERVAL_EQ_EMPTY_1; IN_INTERVAL_1; REAL_NOT_LT] THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
     DISCH_THEN SUBST1_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let VECTOR_VARIATION_CONTINUOUS = prove
 (`!f:real^1->real^1 a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ((\x. lift(vector_variation(interval[a,x]) f))
             continuous (at c within interval[a,b]) <=>
            f continuous (at c within interval[a,b]))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!f:real^1->real^1.
        f continuous (at c within interval[a,b]) <=>
        f continuous (at c within interval[a,c]) /\
        f continuous (at c within interval[c,b])`
   (fun th -> REWRITE_TAC[th] THEN
              ASM_MESON_TAC[VECTOR_VARIATION_CONTINUOUS_LEFT;
                            VECTOR_VARIATION_CONTINUOUS_RIGHT]) THEN
  GEN_TAC THEN REWRITE_TAC[CONTINUOUS_WITHIN] THEN EQ_TAC THENL
   [DISCH_THEN(ASSUME_TAC o GEN_ALL o
     MATCH_MP (REWRITE_RULE[IMP_CONJ] LIM_WITHIN_SUBSET)) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP LIM_UNION) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LIM_WITHIN_SUBSET)] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_INTERVAL_1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC);;

let HAS_BOUNDED_VARIATION_DARBOUX_STRONG = prove
 (`!f a b.
     f has_bounded_variation_on interval[a,b]
     ==> ?g h. (!x. f x = g x - h x) /\
               (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
                      drop x <= drop y
                      ==> drop(g x) <= drop(g y)) /\
               (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
                      drop x <= drop y
                      ==> drop(h x) <= drop(h y)) /\
               (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
                      drop x < drop y
                      ==> drop(g x) < drop(g y)) /\
               (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
                      drop x < drop y
                      ==> drop(h x) < drop(h y)) /\
               (!x. x IN interval[a,b] /\
                    f continuous (at x within interval[a,x])
                    ==> g continuous (at x within interval[a,x]) /\
                        h continuous (at x within interval[a,x])) /\
               (!x. x IN interval[a,b] /\
                    f continuous (at x within interval[x,b])
                    ==> g continuous (at x within interval[x,b]) /\
                        h continuous (at x within interval[x,b])) /\
               (!x. x IN interval[a,b] /\
                    f continuous (at x within interval[a,b])
                    ==> g continuous (at x within interval[a,b]) /\
                        h continuous (at x within interval[a,b]))`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^1. x + lift(vector_variation (interval[a,x]) (f:real^1->real^1))`;
    `\x:real^1. x + lift(vector_variation (interval[a,x]) f) - f x`] THEN
  REWRITE_TAC[VECTOR_ARITH `(x + l) - (x + l - f):real^1 = f`] THEN
  REWRITE_TAC[LIFT_DROP; DROP_SUB; DROP_ADD] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC VECTOR_VARIATION_MONOTONE;
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x. a - (b - x) <= c - (d - x) ==> a - b <= c - d`) THEN
    EXISTS_TAC `drop(f(a:real^1))` THEN
    REWRITE_TAC[GSYM DROP_SUB] THEN
    MATCH_MP_TAC VECTOR_VARIATION_MINUS_FUNCTION_MONOTONE;
    MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC VECTOR_VARIATION_MONOTONE;
    MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x. a - (b - x) <= c - (d - x) ==> a - b <= c - d`) THEN
    EXISTS_TAC `drop(f(a:real^1))` THEN
    REWRITE_TAC[GSYM DROP_SUB] THEN
    MATCH_MP_TAC VECTOR_VARIATION_MINUS_FUNCTION_MONOTONE;
    MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `x:real^1`]
        VECTOR_VARIATION_CONTINUOUS_LEFT) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `x:real^1`]
        VECTOR_VARIATION_CONTINUOUS_LEFT) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `x:real^1`]
        VECTOR_VARIATION_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `x:real^1`]
        VECTOR_VARIATION_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `x:real^1`]
        VECTOR_VARIATION_CONTINUOUS) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `x:real^1`]
        VECTOR_VARIATION_CONTINUOUS) THEN
    ASM_REWRITE_TAC[]] THEN
  (CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_BOUNDED_VARIATION_ON_SUBSET));
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; INTERVAL_EQ_EMPTY_1] THEN
    ASM_REAL_ARITH_TAC));;

let HAS_BOUNDED_VARIATION_COUNTABLE_DISCONTINUITIES = prove
 (`!f:real^1->real^1 a b.
        f has_bounded_variation_on interval[a,b]
        ==> COUNTABLE {x | x IN interval[a,b] /\ ~(f continuous at x)}`,
  SUBGOAL_THEN
   `!f a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> COUNTABLE {x | x IN interval[a,b] /\ ~(f continuous at x)}`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [HAS_BOUNDED_VARIATION_DARBOUX]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
      MP_TAC(ISPECL [`g:real^1->real^1`; `a:real^1`; `b:real^1`] th) THEN
      MP_TAC(ISPECL [`h:real^1->real^1`; `a:real^1`; `b:real^1`] th)) THEN
    ASM_REWRITE_TAC[IMP_IMP; GSYM COUNTABLE_UNION] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT
     `(p /\ q ==> r) ==> a /\ ~r ==> a /\ ~p \/ a /\ ~q`) THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM ETA_AX] THEN
    ASM_SIMP_TAC[CONTINUOUS_SUB]] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `interval[a:real^1,b] = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; COUNTABLE_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[CLOSED_OPEN_INTERVAL_1] THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC
   `a INSERT b INSERT
    {x | x IN interval(a,b) /\ ~((f:real^1->real^1) continuous at x)}` THEN
  CONJ_TAC THENL [REWRITE_TAC[COUNTABLE_INSERT]; SET_TAC[]] THEN
  SUBGOAL_THEN
   `(!c:real^1. c IN interval(a,b) ==> c limit_point_of interval[a,c]) /\
    (!c:real^1. c IN interval(a,b) ==> c limit_point_of interval[c,b])`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[IN_INTERVAL_1; REAL_LE_REFL; LIMPT_OF_CONVEX;
             CONVEX_INTERVAL; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[GSYM INTERVAL_SING; GSYM SUBSET_ANTISYM_EQ] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`]
        INCREASING_LEFT_LIMIT_1) THEN
  ASM_REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^1->real^1` (LABEL_TAC "l")) THEN
  MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`]
        INCREASING_RIGHT_LIMIT_1) THEN
  ASM_REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^1->real^1` (LABEL_TAC "r")) THEN
  SUBGOAL_THEN
   `!c. c IN interval(a:real^1,b)
        ==> drop(l c) <= drop(f c) /\ drop(f c) <= drop(r c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(ISPEC `at c within interval[a:real^1,c]`
        LIM_DROP_UBOUND);
      MATCH_MP_TAC(ISPEC `at c within interval[c:real^1,b]`
        LIM_DROP_LBOUND)] THEN
    EXISTS_TAC `f:real^1->real^1` THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] INTERVAL_OPEN_SUBSET_CLOSED;
                 TRIVIAL_LIMIT_WITHIN; EVENTUALLY_WITHIN] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; IN_INTERVAL_1] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!c x. c IN interval(a:real^1,b) /\ x IN interval[a,b] /\ drop x < drop c
           ==> drop(f x) <= drop(l c)) /\
    (!c x. c IN interval(a:real^1,b) /\ x IN interval[a,b] /\ drop c < drop x
           ==> drop(r c) <= drop(f x))`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(ISPEC `at c within interval[a:real^1,c]`
        LIM_DROP_LBOUND);
      MATCH_MP_TAC(ISPEC `at c within interval[c:real^1,b]`
        LIM_DROP_UBOUND)] THEN
    EXISTS_TAC `f:real^1->real^1` THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] INTERVAL_OPEN_SUBSET_CLOSED;
                 TRIVIAL_LIMIT_WITHIN; EVENTUALLY_WITHIN]
    THENL
     [EXISTS_TAC `drop c - drop x`; EXISTS_TAC `drop x - drop c`] THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    X_GEN_TAC `y:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_ELIM_THM; DIST_REAL; GSYM drop] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COUNTABLE; ge_c] THEN
  TRANS_TAC CARD_LE_TRANS `rational` THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM ge_c] THEN
  REWRITE_TAC[COUNTABLE_RATIONAL; GSYM COUNTABLE; le_c] THEN
  SUBGOAL_THEN
   `!c. c IN interval(a,b) /\ ~((f:real^1->real^1) continuous at c)
          ==> drop(l(c:real^1)) < drop(r c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[DROP_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `l c = (f:real^1->real^1) c /\ r c = f c` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_LE_ANTISYM; DROP_EQ]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CONTINUOUS_AT]) THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `((f:real^1->real^1) --> f c) (at c within interval(a,b))`
    MP_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[OPEN_INTERVAL; LIM_WITHIN_OPEN]] THEN
    MATCH_MP_TAC LIM_WITHIN_SUBSET THEN
    EXISTS_TAC `interval[a:real^1,c] UNION interval[c,b]` THEN
    REWRITE_TAC[LIM_WITHIN_UNION] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[REWRITE_RULE[SUBSET] INTERVAL_OPEN_SUBSET_CLOSED];
      REWRITE_TAC[SUBSET; IN_UNION; IN_INTERVAL_1] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN interval(a,b) /\ ~((f:real^1->real^1) continuous at c)
        ==> ?q. rational q /\ drop(l c) < q /\ q < drop(r c)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `drop(l(c:real^1)) < drop(r c)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(drop(l(c:real^1)) + drop(r c)) / &2`;
                   `(drop(r c) - drop(l(c:real^1))) / &2`]
      RATIONAL_APPROXIMATION) THEN
    ASM_REWRITE_TAC[REAL_HALF; REAL_SUB_LT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; IN_ELIM_THM; IN_INTERVAL_1] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^1->real` THEN
  SIMP_TAC[IN] THEN DISCH_THEN(LABEL_TAC "*") THEN
  MATCH_MP_TAC(MESON[REAL_LE_TOTAL]
   `(!x y. P x y ==> P y x) /\ (!x y. drop x <= drop y ==> P x y)
    ==> !x y. P x y`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
  REWRITE_TAC[REAL_LE_LT; DROP_EQ] THEN
  ASM_CASES_TAC `x:real^1 = y` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `q(x:real^1) < q(y)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[REAL_LT_REFL]] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `drop(r(x:real^1))` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `drop(l(y:real^1))` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(f(inv(&2) % (x + y):real^1))` THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_ADD] THEN
  ASM_REAL_ARITH_TAC);;

let HAS_BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE_DERIVATIVE = prove
 (`!f:real^1->real^N s a b.
        COUNTABLE s /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s ==> f differentiable at x)
        ==> (f has_bounded_variation_on interval[a,b] <=>
             (\x. vector_derivative f (at x))
             absolutely_integrable_on interval[a,b])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION_EQ] THEN
  REWRITE_TAC[has_bounded_variation_on] THEN
  MATCH_MP_TAC(TAUT `q /\ (p <=> r) ==> (p <=> q /\ r)`) THEN CONJ_TAC THENL
   [ASM_CASES_TAC `interval[a:real^1,b] = {}` THEN
    ASM_REWRITE_TAC[INTEGRABLE_ON_EMPTY] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1]) THEN
    MP_TAC(ISPECL [`f:real^1->real^N`;
                   `\x. vector_derivative (f:real^1->real^N) (at x)`;
                   `s:real^1->bool`; `a:real^1`; `b:real^1`]
      FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG) THEN
    ASM_MESON_TAC[VECTOR_DERIVATIVE_WORKS; integrable_on;
                  HAS_VECTOR_DERIVATIVE_AT_WITHIN];
    MATCH_MP_TAC(MESON[HAS_BOUNDED_SETVARIATION_ON_EQ]
     `(!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s
               ==> f(interval[a,b]) = g(interval[a,b]))
      ==> (f has_bounded_setvariation_on s <=>
           g has_bounded_setvariation_on s)`) THEN
    SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND;
             GSYM INTERVAL_NE_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
    REWRITE_TAC[INTERVAL_NE_EMPTY_1] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^1->real^N`;
                   `\x. vector_derivative (f:real^1->real^N) (at x)`;
                   `s:real^1->bool`; `u:real^1`; `v:real^1`]
      FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG) THEN
    ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[INTEGRAL_UNIQUE]] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; IN_DIFF; SUBSET];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      ASM_SIMP_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN ASM SET_TAC[]]]);;

let HAS_BOUNDED_VARIATION_INTEGRABLE_NORM_DERIVATIVE = prove
 (`!f:real^1->real^N s a b.
        COUNTABLE s /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s ==> f differentiable at x)
        ==> (f has_bounded_variation_on interval[a,b] <=>
             (\x. lift(norm(vector_derivative f (at x))))
             integrable_on interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    STRIP_ASSUME_TAC th THEN
    REWRITE_TAC[MATCH_MP HAS_BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE_DERIVATIVE
                th]) THEN
  REWRITE_TAC[absolutely_integrable_on] THEN
  MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN
  ASM_CASES_TAC `interval[a:real^1,b] = {}` THEN
  ASM_REWRITE_TAC[INTEGRABLE_ON_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1]) THEN
  MP_TAC(ISPECL [`f:real^1->real^N`;
                 `\x. vector_derivative (f:real^1->real^N) (at x)`;
                 `s:real^1->bool`; `a:real^1`; `b:real^1`]
    FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG) THEN
  ASM_MESON_TAC[VECTOR_DERIVATIVE_WORKS; integrable_on;
                HAS_VECTOR_DERIVATIVE_AT_WITHIN]);;

let VECTOR_VARIATION_INTEGRAL_NORM_DERIVATIVE = prove
 (`!f:real^1->real^N s a b.
        COUNTABLE s /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s ==> f differentiable at x) /\
        f has_bounded_variation_on interval[a,b]
        ==> vector_variation (interval[a,b]) f =
                drop(integral (interval[a,b])
                        (\x. lift(norm(vector_derivative f (at x)))))`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`f:real^1->real^N`; `s:real^1->bool`; `a:real^1`; `b:real^1`]
   HAS_BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_SET_VARIATION) THEN
  REWRITE_TAC[vector_variation] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SET_VARIATION_EQ THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
  SIMP_TAC[INTERVAL_NE_EMPTY_1; INTERVAL_LOWERBOUND_1;
           INTERVAL_UPPERBOUND_1] THEN
  STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG THEN
  EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  ASM_MESON_TAC[VECTOR_DERIVATIVE_WORKS; HAS_VECTOR_DERIVATIVE_AT_WITHIN;
                IN_DIFF; SUBSET]);;

let INTEGRABLE_BOUNDED_VARIATION_PRODUCT = prove
 (`!f:real^1->real^N g a b.
        f integrable_on interval[a,b] /\
        g has_bounded_variation_on interval[a,b]
        ==> (\x. drop(g x) % f x) integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [HAS_BOUNDED_VARIATION_DARBOUX]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^1->real^1`; `k:real^1->real^1`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[DROP_SUB; VECTOR_SUB_RDISTRIB] THEN
  MATCH_MP_TAC INTEGRABLE_SUB THEN
  CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_INCREASING_PRODUCT THEN
  ASM_REWRITE_TAC[]);;

let INTEGRABLE_BOUNDED_VARIATION_PRODUCT_ALT = prove
 (`!f:real^1->real^N g a b.
        f integrable_on interval[a,b] /\
        (lift o g) has_bounded_variation_on interval[a,b]
        ==> (\x. g x % f x) integrable_on interval[a,b]`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_BOUNDED_VARIATION_PRODUCT) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let HAS_BOUNDED_VARIATION_ON_INDEFINITE_INTEGRAL_RIGHT = prove
 (`!f:real^1->real^N a b.
        f absolutely_integrable_on interval[a,b]
        ==> (\c. integral (interval[a,c]) f) has_bounded_variation_on
            interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  FIRST_ASSUM(MP_TAC o
    MATCH_MP ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_BOUNDED_SETVARIATION_ON_EQ) THEN
  SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY; LIFT_EQ;
           INTERVAL_UPPERBOUND_NONEMPTY] THEN
  SIMP_TAC[INTERVAL_NE_EMPTY_1; SUBSET_INTERVAL_1; GSYM REAL_NOT_LE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_ARITH
   `a:real^N = b - c <=> c + a = b`] THEN
  MATCH_MP_TAC INTEGRAL_COMBINE THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INTEGRABLE_ON_SUBINTERVAL) THEN
  ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

let HAS_BOUNDED_VARIATION_ON_INDEFINITE_INTEGRAL_LEFT = prove
 (`!f:real^1->real^N a b.
        f absolutely_integrable_on interval[a,b]
        ==> (\c. integral (interval[c,b]) f) has_bounded_variation_on
            interval[a,b]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[has_bounded_variation_on] THEN
  ONCE_REWRITE_TAC[GSYM HAS_BOUNDED_SETVARIATION_ON_NEG] THEN
  FIRST_ASSUM(MP_TAC o
    MATCH_MP ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_BOUNDED_SETVARIATION_ON_EQ) THEN
  SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY; LIFT_EQ;
           INTERVAL_UPPERBOUND_NONEMPTY] THEN
  SIMP_TAC[INTERVAL_NE_EMPTY_1; SUBSET_INTERVAL_1; GSYM REAL_NOT_LE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_ARITH
   `a:real^N = --(b - c) <=> a + b = c`] THEN
  MATCH_MP_TAC INTEGRAL_COMBINE THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INTEGRABLE_ON_SUBINTERVAL) THEN
  ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Rectifiable paths and path length defined using variation.                *)
(* ------------------------------------------------------------------------- *)

let rectifiable_path = new_definition
 `rectifiable_path (g:real^1->real^N) <=>
    path g /\ g has_bounded_variation_on interval[vec 0,vec 1]`;;

let path_length = new_definition
 `path_length (g:real^1->real^N) =
  vector_variation (interval[vec 0,vec 1]) g`;;

let BOUNDED_RECTIFIABLE_PATH_IMAGE = prove
 (`!g:real^1->real^N. rectifiable_path g ==> bounded(path_image g)`,
  SIMP_TAC[rectifiable_path; BOUNDED_PATH_IMAGE]);;

let RECTIFIABLE_PATH_IMP_PATH = prove
 (`!g:real^1->real^N. rectifiable_path g ==> path g`,
  SIMP_TAC[rectifiable_path]);;

let RECTIFIABLE_PATH_LINEPATH = prove
 (`!a b:real^N. rectifiable_path(linepath(a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rectifiable_path; PATH_LINEPATH] THEN
  REWRITE_TAC[linepath] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_ADD THEN
  REWRITE_TAC[GSYM DROP_VEC; GSYM DROP_SUB] THEN
  CONJ_TAC THEN MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_MUL THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_CONST] THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_ID] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_CONST] THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_ID]);;

let RECTIFIABLE_PATH_REVERSEPATH = prove
 (`!g:real^1->real^N. rectifiable_path(reversepath g) <=> rectifiable_path g`,
  SUBGOAL_THEN
   `!g:real^1->real^N. rectifiable_path g ==> rectifiable_path(reversepath g)`
   (fun th -> MESON_TAC[th; REVERSEPATH_REVERSEPATH]) THEN
  GEN_TAC THEN REWRITE_TAC[rectifiable_path] THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[PATH_REVERSEPATH] THEN
  REWRITE_TAC[reversepath] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_COMPOSE_DECREASING THEN
  ASM_REWRITE_TAC[DROP_SUB; VECTOR_SUB_RZERO; VECTOR_SUB_REFL] THEN
  REAL_ARITH_TAC);;

let PATH_LENGTH_REVERSEPATH = prove
 (`!g:real^1->real^N. path_length(reversepath g) = path_length g`,
  GEN_TAC THEN REWRITE_TAC[path_length; reversepath] THEN
  REWRITE_TAC[VECTOR_SUB; VECTOR_VARIATION_REFLECT] THEN
  REWRITE_TAC[VECTOR_VARIATION_TRANSLATION] THEN
  REWRITE_TAC[REFLECT_INTERVAL; GSYM INTERVAL_TRANSLATION] THEN
  REWRITE_TAC[GSYM VECTOR_SUB; VECTOR_SUB_REFL; VECTOR_SUB_RZERO]);;

let RECTIFIABLE_PATH_SUBPATH = prove
 (`!u v g:real^1->real^N.
        rectifiable_path g /\
        u IN interval[vec 0,vec 1] /\
        v IN interval[vec 0,vec 1]
        ==> rectifiable_path(subpath u v g)`,
  REPEAT GEN_TAC THEN SIMP_TAC[PATH_SUBPATH; rectifiable_path] THEN
  STRIP_TAC THEN REWRITE_TAC[subpath] THEN
  ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_AFFINITY_EQ; IMAGE_AFFINITY_INTERVAL] THEN
  REWRITE_TAC[UNIT_INTERVAL_NONEMPTY; DROP_SUB; REAL_SUB_LE; REAL_SUB_0] THEN
  DISJ2_TAC THEN COND_CASES_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET_INTERVAL_1] THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_VEC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  ASM_REAL_ARITH_TAC);;

let RECTIFIABLE_PATH_JOIN = prove
 (`!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2
        ==> (rectifiable_path(g1 ++ g2) <=>
             rectifiable_path g1 /\ rectifiable_path g2)`,
  REPEAT GEN_TAC THEN SIMP_TAC[rectifiable_path; PATH_JOIN] THEN
  REWRITE_TAC[pathfinish; pathstart] THEN DISCH_TAC THEN
  ASM_CASES_TAC `path(g1:real^1->real^N)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `path(g2:real^1->real^N)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g1 ++ g2:real^1->real^N`; `vec 0:real^1`; `vec 1:real^1`;
                 `lift(&1 / &2)`]
        HAS_BOUNDED_VARIATION_ON_COMBINE) THEN
  REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[joinpaths] THEN BINOP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THENL
   [EXISTS_TAC
     `(\x. (g1:real^1->real^N)(&2 % x)) has_bounded_variation_on
      interval [vec 0,lift(&1 / &2)]` THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `&2 % x:real^N = &2 % x + vec 0`];
    EXISTS_TAC
     `(\x. (g2:real^1->real^N)(&2 % x - vec 1)) has_bounded_variation_on
      interval [lift (&1 / &2),vec 1]` THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `&2 % x - v:real^N = &2 % x + --v`]] THEN
  (CONJ_TAC THENL
    [ALL_TAC;
     REWRITE_TAC[HAS_BOUNDED_VARIATION_AFFINITY_EQ] THEN
     REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; INTERVAL_EQ_EMPTY_1] THEN
     REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
     AP_TERM_TAC THEN AP_TERM_TAC THEN
     REWRITE_TAC[CONS_11; PAIR_EQ; GSYM DROP_EQ] THEN
     REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP; DROP_VEC; DROP_NEG] THEN
     REAL_ARITH_TAC]) THEN
  MATCH_MP_TAC(MESON[HAS_BOUNDED_VARIATION_ON_EQ]
   `(!x. x IN s ==> f x = g x)
    ==> (f has_bounded_variation_on s <=>
         g has_bounded_variation_on s)`) THEN
  SIMP_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN X_GEN_TAC `x:real^1` THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 % x + --vec 1:real^1 = vec 0 /\ &2 % x = vec 1`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[VECTOR_SUB_EQ; GSYM VECTOR_SUB] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC] THEN ASM_REAL_ARITH_TAC);;

let RECTIFIABLE_PATH_JOIN_IMP = prove
 (`!g1 g2:real^1->real^N.
        rectifiable_path g1 /\ rectifiable_path g2 /\
        pathfinish g1 = pathstart g2
        ==> rectifiable_path(g1 ++ g2)`,
  SIMP_TAC[RECTIFIABLE_PATH_JOIN]);;

let RECTIFIABLE_PATH_JOIN_EQ = prove
 (`!g1 g2:real^1->real^N.
        rectifiable_path g1 /\ rectifiable_path g2
        ==> (rectifiable_path (g1 ++ g2) <=> pathfinish g1 = pathstart g2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[RECTIFIABLE_PATH_JOIN_IMP] THEN
  DISCH_TAC THEN MATCH_MP_TAC PATH_JOIN_PATH_ENDS THEN
  ASM_SIMP_TAC[RECTIFIABLE_PATH_IMP_PATH]);;

let PATH_LENGTH_JOIN = prove
 (`!g1 g2:real^1->real^N.
        rectifiable_path g1 /\ rectifiable_path g2 /\
        pathfinish g1 = pathstart g2
        ==> path_length(g1 ++ g2) = path_length g1 + path_length g2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_length] THEN
  MP_TAC(ISPECL [`g1 ++ g2:real^1->real^N`; `vec 0:real^1`; `vec 1:real^1`;
                 `lift(&1 / &2)`]
        VECTOR_VARIATION_COMBINE) THEN
  REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[rectifiable_path; RECTIFIABLE_PATH_JOIN_IMP];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `vector_variation (interval [vec 0,lift (&1 / &2)])
                     (\x. (g1:real^1->real^N)(&2 % x)) +
    vector_variation (interval [lift (&1 / &2),vec 1])
                     (\x.  (g2:real^1->real^N)(&2 % x - vec 1))` THEN
  CONJ_TAC THENL
   [BINOP_TAC THEN MATCH_MP_TAC VECTOR_VARIATION_EQ THEN
    SIMP_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; joinpaths] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathfinish; pathstart]) THEN
    X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&2 % x - vec 1:real^1 = vec 0 /\ &2 % x = vec 1`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[VECTOR_ARITH `&2 % x:real^N = &2 % x + vec 0`] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `(&2 % x + vec 0) - v:real^N = &2 % x + --v`] THEN
    REWRITE_TAC[VECTOR_VARIATION_AFFINITY; IMAGE_AFFINITY_INTERVAL] THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; LIFT_DROP; DROP_VEC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN BINOP_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CONS_11; PAIR_EQ; GSYM DROP_EQ] THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP; DROP_VEC; DROP_NEG] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Useful equivalent formulations where the path is differentiable.          *)
(* ------------------------------------------------------------------------- *)

let RECTIFIABLE_PATH_DIFFERENTIABLE = prove
 (`!g:real^1->real^N s.
        COUNTABLE s /\ path g /\
        (!t. t IN interval[vec 0,vec 1] DIFF s ==> g differentiable at t)
        ==> (rectifiable_path g <=>
                (\t. vector_derivative g (at t))
                absolutely_integrable_on interval[vec 0,vec 1])`,
  SIMP_TAC[rectifiable_path] THEN REWRITE_TAC[path] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
    HAS_BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE_DERIVATIVE THEN
  EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[]);;

let PATH_LENGTH_DIFFERENTIABLE = prove
 (`!g:real^1->real^N s.
        COUNTABLE s /\ rectifiable_path g /\
        (!t. t IN interval[vec 0,vec 1] DIFF s ==> g differentiable at t)
        ==> path_length g =
                drop(integral (interval[vec 0,vec 1])
                              (\t. lift(norm(vector_derivative g (at t)))))`,
  REWRITE_TAC[rectifiable_path; path_length; path] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VECTOR_VARIATION_INTEGRAL_NORM_DERIVATIVE THEN
  EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[]);;


print_endline "integration.ml loaded"
