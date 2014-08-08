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
open Integration
include Measure1

(* ------------------------------------------------------------------------- *)
(* Hence the effect of an arbitrary linear map on a measurable set.          *)
(* ------------------------------------------------------------------------- *)

let LAMBDA_SWAP_GALOIS = prove
 (`!x:real^N y:real^N.
        1 <= m /\ m <= dimindex(:N) /\ 1 <= n /\ n <= dimindex(:N)
        ==> (x = (lambda i. y$swap(m,n) i) <=>
             (lambda i. x$swap(m,n) i) = y)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; IN_DIMINDEX_SWAP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `swap(m,n) (i:num)`) THEN
  ASM_SIMP_TAC[IN_DIMINDEX_SWAP] THEN
  ASM_MESON_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] SWAP_IDEMPOTENT]);;

let LAMBDA_ADD_GALOIS = prove
 (`!x:real^N y:real^N.
        1 <= m /\ m <= dimindex(:N) /\ 1 <= n /\ n <= dimindex(:N) /\
        ~(m = n)
        ==> (x = (lambda i. if i = m then y$m + y$n else y$i) <=>
             (lambda i. if i = m then x$m - x$n else x$i) = y)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let HAS_MEASURE_SHEAR_INTERVAL = prove
 (`!a b:real^N m n.
        1 <= m /\ m <= dimindex(:N) /\
        1 <= n /\ n <= dimindex(:N) /\
        ~(m = n) /\ ~(interval[a,b] = {}) /\
        &0 <= a$n
        ==> (IMAGE (\x. (lambda i. if i = m then x$m + x$n else x$i))
                   (interval[a,b]):real^N->bool)
            has_measure measure (interval [a,b])`,
  let lemma = prove
   (`!s t u v:real^N->bool.
          measurable s /\ measurable t /\ measurable u /\
          negligible(s INTER t) /\ negligible(s INTER u) /\
          negligible(t INTER u) /\
          s UNION t UNION u = v
          ==> v has_measure (measure s) + (measure t) + (measure u)`,
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_UNION] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MEASURE_UNION; MEASURABLE_UNION] THEN
    ASM_SIMP_TAC[MEASURE_EQ_0; UNION_OVER_INTER; MEASURE_UNION;
                 MEASURABLE_UNION; NEGLIGIBLE_INTER; MEASURABLE_INTER] THEN
    REAL_ARITH_TAC)
  and lemma' = prove
   (`!s t u a:real^N.
          measurable s /\ measurable t /\
          s UNION (IMAGE (\x. a + x) t) = u /\
          negligible(s INTER (IMAGE (\x. a + x) t))
          ==> measure s + measure t = measure u`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[MEASURE_NEGLIGIBLE_UNION; MEASURABLE_TRANSLATION_EQ;
                 MEASURE_TRANSLATION]) in
  REWRITE_TAC[INTERVAL_NE_EMPTY] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `linear((\x. lambda i. if i = m then x$m + x$n else x$i):real^N->real^N)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[linear; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; CART_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (\x. lambda i. if i = m then x$m + x$n else x$i)
            (interval[a:real^N,b]):real^N->bool`;
    `interval[a,(lambda i. if i = m then (b:real^N)$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x <= a$m}`;
    `interval[a,(lambda i. if i = m then b$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x >= (b:real^N)$m}`;
    `interval[a:real^N,
              (lambda i. if i = m then (b:real^N)$m + b$n else b$i)]`]
     lemma) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_LINEAR_IMAGE; CONVEX_INTERVAL;
                 CONVEX_HALFSPACE_LE; CONVEX_HALFSPACE_GE;
                 CONVEX_INTER; MEASURABLE_CONVEX; BOUNDED_INTER;
                 BOUNDED_LINEAR_IMAGE; BOUNDED_INTERVAL] THEN
    REWRITE_TAC[INTER] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_IMAGE] THEN
    ASM_SIMP_TAC[LAMBDA_ADD_GALOIS; UNWIND_THM1] THEN
    ASM_SIMP_TAC[IN_INTERVAL; IN_ELIM_THM; LAMBDA_BETA;
                 DOT_BASIS; DOT_LSUB] THEN
    ONCE_REWRITE_TAC[MESON[]
       `(!i:num. P i) <=> P m /\ (!i. ~(i = m) ==> P i)`] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[TAUT `(p /\ x) /\ (q /\ x) /\ r <=> x /\ p /\ q /\ r`;
                TAUT `(p /\ x) /\ q /\ (r /\ x) <=> x /\ p /\ q /\ r`;
                TAUT `((p /\ x) /\ q) /\ (r /\ x) /\ s <=>
                            x /\ p /\ q /\ r /\ s`;
            TAUT `(a /\ x \/ (b /\ x) /\ c \/ (d /\ x) /\ e <=> f /\ x) <=>
                  x ==> (a \/ b /\ c \/ d /\ e <=> f)`] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC;
      GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_INTER THEN DISJ2_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THENL
     [EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (a:real^N)$m}`;
      EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (b:real^N)$m}`;
      EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (b:real^N)$m}`]
    THEN (CONJ_TAC THENL
      [MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN
       REWRITE_TAC[VECTOR_SUB_EQ] THEN
       ASM_MESON_TAC[BASIS_INJ];
       ASM_SIMP_TAC[DOT_LSUB; DOT_BASIS; SUBSET; IN_ELIM_THM;
                    NOT_IN_EMPTY] THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
       ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE;
               MEASURABLE_LINEAR_IMAGE_INTERVAL;
               MEASURABLE_INTERVAL] THEN
  MP_TAC(ISPECL
   [`interval[a,(lambda i. if i = m then (b:real^N)$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x <= a$m}`;
    `interval[a,(lambda i. if i = m then b$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x >= (b:real^N)$m}`;
    `interval[a:real^N,
              (lambda i. if i = m then (a:real^N)$m + b$n
                         else (b:real^N)$i)]`;
    `(lambda i. if i = m then (a:real^N)$m - (b:real^N)$m
                else &0):real^N`]
     lemma') THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_LINEAR_IMAGE; CONVEX_INTERVAL;
                 CONVEX_HALFSPACE_LE; CONVEX_HALFSPACE_GE;
                 CONVEX_INTER; MEASURABLE_CONVEX; BOUNDED_INTER;
                 BOUNDED_LINEAR_IMAGE; BOUNDED_INTERVAL] THEN
    REWRITE_TAC[INTER] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_IMAGE] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^N = (lambda i. p i) + y <=>
                                   x - (lambda i. p i) = y`] THEN
    ASM_SIMP_TAC[IN_INTERVAL; IN_ELIM_THM; LAMBDA_BETA;
                 DOT_BASIS; DOT_LSUB; UNWIND_THM1;
                 VECTOR_SUB_COMPONENT] THEN
    ONCE_REWRITE_TAC[MESON[]
       `(!i:num. P i) <=> P m /\ (!i. ~(i = m) ==> P i)`] THEN
    ASM_SIMP_TAC[REAL_SUB_RZERO] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN
      FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC
       `!i. ~(i = m)
            ==> 1 <= i /\ i <= dimindex (:N)
                ==> (a:real^N)$i <= (x:real^N)$i /\
                    x$i <= (b:real^N)$i` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[TAUT `((a /\ b) /\ c) /\ (d /\ e) /\ f <=>
                             (b /\ e) /\ a /\ c /\ d /\ f`] THEN
      ONCE_REWRITE_TAC[SET_RULE
       `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
      MATCH_MP_TAC NEGLIGIBLE_INTER THEN DISJ2_TAC THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (a:real^N)$m}`
      THEN CONJ_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN
        REWRITE_TAC[VECTOR_SUB_EQ] THEN
        ASM_MESON_TAC[BASIS_INJ];
        ASM_SIMP_TAC[DOT_LSUB; DOT_BASIS; SUBSET; IN_ELIM_THM;
                     NOT_IN_EMPTY] THEN
        FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `a:real = b + c ==> a = x + b ==> x = c`) THEN
  ASM_SIMP_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES;
               LAMBDA_BETA] THEN
  REPEAT(COND_CASES_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]) THEN
  SUBGOAL_THEN `1..dimindex(:N) = m INSERT ((1..dimindex(:N)) DELETE m)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[IN_DELETE] THEN
  MATCH_MP_TAC(REAL_RING
   `s1:real = s3 /\ s2 = s3
    ==> ((bm + bn) - am) * s1 =
        ((am + bn) - am) * s2 + (bm - am) * s3`) THEN
  CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
  SIMP_TAC[IN_DELETE] THEN REAL_ARITH_TAC);;

let HAS_MEASURE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ measurable s
        ==> (IMAGE f s) has_measure (abs(det(matrix f)) * measure s)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC INDUCT_LINEAR_ELEMENTARY THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC o SPEC `IMAGE (g:real^N->real^N) s`)
     (MP_TAC o SPEC `s:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [HAS_MEASURE_MEASURABLE_MEASURE] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_COMPOSE; DET_MUL; REAL_ABS_MUL] THEN
    REWRITE_TAC[IMAGE_o; GSYM REAL_MUL_ASSOC];

    MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `m:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(!x y. (f:real^N->real^N) x = f y ==> x = y)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[LINEAR_SINGULAR_INTO_HYPERPLANE] THEN
      EXISTS_TAC `basis m:real^N` THEN
      ASM_SIMP_TAC[BASIS_NONZERO; DOT_BASIS];
      ALL_TAC] THEN
    MP_TAC(ISPEC `matrix f:real^N^N` INVERTIBLE_DET_NZ) THEN
    ASM_SIMP_TAC[INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE_INJECTIVE;
                 MATRIX_WORKS; REAL_ABS_NUM; REAL_MUL_LZERO] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[HAS_MEASURE_0] THEN
    ASM_SIMP_TAC[NEGLIGIBLE_LINEAR_SINGULAR_IMAGE];

    MAP_EVERY X_GEN_TAC [`c:num->real`; `s:real^N->bool`] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[HAS_MEASURE_MEASURE]) THEN
    FIRST_ASSUM(MP_TAC o SPEC `c:num->real` o
     MATCH_MP HAS_MEASURE_STRETCH) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[matrix; LAMBDA_BETA] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) DET_DIAGONAL o rand o snd) THEN
    SIMP_TAC[LAMBDA_BETA; BASIS_COMPONENT; REAL_MUL_RZERO] THEN
    DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
    REWRITE_TAC[REAL_MUL_RID];

    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_MEASURE_LINEAR_SUFFICIENT THEN
    ASM_SIMP_TAC[linear; LAMBDA_BETA; IN_DIMINDEX_SWAP; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; CART_EQ] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
    SUBGOAL_THEN `matrix (\x:real^N. lambda i. x$swap (m,n) i):real^N^N =
                  transp(lambda i j. (mat 1:real^N^N)$i$swap (m,n) j)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[MATRIX_EQ; LAMBDA_BETA; IN_DIMINDEX_SWAP;
                    matrix_vector_mul; CART_EQ; matrix; mat; basis;
                    COND_COMPONENT; transp] THEN
      REWRITE_TAC[EQ_SYM_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[DET_TRANSP] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) DET_PERMUTE_COLUMNS o
        rand o lhand o rand o snd) THEN
    ASM_SIMP_TAC[PERMUTES_SWAP; IN_NUMSEG; ETA_AX] THEN
    DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[DET_I; REAL_ABS_SIGN; REAL_MUL_RID; REAL_MUL_LID] THEN
    ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
     [ASM_SIMP_TAC[IMAGE_CLAUSES; HAS_MEASURE_EMPTY; MEASURE_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(IMAGE (\x:real^N. lambda i. x$swap (m,n) i)
              (interval[a,b]):real^N->bool = {})`
    MP_TAC THENL [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (\x:real^N. lambda i. x$swap (m,n) i)
              (interval[a,b]):real^N->bool =
      interval[(lambda i. a$swap (m,n) i),
               (lambda i. b$swap (m,n) i)]`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTERVAL; IN_IMAGE] THEN
      ASM_SIMP_TAC[LAMBDA_SWAP_GALOIS; UNWIND_THM1] THEN
      SIMP_TAC[LAMBDA_BETA] THEN GEN_TAC THEN EQ_TAC THEN
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `swap(m,n) (i:num)`) THEN
      ASM_SIMP_TAC[IN_DIMINDEX_SWAP] THEN
      ASM_MESON_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] SWAP_IDEMPOTENT];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_INTERVAL] THEN
    REWRITE_TAC[MEASURE_INTERVAL] THEN
    ASM_SIMP_TAC[CONTENT_CLOSED_INTERVAL; GSYM INTERVAL_NE_EMPTY] THEN
    DISCH_THEN(K ALL_TAC) THEN SIMP_TAC[LAMBDA_BETA] THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; IN_DIMINDEX_SWAP] THEN
    MP_TAC(ISPECL [`\i. (b - a:real^N)$i`; `swap(m:num,n)`; `1..dimindex(:N)`]
                (GSYM PRODUCT_PERMUTE)) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PERMUTES_SWAP; IN_NUMSEG];

    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_MEASURE_LINEAR_SUFFICIENT THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[linear; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                   VECTOR_MUL_COMPONENT; CART_EQ] THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
    SUBGOAL_THEN
      `det(matrix(\x. lambda i. if i = m then (x:real^N)$m + x$n
                                else x$i):real^N^N) = &1`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[matrix; basis; COND_COMPONENT; LAMBDA_BETA] THEN
      FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
       `~(m:num = n) ==> m < n \/ n < m`))
      THENL
       [W(MP_TAC o PART_MATCH (lhs o rand) DET_UPPERTRIANGULAR o lhs o snd);
        W(MP_TAC o PART_MATCH (lhs o rand) DET_LOWERTRIANGULAR o lhs o snd)]
      THEN ASM_SIMP_TAC[LAMBDA_BETA; BASIS_COMPONENT; COND_COMPONENT;
                        matrix; REAL_ADD_RID; COND_ID;
                        PRODUCT_CONST_NUMSEG; REAL_POW_ONE] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LID] THEN
    ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
     [ASM_SIMP_TAC[IMAGE_CLAUSES; HAS_MEASURE_EMPTY; MEASURE_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (\x. lambda i. if i = m then x$m + x$n else x$i) (interval [a,b]) =
      IMAGE (\x:real^N. (lambda i. if i = m \/ i = n then a$n else &0) +
                        x)
            (IMAGE (\x:real^N. lambda i. if i = m then x$m + x$n else x$i)
                   (IMAGE (\x. (lambda i. if i = n then --(a$n) else &0) + x)
                          (interval[a,b])))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[FUN_EQ_THM; o_THM; VECTOR_ADD_COMPONENT; LAMBDA_BETA;
                   CART_EQ] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN
      STRIP_TAC THEN ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i:num = n` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_MEASURE_TRANSLATION THEN
    SUBGOAL_THEN
     `measure(interval[a,b]) =
      measure(IMAGE (\x:real^N. (lambda i. if i = n then --(a$n) else &0) + x)
                    (interval[a,b]):real^N->bool)`
    SUBST1_TAC THENL [REWRITE_TAC[MEASURE_TRANSLATION]; ALL_TAC] THEN
    SUBGOAL_THEN
     `~(IMAGE (\x:real^N. (lambda i. if i = n then --(a$n) else &0) + x)
                    (interval[a,b]):real^N->bool = {})`
    MP_TAC THENL [ASM_SIMP_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `c + x:real^N = &1 % x + c`] THEN
    ASM_REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; REAL_POS] THEN
    DISCH_TAC THEN MATCH_MP_TAC HAS_MEASURE_SHEAR_INTERVAL THEN
    ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let MEASURABLE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ measurable s ==> measurable(IMAGE f s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE) THEN
  SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE]);;

let MEASURE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ measurable s
        ==> measure(IMAGE f s) = abs(det(matrix f)) * measure s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE) THEN
  SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE]);;

let HAS_MEASURE_LINEAR_IMAGE_ALT = prove
 (`!f:real^N->real^N s m.
        linear f /\ s has_measure m
        ==> (IMAGE f s) has_measure (abs(det(matrix f)) * m)`,
  MESON_TAC[MEASURE_UNIQUE; measurable; HAS_MEASURE_LINEAR_IMAGE]);;

let HAS_MEASURE_LINEAR_IMAGE_SAME = prove
 (`!f s. linear f /\ measurable s /\ abs(det(matrix f)) = &1
         ==> (IMAGE f s) has_measure (measure s)`,
  MESON_TAC[HAS_MEASURE_LINEAR_IMAGE; REAL_MUL_LID]);;

let MEASURE_LINEAR_IMAGE_SAME = prove
 (`!f:real^N->real^N s.
        linear f /\ measurable s /\ abs(det(matrix f)) = &1
        ==> measure(IMAGE f s) = measure s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE_SAME) THEN
  SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE]);;

let MEASURABLE_LINEAR_IMAGE_EQ = prove
 (`!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (measurable (IMAGE f s) <=> measurable s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE MEASURABLE_LINEAR_IMAGE));;

add_linear_invariants [MEASURABLE_LINEAR_IMAGE_EQ];;

let NEGLIGIBLE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s. linear f /\ negligible s ==> negligible(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM HAS_MEASURE_0] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE_ALT) THEN
  REWRITE_TAC[REAL_MUL_RZERO]);;

let NEGLIGIBLE_LINEAR_IMAGE_EQ = prove
 (`!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (negligible (IMAGE f s) <=> negligible s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE NEGLIGIBLE_LINEAR_IMAGE));;

add_linear_invariants [NEGLIGIBLE_LINEAR_IMAGE_EQ];;

let HAS_MEASURE_ORTHOGONAL_IMAGE = prove
 (`!f:real^N->real^N s m.
        orthogonal_transformation f /\ s has_measure m
        ==> (IMAGE f s) has_measure m`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE_ALT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(REAL_RING `x = &1 ==> x * m = m`) THEN
  REWRITE_TAC[REAL_ARITH `abs x = &1 <=> x = &1 \/ x = -- &1`] THEN
  MATCH_MP_TAC DET_ORTHOGONAL_MATRIX THEN
  ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX]);;

let HAS_MEASURE_ORTHOGONAL_IMAGE_EQ = prove
 (`!f:real^N->real^N s m.
        orthogonal_transformation f
        ==> ((IMAGE f s) has_measure m <=> s has_measure m)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[HAS_MEASURE_ORTHOGONAL_IMAGE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
   REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_ORTHOGONAL_IMAGE) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; IMAGE_I]);;

add_linear_invariants
 [REWRITE_RULE[ORTHOGONAL_TRANSFORMATION] HAS_MEASURE_ORTHOGONAL_IMAGE_EQ];;

let MEASURE_ORTHOGONAL_IMAGE_EQ = prove
 (`!f:real^N->real^N s.
        orthogonal_transformation f
        ==> measure(IMAGE f s) = measure s`,
  SIMP_TAC[measure; HAS_MEASURE_ORTHOGONAL_IMAGE_EQ]);;

add_linear_invariants
 [REWRITE_RULE[ORTHOGONAL_TRANSFORMATION] MEASURE_ORTHOGONAL_IMAGE_EQ];;

let HAS_MEASURE_ISOMETRY = prove
 (`!f:real^M->real^N s m.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x. norm(f x) = norm x)
        ==> (IMAGE f s has_measure m <=> s has_measure m)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `IMAGE ((\x. lambda i. x$i):real^N->real^M) (IMAGE (f:real^M->real^N) s)
    has_measure m` THEN
  CONJ_TAC THENL
   [SPEC_TAC(`IMAGE (f:real^M->real^N) s`,`s:real^N->bool`) THEN GEN_TAC THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[has_measure] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
        HAS_INTEGRAL_TWIZZLE_EQ o lhand o snd) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM I_DEF; PERMUTES_I];
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC HAS_MEASURE_ORTHOGONAL_IMAGE_EQ THEN
    ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT];
      X_GEN_TAC `x:real^M` THEN
      TRANS_TAC EQ_TRANS `norm((f:real^M->real^N) x)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      SIMP_TAC[NORM_EQ; dot; LAMBDA_BETA] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA]]]);;

let MEASURABLE_LINEAR_IMAGE_EQ_GEN = prove
 (`!f:real^M->real^N s.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x y. f x = f y ==> x = y)
        ==> (measurable(IMAGE f s) <=> measurable s)`,
  REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
   `measurable(IMAGE ((\x. lambda i. x$i):real^N->real^M)
                     (IMAGE (f:real^M->real^N) s))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN REWRITE_TAC[measurable] THEN
    AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_MEASURE_ISOMETRY THEN
    ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT];
      SIMP_TAC[NORM_EQ; dot; LAMBDA_BETA] THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC MEASURABLE_LINEAR_IMAGE_EQ THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT];
      SIMP_TAC[CART_EQ; LAMBDA_BETA; o_DEF] THEN
      ASM_MESON_TAC[CART_EQ]]]);;

let MEASURE_ISOMETRY = prove
 (`!f:real^M->real^N s.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x. norm(f x) = norm x)
        ==> measure (IMAGE f s) = measure s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[measure] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HAS_MEASURE_ISOMETRY th]));;

(* ------------------------------------------------------------------------- *)
(* Measure of a standard simplex.                                            *)
(* ------------------------------------------------------------------------- *)

let CONGRUENT_IMAGE_STD_SIMPLEX = prove
 (`!p. p permutes 1..dimindex(:N)
       ==> {x:real^N | &0 <= x$(p 1) /\ x$(p(dimindex(:N))) <= &1 /\
                       (!i. 1 <= i /\ i < dimindex(:N)
                            ==> x$(p i) <= x$(p(i + 1)))} =
           IMAGE (\x:real^N. lambda i. sum(1..inverse p(i)) (\j. x$j))
                 {x | (!i. 1 <= i /\ i <= dimindex (:N) ==> &0 <= x$i) /\
                      sum (1..dimindex (:N)) (\i. x$i) <= &1}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA; LAMBDA_BETA_PERM; LE_REFL;
                 ARITH_RULE `i < n ==> i <= n /\ i + 1 <= n`;
                 ARITH_RULE `1 <= n + 1`; DIMINDEX_GE_1] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_INVERSES th]) THEN
    ASM_SIMP_TAC[SUM_SING_NUMSEG; DIMINDEX_GE_1; LE_REFL] THEN
    REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    ASM_SIMP_TAC[REAL_LE_ADDR] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  STRIP_TAC THEN
  EXISTS_TAC `(lambda i. if i = 1 then x$(p 1)
                         else (x:real^N)$p(i) - x$p(i - 1)):real^N` THEN
  ASM_SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA; LAMBDA_BETA_PERM; LE_REFL;
               ARITH_RULE `i < n ==> i <= n /\ i + 1 <= n`;
               ARITH_RULE `1 <= n + 1`; DIMINDEX_GE_1; CART_EQ] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `1 <= inverse (p:num->num) i /\
                  !x. x <= inverse p i ==> x <= dimindex(:N)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_INVERSE; IN_NUMSEG; LE_TRANS; PERMUTES_IN_IMAGE];
      ASM_SIMP_TAC[LAMBDA_BETA] THEN ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH]] THEN
    SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n = 1)`] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o BINDER_CONV)
                [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[SUM_PARTIAL_PRE] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0; COND_ID] THEN
    REWRITE_TAC[REAL_MUL_LID; ARITH; REAL_SUB_RZERO] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `1 <= p ==> p = 1 \/ 2 <= p`) o CONJUNCT1) THEN
    ASM_SIMP_TAC[ARITH] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_INVERSES th]) THEN
    REWRITE_TAC[REAL_ADD_RID] THEN TRY REAL_ARITH_TAC THEN
    ASM_MESON_TAC[PERMUTES_INVERSE_EQ; PERMUTES_INVERSE];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
    ASM_SIMP_TAC[SUB_ADD] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;

    SIMP_TAC[SUM_CLAUSES_LEFT; DIMINDEX_GE_1; ARITH;
             ARITH_RULE `2 <= n ==> ~(n = 1)`] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o BINDER_CONV)
                [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[SUM_PARTIAL_PRE] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0; COND_ID] THEN
    REWRITE_TAC[REAL_MUL_LID; ARITH; REAL_SUB_RZERO] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[REAL_ARITH `x + y - x:real = y`] THEN
    ASM_MESON_TAC[DIMINDEX_GE_1;
                  ARITH_RULE `1 <= n /\ ~(2 <= n) ==> n = 1`]]);;

let HAS_MEASURE_IMAGE_STD_SIMPLEX = prove
 (`!p. p permutes 1..dimindex(:N)
       ==> {x:real^N | &0 <= x$(p 1) /\ x$(p(dimindex(:N))) <= &1 /\
                       (!i. 1 <= i /\ i < dimindex(:N)
                            ==> x$(p i) <= x$(p(i + 1)))}
           has_measure
           (measure (convex hull
             (vec 0 INSERT {basis i:real^N | 1 <= i /\ i <= dimindex(:N)})))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONGRUENT_IMAGE_STD_SIMPLEX] THEN
  ASM_SIMP_TAC[GSYM STD_SIMPLEX] THEN
  MATCH_MP_TAC HAS_MEASURE_LINEAR_IMAGE_SAME THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear; CART_EQ] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                 GSYM SUM_ADD_NUMSEG; GSYM SUM_LMUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[];
    MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN REWRITE_TAC[BOUNDED_INSERT] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_IMP_BOUNDED THEN MATCH_MP_TAC FINITE_IMAGE THEN
    REWRITE_TAC[GSYM numseg; FINITE_NUMSEG];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `abs(det
       ((lambda i. ((lambda i j. if j <= i then &1 else &0):real^N^N)
                   $inverse p i)
        :real^N^N))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[CART_EQ] THEN
      ASM_SIMP_TAC[matrix; LAMBDA_BETA; BASIS_COMPONENT; COND_COMPONENT;
                   LAMBDA_BETA_PERM; PERMUTES_INVERSE] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum (1..inverse (p:num->num) i)
                      (\k. if k = j then &1 else &0)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN
        ASM_SIMP_TAC[IN_NUMSEG; PERMUTES_IN_IMAGE; basis] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC LAMBDA_BETA THEN
        ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; LE_TRANS;
                      PERMUTES_INVERSE];
        ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PERMUTES_INVERSE; DET_PERMUTE_ROWS; ETA_AX] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_SIGN; REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `x = &1 ==> abs x = &1`) THEN
    ASM_SIMP_TAC[DET_LOWERTRIANGULAR; GSYM NOT_LT; LAMBDA_BETA] THEN
    REWRITE_TAC[LT_REFL; PRODUCT_CONST_NUMSEG; REAL_POW_ONE]]);;

let HAS_MEASURE_STD_SIMPLEX = prove
 (`(convex hull (vec 0:real^N INSERT {basis i | 1 <= i /\ i <= dimindex(:N)}))
   has_measure inv(&(FACT(dimindex(:N))))`,
  let lemma = prove
   (`!f:num->real. (!i. 1 <= i /\ i < n ==> f i <= f(i + 1)) <=>
                   (!i j. 1 <= i /\ i <= j /\ j <= n ==> f i <= f j)`,
    GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THEN
      SIMP_TAC[LE; REAL_LE_REFL] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) j` THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC x <= y ==> x <= y`] THEN
      REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]) in
  MP_TAC(ISPECL
   [`\p. {x:real^N | &0 <= x$(p 1) /\ x$(p(dimindex(:N))) <= &1 /\
                     (!i. 1 <= i /\ i < dimindex(:N)
                          ==> x$(p i) <= x$(p(i + 1)))}`;
    `{p | p permutes 1..dimindex(:N)}`]
    HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE) THEN
  ASM_SIMP_TAC[REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
                            HAS_MEASURE_IMAGE_STD_SIMPLEX; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_PERMUTATIONS; FINITE_NUMSEG;
               CARD_PERMUTATIONS; CARD_NUMSEG_1] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:num->num`; `q:num->num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?i. i IN 1..dimindex(:N) /\ ~(p i:num = q i)` MP_TAC THENL
     [ASM_MESON_TAC[permutes; FUN_EQ_THM]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC[TAUT `a ==> ~(b /\ ~c) <=> a /\ b ==> c`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x:real^N | (basis(p(k:num)) - basis(q k)) dot x = &0}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC BASIS_NE THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; DOT_LSUB; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[DOT_BASIS; GSYM IN_NUMSEG; PERMUTES_IN_IMAGE] THEN
    SUBGOAL_THEN `?l. (q:num->num) l = p(k:num)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[permutes]; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= l /\ l <= dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
    SUBGOAL_THEN `k:num < l` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN REWRITE_TAC[LE_LT] THEN
      ASM_MESON_TAC[PERMUTES_INJECTIVE; IN_NUMSEG];
      ALL_TAC] THEN
    SUBGOAL_THEN `?m. (p:num->num) m = q(k:num)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[permutes]; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= m /\ m <= dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
    SUBGOAL_THEN `k:num < m` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN REWRITE_TAC[LE_LT] THEN
      ASM_MESON_TAC[PERMUTES_INJECTIVE; IN_NUMSEG];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[lemma] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `l:num`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `m:num`]) THEN
    ASM_SIMP_TAC[LT_IMP_LE; IMP_IMP; REAL_LE_ANTISYM; REAL_SUB_0] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; DOT_BASIS];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN REWRITE_TAC[BOUNDED_INSERT] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_IMP_BOUNDED THEN MATCH_MP_TAC FINITE_IMAGE THEN
    REWRITE_TAC[GSYM numseg; FINITE_NUMSEG];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(y = &0) ==> (x = inv y <=> y * x = &1)`;
               REAL_OF_NUM_EQ; FACT_NZ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `measure(interval[vec 0:real^N,vec 1])` THEN CONJ_TAC THENL
   [AP_TERM_TAC; REWRITE_TAC[MEASURE_INTERVAL; CONTENT_UNIT]] THEN
  REWRITE_TAC[lemma] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; FORALL_IN_IMAGE; IMP_CONJ;
                RIGHT_FORALL_IMP_THM; IN_ELIM_THM] THEN
    SIMP_TAC[IMP_IMP; IN_INTERVAL; LAMBDA_BETA; VEC_COMPONENT] THEN
    X_GEN_TAC `p:num->num` THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN X_GEN_TAC `i:num` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `(x:real^N)$(p 1)`;
      EXISTS_TAC `(x:real^N)$(p(dimindex(:N)))`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP PERMUTES_SURJECTIVE) THEN
    ASM_MESON_TAC[LE_REFL; PERMUTES_IN_IMAGE; IN_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `s SUBSET UNIONS(IMAGE f t) <=>
                        !x. x IN s ==> ?y. y IN t /\ x IN f y`] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTERVAL; IN_ELIM_THM] THEN
  SIMP_TAC[VEC_COMPONENT] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\i j. ~((x:real^N)$j <= x$i)` TOPOLOGICAL_SORT) THEN
  REWRITE_TAC[REAL_NOT_LE; REAL_NOT_LT] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`dimindex(:N)`; `1..dimindex(:N)`]) THEN
  REWRITE_TAC[HAS_SIZE_NUMSEG_1; EXTENSION; IN_IMAGE; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` (CONJUNCTS_THEN2
   (ASSUME_TAC o GSYM) ASSUME_TAC)) THEN
  EXISTS_TAC `\i. if i IN 1..dimindex(:N) then f(i) else i` THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ARITH_RULE
    `1 <= i /\ i <= j /\ j <= n <=>
     1 <= i /\ 1 <= j /\ i <= n /\ j <= n /\ i <= j`] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_REFL; DIMINDEX_GE_1] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[LE_REFL; DIMINDEX_GE_1; LE_LT; REAL_LE_LT]] THEN
  SIMP_TAC[PERMUTES_FINITE_SURJECTIVE; FINITE_NUMSEG] THEN
  SIMP_TAC[IN_NUMSEG] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence the measure of a general simplex.                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_SIMPLEX_0 = prove
 (`!l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> (convex hull (vec 0 INSERT set_of_list l)) has_measure
            abs(det(vector l)) / &(FACT(dimindex(:N)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vec 0 INSERT (set_of_list l) =
        IMAGE (\x:real^N. transp(vector l:real^N^N) ** x)
              (vec 0 INSERT {basis i:real^N | 1 <= i /\ i <= dimindex(:N)})`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[IMAGE_CLAUSES; GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN AP_TERM_TAC THEN
    SIMP_TAC[matrix_vector_mul; vector; transp; LAMBDA_BETA; basis] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[REAL_MUL_RZERO; SUM_DELTA] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(b /\ c ==> ~a)`] THEN
    X_GEN_TAC `y:real^N` THEN SIMP_TAC[LAMBDA_BETA; REAL_MUL_RID] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
    REWRITE_TAC[NOT_IMP; REAL_MUL_RID; GSYM CART_EQ] THEN
    ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL] THEN
    EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `SUC i`; EXISTS_TAC `i - 1`] THEN
    ASM_REWRITE_TAC[SUC_SUB1] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE; MATRIX_VECTOR_MUL_LINEAR] THEN
  SUBGOAL_THEN
   `det(vector l:real^N^N) = det(matrix(\x:real^N. transp(vector l) ** x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; DET_TRANSP]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  ASM_SIMP_TAC[GSYM(REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
                 HAS_MEASURE_STD_SIMPLEX)] THEN
  MATCH_MP_TAC HAS_MEASURE_LINEAR_IMAGE THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
  MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN REWRITE_TAC[BOUNDED_INSERT] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  MATCH_MP_TAC FINITE_IMP_BOUNDED THEN MATCH_MP_TAC FINITE_IMAGE THEN
  REWRITE_TAC[GSYM numseg; FINITE_NUMSEG]);;

let HAS_MEASURE_SIMPLEX = prove
 (`!a l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> (convex hull (set_of_list(CONS a l))) has_measure
            abs(det(vector(MAP (\x. x - a) l))) / &(FACT(dimindex(:N)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `MAP (\x:real^N. x - a) l` HAS_MEASURE_SIMPLEX_0) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; set_of_list] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N` o MATCH_MP HAS_MEASURE_TRANSLATION) THEN
  REWRITE_TAC[GSYM CONVEX_HULL_TRANSLATION] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[IMAGE_CLAUSES; VECTOR_ADD_RID; SET_OF_LIST_MAP] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `a + x - a:real^N = x`;
              SET_RULE `IMAGE (\x. x) s = s`]);;

let MEASURABLE_CONVEX_HULL = prove
 (`!s. bounded s ==> measurable(convex hull s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_CONVEX THEN
  ASM_SIMP_TAC[CONVEX_CONVEX_HULL; BOUNDED_CONVEX_HULL]);;

let MEASURABLE_SIMPLEX = prove
 (`!l. measurable(convex hull (set_of_list l))`,
  GEN_TAC THEN MATCH_MP_TAC MEASURABLE_CONVEX_HULL THEN
  MATCH_MP_TAC FINITE_IMP_BOUNDED THEN REWRITE_TAC[FINITE_SET_OF_LIST]);;

let MEASURE_SIMPLEX = prove
 (`!a l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> measure(convex hull (set_of_list(CONS a l))) =
            abs(det(vector(MAP (\x. x - a) l))) / &(FACT(dimindex(:N)))`,
  MESON_TAC[HAS_MEASURE_SIMPLEX; HAS_MEASURE_MEASURABLE_MEASURE]);;

(* ------------------------------------------------------------------------- *)
(* Area of a triangle.                                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_TRIANGLE = prove
 (`!a b c:real^2.
        convex hull {a,b,c} has_measure
        abs((b$1 - a$1) * (c$2 - a$2) - (b$2 - a$2) * (c$1 - a$1)) / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `[b;c]:(real^2)list`] HAS_MEASURE_SIMPLEX) THEN
  REWRITE_TAC[LENGTH; DIMINDEX_2; ARITH; set_of_list; MAP] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DET_2; VECTOR_2] THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_2; ARITH]);;

let MEASURABLE_TRIANGLE = prove
 (`!a b c:real^N. measurable(convex hull {a,b,c})`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_BOUNDED THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES]);;

let MEASURE_TRIANGLE = prove
 (`!a b c:real^2.
        measure(convex hull {a,b,c}) =
        abs((b$1 - a$1) * (c$2 - a$2) - (b$2 - a$2) * (c$1 - a$1)) / &2`,
  REWRITE_TAC[REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
               HAS_MEASURE_TRIANGLE]);;

(* ------------------------------------------------------------------------- *)
(* Volume of a tetrahedron.                                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_TETRAHEDRON = prove
 (`!a b c d:real^3.
        convex hull {a,b,c,d} has_measure
        abs((b$1 - a$1) * (c$2 - a$2) * (d$3 - a$3) +
            (b$2 - a$2) * (c$3 - a$3) * (d$1 - a$1) +
            (b$3 - a$3) * (c$1 - a$1) * (d$2 - a$2) -
            (b$1 - a$1) * (c$3 - a$3) * (d$2 - a$2) -
            (b$2 - a$2) * (c$1 - a$1) * (d$3 - a$3) -
            (b$3 - a$3) * (c$2 - a$2) * (d$1 - a$1)) /
           &6`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `[b;c;d]:(real^3)list`] HAS_MEASURE_SIMPLEX) THEN
  REWRITE_TAC[LENGTH; DIMINDEX_3; ARITH; set_of_list; MAP] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DET_3; VECTOR_3] THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_3; ARITH]);;

let MEASURABLE_TETRAHEDRON = prove
 (`!a b c d:real^N. measurable(convex hull {a,b,c,d})`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_BOUNDED THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES]);;

let MEASURE_TETRAHEDRON = prove
 (`!a b c d:real^3.
        measure(convex hull {a,b,c,d}) =
        abs((b$1 - a$1) * (c$2 - a$2) * (d$3 - a$3) +
            (b$2 - a$2) * (c$3 - a$3) * (d$1 - a$1) +
            (b$3 - a$3) * (c$1 - a$1) * (d$2 - a$2) -
            (b$1 - a$1) * (c$3 - a$3) * (d$2 - a$2) -
            (b$2 - a$2) * (c$1 - a$1) * (d$3 - a$3) -
            (b$3 - a$3) * (c$2 - a$2) * (d$1 - a$1)) / &6`,
  REWRITE_TAC[REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
               HAS_MEASURE_TETRAHEDRON]);;

(* ------------------------------------------------------------------------- *)
(* Steinhaus's theorem. (Stromberg's proof as given on Wikipedia.)           *)
(* ------------------------------------------------------------------------- *)

let STEINHAUS = prove
 (`!s:real^N->bool.
        measurable s /\ &0 < measure s
        ==> ?d. &0 < d /\ ball(vec 0,d) SUBSET {x - y | x IN s /\ y IN s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `measure(s:real^N->bool) / &3`]
    MEASURABLE_INNER_COMPACT) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `measure(s:real^N->bool) / &3`]
    MEASURABLE_OUTER_OPEN) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < x / &3 <=> &0 < x`] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(:real^N) DIFF u`]
    SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_BALL_0; IN_ELIM_THM] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((IMAGE (\x:real^N. v + x) k) INTER k = {})` MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`IMAGE (\x:real^N. v + x) k`; `k:real^N->bool`]
        MEASURE_UNION) THEN
    ASM_REWRITE_TAC[MEASURABLE_TRANSLATION_EQ; MEASURE_EMPTY] THEN
    REWRITE_TAC[MEASURE_TRANSLATION; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!s:real^N->bool u:real^N->bool.
        measure u < measure s + measure s / &3 /\
        measure s < measure k + measure s / &3 /\
        measure x <= measure u
        ==> ~(measure x = measure k + measure k)`) THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `u:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_TRANSLATION_EQ; MEASURABLE_UNION] THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `v + x:real^N`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; NORM_ARITH
     `d <= dist(x:real^N,v + x) <=> ~(norm v < d)`];
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    REWRITE_TAC[VECTOR_ARITH `v:real^N = x - y <=> x = v + y`] THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A measurable set with cardinality less than c is negligible.              *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_NONNEGLIGIBLE_IMP_LARGE = prove
 (`!s:real^N->bool. measurable s /\ &0 < measure s ==> s =_c (:real)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `FINITE(s:real^N->bool)` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_FINITE; MEASURABLE_MEASURE_POS_LT];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP STEINHAUS) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
    REWRITE_TAC[CARD_LE_UNIV] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    REWRITE_TAC[CARD_EQ_EUCLIDEAN];
    ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN CONJ_TAC THENL
   [MESON_TAC[CARD_EQ_EUCLIDEAN; CARD_EQ_SYM; CARD_EQ_IMP_LE]; ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `interval(vec 0:real^N,vec 1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
    MATCH_MP_TAC HOMEOMORPHIC_IMP_CARD_EQ THEN
    MATCH_MP_TAC HOMEOMORPHIC_OPEN_INTERVAL_UNIV THEN
    REWRITE_TAC[UNIT_INTERVAL_NONEMPTY];
    ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `interval[vec 0:real^N,vec 1]` THEN
  SIMP_TAC[INTERVAL_OPEN_SUBSET_CLOSED; CARD_LE_SUBSET] THEN
  TRANS_TAC CARD_LE_TRANS `cball(vec 0:real^N,d / &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    MATCH_MP_TAC HOMEOMORPHIC_IMP_CARD_EQ THEN
    MATCH_MP_TAC HOMEOMORPHIC_CONVEX_COMPACT THEN
    REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL; INTERIOR_CLOSED_INTERVAL;
                CONVEX_CBALL; COMPACT_CBALL; UNIT_INTERVAL_NONEMPTY;
                INTERIOR_CBALL; BALL_EQ_EMPTY] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `ball(vec 0:real^N,d)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_LE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `IMAGE (\(x:real^N,y). x - y) (s *_c s)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[mul_c; CARD_LE_SUBSET; SET_RULE
     `IMAGE f {g x y | P x /\ Q y} = {f(g x y) | P x /\ Q y}`];
    ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `((s:real^N->bool) *_c s)` THEN
  REWRITE_TAC[CARD_LE_IMAGE] THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN MATCH_MP_TAC CARD_SQUARE_INFINITE THEN
  ASM_REWRITE_TAC[INFINITE]);;

let MEASURABLE_SMALL_IMP_NEGLIGIBLE = prove
 (`!s:real^N->bool. measurable s /\ s <_c (:real) ==> negligible s`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `a /\ b ==> c <=> a ==> ~c ==> ~b`] THEN
  SIMP_TAC[GSYM MEASURABLE_MEASURE_POS_LT] THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_NONNEGLIGIBLE_IMP_LARGE) THEN
  REWRITE_TAC[lt_c] THEN MESON_TAC[CARD_EQ_IMP_LE; CARD_EQ_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Austin's Lemma.                                                           *)
(* ------------------------------------------------------------------------- *)

let AUSTIN_LEMMA = prove
 (`!D. FINITE D /\
       (!d. d IN D
            ==> ?k a b. d = interval[a:real^N,b] /\
                        (!i. 1 <= i /\ i <= dimindex(:N) ==> b$i - a$i = k))
       ==> ?D'. D' SUBSET D /\ pairwise DISJOINT D' /\
                measure(UNIONS D') >=
                measure(UNIONS D) / &3 pow (dimindex(:N))`,
  GEN_TAC THEN WF_INDUCT_TAC `CARD(D:(real^N->bool)->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
  ASM_CASES_TAC `D:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[SUBSET_EMPTY; UNWIND_THM2; PAIRWISE_EMPTY] THEN
    REWRITE_TAC[UNIONS_0; real_ge; MEASURE_EMPTY; NOT_IN_EMPTY] THEN
    REWRITE_TAC[REAL_ARITH `&0 / x = &0`; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d:real^N->bool. d IN D /\ !d'. d' IN D ==> measure d' <= measure d`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE measure (D:(real^N->bool)->bool)` SUP_FINITE) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `{c:real^N->bool | c IN (D DELETE d) /\ c INTER d = {}}`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC CARD_PSUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_DELETE; FINITE_RESTRICT; IN_ELIM_THM; real_ge] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(d:real^N->bool) INSERT D'` THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
    REWRITE_TAC[pairwise; IN_INSERT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a3 b3:real^N.
        measure(interval[a3,b3]) = &3 pow dimindex(:N) * measure d /\
        !c. c IN D /\ ~(c INTER d = {}) ==> c SUBSET interval[a3,b3]`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "*" (MP_TAC o SPEC `d:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:real`; `a:real^N`; `b:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    EXISTS_TAC `inv(&2) % (a + b) - &3 / &2 % (b - a):real^N` THEN
    EXISTS_TAC `inv(&2) % (a + b) + &3 / &2 % (b - a):real^N` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[REAL_ARITH `(x + &3 / &2 * a) - (x - &3 / &2 * a) = &3 * a`;
                  REAL_ARITH `x - a <= x + a <=> &0 <= a`] THEN
      ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= &3 / &2 * x - &0 <=> &0 <= x`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
      SIMP_TAC[PRODUCT_CONST; FINITE_NUMSEG; CARD_NUMSEG_1; REAL_POW_MUL];
      X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `c:real^N->bool`) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`k':real`; `a':real^N`; `b':real^N`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o
        GEN_REWRITE_RULE RAND_CONV [DISJOINT_INTERVAL]) THEN
      REWRITE_TAC[NOT_EXISTS_THM; SUBSET_INTERVAL] THEN
      REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
      ASM_CASES_TAC `1 <= i` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `interval[a':real^N,b']`) THEN
      ASM_REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
      REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LT] THEN
      REWRITE_TAC[REAL_ARITH `a$k <= b$k <=> &0 <= b$k - a$k`] THEN
      ASM_SIMP_TAC[IN_NUMSEG] THEN
      ASM_CASES_TAC `&0 <= k` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `&0 <= k'` THEN ASM_REWRITE_TAC[] THEN
      REPEAT(FIRST_X_ASSUM(fun th ->
        SIMP_TAC[th] THEN MP_TAC(ISPEC `i:num` th))) THEN
      ASM_SIMP_TAC[PRODUCT_CONST; CARD_NUMSEG_1; FINITE_NUMSEG] THEN
      DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
       (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`]
        REAL_POW_LE2_REV)) THEN
      ASM_SIMP_TAC[DIMINDEX_GE_1; LE_1] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_INSERT] THEN
  SUBGOAL_THEN `!d:real^N->bool. d IN D ==> measurable d` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEASURABLE_INTERVAL]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_DISJOINT_UNION o
    rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC MEASURABLE_UNIONS THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      FINITE_SUBSET)) THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_DELETE];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(interval[a3:real^N,b3]) +
              measure(UNIONS D DIFF interval[a3,b3])` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) MEASURE_DISJOINT_UNION o
      rand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MEASURABLE_UNIONS; MEASURABLE_DIFF;
                   MEASURABLE_INTERVAL] THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[MEASURABLE_UNIONS];
        ASM_MESON_TAC[MEASURABLE_UNIONS; MEASURABLE_DIFF;
                     MEASURABLE_INTERVAL; MEASURABLE_UNION];
        SET_TAC[]]];
    ASM_REWRITE_TAC[REAL_ARITH `a * x + y <= (x + z) * a <=> y <= z * a`] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `y <= a ==> x <= y ==> x <= a`)) THEN
    SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_UNIONS; MEASURABLE_INTERVAL;
                 IN_ELIM_THM; IN_DELETE; FINITE_DELETE; FINITE_RESTRICT] THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Some differentiability-like properties of the indefinite integral.        *)
(* The first two proofs are minor variants of each other, but it was more    *)
(* work to derive one from the other.                                        *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_CCONTINUOUS_EXPLICIT = prove
 (`!f:real^M->real^N.
    (!a b. f integrable_on interval[a,b])
    ==> ?k. negligible k /\
         !x e. ~(x IN k) /\ &0 < e
               ==> ?d. &0 < d /\
                       !h. &0 < h /\ h < d
                           ==> norm(inv(content(interval[x,x + h % vec 1])) %
                                    integral (interval[x,x + h % vec 1]) f -
                                    f(x)) < e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_UNIV] THEN
  MAP_EVERY ABBREV_TAC
   [`box = \h x. interval[x:real^M,x + h % vec 1]`;
    `box2 = \h x. interval[x:real^M - h % vec 1,x + h % vec 1]`;
    `i = \h:real x:real^M. inv(content(box h x)) %
                      integral (box h x) (f:real^M->real^N)`] THEN
  SUBGOAL_THEN
   `?k. negligible k /\
        !x e. ~(x IN k) /\ &0 < e
              ==> ?d. &0 < d /\
                      !h. &0 < h /\ h < d
                          ==> norm(i h x - (f:real^M->real^N) x) < e`
  MP_TAC THENL
   [ALL_TAC; MAP_EVERY EXPAND_TAC ["i"; "box"] THEN REWRITE_TAC[]] THEN
  EXISTS_TAC
   `{x | ~(!e. &0 < e
              ==> ?d. &0 < d /\
                      !h. &0 < h /\ h < d
                          ==> norm(i h x - (f:real^M->real^N) x) < e)}` THEN
  SIMP_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC
   `UNIONS {{x | !d. &0 < d
                     ==> ?h. &0 < h /\ h < d /\
                             inv(&k + &1) <= dist(i h x,(f:real^M->real^N) x)}
            |  k IN (:num)}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:real^M`; `e:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[dist] THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&k)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC] THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
  X_GEN_TAC `jj:num` THEN
  SUBGOAL_THEN `&0 < inv(&jj + &1)` MP_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    SPEC_TAC(`inv(&jj + &1)`,`mu:real`) THEN GEN_TAC THEN DISCH_TAC] THEN
  ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  ASM_CASES_TAC `negligible(interval[a:real^M,b])` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_SUBSET; INTER_SUBSET]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NEGLIGIBLE_INTERVAL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
  REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `a - vec 1:real^M`; `b + vec 1:real^M`]
    HENSTOCK_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_ON_SUBINTERVAL; SUBSET_UNIV]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(e * mu) / &2 / &6 pow (dimindex(:M))`) THEN
  ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; REAL_LT_MUL;
               REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE `{x | P x} INTER s = {x | x IN s /\ P x}`] THEN
  ABBREV_TAC
    `E = {x | x IN interval[a,b] /\
              !d. &0 < d
                   ==> ?h. &0 < h /\ h < d /\
                           mu <= dist(i h x,(f:real^M->real^N) x)}` THEN
  SUBGOAL_THEN
   `!x. x IN E
        ==> ?h. &0 < h /\
                (box h x:real^M->bool) SUBSET (g x) /\
                (box h x:real^M->bool) SUBSET interval[a - vec 1,b + vec 1] /\
                mu <= dist(i h x,(f:real^M->real^N) x)`
  MP_TAC THENL
   [X_GEN_TAC `x:real^M` THEN EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [gauge]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o SPEC `x:real^M`) THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC `min (&1) (d / &(dimindex(:M)))`)) THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_LT_01; GSYM CONJ_ASSOC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; DIMINDEX_GE_1; LE_1; REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(x:real^M,d)` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "box" THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL; IN_BALL] THEN
      X_GEN_TAC `y:real^M` THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:M)) (\i. abs((x - y:real^M)$i))` THEN
      REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_BOUND_LT_GEN THEN
      REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; IN_NUMSEG] THEN
      SIMP_TAC[NOT_LT; DIMINDEX_GE_1; CARD_NUMSEG_1; VECTOR_SUB_COMPONENT] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(x:real^M) IN interval[a,b]` THEN
      EXPAND_TAC "box" THEN REWRITE_TAC[SUBSET; IN_INTERVAL] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `y:real^M` THEN MP_TAC th) THEN
      REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      X_GEN_TAC `i:num` THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `uv:real^M->real` THEN
  REWRITE_TAC[TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^M`; `b:real^M`; `E:real^M->bool`;
                 `\x:real^M. if x IN E then ball(x,uv x) else g(x)`]
   COVERING_LEMMA) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTERVAL_NE_EMPTY] THEN CONJ_TAC THENL
     [EXPAND_TAC "E" THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[gauge] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gauge]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `D:(real^M->bool)->bool`) THEN
  EXISTS_TAC `UNIONS D:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `measurable(UNIONS D:real^M->bool) /\
    measure(UNIONS D) <= measure(interval[a:real^M,b])`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    REWRITE_TAC[MEASURABLE_INTERVAL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC MEASURABLE_UNIONS THEN
    ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `?d. d SUBSET D /\ FINITE d /\
        measure(UNIONS D:real^M->bool) <= &2 * measure(UNIONS d)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `measure(UNIONS D:real^M->bool) = &0` THENL
     [EXISTS_TAC `{}:(real^M->bool)->bool` THEN
      ASM_REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET; MEASURE_EMPTY; UNIONS_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      MP_TAC(ISPECL [`D:(real^M->bool)->bool`; `measure(interval[a:real^M,b])`;
                     `measure(UNIONS D:real^M->bool) / &2`]
                MEASURE_COUNTABLE_UNIONS_APPROACHABLE) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[MEASURABLE_MEASURE_POS_LT; REAL_HALF] THEN
        ASM_SIMP_TAC[GSYM MEASURABLE_MEASURE_EQ_0] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[MEASURABLE_INTERVAL]; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
        REPEAT(CONJ_TAC THENL
          [ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL; MEASURABLE_UNIONS];
           ALL_TAC]) THEN
        ASM SET_TAC[];
        MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o el 3 o CONJUNCTS) THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
  SIMP_TAC[IN_INTER] THEN REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_TAC `tag:(real^M->bool)->real^M`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `D <= &2 * d ==> d <= e / &2 ==> D <= e`)) THEN
  MP_TAC(ISPEC
   `IMAGE (\k:real^M->bool. (box2:real->real^M->real^M->bool)
                            (uv(tag k):real) ((tag k:real^M))) d`
   AUSTIN_LEMMA) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN EXPAND_TAC "box2" THEN
    EXISTS_TAC `&2 * uv((tag:(real^M->bool)->real^M) k):real` THEN
    EXISTS_TAC `(tag:(real^M->bool)->real^M) k - uv(tag k) % vec 1:real^M` THEN
    EXISTS_TAC `(tag:(real^M->bool)->real^M) k + uv(tag k) % vec 1:real^M` THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_SUBSET_IMAGE; real_ge] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^M->bool)->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REAL_ARITH
   `d <= d' /\ p <= e ==> d' <= p ==> d <= e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL];
      MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      EXPAND_TAC "box2" THEN REWRITE_TAC[MEASURABLE_INTERVAL];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `z:real^M` THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^M) IN k` THEN SPEC_TAC(`z:real^M`,`z:real^M`) THEN
      REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(tag k:real^M,uv(tag(k:real^M->bool)))` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      EXPAND_TAC "box2" THEN REWRITE_TAC[SUBSET; IN_BALL; IN_INTERVAL] THEN
      X_GEN_TAC `z:real^M` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN

      SIMP_TAC[REAL_ARITH `x - h <= y /\ y <= x + h <=> abs(x - y) <= h`] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
      ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LT_IMP_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(UNIONS (IMAGE (\k:real^M->bool.
                            (box:real->real^M->real^M->bool)
                            (uv(tag k):real) ((tag k:real^M))) p)) *
              &6 pow dimindex (:M)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `!box. IMAGE (\k:real^M->bool. (box:real->real^M->real^M->bool)
                                    (uv(tag k):real) ((tag k:real^M))) p =
             IMAGE (\t. box (uv t) t) (IMAGE tag p)`
     (fun th -> REWRITE_TAC[th])
    THENL [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) MEASURE_NEGLIGIBLE_UNIONS_IMAGE o
        lhand o rand o snd) THEN
    W(MP_TAC o PART_MATCH (lhs o rand) MEASURE_NEGLIGIBLE_UNIONS_IMAGE o
        lhand o lhand o rand o snd) THEN
    MATCH_MP_TAC(TAUT
     `fp /\ (mb /\ mb') /\ (db /\ db') /\ (m1 /\ m2 ==> p)
      ==> (fp /\ mb /\ db ==> m1) ==> (fp /\ mb' /\ db' ==> m2) ==> p`) THEN
    SUBGOAL_THEN `FINITE(p:(real^M->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ASM_SIMP_TAC[FINITE_IMAGE]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["box"; "box2"] THEN
      REWRITE_TAC[MEASURABLE_INTERVAL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; AND_FORALL_THM] THEN
      MAP_EVERY X_GEN_TAC [`k1:real^M->bool`; `k2:real^M->bool`] THEN
      MATCH_MP_TAC(TAUT
        `(q ==> r) /\ (p ==> q) ==> (p ==> q) /\ (p ==> r)`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
        MATCH_MP_TAC(SET_RULE
        `s SUBSET s' /\ t SUBSET t' ==> (s INTER t) SUBSET (s' INTER t')`) THEN
        CONJ_TAC THEN MAP_EVERY EXPAND_TAC ["box"; "box2"] THEN
        REWRITE_TAC[SUBSET_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY] `s = {} ==> negligible s`) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `k1:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `k2:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [EXPAND_TAC "box2" THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
        REWRITE_TAC[SUBSET_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        REWRITE_TAC[REAL_ARITH `x - e <= x + e <=> &0 <= e`] THEN
        SUBGOAL_THEN `&0 <= uv((tag:(real^M->bool)->real^M) k1) /\
                      &0 <= uv((tag:(real^M->bool)->real^M) k2)`
        STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[SUBSET; REAL_LT_IMP_LE]; ASM_REWRITE_TAC[]] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
        MATCH_MP_TAC MONO_NOT THEN REWRITE_TAC[AND_FORALL_THM] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `t:real^M` THEN DISCH_THEN(K ALL_TAC) THEN
    SUBST1_TAC(REAL_ARITH `&6 = &2 * &3`) THEN
    REWRITE_TAC[REAL_POW_MUL; REAL_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY EXPAND_TAC ["box"; "box2"] THEN
    REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH `a <= a + x <=> &0 <= x`;
                REAL_ARITH `a - x <= a + x <=> &0 <= x`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    REWRITE_TAC[REAL_ARITH `(t + h) - (t - h):real = &2 * h`;
                REAL_ARITH `(t + h) - t:real = h`] THEN
    REWRITE_TAC[PRODUCT_MUL_NUMSEG; PRODUCT_CONST_NUMSEG] THEN
    REWRITE_TAC[ADD_SUB; REAL_MUL_AC];
    ALL_TAC] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  SUBGOAL_THEN `FINITE(p:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
  EXISTS_TAC `mu:real` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `IMAGE (\k. (tag:(real^M->bool)->real^M) k,
                (box(uv(tag k):real) (tag k):real^M->bool)) p`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[tagged_partial_division_of; fine] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN
    REWRITE_TAC[MESON[]
     `(!x j. (?k. (x = tag k /\ j = g k) /\ k IN d) ==> P x j) <=>
      (!k. k IN d ==> P (tag k) (g k))`] THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "box" THEN REWRITE_TAC[IN_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `&0 < u ==> x <= x /\ x <= x + u`) THEN ASM_MESON_TAC[SUBSET];
        ASM_MESON_TAC[SUBSET];
        EXPAND_TAC "box" THEN MESON_TAC[]];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k1:real^M->bool` THEN
      ASM_CASES_TAC `(k1:real^M->bool) IN p` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k2:real^M->bool` THEN
      ASM_CASES_TAC `(k2:real^M->bool) IN p` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(tag:(real^M->bool)->real^M) k1 = tag k2` THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [EXPAND_TAC "box2" THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
        REWRITE_TAC[SUBSET_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        REWRITE_TAC[REAL_ARITH `x - e <= x + e <=> &0 <= e`] THEN
        SUBGOAL_THEN `&0 <= uv((tag:(real^M->bool)->real^M) k1) /\
                      &0 <= uv((tag:(real^M->bool)->real^M) k2)`
        STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[SUBSET; REAL_LT_IMP_LE]; ASM_REWRITE_TAC[]] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
        MATCH_MP_TAC MONO_NOT THEN REWRITE_TAC[AND_FORALL_THM] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(SET_RULE
         `i1 SUBSET s1 /\ i2 SUBSET s2
          ==> DISJOINT s1 s2 ==> i1 INTER i2 = {}`) THEN
        CONJ_TAC THEN MATCH_MP_TAC(MESON[INTERIOR_SUBSET; SUBSET_TRANS]
         `s SUBSET t ==> interior s SUBSET t`) THEN
        MAP_EVERY EXPAND_TAC ["box"; "box2"] THEN
        REWRITE_TAC[SUBSET_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `e = e' /\ y <= x ==> x < e ==> y <= e'`) THEN
  CONJ_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    EXPAND_TAC "box" THEN REWRITE_TAC[MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a' <= e ==> a <= a' ==> a <= e`) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_LE_INCLUDED THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; RIGHT_EXISTS_AND_THM; FINITE_IMAGE] THEN
  REWRITE_TAC[NORM_POS_LE; EXISTS_IN_IMAGE] THEN
  EXISTS_TAC `SND:real^M#(real^M->bool)->real^M->bool` THEN
  X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&0 < uv(tag(k:real^M->bool):real^M):real` ASSUME_TAC
  THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < measure(box(uv(tag(k:real^M->bool):real^M):real) (tag k):real^M->bool)`
  MP_TAC THENL
   [EXPAND_TAC "box" THEN
    REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> a <= a + x`] THEN
    MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN
    REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  DISCH_THEN(fun th ->
   GEN_REWRITE_TAC (funpow 2 RAND_CONV)
    [MATCH_MP(REAL_ARITH `&0 < x ==> x = abs x`) th] THEN
   ASSUME_TAC th) THEN
  REWRITE_TAC[real_div; GSYM REAL_ABS_INV] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM NORM_MUL] THEN
  SUBGOAL_THEN
   `mu <= dist(i (uv(tag(k:real^M->bool):real^M):real) (tag k):real^N,
               f(tag k))`
  MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> m <= x ==> m <= y`) THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN EXPAND_TAC "i" THEN
  REWRITE_TAC[dist; VECTOR_SUB_LDISTRIB] THEN
  UNDISCH_TAC
    `&0 < measure(box(uv(tag(k:real^M->bool):real^M):real)
                (tag k):real^M->bool)` THEN
  EXPAND_TAC "box" THEN REWRITE_TAC[MEASURE_INTERVAL] THEN
  SIMP_TAC[VECTOR_MUL_ASSOC; REAL_LT_IMP_NZ; REAL_MUL_LINV] THEN
  REWRITE_TAC[VECTOR_MUL_LID]);;

let INTEGRABLE_CCONTINUOUS_EXPLICIT_SYMMETRIC = prove
 (`!f:real^M->real^N.
    (!a b. f integrable_on interval[a,b])
    ==> ?k. negligible k /\
         !x e. ~(x IN k) /\ &0 < e
               ==> ?d. &0 < d /\
                       !h. &0 < h /\ h < d
                ==> norm(inv(content(interval[x - h % vec 1,x + h % vec 1])) %
                    integral (interval[x - h % vec 1,x + h % vec 1]) f -
                    f(x)) < e`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`box = \h x. interval[x - h % vec 1:real^M,x + h % vec 1]`;
    `i = \h:real x:real^M. inv(content(box h x)) %
                      integral (box h x) (f:real^M->real^N)`] THEN
  SUBGOAL_THEN
   `?k. negligible k /\
        !x e. ~(x IN k) /\ &0 < e
              ==> ?d. &0 < d /\
                      !h. &0 < h /\ h < d
                          ==> norm(i h x - (f:real^M->real^N) x) < e`
  MP_TAC THENL
   [ALL_TAC; MAP_EVERY EXPAND_TAC ["i"; "box"] THEN REWRITE_TAC[]] THEN
  EXISTS_TAC
   `{x | ~(!e. &0 < e
              ==> ?d. &0 < d /\
                      !h. &0 < h /\ h < d
                          ==> norm(i h x - (f:real^M->real^N) x) < e)}` THEN
  SIMP_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC
   `UNIONS {{x | !d. &0 < d
                     ==> ?h. &0 < h /\ h < d /\
                             inv(&k + &1) <= dist(i h x,(f:real^M->real^N) x)}
            |  k IN (:num)}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:real^M`; `e:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[dist] THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&k)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC] THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
  X_GEN_TAC `jj:num` THEN
  SUBGOAL_THEN `&0 < inv(&jj + &1)` MP_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    SPEC_TAC(`inv(&jj + &1)`,`mu:real`) THEN GEN_TAC THEN DISCH_TAC] THEN
  ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  ASM_CASES_TAC `negligible(interval[a:real^M,b])` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_SUBSET; INTER_SUBSET]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NEGLIGIBLE_INTERVAL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
  REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `a - vec 1:real^M`; `b + vec 1:real^M`]
    HENSTOCK_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_ON_SUBINTERVAL; SUBSET_UNIV]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(e * mu) / &2 / &3 pow (dimindex(:M))`) THEN
  ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; REAL_LT_MUL;
               REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE `{x | P x} INTER s = {x | x IN s /\ P x}`] THEN
  ABBREV_TAC
    `E = {x | x IN interval[a,b] /\
              !d. &0 < d
                   ==> ?h. &0 < h /\ h < d /\
                           mu <= dist(i h x,(f:real^M->real^N) x)}` THEN
  SUBGOAL_THEN
   `!x. x IN E
        ==> ?h. &0 < h /\
                (box h x:real^M->bool) SUBSET (g x) /\
                (box h x:real^M->bool) SUBSET interval[a - vec 1,b + vec 1] /\
                mu <= dist(i h x,(f:real^M->real^N) x)`
  MP_TAC THENL
   [X_GEN_TAC `x:real^M` THEN EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [gauge]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o SPEC `x:real^M`) THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC `min (&1) (d / &(dimindex(:M)))`)) THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_LT_01; GSYM CONJ_ASSOC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; DIMINDEX_GE_1; LE_1; REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(x:real^M,d)` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "box" THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL; IN_BALL] THEN
      X_GEN_TAC `y:real^M` THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      SIMP_TAC[REAL_ARITH `x - h <= y /\ y <= x + h <=> abs(x - y) <= h`] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:M)) (\i. abs((x - y:real^M)$i))` THEN
      REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_BOUND_LT_GEN THEN
      REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; IN_NUMSEG] THEN
      SIMP_TAC[NOT_LT; DIMINDEX_GE_1; CARD_NUMSEG_1; VECTOR_SUB_COMPONENT] THEN
      ASM_MESON_TAC[REAL_LET_TRANS];
      UNDISCH_TAC `(x:real^M) IN interval[a,b]` THEN
      EXPAND_TAC "box" THEN REWRITE_TAC[SUBSET; IN_INTERVAL] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `y:real^M` THEN MP_TAC th) THEN
      REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      X_GEN_TAC `i:num` THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `uv:real^M->real` THEN
  REWRITE_TAC[TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^M`; `b:real^M`; `E:real^M->bool`;
                 `\x:real^M. if x IN E then ball(x,uv x) else g(x)`]
   COVERING_LEMMA) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTERVAL_NE_EMPTY] THEN CONJ_TAC THENL
     [EXPAND_TAC "E" THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[gauge] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gauge]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `D:(real^M->bool)->bool`) THEN
  EXISTS_TAC `UNIONS D:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `measurable(UNIONS D:real^M->bool) /\
    measure(UNIONS D) <= measure(interval[a:real^M,b])`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    REWRITE_TAC[MEASURABLE_INTERVAL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC MEASURABLE_UNIONS THEN
    ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `?d. d SUBSET D /\ FINITE d /\
        measure(UNIONS D:real^M->bool) <= &2 * measure(UNIONS d)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `measure(UNIONS D:real^M->bool) = &0` THENL
     [EXISTS_TAC `{}:(real^M->bool)->bool` THEN
      ASM_REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET; MEASURE_EMPTY; UNIONS_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      MP_TAC(ISPECL [`D:(real^M->bool)->bool`; `measure(interval[a:real^M,b])`;
                     `measure(UNIONS D:real^M->bool) / &2`]
                MEASURE_COUNTABLE_UNIONS_APPROACHABLE) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[MEASURABLE_MEASURE_POS_LT; REAL_HALF] THEN
        ASM_SIMP_TAC[GSYM MEASURABLE_MEASURE_EQ_0] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[MEASURABLE_INTERVAL]; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
        REPEAT(CONJ_TAC THENL
          [ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL; MEASURABLE_UNIONS];
           ALL_TAC]) THEN
        ASM SET_TAC[];
        MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o el 3 o CONJUNCTS) THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
  SIMP_TAC[IN_INTER] THEN REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_TAC `tag:(real^M->bool)->real^M`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `D <= &2 * d ==> d <= e / &2 ==> D <= e`)) THEN
  MP_TAC(ISPEC
   `IMAGE (\k:real^M->bool. (box:real->real^M->real^M->bool)
                            (uv(tag k):real) ((tag k:real^M))) d`
   AUSTIN_LEMMA) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN EXPAND_TAC "box" THEN
    EXISTS_TAC `&2 * uv((tag:(real^M->bool)->real^M) k):real` THEN
    EXISTS_TAC `(tag:(real^M->bool)->real^M) k - uv(tag k) % vec 1:real^M` THEN
    EXISTS_TAC `(tag:(real^M->bool)->real^M) k + uv(tag k) % vec 1:real^M` THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_SUBSET_IMAGE; real_ge] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^M->bool)->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REAL_ARITH
   `d <= d' /\ p <= e ==> d' <= p ==> d <= e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL];
      MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      EXPAND_TAC "box" THEN REWRITE_TAC[MEASURABLE_INTERVAL];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `z:real^M` THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^M) IN k` THEN SPEC_TAC(`z:real^M`,`z:real^M`) THEN
      REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(tag k:real^M,uv(tag(k:real^M->bool)))` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      EXPAND_TAC "box" THEN REWRITE_TAC[SUBSET; IN_BALL; IN_INTERVAL] THEN
      X_GEN_TAC `z:real^M` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      SIMP_TAC[REAL_ARITH `x - h <= y /\ y <= x + h <=> abs(x - y) <= h`] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
      ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LT_IMP_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  SUBGOAL_THEN `FINITE(p:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
  EXISTS_TAC `mu:real` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `IMAGE (\k. (tag:(real^M->bool)->real^M) k,
                (box(uv(tag k):real) (tag k):real^M->bool)) p`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[tagged_partial_division_of; fine] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN
    REWRITE_TAC[MESON[]
     `(!x j. (?k. (x = tag k /\ j = g k) /\ k IN d) ==> P x j) <=>
      (!k. k IN d ==> P (tag k) (g k))`] THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "box" THEN REWRITE_TAC[IN_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `&0 < u ==> x - u <= x /\ x <= x + u`) THEN ASM_MESON_TAC[SUBSET];
        ASM_MESON_TAC[SUBSET];
        EXPAND_TAC "box" THEN MESON_TAC[]];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k1:real^M->bool` THEN
      ASM_CASES_TAC `(k1:real^M->bool) IN p` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k2:real^M->bool` THEN
      ASM_CASES_TAC `(k2:real^M->bool) IN p` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(tag:(real^M->bool)->real^M) k1 = tag k2` THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [EXPAND_TAC "box" THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
        REWRITE_TAC[SUBSET_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        REWRITE_TAC[REAL_ARITH `x - e <= x + e <=> &0 <= e`] THEN
        SUBGOAL_THEN `&0 <= uv((tag:(real^M->bool)->real^M) k1) /\
                      &0 <= uv((tag:(real^M->bool)->real^M) k2)`
        STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[SUBSET; REAL_LT_IMP_LE]; ASM_REWRITE_TAC[]] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
        MATCH_MP_TAC MONO_NOT THEN REWRITE_TAC[AND_FORALL_THM] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(SET_RULE
         `i1 SUBSET s1 /\ i2 SUBSET s2
          ==> DISJOINT s1 s2 ==> i1 INTER i2 = {}`) THEN
        REWRITE_TAC[INTERIOR_SUBSET]];
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `e = e' /\ y <= x ==> x < e ==> y <= e'`) THEN
  CONJ_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    EXPAND_TAC "box" THEN REWRITE_TAC[MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a' <= e ==> a <= a' ==> a <= e`) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_LE_INCLUDED THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; RIGHT_EXISTS_AND_THM; FINITE_IMAGE] THEN
  REWRITE_TAC[NORM_POS_LE; EXISTS_IN_IMAGE] THEN
  EXISTS_TAC `SND:real^M#(real^M->bool)->real^M->bool` THEN
  X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&0 < uv(tag(k:real^M->bool):real^M):real` ASSUME_TAC
  THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < measure(box(uv(tag(k:real^M->bool):real^M):real) (tag
k):real^M->bool)`
  MP_TAC THENL
   [EXPAND_TAC "box" THEN
    REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> a - x <= a + x`] THEN
    MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN
    REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  DISCH_THEN(fun th ->
   GEN_REWRITE_TAC (funpow 2 RAND_CONV)
    [MATCH_MP(REAL_ARITH `&0 < x ==> x = abs x`) th] THEN
   ASSUME_TAC th) THEN
  REWRITE_TAC[real_div; GSYM REAL_ABS_INV] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM NORM_MUL] THEN
  SUBGOAL_THEN
   `mu <= dist(i (uv(tag(k:real^M->bool):real^M):real) (tag k):real^N,
               f(tag k))`
  MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> m <= x ==> m <= y`) THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN EXPAND_TAC "i" THEN
  REWRITE_TAC[dist; VECTOR_SUB_LDISTRIB] THEN
  UNDISCH_TAC
    `&0 < measure(box(uv(tag(k:real^M->bool):real^M):real)
                (tag k):real^M->bool)` THEN
  EXPAND_TAC "box" THEN REWRITE_TAC[MEASURE_INTERVAL] THEN
  SIMP_TAC[VECTOR_MUL_ASSOC; REAL_LT_IMP_NZ; REAL_MUL_LINV] THEN
  REWRITE_TAC[VECTOR_MUL_LID]);;

let HAS_VECTOR_DERIVATIVE_INDEFINITE_INTEGRAL = prove
 (`!f:real^1->real^N a b.
        f integrable_on interval[a,b]
        ==> ?k. negligible k /\
                !x. x IN interval[a,b] DIFF k
                    ==> ((\x. integral(interval[a,x]) f) has_vector_derivative
                         f(x)) (at x within interval[a,b])`,
  SUBGOAL_THEN
   `!f:real^1->real^N a b.
        f integrable_on interval[a,b]
        ==> ?k. negligible k /\
                !x e. x IN interval[a,b] DIFF k /\ & 0 < e
                      ==> ?d. &0 < d /\
                              !x'. x' IN interval[a,b] /\
                                   drop x < drop x' /\ drop x' < drop x + d
                                   ==> norm(integral(interval[x,x']) f -
                                            drop(x' - x) % f x) /
                                       norm(x' - x) < e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPEC
     `(\x. if x IN interval[a,b] then f x else vec 0):real^1->real^N`
     INTEGRABLE_CCONTINUOUS_EXPLICIT) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; SUBSET_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^1->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `e:real`] THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^1`; `e:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop y - drop x`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `x + (drop y - drop x) % vec 1 = y` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; DROP_VEC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CONTENT_1; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x < e ==> y < e`) THEN
    ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ;
                 GSYM DROP_EQ; REAL_LT_IMP_NE] THEN
    SUBGOAL_THEN `norm(y - x) = abs(drop y - drop x)` SUBST1_TAC THENL
     [REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB]; ALL_TAC] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM NORM_MUL)] THEN
    REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_FIELD `x < y ==> (y - x) * inv(y - x) = &1`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[DROP_SUB; VECTOR_MUL_LID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    X_GEN_TAC `z:real^1` THEN REWRITE_TAC[DIFF_EMPTY] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(ISPECL [`f:real^1->real^N`; `a:real^1`; `b:real^1`] th) THEN
    MP_TAC(ISPECL [`\x. (f:real^1->real^N) (--x)`; `--b:real^1`;
                   `--a:real^1`] th)) THEN
  ASM_REWRITE_TAC[INTEGRABLE_REFLECT] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^1->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^1->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1"))) THEN
  EXISTS_TAC `k1 UNION IMAGE (--) k2:real^1->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NEGLIGIBLE_LINEAR_IMAGE THEN ASM_REWRITE_TAC[linear] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN
  REWRITE_TAC[IN_IMAGE; VECTOR_ARITH `x:real^1 = --x' <=> --x = x'`] THEN
  REWRITE_TAC[UNWIND_THM1] THEN STRIP_TAC THEN
  REWRITE_TAC[has_vector_derivative; HAS_DERIVATIVE_WITHIN] THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REMOVE_THEN "2" (MP_TAC o SPECL [`--x:real^1`; `e:real`]) THEN
  REMOVE_THEN "1" (MP_TAC o SPECL [`x:real^1`; `e:real`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_INTERVAL_REFLECT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2"))) THEN
  EXISTS_TAC `min d1 d2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `drop x < drop y \/ drop y < drop x` DISJ_CASES_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REMOVE_THEN "1" (MP_TAC o SPEC `y:real^1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x < e ==> y < e`) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(VECTOR_ARITH `c + a:real^N = b ==> a = b - c`) THEN
    MATCH_MP_TAC INTEGRAL_COMBINE THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    REMOVE_THEN "2" (MP_TAC o SPEC `--y:real^1`) THEN
    ANTS_TAC THENL [SIMP_TAC[DROP_NEG] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm(--y - --x) = abs(drop y - drop x)` SUBST1_TAC THENL
     [REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; DROP_NEG] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x < e ==> y < e`) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[INTEGRAL_REFLECT] THEN
    REWRITE_TAC[VECTOR_NEG_NEG; DROP_SUB; DROP_NEG] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
      `x - (--a - --b) % y:real^N = --(--x - (a - b) % y)`] THEN
    REWRITE_TAC[NORM_NEG] THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(VECTOR_ARITH `b + a = c ==> --a:real^N = b - c`) THEN
    MATCH_MP_TAC INTEGRAL_COMBINE THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC]);;

let ABSOLUTELY_INTEGRABLE_LEBESGUE_POINTS = prove
 (`!f:real^M->real^N.
    (!a b. f absolutely_integrable_on interval[a,b])
    ==> ?k. negligible k /\
            !x e. ~(x IN k) /\ &0 < e
                  ==> ?d. &0 < d /\
                          !h. &0 < h /\ h < d
                             ==> norm(inv(content(interval[x - h % vec 1,
                                                           x + h % vec 1])) %
                                      integral (interval[x - h % vec 1,
                                                         x + h % vec 1])
                                               (\t. lift(norm(f t - f x))))
                                 < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(GEN `r:real^N` (ISPEC `\t. lift(norm((f:real^M->real^N) t - r))`
        INTEGRABLE_CCONTINUOUS_EXPLICIT_SYMMETRIC)) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MONO_FORALL) THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
    ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `k:real^N->real^M->bool` THEN STRIP_TAC THEN
  EXISTS_TAC
   `UNIONS (IMAGE (k:real^N->real^M->bool)
           {x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i)})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_RATIONAL_COORDINATES] THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `e:real`] THEN
  REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN STRIP_TAC THEN
  MP_TAC(SET_RULE `(f:real^M->real^N) x IN (:real^N)`) THEN
  REWRITE_TAC[GSYM CLOSURE_RATIONAL_COORDINATES] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &3 <=> &0 < e`] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:real^N`; `x:real^M`; `e / &3`]) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e / &3 <=> &0 < e`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(y1:real^N) < e / &3 /\ norm(i1 - i2) <= e / &3
    ==> norm(i1 - y1) < e / &3 ==> norm(i2) < e`) THEN
  REWRITE_TAC[NORM_LIFT; REAL_ABS_NORM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[dist; DIST_SYM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `abs(inv(content(interval[x - h % vec 1,x + h % vec 1]))) *
    drop(integral (interval[x - h % vec 1,x + h % vec 1])
                  (\x:real^M. lift(e / &3)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    W(MP_TAC o PART_MATCH (rand o rand) INTEGRAL_SUB o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
      ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_CONST];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      REWRITE_TAC[INTEGRABLE_CONST] THEN CONJ_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN CONJ_TAC THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
        ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_CONST];
        X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
        REWRITE_TAC[NORM_LIFT; REAL_ABS_NORM; LIFT_DROP; GSYM LIFT_SUB] THEN
        ASM_MESON_TAC[NORM_ARITH
         `dist(r,x) < e / &3
          ==> abs(norm(y - r:real^N) - norm(y - x)) <= e / &3`]]];
    ASM_CASES_TAC
     `content(interval[x - h % vec 1:real^M,x + h % vec 1]) = &0`
    THENL
     [ASM_REWRITE_TAC[REAL_INV_0; REAL_ABS_NUM; REAL_MUL_LZERO] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_INV] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ;
                   GSYM REAL_ABS_NZ] THEN
      REWRITE_TAC[INTEGRAL_CONST; DROP_CMUL; LIFT_DROP] THEN
      SIMP_TAC[real_abs; CONTENT_POS_LE; REAL_MUL_SYM; REAL_LE_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* Measurability of a function on a set (not necessarily itself measurable). *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("measurable_on",(12,"right"));;

let measurable_on = new_definition
 `(f:real^M->real^N) measurable_on s <=>
        ?k g. negligible k /\
              (!n. (g n) continuous_on (:real^M)) /\
              (!x. ~(x IN k)
                   ==> ((\n. g n x) --> if x IN s then f(x) else vec 0)
                       sequentially)`;;

let MEASURABLE_ON_UNIV = prove
 (`(\x.  if x IN s then f(x) else vec 0) measurable_on (:real^M) <=>
   f measurable_on s`,
  REWRITE_TAC[measurable_on; IN_UNIV; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Lebesgue measurability (like "measurable" but allowing infinite measure)  *)
(* ------------------------------------------------------------------------- *)

let lebesgue_measurable = new_definition
 `lebesgue_measurable s <=> (indicator s) measurable_on (:real^N)`;;

(* ------------------------------------------------------------------------- *)
(* Relation between measurability and integrability.                         *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f:real^M->real^N g s.
        f measurable_on s /\
        g integrable_on s /\
        (!x. x IN s ==> norm(f x) <= drop(g x))
        ==> f integrable_on s`,
  let lemma = prove
   (`!f:real^M->real^N g a b.
          f measurable_on (:real^M) /\
          g integrable_on interval[a,b] /\
          (!x. x IN interval[a,b] ==> norm(f x) <= drop(g x))
          ==> f integrable_on interval[a,b]`,
    REPEAT GEN_TAC THEN REWRITE_TAC[measurable_on; IN_UNIV] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `h:num->real^M->real^N`] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
    EXISTS_TAC `interval[a:real^M,b] DIFF k` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       NEGLIGIBLE_SUBSET)) THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC DOMINATED_CONVERGENCE_INTEGRABLE THEN
    MAP_EVERY EXISTS_TAC
     [`h:num->real^M->real^N`; `g:real^M->real^1`] THEN
    ASM_SIMP_TAC[IN_DIFF] THEN REWRITE_TAC[LEFT_AND_FORALL_THM] THEN
    X_GEN_TAC `n:num` THEN
    UNDISCH_TAC `(g:real^M->real^1) integrable_on interval [a,b]` THEN
    SUBGOAL_THEN
     `(h:num->real^M->real^N) n absolutely_integrable_on interval[a,b]`
    MP_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      REWRITE_TAC[IMP_IMP; absolutely_integrable_on; GSYM CONJ_ASSOC] THEN
      REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
      MATCH_MP_TAC INTEGRABLE_SPIKE_SET THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       NEGLIGIBLE_SUBSET)) THEN SET_TAC[]]) in
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_ON_ALL_INTERVALS_INTEGRABLE_BOUND THEN
  EXISTS_TAC `g:real^M->real^1` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  MATCH_MP_TAC lemma THEN
  EXISTS_TAC `(\x. if x IN s then g x else vec 0):real^M->real^1` THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[INTEGRABLE_ALT]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0; DROP_VEC; REAL_POS]);;

let MEASURABLE_BOUNDED_AE_BY_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f:real^M->real^N g s k.
        f measurable_on s /\ g integrable_on s /\ negligible k /\
        (!x. x IN s DIFF k ==> norm(f x) <= drop(g x))
        ==> f integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN EXISTS_TAC
   `\x. if x IN k then lift(norm((f:real^M->real^N) x)) else g x` THEN
  ASM_SIMP_TAC[COND_RAND; IN_DIFF; LIFT_DROP; REAL_LE_REFL; COND_ID] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
  MAP_EVERY EXISTS_TAC [`g:real^M->real^1`; `k:real^M->bool`] THEN
  ASM_SIMP_TAC[IN_DIFF]);;

let MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE = prove
 (`!f:real^M->real^N g s.
        f measurable_on s /\
        g integrable_on s /\
        (!x. x IN s ==> norm(f x) <= drop(g x))
        ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^M->real^1`]
    ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_BOUND) THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[NORM_REAL; GSYM drop] THEN
    ASM_MESON_TAC[REAL_ABS_LE; REAL_LE_TRANS];
    ASM_MESON_TAC[MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE];
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    ASM_REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; GSYM drop] THEN
    ASM_MESON_TAC[NORM_ARITH `norm(x) <= a ==> &0 <= a`]]);;

let INTEGRAL_DROP_LE_MEASURABLE = prove
 (`!f g s:real^N->bool.
        f measurable_on s /\
        g integrable_on s /\
        (!x. x IN s ==> &0 <= drop(f x) /\ drop(f x) <= drop(g x))
        ==> drop(integral s f) <= drop(integral s g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `g:real^N->real^1` THEN
  ASM_SIMP_TAC[NORM_REAL; GSYM drop; real_abs]);;

let INTEGRABLE_SUBINTERVALS_IMP_MEASURABLE = prove
 (`!f:real^M->real^N.
        (!a b. f integrable_on interval[a,b]) ==> f measurable_on (:real^M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_on; IN_UNIV] THEN
  MAP_EVERY ABBREV_TAC
   [`box = \h x. interval[x:real^M,x + h % vec 1]`;
    `i = \h:real x:real^M. inv(content(box h x)) %
                      integral (box h x) (f:real^M->real^N)`] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  EXISTS_TAC `(\n x. i (inv(&n + &1)) x):num->real^M->real^N` THEN
  REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[continuous_on; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`; `e:real`] THEN
    DISCH_TAC THEN EXPAND_TAC "i" THEN EXPAND_TAC "box" THEN
    MP_TAC(ISPECL
     [`f:real^M->real^N`;
      `x - &2 % vec 1:real^M`;
      `x + &2 % vec 1:real^M`;
      `x:real^M`;
      `x + inv(&n + &1) % vec 1:real^M`;
      `e * (&1 / (&n + &1)) pow dimindex(:M)`]
     INDEFINITE_INTEGRAL_CONTINUOUS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTERVAL; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
        REAL_MUL_RID; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `&0 <= inv(&n + &1) /\ inv(&n + &1) <= &1` MP_TAC THENL
         [ALL_TAC; REAL_ARITH_TAC] THEN
        ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_ARITH `&0 <= &n + &1`] THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
        REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min k (&1)` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
      ASM_REWRITE_TAC[dist] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[CONTENT_CLOSED_INTERVAL_CASES] THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_ARITH `a <= a + x <=> &0 <= x`] THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_ARITH `&0 <= &n + &1`] THEN
      REWRITE_TAC[REAL_ARITH `(x + inv y) - x = &1 / y`] THEN
      REWRITE_TAC[PRODUCT_CONST_NUMSEG; ADD_SUB] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
      REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_DIV] THEN
      REWRITE_TAC[REAL_ABS_NUM; REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_DIV; REAL_POW_LT;
                   REAL_ARITH `&0 < &1 /\ &0 < &n + &1`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[VECTOR_ARITH `(y + i) - (x + i):real^N = y - x`;
                  VECTOR_ARITH `(y - i) - (x - i):real^N = y - x`] THEN
      ASM_SIMP_TAC[IN_INTERVAL; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `i:num` THEN
      ASM_CASES_TAC `1 <= i /\ i <= dimindex(:M)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= i /\ i <= &1 /\ abs(x - y) <= &1
        ==> (x - &2 <= y /\ y <= x + &2) /\
            (x - &2 <= y + i /\ y + i <= x + &2)`) THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_INV_LE_1;
                   REAL_ARITH `&0 <= &n + &1 /\ &1 <= &n + &1`] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
      ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LT_IMP_LE; NORM_SUB;
                    REAL_LE_TRANS]];
    FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_CCONTINUOUS_EXPLICIT) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
    ASM_CASES_TAC `negligible(k:real^M->bool)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    MP_TAC(SPEC `d:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["i"; "box"] THEN REWRITE_TAC[dist] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC]);;

let INTEGRABLE_IMP_MEASURABLE = prove
 (`!f:real^M->real^N s.
        f integrable_on s ==> f measurable_on s`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV; GSYM MEASURABLE_ON_UNIV] THEN
  SPEC_TAC(`\x. if x IN s then (f:real^M->real^N) x else vec 0`,
           `f:real^M->real^N`) THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_SUBINTERVALS_IMP_MEASURABLE THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]);;

let ABSOLUTELY_INTEGRABLE_MEASURABLE = prove
 (`!f:real^M->real^N s.
        f absolutely_integrable_on s <=>
        f measurable_on s /\ (\x. lift(norm(f x))) integrable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[absolutely_integrable_on] THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (b /\ c ==> a) ==> (a /\ c <=> b /\ c)`) THEN
  REWRITE_TAC[INTEGRABLE_IMP_MEASURABLE] THEN STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. lift(norm((f:real^M->real^N) x))` THEN
  ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Composing continuous and measurable functions; a few variants.            *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_COMPOSE_CONTINUOUS = prove
 (`!f:real^M->real^N g:real^N->real^P.
        f measurable_on (:real^M) /\ g continuous_on (:real^N)
        ==> (g o f) measurable_on (:real^M)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[measurable_on; IN_UNIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `h:num->real^M->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\n x. (g:real^N->real^P) ((h:num->real^M->real^N) n x)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_REWRITE_TAC[ETA_AX] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [CONTINUOUS_ON_SEQUENTIALLY]) THEN
    ASM_SIMP_TAC[o_DEF; IN_UNIV]]);;

let MEASURABLE_ON_COMPOSE_CONTINUOUS_0 = prove
 (`!f:real^M->real^N g:real^N->real^P s.
        f measurable_on s /\ g continuous_on (:real^N) /\ g(vec 0) = vec 0
        ==> (g o f) measurable_on s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`] THEN
  DISCH_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_COMPOSE_CONTINUOUS) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_DEF] THEN ASM_MESON_TAC[]);;

let MEASURABLE_ON_COMPOSE_CONTINUOUS_OPEN_INTERVAL = prove
 (`!f:real^M->real^N g:real^N->real^P a b.
        f measurable_on (:real^M) /\
        (!x. f(x) IN interval(a,b)) /\
        g continuous_on interval(a,b)
        ==> (g o f) measurable_on (:real^M)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[measurable_on; IN_UNIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `h:num->real^M->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `(\n x. (g:real^N->real^P)
           (lambda i. max ((a:real^N)$i + (b$i - a$i) / (&n + &2))
                          (min ((h n x:real^N)$i)
                               ((b:real^N)$i - (b$i - a$i) / (&n + &2)))))
    :num->real^M->real^P` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`(:real^M)`;
        `(lambda i. (b:real^N)$i - (b$i - (a:real^N)$i) / (&n + &2)):real^N`]
         CONTINUOUS_ON_CONST) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[IMP_IMP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_MIN) THEN
      MP_TAC(ISPECL
       [`(:real^M)`;
        `(lambda i. (a:real^N)$i + ((b:real^N)$i - a$i) / (&n + &2)):real^N`]
         CONTINUOUS_ON_CONST) THEN
      REWRITE_TAC[IMP_IMP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_MAX) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(a:real^N,b)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `x:real^M` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o CONJUNCT1) THEN
      SIMP_TAC[IN_INTERVAL; LAMBDA_BETA] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN
        `&0 < ((b:real^N)$i - (a:real^N)$i) / (&n + &2) /\
         ((b:real^N)$i - (a:real^N)$i) / (&n + &2) <= (b$i - a$i) / &2` MP_TAC
      THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ;
                   REAL_ARITH `&0 < &n + &2`] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[real_div]] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC]];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_INTERVAL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((\n. (lambda i. ((a:real^N)$i + ((b:real^N)$i - a$i) / (&n + &2))))
       --> a) sequentially /\
      ((\n. (lambda i. ((b:real^N)$i - ((b:real^N)$i - a$i) / (&n + &2))))
       --> b) sequentially`
    MP_TAC THENL
     [ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
      SIMP_TAC[LAMBDA_BETA] THEN
      CONJ_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[real_sub] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_RID] THEN
      REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC LIM_ADD THEN
      REWRITE_TAC[LIM_CONST; LIFT_NEG; real_div; LIFT_CMUL] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_NEG_0] THEN
      TRY(MATCH_MP_TAC LIM_NEG) THEN REWRITE_TAC[VECTOR_NEG_0] THEN
      SUBST1_TAC(VECTOR_ARITH
       `vec 0:real^1 = ((b:real^N)$j + --((a:real^N)$j)) % vec 0`) THEN
      MATCH_MP_TAC LIM_CMUL THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0; NORM_LIFT] THEN
      X_GEN_TAC `e:real` THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_INV] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT; LE_1;
                   REAL_OF_NUM_LE; REAL_ABS_NUM] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[TAUT `a ==> b /\ c ==> d <=> a /\ c ==> b ==> d`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_MIN) THEN
    REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_MAX) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; FUN_EQ_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
    ASM_MESON_TAC[REAL_ARITH `a < x /\ x < b ==> max a (min x b) = x`]]);;

let MEASURABLE_ON_COMPOSE_CONTINUOUS_CLOSED_SET = prove
 (`!f:real^M->real^N g:real^N->real^P s.
        closed s /\
        f measurable_on (:real^M) /\
        (!x. f(x) IN s) /\
        g continuous_on s
        ==> (g o f) measurable_on (:real^M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^P`; `(:real^N)`; `s:real^N->bool`]
    TIETZE_UNBOUNDED) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `h:real^N->real^P` THEN
  DISCH_TAC THEN SUBGOAL_THEN
   `(g:real^N->real^P) o (f:real^M->real^N) = h o f` SUBST1_TAC
  THENL [ASM_SIMP_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS THEN ASM_REWRITE_TAC[]);;

let MEASURABLE_ON_COMPOSE_CONTINUOUS_CLOSED_SET_0 = prove
 (`!f:real^M->real^N g:real^N->real^P s t.
        closed s /\
        f measurable_on t /\
        (!x. f(x) IN s) /\
        g continuous_on s /\
        vec 0 IN s /\ g(vec 0) = vec 0
        ==> (g o f) measurable_on t`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  MP_TAC(ISPECL [`(\x. if x IN t then f x else vec 0):real^M->real^N`;
                 `g:real^N->real^P`; `s:real^N->bool`]
        MEASURABLE_ON_COMPOSE_CONTINUOUS_CLOSED_SET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEASURABLE_ON_UNIV] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Basic closure properties of measurable functions.                         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_IMP_MEASURABLE_ON = prove
 (`!f:real^M->real^N. f continuous_on (:real^M) ==> f measurable_on (:real^M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_on; IN_UNIV] THEN
  EXISTS_TAC `{}:real^M->bool` THEN REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
  EXISTS_TAC `\n:num. (f:real^M->real^N)` THEN
  ASM_REWRITE_TAC[LIM_CONST]);;

let MEASURABLE_ON_CONST = prove
 (`!k:real^N. (\x. k) measurable_on (:real^M)`,
  SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON; CONTINUOUS_ON_CONST]);;

let MEASURABLE_ON_0 = prove
 (`!s. (\x. vec 0) measurable_on s`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[MEASURABLE_ON_CONST; COND_ID]);;

let MEASURABLE_ON_CMUL = prove
 (`!c f:real^M->real^N s.
        f measurable_on s ==> (\x. c % f x) measurable_on s`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS_0 THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID]);;

let MEASURABLE_ON_NEG = prove
 (`!f:real^M->real^N s.
     f measurable_on s ==> (\x. --(f x)) measurable_on s`,
  REWRITE_TAC[VECTOR_ARITH `--x:real^N = --(&1) % x`;
              MEASURABLE_ON_CMUL]);;

let MEASURABLE_ON_NEG_EQ = prove
 (`!f:real^M->real^N s. (\x. --(f x)) measurable_on s <=> f measurable_on s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_NEG) THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX]);;

let MEASURABLE_ON_NORM = prove
 (`!f:real^M->real^N s.
        f measurable_on s ==> (\x. lift(norm(f x))) measurable_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o ISPEC `\x:real^N. lift(norm x)` o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] MEASURABLE_ON_COMPOSE_CONTINUOUS_0)) THEN
  REWRITE_TAC[o_DEF; NORM_0; LIFT_NUM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[continuous_on; IN_UNIV; DIST_LIFT] THEN
  GEN_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN NORM_ARITH_TAC);;

let MEASURABLE_ON_PASTECART = prove
 (`!f:real^M->real^N g:real^M->real^P s.
        f measurable_on s /\ g measurable_on s
        ==> (\x. pastecart (f x) (g x)) measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[measurable_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k1:real^M->bool` MP_TAC)
   (X_CHOOSE_THEN `k2:real^M->bool` MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:num->real^M->real^P` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:num->real^M->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k1 UNION k2:real^M->bool` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_UNION] THEN
  EXISTS_TAC `(\n x. pastecart (g1 n x) (g2 n x))
              :num->real^M->real^(N,P)finite_sum` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_PASTECART; ETA_AX; IN_UNION; DE_MORGAN_THM] THEN
  X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`)) THEN
  ASM_CASES_TAC `(x:real^M) IN s` THEN
  REWRITE_TAC[GSYM PASTECART_VEC] THEN ASM_SIMP_TAC[LIM_PASTECART]);;

let MEASURABLE_ON_COMBINE = prove
 (`!h:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P s.
        f measurable_on s /\ g measurable_on s /\
        (\x. h (fstcart x) (sndcart x)) continuous_on UNIV /\
        h (vec 0) (vec 0) = vec 0
        ==> (\x. h (f x) (g x)) measurable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^M. (h:real^N->real^P->real^Q) (f x) (g x)) =
    (\x. h (fstcart x) (sndcart x)) o (\x. pastecart (f x) (g x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; FSTCART_PASTECART; SNDCART_PASTECART; o_THM];
    MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS_0 THEN
    ASM_SIMP_TAC[MEASURABLE_ON_PASTECART; FSTCART_VEC; SNDCART_VEC]]);;

let MEASURABLE_ON_ADD = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        f measurable_on s /\ g measurable_on s
        ==> (\x. f x + g x) measurable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_COMBINE THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

let MEASURABLE_ON_SUB = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        f measurable_on s /\ g measurable_on s
        ==> (\x. f x - g x) measurable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_COMBINE THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  CONJ_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

let MEASURABLE_ON_MAX = prove
 (`!f:real^M->real^N g:real^M->real^N s.
      f measurable_on s /\ g measurable_on s
      ==> (\x. (lambda i. max ((f x)$i) ((g x)$i)):real^N)
          measurable_on s`,
  let lemma = REWRITE_RULE[]
   (ISPEC `(\x y. lambda i. max (x$i) (y$i)):real^N->real^N->real^N`
          MEASURABLE_ON_COMBINE) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[REAL_ARITH `max x x = x`; LAMBDA_ETA] THEN
  SIMP_TAC[continuous_on; LAMBDA_BETA; IN_UNIV; DIST_LIFT] THEN
  GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^(N,N)finite_sum`; `e:real`] THEN
  DISCH_TAC THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[dist] THEN
  X_GEN_TAC `y:real^(N,N)finite_sum` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(x - y) < e /\ abs(x' - y') < e
    ==> abs(max x x' - max y y') < e`) THEN
  REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN CONJ_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `norm(x) < e /\ abs(x$i) <= norm x ==> abs(x$i) < e`) THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM; GSYM FSTCART_SUB; GSYM SNDCART_SUB] THEN
  ASM_MESON_TAC[REAL_LET_TRANS; NORM_FSTCART; NORM_SNDCART]);;

let MEASURABLE_ON_MIN = prove
 (`!f:real^M->real^N g:real^M->real^N s.
      f measurable_on s /\ g measurable_on s
      ==> (\x. (lambda i. min ((f x)$i) ((g x)$i)):real^N)
          measurable_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_NEG)) THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_MAX) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_NEG) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  SIMP_TAC[CART_EQ; VECTOR_NEG_COMPONENT; LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let MEASURABLE_ON_DROP_MUL = prove
 (`!f g:real^M->real^N s.
      f measurable_on s /\ g measurable_on s
      ==> (\x. drop(f x) % g x) measurable_on s`,
  let lemma = REWRITE_RULE[]
   (ISPEC `\x y. drop x % y :real^N` MEASURABLE_ON_COMBINE) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  REWRITE_TAC[o_DEF; ETA_AX; LIFT_DROP] THEN
  CONJ_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

let MEASURABLE_ON_LIFT_MUL = prove
 (`!f g s. (\x. lift(f x)) measurable_on s /\
           (\x. lift(g x)) measurable_on s
           ==> (\x. lift(f x * g x)) measurable_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_DROP_MUL) THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_DROP]);;

let MEASURABLE_ON_VSUM = prove
 (`!f:A->real^M->real^N t.
        FINITE t /\ (!i. i IN t ==> (f i) measurable_on s)
        ==> (\x. vsum t (\i. f i x)) measurable_on s`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; MEASURABLE_ON_0; MEASURABLE_ON_ADD; IN_INSERT;
           ETA_AX]);;

let MEASURABLE_ON_COMPONENTWISE = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        (!i. 1 <= i /\ i <= dimindex(:N)
             ==> (\x. lift(f x$i)) measurable_on (:real^M))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o
     ISPEC `\x:real^N. lift(x$i)` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] MEASURABLE_ON_COMPOSE_CONTINUOUS)) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; o_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[measurable_on; IN_UNIV] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`k:num->real^M->bool`; `g:num->num->real^M->real^1`] THEN
  DISCH_TAC THEN
  EXISTS_TAC `UNIONS(IMAGE k (1..dimindex(:N))):real^M->bool` THEN
  EXISTS_TAC `(\n x. lambda i. drop(g i n x)):num->real^M->real^N` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; FORALL_IN_IMAGE; FINITE_IMAGE];
    GEN_TAC THEN ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX];
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX]]);;

let MEASURABLE_ON_SPIKE = prove
 (`!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN t DIFF s ==> g x = f x)
        ==> f measurable_on t ==> g measurable_on t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  REWRITE_TAC[measurable_on] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s UNION k:real^M->bool` THEN
  ASM_SIMP_TAC[DE_MORGAN_THM; IN_UNION; NEGLIGIBLE_UNION]);;

let MEASURABLE_ON_SPIKE_SET = prove
 (`!f:real^M->real^N s t.
        negligible (s DIFF t UNION t DIFF s)
        ==> f measurable_on s
            ==> f measurable_on t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[measurable_on] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `g:num->real^M->real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k UNION (s DIFF t UNION t DIFF s):real^M->bool` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_UNION; IN_UNION; DE_MORGAN_THM] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
  MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(x:real^M) IN t`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MEASURABLE_ON_RESTRICT = prove
 (`!f:real^M->real^N s.
        f measurable_on (:real^M) /\ lebesgue_measurable s
        ==> (\x. if x IN s then f(x) else vec 0) measurable_on (:real^M)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lebesgue_measurable; indicator] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_DROP_MUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DROP_VEC] THEN VECTOR_ARITH_TAC);;

let MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET = prove
 (`!f s t. s SUBSET t /\ f measurable_on t /\
           lebesgue_measurable s
           ==> f measurable_on s`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_RESTRICT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM SET_TAC[]);;

let MEASURABLE_ON_LIMIT = prove
 (`!f:num->real^M->real^N g s k.
        (!n. (f n) measurable_on s) /\
        negligible k /\
        (!x. x IN s DIFF k ==> ((\n. f n x) --> g x) sequentially)
        ==> g measurable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `vec 1:real^N`]
    HOMEOMORPHIC_OPEN_INTERVAL_UNIV) THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY; VEC_COMPONENT; REAL_LT_01] THEN
  REWRITE_TAC[homeomorphic; homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h':real^N->real^N`; `h:real^N->real^N`] THEN
  REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((h':real^N->real^N) o (h:real^N->real^N) o
     (\x. if x IN s then g x else vec 0)) measurable_on (:real^M)`
  MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[o_DEF; MEASURABLE_ON_UNIV]] THEN
  SUBGOAL_THEN `!y:real^N. norm(h y:real^N) <= &(dimindex(:N))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE h UNIV = s ==> (!z. z IN s ==> P z) ==> !y. P(h y)`)) THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTERVAL] THEN
    REWRITE_TAC[VEC_COMPONENT] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. abs((y:real^N)$i))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x /\ x < &1 ==> abs(x) <= &1`];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS_OPEN_INTERVAL THEN
  MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `vec 1:real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUBINTERVALS_IMP_MEASURABLE THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
    EXISTS_TAC `interval[a:real^M,b] DIFF k` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC DOMINATED_CONVERGENCE_INTEGRABLE THEN
    MAP_EVERY EXISTS_TAC
     [`(\n x. h(if x IN s then f n x else vec 0:real^N)):num->real^M->real^N`;
      `(\x. vec(dimindex(:N))):real^M->real^1`] THEN
    REWRITE_TAC[o_DEF; INTEGRABLE_CONST] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC
        MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
      EXISTS_TAC `(\x. vec(dimindex(:N))):real^M->real^1` THEN
      ASM_REWRITE_TAC[ETA_AX; INTEGRABLE_CONST] THEN
      ASM_SIMP_TAC[DROP_VEC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE_SET) THEN
        EXISTS_TAC `interval[a:real^M,b:real^M]` THEN CONJ_TAC THENL
         [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          ALL_TAC] THEN
        ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
        MATCH_MP_TAC(REWRITE_RULE[indicator; lebesgue_measurable]
              MEASURABLE_ON_RESTRICT) THEN
        REWRITE_TAC[MEASURABLE_ON_UNIV] THEN CONJ_TAC THENL
         [MP_TAC(ISPECL
           [`(\x. if x IN s then f (n:num) x else vec 0):real^M->real^N`;
            `h:real^N->real^N`] MEASURABLE_ON_COMPOSE_CONTINUOUS) THEN
          ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[MEASURABLE_ON_UNIV; ETA_AX];
          MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
          REWRITE_TAC[INTEGRABLE_CONST]];
        MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
        EXISTS_TAC `interval[a:real^M,b:real^M]` THEN
        REWRITE_TAC[INTEGRABLE_CONST] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
      EXISTS_TAC `interval[a:real^M,b:real^M]` THEN
      REWRITE_TAC[INTEGRABLE_CONST] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_SIMP_TAC[DROP_VEC];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_REWRITE_TAC[LIM_CONST] THEN
      MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]];
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[]]);;

let MEASURABLE_ON_BILINEAR = prove
 (`!op:real^N->real^P->real^Q f g s:real^M->bool.
        bilinear op /\ f measurable_on s /\ g measurable_on s
        ==> (\x. op (f x) (g x)) measurable_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[measurable_on; LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `ff:num->real^M->real^N`] THEN
  REPLICATE_TAC 3 DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`k':real^M->bool`; `gg:num->real^M->real^P`] THEN
  REPLICATE_TAC 3 DISCH_TAC THEN EXISTS_TAC `k UNION k':real^M->bool` THEN
  EXISTS_TAC
   `\n:num x:real^M. (op:real^N->real^P->real^Q) (ff n x) (gg n x)` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THENL
   [GEN_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[TAUT `p /\ q /\ r ==> s <=> r ==> p /\ q ==> s`]
        BILINEAR_CONTINUOUS_ON_COMPOSE)) THEN
    ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(if x IN s then (op:real^N->real^P->real^Q) (f x) (g x) else vec 0) =
      op (if x IN s then f(x:real^M) else vec 0)
         (if x IN s then g(x:real^M) else vec 0)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bilinear]) THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (MP_TAC o GEN `y:real^N` o MATCH_MP LINEAR_0 o SPEC `y:real^N`)
       (MP_TAC o GEN `z:real^P` o MATCH_MP LINEAR_0 o SPEC `z:real^P`)) THEN
      MESON_TAC[];
      REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[TAUT `p /\ q /\ r ==> s <=> r ==> p /\ q ==> s`]
                LIM_BILINEAR)) THEN
      ASM_SIMP_TAC[]]]);;

let ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT = prove
 (`!op:real^N->real^P->real^Q f g s:real^M->bool.
        bilinear op /\
        f measurable_on s /\ bounded (IMAGE f s) /\
        g absolutely_integrable_on s
        ==> (\x. op (f x) (g x)) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BILINEAR_BOUNDED_POS) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real^M. lift(B * C * norm((g:real^M->real^P) x))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        MEASURABLE_ON_BILINEAR)) THEN
    ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE];
    REWRITE_TAC[LIFT_CMUL] THEN
    REPEAT(MATCH_MP_TAC INTEGRABLE_CMUL) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    TRANS_TAC REAL_LE_TRANS
     `B * norm((f:real^M->real^N) x) * norm(g x:real^P)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[NORM_POS_LE]]);;

let MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_AE = prove
 (`!f:real^M->real^N g s t.
        f measurable_on s /\  g integrable_on s /\ negligible t /\
        (!x. x IN s DIFF t ==> norm(f x) <= drop(g x))
        ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
  MAP_EVERY EXISTS_TAC
   [`\x. if x IN s DIFF t then (f:real^M->real^N) x else vec 0`;
    `t:real^M->bool`] THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x. if x IN s DIFF t then (g:real^M->real^1) x else vec 0` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (ONCE_REWRITE_RULE[TAUT `p ==> q ==> r <=> q ==> p ==> r`]
        MEASURABLE_ON_SPIKE));
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (ONCE_REWRITE_RULE[TAUT `p ==> q ==> r <=> q ==> p ==> r`]
        INTEGRABLE_SPIKE));
    ASM_MESON_TAC[REAL_LE_REFL; NORM_0; DROP_VEC]] THEN
  EXISTS_TAC `t:real^M->bool` THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Natural closure properties of measurable functions; the intersection      *)
(* one is actually quite tedious since we end up reinventing cube roots      *)
(* before they actually get introduced in transcendentals.ml                 *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_EMPTY = prove
 (`!f:real^M->real^N. f measurable_on {}`,
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[NOT_IN_EMPTY; MEASURABLE_ON_CONST]);;

let MEASURABLE_ON_INTER = prove
 (`!f:real^M->real^N s t.
        f measurable_on s /\ f measurable_on t
        ==> f measurable_on (s INTER t)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  ONCE_REWRITE_TAC[MEASURABLE_ON_COMPONENTWISE] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q ==> r <=> p /\ p ==> q ==> r`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_LIFT_MUL) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_LIFT_MUL) THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[VEC_COMPONENT; REAL_ARITH
   `(if p then x else &0) * (if q then y else &0) =
    if p /\ q then x * y else &0`] THEN
  SUBGOAL_THEN `!s. (\x. lift (drop x pow 3)) continuous_on s` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_ARITH `(x:real) pow 3 = x * x * x`] THEN
    REWRITE_TAC[LIFT_CMUL] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
           ASM_REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID]);
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. !x. lift(drop(r x) pow 3) = x` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; FORALL_LIFT; GSYM EXISTS_DROP; LIFT_EQ] THEN
    X_GEN_TAC `x:real` THEN  MP_TAC(ISPECL
     [`\x. lift (drop x pow 3)`; `lift(--(abs x + &1))`;
      `lift(abs x + &1)`;`x:real`; `1`] IVT_INCREASING_COMPONENT_1) THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP; EXISTS_DROP] THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `(:real^1)`) THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
      REWRITE_TAC[REAL_BOUNDS_LE; REAL_POW_NEG; ARITH] THEN
      MATCH_MP_TAC(REAL_ARITH
      `&0 <= x /\ &0 <= x pow 2 /\ &0 <= x pow 3 ==> x <= (x + &1) pow 3`) THEN
      SIMP_TAC[REAL_POW_LE; REAL_ABS_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x.  r(lift(x pow 3)) = lift x` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN GEN_TAC THEN
    MATCH_MP_TAC REAL_POW_EQ_ODD THEN EXISTS_TAC `3` THEN
    ASM_REWRITE_TAC[ARITH; GSYM LIFT_EQ; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^1->real^1) continuous_on (:real^1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_INVERSE_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`\x. lift(drop x pow 3)`; `(:real^1)`] THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN SUBST1_TAC(SYM th)) THEN
    MATCH_MP_TAC INJECTIVE_INTO_1D_IMP_OPEN_MAP THEN
    ASM_REWRITE_TAC[PATH_CONNECTED_UNIV; LIFT_EQ] THEN
    SIMP_TAC[REAL_POW_EQ_ODD_EQ; ARITH; DROP_EQ];
    ONCE_REWRITE_TAC[REAL_ARITH `&0 = &0 pow 3`] THEN
    REWRITE_TAC[REAL_ARITH `(x * x) * x:real = x pow 3`; IN_INTER] THEN
    REWRITE_TAC[MESON[] `(if p then x pow 3 else y pow 3) =
                         (if p then x else y:real) pow 3`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(MP_TAC o ISPEC `r:real^1->real^1` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] MEASURABLE_ON_COMPOSE_CONTINUOUS)) THEN
    ASM_REWRITE_TAC[o_DEF]]);;

let MEASURABLE_ON_DIFF = prove
 (`!f:real^M->real^N s t.
    f measurable_on s /\ f measurable_on t ==> f measurable_on (s DIFF t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MEASURABLE_ON_INTER) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[IMP_IMP] THEN
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_SUB) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; IN_DIFF; IN_INTER] THEN
  X_GEN_TAC `x:real^M` THEN
  MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(x:real^M) IN t`] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let MEASURABLE_ON_UNION = prove
 (`!f:real^M->real^N s t.
    f measurable_on s /\ f measurable_on t ==> f measurable_on (s UNION t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MEASURABLE_ON_INTER) THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_ADD) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_SUB) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; IN_UNION; IN_INTER] THEN
  X_GEN_TAC `x:real^M` THEN
  MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(x:real^M) IN t`] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let MEASURABLE_ON_UNIONS = prove
 (`!f:real^M->real^N k.
        FINITE k /\ (!s. s IN k ==> f measurable_on s)
        ==> f measurable_on (UNIONS k)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; MEASURABLE_ON_EMPTY; UNIONS_INSERT] THEN
  SIMP_TAC[FORALL_IN_INSERT; MEASURABLE_ON_UNION]);;

let MEASURABLE_ON_COUNTABLE_UNIONS = prove
 (`!f:real^M->real^N k.
        COUNTABLE k /\ (!s. s IN k ==> f measurable_on s)
        ==> f measurable_on (UNIONS k)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k:(real^M->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; MEASURABLE_ON_EMPTY] THEN
  MP_TAC(ISPEC `k:(real^M->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:num->real^M->bool` THEN DISCH_THEN SUBST_ALL_TAC THEN
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
  EXISTS_TAC `(\n x. if x IN UNIONS (IMAGE d (0..n)) then f x else vec 0):
              num->real^M->real^N` THEN
  EXISTS_TAC `{}:real^M->bool` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY; MEASURABLE_ON_UNIV] THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC MEASURABLE_ON_UNIONS THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FORALL_IN_IMAGE]) THEN
    SIMP_TAC[FORALL_IN_IMAGE; IN_UNIV; FINITE_IMAGE; FINITE_NUMSEG];
    X_GEN_TAC `x:real^M` THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_CASES_TAC `(x:real^M) IN UNIONS (IMAGE d (:num))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIM_EVENTUALLY THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; IN_UNIV; EVENTUALLY_SEQUENTIALLY] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_UNIONS]) THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; IN_NUMSEG; LE_0] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN ASM SET_TAC[]]]);;

