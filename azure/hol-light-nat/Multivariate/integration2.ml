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
include Integration1

(* ------------------------------------------------------------------------- *)
(* Finally, the integral of a constant!                                      *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_CONST = prove
 (`!a b:real^M c:real^N.
    ((\x. c) has_integral (content(interval[a,b]) % c)) (interval[a,b])`,
  REWRITE_TAC[has_integral] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x:real^M. ball(x,&1)` THEN REWRITE_TAC[GAUGE_TRIVIAL] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  FIRST_X_ASSUM(fun th ->
  ONCE_REWRITE_TAC[GSYM(MATCH_MP ADDITIVE_CONTENT_TAGGED_DIVISION th)]) THEN
  ASM_SIMP_TAC[VSUM_VMUL; GSYM VSUM_SUB] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM; VECTOR_SUB_REFL] THEN
  ASM_REWRITE_TAC[GSYM LAMBDA_PAIR_THM; VSUM_0; NORM_0]);;

let INTEGRABLE_CONST = prove
 (`!a b:real^M c:real^N. (\x. c) integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integrable_on] THEN
  EXISTS_TAC `content(interval[a:real^M,b]) % c:real^N` THEN
  REWRITE_TAC[HAS_INTEGRAL_CONST]);;

let INTEGRAL_CONST = prove
 (`!a b c. integral (interval[a,b]) (\x. c) = content(interval[a,b]) % c`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_INTEGRAL_CONST]);;

let INTEGRAL_PASTECART_CONST = prove
 (`!a b:real^M c d:real^N k:real^P.
     integral (interval[pastecart a c,pastecart b d]) (\x. k) =
     integral (interval[a,b])
              (\x. integral (interval[c,d]) (\y. k))`,
  REWRITE_TAC[INTEGRAL_CONST; CONTENT_PASTECART; VECTOR_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Bounds on the norm of Riemann sums and the integral itself.               *)
(* ------------------------------------------------------------------------- *)

let DSUM_BOUND = prove
 (`!p a b:real^M c:real^N e.
       p division_of interval[a,b] /\ norm(c) <= e
       ==> norm(vsum p (\l. content l % c)) <= e * content(interval[a,b])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `y <= e ==> x <= y ==> x <= e`) THEN
  REWRITE_TAC[LAMBDA_PAIR_THM; NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum p (\k:real^M->bool. content k * e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    X_GEN_TAC `l:real^M->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs(x) <= x`) THEN
    ASM_MESON_TAC[DIVISION_OF; CONTENT_POS_LE];
    REWRITE_TAC[SUM_RMUL; ETA_AX] THEN
    ASM_MESON_TAC[ADDITIVE_CONTENT_DIVISION; REAL_LE_REFL; REAL_MUL_SYM]]);;

let RSUM_BOUND = prove
 (`!p a b f:real^M->real^N e.
       p tagged_division_of interval[a,b] /\
       (!x. x IN interval[a,b] ==> norm(f x) <= e)
       ==> norm(vsum p (\(x,k). content k % f x))
            <= e * content(interval[a,b])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `y <= e ==> x <= y ==> x <= e`) THEN
  REWRITE_TAC[LAMBDA_PAIR_THM; NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum p (\(x:real^M,k:real^M->bool). content k * e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[TAGGED_DIVISION_OF; CONTENT_POS_LE; REAL_ABS_REFL;
                    REAL_LE_REFL];
      ASM_MESON_TAC[TAG_IN_INTERVAL]];
    FIRST_ASSUM(fun th -> REWRITE_TAC
     [GSYM(MATCH_MP ADDITIVE_CONTENT_TAGGED_DIVISION th)]) THEN
    REWRITE_TAC[GSYM SUM_LMUL; LAMBDA_PAIR_THM] THEN
    REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]]);;

let RSUM_DIFF_BOUND = prove
 (`!p a b f g:real^M->real^N.
       p tagged_division_of interval[a,b] /\
       (!x. x IN interval[a,b] ==> norm(f x - g x) <= e)
       ==> norm(vsum p (\(x,k). content k % f x) -
                vsum p (\(x,k). content k % g x))
           <= e * content(interval[a,b])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(vsum p (\(x,k).
      content(k:real^M->bool) % ((f:real^M->real^N) x - g x)))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM VSUM_SUB; VECTOR_SUB_LDISTRIB] THEN
    REWRITE_TAC[LAMBDA_PAIR_THM; REAL_LE_REFL];
    ASM_SIMP_TAC[RSUM_BOUND]]);;

let HAS_INTEGRAL_BOUND = prove
 (`!f:real^M->real^N a b i B.
        &0 <= B /\
        (f has_integral i) (interval[a,b]) /\
        (!x. x IN interval[a,b] ==> norm(f x) <= B)
        ==> norm i <= B * content(interval[a,b])`,
  let lemma = prove
   (`norm(s) <= B ==> ~(norm(s - i) < norm(i) - B)`,
    MATCH_MP_TAC(REAL_ARITH `n1 <= n + n2 ==> n <= B ==> ~(n2 < n1 - B)`) THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[NORM_TRIANGLE_SUB]) in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 < content(interval[a:real^M,b])` THENL
   [ALL_TAC;
    SUBGOAL_THEN `i:real^N = vec 0` SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_LE_MUL; NORM_0; CONTENT_POS_LE] THEN
    ASM_MESON_TAC[HAS_INTEGRAL_NULL_EQ; CONTENT_LT_NZ]] THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_integral]) THEN
  DISCH_THEN(MP_TAC o SPEC
    `norm(i:real^N) - B * content(interval[a:real^M,b])`) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d:real^M->real^M->bool`; `a:real^M`; `b:real^M`]
        FINE_DIVISION_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (X_CHOOSE_THEN `p:(real^M#(real^M->bool)->bool)` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:(real^M#(real^M->bool)->bool)`) THEN
  ASM_MESON_TAC[lemma; RSUM_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Similar theorems about relationship among components.                     *)
(* ------------------------------------------------------------------------- *)

let RSUM_COMPONENT_LE = prove
 (`!p a b f:real^M->real^N g:real^M->real^N.
       p tagged_division_of interval[a,b] /\ 1 <= i /\ i <= dimindex(:N) /\
       (!x. x IN interval[a,b] ==> (f x)$i <= (g x)$i)
       ==> vsum p (\(x,k). content k % f x)$i <=
           vsum p (\(x,k). content k % g x)$i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VSUM_COMPONENT] THEN
  MATCH_MP_TAC SUM_LE THEN
  ASM_SIMP_TAC[FORALL_PAIR_THM; VECTOR_MUL_COMPONENT] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  ASM_MESON_TAC[SUBSET; REAL_LE_LMUL; CONTENT_POS_LE]);;

let HAS_INTEGRAL_COMPONENT_LE = prove
 (`!f:real^M->real^N g:real^M->real^N s i j k.
        1 <= k /\ k <= dimindex(:N) /\
        (f has_integral i) s /\ (g has_integral j) s /\
        (!x. x IN s ==> (f x)$k <= (g x)$k)
        ==> i$k <= j$k`,
  SUBGOAL_THEN
   `!f:real^M->real^N g:real^M->real^N a b i j k.
        1 <= k /\ k <= dimindex(:N) /\
        (f has_integral i) (interval[a,b]) /\
        (g has_integral j) (interval[a,b]) /\
        (!x. x IN interval[a,b] ==> (f x)$k <= (g x)$k)
        ==> i$k <= j$k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `~(&0 < i - j) ==> i <= j`) THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `((i:real^N)$k - (j:real^N)$k) / &3` o
       GEN_REWRITE_RULE I [has_integral])) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?p. p tagged_division_of interval[a:real^M,b] /\
                      d1 fine p /\ d2 fine p`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM FINE_INTER] THEN MATCH_MP_TAC FINE_DIVISION_EXISTS THEN
      ASM_SIMP_TAC[GAUGE_INTER];
      ALL_TAC] THEN
    REPEAT
     (FIRST_X_ASSUM(MP_TAC o SPEC `p:real^M#(real^M->bool)->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
      DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP NORM_BOUND_COMPONENT_LE) THEN
      ASM_SIMP_TAC[VECTOR_SUB_COMPONENT]) THEN
    SUBGOAL_THEN
     `vsum p (\(x,l:real^M->bool). content l % (f:real^M->real^N) x)$k <=
      vsum p (\(x,l). content l % (g:real^M->real^N) x)$k`
    MP_TAC THENL
     [MATCH_MP_TAC RSUM_COMPONENT_LE THEN ASM_MESON_TAC[];
      UNDISCH_TAC `&0 < (i:real^N)$k - (j:real^N)$k` THEN
      SPEC_TAC(`vsum p (\(x:real^M,l:real^M->bool).
                                content l % (f x):real^N)$k`,
               `fs:real`) THEN
      SPEC_TAC(`vsum p (\(x:real^M,l:real^M->bool).
                                content l % (g x):real^N)$k`,
               `gs:real`) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[has_integral_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC
   `((i:real^N)$k - (j:real^N)$k) / &2`)) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC
   `ball(vec 0,B1) UNION ball(vec 0:real^M,B2)`
   BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[BOUNDED_UNION; BOUNDED_BALL; UNION_SUBSET; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  DISCH_THEN(CONJUNCTS_THEN(ANTE_RES_THEN MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^N)$k <= (w:real^N)$k` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(\x. if x IN s then f x else vec 0):real^M->real^N`;
      `(\x. if x IN s then g x else vec 0):real^M->real^N`;
      `a:real^M`; `b:real^M`] THEN
    ASM_MESON_TAC[REAL_LE_REFL];
    MP_TAC(ISPECL [`w - j:real^N`; `k:num`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`z - i:real^N`; `k:num`] COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; ASSUME `1 <= k`;
              ASSUME `k <= dimindex(:N)`] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LE])) THEN
    NORM_ARITH_TAC]);;

let INTEGRAL_COMPONENT_LE = prove
 (`!f:real^M->real^N g:real^M->real^N s k.
        1 <= k /\ k <= dimindex(:N) /\
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> (f x)$k <= (g x)$k)
        ==> (integral s f)$k <= (integral s g)$k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_LE THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_DROP_LE = prove
 (`!f:real^M->real^1 g:real^M->real^1 s i j.
        (f has_integral i) s /\ (g has_integral j) s /\
        (!x. x IN s ==> drop(f x) <= drop(g x))
        ==> drop i <= drop j`,
  REWRITE_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_LE THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN ASM_MESON_TAC[]);;

let INTEGRAL_DROP_LE = prove
 (`!f:real^M->real^1 g:real^M->real^1 s.
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> drop(f x) <= drop(g x))
        ==> drop(integral s f) <= drop(integral s g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_DROP_LE THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_COMPONENT_POS = prove
 (`!f:real^M->real^N s i k.
        1 <= k /\ k <= dimindex(:N) /\
        (f has_integral i) s /\
        (!x. x IN s ==> &0 <= (f x)$k)
        ==> &0 <= i$k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(\x. vec 0):real^M->real^N`; `f:real^M->real^N`;
                 `s:real^M->bool`; `vec 0:real^N`;
                 `i:real^N`; `k:num`] HAS_INTEGRAL_COMPONENT_LE) THEN
  ASM_SIMP_TAC[VEC_COMPONENT; HAS_INTEGRAL_0]);;

let INTEGRAL_COMPONENT_POS = prove
 (`!f:real^M->real^N s k.
        1 <= k /\ k <= dimindex(:N) /\
        f integrable_on s /\
        (!x. x IN s ==> &0 <= (f x)$k)
        ==> &0 <= (integral s f)$k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_POS THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_DROP_POS = prove
 (`!f:real^M->real^1 s i.
        (f has_integral i) s /\
        (!x. x IN s ==> &0 <= drop(f x))
        ==> &0 <= drop i`,
  REWRITE_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_POS THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN ASM_MESON_TAC[]);;

let INTEGRAL_DROP_POS = prove
 (`!f:real^M->real^1 s.
        f integrable_on s /\
        (!x. x IN s ==> &0 <= drop(f x))
        ==> &0 <= drop(integral s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_DROP_POS THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_COMPONENT_NEG = prove
 (`!f:real^M->real^N s i k.
        1 <= k /\ k <= dimindex(:N) /\
        (f has_integral i) s /\
        (!x. x IN s ==> (f x)$k <= &0)
        ==> i$k <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(\x. vec 0):real^M->real^N`;
                 `s:real^M->bool`; `i:real^N`; `vec 0:real^N`;
                 `k:num`] HAS_INTEGRAL_COMPONENT_LE) THEN
  ASM_SIMP_TAC[VEC_COMPONENT; HAS_INTEGRAL_0]);;

let HAS_INTEGRAL_DROP_NEG = prove
 (`!f:real^M->real^1 s i.
        (f has_integral i) s /\
        (!x. x IN s ==> drop(f x) <= &0)
        ==> drop i <= &0`,
  REWRITE_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_NEG THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN ASM_MESON_TAC[]);;

let HAS_INTEGRAL_COMPONENT_LBOUND = prove
 (`!f:real^M->real^N a b i k.
        (f has_integral i) (interval[a,b]) /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> B <= f(x)$k)
        ==> B * content(interval[a,b]) <= i$k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(\x. lambda i. B):real^M->real^N`; `f:real^M->real^N`;
                 `interval[a:real^M,b]`;
                 `content(interval[a:real^M,b]) % (lambda i. B):real^N`;
                 `i:real^N`; `k:num`]
                HAS_INTEGRAL_COMPONENT_LE) THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; LAMBDA_BETA; HAS_INTEGRAL_CONST] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let HAS_INTEGRAL_COMPONENT_UBOUND = prove
 (`!f:real^M->real^N a b i k.
        (f has_integral i) (interval[a,b]) /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> f(x)$k <= B)
        ==> i$k <= B * content(interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(\x. lambda i. B):real^M->real^N`;
                 `interval[a:real^M,b]`; `i:real^N`;
                 `content(interval[a:real^M,b]) % (lambda i. B):real^N`;
                 `k:num`]
                HAS_INTEGRAL_COMPONENT_LE) THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; LAMBDA_BETA; HAS_INTEGRAL_CONST] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let INTEGRAL_COMPONENT_LBOUND = prove
 (`!f:real^M->real^N a b k.
        f integrable_on interval[a,b] /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> B <= f(x)$k)
        ==> B * content(interval[a,b]) <= (integral(interval[a,b]) f)$k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_LBOUND THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

let INTEGRAL_COMPONENT_UBOUND = prove
 (`!f:real^M->real^N a b k.
        f integrable_on interval[a,b] /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> f(x)$k <= B)
        ==> (integral(interval[a,b]) f)$k <= B * content(interval[a,b])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_UBOUND THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

(* ------------------------------------------------------------------------- *)
(* Uniform limit of integrable functions is integrable.                      *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_UNIFORM_LIMIT = prove
 (`!f a b. (!e. &0 < e
                ==> ?g. (!x. x IN interval[a,b] ==> norm(f x - g x) <= e) /\
                        g integrable_on interval[a,b] )
           ==> (f:real^M->real^N) integrable_on interval[a,b]`,
  let lemma = prove
   (`x <= norm(a + b) + c ==> x <= norm(a) + norm(b) + c`,
    MESON_TAC[REAL_ADD_AC; NORM_TRIANGLE; REAL_LE_TRANS; REAL_LE_RADD]) in
  let (lemma1,lemma2) = (CONJ_PAIR o prove)
   (`(norm(s2 - s1) <= e / &2 /\
      norm(s1 - i1) < e / &4 /\ norm(s2 - i2) < e / &4
      ==> norm(i1 - i2) < e) /\
     (norm(sf - sg) <= e / &3
      ==> norm(i - s) < e / &3 ==> norm(sg - i) < e / &3 ==> norm(sf - s) < e)`,
    CONJ_TAC THENL
     [REWRITE_TAC[CONJ_ASSOC] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [NORM_SUB] THEN
      MATCH_MP_TAC(REAL_ARITH
       `w <= x + y + z + &0
        ==> (x <= e / &2 /\ y < e / &4) /\ z < e / &4 ==> w < e`);
      MATCH_MP_TAC(REAL_ARITH
      `w <= x + y + z + &0
      ==> x <= e / &3 ==> y < e / &3 ==> z < e / &3 ==> w < e`)] THEN
    REPEAT(MATCH_MP_TAC lemma) THEN REWRITE_TAC[REAL_ADD_RID] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 < content(interval[a:real^M,b])` THENL
   [ALL_TAC;
    ASM_MESON_TAC[HAS_INTEGRAL_NULL; CONTENT_LT_NZ; integrable_on]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[FORALL_AND_THM; SKOLEM_THM; integrable_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->real^M->real^N` (CONJUNCTS_THEN2
   ASSUME_TAC (X_CHOOSE_TAC `i:num->real^N`))) THEN
  SUBGOAL_THEN `cauchy(i:num->real^N)` MP_TAC THENL
   [REWRITE_TAC[cauchy] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e / &4 / content(interval[a:real^M,b])`
        REAL_ARCH_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN REWRITE_TAC[GE] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [has_integral]) THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `m:num` th) THEN
      MP_TAC(SPEC `n:num` th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `gn:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `gm:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`(\x. gm(x) INTER gn(x)):real^M->real^M->bool`;
                   `a:real^M`; `b:real^M`] FINE_DIVISION_EXISTS) THEN
    ASM_SIMP_TAC[GAUGE_INTER; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `p:(real^M#(real^M->bool))->bool` THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `p:(real^M#(real^M->bool))->bool`)) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[CONV_RULE(REWR_CONV FINE_INTER) th]) THEN
    SUBGOAL_THEN `norm(vsum p (\(x,k:real^M->bool). content k % g (n:num) x) -
                       vsum p (\(x:real^M,k). content k % g m x :real^N))
                  <= e / &2`
    MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[dist] THEN MESON_TAC[lemma1]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 / &N * content(interval[a:real^M,b])` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RSUM_DIFF_BOUND;
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
      ASM_REAL_ARITH_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`n:num`; `x:real^M`] th) THEN
      MP_TAC(SPECL [`m:num`; `x:real^M`] th)) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [NORM_SUB] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_ADD2) THEN
    DISCH_THEN(MP_TAC o MATCH_MP NORM_TRIANGLE_LE) THEN
    MATCH_MP_TAC(REAL_ARITH `u = v /\ a <= inv(x) /\ b <= inv(x) ==>
                                u <= a + b ==> v <= &2 / x`) THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[has_integral] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &3` o GEN_REWRITE_RULE I
   [LIM_SEQUENTIALLY]) THEN
  ASM_SIMP_TAC[dist; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MP_TAC(SPEC `e / &3 / content(interval[a:real^M,b])` REAL_ARCH_INV) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [has_integral]) THEN
  DISCH_THEN(MP_TAC o SPECL [`N1 + N2:num`; `e / &3`]) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:real^M#(real^M->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ARITH_RULE `N1:num <= N1 + N2`)) THEN
  MATCH_MP_TAC lemma2 THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&(N1 + N2) + &1) * content(interval[a:real^M,b])` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RSUM_DIFF_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x < a ==> y <= x ==> y <= a`)) THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Negligible sets.                                                          *)
(* ------------------------------------------------------------------------- *)

let indicator = new_definition
  `indicator s :real^M->real^1 = \x. if x IN s then vec 1 else vec 0`;;

let DROP_INDICATOR = prove
 (`!s x. drop(indicator s x) = if x IN s then &1 else &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[indicator] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DROP_VEC]);;

let DROP_INDICATOR_POS_LE = prove
 (`!s x. &0 <= drop(indicator s x)`,
  REWRITE_TAC[DROP_INDICATOR] THEN REAL_ARITH_TAC);;

let DROP_INDICATOR_LE_1 = prove
 (`!s x. drop(indicator s x) <= &1`,
  REWRITE_TAC[DROP_INDICATOR] THEN REAL_ARITH_TAC);;

let DROP_INDICATOR_ABS_LE_1 = prove
 (`!s x. abs(drop(indicator s x)) <= &1`,
  REWRITE_TAC[DROP_INDICATOR] THEN REAL_ARITH_TAC);;

let negligible = new_definition
 `negligible s <=> !a b. (indicator s has_integral (vec 0)) (interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Negligibility of hyperplane.                                              *)
(* ------------------------------------------------------------------------- *)

let VSUM_NONZERO_IMAGE_LEMMA = prove
 (`!s f:A->B g:B->real^N a.
        FINITE s /\ g(a) = vec 0 /\
        (!x y. x IN s /\ y IN s /\ f x = f y /\ ~(x = y) ==> g(f x) = vec 0)
       ==> vsum {f x |x| x IN s /\ ~(f x = a)} g =
           vsum s (g o f)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {(f:A->B) x |x| x IN s /\ ~(f x = a)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `IMAGE (f:A->B) s` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ASM_SIMP_TAC[VSUM] THEN MATCH_MP_TAC ITERATE_NONZERO_IMAGE_LEMMA THEN
    ASM_REWRITE_TAC[NEUTRAL_VECTOR_ADD; MONOIDAL_VECTOR_ADD]]);;

let INTERVAL_DOUBLESPLIT = prove
 (`1 <= k /\ k <= dimindex(:N)
      ==> interval[a,b] INTER {x:real^N | abs(x$k - c) <= e} =
          interval[(lambda i. if i = k then max (a$k) (c - e) else a$i),
                   (lambda i. if i = k then min (b$k) (c + e) else b$i)]`,
   REWRITE_TAC[REAL_ARITH `abs(x - c) <= e <=> x >= c - e /\ x <= c + e`] THEN
   REWRITE_TAC[SET_RULE `s INTER {x | P x /\ Q x} =
                        (s INTER {x | Q x}) INTER {x | P x}`] THEN
   SIMP_TAC[INTERVAL_SPLIT]);;

let DIVISION_DOUBLESPLIT = prove
 (`!p a b:real^N k c e.
        p division_of interval[a,b] /\ 1 <= k /\ k <= dimindex(:N)
        ==> {l INTER {x | abs(x$k - c) <= e} |l|
                l IN p /\ ~(l INTER {x | abs(x$k - c) <= e} = {})}
            division_of (interval[a,b] INTER {x | abs(x$k - c) <= e})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `c + e:real` o MATCH_MP DIVISION_SPLIT) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
  FIRST_ASSUM MP_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (TAUT
   `(a /\ b /\ c) /\ d ==> d /\ b /\ c`)) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `c - e:real` o
    MATCH_MP DIVISION_SPLIT) THEN
  ASM_SIMP_TAC[INTERVAL_DOUBLESPLIT; INTERVAL_SPLIT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_ARITH `abs(x - c) <= e <=> x >= c - e /\ x <= c + e`] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  GEN_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> c /\ a /\ b /\ d`] THEN
  REWRITE_TAC[UNWIND_THM2] THEN AP_TERM_TAC THEN ABS_TAC THEN SET_TAC[]);;

let CONTENT_DOUBLESPLIT = prove
 (`!a b:real^N k c e.
        &0 < e /\ 1 <= k /\ k <= dimindex(:N)
        ==> ?d. &0 < d /\
                content(interval[a,b] INTER {x | abs(x$k - c) <= d}) < e`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^N,b]) = &0` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `content(interval[a:real^N,b])` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM(K ALL_TAC o SYM); ASM_REWRITE_TAC[]] THEN
    ASM_SIMP_TAC[INTERVAL_DOUBLESPLIT] THEN MATCH_MP_TAC CONTENT_SUBSET THEN
    ASM_SIMP_TAC[GSYM INTERVAL_DOUBLESPLIT] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CONTENT_EQ_0]) THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < product ((1..dimindex (:N)) DELETE k)
                              (\i. (b:real^N)$i - (a:real^N)$i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT THEN
    ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG; IN_DELETE; IN_NUMSEG;
                 REAL_SUB_LT];
    ALL_TAC] THEN
  ABBREV_TAC `d = e / &3 / product ((1..dimindex (:N)) DELETE k)
                                   (\i. (b:real^N)$i - (a:real^N)$i)` THEN
  EXISTS_TAC `d:real` THEN SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[content; INTERVAL_DOUBLESPLIT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [INTERVAL_NE_EMPTY]) THEN
  SUBGOAL_THEN `1..dimindex(:N) = k INSERT ((1..dimindex(:N)) DELETE k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_NUMSEG] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG; FINITE_DELETE; IN_DELETE] THEN
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND; REAL_LT_IMP_LE;
                LAMBDA_BETA; IN_DELETE; IN_NUMSEG] THEN
  SUBGOAL_THEN
   `product ((1..dimindex (:N)) DELETE k)
     (\j. ((lambda i. if i = k then min (b$k) (c + d) else b$i):real^N)$j -
          ((lambda i. if i = k then max (a$k) (c - d) else a$i):real^N)$j) =
    product ((1..dimindex (:N)) DELETE k)
            (\i. (b:real^N)$i - (a:real^N)$i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN
    SIMP_TAC[IN_DELETE; IN_NUMSEG; LAMBDA_BETA];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * d` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < d /\ &3 * d <= x ==> &2 * d < x`) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "d" THEN REAL_ARITH_TAC);;

let NEGLIGIBLE_STANDARD_HYPERPLANE = prove
 (`!c k. 1 <= k /\ k <= dimindex(:N) ==> negligible {x:real^N | x$k = c}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[negligible; has_integral] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `k:num`; `c:real`; `e:real`]
        CONTENT_DOUBLESPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `\x:real^N. ball(x,d)` THEN ASM_SIMP_TAC[GAUGE_BALL] THEN
  ABBREV_TAC `i = indicator {x:real^N | x$k = c}` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum p (\(x,l). content l % i x) =
    vsum p (\(x,l). content(l INTER {x:real^N | abs(x$k - c) <= d}) %
                    (i:real^N->real^1) x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `l:real^N->bool`] THEN
    DISCH_TAC THEN EXPAND_TAC "i" THEN REWRITE_TAC[indicator] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `l:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> l SUBSET s ==> l = l INTER t`) THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM; dist] THEN
    UNDISCH_THEN `(x:real^N)$k = c` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
   `norm(vsum p (\(x:real^N,l).
          content(l INTER {x:real^N | abs(x$k - c) <= d}) %
         vec 1:real^1))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[VSUM_REAL; NORM_LIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs(x) <= abs(y)`) THEN
    REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM; DROP_CMUL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE; MATCH_MP_TAC SUM_LE] THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `l:real^N->bool`] THEN STRIP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_LMUL] THEN
    EXPAND_TAC "i" THEN REWRITE_TAC[DROP_VEC] THEN
    REWRITE_TAC[DROP_INDICATOR_POS_LE; DROP_INDICATOR_LE_1] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `l:real^N->bool`] o
        el 1 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[INTERVAL_DOUBLESPLIT; CONTENT_POS_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(\l. content (l INTER {x | abs (x$k - c) <= d}) % vec 1):
                  (real^N->bool)->real^1`;
                 `p:real^N#(real^N->bool)->bool`;
                 `interval[a:real^N,b]`]
        VSUM_OVER_TAGGED_DIVISION_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!x. x = &0 /\ &0 <= y /\ y <= x ==> y = &0`) THEN
    EXISTS_TAC `content(interval[u:real^N,v])` THEN
    CONJ_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN
    DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[CONTENT_POS_LE; INTERVAL_DOUBLESPLIT] THEN
    MATCH_MP_TAC CONTENT_SUBSET THEN
    ASM_SIMP_TAC[GSYM INTERVAL_DOUBLESPLIT] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
     [`IMAGE SND (p:real^N#(real^N->bool)->bool)`;
      `\l. l INTER {x:real^N | abs (x$k - c) <= d}`;
      `\l:real^N->bool. content l % vec 1 :real^1`;
      `{}:real^N->bool`] VSUM_NONZERO_IMAGE_LEMMA) THEN
    REWRITE_TAC[o_DEF] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_TAGGED_DIVISION) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_FINITE]; ALL_TAC] THEN
    REWRITE_TAC[CONTENT_EMPTY; VECTOR_MUL_LZERO] THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
    X_GEN_TAC `m:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    SIMP_TAC[INTERVAL_DOUBLESPLIT; ASSUME `1 <= k`;
             ASSUME `k <= dimindex(:N)`] THEN
    REWRITE_TAC[CONTENT_EQ_0_INTERIOR] THEN
    ASM_SIMP_TAC[GSYM INTERVAL_DOUBLESPLIT] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MP_TAC o SPECL [`interval[u:real^N,v]`; `m:real^N->bool`] o
      el 2 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
      `u SUBSET s /\ u SUBSET t ==> s INTER t = {} ==> u = {}`) THEN
    CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC
   `&1 * content(interval[a,b] INTER {x:real^N | abs (x$k - c) <= d})` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_MUL_LID]] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
    DIVISION_DOUBLESPLIT)) THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`; `c:real`; `d:real`]) THEN
  ASM_SIMP_TAC[INTERVAL_DOUBLESPLIT] THEN DISCH_TAC THEN
  MATCH_MP_TAC DSUM_BOUND THEN
  ASM_SIMP_TAC[NORM_REAL; VEC_COMPONENT; DIMINDEX_1; LE_REFL] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A technical lemma about "refinement" of division.                         *)
(* ------------------------------------------------------------------------- *)

let TAGGED_DIVISION_FINER = prove
 (`!p a b:real^N d. p tagged_division_of interval[a,b] /\ gauge d
             ==> ?q. q tagged_division_of interval[a,b] /\ d fine q /\
                     !x k. (x,k) IN p /\ k SUBSET d(x) ==> (x,k) IN q`,
  let lemma1 = prove
   (`{k | ?x. (x,k) IN p} = IMAGE SND p`,
    REWRITE_TAC[EXTENSION; EXISTS_PAIR_THM; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[]) in
  SUBGOAL_THEN
   `!a b:real^N d p.
       FINITE p
       ==> p tagged_partial_division_of interval[a,b] /\ gauge d
           ==> ?q. q tagged_division_of (UNIONS {k | ?x. x,k IN p}) /\
                   d fine q /\
                   !x k. (x,k) IN p /\ k SUBSET d(x) ==> (x,k) IN q`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [tagged_division_of] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    ASM_MESON_TAC[tagged_partial_division_of]] THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[SET_RULE `UNIONS {k | ?x. x,k IN {}} = {}`] THEN
    EXISTS_TAC `{}:real^N#(real^N->bool)->bool` THEN
    REWRITE_TAC[fine; NOT_IN_EMPTY; TAGGED_DIVISION_OF_EMPTY];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC
   [`x:real^N`; `k:real^N->bool`; `p:real^N#(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TAGGED_PARTIAL_DIVISION_SUBSET THEN
    EXISTS_TAC `(x:real^N,k:real^N->bool) INSERT p` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:real^N#(real^N->bool)->bool`
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `UNIONS {l:real^N->bool | ?y:real^N. (y,l) IN (x,k) INSERT p} =
    k UNION UNIONS {l | ?y. (y,l) IN p}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNION; IN_UNIONS] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u v:real^N. k = interval[u,v]` MP_TAC THENL
   [ASM_MESON_TAC[IN_INSERT; tagged_partial_division_of]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  ASM_CASES_TAC `interval[u,v] SUBSET ((d:real^N->real^N->bool) x)` THENL
   [EXISTS_TAC `{(x:real^N,interval[u:real^N,v])} UNION q1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC TAGGED_DIVISION_UNION THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TAGGED_DIVISION_OF_SELF THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
         [tagged_partial_division_of]) THEN
        REWRITE_TAC[IN_INSERT; PAIR_EQ] THEN MESON_TAC[];
        ALL_TAC];
      CONJ_TAC THENL
       [MATCH_MP_TAC FINE_UNION THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[fine; IN_SING; PAIR_EQ] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INSERT; PAIR_EQ; IN_UNION; IN_SING] THEN
      ASM_MESON_TAC[]];
    FIRST_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`] o MATCH_MP
      FINE_DIVISION_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `q2:real^N#(real^N->bool)->bool`
      STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q2 UNION q1:real^N#(real^N->bool)->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC TAGGED_DIVISION_UNION THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[FINE_UNION] THEN
      ASM_REWRITE_TAC[IN_INSERT; PAIR_EQ; IN_UNION; IN_SING] THEN
      ASM_MESON_TAC[]]] THEN
  (MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
   REWRITE_TAC[lemma1; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [tagged_partial_division_of]) THEN
   REWRITE_TAC[IN_INSERT; FINITE_INSERT; PAIR_EQ] THEN
   STRIP_TAC THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN CONJ_TAC THENL
    [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; OPEN_INTERVAL]; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_MESON_TAC[]));;

(* ------------------------------------------------------------------------- *)
(* Hence the main theorem about negligible sets.                             *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_NEGLIGIBLE = prove
 (`!f:real^M->real^N s t.
        negligible s /\ (!x. x IN (t DIFF s) ==> f x = vec 0)
        ==> (f has_integral (vec 0)) t`,
  let lemma = prove
   (`!f:B->real g:A#B->real s t.
          FINITE s /\ FINITE t /\
          (!x y. (x,y) IN t ==> &0 <= g(x,y)) /\
          (!y. y IN s ==> ?x. (x,y) IN t /\ f(y) <= g(x,y))
          ==> sum s f <= sum t g`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_LE_INCLUDED THEN
    EXISTS_TAC `SND:A#B->B` THEN
    REWRITE_TAC[EXISTS_PAIR_THM; FORALL_PAIR_THM] THEN
    ASM_MESON_TAC[]) in
  SUBGOAL_THEN
   `!f:real^M->real^N s a b.
        negligible s /\ (!x. ~(x IN s) ==> f x = vec 0)
        ==> (f has_integral (vec 0)) (interval[a,b])`
  ASSUME_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[has_integral_alt] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
      EXISTS_TAC `\x. if x IN t then (f:real^M->real^N) x else vec 0` THEN
      SIMP_TAC[] THEN
      FIRST_X_ASSUM(CHOOSE_THEN(CHOOSE_THEN SUBST_ALL_TAC)) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `vec 0:real^N` THEN
    ASM_REWRITE_TAC[NORM_0; VECTOR_SUB_REFL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_MESON_TAC[]] THEN
  REWRITE_TAC[negligible; has_integral; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MAP_EVERY(fun t -> MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC t)
   [`a:real^M`; `b:real^M`] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN `n:num` o
      SPEC `e / &2 / ((&n + &1) * &2 pow n)`) THEN
  REWRITE_TAC[real_div; REAL_MUL_POS_LT] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_LT_MUL; REAL_POW_LT; REAL_OF_NUM_LT;
           FORALL_AND_THM; ARITH; REAL_ARITH `&0 < &n + &1`; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. (d:num->real^M->real^M->bool)
                  (num_of_int(int_of_real(floor(norm(f x:real^N))))) x` THEN
  CONJ_TAC THENL [REWRITE_TAC[gauge] THEN ASM_MESON_TAC[gauge]; ALL_TAC] THEN
  X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_CASES_TAC `p:real^M#(real^M->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES; NORM_0] THEN
  MP_TAC(SPEC `sup(IMAGE (\(x,k:real^M->bool). norm((f:real^M->real^N) x)) p)`
    REAL_ARCH_SIMPLE) THEN
  ASM_SIMP_TAC[REAL_SUP_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MP_TAC(GEN `i:num`
   (ISPECL [`p:real^M#(real^M->bool)->bool`; `a:real^M`; `b:real^M`;
                `(d:num->real^M->real^M->bool) i`]
                TAGGED_DIVISION_FINER)) THEN
  ASM_REWRITE_TAC[SKOLEM_THM; RIGHT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->real^M#(real^M->bool)->bool`
        STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
   `sum(0..N+1) (\i. (&i + &1) *
                     norm(vsum (q i) (\(x:real^M,k:real^M->bool).
                                            content k % indicator s x)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum (0..N+1) (\i. e / &2 / &2 pow i)` THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[real_div; SUM_LMUL; GSYM REAL_POW_INV] THEN
      REWRITE_TAC[SUM_GP; LT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_ARITH `(e * &1 / &2) * (&1 - x) / (&1 / &2) < e <=>
                                &0 < e * x`] THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_ARITH `&0 < &1 / &2`]] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN REWRITE_TAC[GSYM real_div] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(ASSUME_TAC o GEN `i:num` o
    MATCH_MP TAGGED_DIVISION_OF_FINITE o SPEC `i:num`) THEN
  ASM_SIMP_TAC[VSUM_REAL; NORM_LIFT] THEN
  REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM; DROP_CMUL] THEN
  REWRITE_TAC[real_abs] THEN
  SUBGOAL_THEN
   `!i:num. &0 <= sum (q i) (\(x:real^M,y:real^M->bool).
              content y * drop (indicator s x))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[DROP_INDICATOR_POS_LE] THEN
    ASM_MESON_TAC[TAGGED_DIVISION_OF; CONTENT_POS_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM SUM_LMUL] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> n <= x ==> n <= y`) THEN
  ASM_SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC lemma THEN
  ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FORALL_PAIR_THM; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL] THEN
    REWRITE_TAC[DROP_INDICATOR_POS_LE] THEN
    ASM_MESON_TAC[TAGGED_DIVISION_OF; CONTENT_POS_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `k:real^M->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC
   `n = num_of_int(int_of_real(floor(norm((f:real^M->real^N) x))))` THEN
  SUBGOAL_THEN `&n <= norm((f:real^M->real^N) x) /\
                norm(f x) < &n + &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&n = floor(norm((f:real^M->real^N) x))`
     (fun th -> MESON_TAC[th; FLOOR]) THEN
    EXPAND_TAC "n" THEN
    MP_TAC(ISPEC `norm((f:real^M->real^N) x)` FLOOR_POS) THEN
    REWRITE_TAC[NORM_POS_LE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `m:num` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM int_of_num; NUM_OF_INT_OF_NUM];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[IN_NUMSEG; LE_0] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((f:real^M->real^N) x)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= n ==> x <= n + &1`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_SIMP_TAC[indicator] THEN
  REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; NORM_0;
              VECTOR_MUL_RZERO; REAL_LE_REFL] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[DROP_VEC; REAL_MUL_RID; NORM_MUL] THEN
  SUBGOAL_THEN `&0 <= content(k:real^M->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[TAGGED_DIVISION_OF; CONTENT_POS_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[real_abs] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let HAS_INTEGRAL_SPIKE = prove
 (`!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x) /\
        (f has_integral y) t
        ==> (g has_integral y) t`,
  SUBGOAL_THEN
   `!f:real^M->real^N g s a b y.
        negligible s /\ (!x. x IN (interval[a,b] DIFF s) ==> g x = f x)
        ==> (f has_integral y) (interval[a,b])
            ==> (g has_integral y) (interval[a,b])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `((\x. (f:real^M->real^N)(x) + (g(x) - f(x))) has_integral (y + vec 0))
      (interval[a,b])`
    MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[VECTOR_ARITH `f + g - f = g /\ f + vec 0 = f`; ETA_AX]] THEN
    MATCH_MP_TAC HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_INTEGRAL_NEGLIGIBLE THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[has_integral_alt] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(CHOOSE_THEN(CHOOSE_THEN SUBST_ALL_TAC)) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:real^M->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let HAS_INTEGRAL_SPIKE_EQ = prove
 (`!f:real^M->real^N g s t y.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> ((f has_integral y) t <=> (g has_integral y) t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THENL
   [EXISTS_TAC `f:real^M->real^N`; EXISTS_TAC `g:real^M->real^N`] THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[NORM_SUB]);;

let INTEGRABLE_SPIKE = prove
 (`!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> f integrable_on t ==> g integrable_on  t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_INTEGRAL_SPIKE) THEN ASM_REWRITE_TAC[]);;

let INTEGRABLE_SPIKE_EQ = prove
 (`!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN t DIFF s ==> g x = f x)
        ==> (f integrable_on t <=> g integrable_on t)`,
  MESON_TAC[INTEGRABLE_SPIKE]);;

let INTEGRAL_SPIKE = prove
 (`!f:real^M->real^N g s t y.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> integral t f = integral t g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_EQ THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some other trivialities about negligible sets.                            *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_SUBSET = prove
 (`!s:real^N->bool t:real^N->bool.
        negligible s /\ t SUBSET s ==> negligible t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[negligible] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  MAP_EVERY EXISTS_TAC [`(\x. vec 0):real^N->real^1`; `s:real^N->bool`] THEN
  ASM_REWRITE_TAC[HAS_INTEGRAL_0] THEN
  REWRITE_TAC[indicator] THEN ASM SET_TAC[]);;

let NEGLIGIBLE_DIFF = prove
 (`!s t:real^N->bool. negligible s ==> negligible(s DIFF t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_DIFF]);;

let NEGLIGIBLE_INTER = prove
 (`!s t. negligible s \/ negligible t ==> negligible(s INTER t)`,
  MESON_TAC[NEGLIGIBLE_SUBSET; INTER_SUBSET]);;

let NEGLIGIBLE_UNION = prove
 (`!s t:real^N->bool.
        negligible s /\ negligible t ==> negligible (s UNION t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MP_TAC THEN
  REWRITE_TAC[negligible; AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `b:real^N` THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_ADD) THEN
  REWRITE_TAC[VECTOR_ADD_LID] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE_EQ THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[indicator; IN_UNION; IN_DIFF; VECTOR_ADD_LID]);;

let NEGLIGIBLE_UNION_EQ = prove
 (`!s t:real^N->bool.
        negligible (s UNION t) <=> negligible s /\ negligible t`,
  MESON_TAC[NEGLIGIBLE_UNION; SUBSET_UNION; NEGLIGIBLE_SUBSET]);;

let NEGLIGIBLE_SING = prove
 (`!a:real^N. negligible {a}`,
  GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x | (x:real^N)$1 = (a:real^N)$1}` THEN
  SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE; LE_REFL; DIMINDEX_GE_1] THEN
  SET_TAC[]);;

let NEGLIGIBLE_INSERT = prove
 (`!a:real^N s. negligible(a INSERT s) <=> negligible s`,
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  REWRITE_TAC[NEGLIGIBLE_UNION_EQ; NEGLIGIBLE_SING]);;

let NEGLIGIBLE_EMPTY = prove
 (`negligible {}`,
  MESON_TAC[EMPTY_SUBSET; NEGLIGIBLE_SUBSET; NEGLIGIBLE_SING]);;

let NEGLIGIBLE_FINITE = prove
 (`!s. FINITE s ==> negligible s`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NEGLIGIBLE_EMPTY; NEGLIGIBLE_INSERT]);;

let NEGLIGIBLE_UNIONS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> negligible t)
       ==> negligible(UNIONS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; NEGLIGIBLE_EMPTY; IN_INSERT] THEN
  SIMP_TAC[NEGLIGIBLE_UNION]);;

let NEGLIGIBLE = prove
 (`!s:real^N->bool. negligible s <=> !t. (indicator s has_integral vec 0) t`,
  GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; REWRITE_TAC[negligible] THEN SIMP_TAC[]] THEN
  DISCH_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[has_integral_alt] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[negligible]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `vec 0:real^1` THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `s INTER t:real^N->bool`]
        NEGLIGIBLE_SUBSET) THEN
  ASM_REWRITE_TAC[INTER_SUBSET; negligible; VECTOR_SUB_REFL; NORM_0] THEN
  REWRITE_TAC[indicator; IN_INTER] THEN
  SIMP_TAC[TAUT `(if p /\ q then r else s) =
                 (if q then if p then r else s else s)`]);;

(* ------------------------------------------------------------------------- *)
(* Finite or empty cases of the spike theorem are quite commonly needed.     *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_SPIKE_FINITE = prove
 (`!f:real^M->real^N g s t y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x) /\
        (f has_integral y) t
        ==> (g has_integral y) t`,
  MESON_TAC[HAS_INTEGRAL_SPIKE; NEGLIGIBLE_FINITE]);;

let HAS_INTEGRAL_SPIKE_FINITE_EQ = prove
 (`!f:real^M->real^N g s y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> ((f has_integral y) t <=> (g has_integral y) t)`,
  MESON_TAC[HAS_INTEGRAL_SPIKE_FINITE]);;

let INTEGRABLE_SPIKE_FINITE = prove
 (`!f:real^M->real^N g s.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> f integrable_on t
            ==> g integrable_on  t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_INTEGRAL_SPIKE_FINITE) THEN ASM_REWRITE_TAC[]);;

let INTEGRAL_EQ = prove
 (`!f:real^M->real^N g s.
        (!x. x IN s ==> f x = g x) ==> integral s f = integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{}:real^M->bool` THEN ASM_SIMP_TAC[NEGLIGIBLE_EMPTY; IN_DIFF]);;

let INTEGRAL_EQ_0 = prove
 (`!f:real^M->real^N s. (!x. x IN s ==> f x = vec 0) ==> integral s f = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral s ((\x. vec 0):real^M->real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INTEGRAL_0]]);;

(* ------------------------------------------------------------------------- *)
(* In particular, the boundary of an interval is negligible.                 *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_FRONTIER_INTERVAL = prove
 (`!a b:real^N. negligible(interval[a,b] DIFF interval(a,b))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `UNIONS (IMAGE (\k. {x:real^N | x$k = (a:real^N)$k} UNION
                                 {x:real^N | x$k = (b:real^N)$k})
                            (1..dimindex(:N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
    SIMP_TAC[IN_NUMSEG; NEGLIGIBLE_UNION_EQ; NEGLIGIBLE_STANDARD_HYPERPLANE];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_INTERVAL; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[IN_NUMSEG; IN_UNION; IN_ELIM_THM; REAL_LT_LE] THEN
    MESON_TAC[]]);;

let HAS_INTEGRAL_SPIKE_INTERIOR = prove
 (`!f:real^M->real^N g a b y.
        (!x. x IN interval(a,b) ==> g x = f x) /\
        (f has_integral y) (interval[a,b])
        ==> (g has_integral y) (interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                           HAS_INTEGRAL_SPIKE) THEN
  EXISTS_TAC `interval[a:real^M,b] DIFF interval(a,b)` THEN
  REWRITE_TAC[NEGLIGIBLE_FRONTIER_INTERVAL] THEN ASM SET_TAC[]);;

let HAS_INTEGRAL_SPIKE_INTERIOR_EQ = prove
 (`!f:real^M->real^N g a b y.
        (!x. x IN interval(a,b) ==> g x = f x)
        ==> ((f has_integral y) (interval[a,b]) <=>
             (g has_integral y) (interval[a,b]))`,
  MESON_TAC[HAS_INTEGRAL_SPIKE_INTERIOR]);;

let INTEGRABLE_SPIKE_INTERIOR = prove
 (`!f:real^M->real^N g a b.
        (!x. x IN interval(a,b) ==> g x = f x)
        ==> f integrable_on (interval[a,b])
            ==> g integrable_on  (interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_INTEGRAL_SPIKE_INTERIOR) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Integrability of continuous functions.                                    *)
(* ------------------------------------------------------------------------- *)

let NEUTRAL_AND = prove
 (`neutral(/\) = T`,
  REWRITE_TAC[neutral; FORALL_BOOL_THM] THEN MESON_TAC[]);;

let MONOIDAL_AND = prove
 (`monoidal(/\)`,
  REWRITE_TAC[monoidal; NEUTRAL_AND; CONJ_ACI]);;

let ITERATE_AND = prove
 (`!p s. FINITE s ==> (iterate(/\) s p <=> !x. x IN s ==> p x)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[MONOIDAL_AND; NEUTRAL_AND; ITERATE_CLAUSES] THEN SET_TAC[]);;

let OPERATIVE_DIVISION_AND = prove
 (`!P d a b. operative(/\) P /\ d division_of interval[a,b]
             ==> ((!i. i IN d ==> P i) <=> P(interval[a,b]))`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o CONJ MONOIDAL_AND) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPERATIVE_DIVISION) THEN
  ASM_MESON_TAC[ITERATE_AND; DIVISION_OF_FINITE]);;

let OPERATIVE_APPROXIMABLE = prove
 (`!f:real^M->real^N e.
        &0 <= e
        ==> operative(/\)
               (\i. ?g. (!x. x IN i ==> norm (f x - g x) <= e) /\
                        g integrable_on i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[operative; NEUTRAL_AND] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `f:real^M->real^N` THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; integrable_on] THEN
    ASM_MESON_TAC[HAS_INTEGRAL_NULL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`; `c:real`; `k:num`] THEN
  STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_SPLIT; IN_INTER]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `g1:real^M->real^N` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `g2:real^M->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x. if x$k = c then (f:real^M->real^N)(x) else
                  if x$k <= c then g1(x) else g2(x)` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_ELIM_THM]) THEN
    ASM_MESON_TAC[REAL_ARITH `x <= c \/ x >= c`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^M. if x$k = c then f x else if x$k <= c then g1 x else g2 x)
    integrable_on (interval[u,v] INTER {x | x$k <= c}) /\
    (\x. if x$k = c then f x :real^N else if x$k <= c then g1 x else g2 x)
    integrable_on (interval[u,v] INTER {x | x$k >= c})`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[integrable_on] THEN ASM_MESON_TAC[HAS_INTEGRAL_SPLIT]] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC
     `(g1:real^M->real^N) integrable_on (interval[u,v] INTER {x | x$k <= c})`;
    UNDISCH_TAC
    `(g2:real^M->real^N) integrable_on (interval[u,v] INTER {x | x$k >= c})`
   ] THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MATCH_MP_TAC INTEGRABLE_SPIKE THEN
  ASM_SIMP_TAC[GSYM INTERVAL_SPLIT] THEN
  EXISTS_TAC `{x:real^M | x$k = c}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE; IN_DIFF; IN_INTER; IN_ELIM_THM;
               REAL_ARITH `x >= c /\ ~(x = c) ==> ~(x <= c)`] THEN
  EXISTS_TAC `e:real` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]);;

let APPROXIMABLE_ON_DIVISION = prove
 (`!f:real^M->real^N d a b.
        &0 <= e /\
        (d division_of interval[a,b]) /\
        (!i. i IN d
             ==> ?g. (!x. x IN i ==> norm (f x - g x) <= e) /\
                     g integrable_on i)
        ==> ?g. (!x. x IN interval[a,b] ==> norm (f x - g x) <= e) /\
                g integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(/\)`; `d:(real^M->bool)->bool`;
                 `a:real^M`; `b:real^M`;
                 `\i. ?g:real^M->real^N.
                       (!x. x IN i ==> norm (f x - g x) <= e) /\
                       g integrable_on i`]
                OPERATIVE_DIVISION) THEN
  ASM_SIMP_TAC[OPERATIVE_APPROXIMABLE; MONOIDAL_AND] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[ITERATE_AND]);;

let INTEGRABLE_CONTINUOUS = prove
 (`!f:real^M->real^N a b.
        f continuous_on interval[a,b] ==> f integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_UNIFORM_LIMIT THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC APPROXIMABLE_ON_DIVISION THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    COMPACT_UNIFORMLY_CONTINUOUS)) THEN
  REWRITE_TAC[COMPACT_INTERVAL; uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[dist] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?p. p tagged_division_of interval[a:real^M,b] /\ (\x. ball(x,d)) fine p`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINE_DIVISION_EXISTS; GAUGE_BALL]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE SND (p:real^M#(real^M->bool)->bool)` THEN
  ASM_SIMP_TAC[DIVISION_OF_TAGGED_DIVISION] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN
  DISCH_TAC THEN EXISTS_TAC `\y:real^M. (f:real^M->real^N) x` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  DISCH_THEN(MP_TAC o
    SPECL [`x:real^M`; `l:real^M->bool`] o el 1 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[SUBSET] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
  REWRITE_TAC[SUBSET; IN_BALL; dist] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[REAL_LT_IMP_LE; NORM_SUB];
    REWRITE_TAC[integrable_on] THEN
    EXISTS_TAC `content(interval[a':real^M,b']) % (f:real^M->real^N) x` THEN
    REWRITE_TAC[HAS_INTEGRAL_CONST]]);;

(* ------------------------------------------------------------------------- *)
(* Specialization of additivity to one dimension.                            *)
(* ------------------------------------------------------------------------- *)

let OPERATIVE_1_LT = prove
 (`!op. monoidal op
        ==> !f. operative op f <=>
                (!a b. drop b <= drop a ==> f(interval[a,b]) = neutral op) /\
                (!a b c. drop a < drop c /\ drop c < drop b
                         ==> op (f(interval[a,c])) (f(interval[c,b])) =
                             f(interval[a,b]))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[operative; CONTENT_EQ_0_1] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN REWRITE_TAC[FORALL_1; DIMINDEX_1] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:real^1` THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `b:real^1` THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `c:real^1` THEN FIRST_ASSUM(SUBST1_TAC o SPEC `drop c`) THEN
    DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_TRANS) THEN
    ASM_SIMP_TAC[INTERVAL_SPLIT; DIMINDEX_1; LE_REFL; REAL_LT_IMP_LE] THEN
    BINOP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CONS_11; PAIR_EQ] THEN
    SIMP_TAC[FORALL_1; CART_EQ; DIMINDEX_1; LAMBDA_BETA; LE_REFL] THEN
    REWRITE_TAC[GSYM drop] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `d:real` THEN ABBREV_TAC `c = lift d` THEN
  SUBGOAL_THEN `d = drop c` SUBST1_TAC THENL
   [ASM_MESON_TAC[LIFT_DROP]; ALL_TAC] THEN
  SIMP_TAC[INTERVAL_SPLIT; LE_REFL; drop; DIMINDEX_1] THEN
  REWRITE_TAC[GSYM drop] THEN
  DISJ_CASES_TAC(REAL_ARITH `drop c <= drop a \/ drop a < drop c`) THENL
   [SUBGOAL_THEN
     `content(interval[a:real^1,
        (lambda i. if i = 1 then min (drop b) (drop c) else b$i)]) = &0 /\
      interval[(lambda i. if i = 1 then max (drop a) (drop c) else a$i),b] =
      interval[a,b]`
    (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [SIMP_TAC[CONTENT_EQ_0_1];
        AP_TERM_TAC THEN REWRITE_TAC[CONS_11; PAIR_EQ]] THEN
      SIMP_TAC[drop; CART_EQ; FORALL_1; LAMBDA_BETA; DIMINDEX_1; LE_REFL] THEN
      UNDISCH_TAC `drop c <= drop a` THEN REWRITE_TAC[drop] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[CONTENT_EQ_0_1] THEN
      DISCH_THEN(ANTE_RES_THEN SUBST1_TAC) THEN ASM_MESON_TAC[monoidal]];
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `drop b <= drop c \/ drop c < drop b`) THENL
   [SUBGOAL_THEN
     `interval[a,(lambda i. if i = 1 then min (drop b) (drop c) else b$i)] =
      interval[a,b] /\
      content(interval
        [(lambda i. if i = 1 then max (drop a) (drop c) else a$i),b]) = &0`
      (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THENL
     [CONJ_TAC THENL
       [AP_TERM_TAC THEN REWRITE_TAC[CONS_11; PAIR_EQ];
        SIMP_TAC[CONTENT_EQ_0_1]] THEN
      SIMP_TAC[drop; CART_EQ; FORALL_1; LAMBDA_BETA; DIMINDEX_1; LE_REFL] THEN
      UNDISCH_TAC `drop b <= drop c` THEN REWRITE_TAC[drop] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[CONTENT_EQ_0_1] THEN
      DISCH_THEN(ANTE_RES_THEN SUBST1_TAC) THEN ASM_MESON_TAC[monoidal]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(lambda i. if i = 1 then min (drop b) (drop c) else b$i) = c /\
    (lambda i. if i = 1 then max (drop a) (drop c) else a$i) = c`
   (fun th -> REWRITE_TAC[th] THEN ASM_MESON_TAC[]) THEN
  SIMP_TAC[CART_EQ; FORALL_1; DIMINDEX_1; LE_REFL; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM drop] THEN ASM_REAL_ARITH_TAC);;

let OPERATIVE_1_LE = prove
 (`!op. monoidal op
        ==> !f. operative op f <=>
                (!a b. drop b <= drop a ==> f(interval[a,b]) = neutral op) /\
                (!a b c. drop a <= drop c /\ drop c <= drop b
                         ==> op (f(interval[a,c])) (f(interval[c,b])) =
                             f(interval[a,b]))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[OPERATIVE_1_LT] THEN MESON_TAC[REAL_LT_IMP_LE]] THEN
  REWRITE_TAC[operative; CONTENT_EQ_0_1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_1; DIMINDEX_1] THEN
  MAP_EVERY (fun t -> MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC t)
   [`a:real^1`; `b:real^1`] THEN DISCH_TAC THEN
  X_GEN_TAC `c:real^1` THEN FIRST_ASSUM(SUBST1_TAC o SPEC `drop c`) THEN
  DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LE_TRANS) THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT; DIMINDEX_1; LE_REFL] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[CONS_11; PAIR_EQ] THEN
  SIMP_TAC[FORALL_1; CART_EQ; DIMINDEX_1; LAMBDA_BETA; LE_REFL] THEN
  REWRITE_TAC[GSYM drop] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Special case of additivity we need for the FCT.                           *)
(* ------------------------------------------------------------------------- *)

let ADDITIVE_TAGGED_DIVISION_1 = prove
 (`!f:real^1->real^N p a b.
        drop a <= drop b /\
        p tagged_division_of interval[a,b]
        ==> vsum p
             (\(x,k). f(interval_upperbound k) - f(interval_lowerbound k)) =
            f b - f a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`(+):real^N->real^N->real^N`;
    `p:(real^1#(real^1->bool)->bool)`;
    `a:real^1`; `b:real^1`;
    `(\k. if k = {} then vec 0
          else f(interval_upperbound k) - f(interval_lowerbound k)):
     ((real^1->bool)->real^N)`] OPERATIVE_TAGGED_DIVISION) THEN
  ASM_SIMP_TAC[MONOIDAL_VECTOR_ADD; OPERATIVE_1_LT; NEUTRAL_VECTOR_ADD;
               INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INTERVAL_EQ_EMPTY_1; REAL_ARITH `a <= b ==> ~(b < a)`;
                 REAL_LT_IMP_LE; CONTENT_EQ_0_1;
                 INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
    SIMP_TAC[REAL_ARITH `b <= a ==> (b < a <=> ~(b = a))`] THEN
    SIMP_TAC[DROP_EQ; TAUT
      `(if ~p then x else y) = (if p then y else x)`] THEN
    SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1; REAL_LE_REFL] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; COND_ID; EQ_SYM_EQ] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_TRANS) THEN
    ASM_SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1;
                 REAL_ARITH `b < a ==> ~(a < b)`; REAL_LT_IMP_LE] THEN
    MESON_TAC[VECTOR_ARITH `(c - a) + (b - c):real^N = b - a`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTERVAL_EQ_EMPTY_1; GSYM REAL_NOT_LE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM VSUM] THEN MATCH_MP_TAC VSUM_EQ THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_MESON_TAC[TAGGED_DIVISION_OF; MEMBER_NOT_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* A useful lemma allowing us to factor out the content size.                *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_FACTOR_CONTENT = prove
 (`!f:real^M->real^N i a b.
      (f has_integral i) (interval[a,b]) <=>
      (!e. &0 < e
           ==> ?d. gauge d /\
                   (!p. p tagged_division_of interval[a,b] /\ d fine p
                        ==> norm (vsum p (\(x,k). content k % f x) - i)
                            <= e * content(interval[a,b])))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^M,b]) = &0` THENL
   [MP_TAC(SPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`]
     VSUM_CONTENT_NULL) THEN
    ASM_SIMP_TAC[HAS_INTEGRAL_NULL_EQ; VECTOR_SUB_LZERO; NORM_NEG] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; NORM_LE_0] THEN
    ASM_MESON_TAC[FINE_DIVISION_EXISTS; GAUGE_TRIVIAL; REAL_LT_01];
    ALL_TAC] THEN
  REWRITE_TAC[has_integral] THEN EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `e * content(interval[a:real^M,b])`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; CONTENT_LT_NZ] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2 / content(interval[a:real^M,b])`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; CONTENT_LT_NZ; REAL_OF_NUM_LT; ARITH] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL] THEN
  ASM_MESON_TAC[REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`]);;

(* ------------------------------------------------------------------------- *)
(* Attempt a systematic general set of "offset" results for components.      *)
(* ------------------------------------------------------------------------- *)

let GAUGE_MODIFY = prove
 (`!f:real^M->real^N.
      (!s. open s ==> open {x | f(x) IN s})
      ==> !d. gauge d ==> gauge (\x y. d (f x) (f y))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  SIMP_TAC[gauge; IN] THEN DISCH_TAC THEN
  X_GEN_TAC `x:real^M` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[IN]);;

(* ------------------------------------------------------------------------- *)
(* Integrabibility on subintervals.                                          *)
(* ------------------------------------------------------------------------- *)

let OPERATIVE_INTEGRABLE = prove
 (`!f. operative (/\) (\i. f integrable_on i)`,
  GEN_TAC THEN REWRITE_TAC[operative; NEUTRAL_AND] THEN CONJ_TAC THENL
   [REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_NULL_EQ];
    REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[INTEGRABLE_SPLIT] THEN
    REWRITE_TAC[integrable_on] THEN ASM_MESON_TAC[HAS_INTEGRAL_SPLIT]]);;

let INTEGRABLE_SUBINTERVAL = prove
 (`!f:real^M->real^N a b c d.
        f integrable_on interval[a,b] /\
        interval[c,d] SUBSET interval[a,b]
        ==> f integrable_on interval[c,d]`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval[c:real^M,d] = {}` THENL
   [ASM_REWRITE_TAC[integrable_on] THEN
    MESON_TAC[HAS_INTEGRAL_NULL; CONTENT_EMPTY; EMPTY_AS_INTERVAL];
    ASM_MESON_TAC[OPERATIVE_INTEGRABLE; OPERATIVE_DIVISION_AND;
                  PARTIAL_DIVISION_EXTEND_1]]);;

(* ------------------------------------------------------------------------- *)
(* Combining adjacent intervals in 1 dimension.                              *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMBINE = prove
 (`!f i:real^N j a b c.
        drop a <= drop c /\ drop c <= drop b /\
        (f has_integral i) (interval[a,c]) /\
        (f has_integral j) (interval[c,b])
        ==> (f has_integral (i + j)) (interval[a,b])`,
  REPEAT STRIP_TAC THEN MP_TAC
   ((CONJUNCT2 o GEN_REWRITE_RULE I
     [MATCH_MP OPERATIVE_1_LE(MATCH_MP MONOIDAL_LIFTED MONOIDAL_VECTOR_ADD)])
    (ISPEC `f:real^1->real^N` OPERATIVE_INTEGRAL)) THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`; `c:real^1`]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[lifted; distinctness "option"; injectivity "option"]) THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL; HAS_INTEGRAL_UNIQUE; integrable_on;
                INTEGRAL_UNIQUE]);;

let INTEGRAL_COMBINE = prove
 (`!f:real^1->real^N a b c.
        drop a <= drop c /\ drop c <= drop b /\ f integrable_on (interval[a,b])
        ==> integral(interval[a,c]) f + integral(interval[c,b]) f =
            integral(interval[a,b]) f`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC HAS_INTEGRAL_COMBINE THEN
  EXISTS_TAC `c:real^1` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN
  MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN
  ASM_REWRITE_TAC[SUBSET_INTERVAL_1; REAL_LE_REFL]);;

let INTEGRABLE_COMBINE = prove
 (`!f a b c.
        drop a <= drop c /\ drop c <= drop b /\
        f integrable_on interval[a,c] /\
        f integrable_on interval[c,b]
        ==> f integrable_on interval[a,b]`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_COMBINE]);;

(* ------------------------------------------------------------------------- *)
(* Reduce integrability to "local" integrability.                            *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_ON_LITTLE_SUBINTERVALS = prove
 (`!f:real^M->real^N a b.
        (!x. x IN interval[a,b]
             ==> ?d. &0 < d /\
                     !u v. x IN interval[u,v] /\
                           interval[u,v] SUBSET ball(x,d) /\
                           interval[u,v] SUBSET interval[a,b]
                           ==> f integrable_on interval[u,v])
        ==> f integrable_on interval[a,b]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; GAUGE_EXISTENCE_LEMMA] THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^M->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\x:real^M. ball(x,d x)`; `a:real^M`; `b:real^M`]
                FINE_DIVISION_EXISTS) THEN
  ASM_SIMP_TAC[GAUGE_BALL_DEPENDENT; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] OPERATIVE_DIVISION_AND)
         (ISPEC `f:real^M->real^N` OPERATIVE_INTEGRABLE)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`IMAGE SND (p:real^M#(real^M->bool)->bool)`; `a:real^M`; `b:real^M`]) THEN
  ASM_SIMP_TAC[DIVISION_OF_TAGGED_DIVISION] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o el 1 o CONJUNCTS o
   GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
  REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `k:real^M->bool`]) THEN
  ASM_REWRITE_TAC[] THEN  ASM_MESON_TAC[SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Second FCT or existence of antiderivative.                                *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_HAS_VECTOR_DERIVATIVE_POINTWISE = prove
 (`!f:real^1->real^N a b x.
        f integrable_on interval[a,b] /\ x IN interval[a,b] /\
        f continuous (at x within interval[a,b])
        ==> ((\u. integral (interval [a,u]) f) has_vector_derivative f x)
            (at x within interval [a,b])`,
  REWRITE_TAC[IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[has_vector_derivative; HAS_DERIVATIVE_WITHIN_ALT] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
    CONJ_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_within]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; dist] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN
  DISJ_CASES_TAC(REAL_ARITH `drop x <= drop y \/ drop y <= drop x`) THENL
   [ASM_SIMP_TAC[REAL_ARITH `x <= y ==> abs(y - x) = y - x`];
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `fy - fx - (x - y) % c:real^N = --(fx - fy - (y - x) % c)`] THEN
    ASM_SIMP_TAC[NORM_NEG; REAL_ARITH `x <= y ==> abs(x - y) = y - x`]] THEN
  ASM_SIMP_TAC[GSYM CONTENT_1] THEN MATCH_MP_TAC HAS_INTEGRAL_BOUND THEN
  EXISTS_TAC `(\u. f(u) - f(x)):real^1->real^N` THEN
  (ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[IN_INTERVAL_1; NORM_REAL; DROP_SUB; GSYM drop] THEN
    REAL_ARITH_TAC] THEN
   MATCH_MP_TAC HAS_INTEGRAL_SUB THEN REWRITE_TAC[HAS_INTEGRAL_CONST]) THENL
    [SUBGOAL_THEN
      `integral(interval[a,x]) f + integral(interval[x,y]) f =
       integral(interval[a,y]) f /\
       ((f:real^1->real^N) has_integral integral(interval[x,y]) f)
        (interval[x,y])`
      (fun th -> MESON_TAC[th;
          VECTOR_ARITH `a + b = c:real^N ==> c - a = b`]);
     SUBGOAL_THEN
      `integral(interval[a,y]) f + integral(interval[y,x]) f =
       integral(interval[a,x]) f /\
       ((f:real^1->real^N) has_integral integral(interval[y,x]) f)
        (interval[y,x])`
       (fun th -> MESON_TAC[th;
         VECTOR_ARITH `a + b = c:real^N ==> c - a = b`])] THEN
   (CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_COMBINE;
      MATCH_MP_TAC INTEGRABLE_INTEGRAL] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN
    ASM_SIMP_TAC[INTEGRABLE_CONTINUOUS; SUBSET_INTERVAL_1] THEN
    ASM_REAL_ARITH_TAC));;

let INTEGRAL_HAS_VECTOR_DERIVATIVE = prove
 (`!f:real^1->real^N a b.
     f continuous_on interval[a,b]
     ==> !x. x IN interval[a,b]
             ==> ((\u. integral (interval[a,u]) f) has_vector_derivative f(x))
                 (at x within interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_HAS_VECTOR_DERIVATIVE_POINTWISE THEN
  ASM_MESON_TAC[INTEGRABLE_CONTINUOUS; CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]);;

let ANTIDERIVATIVE_CONTINUOUS = prove
 (`!f:real^1->real^N a b.
     f continuous_on interval[a,b]
     ==> ?g. !x. x IN interval[a,b]
                 ==> (g has_vector_derivative f(x))
                          (at x within interval[a,b])`,
  MESON_TAC[INTEGRAL_HAS_VECTOR_DERIVATIVE]);;

(* ------------------------------------------------------------------------- *)
(* General "twiddling" for interval-to-interval function image.              *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_TWIDDLE = prove
 (`!f:real^N->real^P (g:real^M->real^N) h r i a b.
      &0 < r /\
      (!x. h(g x) = x) /\ (!x. g(h x) = x) /\ (!x. g continuous at x) /\
      (!u v. ?w z. IMAGE g (interval[u,v]) = interval[w,z]) /\
      (!u v. ?w z. IMAGE h (interval[u,v]) = interval[w,z]) /\
      (!u v. content(IMAGE g (interval[u,v])) = r * content(interval[u,v])) /\
      (f has_integral i) (interval[a,b])
      ==> ((\x. f(g x)) has_integral (inv r) % i) (IMAGE h (interval[a,b]))`,
  let lemma0 = prove
   (`(!x k. (x,k) IN IMAGE (\(x,k). f x,g k) p ==> P x k) <=>
     (!x k. (x,k) IN p ==> P (f x) (g k))`,
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[])
  and lemma1 = prove
   (`{k | ?x. (x,k) IN p} = IMAGE SND p`,
    REWRITE_TAC[EXTENSION; EXISTS_PAIR_THM; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[])
  and lemma2 = prove
   (`SND o (\(x,k). f x,g k) = g o SND`,
    REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_DEF]) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `interval[a:real^N,b] = {}` THEN
  ASM_SIMP_TAC[IMAGE_CLAUSES; HAS_INTEGRAL_EMPTY_EQ; VECTOR_MUL_RZERO] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[has_integral] THEN
  ASM_REWRITE_TAC[has_integral_def; has_integral_compact_interval] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e * r:real`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x y:real^M. (d:real^N->real^N->bool) (g x) (g y)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [gauge]) THEN
    SIMP_TAC[gauge; IN; FORALL_AND_THM] THEN
    STRIP_TAC THEN X_GEN_TAC `x:real^M` THEN
    SUBGOAL_THEN `(\y:real^M. (d:real^N->real^N->bool) (g x) (g y)) =
                  {y | g y IN (d (g x))}` SUBST1_TAC
    THENL [SET_TAC[]; ASM_SIMP_TAC[CONTINUOUS_OPEN_PREIMAGE_UNIV]];
    ALL_TAC] THEN
  X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `IMAGE (\(x,k). (g:real^M->real^N) x, IMAGE g k) p`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      REWRITE_TAC[fine; lemma0] THEN
      STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
      ASM SET_TAC[]] THEN
    SUBGOAL_THEN
     `interval[a,b] = IMAGE ((g:real^M->real^N) o h) (interval[a,b])`
    SUBST1_TAC THENL [SIMP_TAC[o_DEF] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?u v. IMAGE (h:real^N->real^M) (interval[a,b]) =
                        interval[u,v]`
    (REPEAT_TCL CHOOSE_THEN
      (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    REWRITE_TAC[TAGGED_DIVISION_OF; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[lemma0] THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
      DISCH_TAC THEN
      UNDISCH_TAC
       `!x:real^M k.
             x,k IN p
             ==> x IN k /\
                 k SUBSET interval[u,v] /\
                 ?w z. k = interval[w,z]` THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `k:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
       [SET_TAC[];
        REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
        STRIP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[lemma1; GSYM IMAGE_o; lemma2] THEN
      REWRITE_TAC[IMAGE_o; GSYM IMAGE_UNIONS; ETA_AX]] THEN
    MAP_EVERY X_GEN_TAC [`x1:real^M`; `k1:real^M->bool`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x2:real^M`; `k2:real^M->bool`] THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!x1:real^M k1:real^M->bool.
             x1,k1 IN p
             ==> (!x2 k2.
                      x2,k2 IN p /\ ~(x1,k1 = x2,k2)
                      ==> interior k1 INTER interior k2 = {})` THEN
    DISCH_THEN(MP_TAC o SPECL [`x1:real^M`; `k1:real^M->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`x2:real^M`; `k2:real^M->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `interior(IMAGE f s) SUBSET IMAGE f (interior s) /\
      interior(IMAGE f t) SUBSET IMAGE f (interior t) /\
      (!x y. f x = f y ==> x = y)
      ==> interior s INTER interior t = {}
          ==> interior(IMAGE f s) INTER interior(IMAGE f t) = {}`) THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC INTERIOR_IMAGE_SUBSET) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) VSUM_IMAGE
                (lhand(rand(lhand(lhand w)))))) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
  EXISTS_TAC `abs r` THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> &0 < abs x`] THEN
  REWRITE_TAC[GSYM NORM_MUL] THEN ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x < a * b ==> x = y ==> y < b * a`)) THEN
  AP_TERM_TAC THEN REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_MUL_LID; GSYM VSUM_LMUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  REWRITE_TAC[FORALL_PAIR_THM; VECTOR_MUL_ASSOC] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_MESON_TAC[TAGGED_DIVISION_OF]);;

(* ------------------------------------------------------------------------- *)
(* Special case of permuting the coordinates.                                *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_TWIZZLE_INTERVAL = prove
 (`!f:real^N->real^P p a b:real^M.
      (f has_integral y) (interval[(lambda i. a$(p i)),(lambda i. b$(p i))]) /\
      dimindex(:M) = dimindex(:N) /\ p permutes 1..dimindex(:N)
      ==> ((\x. f(lambda i. x$p i)) has_integral y) (interval[a,b])`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`f:real^N->real^P`; `(\x. lambda i. x$(p i)):real^M->real^N`;
    `(\x. lambda i. x$(inverse p i)):real^N->real^M`;
    `&1`; `y:real^P`;
    `((\x. lambda i. x$(p i)):real^M->real^N) a`;
    `((\x. lambda i. x$(p i)):real^M->real^N) b`]
    HAS_INTEGRAL_TWIDDLE) THEN
  REWRITE_TAC[REAL_LT_01] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PERMUTES_INVERSE) THEN
  MP_TAC(SPEC `inverse p:num->num`
   (INST_TYPE [`:N`,`:M`; `:M`,`:N`] IMAGE_TWIZZLE_INTERVAL)) THEN
  MP_TAC(SPEC `p:num->num` IMAGE_TWIZZLE_INTERVAL) THEN
  ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REPLICATE_TAC 2 (DISCH_THEN(fun th -> REWRITE_TAC[th])) THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [IMP_REWRITE_TAC[LAMBDA_BETA] THEN REWRITE_TAC[GSYM IN_NUMSEG] THEN
      ASM_MESON_TAC[PERMUTES_INVERSES; PERMUTES_IN_IMAGE];
      IMP_REWRITE_TAC[LAMBDA_BETA] THEN REWRITE_TAC[GSYM IN_NUMSEG] THEN
      ASM_MESON_TAC[PERMUTES_INVERSES; PERMUTES_IN_IMAGE];
      GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
      SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_MUL_COMPONENT;
               VECTOR_ADD_COMPONENT];
      MESON_TAC[];
      MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN
      SIMP_TAC[REAL_MUL_LID; CONTENT_CLOSED_INTERVAL_CASES] THEN
      AP_THM_TAC THEN BINOP_TAC THENL
       [IMP_REWRITE_TAC[LAMBDA_BETA] THEN
        REWRITE_TAC[GSYM IN_NUMSEG] THEN
        ASM_MESON_TAC[PERMUTES_INVERSES; PERMUTES_IN_IMAGE];
        MP_TAC(MATCH_MP PRODUCT_PERMUTE
          (ASSUME `p permutes 1..dimindex(:N)`)) THEN
        ASM_REWRITE_TAC[] THEN ONCE_ASM_REWRITE_TAC[] THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
        MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REWRITE_TAC[o_DEF] THEN
        IMP_REWRITE_TAC[LAMBDA_BETA] THEN REWRITE_TAC[] THEN
        IMP_REWRITE_TAC[LAMBDA_BETA]]];
    REWRITE_TAC[o_DEF; REAL_INV_1; VECTOR_MUL_LID] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[PAIR_EQ; LAMBDA_BETA; CART_EQ] THEN
    IMP_REWRITE_TAC[LAMBDA_BETA] THEN
    REWRITE_TAC[GSYM IN_NUMSEG] THEN
    ASM_MESON_TAC[PERMUTES_INVERSES; PERMUTES_IN_IMAGE]]);;

(* ------------------------------------------------------------------------- *)
(* Special case of a basic affine transformation.                            *)
(* ------------------------------------------------------------------------- *)

let INTERVAL_IMAGE_AFFINITY_INTERVAL = prove
 (`!a b m c. ?u v. IMAGE (\x. m % x + c) (interval[a,b]) = interval[u,v]`,
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
  MESON_TAC[EMPTY_AS_INTERVAL]);;

let CONTENT_IMAGE_AFFINITY_INTERVAL = prove
 (`!a b:real^N m c.
        content(IMAGE (\x. m % x + c) (interval[a,b])) =
        (abs m) pow (dimindex(:N)) * content(interval[a,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CONTENT_EMPTY; REAL_MUL_RZERO] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN COND_CASES_TAC THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) CONTENT_CLOSED_INTERVAL
                (lhs w))) THEN
  (ANTS_TAC THENL
    [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
     ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                  REAL_LE_RADD; REAL_LE_LMUL] THEN
     ONCE_REWRITE_TAC[REAL_ARITH `m * b <= m * a <=> --m * a <= --m * b`] THEN
     ASM_SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> &0 <= --x`; REAL_LE_LMUL];
     ALL_TAC]) THEN
  DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[GSYM PRODUCT_CONST_NUMSEG_1] THEN
  ASM_SIMP_TAC[CONTENT_CLOSED_INTERVAL; GSYM PRODUCT_MUL_NUMSEG] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN
  SIMP_TAC[IN_NUMSEG; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  ASM_REAL_ARITH_TAC);;

let HAS_INTEGRAL_AFFINITY = prove
 (`!f:real^M->real^N i a b m c.
        (f has_integral i) (interval[a,b]) /\ ~(m = &0)
        ==> ((\x. f(m % x + c)) has_integral
             (inv(abs(m) pow dimindex(:M)) % i))
            (IMAGE (\x. inv m % x + --(inv(m) % c)) (interval[a,b]))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_TWIDDLE THEN
  ASM_SIMP_TAC[INTERVAL_IMAGE_AFFINITY_INTERVAL; GSYM REAL_ABS_NZ;
        REAL_POW_LT; PRODUCT_EQ_0_NUMSEG; CONTENT_IMAGE_AFFINITY_INTERVAL] THEN
  ASM_SIMP_TAC[CONTINUOUS_CMUL; CONTINUOUS_AT_ID; CONTINUOUS_CONST;
               CONTINUOUS_ADD] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; VECTOR_MUL_RNEG] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV] THEN
  CONJ_TAC THEN VECTOR_ARITH_TAC);;

let INTEGRABLE_AFFINITY = prove
 (`!f:real^M->real^N a b m c.
        f integrable_on interval[a,b] /\ ~(m = &0)
        ==> (\x. f(m % x + c)) integrable_on
            (IMAGE (\x. inv m % x + --(inv(m) % c)) (interval[a,b]))`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_AFFINITY]);;

(* ------------------------------------------------------------------------- *)
(* Special case of stretching coordinate axes separately.                    *)
(* ------------------------------------------------------------------------- *)

let CONTENT_IMAGE_STRETCH_INTERVAL = prove
 (`!a b:real^N m.
        content(IMAGE (\x. lambda k. m k * x$k) (interval[a,b]):real^N->bool) =
        abs(product(1..dimindex(:N)) m) * content(interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[content; IMAGE_EQ_EMPTY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  ASM_REWRITE_TAC[IMAGE_STRETCH_INTERVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; LAMBDA_BETA;
               REAL_ARITH `min a b <= max a b`] THEN
  ASM_REWRITE_TAC[REAL_ARITH `max a b - min a b = abs(b - a)`;
                  GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[PRODUCT_MUL; FINITE_NUMSEG;
               REAL_ARITH `a <= b ==> abs(b - a) = b - a`] THEN
  ASM_SIMP_TAC[PRODUCT_ABS; FINITE_NUMSEG]);;

let HAS_INTEGRAL_STRETCH = prove
 (`!f:real^M->real^N i m a b.
        (f has_integral i) (interval[a,b]) /\
        (!k. 1 <= k /\ k <= dimindex(:M) ==>  ~(m k = &0))
        ==> ((\x:real^M. f(lambda k. m k * x$k)) has_integral
             (inv(abs(product(1..dimindex(:M)) m)) % i))
            (IMAGE (\x. lambda k. inv(m k) * x$k) (interval[a,b]))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_TWIDDLE THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RINV; REAL_MUL_LID] THEN
  ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; PRODUCT_EQ_0_NUMSEG] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    SIMP_TAC[linear; LAMBDA_BETA; CART_EQ; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[CONTENT_IMAGE_STRETCH_INTERVAL] THEN
    REWRITE_TAC[IMAGE_STRETCH_INTERVAL] THEN MESON_TAC[EMPTY_AS_INTERVAL]]);;

let INTEGRABLE_STRETCH = prove
 (`!f:real^M->real^N m a b.
        f integrable_on interval[a,b] /\
        (!k. 1 <= k /\ k <= dimindex(:M) ==>  ~(m k = &0))
        ==> (\x:real^M. f(lambda k. m k * x$k)) integrable_on
            (IMAGE (\x. lambda k. inv(m k) * x$k) (interval[a,b]))`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_STRETCH]);;

(* ------------------------------------------------------------------------- *)
(* Even more special cases.                                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_REFLECT_LEMMA = prove
 (`!f:real^M->real^N i a b.
     (f has_integral i) (interval[a,b])
     ==> ((\x. f(--x)) has_integral i) (interval[--b,--a])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o C CONJ (REAL_ARITH `~(-- &1 = &0)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^M`) THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_POW_ONE] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_NEG_0] THEN
  REWRITE_TAC[REAL_INV_NEG; REAL_INV_1] THEN
  REWRITE_TAC[VECTOR_ARITH `-- &1 % x + vec 0 = --x`] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN POP_ASSUM(K ALL_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[INTERVAL_EQ_EMPTY] THEN
  REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a /\ b ==> ~c)`] THEN
  SIMP_TAC[VECTOR_NEG_COMPONENT; REAL_LT_NEG2]);;

let HAS_INTEGRAL_REFLECT = prove
 (`!f:real^M->real^N i a b.
     ((\x. f(--x)) has_integral i) (interval[--b,--a]) <=>
     (f has_integral i) (interval[a,b])`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_REFLECT_LEMMA) THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX]);;

let INTEGRABLE_REFLECT = prove
 (`!f:real^M->real^N a b.
     (\x. f(--x)) integrable_on (interval[--b,--a]) <=>
     f integrable_on (interval[a,b])`,
  REWRITE_TAC[integrable_on; HAS_INTEGRAL_REFLECT]);;

let INTEGRAL_REFLECT = prove
 (`!f:real^M->real^N a b.
     integral (interval[--b,--a]) (\x. f(--x)) =
     integral (interval[a,b]) f`,
  REWRITE_TAC[integral; HAS_INTEGRAL_REFLECT]);;

(* ------------------------------------------------------------------------- *)
(* Technical lemmas about how many non-trivial intervals of a division a     *)
(* point can be in (we sometimes need this for bounding sums).               *)
(* ------------------------------------------------------------------------- *)

let DIVISION_COMMON_POINT_BOUND = prove
 (`!d s:real^N->bool x.
        d division_of s
        ==> CARD {k | k IN d /\ ~(content k = &0) /\ x IN k}
            <= 2 EXP (dimindex(:N))`,
  let lemma = prove
   (`!f s. (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
           FINITE s /\ CARD(IMAGE f s) <= n
           ==> CARD(s) <= n`,
    MESON_TAC[CARD_IMAGE_INJ]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. k IN d ==> ?a b:real^N. interval[a,b] = k` MP_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`A:(real^N->bool)->real^N`; `B:(real^N->bool)->real^N`] THEN
  STRIP_TAC THEN MATCH_MP_TAC(ISPEC
   `\d. (lambda i. (x:real^N)$i = (A:(real^N->bool)->real^N)(d)$i):bool^N`
   lemma) THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[division_of];
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(:bool^N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[SUBSET_UNIV] THEN
      SIMP_TAC[FINITE_CART_UNIV; FINITE_BOOL];
      SIMP_TAC[FINITE_BOOL; CARD_CART_UNIV; CARD_BOOL; LE_REFL]]] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `l:real^N->bool`] THEN
  SIMP_TAC[IN_ELIM_THM; CART_EQ; LAMBDA_BETA] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
  DISCH_THEN(MP_TAC o SPECL [`k:real^N->bool`; `l:real^N->bool`] o
        el 2 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[GSYM INTERIOR_INTER] THEN
  MATCH_MP_TAC(TAUT `~q ==> (~p ==> q) ==> p`) THEN
  MAP_EVERY UNDISCH_TAC
   [`(x:real^N) IN k`; `(x:real^N) IN l`;
    `~(content(k:real^N->bool) = &0)`;
    `~(content(l:real^N->bool) = &0)`] THEN
  SUBGOAL_THEN
   `k = interval[A k:real^N,B k] /\ l = interval[A l,B l]`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL [ASM_MESON_TAC[]; REWRITE_TAC[INTER_INTERVAL]] THEN
  REWRITE_TAC[CONTENT_EQ_0_INTERIOR; INTERIOR_CLOSED_INTERVAL] THEN
  SIMP_TAC[IN_INTERVAL; INTERVAL_NE_EMPTY; LAMBDA_BETA] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let TAGGED_PARTIAL_DIVISION_COMMON_POINT_BOUND = prove
 (`!p s:real^N->bool y.
        p tagged_partial_division_of s
        ==> CARD {(x,k) | (x,k) IN p /\ y IN k /\ ~(content k = &0)}
            <= 2 EXP (dimindex(:N))`,
  let lemma = prove
   (`!f s. (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
           FINITE s /\ CARD(IMAGE f s) <= n
           ==> CARD(s) <= n`,
    MESON_TAC[CARD_IMAGE_INJ]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `SND` lemma) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC; RIGHT_FORALL_IMP_THM; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`x1:real^N`; `k1:real^N->bool`] THEN
    REPEAT DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x2:real^N`; `k2:real^N->bool`] THEN
    REPEAT DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [tagged_partial_division_of]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`x1:real^N`; `k1:real^N->bool`; `x2:real^N`; `k2:real^N->bool`] o
     CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN
    MATCH_MP_TAC(TAUT `~q ==> (~p ==> q) ==> p`) THEN
    REWRITE_TAC[INTER_ACI] THEN
    ASM_MESON_TAC[CONTENT_EQ_0_INTERIOR; tagged_partial_division_of];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `p:real^N#(real^N->bool)->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[tagged_partial_division_of]; SET_TAC[]];
    FIRST_ASSUM(MP_TAC o MATCH_MP PARTIAL_DIVISION_OF_TAGGED_DIVISION) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o
      MATCH_MP DIVISION_COMMON_POINT_BOUND) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LE_TRANS) THEN
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM] THEN MESON_TAC[];
      MATCH_MP_TAC FINITE_RESTRICT THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_MESON_TAC[tagged_partial_division_of]]]);;

let TAGGED_PARTIAL_DIVISION_COMMON_TAGS = prove
 (`!p s:real^N->bool x.
        p tagged_partial_division_of s
        ==> CARD {(x,k) | k | (x,k) IN p /\ ~(content k = &0)}
            <= 2 EXP (dimindex(:N))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o
   MATCH_MP TAGGED_PARTIAL_DIVISION_COMMON_POINT_BOUND) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LE_TRANS) THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_PAIR_THM] THEN
    ASM_MESON_TAC[tagged_partial_division_of];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `p:real^N#(real^N->bool)->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[tagged_partial_division_of]; SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Integrating characteristic function of an interval.                       *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_RESTRICT_OPEN_SUBINTERVAL = prove
 (`!f:real^M->real^N a b c d i.
        (f has_integral i) (interval[c,d]) /\
        interval[c,d] SUBSET interval[a,b]
        ==> ((\x. if x IN interval(c,d) then f x else vec 0) has_integral i)
             (interval[a,b])`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `interval[c:real^M,d] = {}` THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM
     `interior:(real^M->bool)->(real^M->bool)`) THEN
    SIMP_TAC[INTERIOR_CLOSED_INTERVAL; INTERIOR_EMPTY] THEN
    ASM_SIMP_TAC[NOT_IN_EMPTY; HAS_INTEGRAL_0_EQ; HAS_INTEGRAL_EMPTY_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `g:real^M->real^N =
                 \x. if x IN interval(c,d) then f x else vec 0` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check(is_neg o concl)) THEN
  REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP PARTIAL_DIVISION_EXTEND_1) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`lifted((+):real^N->real^N->real^N)`;
    `p:(real^M->bool)->bool`;
    `a:real^M`; `b:real^M`;
    `\i. if (g:real^M->real^N) integrable_on i
         then SOME (integral i g) else NONE`]
   OPERATIVE_DIVISION) THEN
  ASM_SIMP_TAC[OPERATIVE_INTEGRAL; MONOIDAL_LIFTED; MONOIDAL_VECTOR_ADD] THEN
  SUBGOAL_THEN
   `iterate (lifted (+)) p
     (\i. if (g:real^M->real^N) integrable_on i
          then SOME (integral i g) else NONE) =
    SOME i`
  SUBST1_TAC THENL
   [ALL_TAC;
    COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
    ASM_MESON_TAC[INTEGRABLE_INTEGRAL]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_LIFTED; MONOIDAL_VECTOR_ADD;
               FINITE_DELETE; IN_DELETE] THEN
  SUBGOAL_THEN `(g:real^M->real^N) integrable_on interval[c,d]`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HAS_INTEGRAL_INTEGRABLE) THEN
    MATCH_MP_TAC INTEGRABLE_SPIKE_INTERIOR THEN
    EXPAND_TAC "g" THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `iterate (lifted (+)) (p DELETE interval[c,d])
      (\i. if (g:real^M->real^N) integrable_on i
           then SOME (integral i g) else NONE) = SOME(vec 0)`
  SUBST1_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[lifted; VECTOR_ADD_RID] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC HAS_INTEGRAL_SPIKE_INTERIOR THEN
    EXISTS_TAC `f:real^M->real^N` THEN
    EXPAND_TAC "g" THEN ASM_SIMP_TAC[]] THEN
  SIMP_TAC[GSYM NEUTRAL_VECTOR_ADD; GSYM NEUTRAL_LIFTED;
           MONOIDAL_VECTOR_ADD] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_EQ_NEUTRAL
        (MATCH_MP MONOIDAL_LIFTED(SPEC_ALL MONOIDAL_VECTOR_ADD))) THEN
  SIMP_TAC[NEUTRAL_LIFTED; NEUTRAL_VECTOR_ADD; MONOIDAL_VECTOR_ADD] THEN
  X_GEN_TAC `k:real^M->bool` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((g:real^M->real^N) has_integral (vec 0)) k`
   (fun th -> MESON_TAC[th; integrable_on; INTEGRAL_UNIQUE]) THEN
  SUBGOAL_THEN `?u v:real^M. k = interval[u,v]` MP_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE_INTERIOR THEN
  EXISTS_TAC `(\x. vec 0):real^M->real^N` THEN
  REWRITE_TAC[HAS_INTEGRAL_0] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
  DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`interval[c:real^M,d]`; `interval[u:real^M,v]`]) THEN
  ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
  EXPAND_TAC "g" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM SET_TAC[]);;

let HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVAL = prove
 (`!f:real^M->real^N a b c d i.
        (f has_integral i) (interval[c,d]) /\
        interval[c,d] SUBSET interval[a,b]
        ==> ((\x. if x IN interval[c,d] then f x else vec 0) has_integral i)
             (interval[a,b])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_RESTRICT_OPEN_SUBINTERVAL) THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
    HAS_INTEGRAL_SPIKE) THEN
  EXISTS_TAC `interval[c:real^M,d] DIFF interval(c,d)` THEN
  REWRITE_TAC[NEGLIGIBLE_FRONTIER_INTERVAL] THEN REWRITE_TAC[IN_DIFF] THEN
  MP_TAC(ISPECL [`c:real^M`; `d:real^M`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
  SET_TAC[]);;

let HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVALS_EQ = prove
 (`!f:real^M->real^N a b c d i.
        interval[c,d] SUBSET interval[a,b]
        ==> (((\x. if x IN interval[c,d] then f x else vec 0) has_integral i)
              (interval[a,b]) <=>
             (f has_integral i) (interval[c,d]))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `interval[c:real^M,d] = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; HAS_INTEGRAL_0_EQ; HAS_INTEGRAL_EMPTY_EQ];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVAL] THEN
  SUBGOAL_THEN `(f:real^M->real^N) integrable_on interval[c,d]` MP_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_EQ THEN
    EXISTS_TAC `\x. if x IN interval[c:real^M,d]
                    then f x:real^N else vec 0` THEN
    SIMP_TAC[] THEN MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
    ASM_MESON_TAC[integrable_on];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  MP_TAC(ASSUME `interval[c:real^M,d] SUBSET interval[a,b]`) THEN
  REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVAL) THEN
  ASM_MESON_TAC[HAS_INTEGRAL_UNIQUE; INTEGRABLE_INTEGRAL]);;

(* ------------------------------------------------------------------------- *)
(* Hence we can apply the limit process uniformly to all integrals.          *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL = prove
 (`!f:real^M->real^N i s.
     (f has_integral i) s <=>
        !e. &0 < e
            ==> ?B. &0 < B /\
                    !a b. ball(vec 0,B) SUBSET interval[a,b]
                          ==> ?z. ((\x. if x IN s then f(x) else vec 0)
                                   has_integral z) (interval[a,b]) /\
                                  norm(z - i) < e`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [has_integral_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(X_CHOOSE_THEN `a:real^M` (X_CHOOSE_THEN `b:real^M`
   SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`a:real^M`; `b:real^M`] (CONJUNCT1 BOUNDED_INTERVAL)) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `B + &1` THEN ASM_SIMP_TAC[REAL_LT_ADD; REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [`c:real^M`; `d:real^M`] THEN
    REWRITE_TAC[SUBSET; IN_BALL; NORM_ARITH `dist(vec 0,x) = norm x`] THEN
    DISCH_TAC THEN EXISTS_TAC `i:real^N` THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    MATCH_MP_TAC HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVAL THEN
    ASM_MESON_TAC[SUBSET; REAL_ARITH `n <= B ==> n < B + &1`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?y. ((f:real^M->real^N) has_integral y) (interval[a,b])`
  MP_TAC THENL
   [SUBGOAL_THEN
     `?c d. interval[a,b] SUBSET interval[c,d] /\
            (\x. if x IN interval[a,b] then (f:real^M->real^N) x
                 else vec 0) integrable_on interval[c,d]`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP REAL_LT_01) THEN
      DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
      ABBREV_TAC `c:real^M = lambda i. --(max B C)` THEN
      ABBREV_TAC `d:real^M = lambda i. max B C` THEN
      MAP_EVERY EXISTS_TAC [`c:real^M`; `d:real^M`] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^M` THEN
        DISCH_TAC THEN REWRITE_TAC[IN_INTERVAL] THEN
        X_GEN_TAC `k:num` THEN MAP_EVERY EXPAND_TAC ["c"; "d"] THEN
        SIMP_TAC[LAMBDA_BETA; REAL_BOUNDS_LE] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^M)` THEN
        ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= B ==> x <= max B C`) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^M`; `d:real^M`]) THEN ANTS_TAC THENL
       [REWRITE_TAC[SUBSET; IN_BALL; NORM_ARITH `dist(vec 0,x) = norm x`] THEN
        X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[IN_INTERVAL] THEN
        X_GEN_TAC `k:num` THEN MAP_EVERY EXPAND_TAC ["c"; "d"] THEN
        SIMP_TAC[LAMBDA_BETA; REAL_BOUNDS_LE] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^M)` THEN
        ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
        MATCH_MP_TAC(REAL_ARITH `x < C ==> x <= max B C`) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MESON_TAC[integrable_on];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [integrable_on]) THEN
      ASM_SIMP_TAC[HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVALS_EQ]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
  SUBGOAL_THEN `i:real^N = y` ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(NORM_ARITH `~(&0 < norm(y - i)) ==> i = y`) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `norm(y - i:real^N)`) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `C:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  ABBREV_TAC `c:real^M = lambda i. --(max B C)` THEN
  ABBREV_TAC `d:real^M = lambda i. max B C` THEN
  MAP_EVERY EXISTS_TAC [`c:real^M`; `d:real^M`] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; NORM_ARITH `dist(vec 0,x) = norm x`] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[IN_INTERVAL] THEN
    X_GEN_TAC `k:num` THEN MAP_EVERY EXPAND_TAC ["c"; "d"] THEN
    SIMP_TAC[LAMBDA_BETA; REAL_BOUNDS_LE] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^M)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
    MATCH_MP_TAC(REAL_ARITH `x < C ==> x <= max B C`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[a:real^M,b] SUBSET interval[c,d]` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^M` THEN
    DISCH_TAC THEN REWRITE_TAC[IN_INTERVAL] THEN
    X_GEN_TAC `k:num` THEN MAP_EVERY EXPAND_TAC ["c"; "d"] THEN
    SIMP_TAC[LAMBDA_BETA; REAL_BOUNDS_LE] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^M)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= B ==> x <= max B C`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVALS_EQ] THEN
  ASM_MESON_TAC[REAL_LT_REFL; HAS_INTEGRAL_UNIQUE]);;

let HAS_INTEGRAL_TWIZZLE = prove
 (`!f:real^N->real^P s:real^M->bool y p.
        dimindex(:M) = dimindex(:N) /\ p permutes 1..dimindex(:N) /\
        (f has_integral y) (IMAGE (\x. lambda i. x$p i) s)
        ==> ((\x. f(lambda i. x$p i)) has_integral y) s`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(lambda i. (a:real^M)$p i):real^N`;
    `(lambda i. (b:real^M)$p i):real^N`]) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  SIMP_TAC[SUBSET; IN_BALL_0; IN_INTERVAL; LAMBDA_BETA] THEN
  ASM_REWRITE_TAC[NORM_LT_SQUARE; dot] THEN DISCH_TAC THEN ANTS_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `(lambda i. (x:real^N)$(inverse p i)):real^M`) THEN
    SIMP_TAC[LAMBDA_BETA] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `x < a ==> x = y ==> y < a`)) THEN
      FIRST_ASSUM(MP_TAC o GSYM o
        MATCH_MP SUM_PERMUTE o MATCH_MP PERMUTES_INVERSE) THEN
      ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[o_DEF];
      REWRITE_TAC[GSYM IN_NUMSEG] THEN
      ASM_MESON_TAC[PERMUTES_INVERSES; PERMUTES_IN_IMAGE]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^P` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[]] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      HAS_INTEGRAL_TWIZZLE_INTERVAL)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN  GEN_TAC THEN AP_THM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x y. f x = f y ==> x = y)
    ==> (f x IN IMAGE f s <=> x IN s)`) THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM IN_NUMSEG] THEN
  ASM_MESON_TAC[PERMUTES_INVERSES; PERMUTES_IN_IMAGE]);;

let HAS_INTEGRAL_TWIZZLE_EQ = prove
 (`!f:real^N->real^P s:real^M->bool y p.
        dimindex(:M) = dimindex(:N) /\ p permutes 1..dimindex(:N)
        ==> ((f has_integral y) (IMAGE (\x. lambda i. x$p i) s) <=>
             ((\x. f(lambda i. x$p i)) has_integral y) s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[HAS_INTEGRAL_TWIZZLE]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(f:real^N->real^P) o ((\x. lambda i. x$p i):real^M->real^N)`;
    `IMAGE ((\x. lambda i. x$p i):real^M->real^N) s`;
    `y:real^P`; `inverse p:num->num`] HAS_INTEGRAL_TWIZZLE) THEN
  REWRITE_TAC[] THEN ONCE_ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[PERMUTES_INVERSE; o_DEF; GSYM IMAGE_o] THEN
  MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THEN MATCH_MP_TAC EQ_IMP THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
     `(!x. f x = x) ==> s = IMAGE f s`) THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA];
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; FUN_EQ_THM; LAMBDA_BETA]] THEN
  IMP_REWRITE_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM IN_NUMSEG] THEN
  ASM_MESON_TAC[PERMUTES_INVERSES; PERMUTES_IN_IMAGE]);;

let HAS_INTEGRAL_PASTECART_SYM_ALT = prove
 (`!f:real^(M,N)finite_sum->real^P s y.
        ((\z. f(pastecart (sndcart z) (fstcart z))) has_integral y) s <=>
        (f has_integral y) (IMAGE (\z. pastecart (sndcart z) (fstcart z)) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?p. p permutes 1..dimindex(:(M,N)finite_sum) /\
        !z. pastecart (sndcart z:real^M) (fstcart z:real^N) =
            lambda i. z$(p i)`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    EXISTS_TAC `\i. if 1 <= i /\ i <= dimindex(:M) then i + dimindex(:N)
                else if i <= dimindex(:M) + dimindex(:N) then i - dimindex(:M)
                 else i` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
      EXISTS_TAC `\i. if 1 <= i /\ i <= dimindex(:N) then i + dimindex(:M)
                else if i <= dimindex(:M) + dimindex(:N) then i - dimindex(:N)
                else i` THEN
      SIMP_TAC[IN_NUMSEG; DIMINDEX_FINITE_SUM] THEN ARITH_TAC;
      SIMP_TAC[FUN_EQ_THM; CART_EQ; pastecart; LAMBDA_BETA] THEN
      SIMP_TAC[fstcart; sndcart; LAMBDA_BETA; DIMINDEX_FINITE_SUM;
               ARITH_RULE `i:num <= n ==> i + m <= n + m`] THEN
      REPEAT STRIP_TAC THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      TRY(MATCH_MP_TAC LAMBDA_BETA) THEN ASM_ARITH_TAC];
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC HAS_INTEGRAL_TWIZZLE_EQ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_SYM]]);;

let HAS_INTEGRAL_PASTECART_SYM = prove
 (`!f:real^(M,N)finite_sum->real^P s y.
        ((\z. f(pastecart (sndcart z) (fstcart z))) has_integral y)
        (IMAGE (\z. pastecart (sndcart z) (fstcart z)) s) <=>
        (f has_integral y) s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`f:real^(M,N)finite_sum->real^P`;
    `IMAGE (\z. pastecart (sndcart z) (fstcart z))
           (s:real^(M,N)finite_sum->bool)`; `y:real^P`]
   HAS_INTEGRAL_PASTECART_SYM_ALT) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[PASTECART_FST_SND; IMAGE_ID]);;

let INTEGRAL_PASTECART_SYM = prove
 (`!f:real^(M,N)finite_sum->real^P s y.
        integral
           (IMAGE (\z. pastecart (sndcart z) (fstcart z)) s)
           (\z. f(pastecart (sndcart z) (fstcart z))) =
        integral s f`,
  REWRITE_TAC[integral; HAS_INTEGRAL_PASTECART_SYM]);;

let INTEGRABLE_PASTECART_SYM = prove
 (`!f:real^(M,N)finite_sum->real^P s y.
        (\z. f(pastecart (sndcart z) (fstcart z))) integrable_on
        (IMAGE (\z. pastecart (sndcart z) (fstcart z)) s) <=>
        f integrable_on s`,
  REWRITE_TAC[integrable_on; HAS_INTEGRAL_PASTECART_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Hence a general restriction property.                                     *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_RESTRICT = prove
 (`!f:real^M->real^N s t i.
        s SUBSET t
        ==> (((\x. if x IN s then f x else vec 0) has_integral i) t <=>
             (f has_integral i) s)`,
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL] THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[MESON[] `(if p then if q then x else y else y) =
                            (if q then if p then x else y else y)`] THEN
  ASM_SIMP_TAC[]);;

let INTEGRAL_RESTRICT = prove
 (`!f:real^M->real^N s t.
        s SUBSET t
        ==> integral t (\x. if x IN s then f x else vec 0) =
            integral s f`,
  SIMP_TAC[integral; HAS_INTEGRAL_RESTRICT]);;

let INTEGRABLE_RESTRICT = prove
 (`!f:real^M->real^N s t.
        s SUBSET t
        ==> ((\x. if x IN s then f x else vec 0) integrable_on t <=>
             f integrable_on s)`,
  SIMP_TAC[integrable_on; HAS_INTEGRAL_RESTRICT]);;

let HAS_INTEGRAL_RESTRICT_UNIV = prove
 (`!f:real^M->real^N s i.
        ((\x. if x IN s then f x else vec 0) has_integral i) (:real^M) <=>
         (f has_integral i) s`,
  SIMP_TAC[HAS_INTEGRAL_RESTRICT; SUBSET_UNIV]);;

let INTEGRAL_RESTRICT_UNIV = prove
 (`!f:real^M->real^N s.
        integral (:real^M) (\x. if x IN s then f x else vec 0) =
        integral s f`,
  REWRITE_TAC[integral; HAS_INTEGRAL_RESTRICT_UNIV]);;

let INTEGRABLE_RESTRICT_UNIV = prove
 (`!f s. (\x. if x IN s then f x else vec 0) integrable_on (:real^M) <=>
         f integrable_on s`,
  REWRITE_TAC[integrable_on; HAS_INTEGRAL_RESTRICT_UNIV]);;

let HAS_INTEGRAL_RESTRICT_INTER = prove
 (`!f:real^M->real^N s t.
        ((\x. if x IN s then f x else vec 0) has_integral i) t <=>
        (f has_integral i) (s INTER t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[IN_INTER] THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

let INTEGRAL_RESTRICT_INTER = prove
 (`!f:real^M->real^N s t.
        integral t (\x. if x IN s then f x else vec 0) =
        integral (s INTER t) f`,
  REWRITE_TAC[integral; HAS_INTEGRAL_RESTRICT_INTER]);;

let INTEGRABLE_RESTRICT_INTER = prove
 (`!f:real^M->real^N s t.
        (\x. if x IN s then f x else vec 0) integrable_on t <=>
        f integrable_on (s INTER t)`,
  REWRITE_TAC[integrable_on; HAS_INTEGRAL_RESTRICT_INTER]);;

let HAS_INTEGRAL_ON_SUPERSET = prove
 (`!f s t.
        (!x. ~(x IN s) ==> f x = vec 0) /\ s SUBSET t /\ (f has_integral i) s
        ==> (f has_integral i) t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[]);;

let INTEGRABLE_ON_SUPERSET = prove
 (`!f s t.
        (!x. ~(x IN s) ==> f x = vec 0) /\ s SUBSET t /\ f integrable_on s
        ==> f integrable_on t`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_ON_SUPERSET]);;

let NEGLIGIBLE_ON_INTERVALS = prove
 (`!s. negligible s <=> !a b:real^N. negligible(s INTER interval[a,b])`,
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[negligible] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  FIRST_ASSUM(ASSUME_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
  MATCH_MP_TAC HAS_INTEGRAL_NEGLIGIBLE THEN
  EXISTS_TAC `s INTER interval[a:real^N,b]` THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[indicator; IN_DIFF; IN_INTER] THEN
  MESON_TAC[]);;

let NEGLIGIBLE_BOUNDED_SUBSETS = prove
 (`!s:real^N->bool.
    negligible s <=> !t. bounded t /\ t SUBSET s ==> negligible t`,
  MESON_TAC[NEGLIGIBLE_ON_INTERVALS; INTER_SUBSET; BOUNDED_SUBSET;
            BOUNDED_INTERVAL; NEGLIGIBLE_SUBSET]);;

let NEGLIGIBLE_ON_COUNTABLE_INTERVALS = prove
 (`!s:real^N->bool.
        negligible s <=>
        !n. negligible (s INTER interval[--vec n,vec n])`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [NEGLIGIBLE_ON_INTERVALS] THEN
  EQ_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b:real^N. ?n. s INTER interval[a,b] =
                     ((s INTER interval[--vec n,vec n]) INTER interval[a,b])`
   (fun th -> ASM_MESON_TAC[th; NEGLIGIBLE_ON_INTERVALS]) THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`interval[a:real^N,b]`; `vec 0:real^N`]
        BOUNDED_SUBSET_CBALL) THEN
  REWRITE_TAC[BOUNDED_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `r:real` REAL_ARCH_SIMPLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `i SUBSET b ==> b SUBSET n ==> s INTER i = (s INTER n) INTER i`)) THEN
  REWRITE_TAC[SUBSET; IN_CBALL_0; IN_INTERVAL; VEC_COMPONENT;
              VECTOR_NEG_COMPONENT; GSYM REAL_ABS_BOUNDS]  THEN
  ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]);;

let HAS_INTEGRAL_SPIKE_SET_EQ = prove
 (`!f:real^M->real^N s t y.
        negligible(s DIFF t UNION t DIFF s)
        ==> ((f has_integral y) s <=> (f has_integral y) t)`,
  REPEAT STRIP_TAC THEN  ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE_EQ THEN
  EXISTS_TAC `s DIFF t UNION t DIFF s:real^M->bool` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let HAS_INTEGRAL_SPIKE_SET = prove
 (`!f:real^M->real^N s t y.
        negligible(s DIFF t UNION t DIFF s) /\
        (f has_integral y) s
        ==> (f has_integral y) t`,
  MESON_TAC[HAS_INTEGRAL_SPIKE_SET_EQ]);;

let INTEGRABLE_SPIKE_SET = prove
 (`!f:real^M->real^N s t.
        negligible(s DIFF t UNION t DIFF s)
        ==> f integrable_on s ==> f integrable_on t`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_SPIKE_SET_EQ]);;

let INTEGRABLE_SPIKE_SET_EQ = prove
 (`!f:real^M->real^N s t.
        negligible(s DIFF t UNION t DIFF s)
        ==> (f integrable_on s <=> f integrable_on t)`,
  MESON_TAC[INTEGRABLE_SPIKE_SET; UNION_COMM]);;

let INTEGRAL_SPIKE_SET = prove
 (`!f:real^M->real^N g s t.
        negligible(s DIFF t UNION t DIFF s)
        ==> integral s f = integral t f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  ASM_MESON_TAC[]);;

let HAS_INTEGRAL_INTERIOR = prove
 (`!f:real^M->real^N y s.
        negligible(frontier s)
        ==> ((f has_integral y) (interior s) <=> (f has_integral y) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^M->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^M->bool` CLOSURE_SUBSET) THEN
  SET_TAC[]);;

let HAS_INTEGRAL_CLOSURE = prove
 (`!f:real^M->real^N y s.
        negligible(frontier s)
        ==> ((f has_integral y) (closure s) <=> (f has_integral y) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^M->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^M->bool` CLOSURE_SUBSET) THEN
  SET_TAC[]);;

let INTEGRABLE_CASES = prove
 (`!f g:real^M->real^N s.
        f integrable_on {x | x IN s /\ P x} /\
        g integrable_on {x | x IN s /\ ~P x}
        ==> (\x. if P x then f x else g x) integrable_on s`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_ADD) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] INTEGRABLE_EQ) THEN
  REWRITE_TAC[IN_UNIV; IN_ELIM_THM] THEN
  MESON_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID]);;

(* ------------------------------------------------------------------------- *)
(* More lemmas that are useful later.                                        *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_DROP_POS_AE = prove
 (`!f:real^M->real^1 s t i.
        (f has_integral i) s /\
        negligible t /\ (!x. x IN s DIFF t ==> &0 <= drop(f x))
        ==> &0 <= drop i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_DROP_POS THEN
  EXISTS_TAC `f:real^M->real^1` THEN EXISTS_TAC `s DIFF t:real^M->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN
  SET_TAC[]);;

let INTEGRAL_DROP_POS_AE = prove
 (`!f:real^M->real^1 s t.
        f integrable_on s /\
        negligible t /\ (!x. x IN s DIFF t ==> &0 <= drop(f x))
        ==> &0 <= drop(integral s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_DROP_POS_AE THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_SUBSET_COMPONENT_LE = prove
 (`!f:real^M->real^N s t i j k.
        s SUBSET t /\ (f has_integral i) s /\ (f has_integral j) t /\
        1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN t ==> &0 <= f(x)$k)
        ==> i$k <= j$k`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_LE THEN
  MAP_EVERY EXISTS_TAC
   [`(\x. if x IN s then f x else vec 0):real^M->real^N`;
    `(\x. if x IN t then f x else vec 0):real^M->real^N`;
    `(:real^M)`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]) THEN
  ASM_SIMP_TAC[VEC_COMPONENT] THEN ASM SET_TAC[]);;

let INTEGRAL_SUBSET_COMPONENT_LE = prove
 (`!f:real^M->real^N s t k.
        s SUBSET t /\ f integrable_on s /\ f integrable_on t /\
        1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN t ==> &0 <= f(x)$k)
        ==> (integral s f)$k <= (integral t f)$k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SUBSET_COMPONENT_LE THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_SUBSET_DROP_LE = prove
 (`!f:real^M->real^1 s t i j.
        s SUBSET t /\ (f has_integral i) s /\ (f has_integral j) t /\
        (!x. x IN t ==> &0 <= drop(f x))
        ==> drop i <= drop j`,
  REWRITE_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_SUBSET_COMPONENT_LE THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN ASM_MESON_TAC[]);;

let INTEGRAL_SUBSET_DROP_LE = prove
 (`!f:real^M->real^1 s t.
        s SUBSET t /\ f integrable_on s /\ f integrable_on t /\
        (!x. x IN t ==> &0 <= drop(f(x)))
        ==> drop(integral s f) <= drop(integral t f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SUBSET_DROP_LE THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_ALT = prove
 (`!f:real^M->real^N s i.
        (f has_integral i) s <=>
            (!a b. (\x. if x IN s then f x else vec 0)
                   integrable_on interval[a,b]) /\
            (!e. &0 < e
                 ==> ?B. &0 < B /\
                         !a b. ball (vec 0,B) SUBSET interval[a,b]
                               ==> norm(integral(interval[a,b])
                                          (\x. if x IN s then f x else vec 0) -
                                        i) < e)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL] THEN
  SPEC_TAC(`\x. if x IN s then (f:real^M->real^N) x else vec 0`,
           `f:real^M->real^N`) THEN
  GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[INTEGRAL_UNIQUE; integrable_on]] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[INTEGRAL_UNIQUE]] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  POP_ASSUM(MP_TAC o C MATCH_MP REAL_LT_01) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
  EXISTS_TAC `(lambda i. min ((a:real^M)$i) (--B)):real^M` THEN
  EXISTS_TAC `(lambda i. max ((b:real^M)$i) B):real^M` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
     [`(lambda i. min ((a:real^M)$i) (--B)):real^M`;
      `(lambda i. max ((b:real^M)$i) B):real^M`]) THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[integrable_on]];
    SIMP_TAC[SUBSET; IN_INTERVAL; IN_BALL; LAMBDA_BETA;
             REAL_MIN_LE; REAL_LE_MAX]] THEN
  SIMP_TAC[SUBSET; IN_BALL; IN_INTERVAL; LAMBDA_BETA] THEN
  GEN_TAC THEN REWRITE_TAC[NORM_ARITH `dist(vec 0,x) = norm x`] THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
    `abs(x) <= B ==> min a (--B) <= x /\ x <= max b B`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^M)` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; COMPONENT_LE_NORM]);;

let INTEGRABLE_ALT = prove
 (`!f:real^M->real^N s.
        f integrable_on s <=>
          (!a b. (\x. if x IN s then f x else vec 0) integrable_on
                 interval[a,b]) /\
          (!e. &0 < e
               ==> ?B. &0 < B /\
                       !a b c d.
                          ball(vec 0,B) SUBSET interval[a,b] /\
                          ball(vec 0,B) SUBSET interval[c,d]
                          ==> norm(integral (interval[a,b])
                                    (\x. if x IN s then f x else vec 0) -
                                   integral (interval[c,d])
                                    (\x. if x IN s then f x else vec 0)) < e)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [integrable_on] THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL_ALT] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
    MESON_TAC[NORM_ARITH `norm(a - y) < e / &2 /\ norm(b - y) < e / &2
                          ==> norm(a - b) < e`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `cauchy (\n. integral (interval[(lambda i. --(&n)),(lambda i. &n)])
                         (\x. if x IN s then (f:real^M->real^N) x else vec 0))`
  MP_TAC THENL
   [REWRITE_TAC[cauchy] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `B:real` REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[dist] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_BALL; NORM_ARITH `dist(vec 0,x) = norm x`] THEN
    CONJ_TAC;
    REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:real^N` THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_THEN(LABEL_TAC "C") THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "C" (MP_TAC o SPEC `e / &2`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
    MP_TAC(SPEC `max (&N) B` REAL_ARCH_SIMPLE) THEN
    REWRITE_TAC[REAL_MAX_LE; REAL_OF_NUM_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `&n` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(i1 - i2) < e / &2 ==> dist(i1,i) < e / &2 ==> norm(i2 - i) < e`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^M,&n)` THEN
    ASM_SIMP_TAC[SUBSET_BALL] THEN
    REWRITE_TAC[SUBSET; IN_BALL; NORM_ARITH `dist(vec 0,x) = norm x`]] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  SIMP_TAC[IN_INTERVAL; LAMBDA_BETA] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_BOUNDS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(x:real^M)` THEN ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM REAL_OF_NUM_GE] THEN
  REAL_ARITH_TAC);;

let INTEGRABLE_ALT_SUBSET = prove
 (`!f:real^M->real^N s.
        f integrable_on s <=>
          (!a b. (\x. if x IN s then f x else vec 0) integrable_on
                 interval[a,b]) /\
          (!e. &0 < e
               ==> ?B. &0 < B /\
                       !a b c d.
                          ball(vec 0,B) SUBSET interval[a,b] /\
                          interval[a,b] SUBSET interval[c,d]
                          ==> norm(integral (interval[a,b])
                                    (\x. if x IN s then f x else vec 0) -
                                   integral (interval[c,d])
                                    (\x. if x IN s then f x else vec 0)) < e)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [INTEGRABLE_ALT] THEN
  ABBREV_TAC `g:real^M->real^N = \x. if x IN s then f x else vec 0` THEN
  POP_ASSUM(K ALL_TAC) THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN EQ_TAC THENL [MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `c:real^M`; `d:real^M`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(lambda i. max ((a:real^M)$i) ((c:real^M)$i)):real^M`;
    `(lambda i. min ((b:real^M)$i) ((d:real^M)$i)):real^M`]) THEN
  ASM_REWRITE_TAC[GSYM INTER_INTERVAL; SUBSET_INTER] THEN
  DISCH_THEN(fun th ->
    MP_TAC(ISPECL [`a:real^M`; `b:real^M`] th) THEN
    MP_TAC(ISPECL [`c:real^M`; `d:real^M`] th)) THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN NORM_ARITH_TAC);;

let INTEGRABLE_ON_SUBINTERVAL = prove
 (`!f:real^M->real^N s a b.
        f integrable_on s /\ interval[a,b] SUBSET s
        ==> f integrable_on interval[a,b]`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [INTEGRABLE_ALT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONJUNCT1) ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `b:real^M`]) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] INTEGRABLE_EQ) THEN
  ASM SET_TAC[]);;

let INTEGRAL_SPLIT = prove
 (`!f:real^M->real^N a b t k.
        f integrable_on interval[a,b] /\ 1 <= k /\ k <= dimindex(:M)
        ==> integral (interval[a,b]) f =
                integral(interval
                 [a,(lambda i. if i = k then min (b$k) t else b$i)]) f +
                integral(interval
                 [(lambda i. if i = k then max (a$k) t else a$i),b]) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPLIT THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `t:real`] THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT; GSYM HAS_INTEGRAL_INTEGRAL] THEN
  CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `interval[a:real^M,b]` THEN
  ASM_SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let INTEGRAL_SPLIT_SIGNED = prove
 (`!f:real^M->real^N a b t k.
        1 <= k /\ k <= dimindex(:M) /\ a$k <= t /\ a$k <= b$k /\
        f integrable_on
        interval[a,(lambda i. if i = k then max (b$k) t else b$i)]
        ==> integral (interval[a,b]) f =
                integral(interval
                 [a,(lambda i. if i = k then t else b$i)]) f +
                (if b$k < t then -- &1 else &1) %
                integral(interval
                 [(lambda i. if i = k then min (b$k) t else a$i),
                  (lambda i. if i = k then max (b$k) t else b$i)]) f`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL
    [`f:real^M->real^N`;
     `a:real^M`;
     `(lambda i. if i = k then t else (b:real^M)$i):real^M`;
     `(b:real^M)$k`; `k:num`]
        INTEGRAL_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] INTEGRABLE_ON_SUBINTERVAL)) THEN
      ASM_SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(VECTOR_ARITH
       `x = y /\ w = z
        ==> x:real^N = (y + z) + --(&1) % w`) THEN
      CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[CONS_11; PAIR_EQ; CART_EQ] THEN TRY CONJ_TAC THEN
      ASM_SIMP_TAC[LAMBDA_BETA] THEN
      GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL
    [`f:real^M->real^N`;
     `a:real^M`;
     `b:real^M`;
     `t:real`; `k:num`]
        INTEGRAL_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] INTEGRABLE_ON_SUBINTERVAL)) THEN
      ASM_SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_LID] THEN
      BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[CONS_11; PAIR_EQ; CART_EQ] THEN TRY CONJ_TAC THEN
      ASM_SIMP_TAC[LAMBDA_BETA] THEN
      GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      ASM_REAL_ARITH_TAC]]);;

let INTEGRAL_INTERVALS_INCLUSION_EXCLUSION = prove
 (`!f:real^M->real^N a b c d.
        f integrable_on interval[a,b] /\
        c IN interval[a,b] /\ d IN interval[a,b]
        ==> integral(interval[a,d]) f =
                vsum {s | s SUBSET 1..dimindex(:M)}
                    (\s. --(&1) pow CARD {i | i IN s /\ d$i < c$i} %
                         integral
                          (interval[(lambda i. if i IN s
                                               then min (c$i) (d$i)
                                               else (a:real^M)$i),
                                    (lambda i. if i IN s
                                               then max (c$i) (d$i)
                                               else c$i)]) f)`,
  let lemma1 = prove
   (`!f:(num->bool)->real^N n.
          vsum {s | s SUBSET 1..SUC n} f =
          vsum {s | s SUBSET 1..n} f +
          vsum {s | s SUBSET 1..n} (\s. f(SUC n INSERT s))`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[NUMSEG_CLAUSES; ARITH_RULE `1 <= SUC n`; POWERSET_CLAUSES] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_UNION o lhs o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_POWERSET; FINITE_NUMSEG] THEN
      REWRITE_TAC[SET_RULE
       `DISJOINT s (IMAGE f t) <=> !x. x IN t ==> ~(f x IN s)`] THEN
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN
      REWRITE_TAC[IN_INSERT; IN_NUMSEG] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] VSUM_IMAGE) THEN
      SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG] THEN
      MAP_EVERY X_GEN_TAC [`s:num->bool`; `t:num->bool`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC(SET_RULE
       `~(a IN i)
        ==> s SUBSET i /\ t SUBSET i /\ a INSERT s = a INSERT t
            ==> s = t`) THEN
      REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC]) in
  let lemma2 = prove
   (`!f:real^M->real^N m a:real^M c:real^M d:real^M.
          f integrable_on (:real^M) /\ m <= dimindex(:M) /\
          (!i. m < i /\ i <= dimindex(:M) ==> a$i = c$i \/ d$i = c$i) /\
          (!i. m < i /\ i <= dimindex(:M) ==> a$i = c$i ==> a$i = d$i) /\
          (!i. 1 <= i /\ i <= dimindex(:M) ==> a$i <= c$i /\ a$i <= d$i)
          ==> integral(interval[a,d]) f =
                  vsum {s | s SUBSET 1..m}
                      (\s. --(&1) pow CARD {i | i IN s /\ d$i < c$i} %
                           integral
                            (interval[(lambda i. if i IN s
                                                 then min (c$i) (d$i)
                                                 else (a:real^M)$i),
                                      (lambda i. if i IN s
                                                 then max (c$i) (d$i)
                                                 else c$i)]) f)`,
    GEN_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC[NUMSEG_CLAUSES; ARITH; SUBSET_EMPTY; SING_GSPEC] THEN
      REWRITE_TAC[VSUM_SING; NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES] THEN
      REWRITE_TAC[real_pow; LAMBDA_ETA; VECTOR_MUL_LID] THEN
      REWRITE_TAC[ARITH_RULE `0 < i <=> 1 <= i`] THEN REPEAT STRIP_TAC THEN
      ASM_CASES_TAC
       `?k. 1 <= k /\ k <= dimindex(:M) /\ (a:real^M)$k = (c:real^M)$k`
      THENL
       [MATCH_MP_TAC(MESON[] `i = vec 0 /\ j = vec 0 ==> i:real^N = j`) THEN
        CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_NULL THEN
        REWRITE_TAC[CONTENT_EQ_0] THEN ASM_MESON_TAC[];
        SUBGOAL_THEN `d:real^M = c:real^M` (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[CART_EQ] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[lemma1] THEN
    SUBGOAL_THEN
     `!s. s SUBSET 1..m
          ==> --(&1) pow CARD {i | i IN SUC m INSERT s /\ d$i < c$i} =
              (if (d:real^M)$(SUC m) < (c:real^M)$(SUC m) then -- &1 else &1) *
              --(&1) pow CARD {i | i IN s /\ d$i < c$i}`
     (fun th -> SIMP_TAC[th; IN_ELIM_THM]) THENL
     [X_GEN_TAC `s:num->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `FINITE(s:num->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[FINITE_NUMSEG; FINITE_SUBSET]; ALL_TAC] THEN
      COND_CASES_TAC THENL
       [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RESTRICT; SET_RULE
         `P a ==> {x | x IN a INSERT s /\ P x} =
                  a INSERT {x | x IN s /\ P x}`] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[real_pow] THEN
        SUBGOAL_THEN `~(SUC m IN 1..m)` (fun th -> ASM SET_TAC[th]) THEN
        REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
        ASM_SIMP_TAC[REAL_MUL_LID; SET_RULE
         `~(P a) ==> {x | x IN a INSERT s /\ P x} = {x | x IN s /\ P x}`]];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`f:real^M->real^N`; `a:real^M`; `d:real^M`; `(c:real^M)$SUC m`; `SUC m`]
         INTEGRAL_SPLIT_SIGNED) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `1 <= SUC n`; INTEGRABLE_ON_SUBINTERVAL;
                    SUBSET_UNIV];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[VSUM_LMUL; GSYM VECTOR_MUL_ASSOC] THEN
    BINOP_TAC THENL [ALL_TAC; AP_TERM_TAC] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL
       [`a:real^M`;
        `c:real^M`;
        `(lambda i. if i = SUC m then (c:real^M)$SUC m
                    else (d:real^M)$i):real^M`]);
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`(lambda i. if i = SUC m
                    then min ((d:real^M)$SUC m) ((c:real^M)$SUC m)
                    else (a:real^M)$i):real^M`;
        `(lambda i. if i = SUC m
                    then max ((d:real^M)$SUC m) ((c:real^M)$SUC m)
                    else (c:real^M)$i):real^M`;
        `(lambda i. if i = SUC m
                    then max ((d:real^M)$SUC m) ((c:real^M)$SUC m)
                    else d$i):real^M`])] THEN
    (ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN
       CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
       CONJ_TAC THENL
        [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
         SUBGOAL_THEN `1 <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
         ASM_SIMP_TAC[LAMBDA_BETA] THEN
         COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
         FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
         ALL_TAC] THEN
       CONJ_TAC THENL
        [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
         SUBGOAL_THEN `1 <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
         ASM_SIMP_TAC[LAMBDA_BETA] THEN
         COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
         ASM_MESON_TAC[ARITH_RULE `m < i <=> i = SUC m \/ SUC m < i`];
         X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
         COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN TRY REAL_ARITH_TAC THEN
         FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
         ASM_MESON_TAC[]];
       DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
       X_GEN_TAC `s:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
       DISCH_TAC THEN BINOP_TAC THENL
        [AP_TERM_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
         X_GEN_TAC `i:num` THEN
         ASM_CASES_TAC `(i:num) IN s` THEN ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `i IN 1..m` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
         REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
         SUBGOAL_THEN `i <= dimindex(:M)` ASSUME_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         ASM_SIMP_TAC[LAMBDA_BETA] THEN
         COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
         AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[CONS_11; PAIR_EQ] THEN
         SIMP_TAC[CART_EQ; LAMBDA_BETA; AND_FORALL_THM] THEN
         X_GEN_TAC `i:num` THEN
         ASM_CASES_TAC `1 <= i /\ i <= dimindex(:M)` THEN
         ASM_REWRITE_TAC[] THEN
         ASM_CASES_TAC `(i:num) IN s` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
         COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TRY REAL_ARITH_TAC THEN
         SUBGOAL_THEN `~(SUC m IN 1..m)` (fun th -> ASM SET_TAC[th]) THEN
         REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC]])) in
  REWRITE_TAC[IN_INTERVAL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. if x IN interval[a,b] then (f:real^M->real^N) x else vec 0`;
    `dimindex(:M)`; `a:real^M`; `c:real^M`; `d:real^M`]
   lemma2) THEN
  ASM_SIMP_TAC[LTE_ANTISYM; INTEGRABLE_RESTRICT_UNIV; LE_REFL] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `s:num->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN AP_TERM_TAC] THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `i SUBSET j ==> !x. x IN i ==> (if x IN j then f x else b) = f x`) THEN
  ASM_SIMP_TAC[SUBSET_INTERVAL; REAL_LE_REFL; LAMBDA_BETA] THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let INTEGRAL_INTERVALS_DIFF_INCLUSION_EXCLUSION = prove
 (`!f:real^M->real^N a b c d.
        f integrable_on interval[a,b] /\
        c IN interval[a,b] /\ d IN interval[a,b]
        ==> integral(interval[a,d]) f - integral(interval[a,c]) f =
                vsum {s | ~(s = {}) /\ s SUBSET 1..dimindex(:M)}
                    (\s. --(&1) pow CARD {i | i IN s /\ d$i < c$i} %
                         integral
                          (interval[(lambda i. if i IN s
                                               then min (c$i) (d$i)
                                               else (a:real^M)$i),
                                    (lambda i. if i IN s
                                               then max (c$i) (d$i)
                                               else c$i)]) f)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o
   MATCH_MP INTEGRAL_INTERVALS_INCLUSION_EXCLUSION) THEN
  REWRITE_TAC[SET_RULE `{s | ~(s = a) /\ P s} = {s | P s} DELETE a`] THEN
  SIMP_TAC[VSUM_DELETE; FINITE_POWERSET; FINITE_NUMSEG; EMPTY_SUBSET;
           IN_ELIM_THM] THEN
  REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES; LAMBDA_ETA] THEN
  REWRITE_TAC[real_pow; VECTOR_MUL_LID]);;

let INTEGRAL_INTERVALS_INCLUSION_EXCLUSION_RIGHT = prove
 (`!f:real^M->real^N a b c.
        f integrable_on interval[a,b] /\ c IN interval[a,b]
        ==> integral(interval[a,c]) f =
                vsum {s | s SUBSET 1..dimindex (:M)}
                     (\s. --(&1) pow CARD s %
                          integral
                           (interval[(lambda i. if i IN s then c$i else a$i),
                                     b])
                           f)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`f:real^M->real^N`; `a:real^M`; `b:real^M`; `b:real^M`; `c:real^M`]
        INTEGRAL_INTERVALS_INCLUSION_EXCLUSION) THEN
  ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_INTERVAL; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  X_GEN_TAC `s:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_CASES_TAC `?k. k IN s /\ (c:real^M)$k = (b:real^M)$k` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `1 <= k /\ k <= dimindex(:M)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_NUMSEG; SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[] `a:real^N = vec 0 /\ b = vec 0 ==> a = b`) THEN
    CONJ_TAC THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
    MATCH_MP_TAC INTEGRAL_NULL THEN REWRITE_TAC[CONTENT_EQ_0] THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN BINOP_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[REAL_LT_LE; SUBSET; IN_NUMSEG];
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CART_EQ; PAIR_EQ; LAMBDA_BETA] THEN
    CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let INTEGRAL_INTERVALS_INCLUSION_EXCLUSION_LEFT = prove
 (`!f:real^M->real^N a b c.
        f integrable_on interval[a,b] /\ c IN interval[a,b]
        ==> integral(interval[c,b]) f =
                vsum {s | s SUBSET 1..dimindex (:M)}
                     (\s. --(&1) pow CARD s %
                          integral
                           (interval[a,(lambda i. if i IN s then c$i else b$i)])
                           f)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\x. (f:real^M->real^N) (--x)`;
    `--b:real^M`;
    `--a:real^M`;
    `--c:real^M`]
        INTEGRAL_INTERVALS_INCLUSION_EXCLUSION_RIGHT) THEN
  REWRITE_TAC[REAL_ARITH `min (--a) (--b) = --(max a b)`;
              REAL_ARITH `max (--a) (--b) = --(min a b)`;
              VECTOR_NEG_COMPONENT] THEN
  SUBGOAL_THEN
   `!P x y. (lambda i. if P i then --(x i) else --(y i)):real^M =
            --(lambda i. if P i then x i else y i)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [SIMP_TAC[CART_EQ; VECTOR_NEG_COMPONENT; LAMBDA_BETA] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INTEGRAL_REFLECT; INTEGRABLE_REFLECT;
                  IN_INTERVAL_REFLECT]);;

let HAS_INTEGRAL_REFLECT_GEN = prove
 (`!f:real^M->real^N i s.
     ((\x. f(--x)) has_integral i) s <=> (f has_integral i) (IMAGE (--) s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HAS_INTEGRAL_ALT] THEN
  REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM INTEGRABLE_REFLECT; GSYM INTEGRAL_REFLECT] THEN
  REWRITE_TAC[IN_IMAGE; VECTOR_NEG_NEG] THEN
  REWRITE_TAC[UNWIND_THM1; VECTOR_ARITH `x:real^N = --y <=> --x = y`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MESON[VECTOR_NEG_NEG]
   `(!x:real^N y:real^N. P x y) <=> (!x y. P (--y) (--x))`] THEN
  REWRITE_TAC[VECTOR_NEG_NEG] THEN
  REWRITE_TAC[SUBSET; IN_BALL_0; GSYM REFLECT_INTERVAL; IN_IMAGE] THEN
  REWRITE_TAC[UNWIND_THM1; VECTOR_ARITH `x:real^N = --y <=> --x = y`] THEN
  ONCE_REWRITE_TAC[GSYM NORM_NEG] THEN
  REWRITE_TAC[MESON[VECTOR_NEG_NEG] `(!x:real^N. P (--x)) <=> (!x. P x)`] THEN
  REWRITE_TAC[NORM_NEG]);;

let INTEGRABLE_REFLECT_GEN = prove
 (`!f:real^M->real^N s.
        (\x. f(--x)) integrable_on s <=> f integrable_on (IMAGE (--) s)`,
  REWRITE_TAC[integrable_on; HAS_INTEGRAL_REFLECT_GEN]);;

let INTEGRAL_REFLECT_GEN = prove
 (`!f:real^M->real^N s.
        integral s (\x. f(--x)) = integral (IMAGE (--) s) f`,
   REWRITE_TAC[integral; HAS_INTEGRAL_REFLECT_GEN]);;

(* ------------------------------------------------------------------------- *)
(* A straddling criterion for integrability.                                 *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_STRADDLE_INTERVAL = prove
 (`!f:real^N->real^1 a b.
        (!e. &0 < e
             ==> ?g h i j. (g has_integral i) (interval[a,b]) /\
                           (h has_integral j) (interval[a,b]) /\
                           norm(i - j) < e /\
                           !x. x IN interval[a,b]
                               ==> drop(g x) <= drop(f x) /\
                                   drop(f x) <= drop(h x))
        ==> f integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTEGRABLE_CAUCHY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real^N->real^1`; `h:real^N->real^1`; `i:real^1`; `j:real^1`] THEN
  REWRITE_TAC[has_integral] THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^N->real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^N->real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `(\x. d1 x INTER d2 x):real^N->real^N->bool` THEN
  ASM_SIMP_TAC[GAUGE_INTER; FINE_INTER] THEN
  MAP_EVERY X_GEN_TAC
   [`p1:(real^N#(real^N->bool))->bool`;
    `p2:(real^N#(real^N->bool))->bool`] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
   MP_TAC(SPEC `p1:(real^N#(real^N->bool))->bool` th) THEN
   MP_TAC(SPEC `p2:(real^N#(real^N->bool))->bool` th))) THEN
  EVERY_ASSUM(fun th -> try ASSUME_TAC(MATCH_MP TAGGED_DIVISION_OF_FINITE th)
                        with Failure _ -> ALL_TAC) THEN
  ASM_SIMP_TAC[VSUM_REAL] THEN REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM] THEN
  SUBST1_TAC(SYM(ISPEC `i:real^1` (CONJUNCT1 LIFT_DROP))) THEN
  SUBST1_TAC(SYM(ISPEC `j:real^1` (CONJUNCT1 LIFT_DROP))) THEN
  REWRITE_TAC[GSYM LIFT_SUB; DROP_CMUL; NORM_LIFT] THEN
  MATCH_MP_TAC(REAL_ARITH
   `g1 - h2 <= f1 - f2 /\ f1 - f2 <= h1 - g2 /\
    abs(i - j) < e / &3
    ==> abs(g2 - i) < e / &3
        ==> abs(g1 - i) < e / &3
            ==> abs(h2 - j) < e / &3
                ==> abs(h1 - j) < e / &3
                    ==> abs(f1 - f2) < e`) THEN
  ASM_REWRITE_TAC[GSYM DROP_SUB; GSYM NORM_LIFT; LIFT_DROP] THEN CONJ_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= x' /\ y' <= y ==> x - y <= x' - y'`) THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_MESON_TAC[TAGGED_DIVISION_OF; CONTENT_POS_LE; SUBSET]);;

let INTEGRABLE_STRADDLE = prove
 (`!f:real^N->real^1 s.
        (!e. &0 < e
             ==> ?g h i j. (g has_integral i) s /\
                           (h has_integral j) s /\
                           norm(i - j) < e /\
                           !x. x IN s
                               ==> drop(g x) <= drop(f x) /\
                                   drop(f x) <= drop(h x))
        ==> f integrable_on s`,
  let lemma = prove
   (`&0 <= drop x /\ drop x <= drop y ==> norm x <= norm y`,
    REWRITE_TAC[NORM_REAL; GSYM drop] THEN REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. (\x. if x IN s then (f:real^N->real^1) x else vec 0)
          integrable_on interval[a,b]`
  ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[HAS_INTEGRAL_ALT]) THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
    MATCH_MP_TAC INTEGRABLE_STRADDLE_INTERVAL THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &4`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`g:real^N->real^1`; `h:real^N->real^1`; `i:real^1`; `j:real^1`] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `e / &4`) MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `e / &4`) STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `B2:real`
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))) THEN
    DISCH_THEN(X_CHOOSE_THEN `B1:real`
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G"))) THEN
    MAP_EVERY EXISTS_TAC
     [`\x. if x IN s then (g:real^N->real^1) x else vec 0`;
      `\x. if x IN s then (h:real^N->real^1) x else vec 0`;
      `integral(interval[a:real^N,b])
         (\x. if x IN s then (g:real^N->real^1) x else vec 0:real^1)`;
      `integral(interval[a:real^N,b])
         (\x. if x IN s then (h:real^N->real^1) x else vec 0:real^1)`] THEN
    ASM_SIMP_TAC[INTEGRABLE_INTEGRAL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_REFL]] THEN
    ABBREV_TAC `c:real^N = lambda i. min ((a:real^N)$i) (--(max B1 B2))` THEN
    ABBREV_TAC `d:real^N = lambda i. max ((b:real^N)$i) (max B1 B2)` THEN
    REMOVE_THEN "H" (MP_TAC o SPECL [`c:real^N`; `d:real^N`]) THEN
    REMOVE_THEN "G" (MP_TAC o SPECL [`c:real^N`; `d:real^N`]) THEN
    MATCH_MP_TAC(TAUT
        `(a /\ c) /\ (b /\ d ==> e) ==> (a ==> b) ==> (c ==> d) ==> e`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MAP_EVERY EXPAND_TAC ["c"; "d"] THEN
      SIMP_TAC[SUBSET; IN_BALL; IN_INTERVAL; LAMBDA_BETA] THEN
      GEN_TAC THEN REWRITE_TAC[NORM_ARITH `dist(vec 0,x) = norm x`] THEN
      DISCH_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
        `abs(x) <= B ==> min a (--B) <= x /\ x <= max b B`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^N)` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; COMPONENT_LE_NORM; REAL_LE_MAX];
      ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH
       `norm(i - j) < e / &4 /\
        norm(ah - ag) <= norm(ch - cg)
        ==> norm(cg - i) < e / &4 /\
            norm(ch - j) < e / &4
            ==> norm(ag - ah) < e`) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[GSYM INTEGRAL_SUB] THEN
    MATCH_MP_TAC lemma THEN CONJ_TAC THENL
     [MATCH_MP_TAC(INST_TYPE [`:N`,`:M`] HAS_INTEGRAL_DROP_POS) THEN
      MAP_EVERY EXISTS_TAC
       [`(\x. (if x IN s then h x else vec 0) - (if x IN s then g x else vec 0))
         :real^N->real^1`;
        `interval[a:real^N,b]`] THEN
      ASM_SIMP_TAC[INTEGRABLE_INTEGRAL; HAS_INTEGRAL_SUB] THEN
      ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRABLE_INTEGRAL] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[DROP_SUB; DROP_VEC; REAL_SUB_LE; REAL_POS] THEN
      ASM_MESON_TAC[REAL_LE_TRANS];
      ALL_TAC] THEN
    MATCH_MP_TAC(INST_TYPE [`:N`,`:M`] HAS_INTEGRAL_SUBSET_DROP_LE) THEN
    MAP_EVERY EXISTS_TAC
     [`(\x. (if x IN s then h x else vec 0) - (if x IN s then g x else vec 0))
       :real^N->real^1`;
      `interval[a:real^N,b]`; `interval[c:real^N,d]`] THEN
    ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRABLE_INTEGRAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET_INTERVAL] THEN DISCH_TAC THEN
      MAP_EVERY EXPAND_TAC ["c"; "d"] THEN
      SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[DROP_SUB; DROP_VEC; REAL_SUB_LE; REAL_POS] THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[INTEGRABLE_ALT] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; HAS_INTEGRAL_ALT] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real^N->real^1`; `h:real^N->real^1`; `i:real^1`; `j:real^1`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `e / &3`)) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `e / &3`)) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))) THEN
  EXISTS_TAC `max B1 B2` THEN
  ASM_REWRITE_TAC[REAL_LT_MAX; BALL_MAX_UNION; UNION_SUBSET] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[ABS_DROP; DROP_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!ga gc ha hc i j.
        ga <= fa /\ fa <= ha /\
        gc <= fc /\ fc <= hc /\
        abs(ga - i) < e / &3 /\
        abs(gc - i) < e / &3 /\
        abs(ha - j) < e / &3 /\
        abs(hc - j) < e / &3 /\
        abs(i - j) < e / &3
        ==> abs(fa - fc) < e`) THEN
  MAP_EVERY EXISTS_TAC
   [`drop(integral(interval[a:real^N,b]) (\x. if x IN s then g x else vec 0))`;
    `drop(integral(interval[c:real^N,d]) (\x. if x IN s then g x else vec 0))`;
    `drop(integral(interval[a:real^N,b]) (\x. if x IN s then h x else vec 0))`;
    `drop(integral(interval[c:real^N,d]) (\x. if x IN s then h x else vec 0))`;
    `drop i`; `drop j`] THEN
  REWRITE_TAC[GSYM DROP_SUB; GSYM ABS_DROP] THEN ASM_SIMP_TAC[] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL]);;

let HAS_INTEGRAL_STRADDLE_NULL = prove
 (`!f g:real^N->real^1 s.
        (!x. x IN s ==> &0 <= drop(f x) /\ drop(f x) <= drop(g x)) /\
        (g has_integral (vec 0)) s
        ==> (f has_integral (vec 0)) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_STRADDLE THEN
    GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(\x. vec 0):real^N->real^1`; `g:real^N->real^1`;
      `vec 0:real^1`; `vec 0:real^1`] THEN
    ASM_REWRITE_TAC[DROP_VEC; HAS_INTEGRAL_0; VECTOR_SUB_REFL; NORM_0];
    DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`f:real^N->real^1`; `g:real^N->real^1`]
        HAS_INTEGRAL_DROP_LE);
      MATCH_MP_TAC(ISPECL [`(\x. vec 0):real^N->real^1`; `f:real^N->real^1`]
        HAS_INTEGRAL_DROP_LE)] THEN
    EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; DROP_VEC; HAS_INTEGRAL_0]]);;

(* ------------------------------------------------------------------------- *)
(* Adding integrals over several sets.                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_UNION = prove
 (`!f:real^M->real^N i j s t.
        (f has_integral i) s /\ (f has_integral j) t /\ negligible(s INTER t)
        ==> (f has_integral (i + j)) (s UNION t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  EXISTS_TAC `(\x. if x IN (s INTER t) then &2 % f(x)
                   else if x IN (s UNION t) then f(x)
                   else vec 0):real^M->real^N` THEN
  EXISTS_TAC `s INTER t:real^M->bool` THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNION; IN_INTER; IN_UNIV] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_INTEGRAL_ADD) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(x:real^M) IN t`] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let INTEGRAL_UNION = prove
 (`!f:real^M->real^N s t.
        f integrable_on s /\ f integrable_on t /\ negligible(s INTER t)
        ==> integral (s UNION t) f = integral s f + integral t f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_UNION THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

let HAS_INTEGRAL_UNIONS = prove
 (`!f:real^M->real^N i t.
        FINITE t /\
        (!s. s IN t ==> (f has_integral (i s)) s) /\
        (!s s'. s IN t /\ s' IN t /\ ~(s = s') ==> negligible(s INTER s'))
        ==> (f has_integral (vsum t i)) (UNIONS t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_INTEGRAL_VSUM) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                HAS_INTEGRAL_SPIKE) THEN
  EXISTS_TAC
   `UNIONS (IMAGE (\(a,b). a INTER b :real^M->bool)
                  {a,b | a IN t /\ b IN {y | y IN t /\ ~(a = y)}})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
      ASM_SIMP_TAC[FINITE_RESTRICT];
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
      ASM_SIMP_TAC[IN_ELIM_THM]];
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_UNIV; IN_DIFF] THEN
    ASM_CASES_TAC `(x:real^M) IN UNIONS t` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[SET_RULE
       `~(x IN UNIONS t) <=> !s. s IN t ==> ~(x IN s)`]) THEN
      ASM_SIMP_TAC[VSUM_0]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^M->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; EXISTS_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^M->bool`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
    ASM_SIMP_TAC[MESON[]
     `x IN a /\ a IN t
      ==> ((!b. ~((b IN t /\ ~(a = b)) /\ x IN b)) <=>
           (!b. b IN t ==> (x IN b <=> b = a)))`] THEN
    ASM_REWRITE_TAC[VSUM_DELTA]]);;

let HAS_INTEGRAL_DIFF = prove
 (`!f:real^M->real^N i j s t.
    (f has_integral i) s /\
    (f has_integral j) t /\
    negligible (t DIFF s)
    ==> (f has_integral (i - j)) (s DIFF t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  EXISTS_TAC `(\x. if x IN (t DIFF s) then --(f x)
                   else if x IN (s DIFF t) then f x
                   else vec 0):real^M->real^N` THEN
  EXISTS_TAC `t DIFF s:real^M->bool` THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNION; IN_INTER; IN_UNIV] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(x:real^M) IN t`] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let INTEGRAL_DIFF = prove
 (`!f:real^M->real^N s t.
        f integrable_on s /\ f integrable_on t /\ negligible(t DIFF s)
        ==> integral (s DIFF t) f = integral s f - integral t f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_DIFF THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

(* ------------------------------------------------------------------------- *)
(* In particular adding integrals over a division, maybe not of an interval. *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMBINE_DIVISION = prove
 (`!f:real^M->real^N s d i.
        d division_of s /\
        (!k. k IN d ==> (f has_integral (i k)) k)
        ==> (f has_integral (vsum d i)) s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o last o CONJUNCTS o
              GEN_REWRITE_RULE I [division_of]) THEN
  MATCH_MP_TAC HAS_INTEGRAL_UNIONS THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_FINITE]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k1:real^M->bool`; `k2:real^M->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?u v:real^M x y:real^M.
                k1 = interval[u,v] /\ k2 = interval[x,y]`
   (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN SUBST_ALL_TAC))
  THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o el 2 o CONJUNCTS o
              GEN_REWRITE_RULE I [division_of]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`interval[u:real^M,v]`; `interval[x:real^M,y]`]) THEN
  ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN DISCH_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `(interval[u,v:real^M] DIFF interval(u,v)) UNION
              (interval[x,y] DIFF interval(x,y))` THEN
  SIMP_TAC[NEGLIGIBLE_FRONTIER_INTERVAL; NEGLIGIBLE_UNION] THEN
  ASM SET_TAC[]);;

let INTEGRAL_COMBINE_DIVISION_BOTTOMUP = prove
 (`!f:real^M->real^N d s.
        d division_of s /\ (!k. k IN d ==> f integrable_on k)
        ==> integral s f = vsum d (\i. integral i f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_DIVISION THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

let HAS_INTEGRAL_COMBINE_DIVISION_TOPDOWN = prove
 (`!f:real^M->real^N s d k.
        f integrable_on s /\ d division_of k /\ k SUBSET s
        ==> (f has_integral (vsum d (\i. integral i f))) k`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_DIVISION THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[division_of; SUBSET_TRANS]);;

let INTEGRAL_COMBINE_DIVISION_TOPDOWN = prove
 (`!f:real^M->real^N d s.
        f integrable_on s /\ d division_of s
        ==> integral s f = vsum d (\i. integral i f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_DIVISION_TOPDOWN THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL]);;

let INTEGRABLE_COMBINE_DIVISION = prove
 (`!f d s.
        d division_of s /\ (!i. i IN d ==> f integrable_on i)
        ==> f integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_COMBINE_DIVISION]);;

let INTEGRABLE_ON_SUBDIVISION = prove
 (`!f:real^M->real^N s d i.
        d division_of i /\
        f integrable_on s /\ i SUBSET s
        ==> f integrable_on i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_COMBINE_DIVISION THEN
  EXISTS_TAC `d:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  ASM_MESON_TAC[division_of; UNIONS_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Also tagged divisions.                                                    *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMBINE_TAGGED_DIVISION = prove
 (`!f:real^M->real^N s p i.
        p tagged_division_of s /\
        (!x k. (x,k) IN p ==> (f has_integral (i k)) k)
        ==> (f has_integral (vsum p (\(x,k). i k))) s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^M k:real^M->bool.
      (x,k) IN p ==> ((f:real^M->real^N) has_integral integral k f) k`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[HAS_INTEGRAL_INTEGRAL; integrable_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((f:real^M->real^N) has_integral
     (vsum (IMAGE SND (p:real^M#(real^M->bool)->bool))
           (\k. integral k f))) s`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_COMBINE_DIVISION THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    ASM_SIMP_TAC[DIVISION_OF_TAGGED_DIVISION];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum p (\(x:real^M,k:real^M->bool). integral k f:real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    ASM_MESON_TAC[HAS_INTEGRAL_UNIQUE];
    MATCH_MP_TAC VSUM_OVER_TAGGED_DIVISION_LEMMA THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[INTEGRAL_NULL]]);;

let INTEGRAL_COMBINE_TAGGED_DIVISION_BOTTOMUP = prove
 (`!f:real^M->real^N p a b.
        p tagged_division_of interval[a,b] /\
        (!x k. (x,k) IN p ==> f integrable_on k)
        ==> integral (interval[a,b]) f = vsum p (\(x,k). integral k f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_TAGGED_DIVISION THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

let HAS_INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN = prove
 (`!f:real^M->real^N a b p.
        f integrable_on interval[a,b] /\ p tagged_division_of interval[a,b]
        ==> (f has_integral (vsum p (\(x,k). integral k f))) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_TAGGED_DIVISION THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
  ASM_MESON_TAC[INTEGRABLE_SUBINTERVAL; TAGGED_DIVISION_OF]);;

let INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN = prove
 (`!f:real^M->real^N a b p.
        f integrable_on interval[a,b] /\ p tagged_division_of interval[a,b]
        ==> integral (interval[a,b]) f = vsum p (\(x,k). integral k f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Henstock's lemma.                                                         *)
(* ------------------------------------------------------------------------- *)

let HENSTOCK_LEMMA_PART1 = prove
 (`!f:real^M->real^N a b d e.
        f integrable_on interval[a,b] /\
        &0 < e /\ gauge d /\
        (!p. p tagged_division_of interval[a,b] /\ d fine p
             ==> norm (vsum p (\(x,k). content k % f x) -
                       integral(interval[a,b]) f) < e)
        ==> !p. p tagged_partial_division_of interval[a,b] /\ d fine p
                            ==> norm(vsum p (\(x,k). content k % f x -
                                                     integral k f)) <= e`,
  let lemma = prove
   (`(!k. &0 < k ==> x <= e + k) ==> x <= e`,
    DISCH_THEN(MP_TAC o SPEC `(x - e) / &2`) THEN REAL_ARITH_TAC) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC lemma THEN X_GEN_TAC `k:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
    [`IMAGE SND (p:(real^M#(real^M->bool))->bool)`; `a:real^M`; `b:real^M`]
    PARTIAL_DIVISION_EXTEND_INTERVAL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[PARTIAL_DIVISION_OF_TAGGED_DIVISION]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    ASM_MESON_TAC[tagged_partial_division_of; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(p:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP(SET_RULE
   `s SUBSET t ==> t = s UNION (t DIFF s)`)) THEN
  ABBREV_TAC `r = q DIFF IMAGE SND (p:(real^M#(real^M->bool))->bool)` THEN
  SUBGOAL_THEN `IMAGE SND (p:(real^M#(real^M->bool))->bool) INTER r = {}`
  ASSUME_TAC THENL [EXPAND_TAC "r" THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `FINITE(r:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[division_of; FINITE_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN r
        ==> ?p. p tagged_division_of i /\ d fine p /\
                norm(vsum p (\(x,j). content j % f x) -
                     integral i (f:real^M->real^N))
                < k / (&(CARD(r:(real^M->bool)->bool)) + &1)`
  MP_TAC THENL
   [X_GEN_TAC `i:real^M->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(i:real^M->bool) SUBSET interval[a,b]` ASSUME_TAC THENL
     [ASM_MESON_TAC[division_of; IN_UNION]; ALL_TAC] THEN
    SUBGOAL_THEN `?u v:real^M. i = interval[u,v]`
     (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[division_of; IN_UNION]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^M->real^N) integrable_on interval[u,v]` MP_TAC THENL
     [ASM_MESON_TAC[INTEGRABLE_SUBINTERVAL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
    REWRITE_TAC[has_integral] THEN
    DISCH_THEN(MP_TAC o SPEC `k / (&(CARD(r:(real^M->bool)->bool)) + &1)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &n + &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `dd:real^M->real^M->bool` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(ISPECL [`d:real^M->real^M->bool`; `dd:real^M->real^M->bool`]
      GAUGE_INTER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP FINE_DIVISION_EXISTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real^M`; `v:real^M`]) THEN
    REWRITE_TAC[FINE_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  REWRITE_TAC[TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(real^M->bool)->(real^M#(real^M->bool))->bool`
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `p UNION UNIONS {q (i:real^M->bool) | i IN r}
     :(real^M#(real^M->bool))->bool`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC FINE_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINE_UNIONS THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE]] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o last o CONJUNCTS o
                GEN_REWRITE_RULE I [division_of]) THEN
    REWRITE_TAC[UNIONS_UNION] THEN
    MATCH_MP_TAC TAGGED_DIVISION_UNION THEN CONJ_TAC THENL
     [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_OF_UNION_SELF]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC TAGGED_DIVISION_UNIONS THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      SIMP_TAC[FINITE_UNION; IN_UNION] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN
    REPEAT(CONJ_TAC THENL
            [ASM_MESON_TAC[division_of; FINITE_UNION; IN_UNION]; ALL_TAC]) THEN
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; OPEN_INTERIOR] THEN
    REPEAT(CONJ_TAC THENL
     [ASM_MESON_TAC[tagged_partial_division_of; FINITE_IMAGE]; ALL_TAC]) THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[NOT_IN_EMPTY; GSYM NOT_EXISTS_THM] THEN
    ASM_REWRITE_TAC[EXISTS_PAIR_THM; IN_IMAGE; IN_INTER; IN_UNION] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum (p UNION UNIONS {q i | i IN r}) (\(x,k). content k % f x) =
    vsum p (\(x:real^M,k:real^M->bool). content k % f x:real^N) +
    vsum (UNIONS {q i | (i:real^M->bool) IN r}) (\(x,k). content k % f x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_UNION_NONZERO THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF_FINITE]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_UNIONS; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FORALL_PAIR_THM; FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM] THEN
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(l:real^M->bool) SUBSET k` ASSUME_TAC THENL
     [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MP_TAC o SPECL [`k:real^M->bool`; `l:real^M->bool`] o
               el 2 o CONJUNCTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_UNION; IN_IMAGE; EXISTS_PAIR_THM] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
      REWRITE_TAC[NOT_IN_EMPTY; GSYM NOT_EXISTS_THM] THEN
      ASM_REWRITE_TAC[EXISTS_PAIR_THM; IN_IMAGE; IN_INTER; IN_UNION] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUBSET_INTERIOR; SET_RULE `s SUBSET t ==> t INTER s = s`] THEN
    SUBGOAL_THEN `?u v:real^M. l = interval[u,v]`
     (fun th -> REPEAT_TCL CHOOSE_THEN SUBST1_TAC th THEN
                SIMP_TAC[VECTOR_MUL_LZERO; GSYM CONTENT_EQ_0_INTERIOR]) THEN
    ASM_MESON_TAC[tagged_partial_division_of];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_UNIONS_NONZERO o
    rand o lhand o rand o lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF; IN_UNION]; ALL_TAC] THEN
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `l:real^M->bool` THEN DISCH_TAC THEN
    DISCH_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `m:real^M->bool`] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    SUBGOAL_THEN `?u v:real^M. m = interval[u,v]`
     (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF; IN_UNION]; ALL_TAC] THEN
    REWRITE_TAC[CONTENT_EQ_0_INTERIOR] THEN
    MATCH_MP_TAC(SET_RULE `!t. s SUBSET t /\ t = {} ==> s = {}`) THEN
    EXISTS_TAC `interior(k INTER l:real^M->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_INTERIOR THEN REWRITE_TAC[SUBSET_INTER] THEN
      ASM_MESON_TAC[TAGGED_DIVISION_OF];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    REWRITE_TAC[INTERIOR_INTER] THEN
    DISCH_THEN(MATCH_MP_TAC o SPECL [`k:real^M->bool`; `l:real^M->bool`] o
               el 2 o CONJUNCTS) THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; IN_UNION] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE_NONZERO o
    rand o lhand o rand o lhand o lhand o snd) THEN
  ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `l:real^M->bool`] THEN
    STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ_0 THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `m:real^M->bool`] THEN DISCH_TAC THEN
    MP_TAC(ASSUME `!i:real^M->bool. i IN r ==> q i tagged_division_of i`) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `l:real^M->bool` th) THEN
                         ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
                         MP_TAC(SPEC `k:real^M->bool` th) THEN
                         ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[tagged_division_of] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `vsum p (\(x,k). content k % (f:real^M->real^N) x - integral k f) =
    vsum p (\(x,k). content k % f x) - vsum p (\(x,k). integral k f)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[GSYM VSUM_SUB; LAMBDA_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!ir. ip + ir = i /\
         norm(cr - ir) < k
         ==> norm((cp + cr) - i) < e ==> norm(cp - ip) <= e + k`) THEN
  EXISTS_TAC `vsum r (\k. integral k (f:real^M->real^N))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum (IMAGE SND (p:(real^M#(real^M->bool))->bool) UNION r)
                     (\k. integral k (f:real^M->real^N))` THEN
    CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[INTEGRAL_COMBINE_DIVISION_TOPDOWN]] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum (IMAGE SND (p:(real^M#(real^M->bool))->bool))
                     (\k. integral k (f:real^M->real^N)) +
                vsum r (\k. integral k f)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_UNION_NONZERO THEN
      ASM_SIMP_TAC[FINITE_IMAGE; NOT_IN_EMPTY]] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(\(x:real^M,k). integral k (f:real^M->real^N)) =
                  (\k. integral k f) o SND`
    SUBST1_TAC THENL
     [SIMP_TAC[o_THM; FUN_EQ_THM; FORALL_PAIR_THM]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_IMAGE_NONZERO THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`x:real^M`; `l:real^M->bool`; `y:real^M`; `m:real^M->bool`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE I [tagged_partial_division_of]) THEN
    DISCH_THEN(CONJUNCTS_THEN MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`x:real^M`; `l:real^M->bool`; `y:real^M`; `l:real^M->bool`]) THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `l:real^M->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC o last o CONJUNCTS) THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC HAS_INTEGRAL_NULL THEN
    ASM_REWRITE_TAC[CONTENT_EQ_0_INTERIOR];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VSUM_SUB] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sum (r:(real^M->bool)->bool) (\x. k / (&(CARD r) + &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[SUM_CONST] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &x + &1`] THEN
    REWRITE_TAC[REAL_ARITH `a * k < k * b <=> &0 < k * (b - a)`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let HENSTOCK_LEMMA_PART2 = prove
 (`!f:real^M->real^N a b d e.
        f integrable_on interval[a,b] /\
        &0 < e /\ gauge d /\
        (!p. p tagged_division_of interval[a,b] /\ d fine p
             ==> norm (vsum p (\(x,k). content k % f x) -
                       integral(interval[a,b]) f) < e)
        ==> !p. p tagged_partial_division_of interval[a,b] /\ d fine p
                            ==> sum p (\(x,k). norm(content k % f x -
                                                    integral k f))
                                <= &2 * &(dimindex(:N)) * e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LAMBDA_PAIR] THEN
  MATCH_MP_TAC VSUM_NORM_ALLSUBSETS_BOUND THEN
  REWRITE_TAC[LAMBDA_PAIR_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
  X_GEN_TAC `q:(real^M#(real^M->bool))->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
    HENSTOCK_LEMMA_PART1) THEN
  MAP_EVERY EXISTS_TAC
   [`a:real^M`; `b:real^M`; `d:real^M->real^M->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[FINE_SUBSET; TAGGED_PARTIAL_DIVISION_SUBSET]);;

let HENSTOCK_LEMMA = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> !e. &0 < e
                ==> ?d. gauge d /\
                        !p. p tagged_partial_division_of interval[a,b] /\
                            d fine p
                            ==> sum p (\(x,k). norm(content k % f x -
                                                    integral k f)) < e`,
  MP_TAC HENSTOCK_LEMMA_PART2 THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN X_GEN_TAC `e:real` THEN
                       STRIP_TAC THEN MP_TAC th) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  GEN_REWRITE_TAC LAND_CONV [has_integral] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (&2 * (&(dimindex(:N)) + &1))`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &2 * (&n + &1)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`d:real^M->real^M->bool`; `e / (&2 * (&(dimindex(:N)) + &1))`]) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &2 * (&n + &1)`] THEN
  DISCH_THEN(fun th -> EXISTS_TAC `d:real^M->real^M->bool` THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `d < e ==> x <= d ==> x < e`) THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV; REAL_MUL_ASSOC] THEN
  SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;
